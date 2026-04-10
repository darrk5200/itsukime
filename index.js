const fetch = require('node-fetch');
const { Client } = require("discord.js-selfbot-v13");
const express = require("express");
const compression = require("compression");
const path = require("path");
const http = require("http");
const { Server } = require("socket.io");
const cors = require("cors");
require("dotenv").config();

// ============================================
// CONFIGURATION
// ============================================

// Multiple bot configuration for parallel caching
const CACHE_BOTS = {
    bot3: {
        token: process.env.BOT3_TOKEN,
        cacheCategoryIds: process.env.BOT3_CATEGORIES.split(","),
        databaseChannelId: process.env.BOT3_DATABASE,
        guildId: process.env.BOT3_GUILD,
        isPrimary: true
    },
    bot1: {
        token: process.env.BOT1_TOKEN,
        cacheCategoryIds: process.env.BOT1_CATEGORIES.split(","), 
        databaseChannelId: process.env.BOT1_DATABASE,
        guildId: process.env.BOT1_GUILD,
        isPrimary: false
    },
    bot2: {
        token: process.env.BOT2_TOKEN,
        cacheCategoryIds: process.env.BOT2_CATEGORIES.split(","),
        databaseChannelId: process.env.BOT2_DATABASE,
        guildId: process.env.BOT2_GUILD,
        isPrimary: false
    }
};

const DISCORD_RESTART_INTERVAL = 5 * 60 * 60 * 1000; // 3 hours in milliseconds
const LATEST_ANIME_COUNT = 3; // Number of latest anime to show at the top
const CHANNEL_CONCURRENCY = 3;  // Concurrent REST channel fetches per bot (keep low to avoid rate limit thundering herd)
const REST_PAGE_DELAY_MS = 100; // Delay between paginated requests within a single channel
const BOT_BATCH_SIZE = parseInt(process.env.BOT_BATCH_SIZE) || 2; // Bots processed simultaneously during init/fetch

// Run async tasks in sequential batches of batchSize, collecting all results
async function runInBatches(items, batchSize, fn) {
    const results = [];
    for (let i = 0; i < items.length; i += batchSize) {
        const batch = items.slice(i, i + batchSize);
        const batchResults = await Promise.all(batch.map(fn));
        results.push(...batchResults);
    }
    return results;
}

// ============================================
// EXPRESS SETUP
// ============================================

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
    cors: {
        origin: "*",
        methods: ["GET", "POST"]
    }
});

app.use(compression());
app.use(cors());
app.use(express.json());
app.use(express.static(path.join(__dirname, "public"), { maxAge: '1h' }));
app.set("view engine", "ejs");
app.set("views", path.join(__dirname, "views"));

// ============================================
// MULTI-BOT DISCORD SETUP
// ============================================

let botClients = new Map();
let botStatus = new Map();
let videoLibrary = new Map();
let animeMetadata = new Map();
let channelNameToMetadata = new Map();
let synonymMap = new Map();
let channelList = [];
let botRestartTimers = new Map();
let latestAnimeEntries = []; // Store the latest anime entries

// Cache distribution tracking
let cacheDistribution = new Map();

let libraryUpdateTimer = null;
let latestVideoTimestampCache = new Map();

// TMDB cache
const tmdbCache = new Map();
const TMDB_API_KEY = process.env.TMDB_API_KEY;
const TMDB_BASE = 'https://api.themoviedb.org/3';
const TMDB_IMG = 'https://image.tmdb.org/t/p/w300';

// Manual episode offset overrides
// Format: "Anime Name ### TMDB Show Name EP{start_episode}"
// This tells TMDB to search for "TMDB Show Name" and start from that episode number
// e.g. EP29 means episode 1 of this anime = TMDB episode 29 (offset 28)
const getCorrectEp = [
    "Frieren Beyond Journey's End Season 2 ### Frieren Beyond Journey's End EP29",
    "Re:ZERO - Starting Life in Another World Season 2 ### Re:ZERO - Starting Life in Another World EP26",
    "Re:ZERO - Starting Life in Another World Season 2 Part 2 ### Re:ZERO - Starting Life in Another World EP39",
    "Re:ZERO - Starting Life in Another World Season 2 Part II ### Re:ZERO - Starting Life in Another World EP39",
    "Re:ZERO - Starting Life in Another World Season 3 ### Re:ZERO - Starting Life in Another World EP51",
    "Re:ZERO - Starting Life in Another World Season 3 Part 1 ### Re:ZERO - Starting Life in Another World EP51",
    "Oshi no Ko 2nd Season ### Oshi no Ko EP12",
    "Oshi no Ko 3rd Season ### Oshi no Ko EP25",
    "The Disastrous Life of Saiki K. 2nd Season ### The Disastrous Life of Saiki K. EP25",
    "Masamune-kun's Revenge R ### Masamune-kun's Revenge EP13",
    "Snow White with the Red Hair 2nd Season ### Snow White with the Red Hair EP13",
    "My Teen Romantic Comedy SNAFU (S1) ### My Teen Romantic Comedy SNAFU EP1",
    "My Teen Romantic Comedy SNAFU TOO! (S2) ### My Teen Romantic Comedy SNAFU EP14",
    "My Teen Romantic Comedy SNAFU Climax (S3) ### My Teen Romantic Comedy SNAFU EP27",
    "Jujutsu Kaisen Season 2 ### Jujutsu Kaisen EP25",
    "Jujutsu Kaisen: The Culling Game ### Jujutsu Kaisen EP48",
    "Demon Slayer: Kimetsu no Yaiba ### Demon Slayer: Kimetsu no Yaiba EP1",
    "Demon Slayer: Kimetsu no Yaiba - Mugen Train ### Demon Slayer: Kimetsu no Yaiba EP27",
    "Demon Slayer: Kimetsu no Yaiba - Entertainment District Arc ### Demon Slayer: Kimetsu no Yaiba EP34",
    "Demon Slayer: Kimetsu no Yaiba - Swordsmith Village Arc ### Demon Slayer: Kimetsu no Yaiba EP45",
    "Demon Slayer: Kimetsu no Yaiba - Hashira Training Arc ### Demon Slayer: Kimetsu no Yaiba EP56"
];

function getAutomaticOffset(animeName) {
    const lower = animeName.toLowerCase();
    const seasonMatch = lower.match(/(\d+)(?:st|nd|rd|th)\s+season/i) || lower.match(/season\s+(\d+)/i) || lower.match(/\s+(\d{1,2})$/);

    if (seasonMatch) {
        const seasonNum = parseInt(seasonMatch[1]);
        if (seasonNum > 1) {
            // Check if we already have a manual override
            const cacheKey = animeName.toLowerCase().replace(/[^a-z0-9]/g, '');
            if (manualOverrides.has(cacheKey)) return null;

            const baseName = stripSeasonFromName(animeName);
            return {
                searchName: baseName,
                seasonNum: seasonNum
            };
        }
    }
    return null;
}

const manualOverrides = new Map();
for (const entry of getCorrectEp) {
    const [animePart, tmdbPart] = entry.split('###').map(s => s.trim());
    if (!animePart || !tmdbPart) continue;
    const epMatch = tmdbPart.match(/^(.+?)\s+EP(\d+)$/i);
    if (epMatch) {
        const key = animePart.toLowerCase().replace(/[^a-z0-9]/g, '');
        manualOverrides.set(key, {
            searchName: epMatch[1].trim(),
            startEp: parseInt(epMatch[2])
        });
    }
}

function detectSeasonNumber(animeName) {
    if (!animeName) return 1;

    const lower = animeName.toLowerCase().trim();

    const patterns = [
        /season[\s\-]*(\d+)/i,        // Season 2
        /s(\d+)/i,                   // S2
        /(\d+)(st|nd|rd|th)\s*season/i, // 2nd Season
        /\s(\d{1,2})$/               // "Anime Name 3"
    ];

    for (const p of patterns) {
        const match = lower.match(p);
        if (match) {
            const num = parseInt(match[1]);
            if (!isNaN(num)) return num;
        }
    }

    return 1;
}

function getBaseAnimeTitle(animeName) {
    if (!animeName) return "";

    return animeName
        .replace(/(\d+)(st|nd|rd|th)\s*season/gi, "")
        .replace(/season\s*\d+/gi, "")
        .replace(/\bs\d+\b/gi, "")
        .replace(/\s+\d+$/, "")
        .replace(/part\s*\d+/gi, "")
        .replace(/\s+/g, " ")
        .trim();
}

function stripSeasonFromName(animeName) {
    const lower = animeName.toLowerCase();
    // Special handling for Oshi no Ko and Saiki K
    if (lower.includes('oshi no ko') || lower.includes('saiki k')) {
        return animeName.replace(/(?:\s+|[-:])\s*(?:\d+(?:st|nd|rd|th)|season|s)\b\s*(?:season|s)?\s*\d*/gi, '').trim();
    }

    // Special handling for Re:ZERO
    if (lower.includes('re:zero')) {
        return animeName.replace(/\s*[-:]?\s*(?:season|s)\s*\d+/gi, '').trim();
    }

    return animeName
        .replace(/\s*[-:]?\s*(?:season|s)\s*\d+/gi, '')
        .replace(/\s*\d+(?:st|nd|rd|th)\s*season/gi, '')
        .replace(/\s+\d{1,2}$/, '')
        .trim();
}

function extractTitleSuffix(animeName) {
    const stripped = stripSeasonFromName(animeName);
    const m = stripped.match(/\s+([a-z]{1,4})$/i);
    return m ? m[1] : null;
}

function normalizeForTMDB(animeName) {
    let normalized = animeName;

    // Special handling for Oshi no Ko and Saiki K
    if (animeName.toLowerCase().includes('oshi no ko') || animeName.toLowerCase().includes('saiki k')) {
        normalized = stripSeasonFromName(animeName);
    }

    // Special handling for Re:ZERO
    if (animeName.toLowerCase().includes('re:zero')) {
        normalized = animeName.replace(/season\s*\d+/i, '').trim();
        normalized = normalized.replace(/\s*-\s*/, ' ');
        // Remove part indicators for TMDB search
        normalized = normalized.replace(/part\s*(i{1,3}|\d+)/i, '').trim();
    }

    return normalized;
}

// FIXED: Improved function to calculate cumulative episodes across all seasons
async function calculateCumulativeEpisodes(showId, targetSeasonNum) {
    try {
        const showRes = await fetch(`${TMDB_BASE}/tv/${showId}?api_key=${TMDB_API_KEY}`);
        const showData = await showRes.json();

        let cumulativeEps = 0;

        if (showData.seasons) {
            // Sort seasons by season number
            const sortedSeasons = showData.seasons
                .filter(s => s.season_number > 0)
                .sort((a, b) => a.season_number - b.season_number);

            // Add episodes from all seasons before the target season
            for (const season of sortedSeasons) {
                if (season.season_number < targetSeasonNum) {
                    cumulativeEps += season.episode_count || 0;
                } else {
                    break;
                }
            }
        }

        return cumulativeEps;
    } catch (error) {
        console.error(`Error calculating cumulative episodes: ${error.message}`);
        return 0;
    }
}

// Pick the TMDB result whose name most closely matches the search query
function pickBestTMDBResult(results, searchName) {
    if (!results || results.length === 0) return null;
    const target = searchName.toLowerCase().replace(/[^a-z0-9]/g, '');
    let best = null;
    let bestScore = Infinity;
    for (const r of results) {
        const name = (r.name || r.original_name || '').toLowerCase().replace(/[^a-z0-9]/g, '');
        if (name === target) return r; // exact match wins immediately
        if (name.includes(target) || target.includes(name)) {
            const score = Math.abs(name.length - target.length);
            if (score < bestScore) { bestScore = score; best = r; }
        }
    }
    return best || results[0];
}

// FIXED: Improved TMDB episode fetching with better season and offset handling
async function fetchTMDBEpisodes(animeName) {
    if (!TMDB_API_KEY) return null;
    const cacheKey = animeName.toLowerCase().replace(/[^a-z0-9]/g, '');
    if (tmdbCache.has(cacheKey)) return tmdbCache.get(cacheKey);

    // Check for manual overrides first
    const override = manualOverrides.get(cacheKey);
    if (override) {
        try {

            const searchRes = await fetch(`${TMDB_BASE}/search/tv?api_key=${TMDB_API_KEY}&query=${encodeURIComponent(override.searchName)}`);
            const searchData = await searchRes.json();

            if (searchData.results && searchData.results.length > 0) {
                const show = pickBestTMDBResult(searchData.results, override.searchName);
                const showId = show.id;

                // Get full show details including all seasons
                const showRes = await fetch(`${TMDB_BASE}/tv/${showId}?api_key=${TMDB_API_KEY}`);
                const showData = await showRes.json();

                const episodeMap = {};
                let cumulativeEps = 0;
                let targetSeasonFound = false;

                // Find which season contains the starting episode
                if (showData.seasons) {
                    const sortedSeasons = showData.seasons
                        .filter(s => s.season_number > 0)
                        .sort((a, b) => a.season_number - b.season_number);

                    for (const season of sortedSeasons) {
                        const seasonEndEp = cumulativeEps + (season.episode_count || 0);

                        // If our start episode falls within this season
                        if (override.startEp <= seasonEndEp) {
                            targetSeasonFound = true;

                            // Fetch this season's episodes
                            const seasonRes = await fetch(`${TMDB_BASE}/tv/${showId}/season/${season.season_number}?api_key=${TMDB_API_KEY}`);
                            const seasonData = await seasonRes.json();

                            if (seasonData.episodes) {
                                for (const ep of seasonData.episodes) {
                                    // Calculate the global episode number
                                    const globalEpNum = cumulativeEps + ep.episode_number;
                                    // Map to our local episode number (starting from 1)
                                    const localEpNum = globalEpNum - override.startEp + 1;

                                    if (localEpNum > 0) {
                                        episodeMap[localEpNum] = {
                                            title: ep.name || '',
                                            description: ep.overview || '',
                                            thumbnail: ep.still_path ? `${TMDB_IMG}${ep.still_path}` : null,
                                            airDate: ep.air_date || null,
                                            globalEpisode: globalEpNum,
                                            seasonNumber: season.season_number,
                                            episodeInSeason: ep.episode_number
                                        };
                                    }
                                }
                            }
                            break;
                        }

                        cumulativeEps += season.episode_count || 0;
                    }
                }

                if (!targetSeasonFound) {
                }

                const showInfo = {
                    genres: (showData.genres || []).map(g => g.name),
                    status: showData.status || null,
                    rating: showData.vote_average ? Math.round(showData.vote_average * 10) / 10 : null,
                    firstAirDate: showData.first_air_date || null,
                    name: showData.name,
                    numberOfSeasons: showData.number_of_seasons,
                    numberOfEpisodes: showData.number_of_episodes,
                    networks: (showData.networks || []).map(n => n.name).filter(Boolean),
                    type: showData.type || null,
                    originalLanguage: showData.original_language || null
                };

                const result = { episodes: Object.keys(episodeMap).length > 0 ? episodeMap : null, showInfo };
                tmdbCache.set(cacheKey, result);

                return result;
            }
        } catch (err) {
            console.error(`Error in manual override for ${animeName}:`, err.message);
        }
    }

    // Check for automatic season handling
    const autoOffset = getAutomaticOffset(animeName);
    if (autoOffset) {
        try {

            const searchRes = await fetch(`${TMDB_BASE}/search/tv?api_key=${TMDB_API_KEY}&query=${encodeURIComponent(autoOffset.searchName)}`);
            const searchData = await searchRes.json();

            if (searchData.results && searchData.results.length > 0) {
                const show = pickBestTMDBResult(searchData.results, autoOffset.searchName);
                const showId = show.id;

                const showRes = await fetch(`${TMDB_BASE}/tv/${showId}?api_key=${TMDB_API_KEY}`);
                const showData = await showRes.json();

                let cumulativeEps = 0;
                if (showData.seasons) {
                    const sortedSeasons = showData.seasons
                        .filter(s => s.season_number > 0)
                        .sort((a, b) => a.season_number - b.season_number);

                    for (const season of sortedSeasons) {
                        if (season.season_number < autoOffset.seasonNum) {
                            cumulativeEps += season.episode_count || 0;
                        }
                    }
                }

                const seasonRes = await fetch(`${TMDB_BASE}/tv/${showId}/season/${autoOffset.seasonNum}?api_key=${TMDB_API_KEY}`);
                const seasonData = await seasonRes.json();

                const episodeMap = {};
                if (seasonData.episodes) {
                    for (const ep of seasonData.episodes) {
                        const globalEpNum = cumulativeEps + ep.episode_number;
                        episodeMap[ep.episode_number] = {
                            title: ep.name || '',
                            description: ep.overview || '',
                            thumbnail: ep.still_path ? `${TMDB_IMG}${ep.still_path}` : null,
                            airDate: ep.air_date || null,
                            globalEpisode: globalEpNum,
                            seasonNumber: autoOffset.seasonNum,
                            episodeInSeason: ep.episode_number
                        };
                    }
                }

                const showInfo = {
                    genres: (showData.genres || []).map(g => g.name),
                    status: showData.status || null,
                    rating: showData.vote_average ? Math.round(showData.vote_average * 10) / 10 : null,
                    firstAirDate: showData.first_air_date || null,
                    name: showData.name,
                    numberOfSeasons: showData.number_of_seasons,
                    numberOfEpisodes: showData.number_of_episodes,
                    networks: (showData.networks || []).map(n => n.name).filter(Boolean),
                    type: showData.type || null,
                    originalLanguage: showData.original_language || null
                };

                const result = { episodes: Object.keys(episodeMap).length > 0 ? episodeMap : null, showInfo };
                tmdbCache.set(cacheKey, result);

                return result;
            }
        } catch (err) {
            console.error(`Error in automatic offset for ${animeName}:`, err.message);
        }
    }

    // Standard TMDB fetch without override
    try {
        let seasonNum = detectSeasonNumber(animeName);
        const baseTitle = getBaseAnimeTitle(animeName);
        const searchName = normalizeForTMDB(baseTitle);


        // Search for the show
        let searchData;
        const searchRes = await fetch(`${TMDB_BASE}/search/tv?api_key=${TMDB_API_KEY}&query=${encodeURIComponent(searchName)}`);
        searchData = await searchRes.json();

        // Try without colon if first search fails
        if ((!searchData.results || searchData.results.length === 0) && searchName.includes(':')) {
            const baseName = searchName.split(':')[0].trim();
            const fallbackRes = await fetch(`${TMDB_BASE}/search/tv?api_key=${TMDB_API_KEY}&query=${encodeURIComponent(baseName)}`);
            searchData = await fallbackRes.json();
        }

        if (!searchData.results || searchData.results.length === 0) {
            console.log(`   No TMDB results found for "${animeName}"`);
            tmdbCache.set(cacheKey, null);
            return null;
        }

        const show = pickBestTMDBResult(searchData.results, searchName);
        const showId = show.id;

        // Get full show details including all seasons
        const showRes = await fetch(`${TMDB_BASE}/tv/${showId}?api_key=${TMDB_API_KEY}`);
        const showData = await showRes.json();

        // Improved season detection - check for part indicators
        const isPartTwo = animeName.toLowerCase().includes('part 2') || 
                          animeName.toLowerCase().includes('part ii') ||
                          animeName.toLowerCase().includes('part two');

        const isPartThree = animeName.toLowerCase().includes('part 3') || 
                            animeName.toLowerCase().includes('part iii');

        // Adjust season number for parts
        if (isPartTwo && showData.seasons) {
            // For part 2, we need to look at the second half of the season
        }

        // Calculate cumulative episodes before our target season
        let cumulativeEps = 0;
        if (showData.seasons) {
            const sortedSeasons = showData.seasons
                .filter(s => s.season_number > 0)
                .sort((a, b) => a.season_number - b.season_number);

            for (const season of sortedSeasons) {
                if (season.season_number < seasonNum) {
                    cumulativeEps += season.episode_count || 0;
                }
            }

        }

        // If this is a part, adjust the offset
        let partOffset = 0;
        if (isPartTwo || isPartThree) {
            // Find the target season to get its episode count
            const targetSeason = showData.seasons?.find(s => s.season_number === seasonNum);
            if (targetSeason && targetSeason.episode_count) {
                if (isPartTwo) {
                    partOffset = Math.floor(targetSeason.episode_count / 2);

                } else if (isPartThree) {
                    partOffset = Math.floor(targetSeason.episode_count * 2 / 3);

                }
            }
        }

        // Fetch the target season
        const seasonRes = await fetch(`${TMDB_BASE}/tv/${showId}/season/${seasonNum}?api_key=${TMDB_API_KEY}`);
        const seasonData = await seasonRes.json();

        const episodeMap = {};
        if (seasonData.episodes) {
            for (const ep of seasonData.episodes) {
                // Calculate global episode number (across all seasons)
                const globalEpNum = cumulativeEps + ep.episode_number;
                // Map to our local episode number (starting from 1, accounting for part offset)
                const localEpNum = ep.episode_number - partOffset;

                if (localEpNum > 0) {
                    episodeMap[localEpNum] = {
                        title: ep.name || '',
                        description: ep.overview || '',
                        thumbnail: ep.still_path ? `${TMDB_IMG}${ep.still_path}` : null,
                        airDate: ep.air_date || null,
                        globalEpisode: globalEpNum,
                        seasonNumber: seasonNum,
                        episodeInSeason: ep.episode_number
                    };
                }
            }
        }

        const showInfo = {
            genres: (showData.genres || []).map(g => g.name),
            status: showData.status || null,
            rating: showData.vote_average ? Math.round(showData.vote_average * 10) / 10 : null,
            firstAirDate: showData.first_air_date || null,
            name: showData.name,
            numberOfSeasons: showData.number_of_seasons,
            numberOfEpisodes: showData.number_of_episodes,
            networks: (showData.networks || []).map(n => n.name).filter(Boolean),
            type: showData.type || null,
            originalLanguage: showData.original_language || null
        };

        const result = {
            episodes: Object.keys(episodeMap).length > 0 ? episodeMap : null,
            showInfo
        };

        tmdbCache.set(cacheKey, result);

        return result;
    } catch (err) {
        console.error(`Error fetching TMDB for ${animeName}:`, err.message);
        tmdbCache.set(cacheKey, null);
        return null;
    }
}

async function prefetchTMDBData() {
    if (!TMDB_API_KEY) return;
    const animeNames = new Set();
    for (const [key, value] of animeMetadata.entries()) {
        if (value?.name) animeNames.add(value.name);
    }
    let fetched = 0;
    let genresEnriched = 0;
    for (const name of animeNames) {
        const cacheKey = name.toLowerCase().replace(/[^a-z0-9]/g, '');
        if (tmdbCache.has(cacheKey)) {
            // Backfill genres from already-cached TMDB data
            const cached = tmdbCache.get(cacheKey);
            if (cached?.showInfo?.genres?.length) {
                const metaKey = titleToChannelName(name);
                const entry = animeMetadata.get(metaKey);
                if (entry && (!entry.genres || entry.genres.length === 0)) {
                    entry.genres = cached.showInfo.genres;
                    genresEnriched++;
                }
            }
            continue;
        }
        try {
            const tmdbResult = await fetchTMDBEpisodes(name);
            fetched++;
            // Write TMDB genres back to animeMetadata if the entry has no genres
            if (tmdbResult?.showInfo?.genres?.length) {
                const metaKey = titleToChannelName(name);
                const entry = animeMetadata.get(metaKey);
                if (entry && (!entry.genres || entry.genres.length === 0)) {
                    entry.genres = tmdbResult.showInfo.genres;
                    genresEnriched++;
                }
            }
            if (fetched % 20 === 0) {
                await new Promise(r => setTimeout(r, 500));
            }
        } catch (err) {}
    }
    if (genresEnriched > 0) {
        console.log(`🎭 Backfilled TMDB genres for ${genresEnriched} anime entries`);
        cachedSocketMeta = null;
        io.emit("metadata-update", {
            metadata: Object.fromEntries(animeMetadata),
            synonyms: Object.fromEntries(synonymMap)
        });
    }
}

function rebuildTimestampCache() {
    latestVideoTimestampCache.clear();
    for (const [key, videos] of videoLibrary.entries()) {
        if (videos && videos.length > 0) {
            latestVideoTimestampCache.set(key, Math.max(...videos.map(v => v.timestamp || 0)));
        }
    }
}

function debouncedLibraryUpdate() {
    if (libraryUpdateTimer) clearTimeout(libraryUpdateTimer);
    libraryUpdateTimer = setTimeout(() => {
        rebuildTimestampCache();
        io.emit("library-update", {
            channels: Array.from(videoLibrary.keys()),
            latestAnime: latestAnimeEntries
        });
        libraryUpdateTimer = null;
    }, 2000);
}

const channelFetchTimers = new Map();
function debouncedChannelFetch(channel, botId) {
    const key = `${channel.id}-${botId}`;
    if (channelFetchTimers.has(key)) clearTimeout(channelFetchTimers.get(key));
    channelFetchTimers.set(key, setTimeout(() => {
        channelFetchTimers.delete(key);
        handleNewVideo(channel, botId);
    }, 5000));
}

// ============================================
// SIMPLIFIED UTILITY FUNCTIONS
// ============================================

/**
 * Convert any anime title to channel name format
 * Examples:
 * "Frieren: Beyond Journey's End Season 2" -> "frieren-beyond-journeys-end-season-2"
 * "Anyway, I'm Falling in Love with You. Season 2" -> "anyway-im-falling-in-love-with-you-season-2"
 * "Re:ZERO - Starting Life in Another World Season 2" -> "rezero-starting-life-in-another-world-season-2"
 */
function titleToChannelName(title) {
    if (!title || typeof title !== 'string') return '';

    // Special handling for Re:ZERO
    let processed = title;
    if (title.toLowerCase().includes('re:zero')) {
        processed = title.replace('Re:ZERO', 'ReZero').replace('Re:Zero', 'ReZero');
    }

    // Special handling for Uma Musume: Pretty Derby
    if (title.toLowerCase().includes('uma musume') && title.toLowerCase().includes('pretty derby')) {
        processed = 'Uma Musume Pretty Derby';
    }

    return processed
        .toLowerCase()
        .replace(/'/g, '') // Remove apostrophes
        .replace(/[^a-z0-9\s]/g, ' ') // Replace other symbols with spaces
        .replace(/\s+/g, ' ') // Collapse multiple spaces
        .trim()
        .replace(/\s+/g, '-'); // Convert spaces to hyphens
}

function getSeasonSuffix(num) {
    if (num >= 11 && num <= 13) return 'th';
    switch (num % 10) {
        case 1: return 'st';
        case 2: return 'nd';
        case 3: return 'rd';
        default: return 'th';
    }
}

function formatDisplayName(channelName, metadata) {
    if (metadata && metadata.name) {
        return metadata.name;
    }

    // Special handling for Re:ZERO
    if (channelName.toLowerCase().includes('rezero')) {
        let formatted = channelName
            .replace(/rezero/i, 'Re:ZERO')
            .split('-')
            .map(word => {
                if (word.toLowerCase() === 're:zero') return 'Re:ZERO';
                return word.charAt(0).toUpperCase() + word.slice(1);
            })
            .join(' ');
        formatted = formatted.replace(/(\d+)(St|Nd|Rd|Th)-Season/gi, '$1$2 Season');
        return formatted;
    }

    let formatted = channelName
        .split('-')
        .map(word => word.charAt(0).toUpperCase() + word.slice(1))
        .join(' ');

    formatted = formatted.replace(/(\d+)(St|Nd|Rd|Th)-Season/gi, '$1$2 Season');

    return formatted;
}

function findMetadataForChannel(channelName) {
    if (animeMetadata.has(channelName)) return animeMetadata.get(channelName);

    const channelAlpha = channelName.toLowerCase().replace(/[^a-z0-9]/g, '');
    let bestMatch = null;
    let bestDiff = Infinity;

    for (const [key, meta] of animeMetadata.entries()) {
        const keyAlpha = key.replace(/[^a-z0-9]/g, '');

        // Special handling for Re:ZERO
        if (channelAlpha.includes('rezero') && keyAlpha.includes('rezero')) {
            if (channelAlpha.includes('season2') && keyAlpha.includes('season2')) return meta;
            if (channelAlpha.includes('season3') && keyAlpha.includes('season3')) return meta;
        }

        if (keyAlpha === channelAlpha) return meta;
        if (keyAlpha.includes(channelAlpha) || channelAlpha.includes(keyAlpha)) {
            const shorter = Math.min(keyAlpha.length, channelAlpha.length);
            const longer = Math.max(keyAlpha.length, channelAlpha.length);
            if (longer === 0 || shorter / longer < 0.5) continue; // too different
            const diff = Math.abs(keyAlpha.length - channelAlpha.length);
            if (diff < bestDiff) {
                bestDiff = diff;
                bestMatch = meta;
            }
        }
    }
    return bestMatch;
}

/**
 * Find a channel by exact title conversion
 * This is the simplified function - just convert title to channel name and look it up
 */
function findChannelByTitle(animeTitle) {
    if (!animeTitle) return null;

    // 1. Try exact match with titleToChannelName normalization
    const expectedChannelName = titleToChannelName(animeTitle);
    if (videoLibrary.has(expectedChannelName)) {
        return expectedChannelName;
    }

    // 2. Try match with simplified normalization (alphanumeric only)
    const simplifiedExpected = animeTitle.toLowerCase().replace(/[^a-z0-9]/g, '');
    if (videoLibrary.has(simplifiedExpected)) {
        return simplifiedExpected;
    }

    // 3. Score all keys and return the best match (smallest length difference wins)
    let bestKey = null;
    let bestScore = Infinity;

    for (const key of videoLibrary.keys()) {
        const normalizedKey = key.toLowerCase();
        const simplifiedKey = normalizedKey.replace(/[^a-z0-9]/g, '');

        // Special handling for Re:ZERO variations
        if (animeTitle.toLowerCase().includes('re:zero') && normalizedKey.includes('rezero')) {
            if (animeTitle.toLowerCase().includes('season 2') && normalizedKey.includes('season-2')) return key;
            if (animeTitle.toLowerCase().includes('season 3') && normalizedKey.includes('season-3')) return key;
            if (animeTitle.toLowerCase().includes('part 2') && normalizedKey.includes('part-2')) return key;
            if (animeTitle.toLowerCase().includes('part ii') && normalizedKey.includes('part-ii')) return key;
        }

        let matched = false;
        if (normalizedKey === expectedChannelName || 
            normalizedKey === simplifiedExpected ||
            simplifiedKey === simplifiedExpected) {
            return key; // Exact match — return immediately
        }

        if (normalizedKey.includes(simplifiedExpected) ||
            simplifiedExpected.includes(normalizedKey) ||
            simplifiedKey.includes(simplifiedExpected) ||
            simplifiedExpected.includes(simplifiedKey)) {
            matched = true;
        }

        if (matched) {
            const shorter = Math.min(simplifiedKey.length, simplifiedExpected.length);
            const longer = Math.max(simplifiedKey.length, simplifiedExpected.length);
            if (longer === 0 || shorter / longer < 0.5) continue; // too different
            const score = Math.abs(simplifiedKey.length - simplifiedExpected.length);
            if (score < bestScore) {
                bestScore = score;
                bestKey = key;
            }
        }
    }

    return bestKey;
}

function expandSearchQuery(query) {
    if (!query || typeof query !== 'string') return [];

    const normalizedQuery = titleToChannelName(query);
    const expandedTerms = new Set();

    expandedTerms.add(query.toLowerCase());
    expandedTerms.add(normalizedQuery);

    // Add Re:ZERO variations
    if (query.toLowerCase().includes('re:zero')) {
        expandedTerms.add(query.toLowerCase().replace('re:zero', 'rezero'));
        expandedTerms.add(normalizedQuery.replace('re-zero', 'rezero'));

        // Add part variations
        if (query.toLowerCase().includes('part 2')) {
            expandedTerms.add('part-2');
            expandedTerms.add('part-ii');
        }
        if (query.toLowerCase().includes('part ii')) {
            expandedTerms.add('part-2');
            expandedTerms.add('part-ii');
        }
    }

    // Add the base title without season
    const baseTitle = query.replace(/(?:^|\s)(?:season|s)[\s-]*\d+/i, '').trim();
    expandedTerms.add(baseTitle.toLowerCase());
    expandedTerms.add(titleToChannelName(baseTitle));

    return Array.from(expandedTerms);
}

// ============================================
// LATEST ANIME TRACKING FUNCTIONS
// ============================================

function updateLatestAnimeEntries(metadataMap) {
    function getNewestVideoTime(channelName) {
        const videos = videoLibrary.get(channelName);
        if (!videos || videos.length === 0) return 0;
        return Math.max(...videos.map(v => v.timestamp || 0));
    }

    const sortedEntries = Array.from(metadataMap.entries())
        .filter(([_, metadata]) => metadata && metadata.timestamp)
        .sort((a, b) => {
            const aTime = getNewestVideoTime(a[0]) || a[1].timestamp;
            const bTime = getNewestVideoTime(b[0]) || b[1].timestamp;
            return bTime - aTime;
        })
        .slice(0, LATEST_ANIME_COUNT)
        .map(([channelName, metadata]) => {
            const latestVideo = getNewestVideoTime(channelName);
            return {
                channelName,
                name: metadata.name,
                timestamp: latestVideo || metadata.timestamp,
                displayName: formatDisplayName(channelName, metadata),
                hasVideos: videoLibrary.has(channelName),
                videoCount: videoLibrary.get(channelName)?.length || 0,
                imageUrl: metadata.imageUrl
            };
        });

    latestAnimeEntries = sortedEntries;

    console.log(`\n📌 Latest ${LATEST_ANIME_COUNT} anime entries:`);
    sortedEntries.forEach((entry, index) => {
        console.log(`   ${index + 1}. ${entry.name} (${new Date(entry.timestamp).toLocaleString()})`);
    });

    return latestAnimeEntries;
}

function getSortedChannelList() {
    const allChannels = Array.from(videoLibrary.keys());

    // Get channel names from latest anime entries
    const latestChannelNames = new Set(
        latestAnimeEntries.map(entry => entry.channelName)
    );

    // Separate channels into latest and others
    const latestChannels = [];
    const otherChannels = [];

    allChannels.forEach(channel => {
        if (latestChannelNames.has(channel)) {
            latestChannels.push(channel);
        } else {
            otherChannels.push(channel);
        }
    });

    // Sort other channels alphabetically
    otherChannels.sort((a, b) => a.localeCompare(b));

    // Return combined list with latest channels first
    return [...latestChannels, ...otherChannels];
}

// ============================================
// MULTI-BOT FUNCTIONS
// ============================================

async function createBotClient(botId, botConfig) {
    if (botClients.has(botId)) {
        console.log(`🔄 Destroying existing Discord client for ${botId}...`);
        try {
            const oldClient = botClients.get(botId);
            oldClient.removeAllListeners();
            await oldClient.destroy();
        } catch (error) {
            console.error(`❌ Error destroying client ${botId}:`, error.message);
        }
    }

    const client = new Client({
        checkUpdate: false
    });

    botClients.set(botId, client);
    botStatus.set(botId, {
        connected: false,
        lastActivity: null,
        channelsCached: 0,
        config: botConfig
    });

    return client;
}

async function fetchAnimeMetadataFromBot(botId, botConfig) {
    try {
        const client = botClients.get(botId);
        if (!client || !client.user) {
            console.log(`⏳ Bot ${botId} not ready, skipping metadata fetch...`);
            return null;
        }

        console.log(`📚 ${botId} fetching anime metadata...`);

        const channel = await client.channels.fetch(botConfig.databaseChannelId);
        let messages = new Map();
        let lastId = null;
        while (true) {
            const options = { limit: 100 };
            if (lastId) options.before = lastId;
            const batch = await channel.messages.fetch(options);
            if (batch.size === 0) break;
            batch.forEach((msg, id) => messages.set(id, msg));
            lastId = batch.last().id;
            if (batch.size < 100) break;
        }

        const metadata = new Map();
        const synonyms = new Map();

        // ===== Process messages to extract metadata =====
        messages.forEach(msg => {
            const content = msg.content;

            const nameMatch = content.match(/Name:\s*(.+)/i);
            const synopsisMatch = content.match(/Synopsis:\s*(.+)/i);
            const genresMatch = content.match(/Genres:\s*(.+)/i);
            const imageUrlMatch = content.match(/ImageURL:\s*(.+)/i);
            const synonymsMatch = content.match(/Synonyms:\s*(.+)/i);

            if (nameMatch && imageUrlMatch) {
                const canonicalName = nameMatch[1].trim();

                // Convert the title to channel name format
                const channelName = titleToChannelName(canonicalName);

                let genres = [];
                if (genresMatch) {
                    genres = genresMatch[1].split(',').map(g => g.trim());
                }

                let synonymList = [];
                if (synonymsMatch) {
                    synonymList = synonymsMatch[1].split(',').map(s => s.trim().toLowerCase());
                }

                const allSearchTerms = [
                    canonicalName.toLowerCase(),
                    channelName,
                    ...canonicalName.toLowerCase().split(' ').map(w => w.replace(/[^\w]/g, '')).filter(w => w.length > 2),
                    ...genres.map(g => g.toLowerCase()),
                    ...synonymList
                ];

                // Add synonyms to search map
                allSearchTerms.forEach(term => {
                    if (term && term.length > 2) {
                        if (!synonyms.has(term)) {
                            synonyms.set(term, new Set());
                        }
                        synonyms.get(term).add(channelName);
                    }
                });

                const metadataObj = {
                    name: canonicalName,
                    synopsis: synopsisMatch ? synopsisMatch[1].trim() : '',
                    genres: genres,
                    imageUrl: imageUrlMatch[1].trim(),
                    synonyms: synonymList,
                    messageId: msg.id,
                    timestamp: msg.createdTimestamp,
                    normalizedName: channelName,
                    searchTerms: allSearchTerms,
                    sourceBot: botId
                };

                metadata.set(channelName, metadataObj);
            }
        });

        console.log(`✅ ${botId} loaded ${metadata.size} metadata entries`);

        return {
            metadata,
            synonyms
        };

    } catch (error) {
        console.error(`❌ Bot ${botId} metadata fetch error:`, error.message);
        return null;
    }
}

// Fetch all messages from a Discord channel using the REST API directly.
// Each bot uses its own token, so rate limits are fully independent per bot.
async function fetchChannelMessagesViaREST(channelId, token) {
    const messages = [];
    let lastId = null;

    while (true) {
        let url = `https://discord.com/api/v9/channels/${channelId}/messages?limit=100`;
        if (lastId) url += `&before=${lastId}`;

        let res;
        while (true) {
            res = await fetch(url, { headers: { 'Authorization': token } });
            if (res.status === 429) {
                let retryAfter = 1;
                try { const body = await res.json(); retryAfter = body.retry_after || 1; } catch {}
                await new Promise(r => setTimeout(r, retryAfter * 1000));
                continue;
            }
            break;
        }

        if (!res.ok) break;

        const batch = await res.json();
        if (!Array.isArray(batch) || batch.length === 0) break;

        messages.push(...batch);
        lastId = batch[batch.length - 1].id;
        if (batch.length < 100) break;

        // Brief pause between pages to stay within Discord's rate limit budget
        await new Promise(r => setTimeout(r, REST_PAGE_DELAY_MS));
    }

    return messages;
}

// Extract video entries from a raw REST API message array.
function extractVideosFromMessages(rawMessages, channel, botId) {
    const videos = [];

    for (const msg of rawMessages) {
        if (!msg.attachments?.length) continue;

        for (const attachment of msg.attachments) {
            if (!attachment.content_type?.includes("video")) continue;

            const textSource = (
                msg.content ||
                msg.embeds?.[0]?.title ||
                msg.embeds?.[0]?.description ||
                attachment.filename ||
                ""
            );

            let episodeNum = 0;
            const episodeMatch =
                textSource.match(/\b(?:episode|ep)\s*(\d+\.?\d*)\b/i) ||
                textSource.match(/\bE(\d{2,}\.?\d*)\b/i) ||
                textSource.match(/(\d+\.?\d*)\/\d+/);

            if (episodeMatch) episodeNum = parseFloat(episodeMatch[1]);

            let title = msg.content || attachment.filename;
            title = title.replace(/[\u{1F300}-\u{1F9FF}]|[\u{2600}-\u{26FF}]/gu, '');
            title = title.replace(/\*\*/g, '');
            title = title.replace(/\(\d+\/\d+\)/g, '');
            title = title.replace(/\s*-\s*Episode\s*\d+\.?\d*/i, '');
            title = title.trim();
            title = title.split(' ').map(word =>
                word.length === 0 ? '' : word.charAt(0).toUpperCase() + word.slice(1).toLowerCase()
            ).join(' ');

            const authorName = (msg.author.discriminator && msg.author.discriminator !== '0')
                ? `${msg.author.username}#${msg.author.discriminator}`
                : msg.author.username;

            videos.push({
                id: msg.id,
                channelId: channel.id,
                channelName: channel.name,
                title: title,
                url: attachment.url,
                filename: attachment.filename,
                episode: episodeNum,
                timestamp: new Date(msg.timestamp).getTime(),
                author: authorName,
                contentType: attachment.content_type,
                size: attachment.size,
                cachedBy: botId
            });
        }
    }

    videos.sort((a, b) => a.episode - b.episode);
    return videos;
}

async function fetchVideosFromBot(botId, botConfig, channelBatch) {
    try {
        const client = botClients.get(botId);
        if (!client || !client.user) {
            console.log(`⏳ Bot ${botId} not ready, skipping video fetch...`);
            return new Map();
        }

        const token = botConfig.token;
        console.log(`📡 ${botId} fetching ${channelBatch.length} channels (${CHANNEL_CONCURRENCY} concurrent)...`);

        const botVideoLibrary = new Map();
        let channelsCached = 0;

        // Process channels in concurrent batches — each bot uses its own token's rate limit budget
        for (let i = 0; i < channelBatch.length; i += CHANNEL_CONCURRENCY) {
            const batch = channelBatch.slice(i, i + CHANNEL_CONCURRENCY);
            await Promise.all(batch.map(async (channel) => {
                try {
                    if (!channel || !channel.name) return;

                    const rawMessages = await fetchChannelMessagesViaREST(channel.id, token);
                    const videos = extractVideosFromMessages(rawMessages, channel, botId);

                    if (videos.length > 0) {
                        botVideoLibrary.set(channel.name, videos);
                        cacheDistribution.set(channel.name, botId);
                        channelsCached++;
                    }
                } catch (error) {
                    console.error(`   ❌ Bot ${botId} error fetching channel ${channel.name}: ${error.message}`);
                }
            }));
        }

        const status = botStatus.get(botId) || {};
        status.channelsCached = (status.channelsCached || 0) + channelsCached;
        status.lastActivity = Date.now();
        botStatus.set(botId, status);

        console.log(`✅ Bot ${botId} cached ${channelsCached} channels with videos`);
        return botVideoLibrary;

    } catch (error) {
        console.error(`❌ Bot ${botId} video fetch error:`, error);
        return new Map();
    }
}

async function fetchAllMetadata() {
    console.log("\n📚 ===== FETCHING METADATA FROM ALL BOTS =====\n");

    const allMetadata = new Map();
    const allSynonyms = new Map();

    const botEntries = Object.entries(CACHE_BOTS);

    const results = await runInBatches(botEntries, BOT_BATCH_SIZE, async ([botId, botConfig]) => {
        const result = await fetchAnimeMetadataFromBot(botId, botConfig);
        return { botId, result };
    });

    for (const { botId, result } of results) {
        if (result) {
            for (const [key, value] of result.metadata.entries()) {
                if (!allMetadata.has(key)) {
                    allMetadata.set(key, value);
                } else if (CACHE_BOTS[botId]?.isPrimary) {
                    allMetadata.set(key, value);
                }
            }

            for (const [synonym, channels] of result.synonyms.entries()) {
                if (!allSynonyms.has(synonym)) {
                    allSynonyms.set(synonym, new Set());
                }
                channels.forEach(ch => {
                    if (ch && typeof ch === 'string') {
                        allSynonyms.get(synonym).add(ch);
                    }
                });
            }
        }
    }

    // Dedup: remove bare-number season entries when a proper ordinal form exists
    // e.g. remove "Oshi no Ko 3" when "Oshi no Ko 3rd Season" is present
    const suffixMap = { 1: 'st', 2: 'nd', 3: 'rd' };
    const getSuffix = n => (n >= 11 && n <= 13) ? 'th' : (suffixMap[n % 10] || 'th');
    const keysToRemove = new Set();
    for (const [key, meta] of allMetadata.entries()) {
        const bareMatch = meta.name.match(/^(.+?)\s+(\d+)$/);
        if (bareMatch) {
            const base = bareMatch[1];
            const num  = parseInt(bareMatch[2]);
            const ordinalForm = `${base} ${num}${getSuffix(num)} Season`;
            const ordinalKey  = titleToChannelName(ordinalForm);
            if (allMetadata.has(ordinalKey)) {
                console.log(`🗑️  Removing duplicate entry "${meta.name}" (superseded by "${ordinalForm}")`);
                keysToRemove.add(key);
            }
        }
    }
    keysToRemove.forEach(k => allMetadata.delete(k));

    animeMetadata = allMetadata;
    synonymMap = allSynonyms;

    // Update latest anime entries after metadata is fetched
    updateLatestAnimeEntries(animeMetadata);

    console.log(`\n✅ Total metadata loaded: ${animeMetadata.size} anime`);
    console.log(`✅ Total synonyms loaded: ${synonymMap.size} entries`);
}

async function handleNewVideo(channel, botId) {
    try {
        console.log(`⚡ Immediately fetching videos for #${channel.name} from bot ${botId}`);

        const token = CACHE_BOTS[botId].token;
        const rawMessages = await fetchChannelMessagesViaREST(channel.id, token);
        const videos = extractVideosFromMessages(rawMessages, channel, botId);

        if (videos.length > 0 && channel.name && typeof channel.name === 'string') {
            videoLibrary.set(channel.name, videos);
            cacheDistribution.set(channel.name, botId);

            console.log(`✅ Updated ${videos.length} videos for #${channel.name} from bot ${botId}`);

            const status = botStatus.get(botId) || {};
            status.channelsCached = (status.channelsCached || 0) + 1;
            status.lastActivity = Date.now();
            botStatus.set(botId, status);

            debouncedLibraryUpdate();
        }

    } catch (error) {
        console.error(`❌ Error handling new video for bot ${botId}:`, error.message);
    }
}

function setupBotListeners(client, botId, botConfig) {
    console.log(`🎧 Setting up listeners for bot ${botId} for ${botConfig.cacheCategoryIds.length} categories`);

    client.on("messageCreate", async (message) => {
        // Check if message is in this bot's guild
        if (message.guild?.id !== botConfig.guildId) return;

        // Handle database channel messages (metadata updates)
        if (message.channel.id === botConfig.databaseChannelId) {
            console.log(`📝 New metadata message detected by ${botId}`);

            // Fetch all metadata from ALL bots to ensure consistency
            await fetchAllMetadata();

            cachedSocketMeta = null;
            io.emit("metadata-update", {
                metadata: Object.fromEntries(animeMetadata),
                synonyms: Object.fromEntries(synonymMap)
            });

            debouncedLibraryUpdate();
        }

        if (botConfig.cacheCategoryIds.includes(message.channel.parentId)) {
            if (message.attachments.size > 0) {
                const hasVideo = message.attachments.some(a => a.contentType?.includes("video"));
                if (hasVideo) {
                    console.log(`📥 New video in #${message.channel.name} detected by ${botId}`);
                    debouncedChannelFetch(message.channel, botId);
                }
            }
        }
    });

    // Also listen for channel creation in ANY of the cache categories
    client.on("channelCreate", async (channel) => {
        if (channel.guild?.id === botConfig.guildId && 
            botConfig.cacheCategoryIds.includes(channel.parentId)) {
            console.log(`🆕 New channel #${channel.name} created in category ${channel.parentId}, detected by ${botId}`);

            // Refresh all videos when new channel is created
            setTimeout(() => {
                fetchAllVideos();
            }, 2000);
        }
    });
}

async function fetchAllVideos() {
    console.log(`\n📡 ===== FETCHING VIDEOS FROM ALL BOTS (batch size: ${BOT_BATCH_SIZE}) =====\n`);

    // Each bot independently discovers and fetches only its own guild's channels.
    // Bots are processed in batches of BOT_BATCH_SIZE to limit concurrent memory
    // and Discord API usage when running many bots.
    const botEntries = Object.entries(CACHE_BOTS)
        .filter(([botId]) => {
            const client = botClients.get(botId);
            return client && client.user;
        });

    const results = await runInBatches(botEntries, BOT_BATCH_SIZE, async ([botId, botConfig]) => {
        const client = botClients.get(botId);
        const botChannels = [];

        try {
            const guild = await client.guilds.fetch(botConfig.guildId);
            await guild.channels.fetch();

            for (const categoryId of botConfig.cacheCategoryIds) {
                const category = guild.channels.cache.get(categoryId);
                if (category) {
                    const channels = guild.channels.cache.filter(
                        ch => ch.parentId === categoryId && ch.type === "GUILD_TEXT"
                    );
                    channels.forEach(ch => botChannels.push(ch));
                    console.log(`   Bot ${botId} found ${channels.size} channels in category ${categoryId}`);
                } else {
                    console.log(`   ⚠️ Bot ${botId} category not found: ${categoryId}`);
                }
            }
        } catch (error) {
            console.error(`❌ Bot ${botId} error fetching channels:`, error.message);
        }

        console.log(`📋 Bot ${botId}: ${botChannels.length} channels to cache`);

        const library = await fetchVideosFromBot(botId, botConfig, botChannels);
        return { botId, library };
    });

    // Clear and rebuild the video library with ALL videos from ALL bots
    videoLibrary.clear();
    cacheDistribution.clear();

    // Merge videos from all bots properly
    for (const result of results) {
        if (!result || !result.botId || !result.library) continue;
        const { botId, library } = result;
        console.log(`\n📥 Processing library for bot: ${botId} (${library.size} channels)`);
        for (const [channelName, videos] of library.entries()) {
            if (channelName && typeof channelName === 'string') {
                // Discord channel names are already unique (e.g., "hyouka")
                const rawName = channelName.toLowerCase();
                const normalizedKey = titleToChannelName(channelName);
                const simplifiedName = channelName.toLowerCase().replace(/[^a-z0-9]/g, '');

                // Assign to all possible variations to ensure matching works
                const keysToAssign = new Set([rawName, normalizedKey, simplifiedName]);

                // Broaden matching for Hyouka and common variations
                if (rawName.includes('hyouka') || normalizedKey.includes('hyouka')) {
                    keysToAssign.add('hyouka');
                }

                // Add base name without season for even broader matching
                const baseName = rawName.replace(/season\s*\d+/g, '').trim().replace(/-+$/, '');
                if (baseName.length > 2) {
                    keysToAssign.add(baseName);
                    keysToAssign.add(titleToChannelName(baseName));
                }

                keysToAssign.forEach(key => {
                    if (key.length < 2) return;
                    const existing = videoLibrary.get(key);
                    // Force update if it has more or equal episodes to ensure Bot 2 content is preferred if better
                    if (!existing || videos.length >= existing.length) {
                        videoLibrary.set(key, videos);
                        cacheDistribution.set(key, botId);
                        if (key.toLowerCase().includes('hyouka')) {
                            console.log(`   [Merge] Hyouka match found: ${key} assigned to ${botId} (${videos.length} eps)`);
                        }
                    }
                });
            }
        }
    }

    console.log(`\n✅ Total videos cached: ${videoLibrary.size} channels`);

    // Log the first few channels to verify
    const channelList = Array.from(videoLibrary.keys()).slice(0, 5);
    console.log("📺 Sample channels with videos:", channelList);

    console.log("\n📊 Bot caching stats:");
    for (const [botId, status] of botStatus.entries()) {
        console.log(`   Bot ${botId}: ${status.channelsCached || 0} channels cached`);
    }

    rebuildTimestampCache();
    debouncedLibraryUpdate();

    prefetchTMDBData();
}

async function initializeBot(botId, botConfig) {
    try {
        // Ensure cacheCategoryIds is an array for backward compatibility
        if (!Array.isArray(botConfig.cacheCategoryIds)) {
            botConfig.cacheCategoryIds = [botConfig.cacheCategoryId];
        }

        console.log(`\n🤖 Initializing bot: ${botId} with ${botConfig.cacheCategoryIds.length} categories`);

        const client = await createBotClient(botId, botConfig);

        client.once("ready", async () => {
            console.log(`✅ Bot ${botId} logged in as ${client.user.tag}`);

            botStatus.set(botId, {
                connected: true,
                lastActivity: Date.now(),
                channelsCached: 0,
                config: botConfig,
                user: client.user.tag,
                categories: botConfig.cacheCategoryIds
            });

            // Setup listeners for ALL bots, not just primary
            setupBotListeners(client, botId, botConfig);
        });

        client.on("error", (error) => {
            console.error(`❌ Bot ${botId} error:`, error.message);
            const status = botStatus.get(botId) || {};
            status.connected = false;
            botStatus.set(botId, status);
        });

        await client.login(botConfig.token);

    } catch (error) {
        console.error(`❌ Bot ${botId} login failed:`, error.message);

        console.log(`⏰ Retrying bot ${botId} in 1 minute...`);
        setTimeout(() => {
            initializeBot(botId, botConfig);
        }, 60000);
    }
}

async function initializeAllBots() {
    console.log("\n🚀 ===== INITIALIZING ALL BOTS =====\n");

    const botEntries = Object.entries(CACHE_BOTS);

    await runInBatches(botEntries, BOT_BATCH_SIZE, ([botId, botConfig]) =>
        initializeBot(botId, botConfig)
    );

    console.log("\n✅ All bots initialized");

    setTimeout(async () => {
        const loadStart = Date.now();

        const metaStart = Date.now();
        await fetchAllMetadata();
        console.log(`⏱️  Metadata loaded in ${((Date.now() - metaStart) / 1000).toFixed(2)}s`);

        // Notify all already-connected clients (e.g. page loaded before bots finished)
        cachedSocketMeta = null;
        io.emit("metadata-update", {
            metadata: Object.fromEntries(animeMetadata),
            synonyms: Object.fromEntries(synonymMap)
        });

        const videoStart = Date.now();
        await fetchAllVideos();
        console.log(`⏱️  Videos loaded in ${((Date.now() - videoStart) / 1000).toFixed(2)}s`);

        console.log(`⏱️  Total data load completed in ${((Date.now() - loadStart) / 1000).toFixed(2)}s`);
    }, 5000);
}

// ============================================
// BOT RESTART FUNCTIONALITY
// ============================================

async function restartBot(botId) {
    console.log(`\n🔄 ===== RESTARTING BOT ${botId} =====`);

    const botConfig = CACHE_BOTS[botId];
    if (!botConfig) {
        console.error(`❌ Bot ${botId} not found in config`);
        return false;
    }

    // For backward compatibility, ensure cacheCategoryIds is an array
    if (!Array.isArray(botConfig.cacheCategoryIds)) {
        botConfig.cacheCategoryIds = [botConfig.cacheCategoryId];
    }

    try {
        io.emit("bot-restart", {
            botId: botId,
            message: `Bot ${botId} is reconnecting...`,
            time: Date.now()
        });

        await initializeBot(botId, botConfig);

        if (cacheDistribution.size > 0) {
            const channelsToRefresh = [];
            for (const [channel, cachingBot] of cacheDistribution.entries()) {
                if (cachingBot === botId) {
                    channelsToRefresh.push(channel);
                }
            }

            if (channelsToRefresh.length > 0) {
                console.log(`📡 Refreshing ${channelsToRefresh.length} channels that were cached by bot ${botId}`);
                await fetchAllVideos();
            }
        }

        io.emit("bot-connected", {
            botId: botId,
            message: `Bot ${botId} reconnected successfully!`,
            time: Date.now()
        });

        console.log(`✅ Bot ${botId} restart complete!`);
        return true;

    } catch (error) {
        console.error(`❌ Bot ${botId} restart failed:`, error.message);

        setTimeout(() => {
            restartBot(botId);
        }, 60000);

        return false;
    }
}

function scheduleBotRestarts() {
    for (const timer of botRestartTimers.values()) {
        clearTimeout(timer);
    }
    botRestartTimers.clear();

    Object.keys(CACHE_BOTS).forEach((botId, index) => {
        const staggerOffset = index * 15 * 60 * 1000;

        console.log(`⏰ Bot ${botId} scheduled restart: Every 3 hours (staggered +${index * 15}min)`);

        const timer = setTimeout(async () => {
            await restartBot(botId);
            scheduleBotRestarts();
        }, DISCORD_RESTART_INTERVAL + staggerOffset);

        botRestartTimers.set(botId, timer);
    });
}

// ============================================
// EXPRESS ROUTES
// ============================================

app.get("/", (req, res) => {
    const sortedChannels = getSortedChannelList();

    const enhancedChannels = sortedChannels.map(channel => ({
        name: channel,
        displayName: formatDisplayName(channel, findMetadataForChannel(channel)),
        hasMetadata: !!findMetadataForChannel(channel)
    }));

    const unsortedMetadata = {};
    const seenAnimeNames = new Set();
    for (const [key, value] of animeMetadata.entries()) {
        const animeName = (value.name || '').toLowerCase().replace(/[^a-z0-9]/g, '');
        if (!seenAnimeNames.has(animeName)) {
            seenAnimeNames.add(animeName);
            unsortedMetadata[key] = value;
        }
    }
    for (const channel of sortedChannels) {
        if (!unsortedMetadata[channel]) {
            const found = findMetadataForChannel(channel);
            if (found) {
                const animeName = (found.name || '').toLowerCase().replace(/[^a-z0-9]/g, '');
                if (!seenAnimeNames.has(animeName)) {
                    seenAnimeNames.add(animeName);
                    unsortedMetadata[channel] = found;
                }
            }
        }
    }

    function getLatestVideoTimestamp(channelKey) {
        const cached = latestVideoTimestampCache.get(channelKey);
        if (cached) return cached;
        const alphaKey = channelKey.replace(/[^a-z0-9]/g, '');
        for (const [libKey, ts] of latestVideoTimestampCache.entries()) {
            if (libKey.replace(/[^a-z0-9]/g, '') === alphaKey) return ts;
        }
        return 0;
    }

    const resolvedMetadata = {};
    Object.entries(unsortedMetadata)
        .sort((a, b) => {
            const aTime = getLatestVideoTimestamp(a[0]) || a[1].timestamp || 0;
            const bTime = getLatestVideoTimestamp(b[0]) || b[1].timestamp || 0;
            return bTime - aTime;
        })
        .forEach(([key, value]) => { resolvedMetadata[key] = value; });

    res.render("index", {
        channels: enhancedChannels,
        channelNames: Array.from(videoLibrary.keys()),
        animeMetadata: resolvedMetadata,
        synonyms: Object.fromEntries(synonymMap),
        latestAnime: latestAnimeEntries,
        formatDisplayName: formatDisplayName
    });
});

app.get("/api/status", (req, res) => {
    const botStatuses = {};
    for (const [botId, status] of botStatus.entries()) {
        botStatuses[botId] = {
            connected: status.connected,
            lastActivity: status.lastActivity,
            channelsCached: status.channelsCached,
            user: status.user
        };
    }

    res.json({
        server: "running",
        bots: botStatuses,
        uptime: process.uptime(),
        channels: videoLibrary.size,
        videos: Array.from(videoLibrary.values()).reduce((sum, v) => sum + v.length, 0),
        anime_with_metadata: animeMetadata.size,
        cache_distribution: Object.fromEntries(cacheDistribution),
        latest_anime: latestAnimeEntries
    });
});

app.get("/api/search", (req, res) => {
    const query = req.query.q?.toLowerCase() || "";

    if (!query) {
        return res.json([]);
    }

    const expandedTerms = expandSearchQuery(query);

    const channelResults = Array.from(videoLibrary.keys())
        .filter(name => {
            if (!name || typeof name !== 'string') return false;

            const nameLower = name.toLowerCase();
            const nameAlpha = nameLower.replace(/[^a-z0-9]/g, '');
            return expandedTerms.some(term => {
                const termAlpha = term.replace(/[^a-z0-9]/g, '');
                return nameLower.includes(term) || term.includes(nameLower) ||
                       nameAlpha.includes(termAlpha) || termAlpha.includes(nameAlpha);
            });
        })
        .map(name => {
            const meta = animeMetadata.get(name);
            if (!meta) {
                for (const [metaKey, metaVal] of animeMetadata.entries()) {
                    const metaAlpha = metaKey.replace(/[^a-z0-9]/g, '');
                    const nameAlpha = name.toLowerCase().replace(/[^a-z0-9]/g, '');
                    if (metaAlpha === nameAlpha) {
                        return {
                            name: metaKey,
                            displayName: metaVal.name,
                            videoCount: videoLibrary.get(name).length,
                            firstVideo: videoLibrary.get(name)[0],
                            cachedBy: cacheDistribution.get(name),
                            matchType: 'channel',
                            isLatest: latestAnimeEntries.some(entry => entry.channelName === metaKey)
                        };
                    }
                }
            }
            return {
                name: name,
                displayName: formatDisplayName(name, meta),
                videoCount: videoLibrary.get(name).length,
                firstVideo: videoLibrary.get(name)[0],
                cachedBy: cacheDistribution.get(name),
                matchType: 'channel',
                isLatest: latestAnimeEntries.some(entry => entry.channelName === name)
            };
        });

    const metadataResults = Array.from(animeMetadata.entries())
        .filter(([channelName, metadata]) => {
            if (!metadata || !metadata.name) return false;

            const metadataNameLower = metadata.name.toLowerCase();
            return expandedTerms.some(term => {
                return metadataNameLower.includes(term) || 
                       term.includes(metadataNameLower) ||
                       (metadata.searchTerms && metadata.searchTerms.some(t => 
                           t.includes(term) || term.includes(t)
                       ));
            });
        })
        .map(([channelName, metadata]) => ({
            name: channelName,
            displayName: metadata.name,
            videoCount: videoLibrary.get(channelName)?.length || 0,
            firstVideo: videoLibrary.get(channelName)?.[0],
            cachedBy: cacheDistribution.get(channelName),
            metadata: metadata,
            matchType: 'metadata',
            isLatest: latestAnimeEntries.some(entry => entry.channelName === channelName)
        }));

    const combinedResults = [...metadataResults, ...channelResults];
    const seen = new Map();
    const uniqueResults = [];

    function normalizeSeasonFormat(name) {
        let n = name.toLowerCase().replace(/[^a-z0-9\s]/g, '').trim();
        n = n.replace(/\b(\d+)(st|nd|rd|th)\s*season\b/g, 'season$1');
        n = n.replace(/\bseason\s*(\d+)\b/g, 'season$1');
        n = n.replace(/\bs(\d+)\b/g, 'season$1');
        n = n.replace(/\s+(\d+)$/, ' season$1');
        return n.replace(/[^a-z0-9]/g, '');
    }

    for (const item of combinedResults) {
        const dedupKey = normalizeSeasonFormat(item.displayName || item.name);
        if (!seen.has(dedupKey)) {
            seen.set(dedupKey, true);
            uniqueResults.push(item);
        }
    }

    const queryAlpha = query.replace(/[^a-z0-9]/g, '');
    uniqueResults.sort((a, b) => {
        const aName = (a.displayName || a.name).toLowerCase().replace(/[^a-z0-9]/g, '');
        const bName = (b.displayName || b.name).toLowerCase().replace(/[^a-z0-9]/g, '');
        const aExact = aName === queryAlpha ? 1 : 0;
        const bExact = bName === queryAlpha ? 1 : 0;
        if (aExact !== bExact) return bExact - aExact;
        const aStarts = aName.startsWith(queryAlpha) ? 1 : 0;
        const bStarts = bName.startsWith(queryAlpha) ? 1 : 0;
        if (aStarts !== bStarts) return bStarts - aStarts;
        if (a.isLatest && !b.isLatest) return -1;
        if (!a.isLatest && b.isLatest) return 1;
        return (b.videoCount || 0) - (a.videoCount || 0);
    });

    res.json(uniqueResults);
});

app.get("/api/channel/:name", async (req, res) => {
    const channelName = req.params.name;

    let videos = videoLibrary.get(channelName);
    let resolvedName = channelName;

    if (!videos) {
        const convertedName = titleToChannelName(channelName);
        if (convertedName !== channelName) {
            videos = videoLibrary.get(convertedName);
            if (videos) resolvedName = convertedName;
        }
    }

    if (!videos) {
        const foundName = findChannelByTitle(channelName);
        if (foundName) {
            videos = videoLibrary.get(foundName);
            resolvedName = foundName;
        }
    }

    if (!videos) {
        return res.status(404).json({ error: "Channel not found" });
    }

    const isLatest = latestAnimeEntries.some(entry => entry.channelName === resolvedName);
    const metadata = findMetadataForChannel(resolvedName);

    const animeName = metadata?.name || formatDisplayName(resolvedName, metadata);
    const cacheKey = animeName.toLowerCase().replace(/[^a-z0-9]/g, '');
    const cachedTmdb = tmdbCache.get(cacheKey);

    let tmdbData = cachedTmdb !== undefined ? cachedTmdb : null;
    if (cachedTmdb === undefined) {
        try {
            tmdbData = await fetchTMDBEpisodes(animeName);
        } catch (err) {}
    }

    const tmdbEpisodes = tmdbData?.episodes || null;
    const tmdbShowInfo = tmdbData?.showInfo || null;

    const enrichedVideos = videos.map(v => {
        const epNum = v.episode || 0;
        const tmdb = tmdbEpisodes && tmdbEpisodes[epNum];
        return {
            ...v,
            tmdbThumbnail: tmdb?.thumbnail || null,
            tmdbTitle: tmdb?.title || null,
            tmdbDescription: tmdb?.description || null
        };
    });

    res.json({
        channel: channelName,
        displayName: formatDisplayName(resolvedName, metadata),
        cachedBy: cacheDistribution.get(channelName),
        videos: enrichedVideos,
        isLatest: isLatest,
        latestRank: isLatest ? latestAnimeEntries.findIndex(entry => entry.channelName === channelName) + 1 : null,
        metadata: metadata,
        tmdbShowInfo: tmdbShowInfo
    });
});

// ============================================
// SOCKET.IO
// ============================================

let lastLibraryHash = '';
let cachedSocketMeta = null;
let cachedSocketMetaTime = 0;

io.on("connection", (socket) => {
    console.log("👤 Client connected");

    const channelKeys = Array.from(videoLibrary.keys());
    socket.emit("library-update", {
        channels: channelKeys,
        latestAnime: latestAnimeEntries
    });

    const now = Date.now();
    if (!cachedSocketMeta || now - cachedSocketMetaTime > 30000) {
        const resolvedMeta = Object.fromEntries(animeMetadata);
        const sortedChannels = getSortedChannelList();
        for (const channel of sortedChannels) {
            if (!resolvedMeta[channel]) {
                const found = findMetadataForChannel(channel);
                if (found) resolvedMeta[channel] = found;
            }
        }
        cachedSocketMeta = {
            metadata: resolvedMeta,
            synonyms: Object.fromEntries(synonymMap)
        };
        cachedSocketMetaTime = now;
    }

    socket.emit("metadata-update", cachedSocketMeta);

    socket.on("disconnect", () => {
        console.log("👤 Client disconnected");
    });
});

// ============================================
// START SERVER
// ============================================

const PORT = process.env.PORT || 5000;
server.listen(PORT, "0.0.0.0", async () => {
    console.log(`🌐 Server running on http://localhost:${PORT}`);
    await initializeAllBots();
    scheduleBotRestarts();
});

async function gracefulShutdown(signal) {
    console.log(`📴 ${signal} received, shutting down gracefully...`);

    for (const timer of botRestartTimers.values()) {
        clearTimeout(timer);
    }

    for (const [botId, client] of botClients.entries()) {
        console.log(`🛑 Destroying bot ${botId}...`);
        try {
            await client.destroy();
        } catch (error) {
            console.error(`❌ Error destroying bot ${botId}:`, error.message);
        }
    }

    server.close(() => {
        console.log('✅ Server terminated');
        process.exit(0);
    });
}

process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));
process.on('SIGINT', () => gracefulShutdown('SIGINT'));

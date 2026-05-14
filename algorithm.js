// algorithm.js — NYT Strands Generator Worker
'use strict';

const MAX_WORDS = 20;
let difficultyMode = 'medium';
let globalResults = [];
let startTime = 0;

let numWords = 0;
let wordObjects = [];
let wordLens = new Int8Array(MAX_WORDS);
let wordString = "";
const DP_MASKS = new BigInt64Array(MAX_WORDS);

let NEIGHBORS = [];
const CROSSING_INFO = new Int16Array(48 * 48);

// The Kill Switch Tracker
let themeBacktracks = 0;
const SPANGRAM_ABORT_LIMIT = 1000; 

// ============================================================================
// Initialization
// ============================================================================

function initNeighbors(diff) {
    NEIGHBORS = new Array(48);
    for (let i = 0; i < 48; i++) {
        let nbs = [];
        let r = Math.floor(i / 6), c = i % 6;
        for (let dr = -1; dr <= 1; dr++) {
            for (let dc = -1; dc <= 1; dc++) {
                if (dr === 0 && dc === 0) continue;
                if (diff === 'easy' && (dr !== 0 && dc !== 0)) continue; 
                let nr = r + dr, nc = c + dc;
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 6) nbs.push(nr * 6 + nc);
            }
        }
        NEIGHBORS[i] = new Int8Array(nbs);
    }
}

function initCrossings() {
    CROSSING_INFO.fill(-1);
    for (let r = 0; r < 7; r++) {
        for (let c = 0; c < 5; c++) {
            let tl = r * 6 + c, tr = r * 6 + c + 1;
            let bl = (r + 1) * 6 + c, br = (r + 1) * 6 + c + 1;
            let slot = r * 6 + c;
            
            CROSSING_INFO[tl * 48 + br] = (slot << 2) | 1;
            CROSSING_INFO[br * 48 + tl] = (slot << 2) | 1;
            CROSSING_INFO[tr * 48 + bl] = (slot << 2) | 2;
            CROSSING_INFO[bl * 48 + tr] = (slot << 2) | 2;
        }
    }
}

// ============================================================================
// Logic Helpers
// ============================================================================

function doesSpangramSpan(path) {
    let top = false, bot = false, left = false, right = false;
    for (let i = 0; i < path.length; i++) {
        let idx = path[i];
        if (idx < 6) top = true;
        if (idx >= 42) bot = true;
        if (idx % 6 === 0) left = true;
        if (idx % 6 === 5) right = true;
    }
    return (top && bot) || (left && right);
}

const q = new Int8Array(48);
// FIX: Was Uint8Array(48) — overflowed to 0 at islandToken=256, causing
// the flood-fill to re-enqueue already-visited cells, blowing past q[48]
// and crashing the Web Worker with a silent TypeError.
const visitedIsland = new Int32Array(48);
let islandToken = 0;

// Lightning Fast DP Island Pruning (Only runs when a word finishes)
function checkIslandsFast(wordIdx, used) {
    islandToken++;
    let dp = DP_MASKS[wordIdx];

    for (let i = 0; i < 48; i++) {
        if (used[i] === 0 && visitedIsland[i] !== islandToken) {
            let head = 0, tail = 0;
            q[tail++] = i;
            visitedIsland[i] = islandToken;
            
            while (head < tail) {
                let cur = q[head++];
                let nbs = NEIGHBORS[cur];
                for (let j = 0; j < nbs.length; j++) {
                    let nb = nbs[j];
                    if (used[nb] === 0 && visitedIsland[nb] !== islandToken) {
                        visitedIsland[nb] = islandToken;
                        q[tail++] = nb;
                    }
                }
            }
            
            // If the size of this empty pocket cannot be filled by any mathematical 
            // combination of the remaining theme words, instantly flag as false.
            let size = tail;
            if ((dp & (1n << BigInt(size))) === 0n) return false;
        }
    }
    return true;
}

function isUnambiguous(gridLetters) {
    for (let w = 0; w < numWords; w++) {
        let word = wordObjects[w].word;
        let len = wordLens[w];
        let foundMasks = [];
        
        function findWord(charIdx, currentCell, vMask) {
            if (foundMasks.length > 1 && foundMasks[0] !== foundMasks[1]) return;
            if (charIdx === len) {
                let isDup = false;
                for(let m = 0; m < foundMasks.length; m++) if (foundMasks[m] === vMask) isDup = true;
                if (!isDup) foundMasks.push(vMask);
                return;
            }
            let targetChar = word.charCodeAt(charIdx);
            let nbs = NEIGHBORS[currentCell];
            for(let i = 0; i < nbs.length; i++) {
                let nb = nbs[i];
                if (gridLetters[nb] === targetChar && (vMask & (1n << BigInt(nb))) === 0n) {
                    findWord(charIdx + 1, nb, vMask | (1n << BigInt(nb)));
                }
            }
        }
        
        let firstChar = word.charCodeAt(0);
        for(let i = 0; i < 48; i++) {
            if (gridLetters[i] === firstChar) {
                findWord(1, i, 1n << BigInt(i));
                if (foundMasks.length > 1 && foundMasks[0] !== foundMasks[1]) return false;
            }
        }
        if (foundMasks.length > 1 && foundMasks[0] !== foundMasks[1]) return false;
    }
    return true;
}

// ============================================================================
// Core Solver Engine
// ============================================================================

function solveDFS(wordIdx, charIdx, pathIdx, used, path, crossings, gridLetters) {
    // 10 Second Maximum Timeout. Browser will never hang.
    if (Date.now() - startTime > 10000) return "TIMEOUT"; 
    if (globalResults.length >= 10) return "DONE"; 

    // THE KILL SWITCH: If Theme Words are struggling, abort the Spangram.
    if (wordIdx > 0) {
        themeBacktracks++;
        if (themeBacktracks > SPANGRAM_ABORT_LIMIT) return "BAD_SPANGRAM";
    }

    if (wordIdx === numWords) {
        if (isUnambiguous(gridLetters)) {
            saveSolution(path);
            return "DONE"; // Triggers a total board reset for the next variation
        }
        return "CONTINUE";
    }

    let wLen = wordLens[wordIdx];
    
    // Finished placing a word
    if (charIdx === wLen) {
        if (wordIdx === 0 && !doesSpangramSpan(path.slice(0, wLen))) return "CONTINUE";
        if (!checkIslandsFast(wordIdx, used)) return "CONTINUE"; 

        // Reset the tracker because we have a mathematically viable Spangram
        if (wordIdx === 0) themeBacktracks = 0; 
        
        let res = solveDFS(wordIdx + 1, 0, pathIdx, used, path, crossings, gridLetters);
        
        if (res === "DONE") return "DONE";
        if (res === "TIMEOUT") return "TIMEOUT";
        
        // If theme words failed, bubble the error up UNLESS we are the Spangram, 
        // in which case we swallow the error, erase the Spangram, and try a new shape.
        if (res === "BAD_SPANGRAM" && wordIdx > 0) return "BAD_SPANGRAM";
        
        return "CONTINUE";
    }

    let cands = [];
    // User's Quadrant Forcing Idea: Calculate phase based on how many boards are done.
    let phase = Math.min(Math.floor(globalResults.length / 2), 4); 

    if (charIdx === 0) {
        for (let i = 0; i < 48; i++) {
            if (used[i] === 0) {
                let nbs = NEIGHBORS[i], freeNbs = 0;
                for (let j = 0; j < nbs.length; j++) if (used[nbs[j]] === 0) freeNbs++;
                
                let penalty = 0;
                if (wordIdx === 0) {
                    let r = Math.floor(i / 6), c = i % 6;
                    if (phase === 0) penalty = c * 5;           // Hug Left
                    else if (phase === 1) penalty = (5 - c) * 5;  // Hug Right
                    else if (phase === 2) penalty = Math.abs(c - 2.5) * 5; // Hug Center
                    else if (phase === 3) penalty = r * 5;        // Hug Top
                    else if (phase === 4) penalty = (7 - r) * 5;  // Hug Bottom
                }
                cands.push({ pos: i, score: freeNbs + penalty + Math.random() });
            }
        }
    } else {
        let prevPos = path[pathIdx - 1];
        let nbs = NEIGHBORS[prevPos];
        for (let j = 0; j < nbs.length; j++) {
            let nb = nbs[j];
            if (used[nb] === 0) {
                if (difficultyMode === 'medium') {
                    let info = CROSSING_INFO[prevPos * 48 + nb];
                    if (info !== -1) {
                        let slot = info >> 2, type = info & 3;
                        if (crossings[slot] !== 0 && crossings[slot] !== type) continue;
                    }
                }
                let nb_nbs = NEIGHBORS[nb], freeNbs = 0;
                for (let k = 0; k < nb_nbs.length; k++) if (used[nb_nbs[k]] === 0) freeNbs++;
                
                cands.push({ pos: nb, score: freeNbs + Math.random() });
            }
        }
    }

    cands.sort((a, b) => a.score - b.score);
    let letterCode = wordString.charCodeAt(pathIdx);

    for (let i = 0; i < cands.length; i++) {
        let pos = cands[i].pos;
        
        used[pos] = 1;
        gridLetters[pos] = letterCode;
        path[pathIdx] = pos;

        let cSlot = -1;
        if (difficultyMode === 'medium' && charIdx > 0) {
            let info = CROSSING_INFO[path[pathIdx - 1] * 48 + pos];
            if (info !== -1) {
                let slot = info >> 2, type = info & 3;
                if (crossings[slot] === 0) {
                    crossings[slot] = type;
                    cSlot = slot;
                }
            }
        }

        let res = solveDFS(wordIdx, charIdx + 1, pathIdx + 1, used, path, crossings, gridLetters);

        used[pos] = 0;
        gridLetters[pos] = 0;
        if (cSlot !== -1) crossings[cSlot] = 0;

        if (res === "DONE") return "DONE";
        if (res === "TIMEOUT") return "TIMEOUT";
        if (res === "BAD_SPANGRAM" && wordIdx > 0) return "BAD_SPANGRAM";
    }
    return "CONTINUE";
}

function saveSolution(finalPath) {
    let formatted = new Array(numWords);
    let pIndex = 0;
    for(let w = 0; w < numWords; w++) {
        let len = wordLens[w];
        let wPath = [];
        for(let c = 0; c < len; c++) wPath.push(finalPath[pIndex++]);
        formatted[wordObjects[w].originalIdx] = wPath;
    }
    
    let key = JSON.stringify(formatted);
    for(let r = 0; r < globalResults.length; r++) {
        if(JSON.stringify(globalResults[r]) === key) return;
    }
    globalResults.push(formatted);
}

// ============================================================================
// Worker Initialization
// ============================================================================

self.onmessage = function (e) {
    const { words, difficulty } = e.data;
    difficultyMode = difficulty;
    
    initNeighbors(difficultyMode);
    initCrossings();

    let mappedWords = words.map((w, idx) => ({
        originalIdx: idx,
        word: w.replace(/\s/g, '').toUpperCase(),
        isSpangram: idx === 0
    }));

    let spangramObj = mappedWords[0];
    let originalOthers = mappedWords.slice(1);

    globalResults = [];
    startTime = Date.now();

    while (globalResults.length < 10 && (Date.now() - startTime) < 10000) {
        let used = new Uint8Array(48);
        let path = new Int8Array(48);
        let crossings = new Int8Array(35);
        let gridLetters = new Uint8Array(48);
        themeBacktracks = 0;

        // Shuffle Theme Words so packing logic varies
        let others = [...originalOthers];
        others.sort(() => Math.random() - 0.5);
        wordObjects = [spangramObj, ...others];

        numWords = wordObjects.length;
        wordString = "";
        
        for (let i = 0; i < numWords; i++) {
            wordLens[i] = wordObjects[i].word.length;
            wordString += wordObjects[i].word;
        }

        // DP Island Masks for the current word order
        for (let i = 0; i < numWords; i++) {
            let mask = 1n;
            for(let j = i + 1; j < numWords; j++) mask |= (mask << BigInt(wordLens[j]));
            DP_MASKS[i] = mask;
        }

        solveDFS(0, 0, 0, used, path, crossings, gridLetters);
    }

    self.postMessage({ results: globalResults, exhausted: globalResults.length === 0 });
};
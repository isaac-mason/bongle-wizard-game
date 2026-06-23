import {
    AabbBodyMotionType,
    AabbBodyTrait,
    aabbBody,
    addChild,
    addCharacter,
    addTrait,
    assignAvatar,
    loadAvatar,
    randomDisplayName,
    releaseAvatar,
    sampleAvatars,
    BLOCK_AIR,
    broadcast,
    chat,
    CharacterControllerTrait,
    CharacterTrait,
    CLIENT_TO_SERVER,
    cloneModel,
    command,
    createNode,
    createVoxelRaycastResult,
    destroyNode,
    draw,
    ENVIRONMENT_OVERWORLD,
    env,
    findByName,
    findChildByName,
    getBlock,
    getBlockState,
    getCanvasTouches,
    getControlNode,
    getTrait,
    getWorldMatrix,
    getWorldPosition,
    getWorldQuaternion,
    HtmlTrait,
    isMobile,
    isMouseDown,
    listen,
    MeshTrait,
    matchmaking,
    model,
    type Node,
    onDispose,
    onFrame,
    onInit,
    onJoin,
    onPostAnimate,
    onTick,
    PlayerControllerTrait,
    PlayerTrait,
    pack,
    type ParticleHandle,
    particleUpdate,
    playAt,
    playMono,
    query,
    raycastVoxels,
    removeTrait,
    resolveCamera,
    rooms,
    script,
    type ScriptContext,
    send,
    SERVER_TO_CLIENT,
    sprite,
    setBlock,
    setEnvironment,
    setEnvironmentTime,
    setMeshFlash,
    setMeshGlow,
    setMeshLitMin,
    setMeshTint,
    setPosition,
    sound,
    setQuaternion,
    setScale,
    setWorldPosition,
    setWorldQuaternion,
    spawnParticle,
    type SpriteHandle,
    SpriteTrait,
    sync,
    TransformTrait,
    trait,
    type TraitType,
    traverse,
    UILayer,
    use,
    voxelNav,
    WorldTrait,
} from 'bongle';
import { RIG_6BONE_ARM_RIGHT, RIG_6BONE_HAND_RIGHT, RIG_6BONE_HEAD } from 'bongle/avatar/rig';
import { blocks, particlePresets, sounds } from 'bongle/starter';
import { floodFillGround } from './nav';
import { degreesToRadians, mat4, quat, type Quat, vec3, type Vec3, type Vec4 } from 'mathcat';
import { castRay, CastRayStatus, createClosestCastRayCollector, createDefaultCastRaySettings, filter as crashFilter } from 'crashcat';

matchmaking({ maxPlayers: 32 });

use(blocks);

const wizardModels = model('wizard-assets', {
    src: 'assets/wizard-game-assets.gltf',
});

script(WorldTrait, 'environment', (ctx) => {
    setEnvironment(ctx, ENVIRONMENT_OVERWORLD);
    setEnvironmentTime(ctx, 14);
});

// ── world generation ────────────────────────────────────────────────
// the arena is a seeded fractal-noise heightmap. the analytic surface height is the
// shared source of truth — spawn placement, gems, and NPCs all snap to the ground
// through it; the `worldgen` script below paints that heightmap into voxels. fully
// deterministic from SEED, so every room (each round's rooms.recreate) rebuilds the
// identical map and server + client agree.

// arena dimensions: a square [0, MAP_SIZE) in x/z, play centred on MAP_CENTER, y up from 0.
const MAP_SIZE = 128;
const MAP_CENTER: [number, number] = [MAP_SIZE / 2, MAP_SIZE / 2];

// heightmap tunables.
const SEED = 1337; // hardcoded — change for a different map
const BASE_HEIGHT = 10; // ground floor — lowest valley surface
const HILL_AMP = 12; // peak-to-valley swing added by the noise
const NOISE_SCALE = 44; // blocks per noise lattice cell — bigger = broader hills
const OCTAVES = 4; // fractal detail layers
const PERSISTENCE = 0.5; // amplitude falloff per octave
const LACUNARITY = 2; // frequency growth per octave

// integer lattice hash → [0,1). pure function of (ix, iz, salt) — no global state,
// so sampling order never affects the result.
function hash2(ix: number, iz: number, salt: number): number {
    let h = (Math.imul(ix | 0, 0x27d4eb2d) ^ Math.imul(iz | 0, 0x85ebca6b) ^ Math.imul(salt | 0, 0xc2b2ae35)) >>> 0;
    h = Math.imul(h ^ (h >>> 15), 0x2c1b3c6d) >>> 0;
    h = Math.imul(h ^ (h >>> 13), 0x297a2d39) >>> 0;
    return ((h ^ (h >>> 16)) >>> 0) / 0x1_0000_0000;
}

// quintic smoothstep (Perlin's fade) for C2-continuous interpolation.
const fade = (t: number): number => t * t * t * (t * (t * 6 - 15) + 10);

// bilinearly-interpolated value noise at (x, z) on the integer lattice.
function valueNoise(x: number, z: number, salt: number): number {
    const x0 = Math.floor(x);
    const z0 = Math.floor(z);
    const u = fade(x - x0);
    const v = fade(z - z0);
    const v00 = hash2(x0, z0, salt);
    const v10 = hash2(x0 + 1, z0, salt);
    const v01 = hash2(x0, z0 + 1, salt);
    const v11 = hash2(x0 + 1, z0 + 1, salt);
    const a = v00 + (v10 - v00) * u;
    const b = v01 + (v11 - v01) * u;
    return a + (b - a) * v;
}

// fractal sum of octaves, normalised to [0,1).
function fbm(x: number, z: number): number {
    let amplitude = 1;
    let frequency = 1;
    let sum = 0;
    let norm = 0;
    for (let o = 0; o < OCTAVES; o++) {
        sum += amplitude * valueNoise(x * frequency, z * frequency, SEED + o * 101);
        norm += amplitude;
        amplitude *= PERSISTENCE;
        frequency *= LACUNARITY;
    }
    return sum / norm;
}

// surface height (top grass y) at a column — the single source of truth for where
// the ground sits, so spawns can snap to it.
function surfaceHeight(x: number, z: number): number {
    return Math.floor(BASE_HEIGHT + fbm(x / NOISE_SCALE, z / NOISE_SCALE) * HILL_AMP);
}

// the canonical "what y is the ground at (x, z)?" for any spawn decision. raycasts
// down through the live voxels — so it sees trees + (later) stamped structures, not
// just the noise — and returns the surface y. falls back to the analytic height if
// the ray finds nothing (off the map, or before terrain exists). the probe starts
// above all terrain and crucially NOT on a chunk boundary: a y multiple of 16 makes
// the DDA's first exit test resolve to t=0 → an immediate false miss.
const _groundRay = createVoxelRaycastResult();
const GROUND_PROBE_Y = 200.5;
const GROUND_PROBE_DIST = 260;
function groundHeightAt(ctx: ScriptContext, x: number, z: number): number {
    raycastVoxels(_groundRay, ctx.voxels, ctx.voxels.registry, x, GROUND_PROBE_Y, z, 0, -1, 0, GROUND_PROBE_DIST, 0);
    return _groundRay.hit ? _groundRay.py : surfaceHeight(x, z) + 1;
}

// the terrain pass — paints the heightmap into voxels (stone → dirt → grass, a light
// plant scatter, and a sparse oak forest). registers BEFORE the gem + npc spawn
// onInits (which raycast the ground), so it must come first. server-only; the voxel
// edits replicate to clients automatically. the block palette + scatter/tree knobs
// live in this scope since nothing outside generation needs them.
script(WorldTrait, 'worldgen', (ctx) => {
    if (!env.server) return;

    // resolved block keys (defaultKey, not raw strings).
    const STONE = blocks.stone.defaultKey();
    const DIRT = blocks.dirt.defaultKey();
    const GRASS = blocks.grass.defaultKey();
    const LOG = blocks.oakLog.defaultKey();
    const LEAVES = blocks.oakLeaves.defaultKey();
    const DIRT_DEPTH = 3; // dirt layers between the grass cap and stone

    // surface scatter chances (per grass cell), rolled from the same seed.
    const SCATTER = [
        { key: blocks.grassPlant1.defaultKey(), chance: 0.06 },
        { key: blocks.grassPlant2.defaultKey(), chance: 0.03 },
        { key: blocks.mushroomRed.defaultKey(), chance: 0.004 },
    ] as const;

    // trees — one candidate per TREE_GRID×TREE_GRID cell (so trunks never touch),
    // grown with probability TREE_CHANCE at a hash-jittered spot in the cell.
    const TREE_GRID = 10; // cell size in blocks — also the minimum trunk spacing
    const TREE_CHANCE = 0.2; // fraction of cells that actually grow a tree
    const TREE_MIN_H = 4; // shortest trunk
    const TREE_MAX_H = 6; // tallest trunk
    const TREE_MARGIN = 3; // keep trunks this far from the map edge (canopy fits)
    const SPAWN_CLEAR = 8; // radius around MAP_CENTER kept tree-free for spawns

    // grow one oak at column (bx, bz): a trunk rising from the surface + a small leaf
    // canopy, both deterministic from the column + seed so the forest is identical
    // every run.
    const placeTree = (bx: number, bz: number): void => {
        const base = surfaceHeight(bx, bz);
        const trunkH = TREE_MIN_H + Math.floor(hash2(bx, bz, SEED ^ 0x7a3) * (TREE_MAX_H - TREE_MIN_H + 1));
        const topY = base + trunkH; // y of the topmost trunk log

        for (let y = base + 1; y <= topY; y++) setBlock(ctx.voxels, bx, y, bz, LOG);

        // canopy: two wide layers (radius 2, clipped corners) under two narrow ones,
        // capped by a plus. the trunk column stays clear up to the top log.
        for (let dy = -2; dy <= 1; dy++) {
            const y = topY + dy;
            const r = dy <= -1 ? 2 : 1;
            for (let dx = -r; dx <= r; dx++) {
                for (let dz = -r; dz <= r; dz++) {
                    if (dx === 0 && dz === 0 && dy <= 0) continue; // don't bury the trunk
                    if (r === 2 && Math.abs(dx) === 2 && Math.abs(dz) === 2) continue; // clip corners
                    if (dy === 1 && Math.abs(dx) + Math.abs(dz) > 1) continue; // plus-shaped cap
                    setBlock(ctx.voxels, bx + dx, y, bz + dz, LEAVES);
                }
            }
        }
    };

    onInit(ctx, () => {
        const voxels = ctx.voxels;
        // fill the whole arena: a stone column up to the dirt band, the dirt band, a
        // grass cap, then a scattered plant on top.
        for (let x = 0; x < MAP_SIZE; x++) {
            for (let z = 0; z < MAP_SIZE; z++) {
                const top = surfaceHeight(x, z);
                const dirtFrom = top - DIRT_DEPTH;
                for (let y = 0; y < top; y++) {
                    setBlock(voxels, x, y, z, y >= dirtFrom ? DIRT : STONE);
                }
                setBlock(voxels, x, top, z, GRASS);

                // surface scatter — first matching roll wins, so chances don't stack.
                const roll = hash2(x, z, SEED ^ 0x5f5f);
                let acc = 0;
                for (const { key, chance } of SCATTER) {
                    acc += chance;
                    if (roll < acc) {
                        setBlock(voxels, x, top + 1, z, key);
                        break;
                    }
                }
            }
        }

        // forest pass: one hash-jittered candidate per grid cell, grown with
        // probability TREE_CHANCE; the grid guarantees a minimum trunk spacing.
        for (let cz = 0; cz < MAP_SIZE; cz += TREE_GRID) {
            for (let cx = 0; cx < MAP_SIZE; cx += TREE_GRID) {
                if (hash2(cx, cz, SEED ^ 0x2ee) >= TREE_CHANCE) continue;
                const jx = cx + 1 + Math.floor(hash2(cx, cz, SEED ^ 0x111) * (TREE_GRID - 2));
                const jz = cz + 1 + Math.floor(hash2(cx, cz, SEED ^ 0x222) * (TREE_GRID - 2));
                if (jx < TREE_MARGIN || jx >= MAP_SIZE - TREE_MARGIN || jz < TREE_MARGIN || jz >= MAP_SIZE - TREE_MARGIN) continue;
                // keep the centre spawn clearing tree-free so players/npcs don't spawn in a trunk.
                const dxC = jx - MAP_CENTER[0];
                const dzC = jz - MAP_CENTER[1];
                if (dxC * dxC + dzC * dzC < SPAWN_CLEAR * SPAWN_CLEAR) continue;
                placeTree(jx, jz);
            }
        }
    });
});

// ─────────────────────────────────────────────────────────────────────
// combat core — one server-authoritative projectile, no elements yet.
//
// flow: click → Cast{dir} → server spawns a projectile node (auto-
// replicates) → server integrates + collides each tick → on hit it
// carves terrain + damages nearby health entities → broadcasts Impact /
// Damage / Death → clients render particle vfx. health drives regen,
// death and respawn for both players and NPC dummies.
//
// deliberately minimal: stats are hardcoded constants, the projectile
// moves analytically (no physics body, tunnel-proof), and entity hits
// are plain sphere checks. elements / tint / stat tables / status
// effects / knockback / AI all layer on top later without touching this.
// ─────────────────────────────────────────────────────────────────────

// projectile
const PROJECTILE_LIFETIME = 2.5; // s before it fizzles
const CHEST_OFFSET = 1.0; // m above a character's origin (feet) — splash-damage aim point
const EYE_HEIGHT = 1.5; // m — spawn origin above the caster's origin

// per-projectile stats, carried on the trait (set once, synced). one default for
// now; the elements / stat-table layer varies them per cast later.
type ProjectileStats = { speed: number; damage: number; damageRadius: number; terrainDamageRadius: number; knockback: number };
// gameplay rule (game-side, not engine): grass plants + mushrooms are placed
// resting on a block, so carving the block out from under one kills it too.
// matched by block key — what getBlock returns and worldgen places with.
const SUPPORTED_DECOR_KEYS = new Set<string>([
    blocks.grassPlant1.defaultKey(),
    blocks.grassPlant2.defaultKey(),
    blocks.mushroomRed.defaultKey(),
]);
const KNOCKBACK_UP = 0.4; // upward kick as a fraction of the horizontal impulse (pops grounded targets so the shove lands)
const KNOCKBACK_MIN_UP = 3; // m/s — floor on the upward kick so every hit lifts the target off the ground, even a weak/overhead shove
// staff tip in the staff node's local space: mesh max-Y from the gltf, with the
// node origin reset to [0,0,0] by the gear script. used to place the muzzle vfx.
const STAFF_TIP_LOCAL: Vec3 = [0, 1.0625, 0];

// ── upgradable stats (diep-style) ───────────────────────────────────
// each stat is an integer LEVEL (0..max) carried on the wizard; the effective
// value is derived here as base + level*perLevel. character stats apply to the
// wizard/controller; projectile stats snapshot into each shot at fire time.
const STAT_TABLE = {
    maxHealth: { base: 8, perLevel: 2, max: 8, label: 'Max Health', color: '#e06ec6' },
    damage: { base: 3, perLevel: 1, max: 8, label: 'Bullet Damage', color: '#e06e6e' },
    speed: { base: 18, perLevel: 3, max: 8, label: 'Bullet Speed', color: '#6e9de0' },
    // Blast: one stat, two payoffs — splash damage radius (the value below) and
    // knockback impulse (its own stronger scale, applied in projectileStatsOf).
    blast: { base: 2, perLevel: 0.5, max: 8, label: 'Blast', color: '#e0934a' },
    fireRate: { base: 1.5, perLevel: 0.6, max: 8, label: 'Fire Rate', color: '#8ce06e' },
    moveSpeed: { base: 4.317, perLevel: 0.4, max: 8, label: 'Movement Speed', color: '#6ee0d5' },
} as const;
type StatKey = keyof typeof STAT_TABLE;
const STAT_KEYS = Object.keys(STAT_TABLE) as StatKey[];
type StatLevels = Record<StatKey, number>;

// Lucide glyphs (24×24, stroke=currentColor) per stat: heart (health), sword
// (damage), fast-forward chevrons (bullet speed), concentric rings (blast),
// stopwatch (fire rate), footprints (move). the panel tints each to its stat
// colour; the collapsed rail is just icon + level.
const STAT_ICON_PATHS: Record<StatKey, string> = {
    maxHealth: '<path d="M20.42 4.58a5.4 5.4 0 0 0-7.65 0l-.77.78-.77-.78a5.4 5.4 0 0 0-7.65 0C1.46 6.7 1.33 10.28 4 13l8 8 8-8c2.67-2.72 2.54-6.3.42-8.42z"/>',
    damage: '<polyline points="14.5 17.5 3 6 3 3 6 3 17.5 14.5"/><line x1="13" x2="19" y1="19" y2="13"/><line x1="16" x2="20" y1="16" y2="20"/><line x1="19" x2="21" y1="21" y2="19"/>',
    speed: '<path d="m6 17 5-5-5-5"/><path d="m13 17 5-5-5-5"/>',
    blast: '<circle cx="12" cy="12" r="10"/><circle cx="12" cy="12" r="6"/><circle cx="12" cy="12" r="2"/>',
    fireRate: '<line x1="10" x2="14" y1="2" y2="2"/><line x1="12" x2="15" y1="14" y2="11"/><circle cx="12" cy="14" r="8"/>',
    moveSpeed:
        '<path d="M4 16v-2.38C4 11.5 2.97 10.5 3 8c.03-2.72 1.49-6 4.5-6C9.37 2 10 3.8 10 5.5c0 3.11-2 5.66-2 8.68V16a2 2 0 1 1-4 0Z"/><path d="M20 20v-2.38c0-2.12 1.03-3.12 1-5.62-.03-2.72-1.49-6-4.5-6C14.63 6 14 7.8 14 9.5c0 3.11 2 5.66 2 8.68V20a2 2 0 1 0 4 0Z"/><path d="M16 17h4"/><path d="M4 13h4"/>',
};
const statIconSvg = (key: StatKey): string =>
    `<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" style="display:block">${STAT_ICON_PATHS[key]}</svg>`;

// effective value of a stat at a given level.
const lvlValue = (key: StatKey, level: number): number => STAT_TABLE[key].base + level * STAT_TABLE[key].perLevel;
// derived effective values used at the call sites.
const maxHealthOf = (levels: StatLevels): number => lvlValue('maxHealth', levels.maxHealth);
const fireIntervalOf = (levels: StatLevels): number => 1 / lvlValue('fireRate', levels.fireRate);
// terrain destruction isn't its own stat — it's a milestone payoff of Bullet
// Damage: nothing until L3, then craters that grow with investment (capped so a
// maxed shooter is a wrecking ball, not a map-eraser).
const terrainRadiusForDamage = (damageLevel: number): number => (damageLevel >= 5 ? 2 : damageLevel >= 3 ? 1 : 0);
// knockback rides the Blast level on its own (stronger) scale — kept from the
// old standalone Knockback stat so shoves feel exactly as they did.
const BLAST_KNOCKBACK_BASE = 5;
const BLAST_KNOCKBACK_PER_LEVEL = 1.5;
const projectileStatsOf = (levels: StatLevels): ProjectileStats => ({
    speed: lvlValue('speed', levels.speed),
    damage: lvlValue('damage', levels.damage),
    damageRadius: lvlValue('blast', levels.blast),
    terrainDamageRadius: terrainRadiusForDamage(levels.damage),
    knockback: BLAST_KNOCKBACK_BASE + levels.blast * BLAST_KNOCKBACK_PER_LEVEL,
});
// the level-0 baseline shot — what an unupgraded wizard fires. derived from the stat
// table so it can't drift from the bases. used as a reference scale for the impact /
// trail vfx and as the stand-in stats on a replicated client bolt (only speed +
// damage are read there); every real shot snapshots projectileStatsOf at fire time.
const DEFAULT_PROJECTILE_STATS = projectileStatsOf({ maxHealth: 0, moveSpeed: 0, fireRate: 0, damage: 0, speed: 0, blast: 0 });

// ── xp / levels ─────────────────────────────────────────────────────
// xp accrues from orbs; each level grants one upgrade point. quadratic curve:
// reaching level L needs XP_PER_LEVEL * L^2 total xp, so each level costs more.
const XP_PER_LEVEL = 12;
const levelForXp = (xp: number): number => Math.floor(Math.sqrt(xp / XP_PER_LEVEL));
const xpForLevel = (lvl: number): number => XP_PER_LEVEL * lvl * lvl; // inverse — xp at the start of `lvl`

// level → rarity tier: a colour (hat tint + nameplate badge) and a hat scale that
// grows with level. discrete colour bands read as a power/threat tier at a glance.
const LEVEL_TIERS: { min: number; color: string }[] = [
    { min: 15, color: '#fbbf24' }, // gold
    { min: 10, color: '#a78bfa' }, // purple
    { min: 6, color: '#6e9de0' }, // blue
    { min: 3, color: '#2dd4bf' }, // teal (green blends into grass)
    { min: 0, color: '#bdbdbd' }, // gray
];
const tierColor = (level: number): string => LEVEL_TIERS.find((t) => level >= t.min)!.color;
const tierScale = (level: number): number => 1 + Math.min(level, 20) * 0.02; // 1.0 → 1.4
// '#rrggbb' → a mesh tint Vec4 (alpha 1 = full mix tint).
const hexTint = (hex: string): Vec4 => {
    const n = parseInt(hex.slice(1), 16);
    return [((n >> 16) & 255) / 255, ((n >> 8) & 255) / 255, (n & 255) / 255, 1];
};
const sumLevels = (levels: StatLevels): number => STAT_KEYS.reduce((n, k) => n + levels[k], 0);
// upgrade points still to spend = levels earned − levels allocated.
const availablePoints = (xp: number, levels: StatLevels): number => levelForXp(xp) - sumLevels(levels);

// ── health timing ───────────────────────────────────────────────────
const REGEN_DELAY = 3; // s without damage before health regenerates
const BASE_REGEN_RATE = 2; // hp/s — flat baseline regen, the same for everyone (not an upgradable stat)
const RESPAWN_DELAY = 3; // s after death before respawn

// ── xp orbs (death drops from gems + wizards) ───────────────────────
const ORB_AMOUNT = 6; // xp per orb
const ORB_LIFETIME = 60; // s — orbs despawn after this (generous; keeps uncollected litter from piling up)
const ORB_GRAB_RADIUS = 1.1; // m — an alive wizard within this collects an orb
const ORB_MAGNET_RADIUS = 5; // m — within this (but outside grab) an orb reels toward the nearest wizard
const ORB_MAGNET_PULL = 18; // m/s base — fly-in speed = (PULL − distance), so it accelerates as it nears (luanti-style)
const ORB_DROP_KEEP = 0.25; // fraction of xp the dead wizard keeps on respawn
const ORB_DROP_SCATTER = 0.5; // fraction dropped as orbs (the rest is lost)
const ORB_POP_UP = 4; // m/s — upward burst on a death-drop (physics scatters them)
const ORB_POP_OUT = 3; // m/s — horizontal burst on a death-drop
const ORB_DROP_MIN = 3; // orbs — every kill scatters at least this many, so low-xp/NPC kills still pay out

// ── gems (tiered, shootable xp sources) ─────────────────────────────
// gems are the ambient xp source (they replace free-floating litter orbs): each
// is a destructible, slowly-spinning crystal with health. shoot one to death and
// it shatters into a burst of the same magnet-collected xp orbs, proportional to
// its tier. higher tiers are bigger, tougher, and pay out more — but rarer.
type GemTier = { color: string; scale: number; halfExtent: number; health: number; xp: number; weight: number };
const GEM_TIERS: GemTier[] = [
    // ascending cool→hot ramp: azure → violet → magenta (no green=grass, no gold=xp).
    { color: '#2e9bff', scale: 0.95, halfExtent: 0.48, health: 9, xp: 12, weight: 12 }, // common — azure
    { color: '#9d5cff', scale: 1.4, halfExtent: 0.7, health: 24, xp: 36, weight: 5 }, // rare — violet
    { color: '#ff3ea5', scale: 1.85, halfExtent: 0.92, health: 60, xp: 90, weight: 1 }, // epic — magenta
];
// gems blanket the WHOLE arena at a fixed density (not a pile near spawn). the
// target scales with map area, and a minimum spacing keeps them evenly spread.
const GEM_TARGET = Math.round((MAP_SIZE * MAP_SIZE) / 420); // ≈ one gem per 420 m²
const GEM_RESPAWN_INTERVAL = 1.5; // s between litter top-ups
const GEM_MARGIN = 6; // m — keep gems this far inside the map edges
const GEM_MIN_SPACING = 12; // m — desired clearance between gems (prevents clumping)
const GEM_PLACE_TRIES = 16; // candidate samples per gem; most-isolated wins
const GEM_HOVER = 1.3; // m — float height above the ground (clears the largest tier's bob)
const GEM_HIT_MARGIN = 0.25; // m — padding on the gem's AABB so shots are forgiving to land

// weighted tier roll — commons frequent, epics rare.
const GEM_WEIGHT_TOTAL = GEM_TIERS.reduce((sum, t) => sum + t.weight, 0);
function rollGemTier(): number {
    let r = Math.random() * GEM_WEIGHT_TOTAL;
    for (let i = 0; i < GEM_TIERS.length; i++) {
        r -= GEM_TIERS[i]!.weight;
        if (r < 0) return i;
    }
    return 0;
}

// random unit-ish direction for particle bursts.
function randomDir(): Vec3 {
    const x = Math.random() * 2 - 1;
    const y = Math.random() * 2 - 1;
    const z = Math.random() * 2 - 1;
    const len = Math.hypot(x, y, z) || 1;
    return [x / len, y / len, z / len];
}

// vary a base particle lifetime ±35% so a burst doesn't all die at once.
const varyLife = (base: number): number => base * (0.65 + Math.random() * 0.7);

// reusable quats for composing a local rotation onto a base orientation — the
// projectile spin (combat-vfx) and the falling-hat tilt (health-fx).
const _rotation = quat.create();
const _orientation = quat.create();

// ── traits ──────────────────────────────────────────────────────────

// the wizard entity — every combatant (players AND npcs) is one. it folds together
// score, xp/level, stat levels, the held cast intent, and the health pool, so the
// combat systems only ever query for `WizardTrait`.
const WizardTrait = trait('wizard', {
    color: [1, 1, 1, 1] as Vec4,
    // display name + per-round score (kills/deaths). server-authored and synced
    // for the leaderboard — players AND npcs. resets each round (the trait is
    // re-created on the fresh room).
    name: '',
    kills: 0,
    deaths: 0,
    // owner-authored + replicated *held* cast intent: true while this wizard's
    // owner is holding fire — see combat-cast. drives the firing tick + arm-raise.
    casting: false,
    // xp accrued from orbs → level → upgrade points. synced for the hud + cadence.
    xp: 0,
    // upgradable stat LEVELS (integers); effective values derived via STAT_TABLE.
    // synced so the client derives fire cadence, max health, the hud panel, etc.
    stats: { levels: { maxHealth: 0, moveSpeed: 0, fireRate: 0, damage: 0, speed: 0, blast: 0 } as StatLevels },
    // live health pool (folded in — every combatant is a wizard). `current` is
    // discrete + synced; max is DERIVED from the maxHealth stat (not stored). the
    // regen carry + damage bookkeeping stay server-only.
    current: lvlValue('maxHealth', 0),
    regenAccum: 0,
    lastDamageTime: -999,
    lastAttacker: -1,
    // server-only clock of this wizard's last spawned shot — paces the firing tick.
    lastFireTime: -999,
    // client-side timestamp of the LOCAL player's own last authoritative shot — set
    // from the ProjectileCast we own (combat-vfx), drives the first-person viewmodel
    // muzzle + recoil edge. not synced.
    lastCastTime: -999,
    // eased 0..1 arm-raise amount (client-side), toward `casting`. not synced.
    armRaise: 0,
});
type WizardTrait = TraitType<typeof WizardTrait>;

sync(WizardTrait, 'color', {
    schema: pack.list(pack.float32(), 4),
    pack: (t) => t.color,
    unpack: (v, t) => (t.color = v),
    rate: 'dirty',
});

// name is set once (spawn / join); kills + deaths change at runtime, so
// 'realtime' lets the engine diff + emit them without explicit dirtying.
sync(WizardTrait, 'name', {
    schema: pack.string(),
    pack: (t) => t.name,
    unpack: (v, t) => (t.name = v),
    rate: 'dirty',
});

sync(WizardTrait, 'kills', {
    schema: pack.uint32(),
    pack: (t) => t.kills,
    unpack: (v, t) => (t.kills = v),
});

sync(WizardTrait, 'deaths', {
    schema: pack.uint32(),
    pack: (t) => t.deaths,
    unpack: (v, t) => (t.deaths = v),
});

// cast flag, owner-authored: the local player's client flips its own on/off
// (instant), the server does it for npcs — so it replicates out the same way the
// transform does. every client reads it to drive the third-person arm-raise.
sync(WizardTrait, 'casting', {
    schema: pack.boolean(),
    pack: (t) => t.casting,
    unpack: (v, t) => (t.casting = v),
    authority: 'owner',
});

// stat levels change at runtime (upgrades), so 'realtime' re-emits on byte-change.
// the client derives fire cadence + max health + the hud panel from these.
sync(WizardTrait, 'stats', {
    schema: pack.object({
        maxHealth: pack.uint8(),
        moveSpeed: pack.uint8(),
        fireRate: pack.uint8(),
        damage: pack.uint8(),
        speed: pack.uint8(),
        blast: pack.uint8(),
    }),
    pack: (t) => t.stats.levels,
    unpack: (v, t) => (t.stats.levels = v),
    rate: 'realtime',
});

sync(WizardTrait, 'xp', {
    schema: pack.uint32(),
    pack: (t) => t.xp,
    unpack: (v, t) => (t.xp = v),
    rate: 'realtime',
});

// folded-in health pool: `current` is discrete and synced for the bar; max is
// derived client-side from the maxHealth stat, so it isn't sent.
sync(WizardTrait, 'current', {
    schema: pack.float32(),
    pack: (t) => t.current,
    unpack: (v, t) => (t.current = v),
    rate: 'realtime',
});

// attach a wizard's staff + hat to its rig (server-side; the cloned nodes
// replicate down). called as each wizard appears — see wizard-visuals.
function attachGear(wizardNode: Node): void {
    const staff = cloneModel(wizardModels.nodes.staff);
    staff.name = 'wizard:staff';
    // cloneModel keeps the node's authored scene-layout transform (the staff is
    // lifted in the asset so it stands on the ground). clear it so the staff's own
    // pivot — not that layout offset — lands at the socket. identity, not a tuning
    // offset: the engine socket supplies the hand position + grip rotation.
    setPosition(getTrait(staff, TransformTrait)!, [0, 0, 0]);
    addChild(findByName(wizardNode, RIG_6BONE_HAND_RIGHT)!, staff);

    const hat = cloneModel(wizardModels.nodes.hat);
    hat.name = 'wizard:hat';
    setPosition(getTrait(hat, TransformTrait)!, [0, 0.5, 0]);
    addChild(findByName(wizardNode, RIG_6BONE_HEAD)!, hat);
}

// a live projectile. `spawnTime` / `aim` / `stats` are synced so the trait (and
// node) replicates to clients for the trail + spin visuals. `ownerId` is
// server-only. the server raycasts the bolt forward each tick (it never stores a
// velocity — it derives it from aim × stats.speed); clients only render. `aim`
// is the cast-time direction: the node faces it and rolls around it.
// projectiles are NOT replicated — they live only on the server as `realm:'server'`
// nodes, and reach clients purely through the ProjectileCast + ImpactCommand
// broadcasts. so the trait carries no `sync()` at all; it's just the server's sim
// state. `id` is a monotonic token that correlates a bolt's cast + impact across
// the wire (so a client can match an impact to the right local bolt).
const ProjectileTrait = trait('projectile', {
    id: 0,
    ownerId: -1,
    spawnTime: 0,
    aim: [0, 0, 0, 1] as Quat,
    stats: DEFAULT_PROJECTILE_STATS,
    // the spawn origin, kept so a mid-flight cast can be re-sent to a late joiner
    // (the sim transform has since advanced past it). clients derive from origin.
    origin: [0, 0, 0] as Vec3,
    // client-only: `wallSpawn` is the smooth render-clock time (`ctx.clock.wall`)
    // this bolt's flight is anchored to — set once from `ctx.clock.server` on first
    // render, then the visual advances by per-frame wall delta so motion is smooth
    // at any refresh rate (the tick clock only steps at 60Hz). -1 = not yet anchored.
    wallSpawn: -1,
});

// xp pickup. `amount` synced (dirty) so the orb node replicates to clients,
// which decorate it with a billboard sprite (SpriteTrait isn't itself synced).
// `spawnTime` is server-only (the server owns orbs) — drives the despawn timer.
const XpOrbTrait = trait('xp-orb', { amount: ORB_AMOUNT, spawnTime: 0 });
sync(XpOrbTrait, 'amount', {
    schema: pack.uint16(),
    pack: (t) => t.amount,
    unpack: (v, t) => (t.amount = v),
    rate: 'dirty',
});

// a destructible tiered gem — the ambient xp source you shoot. `tier` (synced
// once) selects scale/colour/health/payout from GEM_TIERS; `current` (synced
// dirty) drives the damage-triggered healthbar — clients derive max + "is it
// damaged?" from the tier table. there's no killer credit: the shatter drops
// orbs, and whoever magnets them in gets the xp.
const GemTrait = trait('gem', { tier: 0, current: GEM_TIERS[0]!.health });
sync(GemTrait, 'tier', {
    schema: pack.uint8(),
    pack: (t) => t.tier,
    unpack: (v, t) => (t.tier = v),
    rate: 'dirty',
});
// `current` drops every hit, so it must re-emit on change — 'realtime' diffs +
// emits without explicit dirtying (like WizardTrait.current). 'dirty' would only
// send the spawn value, so clients would never see damage and the bar never shows.
sync(GemTrait, 'current', {
    schema: pack.float32(),
    pack: (t) => t.current,
    unpack: (v, t) => (t.current = v),
    rate: 'realtime',
});

// marker: present iff the entity is alive. removed on death, re-added on
// respawn. the combat systems only touch entities that have it. (health itself
// folded onto WizardTrait — every combatant is a wizard.)
const AliveTrait = trait('alive');

// marker + respawn home for non-player targets.
const NpcTrait = trait('npc', {
    homeX: 0,
    homeY: 0,
    homeZ: 0,
    archetype: 0, // index into NPC_ARCHETYPES — its stat-allocation build (server-only)
});

// ── messages ────────────────────────────────────────────────────────

// `block` = the struck block's global state id on a terrain hit (0 = body/fizzle);
// the client uses its dust sprite for the impact.
// `id` ties the impact to the bolt that caused it so the client destroys the
// matching local bolt. broadcast to every client including the owner (no prediction).
// `radius` is the bolt's splash damageRadius (what the `blast` stat drives) — the
// client scales the impact burst by it so a bigger blast looks proportionally bigger.
const ImpactCommand = command('wizards.impact', SERVER_TO_CLIENT, pack.object({ id: pack.uint32(), pos: pack.list(pack.float32(), 3), fizzle: pack.boolean(), block: pack.uint32(), radius: pack.float32() }));
const DamageCommand = command('wizards.damage', SERVER_TO_CLIENT, pack.object({ pos: pack.list(pack.float32(), 3), amount: pack.float32(), tier: pack.int8() })); // tier ≥ 0 colours the pop as that gem; -1 for wizards
const DeathCommand = command('wizards.death', SERVER_TO_CLIENT, pack.object({ pos: pack.list(pack.float32(), 3) }));
// server → client: a gem shattered at `pos`; `tier` selects the burst colour/size.
const GemDeathCommand = command('wizards.gem-death', SERVER_TO_CLIENT, pack.object({ pos: pack.list(pack.float32(), 3), tier: pack.uint8() }));
// client → server: spend an upgrade point on the stat at index `stat` (into STAT_KEYS).
const UpgradeStat = command('wizards.upgrade', CLIENT_TO_SERVER, pack.object({ stat: pack.uint8() }));
// a projectile was cast — the entire wire footprint of a (server-simulated) bolt.
// clients derive its straight-line flight from these; `id` correlates the later
// ImpactCommand. broadcast to EVERY client including the owner — bolts are fully
// server-authoritative (no prediction), so the owner renders its own from this too.
// `ownerId` lets the owner route the muzzle/recoil to its first-person viewmodel.
const ProjectileCast = command('wizards.projectile-cast', SERVER_TO_CLIENT, pack.object({
    id: pack.uint32(),
    ownerId: pack.uint32(),
    origin: pack.list(pack.float32(), 3),
    aim: pack.list(pack.float32(), 4),
    speed: pack.float32(),
    spawnTime: pack.float64(),
    damage: pack.uint8(), // drives the bolt's visual size (purely cosmetic — collision is the raycast)
}));
// server → one client: a knockback impulse for that player's own wizard. velocity is
// owner-authored, so the client applies it to its controller and it replicates out.
const KnockbackCommand = command('wizards.knockback', SERVER_TO_CLIENT, pack.object({ impulse: pack.list(pack.float32(), 3) }));

// ── particle types (client vfx) ─────────────────────────────────────
// deliberately low-detail: instead of the starter pack's 8–16px pixel-art
// sprites we bake flat white squares procedurally (no art assets). tiny so
// the fx read as chunky pixels rather than soft puffs, white so a future
// elements layer can tint them per cast.
const whiteSprite = (id: string, size: [number, number]) =>
    sprite(id, {
        src: draw(
            (ctx) => {
                ctx.fillStyle = '#fff';
                ctx.fillRect(0, 0, size[0], size[1]);
            },
            { size },
        ),
        mipmap: false, // crisp pixels, no mushy mip blur
    });

// 1×1 smoke puff for death; 3×3 for the chunkier cast/impact spark.
const SmokeSprite = whiteSprite('wizards:smoke', [1, 1]);
const SparkSprite = whiteSprite('wizards:spark', [3, 3]);

// 2×2 trail variants: each is a different filled/empty pixel pattern, not
// just a size. pixel index k → (x = k&1, y = k>>1), so bit k of `mask` sets
// that cell. the trail picks among them deterministically per particle for
// a bit of chunky variety without any single-frame flicker.
const pattern2x2 = (id: string, mask: number) =>
    sprite(id, {
        src: draw(
            (ctx, _inputs, { mask }) => {
                ctx.fillStyle = '#fff';
                for (let k = 0; k < 4; k++) {
                    if (mask & (1 << k)) ctx.fillRect(k & 1, k >> 1, 1, 1);
                }
            },
            { size: [2, 2], params: { mask } }, // mask in params → re-bakes when edited
        ),
        mipmap: false,
    });

// a few patterns to try: single corner, the two diagonals, a triple. tweak
// this list to taste — index order doesn't matter, the pick is hashed.
const TRAIL_MASKS = [
    0b0001, // ▘ top-left
    0b1001, // ◣ main diagonal
    0b0110, // ◢ anti-diagonal
    0b0111, // ◳ triple
];
const TrailVariants = TRAIL_MASKS.map((mask, i) =>
    particlePresets.smoke(`wizards:trail-${i}`, { sprite: pattern2x2(`wizards:trail-px-${i}`, mask) }),
);

const ImpactFx = particlePresets.spark('wizards:impact', { sprite: SparkSprite });
const DeathFx = particlePresets.smoke('wizards:death', { sprite: SmokeSprite });
// glowy "gathering energy" spark, emitted continuously at the staff tip while a
// wizard channels (holds cast). white for now — the elements layer tints it later.
const ChargeFx = particlePresets.spark('wizards:charge', { sprite: SparkSprite });

// charge-glow emission rate — shared by the viewmodel + wizard-visuals tip loops
// and chargeGlow itself; the per-particle look lives inside chargeGlow.
const CHARGE_RATE = 22; // particles/s while casting

// gem shatter — a chunky spark burst baked in each tier's colour (the gems are
// flat-tinted, so a matching shard burst reads as the crystal breaking apart).
const gemShardSprite = (id: string, hex: string) =>
    sprite(id, {
        src: draw(
            (ctx) => {
                ctx.fillStyle = hex;
                ctx.fillRect(0, 0, 2, 2);
            },
            { size: [2, 2] },
        ),
        mipmap: false,
    });
const GemShatterFx = GEM_TIERS.map((t, i) => particlePresets.spark(`wizards:gem-shatter-${i}`, { sprite: gemShardSprite(`wizards:gem-shard-${i}`, t.color) }));

// small deterministic 32-bit hash (two ints in) — drives the trail variant
// pick + scatter + per-particle seed so trails are reproducible, no Math.random.
function hash32(a: number, b: number): number {
    let x = (Math.imul(a ^ 0x9e3779b9, 0x85ebca6b) ^ Math.imul(b + 1, 0xc2b2ae35)) >>> 0;
    x = Math.imul(x ^ (x >>> 15), 0x2c1b3c6d) >>> 0;
    x = Math.imul(x ^ (x >>> 13), 0x297a2d39) >>> 0;
    return (x ^ (x >>> 16)) >>> 0;
}
// hash → float in [-0.5, 0.5), re-hashed per component `k`.
const hashUnit = (h: number, k: number) => (hash32(h, k) >>> 8) / 0x100_0000 - 0.5;

// xp orb — a small two-tone green diamond, billboarded on the client.
const XpOrbSprite = sprite('wizards:xp-orb', {
    src: draw(
        (ctx, _inputs, { n }) => {
            const c = (n - 1) / 2;
            for (let y = 0; y < n; y++) {
                for (let x = 0; x < n; x++) {
                    const d = Math.abs(x - c) + Math.abs(y - c);
                    if (d > c) continue;
                    ctx.fillStyle = d <= c - 2 ? '#ffe9a8' : '#f5a623'; // light gold core, amber rim (pops on grass; green vanished)
                    ctx.fillRect(x, y, 1, 1);
                }
            }
        },
        { size: [7, 7], params: { n: 7 } },
    ),
    mipmap: false,
});

// pickup blip — VoxeLibre `mcl_item_entity` item-pickup, detuned ~6% (GPL-3.0;
// game-local, see assets/sounds/NOTICE.txt). kept out of the CC starter pack.
const PickupSound = sound('wizards:pickup', { src: 'assets/sounds/pickup.ogg' });

// ── server: spawn + simulate projectiles ────────────────────────────

// monotonic projectile id (server-only) — correlates a bolt's cast + impact.
let projectileSeq = 0;

// the ProjectileCast wire payload for a bolt — built from the live shot or a trait,
// shared by the initial broadcast and the per-joiner re-send so they can't drift.
function projectileCastPayload(p: { id: number; ownerId: number; origin: Vec3; aim: Quat; stats: ProjectileStats; spawnTime: number }) {
    return {
        id: p.id,
        ownerId: p.ownerId,
        origin: [p.origin[0], p.origin[1], p.origin[2]] as Vec3,
        aim: [p.aim[0], p.aim[1], p.aim[2], p.aim[3]] as Quat,
        speed: p.stats.speed,
        spawnTime: p.spawnTime,
        damage: p.stats.damage,
    };
}

// spawn a projectile as a `realm:'server'` node — it lives ONLY on the server (never
// replicated) and is simulated there for authoritative hit detection. its entire
// presence on clients is the `ProjectileCast`, broadcast to every client (including
// the owner); each derives the flight + builds its visual.
function spawnProjectile(ctx: ScriptContext, sceneRoot: Node, ownerNode: Node, origin: Vec3, aim: Quat, spawnTime: number, stats: ProjectileStats): void {
    const id = ++projectileSeq;
    const node = createNode({ name: 'projectile', realm: 'server' });
    const transform = addTrait(node, TransformTrait);
    setPosition(transform, origin);
    setQuaternion(transform, aim);
    addTrait(node, ProjectileTrait, {
        id,
        ownerId: ownerNode.id,
        spawnTime,
        aim: [aim[0], aim[1], aim[2], aim[3]],
        stats,
        origin: [origin[0], origin[1], origin[2]],
    });
    addChild(sceneRoot, node);

    broadcast(ctx, ProjectileCast, projectileCastPayload({ id, ownerId: ownerNode.id, origin, aim, stats, spawnTime }));
}


// ── spawn placement ──────────────────────────────────────────────────
// players + npcs spawn spread out (not piled on one point) so they don't
// spawn-die. a fresh spawn samples a few ground points near the arena centre
// and keeps the one with the most clearance from existing combatants.
const SPAWN_RING = 26; // m — radius around MAP_CENTER spawns scatter within
const SPAWN_SEP = 7; // m — clearance from others that's "good enough" to stop early
const SPAWN_LIFT = 2; // m — drop-in height above ground; gravity settles them
const SPAWN_TRIES = 24; // candidate samples per spawn

// world positions of every wizard in `wizards`, minus `exclude` (the node being
// (re)spawned) — the set a new spawn should keep clear of.
function positionsOf(wizards: ReturnType<typeof query<[typeof WizardTrait, typeof TransformTrait]>>, exclude?: number): Vec3[] {
    const out: Vec3[] = [];
    for (const [, transform] of wizards) {
        if (exclude !== undefined && transform._node.id === exclude) continue;
        const wp = getWorldPosition(transform);
        out.push([wp[0], wp[1], wp[2]]);
    }
    return out;
}

// pick a ground spawn near the arena centre, as far as possible from `occupied`.
// uniform over the spawn disc; keeps the most-separated candidate, early-outs
// once one clears SPAWN_SEP. y snaps to the ground (+ a small drop-in lift).
function pickSpawnPosition(ctx: ScriptContext, occupied: Vec3[]): Vec3 {
    let bestX = MAP_CENTER[0];
    let bestZ = MAP_CENTER[1];
    let bestClearance = -1;
    for (let i = 0; i < SPAWN_TRIES; i++) {
        const ang = Math.random() * Math.PI * 2;
        const rad = Math.sqrt(Math.random()) * SPAWN_RING; // sqrt → uniform over the disc
        const x = MAP_CENTER[0] + Math.cos(ang) * rad;
        const z = MAP_CENTER[1] + Math.sin(ang) * rad;
        let clearance = Infinity;
        for (const p of occupied) {
            const d = Math.hypot(x - p[0], z - p[2]);
            if (d < clearance) clearance = d;
        }
        if (clearance > bestClearance) {
            bestClearance = clearance;
            bestX = x;
            bestZ = z;
        }
        if (clearance >= SPAWN_SEP) break; // far enough from everyone — take it
    }
    return [bestX, groundHeightAt(ctx, bestX, bestZ) + SPAWN_LIFT, bestZ];
}

// y below which a combatant has fallen out of the world (off a map edge into the
// void) — they take lethal "fizzle" damage and respawn. terrain floors at y=0.
const KILL_Y = -8;

// spawn an xp orb as a *voxel-only* AABB body: it falls + settles on terrain
// (and bounces a touch) but passes through wizards (`collisionMask: 0`) and the
// character bodies (`rigidBodyImpostor: false`). `vel` is the initial pop —
// death-drops burst outward, litter drops in still. server-authoritative; the
// node + body replicate, the client renders the synced transform.
function spawnOrb(ctx: ScriptContext, x: number, y: number, z: number, amount: number, vel: Vec3): void {
    const node = createNode({ name: 'xp-orb' });
    setPosition(addTrait(node, TransformTrait), [x, y, z]);
    addTrait(node, XpOrbTrait, { amount, spawnTime: ctx.clock.time });
    addTrait(node, AabbBodyTrait, {
        halfExtents: [0.15, 0.15, 0.15],
        motionType: AabbBodyMotionType.DYNAMIC,
        collisionMask: 0, // no body-vs-body (other orbs, items)
        rigidBodyImpostor: false, // the character (rigid world) ignores it
        prediction: false, // server-authoritative; clients render the synced transform
        restitution: 0.3, // a little bounce on landing
        linearVelocity: vel,
    });
    addChild(ctx.node, node);
}

// spawn a tiered gem: just a node at a fixed hover position — no physics body.
// gems are hit by sweeping the projectile segment against their AABB analytically
// (see the combat-damage tick); a rigid impostor wouldn't help because ray queries
// skip the impostor layer. bodyless also means characters pass straight through for
// free. server-authoritative; the node + GemTrait replicate, and the client builds
// the spinning crystal + healthbar from the synced tier/current.
function spawnGem(ctx: ScriptContext, x: number, y: number, z: number, tier: number): void {
    const t = GEM_TIERS[tier] ?? GEM_TIERS[0]!;
    const node = createNode({ name: 'gem' });
    setPosition(addTrait(node, TransformTrait), [x, y, z]);
    addTrait(node, GemTrait, { tier, current: t.health });
    addChild(ctx.node, node);
}

// world positions of the live gems — the set a new gem should spread away from.
function gemPositions(gems: ReturnType<typeof query<[typeof GemTrait, typeof TransformTrait]>>): Vec3[] {
    const out: Vec3[] = [];
    for (const [, transform] of gems) {
        const wp = getWorldPosition(transform);
        out.push([wp[0], wp[1], wp[2]]);
    }
    return out;
}

// pick a ground spot for a new gem, spread across the WHOLE map and away from
// existing gems. samples uniformly over the (margined) arena and keeps the most-
// isolated candidate, early-outing once one clears GEM_MIN_SPACING. returns the
// full spawn position (y snapped to the surface + hover).
function pickGemSpot(ctx: ScriptContext, existing: Vec3[]): Vec3 {
    const span = MAP_SIZE - 2 * GEM_MARGIN;
    let bestX = GEM_MARGIN + Math.random() * span;
    let bestZ = GEM_MARGIN + Math.random() * span;
    let bestClearance = -1;
    for (let i = 0; i < GEM_PLACE_TRIES; i++) {
        const x = GEM_MARGIN + Math.random() * span;
        const z = GEM_MARGIN + Math.random() * span;
        let clearance = Infinity;
        for (const p of existing) {
            const d = Math.hypot(x - p[0], z - p[2]);
            if (d < clearance) clearance = d;
        }
        if (clearance > bestClearance) {
            bestClearance = clearance;
            bestX = x;
            bestZ = z;
        }
        if (clearance >= GEM_MIN_SPACING) break; // far enough from the others — take it
    }
    return [bestX, groundHeightAt(ctx, bestX, bestZ) + GEM_HOVER, bestZ];
}

// slab test: does the segment from `p` along unit dir `d` for `len` metres enter
// the axis-aligned box centred at (cx,cy,cz) with scalar half-size `half`? returns
// the entry fraction in [0,1] of the segment (0 if `p` starts inside), or -1 on a
// miss. used to shoot bodyless gems without a physics ray.
function raySegmentAabb(p: Vec3, d: Vec3, len: number, cx: number, cy: number, cz: number, half: number): number {
    let tmin = 0;
    let tmax = len;
    if (d[0] !== 0) {
        const inv = 1 / d[0];
        let t1 = (cx - half - p[0]) * inv;
        let t2 = (cx + half - p[0]) * inv;
        if (t1 > t2) [t1, t2] = [t2, t1];
        if (t1 > tmin) tmin = t1;
        if (t2 < tmax) tmax = t2;
    } else if (p[0] < cx - half || p[0] > cx + half) return -1;
    if (d[1] !== 0) {
        const inv = 1 / d[1];
        let t1 = (cy - half - p[1]) * inv;
        let t2 = (cy + half - p[1]) * inv;
        if (t1 > t2) [t1, t2] = [t2, t1];
        if (t1 > tmin) tmin = t1;
        if (t2 < tmax) tmax = t2;
    } else if (p[1] < cy - half || p[1] > cy + half) return -1;
    if (d[2] !== 0) {
        const inv = 1 / d[2];
        let t1 = (cz - half - p[2]) * inv;
        let t2 = (cz + half - p[2]) * inv;
        if (t1 > t2) [t1, t2] = [t2, t1];
        if (t1 > tmin) tmin = t1;
        if (t2 < tmax) tmax = t2;
    } else if (p[2] < cz - half || p[2] > cz + half) return -1;
    if (tmax < tmin) return -1;
    return tmin / len;
}

// the nearest thing a bolt segment hits this step: one ray against the rigid world
// (terrain voxels + every character's VCC body — both present on the SERVER and the
// CLIENT, so this runs identically on each) plus the analytical gem AABB sweep
// (gems carry no rigid body). returns the hit point + struck block (0 = body/gem),
// or null for a clean miss. shared by the server sim (→ damage) and the client's
// predicted bolts (→ impact vfx). the owner is behind its own bolt, so a hit that
// resolves to the owner is ignored ("keep flying").
function castProjectileSegment(
    ctx: ScriptContext,
    pos: Vec3,
    dir: Vec3,
    step: number,
    ownerId: number,
    gems: ReturnType<typeof query<[typeof GemTrait, typeof TransformTrait]>>,
    rayCollector: ReturnType<typeof createClosestCastRayCollector>,
    raySettings: ReturnType<typeof createDefaultCastRaySettings>,
    rayFilter: ReturnType<typeof crashFilter.forWorld>,
): { point: Vec3; block: number; cell: Vec3 } | null {
    const rigid = ctx.physics.rigid;
    rayCollector.reset();
    castRay(rigid.world, rayCollector, raySettings, pos, dir, step, rayFilter);
    const rigidHit = rayCollector.hit;
    const rigidValid = rigidHit.status === CastRayStatus.COLLIDING && rigid.bodyToNode.get(rigidHit.bodyIdB) !== ownerId;
    const tRigid = rigidValid ? rigidHit.fraction : Infinity;

    let tGem = Infinity;
    for (const [gem, gemTransform] of gems) {
        if (gem.current <= 0) continue;
        const gc = getWorldPosition(gemTransform);
        const half = (GEM_TIERS[gem.tier] ?? GEM_TIERS[0]!).halfExtent + GEM_HIT_MARGIN;
        const tHit = raySegmentAabb(pos, dir, step, gc[0], gc[1], gc[2], half);
        if (tHit >= 0 && tHit < tGem) tGem = tHit;
    }

    const t = Math.min(tRigid, tGem); // a gem ties to its own favour (block stays 0)
    if (t === Infinity) return null;
    const hx = pos[0] + dir[0] * step * t;
    const hy = pos[1] + dir[1] * step * t;
    const hz = pos[2] + dir[2] * step * t;
    // step ~0.1 past the surface along travel so we land INSIDE the struck voxel
    // (the hit point sits on the face; flooring it alone can pick the air cell in
    // front). this cell is what we sample for the block id AND centre the carve on.
    const cell: Vec3 = [Math.floor(hx + dir[0] * 0.1), Math.floor(hy + dir[1] * 0.1), Math.floor(hz + dir[2] * 0.1)];
    // only a nearer terrain rigid-hit samples a block id (for the dust sprite); a
    // body or gem hit sends 0 → the white spark.
    const block =
        tRigid <= tGem && rigid.bodyToNode.get(rigidHit.bodyIdB) === undefined
            ? getBlockState(ctx.voxels, cell[0], cell[1], cell[2])
            : 0;
    return { point: [hx, hy, hz], block, cell };
}

// world-space forward unit vector from a CharacterController look spherical
// [_, yaw, pitch] — the same basis the player-controller builds its camera
// forward from (yaw=0, pitch=π/2 → -Z). the server firing tick uses this to
// derive a wizard's fire direction from its synced look, identically for the
// local player (look set from its camera) and npcs (look set by the AI).
function lookDirection(look: Vec3, out: Vec3): Vec3 {
    const theta = look[1]; // yaw
    const phi = look[2]; // pitch
    const sinPhi = Math.sin(phi);
    out[0] = -Math.sin(theta) * sinPhi;
    out[1] = -Math.cos(phi);
    out[2] = -Math.cos(theta) * sinPhi;
    return out;
}

// ── server: player join → spawn ─────────────────────────────────────
script(WorldTrait, 'join', (ctx) => {
    if (!env.server) return;

    const palette: Vec4[] = [
        [0.9, 0.1, 0.1, 1], // red
        [0.2, 0.3, 0.95, 1], // blue
        [0.6, 0.15, 0.85, 1], // purple
    ];

    // existing combatants to spawn the joiner clear of (the new node has no
    // WizardTrait yet at setPosition time, so it isn't counted).
    const wizards = query(ctx, [WizardTrait, TransformTrait]);

    onJoin(ctx, ({ playerNode, user }) => {
        const transform = getTrait(playerNode, TransformTrait)!;
        setPosition(transform, pickSpawnPosition(ctx, positionsOf(wizards)));

        addTrait(playerNode, WizardTrait, {
            color: palette[Math.floor(Math.random() * palette.length)],
            name: user.username || 'anon',
        });
        attachGear(playerNode); // staff + hat onto the rig

        // combat entity: WizardTrait already carries the health pool (current
        // defaults to base max); the AliveTrait marker gates the combat systems.
        addTrait(playerNode, AliveTrait);
    });
});

// ── server: round timer → map reset ─────────────────────────────────
// every ROUND_DURATION the arena resets, with a chat countdown over the final
// seconds. rooms.recreate boots a fresh room from the same on-disk scene
// (pristine terrain + fresh NPCs/environment) and moves every player into it,
// then destroys this one. the successor runs this same script, so the timer
// restarts on its own — a perpetual round loop.
const ROUND_DURATION = 15 * 60; // s — 15 minutes between map changes
const COUNTDOWN_FROM = 10; // s — chat countdown before the map changes

// server → joining client: the moment the map changes, on the shared server timeline
// (ctx.clock.server, which both sides read). sent ONCE per join — the client derives a
// smooth countdown locally (endsAt − clock.server), no per-second churn or sync.
const RoundInfo = command('wizards.round-info', SERVER_TO_CLIENT, pack.object({ endsAt: pack.float64() }));

script(WorldTrait, 'round-timer', (ctx) => {
    if (!env.server) return;

    const players = query(ctx, [PlayerTrait]);
    let endsAt = 0; // absolute server-clock end time; 0 = unarmed (room empty)
    let lastShown = -1; // last whole second announced, so we post once per second

    // first joiner into an empty/lapsed room arms a fresh round; then tell the
    // joiner the current end. use the `client` the join event hands us — always
    // present — rather than a PlayerTrait lookup, which can be undefined this
    // early and silently skip the send (leaving the HUD clock frozen).
    onJoin(ctx, ({ client }) => {
        const now = ctx.clock.server;
        if (endsAt <= now) endsAt = now + ROUND_DURATION;
        send(ctx, RoundInfo, { endsAt }, client);
    });

    onTick(ctx, () => {
        const now = ctx.clock.server;
        // idle while empty — matchmaking reaps empty rooms; the next join re-arms.
        if (players.matches.length === 0) {
            endsAt = 0;
            lastShown = -1;
            return;
        }
        if (endsAt <= 0) endsAt = now + ROUND_DURATION; // safety: arm if somehow unset with players present
        const remaining = endsAt - now;

        // "Map changing in N..." once per second over the final COUNTDOWN_FROM s.
        if (remaining <= COUNTDOWN_FROM && remaining > 0) {
            const sec = Math.ceil(remaining);
            if (sec !== lastShown) {
                lastShown = sec;
                chat.message(ctx, `Map changing in ${sec}...`);
            }
        }

        if (remaining > 0) return;
        rooms.recreate(ctx);
    });
});

// projectiles anchor their flight to `ctx.clock.server - spawnTime`, the shared
// server timeline both sides read (a joining client seeds it from the server in the
// join handshake — see the engine's Clock). spawnTime is the SERVER's clock value at
// the cast, so a client — a touch behind by join latency — places the bolt slightly
// in the past, landing its despawn cleanly at the authoritative impact. the client
// then advances each bolt's visual by wall-clock delta for smooth RAF motion (see
// combat-vfx) — `ctx.clock.server` itself only steps at the 60Hz tick.

script(WorldTrait, 'combat-cast', (ctx) => {
    // ── client: own our held cast intent. that's ALL the client does for firing —
    // the bolt, muzzle, sound and impact are fully server-authoritative (broadcast
    // via ProjectileCast / ImpactCommand, rendered in combat-vfx). no prediction. ──
    if (env.client) {
        onFrame(ctx, () => {
            const controlNode = getControlNode(ctx);
            const pc = controlNode && getTrait(controlNode, PlayerControllerTrait);

            const selfWizard = controlNode && getTrait(controlNode, WizardTrait);
            if (!selfWizard) return;

            const mk = ctx.client?.input?.mouseKeyboard;
            const touch = ctx.client?.input?.touch;

            // scan canvas touches once. `anyTouch`: a finger is driving — so we ignore
            // the synthetic mouse-down the browser fires alongside touch (otherwise it
            // would grab pointer lock and fight the look-drag). `rightTouch`: a finger
            // held on the RIGHT half is the cast intent — the same finger the controller
            // aims with (canvasLook reserves the right half), so aim + cast are one drag.
            let anyTouch = false;
            let rightTouch = false;
            if (touch) {
                const halfWidth = (ctx.client?.state?.viewport.width ?? 0) / 2;
                for (const t of getCanvasTouches(touch).values()) {
                    anyTouch = true;
                    if (t.startX > halfWidth) rightTouch = true;
                }
            }

            // desktop fires on held LMB (with pointer lock); first click (no lock yet)
            // grabs the pointer instead of firing. suppressed while a finger is down so
            // touch's synthetic mouse events never request lock mid-drag.
            const mouseFire = !!mk && isMouseDown(mk, 'left') && !anyTouch;
            if (mouseFire && !document.pointerLockElement) {
                ctx.client?.domElement?.requestPointerLock?.();
            }

            // fire only while alive — the PlayerController is gone while dead, so gate
            // on it so a held input doesn't fire from a corpse. touch needs no pointer
            // lock; desktop does. the server reads `casting` (+ synced look + fireRate)
            // and spawns the shots.
            const alive = !!pc;
            const wantsFire = alive && ((mouseFire && !!document.pointerLockElement) || rightTouch);
            selfWizard.casting = wantsFire; // owner-authored → replicates out
        });

        // knockback — the server directs an impulse to us when our wizard is hit.
        // add it to our own controller velocity; owner-authority replicates the
        // shove out, so the server + other clients see the same motion.
        listen(ctx, KnockbackCommand, ({ impulse }) => {
            const node = getControlNode(ctx);
            const cc = node && getTrait(node, CharacterControllerTrait);
            if (cc) {
                cc.state.velocity[0] += impulse[0];
                cc.state.velocity[1] += impulse[1];
                cc.state.velocity[2] += impulse[2];
            }
        });
    }

    // ── server: one firing tick for ALL wizards — players AND npcs feed the same
    // two inputs (held `casting` + synced `look`); we pace each off its own
    // stats.fireRate and spawn the authoritative projectile along its look. ──
    if (env.server) {
        const wizards = query(ctx, [WizardTrait, CharacterControllerTrait, AliveTrait, TransformTrait]);
        const _fireDir = vec3.create();

        onTick(ctx, () => {
            // server clock (== local time here) so the bolt's spawnTime is in the
            // shared timeline clients derive from.
            const now = ctx.clock.server;
            for (const [wizard, controller, , transform] of wizards) {
                if (!wizard.casting) continue;
                if (now - wizard.lastFireTime < fireIntervalOf(wizard.stats.levels)) continue;
                wizard.lastFireTime = now;

                const dir = lookDirection(controller.input.look, _fireDir);
                const aim = quat.rotationTo(quat.create(), [0, 0, -1], dir);
                const p = getWorldPosition(transform);
                const origin: Vec3 = [p[0] + dir[0] * 1.2, p[1] + EYE_HEIGHT + dir[1] * 1.2, p[2] + dir[2] * 1.2];
                // snapshot the wizard's current projectile stats into the shot.
                spawnProjectile(ctx, ctx.node, wizard._node, origin, aim, now, projectileStatsOf(wizard.stats.levels));
            }
        });
    }
});

script(WorldTrait, 'combat-projectiles', (ctx) => {
    if (!env.server) return;

    const projectiles = query(ctx, [ProjectileTrait, TransformTrait]);
    const targets = query(ctx, [WizardTrait, AliveTrait, TransformTrait]);
    const gems = query(ctx, [GemTrait, TransformTrait]); // shootable xp crystals — splashed like wizards

    // catch a joining client up on bolts already in flight: re-send each one's cast
    // (with its ORIGINAL origin + spawnTime) just to them. the seeded clock then
    // places each at the correct point along its path, not back at the muzzle.
    onJoin(ctx, ({ playerNode }) => {
        const client = getTrait(playerNode, PlayerTrait)?.client;
        if (!client) return;
        for (const [projectile] of projectiles) {
            send(ctx, ProjectileCast, projectileCastPayload(projectile), client);
        }
    });

    // reusable crashcat ray-query state.
    const rayCollector = createClosestCastRayCollector();
    const raySettings = createDefaultCastRaySettings();
    let rayFilter: ReturnType<typeof crashFilter.forWorld> | null = null; // built lazily once the world exists
    const _rayDir = vec3.create();

    // carve a voxel sphere + splash-damage characters within `damageRadius`,
    // then tell clients where it landed.
    const handleHit = (id: number, pos: Vec3, ownerId: number, stats: ProjectileStats, block: number, cell: Vec3) => {
        // terrain carve, centred on the struck voxel (`cell` = the hit point
        // stepped into the surface). even radius 0 (low Bullet Damage) clears
        // that one block — so a fresh wizard can always blast out of a hole;
        // the wider crater is the Bullet Damage milestone payoff on top.
        {
            const r = Math.floor(stats.terrainDamageRadius);
            const cx = cell[0];
            const cy = cell[1];
            const cz = cell[2];
            for (let dx = -r; dx <= r; dx++) {
                for (let dy = -r; dy <= r; dy++) {
                    for (let dz = -r; dz <= r; dz++) {
                        if (dx * dx + dy * dy + dz * dz > stats.terrainDamageRadius * stats.terrainDamageRadius) continue;
                        if (getBlock(ctx.voxels, cx + dx, cy + dy, cz + dz) !== BLOCK_AIR) {
                            setBlock(ctx.voxels, cx + dx, cy + dy, cz + dz, BLOCK_AIR);
                            // a grass plant / mushroom resting on this block loses
                            // its footing — cull it (gameplay, not engine physics).
                            if (SUPPORTED_DECOR_KEYS.has(getBlock(ctx.voxels, cx + dx, cy + dy + 1, cz + dz))) {
                                setBlock(ctx.voxels, cx + dx, cy + dy + 1, cz + dz, BLOCK_AIR);
                            }
                        }
                    }
                }
            }
        }

        for (const [wiz, , transform] of targets) {
            const isOwner = transform._node.id === ownerId;
            const wp = getWorldPosition(transform);
            const tx = wp[0];
            const ty = wp[1] + CHEST_OFFSET;
            const tz = wp[2];
            const ex = pos[0] - tx;
            const ey = pos[1] - ty;
            const ez = pos[2] - tz;
            if (ex * ex + ey * ey + ez * ez > stats.damageRadius * stats.damageRadius) continue;

            // the shooter is shoved by their own blast (rocket-jump) but takes no self-damage.
            if (!isOwner) {
                wiz.current = Math.max(0, wiz.current - stats.damage);
                wiz.lastDamageTime = ctx.clock.time;
                wiz.lastAttacker = ownerId;
                broadcast(ctx, DamageCommand, { pos: [tx, ty, tz], amount: stats.damage, tier: -1 });
            }

            // knockback. enemies get a radial horizontal shove + an up-kick so it lands
            // on grounded targets (ground drag would eat a flat horizontal push). the
            // shooter instead gets a full 3D shove away from their own blast — a shot at
            // your feet launches you up, one at a nearby wall flings you off it.
            // players own their velocity → apply on their own client via a directed
            // command; the server applies it for npcs (which it owns) directly.
            const mag = stats.knockback;
            let impulse: Vec3;
            if (isOwner) {
                const dx = tx - pos[0];
                const dy = ty - pos[1];
                const dz = tz - pos[2];
                const len = Math.hypot(dx, dy, dz) || 1;
                impulse = [(dx / len) * mag, (dy / len) * mag + mag * KNOCKBACK_UP, (dz / len) * mag];
            } else {
                const kx = tx - pos[0];
                const kz = tz - pos[2];
                const klen = Math.hypot(kx, kz) || 1;
                impulse = [(kx / klen) * mag, mag * KNOCKBACK_UP, (kz / klen) * mag];
            }
            // always lift off the ground: floor the upward component so even a
            // weak or overhead shove pops the target up rather than scrubbing
            // along the floor (ground drag would eat a purely horizontal push).
            impulse[1] = Math.max(impulse[1], KNOCKBACK_MIN_UP);
            const node = transform._node;
            const player = getTrait(node, PlayerTrait);
            if (player) {
                send(ctx, KnockbackCommand, { impulse }, player.client);
            } else {
                const cc = getTrait(node, CharacterControllerTrait);
                if (cc) {
                    cc.state.velocity[0] += impulse[0];
                    cc.state.velocity[1] += impulse[1];
                    cc.state.velocity[2] += impulse[2];
                }
            }
        }

        // gems take the same splash within `damageRadius` (the projectile is swept
        // to detonate on a gem's AABB, so a direct shot lands its centre well inside
        // the blast). the hit pop is shared with wizards; the gems script reaps deaths.
        for (const [gem, transform] of gems) {
            if (gem.current <= 0) continue; // already dead this tick, awaiting reap
            const gp = getWorldPosition(transform);
            const ex = pos[0] - gp[0];
            const ey = pos[1] - gp[1];
            const ez = pos[2] - gp[2];
            if (ex * ex + ey * ey + ez * ez > stats.damageRadius * stats.damageRadius) continue;
            gem.current = Math.max(0, gem.current - stats.damage);
            broadcast(ctx, DamageCommand, { pos: [gp[0], gp[1], gp[2]], amount: stats.damage, tier: gem.tier });
        }

        broadcast(ctx, ImpactCommand, { id, pos: [pos[0], pos[1], pos[2]], fizzle: false, block, radius: stats.damageRadius });
    };

    onTick(ctx, ({ delta }) => {
        const now = ctx.clock.server; // bolts' spawnTime is in the shared (server) timeline
        // the rigid world — voxels live in this same crashcat world, so one cast
        // covers terrain + character bodies.
        const rigid = ctx.physics.rigid;
        rayFilter ??= crashFilter.forWorld(rigid.world); // all layers: terrain + bodies

        // resolve outside the loop — destroying nodes mid-iteration is unsafe.
        const spent: Array<{ node: Node; id: number; pos: Vec3; ownerId: number; stats: ProjectileStats; fizzle: boolean; block: number; cell?: Vec3 }> = [];

        for (const [projectile, transform] of projectiles) {
            const pos = transform.position;
            if (now - projectile.spawnTime > PROJECTILE_LIFETIME) {
                spent.push({ node: projectile._node, id: projectile.id, pos: [pos[0], pos[1], pos[2]], ownerId: projectile.ownerId, stats: projectile.stats, fizzle: true, block: 0 });
                continue;
            }

            // travel direction (from the cast aim) and this tick's step distance.
            const dir = vec3.transformQuat(_rayDir, [0, 0, -1], projectile.aim);
            const step = projectile.stats.speed * delta;

            // the SAME query the client predicts with — terrain + characters + gems.
            const hit = castProjectileSegment(ctx, pos, dir, step, projectile.ownerId, gems, rayCollector, raySettings, rayFilter);
            if (hit) {
                spent.push({ node: projectile._node, id: projectile.id, pos: hit.point, ownerId: projectile.ownerId, stats: projectile.stats, fizzle: false, block: hit.block, cell: hit.cell });
                continue;
            }

            // no hit — advance the server-only sim position.
            setPosition(transform, [pos[0] + dir[0] * step, pos[1] + dir[1] * step, pos[2] + dir[2] * step]);
        }

        for (const s of spent) {
            if (s.fizzle) broadcast(ctx, ImpactCommand, { id: s.id, pos: s.pos, fizzle: true, block: 0, radius: s.stats.damageRadius });
            else handleHit(s.id, s.pos, s.ownerId, s.stats, s.block, s.cell!);
            destroyNode(s.node);
        }
    });
});

// ── server: health, death, respawn ──────────────────────────────────

script(WorldTrait, 'combat-health', (ctx) => {
    if (!env.server) return;

    const alive = query(ctx, [WizardTrait, AliveTrait, TransformTrait]);
    const combatants = query(ctx, [WizardTrait, TransformTrait]); // every scoreable entity (players + npcs); transform for spawn spacing
    const respawns: Array<{ node: Node; at: number; pos: Vec3 }> = [];

    onTick(ctx, ({ delta }) => {
        const now = ctx.clock.time;
        const deaths: Array<{ node: Node; pos: Vec3; attacker: number }> = [];

        for (const [wiz, , transform] of alive) {
            // fell out of the world (off a map edge into the void) → lethal fizzle.
            if (getWorldPosition(transform)[1] < KILL_Y) {
                wiz.current = 0;
                wiz.lastAttacker = -1; // environmental — no kill credit
            }
            if (wiz.current <= 0) {
                const wp = getWorldPosition(transform);
                deaths.push({ node: transform._node, pos: [wp[0], wp[1], wp[2]], attacker: wiz.lastAttacker });
                continue;
            }
            const max = maxHealthOf(wiz.stats.levels);
            if (wiz.current < max && now - wiz.lastDamageTime >= REGEN_DELAY) {
                // accumulate at the flat baseline regen rate, commit only whole hp so `current` stays discrete.
                wiz.regenAccum += BASE_REGEN_RATE * delta;
                if (wiz.regenAccum >= 1) {
                    const gained = Math.floor(wiz.regenAccum);
                    wiz.current = Math.min(max, wiz.current + gained);
                    wiz.regenAccum -= gained;
                }
            } else {
                wiz.regenAccum = 0; // drop partial progress while damaged or full
            }
        }

        for (const d of deaths) {
            removeTrait(d.node, AliveTrait);
            broadcast(ctx, DeathCommand, { pos: d.pos });

            // score + log: credit the victim a death, and the killer (if any, and
            // not self/terrain) a kill. `attacker` is the last node to damage them.
            const victim = getTrait(d.node, WizardTrait);
            if (victim) victim.deaths++;

            // diep-style re-spec on death: scatter a chunk of xp as orbs near the
            // corpse, keep a slice for the respawn, lose the rest, and reset all
            // stat allocations to 0 so the wizard re-spends from scratch.
            if (victim) {
                const dropCount = Math.max(ORB_DROP_MIN, Math.floor((victim.xp * ORB_DROP_SCATTER) / ORB_AMOUNT));
                for (let n = 0; n < dropCount; n++) {
                    // burst up + out from the corpse; physics arcs them down to scatter.
                    const ang = Math.random() * Math.PI * 2;
                    const out = 1 + Math.random() * ORB_POP_OUT;
                    const vel: Vec3 = [Math.cos(ang) * out, ORB_POP_UP + Math.random() * 2, Math.sin(ang) * out];
                    spawnOrb(ctx, d.pos[0], d.pos[1] + 1, d.pos[2], ORB_AMOUNT, vel);
                }
                victim.xp = Math.floor(victim.xp * ORB_DROP_KEEP);
                for (const k of STAT_KEYS) victim.stats.levels[k] = 0;
            }

            let killerName = '';
            if (d.attacker >= 0 && d.attacker !== d.node.id) {
                for (const [w] of combatants) {
                    if (w._node.id === d.attacker) {
                        w.kills++;
                        killerName = w.name;
                        break;
                    }
                }
            }
            const victimName = victim?.name || 'someone';
            chat.message(ctx, killerName ? `${killerName} blasted ${victimName}` : `${victimName} fizzled out`);

            // players lose their player-controller while dead — frees the camera for
            // the death-cam, stops input, and hides the viewmodel. and dropping the
            // character-controller freezes the body where it died (no slide/settle),
            // so the orbit pins to a fixed point. both re-added on respawn.
            if (getTrait(d.node, PlayerControllerTrait)) removeTrait(d.node, PlayerControllerTrait);
            if (getTrait(d.node, CharacterControllerTrait)) removeTrait(d.node, CharacterControllerTrait);
            // respawn spread out from everyone else (players + npcs alike), on the
            // ground — no more piling onto a fixed point and spawn-dying.
            const pos = pickSpawnPosition(ctx, positionsOf(combatants, d.node.id));
            respawns.push({ node: d.node, at: now + RESPAWN_DELAY, pos });
        }

        for (let i = respawns.length - 1; i >= 0; i--) {
            if (now < respawns[i]!.at) continue;
            const r = respawns.splice(i, 1)[0]!;
            const wiz = getTrait(r.node, WizardTrait);
            const transform = getTrait(r.node, TransformTrait);
            if (!wiz || !transform) continue; // node went away
            wiz.current = maxHealthOf(wiz.stats.levels); // base max (levels reset on death)
            wiz.regenAccum = 0;
            wiz.lastDamageTime = now;
            wiz.lastAttacker = -1;
            setPosition(transform, r.pos);
            // re-add the character-controller first (it inits its body at the
            // freshly-set spawn position), then the player-controller (which
            // requires it) for players only.
            if (!getTrait(r.node, CharacterControllerTrait)) addTrait(r.node, CharacterControllerTrait);
            addTrait(r.node, AliveTrait);
            if (getTrait(r.node, PlayerTrait)) addTrait(r.node, PlayerControllerTrait);
        }
    });
});

// ── server: stat upgrades ───────────────────────────────────────────
// spend an earned point (level − allocated) on a stat. character stats apply
// immediately; projectile / fire-rate / regen read their level at use.

// apply one point into `key` if the wizard has a spare point and the stat isn't
// capped; returns whether it spent. shared by the player command + the npc AI.
function tryUpgrade(wiz: WizardTrait, key: StatKey): boolean {
    const levels = wiz.stats.levels;
    if (availablePoints(wiz.xp, levels) <= 0) return false; // no points to spend
    if (levels[key] >= STAT_TABLE[key].max) return false; // capped
    const beforeMax = maxHealthOf(levels);
    levels[key]++;
    if (key === 'maxHealth') wiz.current += maxHealthOf(levels) - beforeMax; // grant the new hp
    if (key === 'moveSpeed') {
        const cc = getTrait(wiz._node, CharacterControllerTrait);
        if (cc) cc.config.walkSpeed = lvlValue('moveSpeed', levels.moveSpeed);
    }
    return true;
}

script(WorldTrait, 'upgrades', (ctx) => {
    if (!env.server) return;
    const players = query(ctx, [PlayerTrait, WizardTrait]);

    listen(ctx, UpgradeStat, ({ stat }, from) => {
        const key = STAT_KEYS[stat];
        if (!key) return;
        for (const [player, wiz] of players) {
            if (player.client !== from) continue;
            tryUpgrade(wiz, key);
            return;
        }
    });
});

// ── xp orbs — pickup (server), sprite decorate (client) ─────────────
// orbs drop from shattered gems and dead wizards (gems are the ambient source).
// this script only reels them in (server) and renders them (client).

script(WorldTrait, 'xp', (ctx) => {
    if (env.server) {
        const orbs = query(ctx, [XpOrbTrait, AabbBodyTrait, TransformTrait]);
        const wizards = query(ctx, [WizardTrait, AliveTrait, TransformTrait]);

        onTick(ctx, () => {
            const now = ctx.clock.time;
            // pickup: for each orb find the nearest alive wizard within the magnet
            // radius — inside grab range it's collected, otherwise it reels toward
            // them (aimed at chest height). removal (collected/despawned) is deferred
            // — destroying nodes mid-iteration is unsafe.
            const collected: Node[] = [];
            for (const [orb, orbBody, orbTransform] of orbs) {
                const op = getWorldPosition(orbTransform);
                // despawn: aged out, or fell out of the world (same kill plane as players).
                if (now - orb.spawnTime > ORB_LIFETIME || op[1] < KILL_Y) {
                    collected.push(orb._node);
                    continue;
                }
                if (!orbBody.body) continue; // body installs on the next physics step
                let target: { xp: number; _node: Node } | null = null;
                let targetX = 0;
                let targetY = 0;
                let targetZ = 0;
                let bestSq = ORB_MAGNET_RADIUS * ORB_MAGNET_RADIUS;
                for (const [wiz, , wizTransform] of wizards) {
                    const wp = getWorldPosition(wizTransform);
                    const dx = wp[0] - op[0];
                    const dy = wp[1] + CHEST_OFFSET - op[1];
                    const dz = wp[2] - op[2];
                    const d2 = dx * dx + dy * dy + dz * dz;
                    if (d2 < bestSq) {
                        bestSq = d2;
                        target = wiz;
                        targetX = wp[0];
                        targetY = wp[1] + CHEST_OFFSET;
                        targetZ = wp[2];
                    }
                }
                if (!target) continue;

                if (bestSq <= ORB_GRAB_RADIUS * ORB_GRAB_RADIUS) {
                    target.xp += orb.amount;
                    collected.push(orb._node);
                } else {
                    // luanti-style homing via the body's velocity (setVelocity wakes it
                    // and overrides gravity for the tick): speed grows as it nears, plus
                    // the collector's own velocity so it tracks a moving target.
                    const dx = targetX - op[0];
                    const dy = targetY - op[1];
                    const dz = targetZ - op[2];
                    const dist = Math.hypot(dx, dy, dz) || 1;
                    const speed = ORB_MAGNET_PULL - dist;
                    const cc = getTrait(target._node, CharacterControllerTrait);
                    const pv = cc ? cc.state.velocity : null;
                    aabbBody.setVelocity(
                        ctx.physics.aabb,
                        orbBody.body,
                        (dx / dist) * speed + (pv ? pv[0] : 0),
                        (dy / dist) * speed + (pv ? pv[1] : 0),
                        (dz / dist) * speed + (pv ? pv[2] : 0),
                    );
                }
            }
            for (const n of collected) destroyNode(n);
        });
    }

    if (env.client) {
        const orbs = query(ctx, [XpOrbTrait, TransformTrait]);
        const BOB_FREQ = 2.5; // rad/s
        const BOB_AMP = 0.09; // m — local vertical float
        const PULSE_FREQ = 3.2; // rad/s — white shimmer
        let lastXp = -1; // local player's xp last frame; blip when it rises
        let lastHealth = -1; // local player's health last frame; grunt when it drops
        let lastLevel = -1; // local player's level last frame; chime when it rises

        onFrame(ctx, () => {
            const time = ctx.clock.wall; // smooth per-frame clock → no 60Hz step in the bob/pulse

            // pickup blip — our own xp is synced, so just play when it ticks up
            // (covers magnetised orbs without a dedicated command). first sight
            // seeds lastXp so we don't blip on join / initial sync.
            const self = getControlNode(ctx);
            const selfWiz = self && getTrait(self, WizardTrait);
            if (selfWiz) {
                // luanti-style: randomise pitch down a little each pickup so rapid
                // blips vary instead of machine-gunning the same sample.
                if (lastXp >= 0 && selfWiz.xp > lastXp) playMono(ctx, PickupSound, { volume: 0.75, detune: -Math.random() * 250 });
                lastXp = selfWiz.xp;
                // grunt on taking damage — only on a health drop (regen rises,
                // respawn jumps up, both stay silent). seeded -1 so join/initial
                // sync doesn't trigger it.
                if (lastHealth >= 0 && selfWiz.current < lastHealth) {
                    playMono(ctx, sounds.playerDamage, { detune: (Math.random() * 2 - 1) * 100 });
                }
                lastHealth = selfWiz.current;
                // level-up chime — local player only (this runs on the control
                // node), never for other wizards. seeded -1 so join doesn't fire it.
                const lvl = levelForXp(selfWiz.xp);
                if (lastLevel >= 0 && lvl > lastLevel) playMono(ctx, sounds.levelUp);
                lastLevel = lvl;
            }

            for (const [, transform] of orbs) {
                const orbNode = transform._node;
                // the orb node holds the authoritative (synced) position. the sprite
                // lives on a client-only child so we can bob + pulse it locally without
                // fighting the replicated transform. it despawns with the orb node.
                let visual = findChildByName(orbNode, 'orb-visual');
                if (!visual) {
                    visual = createNode({ name: 'orb-visual' });
                    addTrait(visual, TransformTrait);
                    addTrait(visual, SpriteTrait, { sprite: XpOrbSprite, mode: 'billboard', width: 7, height: 7, worldScale: 1 / 20 });
                    addChild(orbNode, visual);
                }

                const phase = orbNode.id * 1.7; // de-sync the bob/pulse between orbs
                setPosition(getTrait(visual, TransformTrait)!, [0, Math.sin(time * BOB_FREQ + phase) * BOB_AMP, 0]);

                // gentle white shimmer: flash toward white + a touch of glow.
                // (tint can't brighten — it preserves lightness — so the
                // toward-white shimmer is a flash, not a tint.)
                const pulse = Math.sin(time * PULSE_FREQ + phase) * 0.5 + 0.5; // 0..1
                const sprite = getTrait(visual, SpriteTrait)!;
                sprite.flash[0] = sprite.flash[1] = sprite.flash[2] = 1; // white
                sprite.flash[3] = pulse * 0.25; // up to 25% toward white
                sprite.glow = pulse * 0.3; // slight additive glow
            }
        });
    }
});

// ── gems — litter + reap (server), spinning crystal + healthbar (client) ─
// the ambient xp source. the server keeps ~GEM_TARGET tiered gems scattered and
// reaps any whose health hits 0 (damage is applied in combat-damage's splash),
// shattering them into magnet-collected orbs proportional to tier. the client
// decorates each with a spinning, tier-coloured crystal and a healthbar that only
// appears once the gem has been hit.

script(WorldTrait, 'gems', (ctx) => {
    if (env.server) {
        const gems = query(ctx, [GemTrait, TransformTrait]);
        let topUpIn = 0;

        // seed the full litter batch at room start so the arena has gems
        // immediately, rather than trickling in one per GEM_RESPAWN_INTERVAL.
        // runs after worldgen's onInit (registered earlier), so the terrain the
        // ground-raycast reads is already in place. each gem spreads away from
        // the ones placed so far → even coverage across the whole map.
        onInit(ctx, () => {
            const placed: Vec3[] = [];
            for (let i = 0; i < GEM_TARGET; i++) {
                const spot = pickGemSpot(ctx, placed);
                placed.push(spot);
                spawnGem(ctx, spot[0], spot[1], spot[2], rollGemTier());
            }
        });

        onTick(ctx, ({ delta }) => {
            // litter: keep ~GEM_TARGET gems scattered across the map, topping up
            // on a timer into the most-isolated free spot.
            topUpIn -= delta;
            if (topUpIn <= 0) {
                topUpIn = GEM_RESPAWN_INTERVAL;
                if (gems.matches.length < GEM_TARGET) {
                    const spot = pickGemSpot(ctx, gemPositions(gems));
                    spawnGem(ctx, spot[0], spot[1], spot[2], rollGemTier());
                }
            }

            // reap: shatter dead gems into an orb burst proportional to tier, fire
            // the death vfx, then destroy the node (deferred — destroying mid-iter
            // is unsafe). the orbs reuse the existing magnet-collect pickup.
            const dead: Node[] = [];
            for (const [gem, transform] of gems) {
                if (gem.current > 0) continue;
                const gp = getWorldPosition(transform);
                const tier = GEM_TIERS[gem.tier] ?? GEM_TIERS[0]!;
                const count = Math.max(1, Math.floor(tier.xp / ORB_AMOUNT));
                for (let n = 0; n < count; n++) {
                    const ang = Math.random() * Math.PI * 2;
                    const out = 1 + Math.random() * ORB_POP_OUT;
                    const vel: Vec3 = [Math.cos(ang) * out, ORB_POP_UP + Math.random() * 2, Math.sin(ang) * out];
                    spawnOrb(ctx, gp[0], gp[1], gp[2], ORB_AMOUNT, vel);
                }
                broadcast(ctx, GemDeathCommand, { pos: [gp[0], gp[1], gp[2]], tier: gem.tier });
                dead.push(gem._node);
            }
            for (const n of dead) destroyNode(n);
        });
    }

    if (env.client) {
        // client-only idle motion: the crystal visual is built + spun here, so none of
        // this is networked — the server body is a STATIC, non-rotating collider.
        const GEM_SPIN_SPEED = 1.4; // rad/s — continuous yaw
        const GEM_TILT_BASE = 0.55; // rad — constant lean so the spin reads as diagonal, not a flat turntable
        const GEM_TUMBLE_FREQ = 1.1; // rad/s — the lean rocks back and forth at this rate…
        const GEM_TUMBLE_AMP = 0.3; // rad — …by this much, for a livelier tumble
        const GEM_BOB_FREQ = 1.6; // rad/s — gentle vertical float
        const GEM_BOB_AMP = 0.12; // m
        const GEM_HP_MAX_DIST = 24; // m — hide the damage healthbar beyond this

        const gems = query(ctx, [GemTrait, TransformTrait]);
        const _gemYaw = quat.create();
        const _gemTilt = quat.create();
        const _gemRot = quat.create();
        const hpShown = new WeakMap<HTMLElement, number>(); // diff-gate the healthbar repaint

        // a tiny square hp bar: a coloured fill (green→yellow→red) over a dark track.
        // the track div carries its own px size so the bar shows regardless of how
        // the HtmlTrait wrapper element is styled.
        const paintGemBar = (el: HTMLElement, hp: number, max: number) => {
            const pct = max > 0 ? Math.max(0, Math.min(1, hp / max)) : 0;
            const track = document.createElement('div');
            track.style.cssText = 'width:60px; height:9px; background:#222; border:1px solid #000; box-sizing:border-box; overflow:hidden;';
            const fill = document.createElement('div');
            fill.style.cssText = `height:100%; width:${pct * 100}%; background:${pct > 0.5 ? '#22c55e' : pct > 0.25 ? '#eab308' : '#dc2626'};`;
            track.appendChild(fill);
            el.replaceChildren(track);
        };

        // shatter burst — a tier-coloured spark spray, bigger + longer for richer tiers.
        listen(ctx, GemDeathCommand, ({ pos, tier }) => {
            const fx = GemShatterFx[tier] ?? GemShatterFx[0]!;
            const t = GEM_TIERS[tier] ?? GEM_TIERS[0]!;
            const at: Vec3 = [pos[0], pos[1], pos[2]];
            // shatter sound — random glass-break variant, positional with the
            // arena falloff. higher tiers ring out lower + a touch louder.
            const glass = [sounds.breakGlass1, sounds.breakGlass2, sounds.breakGlass3][Math.floor(Math.random() * 3)]!;
            playAt(ctx, glass, at, {
                falloff: { ref: 12, rolloff: 0.4 },
                volume: 0.9 + tier * 0.15,
                detune: -tier * 200 + (Math.random() * 2 - 1) * 120,
            });
            const count = 18 + tier * 12;
            const speed = 5 + tier * 2;
            for (let i = 0; i < count; i++) {
                const d = randomDir();
                spawnParticle(ctx, fx, at, {
                    lifetime: varyLife(1 + tier * 0.3),
                    size: 0.07 + t.scale * 0.06,
                    glow: 1,
                    velX: d[0] * speed,
                    velY: Math.abs(d[1]) * speed + 2,
                    velZ: d[2] * speed,
                });
            }
        });

        onFrame(ctx, () => {
            const time = ctx.clock.wall; // smooth per-frame clock → no 60Hz step in the spin/bob
            const camPos = getWorldPosition(getTrait(resolveCamera(ctx).node, TransformTrait)!);
            for (const [gem, transform] of gems) {
                const gemNode = transform._node;
                const tier = GEM_TIERS[gem.tier] ?? GEM_TIERS[0]!;

                // the gem node holds the authoritative (synced) position; the crystal
                // lives on a client-only child so it can spin + bob locally without
                // fighting the replicated transform. it despawns with the gem node.
                let visual = findChildByName(gemNode, 'gem-visual');
                if (!visual) {
                    visual = cloneModel(wizardModels.nodes.gem);
                    visual.name = 'gem-visual';
                    setScale(getTrait(visual, TransformTrait)!, [tier.scale, tier.scale, tier.scale]);
                    const color = hexTint(tier.color);
                    traverse(visual, (n) => {
                        const mesh = getTrait(n, MeshTrait);
                        if (mesh) setMeshTint(mesh, color);
                    });
                    addChild(gemNode, visual);
                }
                const phase = gemNode.id * 1.7; // de-sync the spin/bob between gems
                const vt = getTrait(visual, TransformTrait)!;
                setPosition(vt, [0, Math.sin(time * GEM_BOB_FREQ + phase) * GEM_BOB_AMP, 0]);
                // diagonal tumble: continuous yaw, composed onto a constant lean that
                // rocks back and forth — a livelier, off-axis spin (client-only).
                const tilt = GEM_TILT_BASE + Math.sin(time * GEM_TUMBLE_FREQ + phase) * GEM_TUMBLE_AMP;
                quat.setAxisAngle(_gemYaw, [0, 1, 0], time * GEM_SPIN_SPEED + phase);
                quat.setAxisAngle(_gemTilt, [0, 0, 1], tilt);
                quat.multiply(_gemRot, _gemYaw, _gemTilt);
                setQuaternion(vt, _gemRot);

                // healthbar — built on first damage (current < max), then shown only
                // while the camera is in range (distant bars would just be clutter).
                if (gem.current < tier.health) {
                    let bar = findChildByName(gemNode, 'gem-hp');
                    if (!bar) {
                        bar = createNode({ name: 'gem-hp' });
                        setPosition(addTrait(bar, TransformTrait), [0, tier.scale + 0.4, 0]);
                        addTrait(bar, HtmlTrait, { mode: 'screen', center: true, distanceFactor: null, pointerEvents: false });
                        addChild(gemNode, bar);
                    }
                    const el = getTrait(bar, HtmlTrait)!.element;
                    if (el) {
                        const gp = getWorldPosition(transform);
                        const dx = gp[0] - camPos[0];
                        const dy = gp[1] - camPos[1];
                        const dz = gp[2] - camPos[2];
                        const inRange = dx * dx + dy * dy + dz * dz < GEM_HP_MAX_DIST * GEM_HP_MAX_DIST;
                        el.style.visibility = inRange ? 'visible' : 'hidden';
                        if (inRange && hpShown.get(el) !== gem.current) {
                            hpShown.set(el, gem.current);
                            paintGemBar(el, gem.current, tier.health);
                        }
                    }
                }
            }
        });
    }
});

// ── server: NPC dummy wizards — spawn + steering ────────────────────
// spawns a few killable dummy wizards at fixed homes (onInit), then each tick
// steers them. pathfinding is voxelNav (in the core lib); the *steering* half
// lives here — repath to the nearest combatant on a timer and walk the
// waypoints (look + move + jump), or circle-strafe + fire when in range.

script(WorldTrait, 'combat-npcs', (ctx) => {
    if (!env.server) return;

    const NPC_COLORS: Vec4[] = [
        [0.15, 0.75, 0.3, 0.8], // green
        [0.95, 0.6, 0.1, 0.8], // orange
        [0.1, 0.7, 0.85, 0.8], // teal
    ];
    const NPC_COUNT = NPC_COLORS.length; // dummies spawned at room init, spread apart

    const CHASE_RANGE = 30; // m — only pursue a player within this
    const REPATH_INTERVAL = 0.5; // s between repaths
    const NPC_REPATHS_PER_TICK = 4; // round-robin cap: at most this many A* runs per tick (spreads + de-bunches repaths).
    //                                 must exceed NPC_COUNT or an idle npc can be starved of a repath on the tick it
    //                                 picks a wander, fail to get a path, and falsely "arrive" → reroll → stand.
    const NPC_PATH_MAX_ITERATIONS = 200; // A* node-expansion cap. raised from 100: on hilly terrain a wander target the
    //                                      flood-fill proved reachable can still be a long step-up/down path, and a too-low
    //                                      cap makes A* give up → empty path → false "arrive" → stand. cheap; bounds spikes.
    const WAYPOINT_REACHED = 0.7; // m (horizontal) to advance to the next waypoint
    const CAST_RANGE = 16; // m — within this (with a clear shot) the NPC strafes + fires
    // burst-fire as a held window: the AI just opens `casting` for a beat (the
    // server firing tick fires at stats.fireRate while it's held → a blob of
    // shots), then closes it for a longer pause. same arm-raise-held feel as
    // before, now with zero shot-spawning logic in the AI.
    const NPC_BURST_DURATION = 0.8; // s — casting held open (≈ 3 shots at fireRate 3)
    const NPC_BURST_PAUSE = 2.0; // s — casting closed between bursts
    const STRAFE_FLIP_MIN = 0.8; // s — min before reversing strafe direction
    const STRAFE_FLIP_MAX = 2.2; // s — max
    const JUMP_INTERVAL_MIN = 1.5; // s — min between hops while engaged
    const JUMP_INTERVAL_MAX = 3.5; // s — max

    // ── idle behaviour (no combat target) ───────────────────────────────
    // an idle npc runs a short "activity", then rolls the next one: mostly
    // wandering (leashed near the arena centre so it stays where players are), the
    // odd emote for personality, and an opportunistic potshot at a nearby gem.
    const WANDER_RADIUS = 36; // m around MAP_CENTER an idle npc roams within (the leash)
    const WANDER_FLOOD_MAX = 300; // max cells the wander flood-fill explores (the iteration cap)
    const WANDER_TIMEOUT = 7; // s — re-roll if a wander hasn't arrived by now (anti-stuck)
    const GEM_NOTICE_RADIUS = 12; // m — only seek a gem this close when idle (opportunistic)
    const SEEKGEM_TIMEOUT = 6; // s — give up chasing a gem after this
    const HALF_PI = Math.PI / 2; // level gaze for look[2] (0 = straight down, π = straight up)
    const GAZE_DOWN = 0.45; // look[2] while "looking around" — eyes toward the ground
    const GAZE_UP = Math.PI * 0.95; // look[2] while shooting skyward — near-straight up
    const IDLE_LOOK_SPEED = 1.1; // rad/s — gentle yaw sweep while "looking around"
    const IDLE_SPIN_SPEED = 5; // rad/s — fast dizzy spin
    const IDLE_LOOK: readonly [number, number] = [1, 2]; // s — emote durations [min,max] (kept short so they snap back to moving)
    const IDLE_SPIN: readonly [number, number] = [0.6, 1.2];
    const IDLE_SHOOTUP: readonly [number, number] = [0.7, 1.2];
    const IDLE_LOITER: readonly [number, number] = [0.8, 1.5];

    const IdleAction = { Wander: 0, SeekGem: 1, LookAround: 2, Spin: 3, ShootUp: 4, Loiter: 5 } as const;
    type IdleAction = (typeof IdleAction)[keyof typeof IdleAction];
    // relative weights (occasional-seasoning feel — mostly wander, the rest sprinkled).
    // SeekGem only enters the roll when a gem is within GEM_NOTICE_RADIUS.
    // wander must dominate so npcs are usually moving. emotes + gem-seek are the
    // occasional seasoning. (gems now blanket the map, so a gem is almost always
    // within notice range — SeekGem's weight, not its eligibility, is what keeps it
    // rare, hence the low value.)
    const IDLE_BASE_WEIGHTS: [IdleAction, number][] = [
        [IdleAction.Wander, 70],
        [IdleAction.LookAround, 4],
        [IdleAction.Spin, 4],
        [IdleAction.ShootUp, 3],
        [IdleAction.Loiter, 4],
    ];
    const IDLE_SEEKGEM_WEIGHT = 7;
    const randRange = ([lo, hi]: readonly [number, number]): number => lo + Math.random() * (hi - lo);

    // npc leveling: each (re)spawn, scale to the players' average level ± spread
    // (floored), then spend all points down an archetype's priority order.
    const MIN_NPC_LEVEL = 1;
    const NPC_LEVEL_SPREAD = 2; // ± levels around the player average
    const NPC_ARCHETYPES: StatKey[][] = [
        ['damage', 'maxHealth', 'moveSpeed', 'fireRate', 'speed', 'blast'], // bruiser
        ['damage', 'speed', 'fireRate', 'blast', 'moveSpeed', 'maxHealth'], // sniper
        ['maxHealth', 'blast', 'moveSpeed', 'damage', 'fireRate', 'speed'], // tank
    ];

    const npcs = query(ctx, [NpcTrait, CharacterControllerTrait, TransformTrait]);
    // free-for-all: any alive entity with health is a candidate target (players
    // AND other NPCs); each NPC skips itself.
    const combatants = query(ctx, [WizardTrait, AliveTrait, TransformTrait]);
    const players = query(ctx, [PlayerTrait, WizardTrait]); // for the player-level average
    const idleGems = query(ctx, [GemTrait, TransformTrait]); // opportunistic idle targets

    // average level of alive players (0 if none).
    const avgPlayerLevel = (): number => {
        let sum = 0;
        let n = 0;
        for (const [player, wiz] of players) {
            if (!getTrait(player._node, AliveTrait)) continue;
            sum += levelForXp(wiz.xp);
            n++;
        }
        return n > 0 ? sum / n : 0;
    };

    // set an npc near the player average level (± spread, floored). once per life;
    // xp orbs picked up while fighting raise it further during the life.
    const setNpcFloor = (wiz: WizardTrait): void => {
        const target = Math.max(MIN_NPC_LEVEL, Math.round(avgPlayerLevel() + (Math.random() * 2 - 1) * NPC_LEVEL_SPREAD));
        wiz.xp = Math.max(wiz.xp, xpForLevel(target)); // grant the level (upward only)
    };

    // spend every available point down the archetype priority (tryUpgrade caps +
    // spills). called each tick so points from the baseline AND from orb pickups are
    // allocated as they arrive — the npc keeps speccing into its build as it grows.
    const spendNpcPoints = (wiz: WizardTrait, archetype: StatKey[]): void => {
        let guard = 64;
        while (availablePoints(wiz.xp, wiz.stats.levels) > 0 && guard-- > 0) {
            let spent = false;
            for (const key of archetype) {
                if (tryUpgrade(wiz, key)) {
                    spent = true;
                    break;
                }
            }
            if (!spent) break; // everything capped
        }
    };

    type Brain = { path: Vec3[]; waypoint: number; repathIn: number; fireWindowIn: number; firing: boolean; strafeDir: number; strafeIn: number; jumpIn: number; leveled: boolean; idleAction: IdleAction; idleUntil: number; wanderTarget: Vec3 | null; idleSpinDir: number };
    const brains = new Map<number, Brain>();

    const worldToCell = (p: Vec3): Vec3 => [Math.floor(p[0]), Math.floor(p[1]), Math.floor(p[2])];

    // stop walking.
    const idle = (controller: CharacterControllerTrait) => {
        controller.input.move[0] = 0;
        controller.input.move[1] = 0;
        controller.input.jump = false;
    };

    // aim the controller's look (yaw + pitch) from `eye` at a world `target` — the
    // same `look` the player's camera drives, read by the server firing tick via
    // lookDirection. shared by the combat aim + the idle gem potshot.
    const aimAt = (controller: CharacterControllerTrait, eye: Vec3, target: Vec3) => {
        const dx = target[0] - eye[0];
        const dy = target[1] - eye[1];
        const dz = target[2] - eye[2];
        controller.input.look[1] = Math.atan2(-dx, -dz); // yaw
        const dist = Math.hypot(dx, dy, dz) || 1;
        controller.input.look[2] = Math.acos(Math.max(-1, Math.min(1, -dy / dist))); // pitch
    };

    // cheap sampled line-of-sight: any non-air cell between the two points
    // blocks the shot (so NPCs don't fire through walls).
    const clearShot = (from: Vec3, to: Vec3): boolean => {
        const dx = to[0] - from[0];
        const dy = to[1] - from[1];
        const dz = to[2] - from[2];
        const steps = Math.ceil(Math.hypot(dx, dy, dz));
        for (let i = 1; i < steps; i++) {
            const t = i / steps;
            if (getBlock(ctx.voxels, Math.floor(from[0] + dx * t), Math.floor(from[1] + dy * t), Math.floor(from[2] + dz * t)) !== BLOCK_AIR) {
                return false;
            }
        }
        return true;
    };

    // walk along brain.path toward `goalCell`, optionally recomputing it this tick.
    // writes the controller's yaw/move/jump and returns 'arrived' once the path is
    // exhausted (caller decides what's next), else 'traveling'. shared by chase +
    // wander + gem-seek so they all use one A* + step-up walker.
    const followPath = (brain: Brain, controller: CharacterControllerTrait, pos: Vec3, goalCell: Vec3, doRepath: boolean): 'arrived' | 'traveling' => {
        if (doRepath) {
            brain.path = voxelNav.findGroundPath(ctx.voxels, worldToCell(pos), goalCell, { maxIterations: NPC_PATH_MAX_ITERATIONS }) ?? [];
            brain.waypoint = 1; // skip our own starting cell
        }
        while (brain.waypoint < brain.path.length) {
            const cell = brain.path[brain.waypoint]!;
            const hx = cell[0] + 0.5 - pos[0];
            const hz = cell[2] + 0.5 - pos[2];
            if (hx * hx + hz * hz > WAYPOINT_REACHED * WAYPOINT_REACHED) break;
            brain.waypoint++;
        }
        if (brain.waypoint >= brain.path.length) return 'arrived';
        const cell = brain.path[brain.waypoint]!;
        controller.input.look[1] = Math.atan2(-(cell[0] + 0.5 - pos[0]), -(cell[2] + 0.5 - pos[2]));
        controller.input.look[2] = HALF_PI; // level gaze while walking
        controller.input.move[0] = 0;
        controller.input.move[1] = 1;
        controller.input.jump = cell[1] > Math.floor(pos[1]); // hop up steps
        return 'traveling';
    };

    // nearest live gem within `maxDist` of `pos` (world position), or null.
    const nearestGemWithin = (pos: Vec3, maxDist: number): Vec3 | null => {
        let best: Vec3 | null = null;
        let bestSq = maxDist * maxDist;
        for (const [gem, transform] of idleGems) {
            if (gem.current <= 0) continue;
            const gp = getWorldPosition(transform);
            const dx = gp[0] - pos[0];
            const dy = gp[1] - pos[1];
            const dz = gp[2] - pos[2];
            const distSq = dx * dx + dy * dy + dz * dz;
            if (distSq < bestSq) {
                bestSq = distSq;
                best = [gp[0], gp[1], gp[2]];
            }
        }
        return best;
    };

    // wander destination: a random cell reachable on foot from `pos`, kept within
    // WANDER_RADIUS of the arena centre (the leash). drawn from the flood-fill, so
    // pathing to it can't fail. if the npc is boxed outside the leash, it heads to
    // the reachable cell nearest the centre, so it drifts back. null only when
    // genuinely boxed in (no walkable neighbours at all).
    const pickWanderTarget = (pos: Vec3): Vec3 | null => {
        const reachable = floodFillGround(ctx.voxels, worldToCell(pos), WANDER_FLOOD_MAX);
        if (reachable.length <= 1) return null;
        const distSqToCenter = (c: Vec3): number => {
            const dx = c[0] + 0.5 - MAP_CENTER[0];
            const dz = c[2] + 0.5 - MAP_CENTER[1];
            return dx * dx + dz * dz;
        };
        const inLeash = reachable.filter((c) => distSqToCenter(c) <= WANDER_RADIUS * WANDER_RADIUS);
        if (inLeash.length > 0) return inLeash[Math.floor(Math.random() * inLeash.length)]!;
        // outside the leash → walk back toward the centre.
        return reachable.reduce((best, c) => (distSqToCenter(c) < distSqToCenter(best) ? c : best), reachable[0]!);
    };

    // roll the next idle activity (weighted) and stamp its deadline + scratch onto
    // the brain. SeekGem only competes when a gem is within notice range.
    const pickIdleAction = (brain: Brain, pos: Vec3, now: number): void => {
        const gemNear = nearestGemWithin(pos, GEM_NOTICE_RADIUS) !== null;
        let total = gemNear ? IDLE_SEEKGEM_WEIGHT : 0;
        for (const [, w] of IDLE_BASE_WEIGHTS) total += w;

        let r = Math.random() * total;
        let action: IdleAction = IdleAction.Wander;
        if (gemNear && r < IDLE_SEEKGEM_WEIGHT) {
            action = IdleAction.SeekGem;
        } else {
            if (gemNear) r -= IDLE_SEEKGEM_WEIGHT;
            for (const [a, w] of IDLE_BASE_WEIGHTS) {
                if (r < w) {
                    action = a;
                    break;
                }
                r -= w;
            }
        }

        brain.idleAction = action;
        switch (action) {
            case IdleAction.Wander:
                brain.wanderTarget = pickWanderTarget(pos);
                brain.idleUntil = now + WANDER_TIMEOUT;
                brain.path = [];
                brain.waypoint = 0;
                brain.repathIn = 0;
                break;
            case IdleAction.SeekGem:
                brain.idleUntil = now + SEEKGEM_TIMEOUT;
                brain.path = [];
                brain.waypoint = 0;
                brain.repathIn = 0;
                break;
            case IdleAction.LookAround:
                brain.idleUntil = now + randRange(IDLE_LOOK);
                break;
            case IdleAction.Spin:
                brain.idleSpinDir = Math.random() < 0.5 ? 1 : -1;
                brain.idleUntil = now + randRange(IDLE_SPIN);
                break;
            case IdleAction.ShootUp:
                brain.idleUntil = now + randRange(IDLE_SHOOTUP);
                break;
            case IdleAction.Loiter:
                brain.idleUntil = now + randRange(IDLE_LOITER);
                break;
        }
    };

    onInit(ctx, () => {
        // spawn each dummy spread out from the ones already placed (and from the
        // arena centre where players first appear), so they don't cluster.
        const placed: Vec3[] = [];
        const npcNodes: Node[] = [];
        for (let i = 0; i < NPC_COUNT; i++) {
            const home = pickSpawnPosition(ctx, placed);
            placed.push(home);
            const node = createNode({ name: `npc-wizard-${i}` });
            setPosition(addTrait(node, TransformTrait), home);
            addCharacter(node); // engine base-avatar placeholder; a platform avatar swaps in below
            // physics-grounded like a player: the server (owner of this
            // ownerless node) runs the controller sim — gravity, ground,
            // slopes. the steering below writes `input.move` / `look`;
            // idle (move = [0,0]) just stands.
            addTrait(node, CharacterControllerTrait);
            addChild(ctx.node, node);

            // plausible name (not "Dummy N") so NPCs read as people; hat tint by color.
            addTrait(node, WizardTrait, { color: NPC_COLORS[i % NPC_COLORS.length], name: randomDisplayName() });
            attachGear(node); // staff + hat onto the rig

            // combat state: killable dummy that respawns at home. WizardTrait
            // carries the health pool; AliveTrait marks it killable.
            addTrait(node, AliveTrait);
            addTrait(node, NpcTrait, { homeX: home[0], homeY: home[1], homeZ: home[2], archetype: i % NPC_ARCHETYPES.length });
            npcNodes.push(node);
        }

        // dress NPCs in real, varied avatars the platform supplies (popular/random —
        // the host decides). one bulk sample, round-robin onto the dummies; when the
        // platform sources none (dev/offline) they keep the engine base avatar.
        sampleAvatars(ctx)
            .then((sample) => {
                if (!sample.length) return;
                // load the batch once (refcounted), then round-robin assign onto NPCs.
                const loaded = sample.map((avatar) => loadAvatar(ctx, avatar));
                npcNodes.forEach((node, i) => {
                    const { modelId, rigType } = loaded[i % loaded.length]!;
                    assignAvatar(node, modelId, rigType);
                });
                // drop the refs when the world script disposes (room teardown / re-sample).
                onDispose(ctx, () => loaded.forEach((l) => releaseAvatar(ctx, l.modelId)));
            })
            .catch(() => {}); // host error → keep the base avatar
    });

    onTick(ctx, ({ delta }) => {
        const now = ctx.clock.time;
        // round-robin A* across ticks: a per-tick budget so many NPCs coming due on
        // the same tick don't all pathfind at once (the source of the tick spikes).
        let repathBudget = NPC_REPATHS_PER_TICK;

        // walk a brain toward `goal`, repathing on its timer while the shared budget
        // holds. closes over this tick's `delta` + `repathBudget`. returns followPath's
        // 'arrived' | 'traveling'. used by chase, wander, and gem-seek alike.
        const stepToward = (brain: Brain, controller: CharacterControllerTrait, pos: Vec3, goal: Vec3) => {
            brain.repathIn -= delta;
            const doRepath = brain.repathIn <= 0 && repathBudget > 0;
            if (doRepath) {
                repathBudget--;
                brain.repathIn = REPATH_INTERVAL;
            }
            return followPath(brain, controller, pos, goal, doRepath);
        };

        for (const [npc, controller, transform] of npcs) {
            // the server owns npcs, so it authors their held `casting` intent (the
            // same input the player's client authors for itself). default it closed
            // each tick → any non-engaged exit (dead, no target, out of range) holds
            // fire; the engaged branch below re-opens it for the burst window.
            const wiz = getTrait(npc._node, WizardTrait);
            if (wiz) wiz.casting = false;

            let brain = brains.get(npc._node.id);
            if (!brain) {
                brain = {
                    path: [],
                    waypoint: 0,
                    repathIn: 0,
                    fireWindowIn: Math.random() * NPC_BURST_PAUSE,
                    firing: false,
                    strafeDir: Math.random() < 0.5 ? 1 : -1,
                    strafeIn: 0,
                    jumpIn: Math.random() * JUMP_INTERVAL_MAX,
                    leveled: false,
                    idleAction: IdleAction.Loiter,
                    idleUntil: 0, // 0 → roll an idle activity on the first idle tick
                    wanderTarget: null,
                    idleSpinDir: 1,
                };
                brains.set(npc._node.id, brain);
            }

            // dead NPCs (no AliveTrait) just stand until they respawn; re-arm the
            // once-per-life leveling for their next spawn.
            if (!getTrait(npc._node, AliveTrait)) {
                brain.leveled = false;
                idle(controller);
                continue;
            }

            // on (re)spawn: set the baseline level near the players. then every tick
            // spend any available points — from that baseline OR from xp orbs picked
            // up while fighting — down the archetype build.
            if (wiz && !brain.leveled) {
                setNpcFloor(wiz);
                brain.leveled = true;
            }
            if (wiz) spendNpcPoints(wiz, NPC_ARCHETYPES[npc.archetype]!);

            const pos = getWorldPosition(transform);

            // nearest alive combatant (other than self) within chase range.
            let target: Vec3 | null = null;
            let bestDistSq = CHASE_RANGE * CHASE_RANGE;
            for (const [, , otherTransform] of combatants) {
                if (otherTransform._node.id === npc._node.id) continue; // not myself
                const pp = getWorldPosition(otherTransform);
                const dx = pp[0] - pos[0];
                const dy = pp[1] - pos[1];
                const dz = pp[2] - pos[2];
                const distSq = dx * dx + dy * dy + dz * dz;
                if (distSq < bestDistSq) {
                    bestDistSq = distSq;
                    target = [pp[0], pp[1], pp[2]];
                }
            }

            if (!target) {
                // no combatant in range → run an idle activity. (re)roll when the
                // current one's deadline passes; `casting` was already defaulted off.
                if (now >= brain.idleUntil) pickIdleAction(brain, pos, now);

                switch (brain.idleAction) {
                    case IdleAction.SeekGem: {
                        const gem = nearestGemWithin(pos, GEM_NOTICE_RADIUS * 1.5); // a little hysteresis past the notice radius
                        if (!gem) {
                            brain.idleUntil = 0; // gem gone → roll something else next tick
                            idle(controller);
                            break;
                        }
                        const eye: Vec3 = [pos[0], pos[1] + EYE_HEIGHT, pos[2]];
                        const dx = gem[0] - eye[0];
                        const dy = gem[1] - eye[1];
                        const dz = gem[2] - eye[2];
                        if (dx * dx + dy * dy + dz * dz < CAST_RANGE * CAST_RANGE && clearShot(eye, gem)) {
                            // in range with a clear line → stop, aim at it, and fire.
                            idle(controller);
                            aimAt(controller, eye, gem);
                            if (wiz) wiz.casting = true;
                        } else {
                            stepToward(brain, controller, pos, worldToCell(gem)); // walk toward it
                        }
                        break;
                    }
                    case IdleAction.Wander: {
                        if (!brain.wanderTarget) {
                            brain.idleUntil = 0;
                            idle(controller);
                            break;
                        }
                        if (stepToward(brain, controller, pos, worldToCell(brain.wanderTarget)) === 'arrived') {
                            brain.idleUntil = 0; // reached it → roll the next activity
                            idle(controller);
                        }
                        break;
                    }
                    case IdleAction.LookAround: {
                        idle(controller);
                        controller.input.look[1] += IDLE_LOOK_SPEED * delta; // slow sweep…
                        controller.input.look[2] = GAZE_DOWN; // …gaze toward the ground
                        break;
                    }
                    case IdleAction.Spin: {
                        idle(controller);
                        controller.input.look[1] += brain.idleSpinDir * IDLE_SPIN_SPEED * delta; // dizzy whirl
                        controller.input.look[2] = HALF_PI;
                        break;
                    }
                    case IdleAction.ShootUp: {
                        idle(controller);
                        controller.input.look[2] = GAZE_UP; // aim near-straight up
                        if (wiz) wiz.casting = true; // celebratory fountain
                        break;
                    }
                    default: {
                        // Loiter — just stand a beat, gaze level.
                        idle(controller);
                        controller.input.look[2] = HALF_PI;
                        break;
                    }
                }
                continue;
            }

            // engaged: within cast range with a clear shot → circle-strafe the
            // target, hop intermittently, and hold a burst window open (don't close to melee).
            const eye: Vec3 = [pos[0], pos[1] + EYE_HEIGHT, pos[2]];
            const aimPoint: Vec3 = [target[0], target[1] + CHEST_OFFSET, target[2]];
            const toAimX = aimPoint[0] - eye[0];
            const toAimY = aimPoint[1] - eye[1];
            const toAimZ = aimPoint[2] - eye[2];
            const inCastRange = toAimX * toAimX + toAimY * toAimY + toAimZ * toAimZ < CAST_RANGE * CAST_RANGE;
            if (inCastRange && clearShot(eye, aimPoint)) {
                // aim at the target (chest) — yaw + pitch into the same `look` the
                // server firing tick reads via lookDirection (identical for npcs + players).
                aimAt(controller, eye, aimPoint);

                // strafe sideways (facing the player → move[0] is left/right),
                // reversing direction on a jittered timer so they weave both ways.
                brain.strafeIn -= delta;
                if (brain.strafeIn <= 0) {
                    brain.strafeDir = -brain.strafeDir;
                    brain.strafeIn = STRAFE_FLIP_MIN + Math.random() * (STRAFE_FLIP_MAX - STRAFE_FLIP_MIN);
                }
                controller.input.move[0] = brain.strafeDir;
                controller.input.move[1] = 0;

                // hop intermittently (one-tick press → single jump).
                brain.jumpIn -= delta;
                controller.input.jump = brain.jumpIn <= 0;
                if (brain.jumpIn <= 0) brain.jumpIn = JUMP_INTERVAL_MIN + Math.random() * (JUMP_INTERVAL_MAX - JUMP_INTERVAL_MIN);

                // hold the burst window open / closed; the server fires at
                // stats.fireRate for as long as `casting` is held.
                brain.fireWindowIn -= delta;
                if (brain.fireWindowIn <= 0) {
                    brain.firing = !brain.firing;
                    brain.fireWindowIn = brain.firing ? NPC_BURST_DURATION : NPC_BURST_PAUSE;
                }
                if (wiz) wiz.casting = brain.firing;
                continue;
            }

            // chase: path toward the nearest target (shares the per-tick A* budget;
            // NPCs due past the budget are serviced on a later tick, which staggers
            // them off each other). reaching the path's end still out of cast range idles.
            if (stepToward(brain, controller, pos, worldToCell(target)) === 'arrived') idle(controller);
        }
    });
});

// ── client: first-person viewmodel ──────────────────────────────────
// the held staff under the camera: walk-bob, a channel-raise while casting, and the
// muzzle/charge tip fx for the local player's own shots (third-person viewers get
// these on the rig staff in wizard-visuals).
script(WorldTrait, 'viewmodel', (ctx) => {
    if (!env.client) return;

    const offset: Vec3 = [0.35, -0.5, -0.55];
    const sway = 0.05; // horizontal walk bob (m) at full speed
    const bounce = 0.05; // vertical footfall dip (m)
    const speedRef = 5; // walk speed (m/s) for full bob amplitude
    const airPerSpeed = 0.02; // airborne lift (m) per (m/s) of vertical velocity
    const airMax = 0.15; // airborne lift clamp (m)

    const basePitch = degreesToRadians(-20); // staff laid forward along the view
    // continuous "channeling" pose while holding cast: the staff just rises straight
    // up in view (no tilt), eased toward the held `casting` intent.
    const raiseLift = 0.15; // m — lift the whole staff up while channeling (+y is up here)
    const raiseEaseRate = 10; // 1/s — eases up while casting, down when it stops

    let bobBlend = 0; // eased walk amount (0..1)
    let air = 0; // eased airborne vertical offset (m); +y is down in this frame
    let raise = 0; // eased channel raise (0..1)
    let prevCastTime = -999; // last seen wizard.lastCastTime — edge fires the muzzle burst
    let chargeAccum = 0; // fractional charge particles owed this frame
    const _tip = vec3.create();
    const _fwd = vec3.create();
    const _viewmodelRot = quat.create(); // scratch for the per-frame staff pose

    onFrame(ctx, ({ delta }) => {
        const { node: cameraNode } = resolveCamera(ctx);

        // build the viewmodel once, under whichever camera is current.
        let viewmodel = findChildByName(cameraNode, 'viewmodel:staff');
        if (!viewmodel) {
            viewmodel = cloneModel(wizardModels.nodes.staff);
            viewmodel.name = 'viewmodel:staff';
            const transform = getTrait(viewmodel, TransformTrait)!;
            setPosition(transform, offset);
            setScale(transform, [0.5, 0.5, 0.5]);
            // lay the staff forward along the view instead of standing it up.
            setQuaternion(transform, quat.setAxisAngle(quat.create(), [1, 0, 0], basePitch));
            // floor the light so the held item stays readable in shadow.
            traverse(viewmodel, (node) => {
                const mesh = getTrait(node, MeshTrait);
                if (mesh) setMeshLitMin(mesh, 0.35);
            });
            addChild(cameraNode, viewmodel);
        }

        // visible only to the local player, only in first person.
        const controlNode = getControlNode(ctx);
        const playerController = controlNode && getTrait(controlNode, PlayerControllerTrait);
        const firstPerson = !!playerController && playerController.config.perspective === 'first';
        traverse(viewmodel, (node) => {
            const mesh = getTrait(node, MeshTrait);
            if (mesh) mesh.visible = firstPerson;
        });

        const characterController = controlNode && getTrait(controlNode, CharacterControllerTrait);
        if (!characterController) return;
        const { velocity, grounded, bobPhase } = characterController.state;

        // walk bob eases in with ground speed; airborne lift tracks vertical
        // velocity (clamped). both ease so stopping / landing don't snap.
        const speed = Math.hypot(velocity[0], velocity[2]);
        bobBlend += ((grounded ? Math.min(speed / speedRef, 1) : 0) - bobBlend) * Math.min(delta * 8, 1);
        const airTarget = grounded ? 0 : Math.max(-airMax, Math.min(airMax, -velocity[1] * airPerSpeed));
        air += (airTarget - air) * Math.min(delta * 10, 1);

        const wizard = controlNode && getTrait(controlNode, WizardTrait);

        // channel raise: ease toward the held `casting` intent — the staff lifts into
        // a ready pose while charging, drops back when we let go.
        const raiseTarget = wizard?.casting ? 1 : 0;
        raise += (raiseTarget - raise) * Math.min(delta * raiseEaseRate, 1);

        // sway side-to-side once per stride (`sin`), dip down each footfall
        // (`abs(sin)`, +y is down); airborne lift + channel raise ride on top.
        const transform = getTrait(viewmodel, TransformTrait)!;
        setPosition(transform, [
            offset[0] + Math.sin(bobPhase) * sway * bobBlend,
            offset[1] + Math.abs(Math.sin(bobPhase)) * bounce * bobBlend + air + raise * raiseLift,
            offset[2],
        ]);
        setQuaternion(transform, quat.setAxisAngle(_viewmodelRot, [1, 0, 0], basePitch));

        // first-person tip fx: the muzzle blast on each shot (the `lastCastTime` edge)
        // and a continuous charge glow while channeling, both at the viewmodel staff
        // tip in view. third-person viewers get these on the rig staff elsewhere.
        if (firstPerson && wizard) {
            vec3.transformMat4(_tip, STAFF_TIP_LOCAL, getWorldMatrix(transform));
            if (wizard.lastCastTime !== prevCastTime) {
                prevCastTime = wizard.lastCastTime;
                const camQuat = getWorldQuaternion(getTrait(cameraNode, TransformTrait)!);
                muzzleBurst(ctx, [_tip[0], _tip[1], _tip[2]], vec3.transformQuat(_fwd, [0, 0, -1], camQuat));
            }
            if (wizard.casting) {
                chargeAccum += CHARGE_RATE * delta;
                while (chargeAccum >= 1) {
                    chargeGlow(ctx, _tip);
                    chargeAccum -= 1;
                }
            } else {
                chargeAccum = 0;
            }
        }
    });
});

// ── client: impact / death / damage / trail particles ───────────────

// for a terrain hit we reuse the block's auto-derived dust SPRITE, but in our own
// particle (our motion + spawn opts) rather than its dust particle — so we keep full
// control. cached per sprite (a ParticleHandle is pure data). dust motion: stronger
// gravity than the stock `particleUpdate.dust` (−20) so the burst flies out then
// snaps back down, with less drag so it carries further.
const dustMotion: typeof particleUpdate.dust = (pool, i, dt, voxels) => {
    particleUpdate.gravity(pool, i, dt, -36);
    particleUpdate.drag(pool, i, dt, 0.97);
    particleUpdate.integrate(pool, i, dt);
    particleUpdate.collideSlide(pool, i, dt, voxels);
};
const dustFx = new Map<string, ParticleHandle>();
const dustParticleFor = (sprite: SpriteHandle): ParticleHandle => {
    let p = dustFx.get(sprite.spriteId);
    if (!p) {
        const id = `wizards:dust:${sprite.spriteId}`;
        p = { typeId: id, name: id, dependency: { registry: 'particles', id }, sprite, playback: 'stretch', fps: 0, update: dustMotion, glow: 0, tint: [1, 1, 1, 1] };
        dustFx.set(sprite.spriteId, p);
    }
    return p;
};

// the impact burst for a bolt landing at `pos`. shared by the authoritative
// ImpactCommand (remote bolts) and the client-side predicted hit (own bolts), so
// both look identical. `block` (>0) → that block's dust sprite; else a white spark.
function spawnImpactVfx(ctx: ScriptContext, pos: Vec3, fizzle: boolean, block: number, radius: number): void {
    // a real hit lands its impact sound here (covers both the authoritative
    // ImpactCommand and the owner's locally-predicted hit). a fizzle just
    // expired mid-air, so it stays silent.
    // gentle falloff: full up close, still clearly audible across the arena.
    // (engine default ref=1/rolloff=1 is ~1/distance — a 20m hit lands at ~5%.)
    if (!fizzle) playAt(ctx, sounds.impact, pos, { falloff: { ref: 12, rolloff: 0.4 }, detune: (Math.random() * 2 - 1) * 120 });

    // spray outward FROM the impact point. speed scales with the splash radius (so the
    // fastest debris reaches ~the damage zone) and varies a lot per particle — the
    // (0.2..1) factor is what keeps it a natural burst instead of a uniform expanding
    // shell. count scales mildly with the radius (capped, chromebook-friendly). a
    // fizzle is a small fixed mid-air puff.
    const blast = fizzle ? 1 : Math.max(0.5, Math.min(2.5, radius / DEFAULT_PROJECTILE_STATS.damageRadius));
    const dust = block > 0 ? ctx.blocks.particles[block]?.dust : undefined;
    const count = Math.round((fizzle ? 3 : dust?.length ? 20 : 8) * blast);
    const spray = fizzle ? 3 : Math.max(2.5, radius * 2.2); // peak outward speed ≈ reaches the radius over a particle's life
    for (let i = 0; i < count; i++) {
        const d = randomDir();
        const spd = spray * (0.2 + 0.8 * Math.random()); // varied reach → non-uniform burst
        if (dust?.length) {
            // block dust: its sprite, our control — fly out + loft, then the dust
            // motion (gravity + terrain collide) arcs it down and settles it.
            spawnParticle(ctx, dustParticleFor(dust[i % dust.length]!.sprite), pos, {
                lifetime: varyLife(1.0),
                size: 0.12,
                glow: 0.4,
                tint: [1.4, 1.4, 1.4, 1], // a touch lighter than the raw block texture
                velX: d[0] * spd,
                velY: Math.abs(d[1]) * spd + 2,
                velZ: d[2] * spd,
            });
        } else {
            spawnParticle(ctx, ImpactFx, pos, {
                lifetime: varyLife(0.5),
                size: 0.1,
                glow: 1,
                velX: d[0] * spd,
                velY: d[1] * spd,
                velZ: d[2] * spd,
            });
        }
    }
}

// muzzle blast at `at` (world space) spraying along unit `forward` with scatter.
// fired on each authoritative ProjectileCast — never predicted.
function muzzleBurst(ctx: ScriptContext, at: Vec3, forward: Vec3): void {
    const MUZZLE_COUNT = 5;
    const MUZZLE_SPEED = 8; // m/s along the fire direction
    const MUZZLE_SCATTER = 2.2; // m/s random spread
    const MUZZLE_LIFE = 0.4; // s base (varied ±35%)
    const MUZZLE_SIZE = 0.07; // m
    for (let i = 0; i < MUZZLE_COUNT; i++) {
        const s = randomDir();
        spawnParticle(ctx, ImpactFx, at, {
            lifetime: varyLife(MUZZLE_LIFE),
            size: MUZZLE_SIZE,
            emissive: 1,
            velX: forward[0] * MUZZLE_SPEED + s[0] * MUZZLE_SCATTER,
            velY: forward[1] * MUZZLE_SPEED + s[1] * MUZZLE_SCATTER,
            velZ: forward[2] * MUZZLE_SPEED + s[2] * MUZZLE_SCATTER,
        });
    }
}

// one charge spark at `at` (world space) — a small emissive crackle with gentle
// random drift. callers emit these at CHARGE_RATE while a wizard is channeling.
function chargeGlow(ctx: ScriptContext, at: Vec3): void {
    const CHARGE_SPREAD = 0.08; // m — random offset sphere around the tip
    const CHARGE_SWIRL = 0.7; // m/s — gentle random drift
    const CHARGE_LIFE = 0.25; // s base (varied ±35%)
    const CHARGE_SIZE = 0.03; // m
    const o = randomDir();
    const v = randomDir();
    spawnParticle(ctx, ChargeFx, [at[0] + o[0] * CHARGE_SPREAD, at[1] + o[1] * CHARGE_SPREAD, at[2] + o[2] * CHARGE_SPREAD], {
        lifetime: varyLife(CHARGE_LIFE),
        size: CHARGE_SIZE,
        glow: 1,
        emissive: 1,
        velX: v[0] * CHARGE_SWIRL,
        velY: v[1] * CHARGE_SWIRL,
        velZ: v[2] * CHARGE_SWIRL,
    });
}

// build a client-only bolt: a `realm:'client'` ProjectileTrait node (never
// networked) with the cloned projectile mesh. spawned from a ProjectileCast — every
// bolt is server-authoritative now, including our own. clients derive the flight
// from `origin` + the seeded clock and render the visual; damage stays on the server.
const _boltDir = vec3.create();

// the bolt's visual size lerps with its damage — purely cosmetic (collision is the
// analytic raycast, not the mesh, so size never affects hits). base damage ≈ 1/3 the
// authored mesh; max damage a touch bigger; the authored size (1.0) sits a bit above
// the midpoint. BOLT_SCALE_MIN/MAX are the only knobs.
const MAX_BOLT_DAMAGE = lvlValue('damage', STAT_TABLE.damage.max);
const BOLT_SCALE_MIN = 0.34; // base-damage bolt
const BOLT_SCALE_MAX = 2.6; // max-damage bolt
const boltScale = (damage: number): number => {
    const t = Math.max(0, Math.min(1, (damage - DEFAULT_PROJECTILE_STATS.damage) / (MAX_BOLT_DAMAGE - DEFAULT_PROJECTILE_STATS.damage)));
    return BOLT_SCALE_MIN + (BOLT_SCALE_MAX - BOLT_SCALE_MIN) * t;
};

function spawnClientBolt(ctx: ScriptContext, info: { id: number; ownerId: number; origin: Vec3; aim: Quat; stats: ProjectileStats; spawnTime: number }): void {
    const node = createNode({ name: 'bolt', realm: 'client' });
    setPosition(addTrait(node, TransformTrait), info.origin);
    addTrait(node, ProjectileTrait, {
        id: info.id,
        ownerId: info.ownerId,
        spawnTime: info.spawnTime,
        aim: [info.aim[0], info.aim[1], info.aim[2], info.aim[3]],
        stats: info.stats,
        origin: [info.origin[0], info.origin[1], info.origin[2]],
    });
    const visual = cloneModel(wizardModels.nodes.projectile);
    visual.name = 'bolt:visual';
    const vtr = getTrait(visual, TransformTrait)!;
    setPosition(vtr, [0, 0, 0]);
    const s = boltScale(info.stats.damage); // 1.0 ≈ the authored mesh size
    setScale(vtr, [s, s, s]);
    addChild(node, visual);
    addChild(ctx.node, node);
}

script(WorldTrait, 'combat-vfx', (ctx) => {
    if (!env.client) return;

    // purely-visual bolt spin (the node faces its aim down -Z; this rolls it).
    const PROJECTILE_SPIN_SPEED = 12; // rad/s — roll around the travel axis while flying
    const PROJECTILE_SPIN_AXIS: Vec3 = [0, 0, 1]; // local forward/back

    // every bolt is a `realm:'client'` ProjectileTrait node (never networked) — one
    // query renders them all uniformly, ours and others' alike.
    const clientBolts = query(ctx, [ProjectileTrait, TransformTrait]);
    const _muzzleFwd = vec3.create();

    // a bolt was cast — spawn its local copy + fire the muzzle. broadcast to everyone
    // (no prediction), so we branch on `ownerId`: our own cast routes the muzzle to
    // the first-person viewmodel tip (handled in `viewmodel` off `lastCastTime`) and
    // plays the loud non-positional sound; others' casts pop a muzzle at the world
    // origin and a positional sound that pans/falls off with distance.
    listen(ctx, ProjectileCast, ({ id, ownerId, origin, aim, speed, spawnTime, damage }) => {
        spawnClientBolt(ctx, {
            id,
            ownerId,
            origin: [origin[0], origin[1], origin[2]],
            aim: [aim[0], aim[1], aim[2], aim[3]],
            stats: { ...DEFAULT_PROJECTILE_STATS, speed, damage }, // speed → flight, damage → visual size
            spawnTime,
        });

        const controlNode = getControlNode(ctx);
        if (controlNode && ownerId === controlNode.id) {
            // our own cast: loud non-positional sound; stamp the cast edge so the
            // viewmodel fires the muzzle + recoil at the staff tip in view.
            const selfWizard = getTrait(controlNode, WizardTrait);
            if (selfWizard) selfWizard.lastCastTime = ctx.clock.time;
            playMono(ctx, sounds.cast, { volume: 0.5, detune: (Math.random() * 2 - 1) * 150 });
            // only the third-person view needs a world-space muzzle; first person gets
            // it at the viewmodel tip instead (avoids a doubled blast downrange).
            if (getTrait(controlNode, PlayerControllerTrait)?.config.perspective !== 'first') {
                muzzleBurst(ctx, [origin[0], origin[1], origin[2]], vec3.transformQuat(_muzzleFwd, [0, 0, -1], aim as Quat));
            }
        } else {
            // another wizard's cast: positional sound + a world-space muzzle at its staff.
            playAt(ctx, sounds.cast, [origin[0], origin[1], origin[2]], { volume: 0.4, falloff: { ref: 6, rolloff: 0.9 }, detune: (Math.random() * 2 - 1) * 150 });
            muzzleBurst(ctx, [origin[0], origin[1], origin[2]], vec3.transformQuat(_muzzleFwd, [0, 0, -1], aim as Quat));
        }
    });

    // a bolt landed — destroy its local copy and play the impact. broadcast to every
    // client now (no prediction), so this also covers our own bolts.
    listen(ctx, ImpactCommand, ({ id, pos, fizzle, block, radius }) => {
        for (const [bolt, transform] of clientBolts) {
            if (bolt.id === id) {
                destroyNode(transform._node);
                break;
            }
        }
        spawnImpactVfx(ctx, pos as Vec3, fizzle, block, radius);
    });

    listen(ctx, DeathCommand, ({ pos }) => {
        const at: Vec3 = [pos[0], pos[1] + 1, pos[2]];
        for (let i = 0; i < 40; i++) {
            const d = randomDir();
            spawnParticle(ctx, DeathFx, at, {
                lifetime: varyLife(1.8),
                size: 0.14,
                glow: 1,
                velX: d[0] * 8,
                velY: Math.abs(d[1]) * 9 + 3,
                velZ: d[2] * 8,
            });
        }
    });

    // damage feedback — a small pop for now; floating numbers later.
    listen(ctx, DamageCommand, ({ pos, tier }) => {
        // gem hits (tier ≥ 0) pop in that gem's colour; wizard hits stay white.
        const fx = tier >= 0 ? (GemShatterFx[tier] ?? GemShatterFx[0]!) : ImpactFx;
        const at: Vec3 = [pos[0], pos[1], pos[2]];
        for (let i = 0; i < 6; i++) {
            const d = randomDir();
            spawnParticle(ctx, fx, at, {
                lifetime: varyLife(0.7),
                size: 0.08,
                emissive: 1,
                velX: d[0] * 3.5,
                velY: d[1] * 3.5 + 1.5,
                velZ: d[2] * 3.5,
            });
        }
    });

    // per frame: derive each client bolt's position from its cast, spin it, trail it,
    // and reap on expiry. no synced positions — the whole flight is reconstructed
    // locally from the seeded clock; the server owns hits + sends the impact.
    let frameNo = 0;
    onFrame(ctx, () => {
        frameNo++;
        const serverNow = ctx.clock.server; // shared timeline (anchors the flight; see below)
        const wallNow = ctx.clock.wall; // smooth per-render-frame clock (engine-provided)
        const reap: Node[] = []; // destroying mid-iteration is unsafe
        for (const [bolt, transform] of clientBolts) {
            const speed = bolt.stats.speed;
            // anchor the flight to the smooth wall clock on first sight, using
            // `serverNow` to place it correctly along its path: the spawnTime is the
            // SERVER clock, so on every client (a touch behind by join latency) the
            // bolt lands slightly in the past — its despawn meets the authoritative
            // impact. then advance by WALL time so motion is smooth at any refresh
            // rate — `serverNow` only steps at the 60Hz tick.
            if (bolt.wallSpawn < 0) bolt.wallSpawn = wallNow - Math.max(0, serverNow - bolt.spawnTime);
            const elapsed = Math.max(0, wallNow - bolt.wallSpawn);

            const dir = vec3.transformQuat(_boltDir, [0, 0, -1], bolt.aim);
            const px = bolt.origin[0] + dir[0] * speed * elapsed;
            const py = bolt.origin[1] + dir[1] * speed * elapsed;
            const pz = bolt.origin[2] + dir[2] * speed * elapsed;

            // id-hashed roll for visual variety; position + trail.
            const ph = hash32(bolt.id, 0);
            const spinSpeed = PROJECTILE_SPIN_SPEED * (0.5 + (hashUnit(ph, 6) + 0.5)) * (hashUnit(ph, 7) < 0 ? -1 : 1);
            quat.setAxisAngle(_rotation, PROJECTILE_SPIN_AXIS, spinSpeed * elapsed);
            setPosition(transform, [px, py, pz]);
            setQuaternion(transform, quat.multiply(_orientation, bolt.aim, _rotation));
            const h = hash32(bolt.id, frameNo);
            spawnParticle(ctx, TrailVariants[h % TrailVariants.length], [px, py, pz], {
                lifetime: 0.6 * (0.65 + (hashUnit(h, 4) + 0.5) * 0.7),
                size: 0.1,
                glow: 1,
                seed: h,
                velX: hashUnit(h, 1) * 1.4,
                velY: hashUnit(h, 2) * 1.4,
                velZ: hashUnit(h, 3) * 1.4,
            });

            // expire at lifetime as a safety net — the authoritative ImpactCommand
            // normally reaps a bolt first (on hit or fizzle), so this just cleans up
            // any straggler whose impact message was dropped.
            if (elapsed > PROJECTILE_LIFETIME) reap.push(transform._node);
        }
        for (const n of reap) destroyNode(n);
    });
});

// ── client: wizard visuals ──────────────────────────────────────────
// everything about how a wizard looks on the client (gear is attached at the
// spawn sites). per wizard: tint the hat to its colour, raise the right arm while
// it's casting (the replicated `casting` flag), flash the body red on taking
// damage, dither out on death / back in on respawn, and on death drop a
// client-only sway-fall hat. the arm-raise composes in onPostAnimate (after
// CharacterTrait's procedural swing); the rest is plain per-frame mesh work.

script(WorldTrait, 'wizard-visuals', (ctx) => {
    if (!env.client) return;

    const wizards = query(ctx, [WizardTrait, TransformTrait]);

    // damage flash — red body flash + glow pulse to 1 then back to 0 on taking a hit.
    const DAMAGE_FLASH_DURATION = 0.2; // s
    const FLASH_TINT: Vec4 = [1, 0, 0, 0]; // red; alpha (flash strength) set per use

    // falling hat — scripted pendulum sway-fall on death; outlives the respawn so you
    // come back hatted while the old one settles.
    const HAT_LIFETIME = 6; // s before the dropped hat despawns
    const HAT_FALL_SPEED = 0.6; // m/s descent
    const HAT_SWING_FREQ = 2.8; // pendulum rad/s
    const HAT_SWING_AMPLITUDE = 0.18; // m side-to-side
    const HAT_SWING_TILT = 0.4; // rad tilt
    const HAT_SWING_DAMPING = 0.35; // 1/s envelope decay

    const armRaiseAngle = degreesToRadians(80); // arm_right local X — staff lifts toward the aim at full raise
    // scratch quats for the third-person cast pose (raise arm_right on top of the procedural swing).
    const _castArmRaise = quat.create();
    const _castArmPose = quat.create();
    const raiseEaseRate = 8; // 1/s — arm eases up while casting / down when it stops
    const FADE_SPEED = 6; // 1/s — death dither lerp (~0.5s in/out)
    const NAMEPLATE_MAX_DIST = 30; // m — hide nameplates beyond this
    const _npRay = createVoxelRaycastResult(); // reused for nameplate occlusion checks

    type Hat = { node: Node; spawnTime: number; startX: number; startY: number; startZ: number; floorY: number; baseRot: Quat };
    const state = new Map<number, { dither: number; dead: boolean; flash: number; prevHealth: number; npSig: string; hatLevel: number; chargeAccum: number }>();
    const _wvTip = vec3.create(); // scratch for the third-person staff-tip charge glow
    const hats: Hat[] = [];

    // red flash + glow on the body meshes only — prune the hat/staff subtrees.
    // flash rides its own channel, so it overlays the persistent team tint
    // rather than clobbering it.
    const flashBody = (entityNode: Node, flash: number) => {
        FLASH_TINT[3] = flash;
        traverse(entityNode, (n) => {
            if (n.name === 'wizard:hat' || n.name === 'wizard:staff') return false; // skip accessories
            const mesh = getTrait(n, MeshTrait);
            if (mesh) {
                setMeshFlash(mesh, FLASH_TINT);
                setMeshGlow(mesh, flash);
            }
        });
    };

    // drop a client-only hat at the entity's *visual* hat pose (so it lands where
    // this client sees the hat, not the server rig) to sway-fall and despawn.
    const dropHat = (entityNode: Node, now: number) => {
        const equipped = findChildByName(entityNode, 'wizard:hat');
        if (!equipped) return;
        const wp = getWorldPosition(getTrait(equipped, TransformTrait)!);
        const wq = getWorldQuaternion(getTrait(equipped, TransformTrait)!);
        const feet = getWorldPosition(getTrait(entityNode, TransformTrait)!);
        const wizard = getTrait(entityNode, WizardTrait);
        const color: Vec4 = wizard ? hexTint(tierColor(levelForXp(wizard.xp))) : [1, 1, 1, 1];

        const node = cloneModel(wizardModels.nodes.hat); // client-created → local only
        node.name = 'falling-hat';
        const transform = getTrait(node, TransformTrait)!;
        setPosition(transform, [wp[0], wp[1], wp[2]]);
        setQuaternion(transform, [wq[0], wq[1], wq[2], wq[3]]);
        traverse(node, (n) => {
            const mesh = getTrait(n, MeshTrait);
            if (mesh) setMeshTint(mesh, color);
        });
        addChild(ctx.node, node);
        hats.push({ node, spawnTime: now, startX: wp[0], startY: wp[1], startZ: wp[2], floorY: feet[1] + 0.1, baseRot: [wq[0], wq[1], wq[2], wq[3]] });
    };

    // build a wizard's nameplate DOM — name + level over an hp bar, outlined for
    // legibility. only called when a value changes (diff-gated by the caller).
    const paintNameplate = (el: HTMLElement, name: string, level: number, hp: number, max: number) => {
        // row 1: name.
        // row 1: level badge + name.
        const top = document.createElement('div');
        top.style.cssText = 'display:flex; align-items:center; justify-content:center; gap:4px; margin-bottom:2px;';
        const lvlBox = document.createElement('div');
        lvlBox.textContent = `Lv ${level}`;
        lvlBox.style.cssText = `flex:none; padding:1px 4px; box-sizing:border-box; background:${tierColor(level)}; border:1px solid #000; border-radius:4px; font-size:9px; line-height:1; font-weight:bold; color:#fff; ${HUD_OUTLINE}`;
        const nameEl = document.createElement('div');
        nameEl.textContent = name; // textContent = safe from username markup
        nameEl.style.cssText = `font-size:12px; font-weight:bold; color:#fff; white-space:nowrap; ${HUD_OUTLINE}`;
        top.append(lvlBox, nameEl);
        // row 2: health bar with N/N.
        const bar = document.createElement('div');
        bar.style.cssText =
            'position:relative; display:flex; align-items:center; justify-content:center; width:92px; height:13px; margin:0 auto; background:#222; border:1px solid #000; border-radius:4px; overflow:hidden; box-sizing:border-box;';
        const pct = max > 0 ? Math.max(0, Math.min(1, hp / max)) : 0;
        const fill = document.createElement('div');
        fill.style.cssText = `position:absolute; left:0; top:0; bottom:0; width:${pct * 100}%; background:${pct > 0.5 ? '#22c55e' : pct > 0.25 ? '#eab308' : '#dc2626'};`;
        const hpText = document.createElement('div');
        hpText.textContent = `${Math.ceil(hp)}/${max}`;
        hpText.style.cssText = `position:relative; font-size:9px; font-weight:bold; color:#fff; ${HUD_OUTLINE}`;
        bar.append(fill, hpText);
        el.replaceChildren(top, bar);
    };

    // per-frame mesh reactions to each wizard's state: hat tint, damage flash,
    // death dither — plus the dropped-hat sim.
    onFrame(ctx, ({ delta }) => {
        const now = ctx.clock.time;
        const controlNode = getControlNode(ctx);
        const controlId = controlNode?.id ?? -1; // skip our own nameplate
        // our own wizard's tip glow is the first-person viewmodel's job (see `viewmodel`)
        // while we're in first person; in third person the rig-staff glow below covers it.
        const localFirstPerson = controlNode ? getTrait(controlNode, PlayerControllerTrait)?.config.perspective === 'first' : false;
        const camPos = getWorldPosition(getTrait(resolveCamera(ctx).node, TransformTrait)!);

        for (const [wizard, transform] of wizards) {
            const node = transform._node;

            const dead = wizard.current <= 0;
            let s = state.get(node.id);
            if (!s) {
                s = { dither: 0, dead: false, flash: 0, prevHealth: wizard.current, npSig: '', hatLevel: -1, chargeAccum: 0 };
                state.set(node.id, s);
            }

            // hat: tint to the level tier + scale with level (re-applied on a level
            // change, and once the replicated hat first appears). resets toward gray
            // + base size when the wizard's levels reset on death.
            const level = levelForXp(wizard.xp);
            const hat = findChildByName(node, 'wizard:hat');
            if (hat && s.hatLevel !== level) {
                s.hatLevel = level;
                const tint = hexTint(tierColor(level));
                const scale = tierScale(level);
                const ht = getTrait(hat, TransformTrait);
                if (ht) setScale(ht, [scale, scale, scale]);
                traverse(hat, (n) => {
                    const mesh = getTrait(n, MeshTrait);
                    if (mesh) setMeshTint(mesh, tint);
                });
            }

            // damage flash: start at 1 on any health drop, decay to 0 over the
            // duration. red tint + glow on the body only.
            if (wizard.current < s.prevHealth) s.flash = 1;
            s.prevHealth = wizard.current;
            if (s.flash > 0) {
                s.flash = Math.max(0, s.flash - delta / DAMAGE_FLASH_DURATION);
                flashBody(node, s.flash); // applies 0 on the last step → resets the body
            }

            // drop the hat once, on the death transition.
            if (dead && !s.dead) dropHat(node, now);
            s.dead = dead;

            // dither the character out (dead) / back in (alive). hand the eased
            // value to CharacterTrait so the engine composes it (max) with its
            // death is the only thing that drives the mesh dither, so walking near a
            // dead body leaves its fade alone (proximity/POV never un-hides it).
            const target = dead ? 1 : 0;
            if (s.dither !== target) {
                let next = s.dither + (target - s.dither) * Math.min(delta * FADE_SPEED, 1);
                if (Math.abs(next - target) < 0.01) next = target;
                s.dither = next;
            }
            const character = getTrait(node, CharacterTrait);
            if (character) character.state.externalDither = s.dither;

            // channel charge glow at the rig staff tip while this wizard casts — the
            // same tell other players read on us, and what we see on ourselves in
            // third person (first person routes our glow through the viewmodel instead).
            const showCharge = wizard.casting && !dead && !(node.id === controlId && localFirstPerson);
            if (showCharge) {
                const staff = findChildByName(node, 'wizard:staff');
                if (staff) {
                    vec3.transformMat4(_wvTip, STAFF_TIP_LOCAL, getWorldMatrix(getTrait(staff, TransformTrait)!));
                    s.chargeAccum += CHARGE_RATE * delta;
                    while (s.chargeAccum >= 1) {
                        chargeGlow(ctx, _wvTip);
                        s.chargeAccum -= 1;
                    }
                }
            } else {
                s.chargeAccum = 0;
            }

            // nameplate (other wizards only): name + level + hp on a billboard
            // canvas above the head; hidden when dead, far, or occluded by terrain.
            if (node.id !== controlId) {
                let plate = findChildByName(node, 'nameplate');
                if (!plate) {
                    plate = createNode({ name: 'nameplate' });
                    setPosition(addTrait(plate, TransformTrait), [0, 3.1, 0]);
                    // screen-mode html overlay at constant css size (distanceFactor null)
                    // → readable at any distance, unlike the shrinking world quad.
                    const h = addTrait(plate, HtmlTrait, { mode: 'screen', center: true, distanceFactor: null });
                    const e = h.element;
                    if (e) {
                        e.style.pointerEvents = 'none';
                        e.style.fontFamily = 'ui-monospace, monospace';
                        e.style.textAlign = 'center';
                    }
                    addChild(node, plate);
                }
                const wp = getWorldPosition(transform);
                const hx = wp[0] - camPos[0];
                const hy = wp[1] + 1.5 - camPos[1];
                const hz = wp[2] - camPos[2];
                const camDist = Math.hypot(hx, hy, hz) || 1;
                let visible = !dead && camDist < NAMEPLATE_MAX_DIST;
                if (visible) {
                    // occluded if terrain is hit before reaching the wizard.
                    raycastVoxels(_npRay, ctx.voxels, ctx.voxels.registry, camPos[0], camPos[1], camPos[2], hx / camDist, hy / camDist, hz / camDist, camDist, 0);
                    if (_npRay.hit && _npRay.distance < camDist) visible = false;
                }
                const el = getTrait(plate, HtmlTrait)!.element;
                if (el) {
                    if (!visible) {
                        el.style.visibility = 'hidden';
                        s.npSig = ''; // repaint when shown again
                    } else {
                        el.style.visibility = 'visible';
                        const level = levelForXp(wizard.xp);
                        const max = maxHealthOf(wizard.stats.levels);
                        const sig = `${wizard.name}|${level}|${wizard.current}/${max}`;
                        if (sig !== s.npSig) {
                            s.npSig = sig;
                            paintNameplate(el, wizard.name, level, wizard.current, max);
                        }
                    }
                }
            }
        }

        // sim + despawn the local falling hats.
        for (let i = hats.length - 1; i >= 0; i--) {
            const hat = hats[i]!;
            const age = now - hat.spawnTime;
            if (age > HAT_LIFETIME) {
                destroyNode(hat.node);
                hats.splice(i, 1);
                continue;
            }
            const envelope = Math.exp(-HAT_SWING_DAMPING * age);
            const swing = Math.sin(age * HAT_SWING_FREQ) * HAT_SWING_AMPLITUDE * envelope;
            const tilt = Math.sin(age * HAT_SWING_FREQ) * HAT_SWING_TILT * envelope;
            const y = Math.max(hat.floorY, hat.startY - HAT_FALL_SPEED * age);
            const transform = getTrait(hat.node, TransformTrait)!;
            setPosition(transform, [hat.startX + swing, y, hat.startZ]);
            quat.setAxisAngle(_rotation, [0, 0, 1], tilt);
            setQuaternion(transform, quat.multiply(_orientation, hat.baseRot, _rotation));
        }
    });

    // cast arm-raise — composed onto the rig *after* the procedural swing.
    onPostAnimate(ctx, ({ delta }) => {
        for (const [wizard] of wizards) {
            const target = wizard.casting ? 1 : 0;
            wizard.armRaise += (target - wizard.armRaise) * Math.min(delta * raiseEaseRate, 1);
            if (wizard.armRaise < 0.01) continue;
            const arm = findByName(wizard._node, RIG_6BONE_ARM_RIGHT);
            if (!arm) continue;
            const armTransform = getTrait(arm, TransformTrait)!;
            quat.setAxisAngle(_castArmRaise, [1, 0, 0], wizard.armRaise * armRaiseAngle);
            setQuaternion(armTransform, quat.multiply(_castArmPose, armTransform.quaternion, _castArmRaise));
        }
    });
});

// ── client: HUD ─────────────────────────────────────────────────────
// screen-space DOM into the viewport, all driven by the local player's synced
// WizardTrait: bottom-centre health + xp pill bars (styled like the stat panel),
// a top-left upgrade panel, and a top-right scoreboard. each section is diff-gated
// — the DOM is only touched when its rendered values change.

// shared with the panel: bold white text outline so HUD copy reads over any scene.
const HUD_OUTLINE = 'text-shadow:-1px -1px 0 #000,1px -1px 0 #000,-1px 1px 0 #000,1px 1px 0 #000;';

script(WorldTrait, 'hud', (ctx) => {
    if (!env.client) return;
    const viewport = ctx.client?.viewport;
    if (!viewport) return;

    const wizards = query(ctx, [WizardTrait]);
    const mobile = isMobile(ctx); // compact, touch-friendly HUD on phones

    // the round end (server clock), pushed once by the server on join. the network
    // hop means this listener is registered before the message lands.
    let roundEndsAt = 0;
    listen(ctx, RoundInfo, ({ endsAt }) => {
        roundEndsAt = endsAt;
    });

    // top-centre: round countdown (mm:ss), turns red over the final seconds.
    const clock = document.createElement('div');
    clock.style.cssText = `position:absolute; top:${mobile ? 8 : 12}px; left:50%; transform:translateX(-50%); background:#383838; border-radius:${mobile ? 8 : 10}px; padding:${mobile ? '3px 9px' : '5px 14px'}; box-sizing:border-box; font-family:ui-monospace,monospace; font-size:${mobile ? 12 : 16}px; font-weight:bold; color:#fff; pointer-events:none; z-index:${UILayer.hud}; ${HUD_OUTLINE}`;

    // bottom-centre: rounded health + xp pill bars, matching the stat panel — a
    // dark pill with a coloured fill behind a centred, outlined label.
    const makeBar = (fillColor: string) => {
        const wrap = document.createElement('div');
        wrap.style.cssText = `position:relative; width:${mobile ? 190 : 300}px; height:${mobile ? 18 : 24}px; border-radius:${mobile ? 9 : 12}px; background:#383838; overflow:hidden;`;
        const fill = document.createElement('div');
        fill.style.cssText = `position:absolute; left:0; top:0; bottom:0; width:0%; background:${fillColor};`;
        const label = document.createElement('div');
        label.style.cssText = `position:absolute; inset:0; display:flex; align-items:center; justify-content:center; font-size:${mobile ? 10 : 12}px; font-weight:bold; color:#fff; ${HUD_OUTLINE}`;
        wrap.append(fill, label);
        return { wrap, fill, label };
    };
    const healthBar = makeBar('#e8324a');
    const xpBar = makeBar('#8ce06e');
    const bottom = document.createElement('div');
    bottom.style.cssText =
        `position:absolute; left:50%; bottom:24px; transform:translateX(-50%); display:flex; flex-direction:column; align-items:center; gap:6px; font-family:ui-monospace,monospace; pointer-events:none; z-index:${UILayer.hud};`;
    bottom.append(healthBar.wrap, xpBar.wrap);

    // leaderboard (top-right): a dark rounded panel with a Name | K | D table.
    const board = document.createElement('div');
    board.style.cssText = `position:absolute; top:${mobile ? 8 : 12}px; right:${mobile ? 8 : 12}px; min-width:${mobile ? 110 : 180}px; background:#383838; border-radius:${mobile ? 8 : 10}px; padding:${mobile ? '4px 7px 5px' : '6px 10px 8px'}; box-sizing:border-box; font-family:ui-monospace,monospace; font-size:${mobile ? 9 : 12}px; color:#fff; pointer-events:none; z-index:${UILayer.hud}; ${HUD_OUTLINE}`;
    const boardTitle = document.createElement('div');
    boardTitle.textContent = 'SCORES';
    boardTitle.style.cssText = 'text-align:center; font-weight:bold; margin-bottom:5px;';
    const boardGrid = document.createElement('div');
    boardGrid.style.cssText = 'display:grid; grid-template-columns:1fr auto auto; gap:3px 12px; align-items:center;';
    board.append(boardTitle, boardGrid);
    const cell = (text: string, css = ''): HTMLSpanElement => {
        const c = document.createElement('span');
        c.textContent = text; // textContent = safe from username markup
        c.style.cssText = css;
        return c;
    };

    // upgrade panel (top-left): each stat row has a tappable + button (works on
    // touch too); number keys 1–N are a desktop shortcut for the same command.
    const panel = document.createElement('div');
    panel.style.cssText = `position:absolute; top:12px; left:12px; width:240px; display:flex; flex-direction:column; gap:6px; font-family:ui-monospace,monospace; z-index:${UILayer.hud};`;
    const panelHeader = document.createElement('div');
    panelHeader.style.cssText = `align-self:center; font-weight:bold; font-size:12px; color:#fff; pointer-events:none; ${HUD_OUTLINE}`;
    const rowEls = STAT_KEYS.map((key, i) => {
        const color = STAT_TABLE[key].color;
        // dark rounded pill: a colour fill grows with the stat's level behind a
        // stat-colour Lucide icon + bold outlined label; a [N] keytag and a
        // colour-matched + button at the right. collapsed, it's just icon + level.
        const pill = document.createElement('div');
        pill.style.cssText = 'position:relative; display:flex; align-items:center; height:28px; border-radius:14px; background:#383838; overflow:hidden; padding-right:3px;';
        const fill = document.createElement('div');
        fill.style.cssText = `position:absolute; left:0; top:0; bottom:0; width:0%; background:${color}; opacity:0.55;`;
        const icon = document.createElement('span');
        icon.innerHTML = statIconSvg(key);
        icon.style.cssText = `position:relative; flex:none; display:flex; color:${color}; pointer-events:none; filter:drop-shadow(0 1px 1px rgba(0,0,0,0.85));`;
        const name = document.createElement('span');
        name.textContent = STAT_TABLE[key].label;
        name.style.cssText = `position:relative; flex:1; text-align:center; padding-left:12px; font-weight:bold; font-size:13px; color:#fff; white-space:nowrap; pointer-events:none; ${HUD_OUTLINE}`;
        const keyTag = document.createElement('span');
        keyTag.textContent = `[${i + 1}]`;
        keyTag.style.cssText = `position:relative; margin:0 6px; font-size:11px; color:#fff; pointer-events:none; ${HUD_OUTLINE}`;
        const btn = document.createElement('button');
        btn.textContent = '+';
        btn.style.cssText = `position:relative; flex:none; width:30px; height:22px; border:none; border-radius:8px; background:${color}; color:#1c1c1c; font-weight:bold; font-size:17px; line-height:1; padding:0; cursor:pointer; pointer-events:auto;`;
        btn.onclick = () => send(ctx, UpgradeStat, { stat: i });
        // mobile: the whole chip is the tap target (big + thumb-friendly). server
        // rejects the upgrade when there are no points, so an idle tap is harmless;
        // we still gate interactivity via pointer-events in the update below.
        if (mobile) pill.onclick = () => send(ctx, UpgradeStat, { stat: i });
        // read-only counterpart shown in the same right-hand slot when there's no
        // point to spend here: the stat's current level (or MAX at the cap).
        const num = document.createElement('span');
        num.style.cssText = `position:relative; flex:none; width:30px; text-align:center; font-size:12px; font-weight:bold; color:#fff; pointer-events:none; ${HUD_OUTLINE}`;
        pill.append(fill, icon, name, keyTag, btn, num);
        panel.append(pill);
        return { pill, fill, icon, name, keyTag, btn, num };
    });
    // header sits below the rows: showing/hiding it grows the panel downward
    // (the panel is top-anchored) instead of shifting the stat rows.
    panel.append(panelHeader);

    // number keys 1..N → upgrade the matching stat.
    const onKey = (e: KeyboardEvent) => {
        const n = parseInt(e.key, 10);
        if (n >= 1 && n <= STAT_KEYS.length) send(ctx, UpgradeStat, { stat: n - 1 });
    };

    onInit(ctx, () => {
        viewport.append(bottom, board, panel, clock);
        window.addEventListener('keydown', onKey);
    });
    onDispose(ctx, () => {
        bottom.remove();
        clock.remove();
        board.remove();
        panel.remove();
        window.removeEventListener('keydown', onKey);
    });

    let healthSig = ''; // each section only touches the DOM when its values change
    let boardSig = '';
    let panelSig = '';
    let xpSig = '';
    let clockSig = '';
    onFrame(ctx, () => {
        // round countdown — derived locally from the absolute end time the server sent
        // on join, so it's smooth with zero ongoing traffic. mm:ss, reddening near the
        // change; full duration until RoundInfo arrives (roundEndsAt 0).
        const remaining = roundEndsAt > 0 ? Math.max(0, Math.ceil(roundEndsAt - ctx.clock.server)) : ROUND_DURATION;
        if (`${remaining}` !== clockSig) {
            clockSig = `${remaining}`;
            clock.textContent = `${Math.floor(remaining / 60)}:${String(remaining % 60).padStart(2, '0')}`;
            clock.style.color = remaining <= COUNTDOWN_FROM ? '#e8324a' : '#fff';
        }

        // local player's wizard drives the health bar + upgrade panel.
        const controlNode = getControlNode(ctx);
        const wiz = controlNode && getTrait(controlNode, WizardTrait);

        // health bar — current vs the derived max.
        const max = wiz ? maxHealthOf(wiz.stats.levels) : 0;
        const hSig = wiz ? `${wiz.current}/${max}` : '';
        if (hSig !== healthSig) {
            healthSig = hSig;
            if (!wiz) {
                bottom.style.display = 'none';
            } else {
                bottom.style.display = 'flex'; // restore flex (not '', which reverts to block)
                const pct = max > 0 ? Math.max(0, Math.min(1, wiz.current / max)) : 0;
                healthBar.fill.style.width = `${pct * 100}%`;
                healthBar.label.textContent = `${Math.ceil(wiz.current)} / ${max}`;
            }
        }

        // xp bar — progress through the current level.
        const xSig = wiz ? `${wiz.xp}` : '';
        if (xSig !== xpSig) {
            xpSig = xSig;
            if (wiz) {
                const lvl = levelForXp(wiz.xp);
                const cur = xpForLevel(lvl);
                const next = xpForLevel(lvl + 1);
                const prog = next > cur ? (wiz.xp - cur) / (next - cur) : 0;
                xpBar.fill.style.width = `${Math.max(0, Math.min(1, prog)) * 100}%`;
                xpBar.label.textContent = `LVL ${lvl}  ·  ${next - wiz.xp} EXP to next level`;
            }
        }

        // upgrade panel — hidden until the first level is earned (nothing to spend,
        // nothing spent yet). the vertical layout is constant (row heights + gaps
        // never change, so rows never move); only the horizontal extent collapses.
        // with no points it's a narrow rail — each row just its stat colour + level
        // number; when points are up it expands rightward to the full-width pills
        // with labels, + buttons, and [N] keytags, plus the "N to spend" footer.
        const lvls = wiz ? wiz.stats.levels : null;
        const pSig = wiz && lvls ? `${levelForXp(wiz.xp)}:${availablePoints(wiz.xp, lvls)}:${STAT_KEYS.map((k) => lvls[k]).join('')}` : '';
        if (pSig !== panelSig) {
            panelSig = pSig;
            const pts = wiz && lvls ? availablePoints(wiz.xp, lvls) : 0;
            const spent = lvls ? sumLevels(lvls) : 0;
            if (!wiz || !lvls || (pts === 0 && spent === 0)) {
                panel.style.display = 'none';
            } else if (mobile) {
                // mobile: a compact 2-column grid of stat chips (icon + level). with a
                // point available, the whole chip is a big tap target that upgrades that
                // stat (outlined in the stat colour); otherwise it's read-only.
                panel.style.display = 'grid';
                panel.style.gridTemplateColumns = 'repeat(2, 90px)';
                panel.style.gap = '4px';
                panel.style.width = 'auto';
                panelHeader.style.display = pts > 0 ? 'block' : 'none';
                panelHeader.style.gridColumn = '1 / -1';
                panelHeader.textContent = pts > 0 ? `${pts} point${pts === 1 ? '' : 's'} to spend` : '';
                STAT_KEYS.forEach((k, i) => {
                    const statMax = STAT_TABLE[k].max;
                    const row = rowEls[i]!;
                    const lvl = lvls![k];
                    const canUp = pts > 0 && lvl < statMax;
                    row.fill.style.width = `${(lvl / statMax) * 100}%`;
                    row.pill.style.height = '34px';
                    row.pill.style.justifyContent = 'center';
                    row.pill.style.paddingRight = '0';
                    row.pill.style.cursor = canUp ? 'pointer' : 'default';
                    row.pill.style.pointerEvents = canUp ? 'auto' : 'none';
                    row.pill.style.outline = canUp ? `2px solid ${STAT_TABLE[k].color}` : '';
                    row.pill.style.outlineOffset = '-2px';
                    row.icon.style.marginLeft = '0';
                    row.icon.style.marginRight = '5px';
                    row.name.style.display = 'none';
                    row.keyTag.style.display = 'none';
                    row.btn.style.display = 'none';
                    row.num.style.display = '';
                    row.num.style.flex = 'none';
                    row.num.style.width = 'auto';
                    row.num.textContent = lvl >= statMax ? 'MAX' : `${lvl}`;
                });
            } else {
                const expanded = pts > 0;
                panel.style.display = 'flex'; // restore flex (not '', which reverts to block)
                panel.style.width = expanded ? '240px' : '44px';
                panelHeader.style.display = expanded ? 'block' : 'none';
                panelHeader.textContent = expanded ? `${pts} point${pts === 1 ? '' : 's'} to spend` : '';
                STAT_KEYS.forEach((k, i) => {
                    const statMax = STAT_TABLE[k].max;
                    const row = rowEls[i]!;
                    const lvl = lvls![k];
                    row.fill.style.width = `${(lvl / statMax) * 100}%`;
                    const canUp = expanded && lvl < statMax;
                    // collapsed: icon + level number centred on the narrow rail.
                    // expanded: icon hugs the left, label + controls fill out the pill.
                    row.pill.style.justifyContent = expanded ? '' : 'center';
                    row.icon.style.marginLeft = expanded ? '10px' : '0';
                    row.icon.style.marginRight = expanded ? '0' : '3px';
                    row.name.style.display = expanded ? '' : 'none';
                    row.keyTag.style.display = canUp ? '' : 'none';
                    row.btn.style.display = canUp ? '' : 'none';
                    row.btn.disabled = !canUp;
                    // level number: a right-hand badge in the wide layout (maxed/idle
                    // rows), beside the icon as the read-out on the collapsed rail.
                    row.num.style.display = canUp ? 'none' : '';
                    row.num.style.flex = 'none';
                    row.num.style.width = expanded ? '30px' : 'auto';
                    row.num.textContent = `${lvl}`;
                    row.pill.style.paddingRight = expanded ? '3px' : '0';
                });
            }
        }

        // leaderboard — every combatant, sorted by kills then fewest deaths.
        const rows = wizards.matches.map(([w]) => w).sort((a, b) => b.kills - a.kills || a.deaths - b.deaths);
        const bSig = rows.map((w) => `${w.name}:${w.kills}/${w.deaths}`).join(',');
        if (bSig !== boardSig) {
            boardSig = bSig;
            boardGrid.replaceChildren(
                cell('', 'font-weight:bold;'), // name column header (blank)
                cell('K', 'font-weight:bold; text-align:center; color:#9be88a;'),
                cell('D', 'font-weight:bold; text-align:center; color:#e88a8a;'),
                ...rows.flatMap((w) => [
                    cell(w.name || '…', `white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:${mobile ? 80 : 130}px;`),
                    cell(`${w.kills}`, 'text-align:center;'),
                    cell(`${w.deaths}`, 'text-align:center;'),
                ]),
            );
        }
    });
});

// ── client: death camera ────────────────────────────────────────────
// on death the server removes our PlayerControllerTrait — that frees the camera,
// stops input, and (since the viewmodel keys off PC) hides the first-person
// staff. this takes over while PC is gone: zero any in-flight movement so the
// body doesn't glide, and orbit the camera around the death spot. respawn re-adds
// PC, handing control straight back.

const _deathLookMat = mat4.create();
const _deathCamQuat = quat.create();

script(WorldTrait, 'death-cam', (ctx) => {
    if (!env.client) return;

    const ORBIT_SPEED = 0.6; // rad/s around the death spot
    const ORBIT_RADIUS = 4; // m out
    const ORBIT_HEIGHT = 2.5; // m up
    const LOOK_HEIGHT = 1; // m above the spot to aim at
    let angle = 0;
    let relockTries = 0; // re-grab attempts after death frees the pointer lock

    onFrame(ctx, ({ delta }) => {
        const node = getControlNode(ctx);
        if (!node || getTrait(node, PlayerControllerTrait)) {
            relockTries = 3; // alive: re-arm the re-grab for the next death
            return; // alive → PC drives
        }

        // the PlayerController releases pointer lock when it's removed on death.
        // re-grab it (a few tries to cover the async unlock) so look-control hands
        // back seamlessly when the PC returns on respawn — no re-click needed.
        if (relockTries > 0 && !document.pointerLockElement) {
            relockTries--;
            ctx.client?.domElement?.requestPointerLock?.();
        }

        // PC is gone, so nothing else writes the controller input — stop the body.
        const cc = getTrait(node, CharacterControllerTrait);
        if (cc) {
            cc.input.move[0] = 0;
            cc.input.move[1] = 0;
            cc.input.jump = false;
        }

        // orbit the (free) camera node around the death spot.
        const center = getWorldPosition(getTrait(node, TransformTrait)!);
        angle += delta * ORBIT_SPEED;
        const camPos: Vec3 = [
            center[0] + Math.cos(angle) * ORBIT_RADIUS,
            center[1] + ORBIT_HEIGHT,
            center[2] + Math.sin(angle) * ORBIT_RADIUS,
        ];
        const camTransform = getTrait(resolveCamera(ctx).node, TransformTrait)!;
        setWorldPosition(camTransform, camPos);
        mat4.targetTo(_deathLookMat, camPos, [center[0], center[1] + LOOK_HEIGHT, center[2]], [0, 1, 0]);
        quat.fromMat4(_deathCamQuat, _deathLookMat);
        setWorldQuaternion(camTransform, _deathCamQuat);
    });
});

// nav.ts — reachability helpers built on the engine's voxel nav.
//
// flood-fill is the dual of pathfinding: instead of "is there a path from A to
// B" it answers "which cells can I reach from A". built on the SAME movement
// models as voxelNav.findPath, so any cell a flood-fill returns is guaranteed
// path-reachable — handy for picking a provably-reachable target (e.g. npc
// wander) without a path query that can fail.
//
// ground/air mirror findGroundPath-over-landWalkable: "ground"/"air" convenience
// names over the engine's "land"/"fly" movement primitives.

import { voxelNav, type Voxels } from 'bongle';
import type { Vec3 } from 'mathcat';

// generic BFS over a movement model's `actions` — the cells reachable from
// `start`, capped at `maxCells` (the iteration bound; flood-fill is otherwise
// unbounded). includes `start`; order is roughly nearest-first.
export function floodFill(voxels: Voxels, start: Vec3, actions: voxelNav.Actions, maxCells: number): Vec3[] {
    const queue: Vec3[] = [start];
    const seen = new Set<string>([`${start[0]},${start[1]},${start[2]}`]);
    let head = 0;
    while (head < queue.length && queue.length < maxCells) {
        const c = queue[head++]!;
        for (const step of actions(voxels, c[0], c[1], c[2])) {
            const k = `${step.x},${step.y},${step.z}`;
            if (seen.has(k)) continue;
            seen.add(k);
            queue.push([step.x, step.y, step.z]);
        }
    }
    return queue;
}

// land movement (walks the ground, steps ±1) — the model findGroundPath uses.
const landActions = voxelNav.landMovement().actions;

// fly movement: 6-connected (±x, ±y, ±z), clearance-only walkability (no ground
// support). the engine ships flyWalkable but no flyMovement helper, so we
// assemble the model the same way landMovement does.
const FLY_MOVES: { offset: Vec3; cost: number }[] = [
    { offset: [1, 0, 0], cost: 1 },
    { offset: [-1, 0, 0], cost: 1 },
    { offset: [0, 1, 0], cost: 1 },
    { offset: [0, -1, 0], cost: 1 },
    { offset: [0, 0, 1], cost: 1 },
    { offset: [0, 0, -1], cost: 1 },
];
const flyActions = voxelNav.gridActions(FLY_MOVES, voxelNav.flyWalkable());

// cells reachable on foot from `start` (walks the terrain). pairs with findGroundPath.
export function floodFillGround(voxels: Voxels, start: Vec3, maxCells: number): Vec3[] {
    return floodFill(voxels, start, landActions, maxCells);
}

// cells reachable in free flight from `start` (any clear body box). pairs with a
// fly-model findPath.
export function floodFillAir(voxels: Voxels, start: Vec3, maxCells: number): Vec3[] {
    return floodFill(voxels, start, flyActions, maxCells);
}

#!/usr/bin/env python3
"""Mine degree vectors from triangulations of random point sets."""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
import time
from collections import Counter

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.crossing_graph import crossing_graph
from planegraphs.geometry import general_position, orient
from planegraphs.search import hull_size
from planegraphs.triangulations import (
    enumerate_triangulations,
    get_degrees,
    random_triangulation_from_graph,
)


def _point_in_triangle(p: tuple[int, int], a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> bool:
    o1 = orient(a, b, p)
    o2 = orient(b, c, p)
    o3 = orient(c, a, p)
    if o1 == 0 or o2 == 0 or o3 == 0:
        return False
    return (o1 > 0 and o2 > 0 and o3 > 0) or (o1 < 0 and o2 < 0 and o3 < 0)


def _collinear_with_any_pair(candidate: tuple[int, int], points: list[tuple[int, int]]) -> bool:
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            if orient(points[i], points[j], candidate) == 0:
                return True
    return False


def _random_point_set(
    n: int,
    rng: random.Random,
    radius: int,
    max_attempts: int = 200,
    max_inner: int = 2000,
) -> list[tuple[int, int]]:
    """Sample a hull-3 point set by construction with bounded retries."""
    for _ in range(max_attempts):
        hull = []
        while len(hull) < 3:
            candidate = (rng.randint(-radius, radius), rng.randint(-radius, radius))
            if candidate not in hull:
                hull.append(candidate)
        if orient(hull[0], hull[1], hull[2]) == 0:
            continue
        a, b, c = hull
        minx = min(a[0], b[0], c[0])
        maxx = max(a[0], b[0], c[0])
        miny = min(a[1], b[1], c[1])
        maxy = max(a[1], b[1], c[1])
        interior = [
            (x, y)
            for x in range(minx, maxx + 1)
            for y in range(miny, maxy + 1)
            if (x, y) not in hull and _point_in_triangle((x, y), a, b, c)
        ]
        if len(interior) < n - 3:
            continue
        points = list(hull)
        attempts = 0
        while len(points) < n and attempts < max_inner:
            attempts += 1
            candidate = rng.choice(interior)
            if candidate in points:
                continue
            if _collinear_with_any_pair(candidate, points):
                continue
            points.append(candidate)
        if len(points) == n:
            return points
    raise RuntimeError("failed to sample hull-3 point set")


def vector_signature(degrees: list[int]) -> tuple[int, int, int, int, int]:
    """Return (v3, v4, v5, v6, vlarge) from a degree list."""
    counts = Counter(degrees)
    v3 = counts.get(3, 0)
    v4 = counts.get(4, 0)
    v5 = counts.get(5, 0)
    v6 = counts.get(6, 0)
    vlarge = sum(count for degree, count in counts.items() if degree >= 7)
    return (v3, v4, v5, v6, vlarge)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="data/degree_vectors.json")
    parser.add_argument("--n-min", type=int, default=6)
    parser.add_argument("--n-max", type=int, default=9)
    parser.add_argument("--samples", type=int, default=50)
    parser.add_argument("--radius", type=int, default=100)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--max-triangulations", type=int)
    parser.add_argument("--random-triangulations", type=int, default=0)
    parser.add_argument("--append", action="store_true")
    parser.add_argument("--max-time", type=float)
    args = parser.parse_args()

    if args.n_min < 4:
        raise SystemExit("--n-min must be >= 4 for triangulations")
    if args.n_max < args.n_min:
        raise SystemExit("--n-max must be >= --n-min")
    if args.samples < 1:
        raise SystemExit("--samples must be >= 1")

    rng = random.Random(args.seed)
    unique_vectors: set[tuple[int, int, int, int, int]] = set()
    print(
        f"Mining vectors for n={args.n_min}..{args.n_max} "
        f"(samples={args.samples})..."
    )

    start = time.perf_counter()
    for n in range(args.n_min, args.n_max + 1):
        for _ in range(args.samples):
            if args.max_time is not None and time.perf_counter() - start > args.max_time:
                print("Reached --max-time; stopping early.")
                break
            try:
                points = _random_point_set(n, rng, args.radius)
            except RuntimeError:
                print("failed to sample point set; skipping")
                continue
            if args.random_triangulations > 0:
                segments, adj = crossing_graph(points)
                for _ in range(args.random_triangulations):
                    edges = random_triangulation_from_graph(segments, adj, rng)
                    degrees = get_degrees(points, edges)
                    sig = vector_signature(degrees)
                    if sum(sig) != n:
                        continue
                    unique_vectors.add(sig)
            else:
                triangulations = enumerate_triangulations(points, max_count=args.max_triangulations)
                for edges in triangulations:
                    degrees = get_degrees(points, edges)
                    sig = vector_signature(degrees)
                    if sum(sig) != n:
                        continue
                    unique_vectors.add(sig)
        if args.max_time is not None and time.perf_counter() - start > args.max_time:
            break

    print(f"Found {len(unique_vectors)} unique degree vectors.")
    if args.append and os.path.exists(args.out):
        with open(args.out, "r", encoding="utf-8") as handle:
            existing = json.load(handle)
        if isinstance(existing, list):
            for row in existing:
                unique_vectors.add(tuple(int(x) for x in row))
        else:
            raise SystemExit("existing data is not a vector list")

    data = sorted(list(unique_vectors))

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2)
    print(f"Saved to {args.out}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Mine degree vectors from triangulations of random point sets."""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
from collections import Counter

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.geometry import general_position
from planegraphs.search import hull_size
from planegraphs.triangulations import enumerate_triangulations, get_degrees


def _random_point_set(n: int, rng: random.Random, radius: int) -> list[tuple[int, int]]:
    while True:
        points: list[tuple[int, int]] = []
        while len(points) < n:
            candidate = (rng.randint(-radius, radius), rng.randint(-radius, radius))
            if candidate not in points:
                points.append(candidate)
        if general_position(points) and hull_size(points) == 3:
            return points


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

    for n in range(args.n_min, args.n_max + 1):
        for _ in range(args.samples):
            points = _random_point_set(n, rng, args.radius)
            triangulations = enumerate_triangulations(points, max_count=args.max_triangulations)
            for edges in triangulations:
                degrees = get_degrees(points, edges)
                sig = vector_signature(degrees)
                if sum(sig) != n:
                    continue
                unique_vectors.add(sig)

    print(f"Found {len(unique_vectors)} unique degree vectors.")
    data = sorted(list(unique_vectors))

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2)
    print(f"Saved to {args.out}")


if __name__ == "__main__":
    main()

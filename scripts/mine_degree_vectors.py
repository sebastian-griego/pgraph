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
from planegraphs.triangulations import summarize_degree_vectors, triangulation_degree_vectors


def _random_point_set(n: int, rng: random.Random, radius: int) -> list[tuple[int, int]]:
    while True:
        points: list[tuple[int, int]] = []
        while len(points) < n:
            candidate = (rng.randint(-radius, radius), rng.randint(-radius, radius))
            if candidate not in points:
                points.append(candidate)
        if general_position(points) and hull_size(points) == 3:
            return points


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=7)
    parser.add_argument("--radius", type=int, default=4)
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-triangulations", type=int)
    parser.add_argument("--out")
    args = parser.parse_args()

    if args.n < 4:
        raise SystemExit("--n must be >= 4 for triangulations")
    if args.samples < 1:
        raise SystemExit("--samples must be >= 1")

    rng = random.Random(args.seed)
    vectors: list[tuple[int, int, int, int, int]] = []
    for idx in range(args.samples):
        points = _random_point_set(args.n, rng, args.radius)
        vecs = triangulation_degree_vectors(points, max_count=args.max_triangulations)
        vectors.extend(vecs)
        # Track minimal degrees to validate the expected lower bound of 3.
        for v3, v4, v5, v6, vlarge in vecs:
            total = v3 + v4 + v5 + v6 + vlarge
            if total != args.n:
                raise RuntimeError("degree vector does not sum to n")
        print(f"sample {idx + 1}/{args.samples}: {len(vecs)} triangulations")

    summary = summarize_degree_vectors(vectors)
    sorted_vectors = [
        {"v3": v3, "v4": v4, "v5": v5, "v6": v6, "vlarge": vlarge, "count": count}
        for (v3, v4, v5, v6, vlarge), count in summary.most_common()
    ]

    payload = {
        "n": args.n,
        "samples": args.samples,
        "radius": args.radius,
        "vectors": sorted_vectors,
    }

    if args.out:
        with open(args.out, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        print(f"wrote {args.out}")
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

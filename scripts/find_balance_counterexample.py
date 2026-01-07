#!/usr/bin/env python3
"""Search for triangulations that violate deg56 balance inequalities."""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
from collections import Counter
from typing import Iterable

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.crossing_graph import crossing_graph
from planegraphs.search import _random_point_set
from planegraphs.triangulations import get_degrees, random_triangulation_from_graph


def degree_counts(degrees: Iterable[int]) -> tuple[int, int, int, int, int]:
    counts = Counter(degrees)
    v3 = counts.get(3, 0)
    v4 = counts.get(4, 0)
    v5 = counts.get(5, 0)
    v6 = counts.get(6, 0)
    vlarge = sum(count for degree, count in counts.items() if degree >= 7)
    return v3, v4, v5, v6, vlarge


def sum_large(degrees: Iterable[int]) -> int:
    return sum(d for d in degrees if d >= 7)


def linear_lhs(v3: int, v4: int, v5: int, v6: int) -> int:
    return 45 * v3 + 21 * v4 + 9 * v5 + 3 * v6


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-min", type=int, default=6)
    parser.add_argument("--n-max", type=int, default=12)
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--triangulations", type=int, default=200)
    parser.add_argument("--radius", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--shift", action="store_true")
    parser.add_argument("--check-sumlarge", action="store_true")
    parser.add_argument("--out")
    args = parser.parse_args()

    rng = random.Random(args.seed)
    threshold = 23 if args.shift else 25

    for n in range(args.n_min, args.n_max + 1):
        for _ in range(args.samples):
            points = _random_point_set(n, rng, args.radius)
            segments, adj = crossing_graph(points)
            for _ in range(args.triangulations):
                edges = random_triangulation_from_graph(segments, adj, rng)
                degrees = get_degrees(points, edges)
                v3, v4, v5, v6, vL = degree_counts(degrees)
                lhs = linear_lhs(v3, v4, v5, v6)
                rhs = threshold * n
                if lhs <= rhs:
                    continue
                payload = {
                    "n": n,
                    "shift": args.shift,
                    "points": points,
                    "edges": edges,
                    "degrees": degrees,
                    "counts": {"v3": v3, "v4": v4, "v5": v5, "v6": v6, "vL": vL},
                    "linear": {"lhs": lhs, "rhs": rhs},
                }
                if args.check_sumlarge:
                    payload["sumLarge"] = sum_large(degrees)
                if args.out:
                    with open(args.out, "w", encoding="utf-8") as handle:
                        json.dump(payload, handle, indent=2)
                else:
                    print(json.dumps(payload, indent=2))
                return
    print("no counterexample found")


if __name__ == "__main__":
    main()

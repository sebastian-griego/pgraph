#!/usr/bin/env python3
from fractions import Fraction
import itertools
import argparse
import os
import sys

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.geometry import general_position
from planegraphs.search import hull_size
from planegraphs.stats import pg


def parse_fraction(text: str) -> Fraction:
    if "/" in text:
        num_str, den_str = text.split("/", 1)
        return Fraction(int(num_str.strip()), int(den_str.strip()))
    return Fraction(int(text.strip()), 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", default="243/20")
    parser.add_argument("--min-n", type=int, default=3)
    parser.add_argument("--max-n", type=int, default=6)
    parser.add_argument("--max-hull", type=int, default=3)
    parser.add_argument("--radius", type=int, default=1)
    args = parser.parse_args()

    bound = parse_fraction(args.bound)

    grid = [
        (x, y)
        for x in range(-args.radius, args.radius + 1)
        for y in range(-args.radius, args.radius + 1)
    ]

    for n in range(args.min_n, args.max_n + 1):
        for pts in itertools.combinations(grid, n):
            pts_list = list(pts)
            if not general_position(pts_list):
                continue
            if hull_size(pts_list) > args.max_hull:
                continue
            value = pg(pts_list)
            if value < bound ** n:
                print("counterexample:")
                print(f"  n={n}")
                print(f"  points={pts_list}")
                print(f"  hull_size={hull_size(pts_list)}")
                print(f"  pg={value}")
                print(f"  bound={bound}^{n}={bound ** n}")
                return

    print("no counterexample found in grid search")


if __name__ == "__main__":
    main()

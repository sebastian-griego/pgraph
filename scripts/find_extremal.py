#!/usr/bin/env python3
"""Search for extremal point sets with hull size 3."""

from __future__ import annotations

import argparse
import os
import sys
from decimal import Decimal, getcontext

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.search import search


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("-n", type=int, default=8)
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--radius", type=int, default=8)
    parser.add_argument("--top", type=int, default=5)
    parser.add_argument("--precision", type=int, default=40)
    args = parser.parse_args()

    getcontext().prec = args.precision
    results = search(args.n, steps=args.steps, seed=args.seed, radius=args.radius, keep=args.top)
    print(f"searched n={args.n}, steps={args.steps}, seed={args.seed}")

    for idx, cand in enumerate(results, start=1):
        root = Decimal(cand.pg) ** (Decimal(1) / Decimal(args.n))
        print(f"#{idx}")
        print(f"points={list(cand.points)}")
        print(f"pg={cand.pg}")
        print(f"E[I]={cand.expected_isolated}")
        print(f"K_est={cand.k_est}")
        print(f"pg^(1/n)={root}")


if __name__ == "__main__":
    main()

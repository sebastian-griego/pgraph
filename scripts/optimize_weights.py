#!/usr/bin/env python3
"""Optimize charging weights from sampled degree vectors."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from typing import Iterable

try:
    from scipy.optimize import linprog
except ImportError as exc:
    raise SystemExit("scipy is required for this script") from exc


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _rationalize(value: float, max_den: int) -> Fraction:
    return Fraction(value).limit_denominator(max_den)


def _load_vectors(path: str) -> tuple[int, list[tuple[int, int, int, int, int]]]:
    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    n = int(data["n"])
    vectors = []
    for row in data["vectors"]:
        vectors.append(
            (
                int(row["v3"]),
                int(row["v4"]),
                int(row["v5"]),
                int(row["v6"]),
                int(row["vlarge"]),
            )
        )
    return n, vectors


def _add_constraint(A: list[list[float]], b: list[float], row: Iterable[float], rhs: float) -> None:
    A.append(list(row))
    b.append(rhs)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--vectors", required=True)
    parser.add_argument("--w3-max", type=float, default=1 / 8)
    parser.add_argument("--w4-max", type=float, default=1 / 16)
    parser.add_argument("--w5-max", type=float, default=1 / 32)
    parser.add_argument("--w6-max", type=float, default=1 / 64)
    parser.add_argument("--wlarge-max", type=float, default=1 / 128)
    parser.add_argument("--monotone", action="store_true")
    parser.add_argument("--no-shift", action="store_true")
    parser.add_argument("--max-den", type=int, default=512)
    args = parser.parse_args()

    n, vectors = _load_vectors(args.vectors)
    if not vectors:
        raise SystemExit("no vectors found in input")

    # Variables: w3, w4, w5, w6, wlarge, a, b (if shift enabled).
    use_shift = not args.no_shift
    if use_shift:
        num_vars = 7
    else:
        num_vars = 6

    A_ub: list[list[float]] = []
    b_ub: list[float] = []

    for v3, v4, v5, v6, vlarge in vectors:
        if use_shift:
            row = [v3, v4, v5, v6, vlarge, -n, -1]
        else:
            row = [v3, v4, v5, v6, vlarge, -n]
        _add_constraint(A_ub, b_ub, row, 0.0)

    if args.monotone:
        # w4 - w3 <= 0
        _add_constraint(A_ub, b_ub, [-1, 1, 0, 0, 0] + ([0, 0] if use_shift else [0]), 0.0)
        # w5 - w4 <= 0
        _add_constraint(A_ub, b_ub, [0, -1, 1, 0, 0] + ([0, 0] if use_shift else [0]), 0.0)
        # w6 - w5 <= 0
        _add_constraint(A_ub, b_ub, [0, 0, -1, 1, 0] + ([0, 0] if use_shift else [0]), 0.0)
        # wlarge - w6 <= 0
        _add_constraint(A_ub, b_ub, [0, 0, 0, -1, 1] + ([0, 0] if use_shift else [0]), 0.0)

    bounds = [
        (0.0, args.w3_max),
        (0.0, args.w4_max),
        (0.0, args.w5_max),
        (0.0, args.w6_max),
        (0.0, args.wlarge_max),
        (0.0, None),  # a
    ]
    if use_shift:
        bounds.append((-float(n), 0.0))  # b <= 0

    # Objective: minimize a (last or second-to-last variable).
    c = [0.0] * num_vars
    c[5] = 1.0

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success:
        raise SystemExit(f"optimization failed: {res.message}")

    w3, w4, w5, w6, wlarge, a = res.x[:6]
    b = res.x[6] if use_shift else 0.0
    if a <= 0:
        raise SystemExit("optimization returned non-positive a")

    k_value = 1.0 / a
    print("optimization=success")
    print(f"n={n}")
    print(f"a={a:.8f} b={b:.8f} K={k_value:.8f}")
    print(f"w3={w3:.8f} w4={w4:.8f} w5={w5:.8f} w6={w6:.8f} wlarge={wlarge:.8f}")

    k_rat = _rationalize(k_value, args.max_den)
    a_rat = _rationalize(a, args.max_den)
    b_rat = _rationalize(b, args.max_den) if use_shift else Fraction(0, 1)
    print("rationalized:")
    print(f"  K={_format_fraction(k_rat)}")
    print(f"  a={_format_fraction(a_rat)}")
    print(f"  b={_format_fraction(b_rat)}")


if __name__ == "__main__":
    main()

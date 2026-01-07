#!/usr/bin/env python3
"""Solve the weight LP and snap-fit an exact rational certificate."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from typing import Iterable

try:
    from scipy.optimize import linprog
except ImportError as exc:
    raise SystemExit("scipy is required for this script") from exc


def _load_vectors(path: str) -> list[tuple[int, int, int, int, int]]:
    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    if isinstance(data, list):
        return [tuple(int(x) for x in row) for row in data]
    if isinstance(data, dict):
        rows = data.get("vectors", [])
        vectors: list[tuple[int, int, int, int, int]] = []
        for row in rows:
            if isinstance(row, dict):
                vectors.append(
                    (
                        int(row["v3"]),
                        int(row["v4"]),
                        int(row["v5"]),
                        int(row["v6"]),
                        int(row.get("vlarge", row.get("vL", 0))),
                    )
                )
            else:
                vectors.append(tuple(int(x) for x in row))
        return vectors
    raise SystemExit("unsupported vector JSON format")


def _solve_lp(
    vectors: Iterable[tuple[int, int, int, int, int]],
    bounds: list[tuple[float, float | None]],
    monotone: bool,
) -> tuple[list[float], float]:
    c = [0.0, 0.0, 0.0, 0.0, 0.0, 1.0]
    A_ub: list[list[float]] = []
    b_ub: list[float] = []
    for v3, v4, v5, v6, vlarge in vectors:
        n = v3 + v4 + v5 + v6 + vlarge
        A_ub.append([v3, v4, v5, v6, vlarge, -n])
        b_ub.append(0.0)

    if monotone:
        A_ub.append([-1, 1, 0, 0, 0, 0])
        b_ub.append(0.0)
        A_ub.append([0, -1, 1, 0, 0, 0])
        b_ub.append(0.0)
        A_ub.append([0, 0, -1, 1, 0, 0])
        b_ub.append(0.0)
        A_ub.append([0, 0, 0, -1, 1, 0])
        b_ub.append(0.0)

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success:
        raise RuntimeError(f"LP failed: {res.message}")
    return res.x[:5], res.x[5]


def _verify_exact(
    vectors: Iterable[tuple[int, int, int, int, int]],
    weights: Iterable[Fraction],
) -> tuple[Fraction, tuple[int, int, int, int, int]]:
    max_required = Fraction(0)
    worst = None
    for vec in vectors:
        n = sum(vec)
        if n == 0:
            continue
        charge = sum(Fraction(v) * w for v, w in zip(vec, weights))
        required = charge / n
        if required > max_required:
            max_required = required
            worst = vec
    if worst is None:
        raise RuntimeError("no vectors to verify")
    if max_required == 0:
        raise RuntimeError("zero charge bound; check weight normalization")
    return max_required, worst


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", default="data/degree_vectors.json")
    parser.add_argument("--w3-max", type=float, default=1 / 8)
    parser.add_argument("--w4-max", type=float, default=1 / 16)
    parser.add_argument("--w5-max", type=float, default=1 / 32)
    parser.add_argument("--w6-max", type=float, default=1 / 64)
    parser.add_argument("--wlarge-max", type=float, default=1 / 128)
    parser.add_argument("--monotone", action="store_true")
    parser.add_argument("--free-weights", action="store_true")
    parser.add_argument("--out")
    parser.add_argument("--k-name", default="K_deg56")
    parser.add_argument("--min-n", type=int)
    parser.add_argument("--max-n", type=int)
    parser.add_argument("--max-den", type=int, default=1000)
    args = parser.parse_args()

    vectors = _load_vectors(args.data)
    if not vectors:
        raise SystemExit("no vectors found in input")
    if args.min_n is not None or args.max_n is not None:
        filtered = []
        for vec in vectors:
            n = sum(vec)
            if args.min_n is not None and n < args.min_n:
                continue
            if args.max_n is not None and n > args.max_n:
                continue
            filtered.append(vec)
        vectors = filtered
        if not vectors:
            raise SystemExit("no vectors left after filtering by n")
    print(f"Loaded {len(vectors)} vectors.")

    if args.free_weights:
        weight_bounds = [
            (0.0, args.w3_max),
            (0.0, args.w4_max),
            (0.0, args.w5_max),
            (0.0, args.w6_max),
            (0.0, args.wlarge_max),
        ]
    else:
        weight_bounds = [
            (args.w3_max, args.w3_max),
            (args.w4_max, args.w4_max),
            (args.w5_max, args.w5_max),
            (args.w6_max, args.w6_max),
            (args.wlarge_max, args.wlarge_max),
        ]

    bounds = weight_bounds + [(1e-6, 1.0)]

    weights_f, z_float = _solve_lp(vectors, bounds, args.monotone)
    weights = [Fraction(w).limit_denominator(args.max_den) for w in weights_f]
    if all(w == 0 for w in weights):
        raise SystemExit(
            "all weights snapped to 0; use fixed weights or raise max-den"
        )

    for w, limit in zip(
        weights,
        [args.w3_max, args.w4_max, args.w5_max, args.w6_max, args.wlarge_max],
    ):
        if w > Fraction(limit):
            raise SystemExit("rationalized weights exceed the specified bounds")

    z_required, worst_vec = _verify_exact(vectors, weights)
    k_exact = Fraction(1, 1) / z_required

    print("Exact certificate:")
    print("weights=" + ("free" if args.free_weights else "fixed"))
    print(f"  {args.k_name}={_format_fraction(k_exact)}")
    labels = ["w3", "w4", "w5", "w6", "wL"]
    for label, weight in zip(labels, weights):
        print(f"  {label}={_format_fraction(weight)}")
    print(f"Worst-case vector: {worst_vec}")

    if args.out:
        payload = {
            "constants": {
                args.k_name: [k_exact.numerator, k_exact.denominator],
                "w3": [weights[0].numerator, weights[0].denominator],
                "w4": [weights[1].numerator, weights[1].denominator],
                "w5": [weights[2].numerator, weights[2].denominator],
                "w6": [weights[3].numerator, weights[3].denominator],
                "wL": [weights[4].numerator, weights[4].denominator],
            }
        }
        with open(args.out, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        print(f"Wrote certificate to {args.out}")
    else:
        print("\nRun this command to generate your certificate:")
        print("python scripts/export_certificate.py --out certificates/deg56.json \\")
        print(f"  --const {args.k_name}={_format_fraction(k_exact)} \\")
        for label, weight in zip(labels, weights):
            print(f"  --const {label}={_format_fraction(weight)} \\")
        print("")


if __name__ == "__main__":
    main()

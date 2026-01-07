#!/usr/bin/env python3
"""Search for simple linear inequalities over degree vectors."""

from __future__ import annotations

import argparse
import json
import math
from itertools import product


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


def _format_ineq(coeffs: tuple[int, int, int, int, int], b: int, c: int, direction: str) -> str:
    names = ["v3", "v4", "v5", "v6", "vL"]
    parts = []
    for coeff, name in zip(coeffs, names):
        if coeff == 0:
            continue
        parts.append(f"{coeff}*{name}")
    lhs = " + ".join(parts) if parts else "0"
    rhs = f"{b}*n"
    if c != 0:
        rhs = f"{rhs} + {c}"
    return f"{lhs} {direction} {rhs}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", default="data/degree_vectors.json")
    parser.add_argument("--coeff-min", type=int, default=-3)
    parser.add_argument("--coeff-max", type=int, default=3)
    parser.add_argument("--b-min", type=int, default=-3)
    parser.add_argument("--b-max", type=int, default=3)
    parser.add_argument("--direction", choices=["<=", ">=", "both"], default="<=")
    parser.add_argument("--max-const", type=int, default=0)
    parser.add_argument("--min-const", type=int, default=0)
    parser.add_argument("--coeff-nonneg", action="store_true")
    parser.add_argument("--coeff-nonpos", action="store_true")
    parser.add_argument("--exclude-constant", action="store_true")
    parser.add_argument("--min-n", type=int)
    parser.add_argument("--max-n", type=int)
    parser.add_argument("--target")
    parser.add_argument("--top", type=int, default=20)
    args = parser.parse_args()

    vectors = _load_vectors(args.data)
    if not vectors:
        raise SystemExit("no vectors found")
    if args.min_n is not None or args.max_n is not None:
        vectors = [
            vec
            for vec in vectors
            if (args.min_n is None or sum(vec) >= args.min_n)
            and (args.max_n is None or sum(vec) <= args.max_n)
        ]
        if not vectors:
            raise SystemExit("no vectors after n-range filtering")

    data = [(vec, sum(vec)) for vec in vectors]

    target_vec = None
    if args.target:
        parts = args.target.split(",")
        if len(parts) != 5:
            raise SystemExit("--target expects 5 comma-separated integers")
        target_vec = tuple(int(p.strip()) for p in parts)

    coeff_range = range(args.coeff_min, args.coeff_max + 1)
    b_range = range(args.b_min, args.b_max + 1)

    upper_results: list[tuple[int, tuple[int, int, int, int, int], int]] = []
    lower_results: list[tuple[int, tuple[int, int, int, int, int], int]] = []

    for coeffs in product(coeff_range, repeat=5):
        if all(c == 0 for c in coeffs):
            continue
        if args.coeff_nonneg and any(c < 0 for c in coeffs):
            continue
        if args.coeff_nonpos and any(c > 0 for c in coeffs):
            continue
        if args.exclude_constant and len(set(coeffs)) == 1:
            continue
        for b in b_range:
            values = [sum(c * v for c, v in zip(coeffs, vec)) - b * n for vec, n in data]
            if args.direction in ("<=", "both"):
                c = max(values)
                if c <= args.max_const:
                    if target_vec is not None:
                        t_val = sum(ca * tv for ca, tv in zip(coeffs, target_vec)) - b * sum(target_vec)
                        if t_val <= c:
                            continue
                    upper_results.append((c, coeffs, b))
            if args.direction in (">=", "both"):
                c = min(values)
                if c >= args.min_const:
                    if target_vec is not None:
                        t_val = sum(ca * tv for ca, tv in zip(coeffs, target_vec)) - b * sum(target_vec)
                        if t_val >= c:
                            continue
                    lower_results.append((c, coeffs, b))

    if args.direction in ("<=", "both"):
        upper_results.sort(key=lambda x: (x[0], sum(abs(c) for c in x[1]), abs(x[2])))
        print("Top upper-bound candidates:")
        for c, coeffs, b in upper_results[: args.top]:
            print(f"  c={c}: {_format_ineq(coeffs, b, c, '<=')}")

    if args.direction in (">=", "both"):
        lower_results.sort(key=lambda x: (-x[0], sum(abs(c) for c in x[1]), abs(x[2])))
        print("Top lower-bound candidates:")
        for c, coeffs, b in lower_results[: args.top]:
            print(f"  c={c}: {_format_ineq(coeffs, b, c, '>=')}")


if __name__ == "__main__":
    main()

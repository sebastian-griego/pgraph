#!/usr/bin/env python3
"""Check a sumLarge lower bound against mined degree vectors."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from typing import Iterable


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


def _parse_fraction(text: str) -> Fraction:
    try:
        return Fraction(text)
    except Exception as exc:  # pragma: no cover - argparse guards usage
        raise SystemExit(f"invalid fraction {text!r}") from exc


def _parse_coeffs(text: str) -> list[Fraction]:
    parts = [p.strip() for p in text.split(",")]
    if len(parts) != 5:
        raise SystemExit("--coeffs expects 5 comma-separated numbers")
    return [_parse_fraction(p) for p in parts]


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fraction_payload(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def _sum_large(n: int, v3: int, v4: int, v5: int, v6: int, hull: int) -> int:
    degree_sum = 6 * n - 6 - 2 * hull
    return degree_sum - (3 * v3 + 4 * v4 + 5 * v5 + 6 * v6)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", default="data/degree_vectors_new.json")
    parser.add_argument("--coeffs", required=True, help="v3,v4,v5,v6,vL coefficients")
    parser.add_argument("--const", default="0", help="constant term on RHS")
    parser.add_argument("--hull", type=int, default=3, help="hull size for degree sum")
    parser.add_argument("--min-n", type=int)
    parser.add_argument("--max-n", type=int)
    parser.add_argument("--max-examples", type=int, default=1)
    parser.add_argument("--max-checked", type=int, default=0)
    parser.add_argument("--shuffle", action="store_true")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--stop-after-examples", action="store_true")
    parser.add_argument("--summary-only", action="store_true")
    parser.add_argument("--out", help="write JSON summary to this path")
    args = parser.parse_args()

    coeffs = _parse_coeffs(args.coeffs)
    const = _parse_fraction(args.const)
    vectors = _load_vectors(args.data)
    if not vectors:
        raise SystemExit("no vectors found in input")
    if args.shuffle:
        import random

        rng = random.Random(args.seed)
        rng.shuffle(vectors)

    shown = 0
    total_checked = 0
    total_bad = 0
    worst_margin: Fraction | None = None
    worst_vec: tuple[int, int, int, int, int] | None = None
    worst_n = 0
    worst_sum_large = 0
    worst_rhs = Fraction(0)
    examples: list[dict[str, object]] = []

    for v3, v4, v5, v6, vL in vectors:
        if args.max_checked > 0 and total_checked >= args.max_checked:
            break
        n = v3 + v4 + v5 + v6 + vL
        if args.min_n is not None and n < args.min_n:
            continue
        if args.max_n is not None and n > args.max_n:
            continue
        total_checked += 1
        sum_large = _sum_large(n, v3, v4, v5, v6, args.hull)
        rhs = (
            coeffs[0] * v3
            + coeffs[1] * v4
            + coeffs[2] * v5
            + coeffs[3] * v6
            + coeffs[4] * vL
            + const
        )
        margin = Fraction(sum_large) - rhs
        if worst_margin is None or margin < worst_margin:
            worst_margin = margin
            worst_vec = (v3, v4, v5, v6, vL)
            worst_n = n
            worst_sum_large = sum_large
            worst_rhs = rhs
        if margin < 0:
            total_bad += 1
            if args.max_examples <= 0 or shown < args.max_examples:
                if not args.summary_only:
                    print(
                        "counterexample",
                        f"n={n}",
                        f"vec={(v3, v4, v5, v6, vL)}",
                        f"sumLarge={sum_large}",
                        f"rhs={_format_fraction(rhs)}",
                    )
                shown += 1
            if args.max_examples <= 0 or len(examples) < args.max_examples:
                examples.append(
                    {
                        "n": n,
                        "vec": [v3, v4, v5, v6, vL],
                        "sumLarge": sum_large,
                        "rhs": _fraction_payload(rhs),
                        "margin": _fraction_payload(margin),
                    }
                )
            if args.stop_after_examples and args.max_examples > 0 and shown >= args.max_examples:
                break

    if total_checked == 0:
        raise SystemExit("no vectors after n-range filtering")

    if total_bad == 0:
        print("no counterexample found")
    else:
        print(f"counterexamples_found={total_bad}")
    if worst_margin is not None and worst_vec is not None:
        print(
            f"worst_margin={_format_fraction(worst_margin)} "
            f"at n={worst_n} vec={worst_vec}"
        )
    if args.out:
        payload = {
            "data": args.data,
            "coeffs": [_fraction_payload(c) for c in coeffs],
            "const": _fraction_payload(const),
            "hull": args.hull,
            "min_n": args.min_n,
            "max_n": args.max_n,
            "total_checked": total_checked,
            "total_bad": total_bad,
            "worst": {
                "n": worst_n,
                "vec": list(worst_vec) if worst_vec is not None else None,
                "sumLarge": worst_sum_large,
                "rhs": _fraction_payload(worst_rhs),
                "margin": _fraction_payload(worst_margin) if worst_margin is not None else None,
            },
            "examples": examples,
        }
        with open(args.out, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        print(f"wrote_summary path={args.out}")


if __name__ == "__main__":
    main()

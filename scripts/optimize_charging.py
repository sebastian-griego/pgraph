#!/usr/bin/env python3
"""Solve small charging LPs exactly and report the worst-case bound."""

from __future__ import annotations

import argparse
import json
import os
import sys
from fractions import Fraction

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.optimize import deg34_program, load_lp_json, solve_lp_max


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fit_linear(results: list[tuple[int, Fraction]]) -> tuple[Fraction, Fraction] | None:
    if len(results) < 2:
        return None
    n1, v1 = results[0]
    n2, v2 = results[-1]
    if n1 == n2:
        return None
    slope = (v2 - v1) / Fraction(n2 - n1, 1)
    intercept = v1 - slope * n1
    for n, v in results:
        if v != slope * n + intercept:
            return None
    return slope, intercept


def _solve_deg34(
    min_n: int,
    max_n: int,
    include_deg3_bound: bool,
) -> list[dict[str, object]]:
    output: list[dict[str, object]] = []
    for n in range(min_n, max_n + 1):
        var_names, objective, eqs, ineqs = deg34_program(n, include_deg3_bound)
        solution = solve_lp_max(objective, eqs, ineqs)
        if solution is None:
            raise SystemExit(f"no feasible solution for n={n}")
        value, xs = solution
        k_value = Fraction(n, 1) / value if value > 0 else Fraction(0, 1)
        row = {
            "n": n,
            "max_charge": value,
            "K": k_value,
            "solution": dict(zip(var_names, xs)),
        }
        output.append(row)
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", default="deg34", choices=["deg34", "json"])
    parser.add_argument("--constraints")
    parser.add_argument("--min-n", type=int, default=5)
    parser.add_argument("--max-n", type=int, default=20)
    parser.add_argument("--include-deg3-bound", action="store_true")
    parser.add_argument("--show-solution", action="store_true")
    parser.add_argument("--fit-linear", action="store_true")
    parser.add_argument("--summary-json")
    parser.add_argument("--cert-out")
    parser.add_argument("--cert-name")
    parser.add_argument("--cert-from-fit", action="store_true")
    args = parser.parse_args()

    if args.min_n > args.max_n:
        raise SystemExit("--min-n must be <= --max-n")

    if args.constraints:
        args.model = "json"

    if args.model == "deg34":
        rows = _solve_deg34(args.min_n, args.max_n, args.include_deg3_bound)
    elif args.model == "json":
        if not args.constraints:
            raise SystemExit("--constraints is required for model=json")
        rows = []
        for n in range(args.min_n, args.max_n + 1):
            var_names, objective, eqs, ineqs = load_lp_json(args.constraints, n)
            solution = solve_lp_max(objective, eqs, ineqs)
            if solution is None:
                raise SystemExit(f"no feasible solution for n={n}")
            value, xs = solution
            k_value = Fraction(n, 1) / value if value > 0 else Fraction(0, 1)
            rows.append(
                {
                    "n": n,
                    "max_charge": value,
                    "K": k_value,
                    "solution": dict(zip(var_names, xs)),
                }
            )
    else:
        raise SystemExit(f"unknown model {args.model}")

    print(
        f"model={args.model} n=[{args.min_n},{args.max_n}] "
        f"include_deg3_bound={args.include_deg3_bound}"
    )
    for row in rows:
        n = row["n"]
        max_charge = row["max_charge"]
        k_val = row["K"]
        print(
            f"n={n} max_charge={_format_fraction(max_charge)} "
            f"K={_format_fraction(k_val)}"
        )
        if args.show_solution:
            solution = row["solution"]
            parts = [f"{name}={_format_fraction(value)}" for name, value in solution.items()]
            print("  " + " ".join(parts))

    min_k_row = min(rows, key=lambda r: r["K"])
    print(
        "min_K_in_range="
        f"{_format_fraction(min_k_row['K'])} at n={min_k_row['n']}"
    )

    fit = None
    if args.fit_linear or args.cert_out:
        fit = _fit_linear([(row["n"], row["max_charge"]) for row in rows])
        if args.fit_linear:
            if fit is None:
                print("linear_fit=none")
            else:
                slope, intercept = fit
                print(
                    "linear_fit="
                    f"{_format_fraction(slope)}*n+{_format_fraction(intercept)}"
                )

    if args.summary_json:
        data = {
            "model": args.model,
            "min_n": args.min_n,
            "max_n": args.max_n,
            "include_deg3_bound": args.include_deg3_bound,
            "results": [
                {
                    "n": row["n"],
                    "max_charge": [
                        row["max_charge"].numerator,
                        row["max_charge"].denominator,
                    ],
                    "K": [row["K"].numerator, row["K"].denominator],
                    "solution": {
                        name: [value.numerator, value.denominator]
                        for name, value in row["solution"].items()
                    },
                }
                for row in rows
            ],
            "min_K": {
                "n": min_k_row["n"],
                "value": [min_k_row["K"].numerator, min_k_row["K"].denominator],
            },
        }
        with open(args.summary_json, "w", encoding="utf-8") as handle:
            json.dump(data, handle, indent=2, sort_keys=True)

    if args.cert_out:
        if fit is None:
            raise SystemExit("cannot write certificate: no exact linear fit")
        slope, intercept = fit
        if slope <= 0:
            raise SystemExit("cannot write certificate: non-positive slope")
        if intercept > 0:
            raise SystemExit("cannot write certificate: positive intercept")
        k_value = Fraction(1, 1) / slope
        cert_name = args.cert_name
        if cert_name is None:
            cert_name = "K_deg34" if args.model == "deg34" else "K_lp"
        payload = {
            "constants": {
                cert_name: [k_value.numerator, k_value.denominator],
            }
        }
        with open(args.cert_out, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        print(
            f"wrote_certificate name={cert_name} K={_format_fraction(k_value)} "
            f"path={args.cert_out}"
        )


if __name__ == "__main__":
    main()

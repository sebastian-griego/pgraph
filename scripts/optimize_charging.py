#!/usr/bin/env python3
"""Solve small charging LPs exactly and report the worst-case bound."""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
import sys
from fractions import Fraction

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.optimize import Constraint, deg34_program, load_lp_json, solve_lp_max


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _dot(coeffs: list[Fraction] | tuple[Fraction, ...], xs: list[Fraction]) -> Fraction:
    return sum(c * x for c, x in zip(coeffs, xs))


def _format_constraint(constraint: Constraint, var_names: tuple[str, ...]) -> str:
    terms: list[tuple[str, str]] = []
    for coeff, name in zip(constraint.coeffs, var_names):
        if coeff == 0:
            continue
        sign = "-" if coeff < 0 else "+"
        abs_coeff = -coeff if coeff < 0 else coeff
        if abs_coeff == 1:
            term = name
        else:
            term = f"{_format_fraction(abs_coeff)}*{name}"
        terms.append((sign, term))
    if not terms:
        lhs = "0"
    else:
        first_sign, first_term = terms[0]
        lhs = f"-{first_term}" if first_sign == "-" else first_term
        for sign, term in terms[1:]:
            lhs += f" {sign} {term}"
    label = f" [{constraint.label}]" if constraint.label else ""
    return f"{lhs} <= {_format_fraction(constraint.rhs)}{label}"


def _tight_inequalities(ineqs: list[Constraint], xs: list[Fraction]) -> list[int]:
    tight: list[int] = []
    for idx, constraint in enumerate(ineqs):
        if _dot(constraint.coeffs, xs) == constraint.rhs:
            tight.append(idx)
    return tight


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
    parser.add_argument("--show-tight", action="store_true")
    parser.add_argument("--show-min-tight", action="store_true")
    parser.add_argument("--min-k-only", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--min-k-json")
    parser.add_argument("--min-k-slack", type=int, default=0)
    parser.add_argument("--min-k-slack-all", action="store_true")
    parser.add_argument("--quiet-slacks", action="store_true")
    parser.add_argument("--quiet-min-k", action="store_true")
    parser.add_argument("--quiet-all", action="store_true")
    parser.add_argument("--tight-summary", action="store_true")
    parser.add_argument("--tight-summary-json")
    parser.add_argument("--fit-linear", action="store_true")
    parser.add_argument("--summary-json")
    parser.add_argument("--cert-out")
    parser.add_argument("--cert-name")
    parser.add_argument("--cert-from-fit", action="store_true")
    args = parser.parse_args()

    if args.min_n > args.max_n:
        raise SystemExit("--min-n must be <= --max-n")

    if args.quiet_all:
        args.quiet = True
        args.quiet_slacks = True
        args.quiet_min_k = True

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

    if (
        args.show_tight
        or args.show_min_tight
        or args.summary_json
        or args.tight_summary
        or args.tight_summary_json
        or args.min_k_json
        or args.min_k_slack
        or args.min_k_slack_all
    ):
        for row in rows:
            n = row["n"]
            if args.model == "deg34":
                var_names, _, _, ineqs = deg34_program(n, args.include_deg3_bound)
            else:
                if not args.constraints:
                    raise SystemExit("--constraints is required for model=json")
                var_names, _, _, ineqs = load_lp_json(args.constraints, n)
            xs = [row["solution"][name] for name in var_names]
            row["tight_ineqs"] = _tight_inequalities(ineqs, xs)

    if not args.quiet:
        print(
            f"model={args.model} n=[{args.min_n},{args.max_n}] "
            f"include_deg3_bound={args.include_deg3_bound}"
        )
    min_k_row = min(rows, key=lambda r: r["K"])
    if not args.min_k_only and not args.quiet:
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
            if args.show_tight:
                tight_ineqs = row.get("tight_ineqs", [])
                if tight_ineqs:
                    print("  tight_ineqs=" + ", ".join(str(idx) for idx in tight_ineqs))
                    if args.model == "deg34":
                        var_names, _, _, ineqs = deg34_program(n, args.include_deg3_bound)
                    else:
                        if not args.constraints:
                            raise SystemExit("--constraints is required for model=json")
                        var_names, _, _, ineqs = load_lp_json(args.constraints, n)
                    for idx in tight_ineqs:
                        constraint = ineqs[idx]
                        print(f"    ineq[{idx}]: {_format_constraint(constraint, var_names)}")
                else:
                    print("  tight_ineqs=none")
    if not args.quiet_min_k:
        print(
            "min_K_in_range="
            f"{_format_fraction(min_k_row['K'])} at n={min_k_row['n']}"
        )
    min_k_var_names = None
    min_k_ineqs = None
    min_k_slacks = None
    if (
        args.show_min_tight
        or args.min_k_json
        or args.min_k_slack
        or args.min_k_slack_all
    ):
        n = min_k_row["n"]
        if args.model == "deg34":
            min_k_var_names, _, _, min_k_ineqs = deg34_program(n, args.include_deg3_bound)
        else:
            if not args.constraints:
                raise SystemExit("--constraints is required for model=json")
            min_k_var_names, _, _, min_k_ineqs = load_lp_json(args.constraints, n)
    slack_limit = 0
    if args.min_k_slack_all:
        slack_limit = len(min_k_ineqs or [])
    elif args.min_k_slack > 0:
        slack_limit = args.min_k_slack
    if slack_limit > 0:
        var_names = min_k_var_names
        ineqs = min_k_ineqs
        xs = [min_k_row["solution"][name] for name in var_names]
        slacks = []
        for idx, constraint in enumerate(ineqs):
            slack = constraint.rhs - _dot(constraint.coeffs, xs)
            slacks.append((slack, idx, constraint))
        slacks.sort(key=lambda row: (row[0], row[1]))
        min_k_slacks = [
            {
                "index": idx,
                "label": constraint.label,
                "constraint": _format_constraint(constraint, var_names),
                "slack": [slack.numerator, slack.denominator],
            }
            for slack, idx, constraint in slacks[:slack_limit]
        ]
    if args.min_k_json:
        var_names = min_k_var_names
        ineqs = min_k_ineqs
        tight_entries = []
        for idx in min_k_row.get("tight_ineqs", []):
            constraint = ineqs[idx]
            tight_entries.append(
                {
                    "index": idx,
                    "label": constraint.label,
                    "constraint": _format_constraint(constraint, var_names),
                }
            )
        payload = {
            "model": args.model,
            "min_n": args.min_n,
            "max_n": args.max_n,
            "include_deg3_bound": args.include_deg3_bound,
            "min_K": {
                "n": n,
                "K": [min_k_row["K"].numerator, min_k_row["K"].denominator],
                "max_charge": [
                    min_k_row["max_charge"].numerator,
                    min_k_row["max_charge"].denominator,
                ],
                "solution": {
                    name: [
                        min_k_row["solution"][name].numerator,
                        min_k_row["solution"][name].denominator,
                    ]
                    for name in var_names
                },
                "tight": tight_entries,
            },
        }
        if min_k_slacks is not None:
            payload["min_K"]["slacks"] = min_k_slacks
        with open(args.min_k_json, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        if not args.quiet:
            print(f"wrote_min_k path={args.min_k_json}")
    if args.show_min_tight:
        var_names = min_k_var_names
        ineqs = min_k_ineqs
        print("min_K_solution:")
        parts = [
            f"{name}={_format_fraction(min_k_row['solution'][name])}"
            for name in var_names
        ]
        print("  " + " ".join(parts))
        tight_ineqs = min_k_row.get("tight_ineqs", [])
        if tight_ineqs:
            print("  tight_ineqs=" + ", ".join(str(idx) for idx in tight_ineqs))
            for idx in tight_ineqs:
                constraint = ineqs[idx]
                print(
                    f"    ineq[{idx}]: {_format_constraint(constraint, var_names)}"
                )
        else:
            print("  tight_ineqs=none")
    if slack_limit > 0 and not args.quiet_slacks:
        var_names = min_k_var_names
        print("min_K_slacks:")
        for entry in min_k_slacks or []:
            slack = Fraction(entry["slack"][0], entry["slack"][1])
            print(
                f"  slack[{entry['index']}]={_format_fraction(slack)} "
                f"{entry['constraint']}"
            )
    if args.tight_summary or args.tight_summary_json:
        counts: Counter[int] = Counter()
        for row in rows:
            counts.update(row.get("tight_ineqs", []))
        if args.model == "deg34":
            var_names, _, _, ineqs = deg34_program(args.min_n, args.include_deg3_bound)
        else:
            if not args.constraints:
                raise SystemExit("--constraints is required for model=json")
            var_names, _, _, ineqs = load_lp_json(args.constraints, args.min_n)
        total = len(rows)
        if args.tight_summary:
            print("tight_summary:")
            if not counts:
                print("  none")
            else:
                for idx, count in counts.most_common():
                    label = ineqs[idx].label
                    label_str = f" [{label}]" if label else ""
                    print(f"  ineq[{idx}]{label_str}: {count}/{total}")
        if args.tight_summary_json:
            payload = {
                "model": args.model,
                "min_n": args.min_n,
                "max_n": args.max_n,
                "total": total,
                "counts": [
                    {
                        "index": idx,
                        "label": ineqs[idx].label,
                        "count": count,
                        "fraction": [count, total],
                        "constraint": _format_constraint(ineqs[idx], var_names),
                    }
                    for idx, count in counts.most_common()
                ],
            }
            with open(args.tight_summary_json, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, indent=2, sort_keys=True)
            if not args.quiet:
                print(f"wrote_tight_summary path={args.tight_summary_json}")

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
                    "tight_ineqs": row.get("tight_ineqs", []),
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
        if not args.quiet:
            print(
                f"wrote_certificate name={cert_name} K={_format_fraction(k_value)} "
                f"path={args.cert_out}"
            )


if __name__ == "__main__":
    main()

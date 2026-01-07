#!/usr/bin/env python3
"""Export rational parameters for Lean to import as a JSON certificate."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def parse_fraction(text: str) -> Fraction:
    if "/" in text:
        num_str, den_str = text.split("/", 1)
        return Fraction(int(num_str.strip()), int(den_str.strip()))
    return Fraction(int(text.strip()), 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument(
        "--const",
        action="append",
        default=[],
        help="name=value with value as integer or rational like 243/20",
    )
    args = parser.parse_args()

    constants: dict[str, list[int]] = {}
    for item in args.const:
        if "=" not in item:
            raise SystemExit("--const must be name=value")
        name, value = item.split("=", 1)
        frac = parse_fraction(value)
        constants[name] = [frac.numerator, frac.denominator]

    payload = {"constants": constants}
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()

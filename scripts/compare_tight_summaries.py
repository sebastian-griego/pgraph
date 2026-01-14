#!/usr/bin/env python3
"""Compare tight-constraint summaries across two LP runs."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def _load_summary(path: str, key_mode: str) -> tuple[int, dict[str, dict[str, object]]]:
    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    total = int(data.get("total", 0))
    counts: dict[str, dict[str, object]] = {}
    for entry in data.get("counts", []):
        if key_mode == "label" and entry.get("label"):
            key = f"label:{entry.get('label')}"
        elif key_mode == "index":
            key = f"idx:{entry.get('index')}"
        else:
            key = entry.get("constraint") or f"idx:{entry.get('index')}"
        counts[str(key)] = entry
    return total, counts


def _load_min_k(path: str, key_mode: str) -> tuple[int, dict[str, dict[str, object]]]:
    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    min_k = data.get("min_K", {})
    n = int(min_k.get("n", 0))
    counts: dict[str, dict[str, object]] = {}
    for entry in min_k.get("tight", []):
        if key_mode == "label" and entry.get("label"):
            key = f"label:{entry.get('label')}"
        elif key_mode == "index":
            key = f"idx:{entry.get('index')}"
        else:
            key = entry.get("constraint") or f"idx:{entry.get('index')}"
        counts[str(key)] = entry
    return n, counts


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _parse_fraction(text: str) -> Fraction:
    try:
        return Fraction(text)
    except Exception as exc:  # pragma: no cover - argparse guards usage
        raise SystemExit(f"invalid fraction {text!r}") from exc


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", required=True, help="first tight-summary JSON")
    parser.add_argument("--b", required=True, help="second tight-summary JSON")
    parser.add_argument("--key", choices=["constraint", "label", "index"], default="constraint")
    parser.add_argument("--mode", choices=["summary", "min-k"], default="summary")
    parser.add_argument("--top", type=int, default=10)
    parser.add_argument("--min-delta", default="0", help="minimum absolute delta to show")
    parser.add_argument("--show-unchanged", action="store_true")
    parser.add_argument("--print-keys", action="store_true")
    args = parser.parse_args()

    if args.mode == "summary":
        total_a, counts_a = _load_summary(args.a, args.key)
        total_b, counts_b = _load_summary(args.b, args.key)
    else:
        total_a, counts_a = _load_min_k(args.a, args.key)
        total_b, counts_b = _load_min_k(args.b, args.key)
    if total_a <= 0 or total_b <= 0:
        if args.mode == "summary":
            raise SystemExit("summary totals must be positive")
        raise SystemExit("min-K entries must include a positive n")

    min_delta = _parse_fraction(args.min_delta)
    keys = set(counts_a) | set(counts_b)
    if args.print_keys:
        for key in sorted(keys):
            print(key)
        return
    rows: list[tuple[Fraction, str, int, int]] = []
    for key in keys:
        count_a = int(counts_a.get(key, {}).get("count", 0))
        count_b = int(counts_b.get(key, {}).get("count", 0))
        frac_a = Fraction(count_a, total_a)
        frac_b = Fraction(count_b, total_b)
        delta = frac_b - frac_a
        if not args.show_unchanged and delta == 0:
            continue
        if abs(delta) < min_delta:
            continue
        rows.append((abs(delta), key, count_a, count_b))

    rows.sort(key=lambda row: (-row[0], row[1]))
    label = "summary" if args.mode == "summary" else "min_k_n"
    print(f"{label}_a={total_a}")
    print(f"{label}_b={total_b}")
    if min_delta != 0:
        print(f"min_delta={_format_fraction(min_delta)}")
    if not rows:
        print("no_changes")
        return
    for _, key, count_a, count_b in rows[: args.top]:
        frac_a = Fraction(count_a, total_a)
        frac_b = Fraction(count_b, total_b)
        delta = frac_b - frac_a
        print(
            f"{key}: "
            f"{count_a}/{total_a} -> {count_b}/{total_b} "
            f"(delta={_format_fraction(delta)})"
        )


if __name__ == "__main__":
    main()

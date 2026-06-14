#!/usr/bin/env python3
"""Generate exact diagnostics for a small point set."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.analysis import analyze_point_set  # noqa: E402
from planegraphs.geometry import Point  # noqa: E402


def parse_points(payload: object) -> list[Point]:
    rows = payload.get("points") if isinstance(payload, dict) else payload
    if not isinstance(rows, list):
        raise ValueError("points must be a list or an object with a points list")

    points: list[Point] = []
    for idx, row in enumerate(rows):
        if not isinstance(row, (list, tuple)) or len(row) != 2:
            raise ValueError(f"point {idx} must be a length-2 list")
        x, y = row
        if not isinstance(x, int) or not isinstance(y, int):
            raise ValueError(f"point {idx} coordinates must be integers")
        points.append((x, y))
    return points


def load_points(args: argparse.Namespace) -> list[Point]:
    if bool(args.points) == bool(args.input):
        raise SystemExit("provide exactly one of --points or --input")
    if args.points:
        payload = json.loads(args.points)
    else:
        payload = json.loads(Path(args.input).read_text(encoding="utf-8"))
    return parse_points(payload)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--points", help='JSON points, for example: "[[0,0],[2,0],[0,2],[1,1]]"')
    parser.add_argument("--input", help="JSON file containing either a points list or {'points': [...]} object")
    parser.add_argument("--format", choices=["json", "markdown"], default="json")
    parser.add_argument("--out", help="write report to this path instead of stdout")
    parser.add_argument(
        "--max-triangulations",
        type=int,
        default=1000,
        help="enumerate at most this many triangulations before marking the report truncated",
    )
    args = parser.parse_args()

    points = load_points(args)
    report = analyze_point_set(points, max_triangulations=args.max_triangulations)
    if args.format == "json":
        text = json.dumps(report.to_json_dict(), indent=2, sort_keys=True) + "\n"
    else:
        text = report.to_markdown()

    if args.out:
        Path(args.out).write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Verify exact JSON certificates against mined degree-vector data."""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from planegraphs.certificate import (  # noqa: E402
    format_fraction,
    load_certificate,
    load_degree_vectors,
    verify_deg56_charge_certificate,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", required=True)
    parser.add_argument("--data", required=True)
    parser.add_argument("--family", choices=["deg56"], default="deg56")
    parser.add_argument("--k-name", default="K_deg56")
    parser.add_argument("--summary-out")
    args = parser.parse_args()

    constants = load_certificate(args.certificate)
    vectors = load_degree_vectors(args.data)
    if args.family == "deg56":
        audit = verify_deg56_charge_certificate(constants, vectors, k_name=args.k_name)
    else:  # pragma: no cover - argparse choices keep this unreachable
        raise SystemExit(f"unsupported family: {args.family}")

    print(f"certificate={args.certificate}")
    print(f"data={args.data}")
    print(f"vectors={audit.total_vectors}")
    print(f"k={format_fraction(audit.k_value)}")
    print(f"worst_margin={format_fraction(audit.worst_margin)} at n={audit.worst_n} vec={audit.worst_vector}")
    print(f"violations={audit.total_violations}")

    if args.summary_out:
        with open(args.summary_out, "w", encoding="utf-8") as handle:
            json.dump(audit.to_json_dict(), handle, indent=2, sort_keys=True)
            handle.write("\n")
        print(f"wrote_summary={args.summary_out}")

    if audit.total_violations:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

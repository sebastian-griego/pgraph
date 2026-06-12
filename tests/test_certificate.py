import json
from fractions import Fraction
import subprocess
import sys

from planegraphs.certificate import (
    load_certificate,
    load_degree_vectors,
    parse_fraction_pair,
    verify_deg56_charge_certificate,
)


def test_parse_fraction_pair_rejects_bad_values():
    assert parse_fraction_pair([2, 4]) == Fraction(1, 2)

    for value in ([1], [1, 0], ["1", 2], "1/2"):
        try:
            parse_fraction_pair(value)
        except ValueError:
            pass
        else:  # pragma: no cover - keeps the assertion message clear
            raise AssertionError(f"expected {value!r} to be rejected")


def test_verify_deg56_certificate_detects_exact_violation():
    vectors = [(1, 0, 0, 0, 0), (0, 2, 0, 0, 0)]
    constants = {
        "K_deg56": Fraction(8, 1),
        "w3": Fraction(1, 8),
        "w4": Fraction(1, 16),
        "w5": Fraction(1, 32),
        "w6": Fraction(1, 64),
        "wL": Fraction(1, 128),
    }
    audit = verify_deg56_charge_certificate(constants, vectors)
    assert audit.total_vectors == 2
    assert audit.total_violations == 0
    assert audit.worst_margin == Fraction(0)

    bad = dict(constants)
    bad["K_deg56"] = Fraction(9, 1)
    bad_audit = verify_deg56_charge_certificate(bad, vectors)
    assert bad_audit.total_violations == 1
    assert bad_audit.worst_margin == Fraction(-1, 8)


def test_load_certificate_and_degree_vectors(tmp_path):
    cert_path = tmp_path / "cert.json"
    data_path = tmp_path / "vectors.json"
    cert_path.write_text(
        json.dumps(
            {
                "constants": {
                    "K_deg56": [8, 1],
                    "w3": [1, 8],
                    "w4": [1, 16],
                    "w5": [1, 32],
                    "w6": [1, 64],
                    "wL": [1, 128],
                }
            }
        ),
        encoding="utf-8",
    )
    data_path.write_text(json.dumps({"vectors": [{"v3": 1, "v4": 0, "v5": 0, "v6": 0, "vL": 0}]}), encoding="utf-8")

    constants = load_certificate(cert_path)
    vectors = load_degree_vectors(data_path)
    audit = verify_deg56_charge_certificate(constants, vectors)
    assert audit.to_json_dict()["total_vectors"] == 1
    assert audit.to_json_dict()["worst_margin"] == [0, 1]


def test_verify_certificate_script_writes_summary(tmp_path):
    summary_path = tmp_path / "summary.json"
    subprocess.run(
        [
            sys.executable,
            "scripts/verify_certificate.py",
            "--certificate",
            "certificates/deg56_sample.json",
            "--data",
            "data/degree_vectors.json",
            "--summary-out",
            str(summary_path),
        ],
        check=True,
    )
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    assert summary["total_vectors"] > 0
    assert summary["total_violations"] == 0

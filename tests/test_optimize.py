import json
from fractions import Fraction

from planegraphs.optimize import eval_linear_expr, load_lp_json, max_charge_deg34, parse_linear_expr


def test_deg34_max_charge_matches_formula():
    for n in [5, 10, 17]:
        value, _ = max_charge_deg34(n)
        assert value == Fraction(11 * n - 6, 112)


def test_parse_linear_expr():
    a, b = parse_linear_expr("6*n-6")
    assert a == Fraction(6, 1)
    assert b == Fraction(-6, 1)
    assert eval_linear_expr("6*n-6", 5) == Fraction(24, 1)


def test_load_lp_json(tmp_path):
    payload = {
        "variables": ["v3", "v4"],
        "objective": ["1/8", "1/16"],
        "equalities": [{"coeffs": ["1", "1"], "rhs": "n"}],
        "inequalities": [{"coeffs": ["-1", "0"], "rhs": "0"}],
    }
    path = tmp_path / "lp.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    names, objective, eqs, ineqs = load_lp_json(str(path), 5)
    assert names == ("v3", "v4")
    assert objective == (Fraction(1, 8), Fraction(1, 16))
    assert eqs[0].rhs == Fraction(5, 1)
    assert ineqs[0].coeffs == (Fraction(-1, 1), Fraction(0, 1))

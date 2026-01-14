"""Exact linear-programming utilities for small charging optimizations."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
import json
from typing import Iterable, Sequence


@dataclass(frozen=True)
class Constraint:
    """Linear constraint of the form coeffs · x <= rhs or == rhs."""

    coeffs: tuple[Fraction, ...]
    rhs: Fraction
    relation: str  # "<=" or "=="
    label: str | None = None


def parse_linear_expr(expr: str) -> tuple[Fraction, Fraction]:
    """Parse a linear expression in n into (a, b) for a*n + b."""
    text = expr.replace(" ", "")
    if not text:
        raise ValueError("empty expression")
    terms: list[str] = []
    current = ""
    for idx, ch in enumerate(text):
        if ch in "+-":
            if idx == 0:
                current = ch
            else:
                terms.append(current)
                current = ch
        else:
            current += ch
    terms.append(current)

    a = Fraction(0)
    b = Fraction(0)
    for term in terms:
        if term in ("", "+", "-"):
            raise ValueError(f"invalid term in expression {expr!r}")
        if "n" in term:
            a += _parse_n_term(term)
        else:
            b += _parse_fraction(term)
    return a, b


def eval_linear_expr(expr: str, n: int) -> Fraction:
    """Evaluate a linear expression in n."""
    a, b = parse_linear_expr(expr)
    return a * Fraction(n, 1) + b


def load_lp_json(
    path: str, n: int
) -> tuple[tuple[str, ...], tuple[Fraction, ...], list[Constraint], list[Constraint]]:
    """Load a linear program from JSON, substituting the numeric value of n."""
    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    variables = tuple(data["variables"])
    objective_exprs = data["objective"]
    objective = _parse_expr_list(objective_exprs, n)

    eqs = []
    for item in data.get("equalities", []):
        coeffs = _parse_expr_list(item["coeffs"], n)
        rhs = eval_linear_expr(item["rhs"], n)
        label = item.get("label")
        eqs.append(Constraint(coeffs=coeffs, rhs=rhs, relation="==", label=label))

    ineqs = []
    for item in data.get("inequalities", []):
        coeffs = _parse_expr_list(item["coeffs"], n)
        rhs = eval_linear_expr(item["rhs"], n)
        label = item.get("label")
        ineqs.append(Constraint(coeffs=coeffs, rhs=rhs, relation="<=", label=label))

    return variables, objective, eqs, ineqs


def _parse_fraction(text: str) -> Fraction:
    value = text.strip()
    if "/" in value:
        num_str, den_str = value.split("/", 1)
        return Fraction(int(num_str.strip()), int(den_str.strip()))
    return Fraction(int(value), 1)


def _parse_n_term(term: str) -> Fraction:
    if term in ("n", "+n"):
        return Fraction(1)
    if term == "-n":
        return Fraction(-1)
    if term.endswith("*n"):
        coeff = term[:-2]
    elif term.endswith("n"):
        coeff = term[:-1]
    else:
        raise ValueError(f"invalid n-term {term!r}")
    if coeff in ("", "+"):
        return Fraction(1)
    if coeff == "-":
        return Fraction(-1)
    return _parse_fraction(coeff)


def _parse_expr_list(exprs: Sequence[str], n: int) -> tuple[Fraction, ...]:
    return tuple(eval_linear_expr(expr, n) for expr in exprs)


def _dot(coeffs: Sequence[Fraction], xs: Sequence[Fraction]) -> Fraction:
    return sum(c * x for c, x in zip(coeffs, xs))


def _solve_linear_system(
    rows: Sequence[Sequence[Fraction]], rhs: Sequence[Fraction]
) -> list[Fraction] | None:
    """Solve a square linear system with Fractions, returning None if singular."""
    n = len(rows)
    if n == 0:
        return []
    matrix = [list(row) + [b] for row, b in zip(rows, rhs)]
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if matrix[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            return None
        if pivot != col:
            matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        pivot_val = matrix[col][col]
        for c in range(col, n + 1):
            matrix[col][c] /= pivot_val
        for r in range(n):
            if r == col:
                continue
            factor = matrix[r][col]
            if factor == 0:
                continue
            for c in range(col, n + 1):
                matrix[r][c] -= factor * matrix[col][c]
    return [row[n] for row in matrix]


def solve_lp_max(
    objective: Sequence[Fraction],
    eqs: Sequence[Constraint],
    ineqs: Sequence[Constraint],
) -> tuple[Fraction, list[Fraction]] | None:
    """Maximize objective · x subject to constraints, returning (value, x)."""
    num_vars = len(objective)
    if any(len(c.coeffs) != num_vars for c in (*eqs, *ineqs)):
        raise ValueError("constraint length does not match objective dimension")
    if any(c.relation != "==" for c in eqs):
        raise ValueError("eqs must use relation '=='")
    if any(c.relation != "<=" for c in ineqs):
        raise ValueError("ineqs must use relation '<='")

    needed = num_vars - len(eqs)
    if needed < 0:
        raise ValueError("too many equalities for the number of variables")
    if needed > len(ineqs):
        return None

    best_val: Fraction | None = None
    best_x: list[Fraction] | None = None
    eq_rows = [c.coeffs for c in eqs]
    eq_rhs = [c.rhs for c in eqs]

    if needed == 0:
        candidate = _solve_linear_system(eq_rows, eq_rhs)
        if candidate is None:
            return None
        if _feasible(candidate, eqs, ineqs):
            best_val = _dot(objective, candidate)
            best_x = candidate
    else:
        for idxs in combinations(range(len(ineqs)), needed):
            rows = list(eq_rows)
            rhs = list(eq_rhs)
            for idx in idxs:
                rows.append(ineqs[idx].coeffs)
                rhs.append(ineqs[idx].rhs)
            candidate = _solve_linear_system(rows, rhs)
            if candidate is None:
                continue
            if not _feasible(candidate, eqs, ineqs):
                continue
            value = _dot(objective, candidate)
            if best_val is None or value > best_val:
                best_val = value
                best_x = candidate

    if best_val is None or best_x is None:
        return None
    return best_val, best_x


def _feasible(
    xs: Sequence[Fraction],
    eqs: Sequence[Constraint],
    ineqs: Sequence[Constraint],
) -> bool:
    for c in eqs:
        if _dot(c.coeffs, xs) != c.rhs:
            return False
    for c in ineqs:
        if _dot(c.coeffs, xs) > c.rhs:
            return False
    return True


def deg34_program(n: int, include_deg3_bound: bool) -> tuple[
    tuple[str, ...],
    tuple[Fraction, ...],
    list[Constraint],
    list[Constraint],
]:
    """Return the deg34 LP for a fixed n."""
    if n <= 0:
        raise ValueError("n must be positive")
    var_names = ("v3", "v4", "vlarge")
    nfrac = Fraction(n, 1)
    objective = (Fraction(1, 8), Fraction(1, 16), Fraction(1, 32))

    eqs = [
        Constraint(
            coeffs=(Fraction(1), Fraction(1), Fraction(1)),
            rhs=nfrac,
            relation="==",
            label="partition",
        )
    ]

    ineqs = [
        Constraint(
            coeffs=(Fraction(-1), Fraction(0), Fraction(0)),
            rhs=Fraction(0),
            relation="<=",
            label="nonneg_v3",
        ),
        Constraint(
            coeffs=(Fraction(0), Fraction(-1), Fraction(0)),
            rhs=Fraction(0),
            relation="<=",
            label="nonneg_v4",
        ),
        Constraint(
            coeffs=(Fraction(0), Fraction(0), Fraction(-1)),
            rhs=Fraction(0),
            relation="<=",
            label="nonneg_vlarge",
        ),
        Constraint(
            coeffs=(Fraction(9), Fraction(2), Fraction(0)),
            rhs=Fraction(6 * n - 6, 1),
            relation="<=",
            label="deg34_bound",
        ),
    ]

    if include_deg3_bound:
        ineqs.append(
            Constraint(
                coeffs=(Fraction(3), Fraction(0), Fraction(0)),
                rhs=Fraction(2 * n - 3, 1),
                relation="<=",
                label="deg3_bound",
            )
        )

    return var_names, objective, eqs, ineqs


def max_charge_deg34(n: int, include_deg3_bound: bool = False) -> tuple[Fraction, list[Fraction]]:
    """Solve the deg34 LP and return (max_charge, variable_values)."""
    _, objective, eqs, ineqs = deg34_program(n, include_deg3_bound)
    solution = solve_lp_max(objective, eqs, ineqs)
    if solution is None:
        raise RuntimeError("deg34 LP is infeasible")
    return solution

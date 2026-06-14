"""Exact certificate loading and verification utilities."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
from typing import Iterable

DegreeVector = tuple[int, int, int, int, int]


@dataclass(frozen=True)
class CertificateAudit:
    total_vectors: int
    total_violations: int
    worst_margin: Fraction
    worst_vector: DegreeVector
    worst_n: int
    k_value: Fraction
    weights: tuple[Fraction, Fraction, Fraction, Fraction, Fraction]

    def to_json_dict(self) -> dict[str, object]:
        return {
            "total_vectors": self.total_vectors,
            "total_violations": self.total_violations,
            "worst_margin": fraction_payload(self.worst_margin),
            "worst_vector": list(self.worst_vector),
            "worst_n": self.worst_n,
            "k_value": fraction_payload(self.k_value),
            "weights": [fraction_payload(w) for w in self.weights],
        }


def fraction_payload(value: Fraction) -> list[int]:
    return [int(value.numerator), int(value.denominator)]


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def load_certificate(path: str | Path) -> dict[str, Fraction]:
    with open(path, "r", encoding="utf-8") as handle:
        payload = json.load(handle)
    constants = payload.get("constants") if isinstance(payload, dict) else None
    if not isinstance(constants, dict):
        raise ValueError("certificate must contain a constants object")
    return {str(name): parse_fraction_pair(value, name=str(name)) for name, value in constants.items()}


def parse_fraction_pair(value: object, *, name: str = "value") -> Fraction:
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError(f"{name} must be [numerator, denominator]")
    numerator, denominator = value
    if not isinstance(numerator, int) or not isinstance(denominator, int):
        raise ValueError(f"{name} numerator and denominator must be integers")
    if denominator == 0:
        raise ValueError(f"{name} denominator must be nonzero")
    return Fraction(numerator, denominator)


def load_degree_vectors(path: str | Path) -> list[DegreeVector]:
    with open(path, "r", encoding="utf-8") as handle:
        payload = json.load(handle)
    rows = payload.get("vectors", []) if isinstance(payload, dict) else payload
    if not isinstance(rows, list):
        raise ValueError("degree vector data must be a list or an object with a vectors list")

    vectors: list[DegreeVector] = []
    for idx, row in enumerate(rows):
        try:
            vectors.append(parse_degree_vector(row))
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"invalid degree vector at index {idx}: {row!r}") from exc
    return vectors


def parse_degree_vector(row: object) -> DegreeVector:
    if isinstance(row, dict):
        return (
            int(row["v3"]),
            int(row["v4"]),
            int(row["v5"]),
            int(row["v6"]),
            int(row.get("vlarge", row.get("vL", 0))),
        )
    if isinstance(row, list) and len(row) == 5:
        return tuple(int(x) for x in row)  # type: ignore[return-value]
    raise ValueError("degree vector must be a dict or length-5 list")


def verify_deg56_charge_certificate(
    constants: dict[str, Fraction],
    vectors: Iterable[DegreeVector],
    *,
    k_name: str = "K_deg56",
    weight_names: tuple[str, str, str, str, str] = ("w3", "w4", "w5", "w6", "wL"),
) -> CertificateAudit:
    missing = [name for name in (k_name, *weight_names) if name not in constants]
    if missing:
        raise ValueError(f"certificate is missing constants: {', '.join(missing)}")

    k_value = constants[k_name]
    if k_value <= 0:
        raise ValueError(f"{k_name} must be positive")
    weights = tuple(constants[name] for name in weight_names)
    if any(weight < 0 for weight in weights):
        raise ValueError("weights must be nonnegative")

    total = 0
    violations = 0
    worst_margin: Fraction | None = None
    worst_vector: DegreeVector | None = None
    worst_n = 0

    for vector in vectors:
        total += 1
        n = sum(vector)
        if n <= 0:
            raise ValueError(f"degree vector has nonpositive size: {vector!r}")
        charge = sum(Fraction(count) * weight for count, weight in zip(vector, weights))
        margin = Fraction(n, 1) - k_value * charge
        if margin < 0:
            violations += 1
        if worst_margin is None or margin < worst_margin:
            worst_margin = margin
            worst_vector = vector
            worst_n = n

    if total == 0 or worst_margin is None or worst_vector is None:
        raise ValueError("no degree vectors to verify")

    return CertificateAudit(
        total_vectors=total,
        total_violations=violations,
        worst_margin=worst_margin,
        worst_vector=worst_vector,
        worst_n=worst_n,
        k_value=k_value,
        weights=weights,
    )

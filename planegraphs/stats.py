"""Statistics derived from plane graphs on a point set."""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable

from .crossing_graph import crossing_graph
from .geometry import Point
from .indepcount import IndepCounter


def pg(points: Iterable[Point]) -> int:
    """Count plane straight-line graphs on points."""
    _, adj = crossing_graph(points)
    return IndepCounter(adj).count()


def isolated_counts(points: Iterable[Point]) -> list[int]:
    """Count plane graphs in which each point is isolated."""
    pts = list(points)
    n = len(pts)
    segments, adj = crossing_graph(pts)
    m = len(segments)
    counter = IndepCounter(adj)
    all_mask = (1 << m) - 1

    incident_mask = [0] * n
    for idx, (i, j) in enumerate(segments):
        bit = 1 << idx
        incident_mask[i] |= bit
        incident_mask[j] |= bit

    counts: list[int] = []
    for k in range(n):
        mask = all_mask & ~incident_mask[k]
        counts.append(counter.count(mask))
    return counts


def isolated_probabilities(points: Iterable[Point]) -> list[Fraction]:
    """Compute the isolation probability for each point."""
    pts = list(points)
    total = pg(pts)
    counts = isolated_counts(pts)
    return [Fraction(c, total) for c in counts]


def expected_isolated(points: Iterable[Point]) -> Fraction:
    """Expected number of isolated vertices in a random plane graph."""
    return sum(isolated_probabilities(points), Fraction(0, 1))


def k_est(points: Iterable[Point]) -> Fraction:
    """Estimate K = n / E[I]."""
    pts = list(points)
    exp_iso = expected_isolated(pts)
    if exp_iso == 0:
        return Fraction(0, 1)
    return Fraction(len(pts), 1) / exp_iso

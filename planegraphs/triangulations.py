"""Enumerate triangulations of small point sets."""

from __future__ import annotations

from collections import Counter
from typing import Iterable

from .crossing_graph import crossing_graph
from .geometry import Point


def triangulation_degree_vectors(
    points: Iterable[Point],
    max_count: int | None = None,
) -> list[tuple[int, int, int, int, int]]:
    """Return degree count vectors (v3, v4, v5, v6, vlarge) for triangulations."""
    pts = list(points)
    n = len(pts)
    target_edges = 3 * n - 6
    if target_edges < 0:
        return []

    segments, adj = crossing_graph(pts)
    m = len(segments)
    if target_edges > m:
        return []

    degrees = [0] * n
    vectors: list[tuple[int, int, int, int, int]] = []
    seen = 0

    def choose_vertex(mask: int) -> int:
        best = -1
        best_deg = -1
        mtemp = mask
        while mtemp:
            lsb = mtemp & -mtemp
            v = lsb.bit_length() - 1
            deg = (adj[v] & mask).bit_count()
            if deg > best_deg:
                best = v
                best_deg = deg
            mtemp ^= lsb
        return best

    def record_vector() -> None:
        v3 = sum(1 for d in degrees if d == 3)
        v4 = sum(1 for d in degrees if d == 4)
        v5 = sum(1 for d in degrees if d == 5)
        v6 = sum(1 for d in degrees if d == 6)
        vlarge = n - v3 - v4 - v5 - v6
        vectors.append((v3, v4, v5, v6, vlarge))

    def backtrack(mask: int, chosen: int) -> None:
        nonlocal seen
        if max_count is not None and seen >= max_count:
            return
        if chosen == target_edges:
            record_vector()
            seen += 1
            return
        if mask == 0:
            return
        if chosen + mask.bit_count() < target_edges:
            return

        v = choose_vertex(mask)
        if v < 0:
            return

        i, j = segments[v]
        degrees[i] += 1
        degrees[j] += 1
        backtrack(mask & ~(1 << v) & ~adj[v], chosen + 1)
        degrees[i] -= 1
        degrees[j] -= 1

        if max_count is not None and seen >= max_count:
            return
        backtrack(mask & ~(1 << v), chosen)

    backtrack((1 << m) - 1, 0)
    return vectors


def summarize_degree_vectors(
    vectors: Iterable[tuple[int, int, int, int, int]],
) -> Counter[tuple[int, int, int, int, int]]:
    """Return counts of identical degree vectors."""
    return Counter(vectors)

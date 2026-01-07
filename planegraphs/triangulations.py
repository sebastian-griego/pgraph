"""Enumerate triangulations of small point sets."""

from __future__ import annotations

from collections import Counter
from typing import Iterable

from .crossing_graph import crossing_graph
from .geometry import Point


def get_degrees(points: list[Point], edges: list[tuple[int, int]]) -> list[int]:
    """Compute vertex degrees for a set of edges."""
    degrees = [0] * len(points)
    for i, j in edges:
        degrees[i] += 1
        degrees[j] += 1
    return degrees


def enumerate_triangulations(
    points: Iterable[Point],
    max_count: int | None = None,
) -> list[list[tuple[int, int]]]:
    """Enumerate all triangulations as maximal non-crossing edge sets."""
    pts = list(points)
    segments, adj = crossing_graph(pts)
    m = len(segments)

    # Build the complement graph: edges correspond to non-crossing segments.
    compat = [set() for _ in range(m)]
    for i in range(m):
        row = compat[i]
        for j in range(m):
            if i == j:
                continue
            if (adj[i] >> j) & 1 == 0:
                row.add(j)

    results: list[list[tuple[int, int]]] = []

    def bron_kerbosch(r: set[int], p: set[int], x: set[int]) -> None:
        if max_count is not None and len(results) >= max_count:
            return
        if not p and not x:
            results.append([segments[i] for i in sorted(r)])
            return
        pivot_candidates = p | x
        if pivot_candidates:
            u = next(iter(pivot_candidates))
            exclude = compat[u]
        else:
            exclude = set()
        for v in list(p - exclude):
            bron_kerbosch(r | {v}, p & compat[v], x & compat[v])
            p.remove(v)
            x.add(v)
            if max_count is not None and len(results) >= max_count:
                return

    bron_kerbosch(set(), set(range(m)), set())
    return results


def triangulation_degree_vectors(
    points: Iterable[Point],
    max_count: int | None = None,
) -> list[tuple[int, int, int, int, int]]:
    """Return degree count vectors (v3, v4, v5, v6, vlarge) for triangulations."""
    pts = list(points)
    vectors: list[tuple[int, int, int, int, int]] = []
    triangulations = enumerate_triangulations(pts, max_count=max_count)
    for edges in triangulations:
        degrees = get_degrees(pts, edges)
        v3 = sum(1 for d in degrees if d == 3)
        v4 = sum(1 for d in degrees if d == 4)
        v5 = sum(1 for d in degrees if d == 5)
        v6 = sum(1 for d in degrees if d == 6)
        vlarge = sum(1 for d in degrees if d >= 7)
        vectors.append((v3, v4, v5, v6, vlarge))
    return vectors


def summarize_degree_vectors(
    vectors: Iterable[tuple[int, int, int, int, int]],
) -> Counter[tuple[int, int, int, int, int]]:
    """Return counts of identical degree vectors."""
    return Counter(vectors)

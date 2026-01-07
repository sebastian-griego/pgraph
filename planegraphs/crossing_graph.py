"""Crossing graph construction for straight-line segments."""

from __future__ import annotations

from typing import Iterable

from .geometry import Point, proper_segment_intersect


def enumerate_segments(n: int) -> list[tuple[int, int]]:
    """Enumerate all segments (i, j) with i < j."""
    segments: list[tuple[int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            segments.append((i, j))
    return segments


def crossing_graph(points: Iterable[Point]) -> tuple[list[tuple[int, int]], list[int]]:
    """Return (segments, adjacency bitsets) for the crossing graph X(P)."""
    pts = list(points)
    n = len(pts)
    segments = enumerate_segments(n)
    m = len(segments)
    adj = [0] * m
    for s_idx, (i, j) in enumerate(segments):
        for t_idx in range(s_idx + 1, m):
            k, l = segments[t_idx]
            if i == k or i == l or j == k or j == l:
                continue
            if proper_segment_intersect(pts[i], pts[j], pts[k], pts[l]):
                adj[s_idx] |= 1 << t_idx
                adj[t_idx] |= 1 << s_idx
    return segments, adj

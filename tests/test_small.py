from __future__ import annotations

import random

from planegraphs.crossing_graph import enumerate_segments
from planegraphs.geometry import general_position, proper_segment_intersect
from planegraphs.stats import pg


def brute_pg(points: list[tuple[int, int]]) -> int:
    n = len(points)
    segments = enumerate_segments(n)
    m = len(segments)
    count = 0
    for mask in range(1 << m):
        ok = True
        for i in range(m):
            if not (mask >> i) & 1:
                continue
            a, b = segments[i]
            for j in range(i + 1, m):
                if not (mask >> j) & 1:
                    continue
                c, d = segments[j]
                if a == c or a == d or b == c or b == d:
                    continue
                if proper_segment_intersect(points[a], points[b], points[c], points[d]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            count += 1
    return count


def test_triangle_pg():
    points = [(0, 0), (1, 0), (0, 1)]
    assert pg(points) == 8


def test_convex_quadrilateral_pg():
    points = [(0, 0), (2, 0), (2, 1), (0, 1)]
    assert pg(points) == 48


def test_pg_equals_independent_sets_small():
    rng = random.Random(0)
    for n in range(2, 7):
        for _ in range(3):
            pts: list[tuple[int, int]] = []
            while True:
                pts = []
                while len(pts) < n:
                    candidate = (rng.randint(-3, 3), rng.randint(-3, 3))
                    if candidate not in pts:
                        pts.append(candidate)
                if general_position(pts):
                    break
            assert pg(pts) == brute_pg(pts)

"""Basic integer geometry utilities."""

from __future__ import annotations

from typing import Iterable

Point = tuple[int, int]


def orient(a: Point, b: Point, c: Point) -> int:
    """Return the signed area determinant (b-a) x (c-a)."""
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def proper_segment_intersect(a: Point, b: Point, c: Point, d: Point) -> bool:
    """Return True iff segments ab and cd cross in their interiors.

    This excludes intersections at endpoints and collinear overlaps.
    """
    if a == c or a == d or b == c or b == d:
        return False
    o1 = orient(a, b, c)
    o2 = orient(a, b, d)
    o3 = orient(c, d, a)
    o4 = orient(c, d, b)
    if o1 == 0 or o2 == 0 or o3 == 0 or o4 == 0:
        return False
    return (o1 > 0) != (o2 > 0) and (o3 > 0) != (o4 > 0)


def general_position(points: Iterable[Point]) -> bool:
    """Check that no three points are collinear."""
    pts = list(points)
    n = len(pts)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if orient(pts[i], pts[j], pts[k]) == 0:
                    return False
    return True

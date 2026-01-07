"""Local search for point sets with small convex hull."""

from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable

from .geometry import Point, general_position, orient
from .stats import expected_isolated, k_est, pg


def hull_size(points: Iterable[Point]) -> int:
    """Compute convex hull size using Andrew's monotone chain."""
    pts = sorted(set(points))
    if len(pts) <= 1:
        return len(pts)

    def cross(o: Point, a: Point, b: Point) -> int:
        return orient(o, a, b)

    lower: list[Point] = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)

    upper: list[Point] = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)

    hull = lower[:-1] + upper[:-1]
    return len(hull)


@dataclass(frozen=True)
class Candidate:
    points: tuple[Point, ...]
    pg: int
    expected_isolated: Fraction
    k_est: Fraction


def _random_points(n: int, rng: random.Random, radius: int) -> list[Point]:
    points: set[Point] = set()
    attempts = 0
    while len(points) < n and attempts < n * 200:
        x = rng.randint(-radius, radius)
        y = rng.randint(-radius, radius)
        points.add((x, y))
        attempts += 1
    if len(points) < n:
        raise RuntimeError("failed to sample enough distinct points")
    pts = list(points)
    rng.shuffle(pts)
    return pts


def _random_point_set(n: int, rng: random.Random, radius: int) -> list[Point]:
    while True:
        pts = _random_points(n, rng, radius)
        if general_position(pts) and hull_size(pts) == 3:
            return pts


def _perturb(points: list[Point], rng: random.Random, radius: int) -> list[Point] | None:
    n = len(points)
    idx = rng.randrange(n)
    for _ in range(200):
        dx = rng.randint(-2, 2)
        dy = rng.randint(-2, 2)
        if dx == 0 and dy == 0:
            continue
        candidate = (points[idx][0] + dx, points[idx][1] + dy)
        if abs(candidate[0]) > radius or abs(candidate[1]) > radius:
            continue
        if candidate in points:
            continue
        new_points = list(points)
        new_points[idx] = candidate
        if general_position(new_points) and hull_size(new_points) == 3:
            return new_points
    return None


def search(
    n: int,
    steps: int = 200,
    seed: int = 0,
    radius: int = 8,
    keep: int = 5,
) -> list[Candidate]:
    rng = random.Random(seed)
    cache: dict[tuple[Point, ...], Candidate] = {}

    def evaluate(points: list[Point]) -> Candidate:
        key = tuple(points)
        if key in cache:
            return cache[key]
        count = pg(points)
        exp_iso = expected_isolated(points)
        kvalue = k_est(points)
        cand = Candidate(points=key, pg=count, expected_isolated=exp_iso, k_est=kvalue)
        cache[key] = cand
        return cand

    current = _random_point_set(n, rng, radius)
    current_cand = evaluate(current)
    best = current_cand
    top: list[Candidate] = [best]

    restart_interval = max(20, steps // 5)
    for step in range(steps):
        proposal = _perturb(current, rng, radius)
        if proposal is None:
            proposal = _random_point_set(n, rng, radius)
        cand = evaluate(proposal)
        if cand.k_est <= current_cand.k_est:
            current = proposal
            current_cand = cand
        if cand.k_est < best.k_est:
            best = cand
        top.append(cand)

        if (step + 1) % restart_interval == 0:
            current = _random_point_set(n, rng, radius)
            current_cand = evaluate(current)

    top.sort(key=lambda c: (c.k_est, -c.pg))
    return top[:keep]

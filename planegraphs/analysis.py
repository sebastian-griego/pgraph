"""Exact point-set analysis reports for plane graph experiments."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable

from .crossing_graph import crossing_graph
from .geometry import Point, general_position
from .search import hull_size
from .stats import isolated_counts, pg
from .triangulations import enumerate_triangulations, get_degrees

DegreeVector = tuple[int, int, int, int, int]


@dataclass(frozen=True)
class PointSetReport:
    points: tuple[Point, ...]
    general_position: bool
    hull_size: int
    segment_count: int
    crossing_count: int
    plane_graph_count: int
    isolated_counts: tuple[int, ...]
    isolated_probabilities: tuple[Fraction, ...]
    expected_isolated: Fraction
    k_estimate: Fraction
    triangulation_count: int | None
    sampled_triangulations: int
    triangulations_truncated: bool
    degree_vector_histogram: tuple[tuple[DegreeVector, int], ...]

    def to_json_dict(self) -> dict[str, object]:
        return {
            "points": [list(point) for point in self.points],
            "n": len(self.points),
            "general_position": self.general_position,
            "hull_size": self.hull_size,
            "segment_count": self.segment_count,
            "crossing_count": self.crossing_count,
            "plane_graph_count": self.plane_graph_count,
            "isolated_counts": list(self.isolated_counts),
            "isolated_probabilities": [fraction_payload(value) for value in self.isolated_probabilities],
            "expected_isolated": fraction_payload(self.expected_isolated),
            "k_estimate": fraction_payload(self.k_estimate),
            "triangulation_count": self.triangulation_count,
            "sampled_triangulations": self.sampled_triangulations,
            "triangulations_truncated": self.triangulations_truncated,
            "degree_vector_histogram": [
                {"vector": list(vector), "count": count}
                for vector, count in self.degree_vector_histogram
            ],
        }

    def to_markdown(self) -> str:
        rows = [
            "# Point-set analysis",
            "",
            f"- Points: `{list(self.points)}`",
            f"- n: `{len(self.points)}`",
            f"- General position: `{self.general_position}`",
            f"- Convex hull size: `{self.hull_size}`",
            f"- Segment count: `{self.segment_count}`",
            f"- Crossing pairs: `{self.crossing_count}`",
            f"- Plane graphs: `{self.plane_graph_count}`",
            f"- Expected isolated vertices: `{format_fraction(self.expected_isolated)}`",
            f"- K estimate: `{format_fraction(self.k_estimate)}`",
            "",
            "## Isolation probabilities",
            "",
            "| vertex | isolated count | probability |",
            "| ---: | ---: | ---: |",
        ]
        for idx, (count, probability) in enumerate(zip(self.isolated_counts, self.isolated_probabilities)):
            rows.append(f"| {idx} | {count} | {format_fraction(probability)} |")

        rows.extend(["", "## Triangulations", ""])
        if self.triangulation_count is None:
            rows.append(
                f"Enumeration was truncated after {self.sampled_triangulations} triangulations."
            )
        else:
            rows.append(f"Exact triangulation count: `{self.triangulation_count}`")

        if self.degree_vector_histogram:
            rows.extend(["", "| degree vector `(v3,v4,v5,v6,vlarge)` | count |", "| --- | ---: |"])
            for vector, count in self.degree_vector_histogram:
                rows.append(f"| `{vector}` | {count} |")
        return "\n".join(rows) + "\n"


def analyze_point_set(
    points: Iterable[Point],
    *,
    max_triangulations: int = 1000,
) -> PointSetReport:
    pts = tuple((int(x), int(y)) for x, y in points)
    if len(set(pts)) != len(pts):
        raise ValueError("point set contains duplicate coordinates")
    if max_triangulations < 0:
        raise ValueError("max_triangulations must be nonnegative")

    segments, crossing_adj = crossing_graph(pts)
    crossing_count = sum(mask.bit_count() for mask in crossing_adj) // 2
    plane_graph_count = pg(pts)
    iso_counts = tuple(isolated_counts(pts))
    iso_probs = tuple(Fraction(count, plane_graph_count) for count in iso_counts)
    exp_iso = sum(iso_probs, Fraction(0, 1))
    k_value = Fraction(len(pts), 1) / exp_iso if exp_iso else Fraction(0, 1)

    triangulations = enumerate_triangulations(pts, max_count=max_triangulations + 1)
    truncated = len(triangulations) > max_triangulations
    sampled = triangulations[:max_triangulations] if truncated else triangulations
    histogram = degree_vector_histogram(pts, sampled)

    return PointSetReport(
        points=pts,
        general_position=general_position(pts),
        hull_size=hull_size(pts),
        segment_count=len(segments),
        crossing_count=crossing_count,
        plane_graph_count=plane_graph_count,
        isolated_counts=iso_counts,
        isolated_probabilities=iso_probs,
        expected_isolated=exp_iso,
        k_estimate=k_value,
        triangulation_count=None if truncated else len(sampled),
        sampled_triangulations=len(sampled),
        triangulations_truncated=truncated,
        degree_vector_histogram=tuple(sorted(histogram.items())),
    )


def degree_vector_histogram(
    points: Iterable[Point],
    triangulations: Iterable[list[tuple[int, int]]],
) -> Counter[DegreeVector]:
    pts = list(points)
    histogram: Counter[DegreeVector] = Counter()
    for edges in triangulations:
        degrees = get_degrees(pts, edges)
        vector = (
            sum(1 for degree in degrees if degree == 3),
            sum(1 for degree in degrees if degree == 4),
            sum(1 for degree in degrees if degree == 5),
            sum(1 for degree in degrees if degree == 6),
            sum(1 for degree in degrees if degree >= 7),
        )
        histogram[vector] += 1
    return histogram


def fraction_payload(value: Fraction) -> dict[str, object]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal": float(value),
    }


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"

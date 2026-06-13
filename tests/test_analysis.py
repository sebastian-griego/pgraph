from __future__ import annotations

from fractions import Fraction
import json
import subprocess
import sys

from planegraphs.analysis import analyze_point_set


def test_analyze_triangle_exact_report():
    report = analyze_point_set([(0, 0), (1, 0), (0, 1)])

    assert report.general_position is True
    assert report.hull_size == 3
    assert report.segment_count == 3
    assert report.crossing_count == 0
    assert report.plane_graph_count == 8
    assert report.isolated_counts == (2, 2, 2)
    assert report.isolated_probabilities == (Fraction(1, 4), Fraction(1, 4), Fraction(1, 4))
    assert report.expected_isolated == Fraction(3, 4)
    assert report.k_estimate == Fraction(4, 1)
    assert report.triangulation_count == 1
    assert report.triangulations_truncated is False
    assert report.degree_vector_histogram == (((0, 0, 0, 0, 0), 1),)

    payload = report.to_json_dict()
    assert payload["expected_isolated"] == {"numerator": 3, "denominator": 4, "decimal": 0.75}
    assert payload["k_estimate"] == {"numerator": 4, "denominator": 1, "decimal": 4.0}


def test_analyze_point_set_marks_truncated_triangulations():
    points = [(0, 0), (10, 0), (15, 8), (5, 15), (-5, 8)]
    report = analyze_point_set(points, max_triangulations=2)

    assert report.triangulation_count is None
    assert report.sampled_triangulations == 2
    assert report.triangulations_truncated is True
    assert sum(count for _, count in report.degree_vector_histogram) == 2


def test_analyze_point_set_cli_json_and_markdown(tmp_path):
    json_out = tmp_path / "report.json"
    subprocess.run(
        [
            sys.executable,
            "scripts/analyze_point_set.py",
            "--points",
            "[[0,0],[1,0],[0,1]]",
            "--out",
            str(json_out),
        ],
        check=True,
    )
    payload = json.loads(json_out.read_text(encoding="utf-8"))
    assert payload["plane_graph_count"] == 8
    assert payload["k_estimate"]["numerator"] == 4

    markdown_out = tmp_path / "report.md"
    subprocess.run(
        [
            sys.executable,
            "scripts/analyze_point_set.py",
            "--points",
            "[[0,0],[1,0],[0,1]]",
            "--format",
            "markdown",
            "--out",
            str(markdown_out),
        ],
        check=True,
    )
    text = markdown_out.read_text(encoding="utf-8")
    assert "# Point-set analysis" in text
    assert "Plane graphs: `8`" in text

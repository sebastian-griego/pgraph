import random

from planegraphs.triangulations import (
    enumerate_triangulations,
    random_triangulation,
    triangulation_degree_vectors,
)


def test_triangulation_degree_vectors_n4():
    points = [(0, 0), (2, 0), (0, 2), (1, 1)]
    vectors = triangulation_degree_vectors(points)
    assert vectors == [(4, 0, 0, 0, 0)]


def test_convex_triangulations():
    points = [(0, 0), (10, 0), (15, 8), (5, 15), (-5, 8)]
    tris = enumerate_triangulations(points)
    assert len(tris) == 5


def test_small_interior():
    points = [(0, 0), (10, 0), (5, 10), (5, 2)]
    tris = enumerate_triangulations(points)
    assert len(tris) == 1

    points_2 = [(0, 0), (10, 0), (5, 10), (5, 2), (5, 4)]
    tris_2 = enumerate_triangulations(points_2)
    assert len(tris_2) >= 1


def test_random_triangulation_edges():
    points = [(0, 0), (2, 0), (0, 2), (1, 1)]
    edges = random_triangulation(points, random.Random(0))
    assert len(edges) == 6

from planegraphs.triangulations import triangulation_degree_vectors


def test_triangulation_degree_vectors_n4():
    points = [(0, 0), (2, 0), (0, 2), (1, 1)]
    vectors = triangulation_degree_vectors(points)
    assert vectors == [(4, 0, 0, 0, 0)]

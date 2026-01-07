"""Exact independent set counting for graphs with bitset adjacency."""

from __future__ import annotations

from typing import Iterable


def _iter_bits(mask: int) -> Iterable[int]:
    while mask:
        lsb = mask & -mask
        yield lsb.bit_length() - 1
        mask ^= lsb


class IndepCounter:
    def __init__(self, adj: list[int]):
        self.adj = adj
        self.n = len(adj)
        self.memo: dict[int, int] = {}

    def count(self, mask: int | None = None) -> int:
        if mask is None:
            mask = (1 << self.n) - 1
        return self._count(mask)

    def _count(self, mask: int) -> int:
        if mask == 0:
            return 1
        if mask in self.memo:
            return self.memo[mask]

        # Factor out isolated vertices.
        iso_mask = 0
        m = mask
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            if self.adj[v] & mask == 0:
                iso_mask |= lsb
            m ^= lsb
        if iso_mask:
            res = (1 << iso_mask.bit_count()) * self._count(mask ^ iso_mask)
            self.memo[mask] = res
            return res

        # Factor across connected components.
        comp = self._component(mask)
        if comp != mask:
            res = self._count(comp) * self._count(mask ^ comp)
            self.memo[mask] = res
            return res

        # Branch on a high-degree vertex.
        v = self._choose_vertex(mask)
        without_v = mask & ~(1 << v)
        res = self._count(without_v) + self._count(without_v & ~self.adj[v])
        self.memo[mask] = res
        return res

    def _choose_vertex(self, mask: int) -> int:
        best_v = -1
        best_deg = -1
        m = mask
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            deg = (self.adj[v] & mask).bit_count()
            if deg > best_deg:
                best_deg = deg
                best_v = v
            m ^= lsb
        return best_v

    def _component(self, mask: int) -> int:
        lsb = mask & -mask
        comp = 0
        frontier = lsb
        while frontier:
            comp |= frontier
            neigh = 0
            temp = frontier
            while temp:
                l2 = temp & -temp
                u = l2.bit_length() - 1
                neigh |= self.adj[u]
                temp ^= l2
            frontier = (neigh & mask) & ~comp
        return comp


def indepcount(adj: list[int]) -> int:
    """Return the number of independent sets in a graph."""
    return IndepCounter(adj).count()

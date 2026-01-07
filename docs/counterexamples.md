Counterexamples
================

The bound (243/20)^n is false as stated. A concrete counterexample is the
triangle with integer coordinates (0,0), (1,0), (0,1); it has pg(P)=8, so
pg(P) < (243/20)^3 and pg(P) < (583/25)^3.

Reproduce by running:
  python scripts/check_bound.py --max-n 3 --radius 1

Lean verification of pg(P)=8 and the inequalities is in:
  Lean/PlaneGraphs/Counterexample.lean

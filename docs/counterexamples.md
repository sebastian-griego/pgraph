Counterexamples
================

The bound (243/20)^n is false as stated. A concrete counterexample is the
triangle with integer coordinates (0,0), (1,0), (0,1); it has pg(P)=8, so
pg(P) < (243/20)^3 and pg(P) < (583/25)^3.

Reproduce by running:
  python scripts/check_bound.py --max-n 3 --radius 1

For asymptotic or shifted statements, use `--nmin` (alias of `--min-n`) and
the shifted/prefactor modes, e.g.:
  python scripts/check_bound.py --bound 112/11 --nmin 6 --shifted

Lean verification of pg(P)=8 and the inequalities is in:
  Lean/PlaneGraphs/Counterexample.lean

Asymptotic statements in Lean are in:
  Lean/Main.lean (see the `main_lower_bound_deg34_*` theorems).

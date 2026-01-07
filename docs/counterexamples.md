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

Degree-balance counterexamples
------------------------------

The deg56 balance/linear inequalities used in the sample pipeline are not valid
for all hull-3 triangulations. A concrete triangulation on n=11 points violates
`45*v3 + 21*v4 + 9*v5 + 3*v6 ≤ 25*n`. The witness is stored at:
  data/deg56_balance_counterexample.json

You can reproduce with:
  python scripts/find_balance_counterexample.py --n-min 11 --n-max 11 --samples 200 \
    --triangulations 400 --seed 123 --out data/deg56_balance_counterexample.json

On the expanded mined dataset, the same inequality holds for all sampled
vectors with n >= 12 (see `deg56FastVectorsN12_balance` in
`Lean/PlaneGraphs/DegreeVectors.lean`), so n=11 is the only data counterexample
currently known.

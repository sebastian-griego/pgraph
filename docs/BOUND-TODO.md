Bound Upgrade TODO
==================

This repo currently proves asymptotic lower bounds using the deg34 charging step
and the derived constant K = 112/11. To upgrade K, only the following needs to
change.

Single lemma to strengthen
--------------------------
- `Lean/PlaneGraphs/Charging.lean`: the lemmas `avgIso_le_deg34_bound` and
  `avgIso_le_deg34_bound_cert` (which goes through the JSON certificate) are the
  final numeric inequalities that plug into the asymptotic framework.
  Strengthen them by proving a tighter bound of the form

  avgIso(P) ≤ n / K'

  with a larger K'. All other asymptotic lemmas will accept the new K' without
  modification.
  The main entry points that consume this are:
  - `Lean/Main.lean`: `main_lower_bound_deg34_from_deg34`
  - `Lean/Main.lean`: `main_lower_bound_deg34_prefactor_from_deg34`
  - `Lean/Main.lean`: `main_lower_bound_deg34_cert`
  - `Lean/Main.lean`: `main_lower_bound_deg34_prefactor_cert`

Certificate shape
-----------------
- JSON file under `certificates/` with this shape:

  {
    "constants": {
      "K_deg34": [numerator, denominator]
    }
  }

- Export using:

  python scripts/export_certificate.py --out certificates/your-cert.json \
    --const K_deg34=NUM/DEN

Then in Lean, update `exampleCertificate` or add a new certificate and replace
uses of `K_deg34` accordingly.

Re-run + rebuild
----------------
1) Generate or update the certificate JSON.
2) Update the lemmas in `Lean/PlaneGraphs/Certificate.lean` that read the
   certificate (e.g., `exampleCertificate_getQ_deg34`).
3) Rebuild:

   lake build

4) Re-check counterexample search with a higher `--nmin` using

   python scripts/check_bound.py --bound NUM/DEN --nmin N --shifted

Helper tooling
--------------
- `scripts/optimize_charging.py` solves the deg34 LP exactly for a range of `n`
  and reports the worst-case charge and implied K. This is a good baseline
  when experimenting with stronger constraints or additional degree buckets.
- The same script accepts a custom LP in JSON via `--constraints`, with linear
  expressions in `n` of the form `a*n+b` (rational `a,b`). The schema is:

  {
    "variables": ["v3", "v4", "vlarge"],
    "objective": ["1/8", "1/16", "1/32"],
    "equalities": [
      {"coeffs": ["1", "1", "1"], "rhs": "n"}
    ],
    "inequalities": [
      {"coeffs": ["-1", "0", "0"], "rhs": "0"},
      {"coeffs": ["0", "-1", "0"], "rhs": "0"},
      {"coeffs": ["0", "0", "-1"], "rhs": "0"},
      {"coeffs": ["9", "1/2", "0"], "rhs": "6*n-6"}
    ]
  }

  Run it with:

  python scripts/optimize_charging.py --constraints path/to/lp.json --min-n 5 --max-n 20

  Example file:

  docs/lp/deg34.json
  docs/lp/deg56.json
  docs/lp/deg56_shift.json

- `scripts/mine_degree_vectors.py` enumerates triangulations for sampled point
  sets and writes degree vectors to JSON. Use `--append` to grow the dataset or
  `--random-triangulations` to sample greedy maximal triangulations. Use
  `--max-time` to cap long runs.
- `scripts/optimize_weights.py` uses SciPy to fit charging weights (and a linear
  bound `a*n+b`) against the sampled vectors. By default the weights are fixed
  at their visibility bounds; pass `--free-weights` to let them vary.
- `scripts/solve_rational.py` runs a float LP and then computes the exact
  rational K for the mined vectors, emitting the command to generate a JSON
  certificate. Use `--min-n` to explore shifted bounds when small-n vectors
  dominate the maximum.
- `scripts/search_degree_inequalities.py` searches mined vectors for candidate
  linear constraints to justify new charging bounds.
- `certificates/deg56_sample.json` is a data-driven sample certificate created
  from mined vectors; it is not a proven bound yet.
- `certificates/deg56_shift_sample.json` is the shifted (n≥9) sample certificate
  with `K_deg56_shift = 192/13`; it uses the same fixed weights.
- `certificates/deg56_n12_sample.json` is the fixed-weight sample certificate
  for the expanded dataset with `n≥12`, giving `K_deg56_n12 = 512/37`.
- A smaller-coefficient inequality that matches the `n≥12` sample data is:

  15*v3 + 7*v4 + 3*v5 + v6 ≤ 8*n + 3

  This holds for all vectors in `data/degree_vectors_new.json` with `n≥12`
  (see `deg56FastVectorsN12_linear8_forall` in
  `Lean/PlaneGraphs/DegreeVectors.lean`). In Lean, this inequality implies
  the `K_deg56_n12` charge bound once `n≥12` (see
  `avgIso_le_deg56_n12_of_linear8` in `Lean/PlaneGraphs/Charging.lean`).
- `Lean/PlaneGraphs/DegreeVectors.lean` loads `data/degree_vectors.json` and
  proves (by computation) that both the unshifted and shifted certificate
  inequalities hold for every mined vector (shifted restricted to `n ≥ 9`).
  This is a Lean-checked data validation step, not yet a geometric proof.
- `Lean/PlaneGraphs/DegreeVectors.lean` now also derives the shifted
  `sumLarge` inequality for every mined vector via
  `deg56ShiftBalance_iff_sumLarge` and `deg56ShiftVectors_sumLarge`, so the
  data check matches the new shifted `sumLarge` target directly.
- `Lean/PlaneGraphs/DegreeVectors.lean` also converts that check into the
  explicit balance inequality above (`deg56ShiftVectors_balance_forall`), so
  the remaining task is to prove that balance for all hull-3 triangulations.
- `Lean/PlaneGraphs/Charging.lean` now includes
  `charge_bound_deg56_shift_iff`, which shows the deg56-shift bound is
  equivalent to the linear inequality:

  22*v3 ≤ 2*v4 + 14*v5 + 20*v6 + 23*vL

  This isolates the exact degree-balance statement that still needs a
  geometric proof for hull-3 triangulations (for n≥9).
- `Lean/PlaneGraphs/Charging.lean` also includes `charge_bound_deg56_iff` for
  the unshifted constant `K_deg56 = 96/7`, which is equivalent to:

  20*v3 ≤ 4*v4 + 16*v5 + 22*v6 + 25*vL

  This is the balance inequality enforced by the fixed weights on the full
  mined dataset (all n), and it is the exact statement that replaces the
  deg34 `v4`-bound in a future proof.
- `Lean/PlaneGraphs/Charging.lean` includes
  `avgIso_le_deg56_shift_of_balance`, which turns that balance inequality
  plus the weighted charging bound into `avgIso ≤ n / K_deg56_shift_sample`.
- `Lean/PlaneGraphs/DegreeCounts.lean` now contains degree-count utilities
  and the Euler-style inequality

  12 ≤ 3*v3 + 2*v4 + v5 - vL

  under the assumptions `G.card = 3*n - 6` and `v3+v4+v5+v6+vL = n`.
  This is the first formal bridge from edge counts to degree-balance.
- `Lean/PlaneGraphs/DegreeCounts.lean` also proves that if all vertex degrees
  are at least 3, then `v3+v4+v5+v6+vL = n` (and its ℚ coercion), so the
  remaining missing ingredient for the Euler balance is a Lean proof that
  hull-3 triangulations have min degree ≥ 3.
- `Lean/PlaneGraphs/DegreeCounts.lean` now tracks `sumLarge` (the sum of
  degrees for vertices with degree ≥ 7) and proves `degreeSum_ge_split`,
  which will be useful when replacing the coarse `7*vL` bound with a sharper
  constraint in the eventual discharging proof.
- `Lean/PlaneGraphs/DegreeCounts.lean` adds `degreeSum_eq_split` (under min
  degree ≥ 3) and `sumLarge_eq_q`, which rewrites `sumLarge` as

  3*v3 + 2*v4 + v5 + 6*vL - 12

  once `G.card = 3*n - 6` and `v3+v4+v5+v6+vL = n`. This isolates the “excess
  large degree” term that needs to be strengthened by a new geometric lemma.
- `Lean/PlaneGraphs/DegreeCounts.lean` also shows `7*vL ≤ sumLarge` and
  packages an Euler bound directly from the `sumLarge` identity via
  `euler_balance_lower_of_sumLarge`, making the dependence on large-degree
  vertices explicit.
- `Lean/PlaneGraphs/DegreeCounts.lean` now has `deg56_balance_iff_sumLarge`
  and `deg56_balance_of_sumLarge`, which reduce the deg56 balance inequality
  to a single lower bound on `sumLarge`:

  sumLarge ≥ 23*v3 - 2*v4 - 15*v5 - 22*v6 - 19*vL - 12

  So the remaining geometric work is exactly to prove this lower bound for
  hull-3 triangulations (plus min degree ≥3 and the edge count).
- `Lean/PlaneGraphs/DegreeCounts.lean` now also has
  `deg56_shift_balance_iff_sumLarge`, which reduces the shifted balance
  inequality `22*v3 ≤ 2*v4 + 14*v5 + 20*v6 + 23*vL` to:

  sumLarge ≥ 25*v3 - 13*v5 - 20*v6 - 17*vL - 12

  This gives a parallel “sumLarge” target for the shifted constant.
- `Lean/PlaneGraphs/DegreeCounts.lean` also rewrites the balance inequalities
  into linear bounds in n (eliminating vL):

  20*v3 ≤ 4*v4 + 16*v5 + 22*v6 + 25*vL  ↔  45*v3 + 21*v4 + 9*v5 + 3*v6 ≤ 25*n
  22*v3 ≤ 2*v4 + 14*v5 + 20*v6 + 23*vL  ↔  45*v3 + 21*v4 + 9*v5 + 3*v6 ≤ 23*n

  These are sometimes easier to target in a discharging proof.
- `Lean/PlaneGraphs/DegreeVectors.lean` now checks these linear bounds on the
  mined datasets via `deg56SampleVectors_linear_forall`,
  `deg56FastVectors_linear_forall`, and `deg56ShiftVectors_linear_forall`.
- `Lean/PlaneGraphs/Charging.lean` includes
  `avgIso_le_deg56_of_sumLarge`, and `Lean/Main.lean` includes
  `main_lower_bound_deg56_sumLarge`, so once the `sumLarge` inequality is
  proved for triangulations the asymptotic lower bound follows directly.
- `Lean/PlaneGraphs/Charging.lean` includes
  `avgIso_le_deg56_shift_of_sumLarge`, and `Lean/Main.lean` includes
  `main_lower_bound_deg56_shift_sumLarge`, so the shifted bound can be
  derived from the shifted `sumLarge` inequality in the same way.
- `Lean/PlaneGraphs/Charging.lean` now also includes
  `avgIso_le_deg56_of_linear` and `avgIso_le_deg56_shift_of_linear`, and
  `Lean/Main.lean` adds `main_lower_bound_deg56_linear` and
  `main_lower_bound_deg56_shift_linear`. These accept the linear forms
  directly and avoid explicit `sumLarge`.
- `Lean/PlaneGraphs/DegreeCounts.lean` adds
  `deg56_balance_of_sumLarge_graph`, which discharges the `v3+...=n` step
  using `v_sum_eq_n_q`, so the graph-level assumptions reduce to:
  edge count `G.card = 3*n - 6`, min degree ≥3, and the `sumLarge` lower bound.
- `Lean/Main.lean` includes `main_lower_bound_deg56_shift_balance`, so once
  the balance inequality is proved for all relevant triangulations the
  asymptotic lower bound follows without further changes.
- `Lean/Main.lean` includes `main_lower_bound_deg56_sample*` and
  `main_lower_bound_deg56_shift_sample*` entry points that accept hypothetical
  `avgIso` bounds for the corresponding sample constants.
- With the expanded mined vectors up to `n=14`, the fixed-weight worst case
  appears at `n=11` with `(v3,v4,v5,v6,vL)=(6,0,0,2,3)`, so the data no longer
  supports the older shifted bound `K=192/13`. For `n≥12`, the worst case in
  the data is `(6,1,0,2,3)` with `K=512/37`. Any Lean proof that excludes the
  `n=11` pattern for large `n` or proves a stronger global inequality will move
  the asymptotic base.
- `data/degree_vectors_new.json` is a fast-run dataset (currently n=6..14, random
  triangulations, 1496 unique vectors). It contains counterexamples to the
  deg56 balance/linear inequalities; see `data/deg56_balance_counterexample.json`
  for an explicit hull-3 triangulation with `v3=6,v6=2,vL=3` (n=11) where
  `45*v3 + 21*v4 + 9*v5 + 3*v6 = 276 > 25*n`. On the same dataset, the balance
  inequality holds for all sampled vectors with `n ≥ 12` (see
  `deg56FastVectorsN12_balance` in `Lean/PlaneGraphs/DegreeVectors.lean`).
- `scripts/find_balance_counterexample.py` searches for explicit triangulations
  that violate the deg56 balance/linear inequalities and writes a JSON witness.
- `scripts/optimize_weights.py` now supports `--fix-w3` and `--normalize-sum`
  to avoid the degenerate free-weight solution `w4=w5=w6=wL=0`. On the current
  datasets, `--fix-w3 1/8` drives K to 16 (data-only artifact), while
  `--normalize-sum 31/128` recovers the fixed-weight bound `K=96/7`.

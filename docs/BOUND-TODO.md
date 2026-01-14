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
  Use `--show-tight` to list the tight inequalities at the optimum; this is a
  quick proxy for the dual witness when deciding which constraint to
  strengthen. If your LP JSON includes `label` fields, they will be printed.
  Use `--show-min-tight` to print only the tight constraints at the worst n
  (the min-K solution) across the range.
  Use `--min-k-only` to suppress per-n output when scanning large ranges.
  Use `--quiet` to suppress the header and per-n rows.
  Use `--min-k-json` to write the min-K solution and its tight constraints.
  Use `--min-k-slack K` to show the K smallest slacks at the min-K solution
  and include them in `--min-k-json`.
  Use `--min-k-slack-all` to include all slacks (sorted) for the min-K row.
  Use `--quiet-slacks` to suppress the slack list.
  Use `--quiet-min-k` to suppress the min-K line.
  Use `--quiet-all` to enable all quiet flags at once.
  `--quiet` also suppresses the certificate write message.
  Use `--tight-summary` to aggregate tight constraints across the n-range, or
  `--tight-summary-json` to write that summary to a file.
- `scripts/compare_tight_summaries.py` compares two summary outputs and reports
  which constraints became more or less tight. Use `--mode summary` for
  `--tight-summary-json` outputs, or `--mode min-k` for `--min-k-json` outputs.
  Use `--key label` or `--key index` to compare by label or index instead of
  the constraint string. Use `--min-delta` to filter out small changes.
  Use `--print-keys` to list the keys that would be compared.
- `scripts/check_sumlarge_bound.py` validates a proposed sumLarge lower bound
  on the mined vectors (useful for quick data checks before formalizing). Use
  `--out` to write a JSON summary with the worst margin and sample witnesses.
  Use `--stop-after-examples` to stop once enough counterexamples are shown.
  Use `--max-checked` to cap the number of vectors scanned. Use `--shuffle`
  (with `--seed`) to randomize the scan order for quick spot checks.
  Use `--summary-only` to suppress per-example output.
- `scripts/check_linear_bound.py` validates linear inequalities of the form
  `a*v3 + b*v4 + c*v5 + d*v6 + e*vL ≤ f*n+g` (or the reverse). Use `--rhs` for
  the right-hand side expression and `--direction ge` to flip the inequality.
- The same script accepts a custom LP in JSON via `--constraints`, with linear
  expressions in `n` of the form `a*n+b` (rational `a,b`). The schema is:

  {
    "variables": ["v3", "v4", "vlarge"],
    "objective": ["1/8", "1/16", "1/32"],
    "equalities": [
      {"coeffs": ["1", "1", "1"], "rhs": "n", "label": "partition"}
    ],
    "inequalities": [
      {"coeffs": ["-1", "0", "0"], "rhs": "0", "label": "nonneg_v3"},
      {"coeffs": ["0", "-1", "0"], "rhs": "0", "label": "nonneg_v4"},
      {"coeffs": ["0", "0", "-1"], "rhs": "0", "label": "nonneg_vlarge"},
      {"coeffs": ["9", "1/2", "0"], "rhs": "6*n-6", "label": "deg34_bound"}
    ]
  }

  Run it with:

  python scripts/optimize_charging.py --constraints path/to/lp.json --min-n 5 --max-n 20

  Example file:

  docs/lp/deg34.json
  docs/lp/deg56.json
  docs/lp/deg56_shift.json
  docs/lp/deg56_n12.json
  docs/lp/deg56_sumlarge.json
  docs/lp/deg56_shift_sumlarge.json

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
  `Lean/PlaneGraphs/DegreeVectors.lean`). The current dataset has 2844 vectors
  up to `n=18`, and the bound is tight at `n=12` for `(v3,v4,v5,v6,vL) =
  (6,1,0,2,3)`. In Lean, this inequality implies the `K_deg56_n12` charge
  bound once `n≥12` (see
  `avgIso_le_deg56_n12_of_linear8` in `Lean/PlaneGraphs/Charging.lean`).
  The corresponding LP template is `docs/lp/deg56_n12.json`; use it with
  `scripts/optimize_charging.py --constraints docs/lp/deg56_n12.json --min-n 12`.
- The same inequality is equivalent to a `sumLarge` lower bound:

  4*sumLarge ≥ 33*v3 + 5*v4 − 11*v5 − 21*v6 − 57

  This is derived by eliminating `vL` using
  `sumLarge = 3*v3 + 2*v4 + v5 + 6*vL − 12`; see
  `deg56_linear8_iff_sumLarge` in `Lean/PlaneGraphs/DegreeCounts.lean`.
  The graph-level wrapper is `deg56_linear8_of_sumLarge_graph`, and the
  charging path is `avgIso_le_deg56_n12_of_sumLarge` in
  `Lean/PlaneGraphs/Charging.lean`.
- The same bound is also equivalent to a simpler balance inequality:

  7*v3 ≤ v4 + 5*v5 + 7*v6 + 8*vL + 3

  This follows from `v3+v4+v5+v6+vL = n` via
  `deg56_linear8_iff_balance_simple` in `Lean/PlaneGraphs/DegreeCounts.lean`.
  The graph-level version is `deg56_balance_simple_graph`.
- `Lean/PlaneGraphs/Hull3Balance.lean` now states the missing geometric
  lemma as a `sumLarge` lower bound (`deg56_sumLarge_hull3` for `n ≥ 12`),
  and derives `deg56_balance_simple_hull3`/`deg56_linear8_hull3_graph`
  from it. This isolates the exact combinatorial gap that still needs a
  real triangulation proof in Lean, without relying on mined vector
  completeness.
- `Lean/PlaneGraphs/DegreeCounts.lean` now includes a discharging scaffold:
  `netTransfer`, `sum_balanceTerm_ge_of_transfer`, and
  `deg56_sumLarge_of_transfer` show how to turn local per-vertex balance
  bounds plus an antisymmetric transfer into the global `sumLarge` inequality.
  The wrapper `deg56_sumLarge_hull3_of_transfer` in
  `Lean/PlaneGraphs/Hull3Balance.lean` is the entry point for a future
  discharging proof that replaces the current axiom.
- A candidate edge-based transfer scheme is defined in
  `Lean/PlaneGraphs/DegreeCounts.lean` as `transferDeg56Base`/`transferDeg56`.
  The lemmas `netTransfer_deg3_eq`, `netTransfer_deg4_eq`,
  `netTransfer_deg5_eq`, and `netTransfer_deg6_eq` compute the net transfer
  for low-degree vertices in terms of high-degree neighbors, so the next step
  is to add per-vertex lower bounds and verify the local inequalities needed
  by `deg56_sumLarge_hull3_of_transfer`. The lemmas
  `deg56BalanceTerm_transfer_ge_deg3/4/5/6` now provide those lower bounds
  assuming a nonnegative transfer coefficient and a lower bound on the
  high-degree neighbor count.
- The helper count `adjacentLargeCountQ` now uses the strict adjacency
  relation `adjacent` (which enforces `u ≠ v`), and a general
  `adjacentDegCountQ` is available for degree‑specific neighbor counts.
  For large vertices, `netTransfer_deg_ge7_eq_neg_sum_base` expresses the
  net transfer as the negative sum of incoming base transfers.
- The adjacency API now includes `adjacent_self_false`, `segment_eq_of_incident`,
  and `adjacent_iff_edge`, which will be useful for counting neighbor
  contributions via edges.
- `Lean/PlaneGraphs/Hull3Balance.lean` also derives an equivalent
  `sumLargeExcess` form (`deg56_sumLarge_hull3_excess`), which packages
  the bound in terms of excess large-degree over 7. This is a convenient
  target if you want to prove the inequality by discharging on large
  vertices instead of using `sumLarge` directly.
- `Lean/PlaneGraphs/DegreeCounts.lean` now includes a per-vertex “debt”
  bookkeeping (`deg56Debt`) and the equivalence
  `deg56_sumLarge_iff_excess_debt`, which rewrites the target inequality as
  `sumLargeExcess + 57/4 ≥ ∑ deg56Debt`. This is the exact shape needed for
  a discharging proof (excess on large vertices pays debt on low-degree
  vertices, with a small constant slack).
- `Lean/PlaneGraphs/DegreeCounts.lean` also defines `deg56Excess` and
  `deg56BalanceTerm`, plus `deg56_sumLarge_iff_balance_terms`, which reduces
  the target to `∑ balanceTerm ≥ -57/4`. This is the most local form of the
  inequality and should be the target for any per-vertex discharging proof.
- The shifted sumLarge lower bound is **not** supported by the current mined
  dataset. See `data/deg56_shift_sumlarge_counterexample.json` for concrete
  counterexamples (the worst margin occurs at `n=11` with `(v3,v4,v5,v6,vL) =
  (6,0,0,2,3)`). The expanded dataset (now up to `n=18`) also violates the
  shifted linear inequality for `n≥12`; for example, `n=14` with
  `(v3,v4,v5,v6,vL) = (7,1,1,0,5)` gives margin `-23`. Until a stronger
  geometric restriction is found, the
  shifted `K=192/13` bound should be treated as experimental and should not
  be used as a general hull-3 theorem.
- `Lean/PlaneGraphs/DegreeVectors.lean` loads `data/degree_vectors.json` and
  proves (by computation) that both the unshifted and shifted certificate
  inequalities hold for every mined vector (shifted restricted to `n ≥ 9`).
  This is a Lean-checked data validation step, not yet a geometric proof.
- `Lean/PlaneGraphs/DegreeVectors.lean` now also derives the shifted
  `sumLarge` inequality for every mined vector via
  `deg56ShiftBalance_iff_sumLarge` and `deg56ShiftVectors_sumLarge`, so the
  data check matches the new shifted `sumLarge` target directly.
- `Lean/PlaneGraphs/DegreeVectors.lean` also converts that check into the
  explicit balance inequality above (`deg56ShiftVectors_balance_forall`), but
  the expanded dataset shows this inequality fails for some hull-3
  triangulations when `n ≥ 9`, so it cannot be the basis of a general proof.
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
  The LP template `docs/lp/deg56_sumlarge.json` encodes this bound along with
  a `sumLarge` variable so you can see the implied K immediately.
- `Lean/PlaneGraphs/DegreeCounts.lean` now also has
  `deg56_shift_balance_iff_sumLarge`, which reduces the shifted balance
  inequality `22*v3 ≤ 2*v4 + 14*v5 + 20*v6 + 23*vL` to:

  sumLarge ≥ 25*v3 - 13*v5 - 20*v6 - 17*vL - 12

  This gives a parallel “sumLarge” target for the shifted constant.
  The LP template `docs/lp/deg56_shift_sumlarge.json` encodes this bound
  alongside the shifted constraints.
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
- `Lean/PlaneGraphs/Charging.lean` also adds
  `avgIso_le_deg56_n12_of_balance_simple`, and `Lean/Main.lean` adds
  `main_lower_bound_deg56_n12_balance_simple`, wiring `K_deg56_n12` once the
  simple balance inequality is available for `n ≥ 12`.
- `Lean/PlaneGraphs/Hull3Balance.lean` now defines the charging scheme from the
  paper: `deg56_charge P G = ∑_u 1/2^{potential(P,G,u)}` where the potential
  is degree plus visibility. Conservation is still an axiom
  (`deg56_charge_conserve`), and the per‑graph bound is now
  `deg56_charge_upper_hull3` (with `potential_ge_degree_hull3` left as the
  geometric hook for the future proof). The lemma `deg56_charge_hull3` derives
  the `avgIso` bound from these.
- `Lean/PlaneGraphs/Hull3Balance.lean` now has a `Hull3Triangulation` record
  (hull size = 3, edges, edge count, min degree) and threads it through the
  hull‑3 axioms so the remaining geometric assumptions are centralized and
  explicit.
- `Lean/PlaneGraphs/Charging.lean` keeps `avgIso_le_of_charge_bound` as a
  reusable bridge from per‑graph charge bounds to `avgIso` bounds, even though
  the hull‑3 path now expects the charging inequality directly.
- `Lean/PlaneGraphs/Hull3Balance.lean` also includes
  `hull3_triangulation_exists` (existence of a hull‑3 triangulation with
  `3*n-6` edges and min degree ≥3). This provides the triangulation needed
  by the charge upper bound and balance inequality.
- `Lean/Main.lean` now includes
  `main_lower_bound_deg56_n12_hull3_class`, which upgrades any class of
  point sets with hull size exactly 3 (and the standard delete closure) to
  the `K_deg56_n12` lower bound using `deg56_charge_hull3`.
- `Lean/PlaneGraphs/Hull3Balance.lean` also adds
  `avgIso_le_deg56_n12_hull3_charge`, which packages the hull‑3 axioms plus
  `deg56_charge_hull3` into the final `avgIso ≤ n / K_deg56_n12` bound used by
  `main_lower_bound_deg56_n12_hull3_class`.
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
- With the expanded mined vectors up to `n=16`, the fixed-weight worst case
  appears at `n=11` with `(v3,v4,v5,v6,vL)=(6,0,0,2,3)`, so the data no longer
  supports the older shifted bound `K=192/13`. For `n≥12`, the worst case in
  the data is `(6,1,0,2,3)` with `K=512/37` (confirmed by
  `scripts/solve_rational.py --min-n 12`). Any Lean proof that excludes the
  `n=11` pattern for large `n` or proves a stronger global inequality will move
  the asymptotic base.
- `data/degree_vectors_new.json` is a fast-run dataset (currently n=6..16, random
  triangulations, 1958 unique vectors). It contains counterexamples to the
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

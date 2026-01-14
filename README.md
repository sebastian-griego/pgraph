# pgraph

Plane graph counting toolkit + Lean formalization.

Quick checks
------------
- Python tests: `pytest -q`
- Lean build: `lake build`

Python tooling
--------------
- `scripts/find_extremal.py`: local search for hull size 3 point sets (supports
  multiple seeds via `--seeds`).
- `scripts/check_bound.py`: counterexample search; supports `--nmin`, `--shifted`,
  and `--prefactor` for asymptotic forms.
- `scripts/export_certificate.py`: export rational constants as JSON.
- `scripts/optimize_charging.py`: exact LP solver for charging bounds (deg34 or a
  JSON-specified LP).
- `scripts/mine_degree_vectors.py`: enumerate triangulations for small point
  sets and collect degree vectors (use `--append` to merge with an existing
  dataset, or `--random-triangulations` to sample greedily, plus `--max-time`
  to cap long runs).
- `scripts/optimize_weights.py`: use SciPy to fit a bound `a*n+b` against sampled
  degree vectors (weights fixed by default; use `--free-weights` to vary them).
- `scripts/solve_rational.py`: solve the weight LP and snap-fit an exact rational
  certificate for the mined degree vectors (supports `--min-n/--max-n` to
  explore shifted bounds).
- `scripts/search_degree_inequalities.py`: search for simple linear inequalities
  satisfied by mined degree vectors, to suggest candidate geometric constraints.
- `scripts/check_linear_bound.py`: validate linear degree inequalities against
  mined vectors (supports sampling and JSON summaries).
- `scripts/check_sumlarge_bound.py`: validate sumLarge lower bounds against
  mined vectors (supports sampling and JSON summaries).

Lean entry points
-----------------
Asymptotic lower bounds are in `Lean/Main.lean`:
- `main_lower_bound_deg34`: shifted bound using explicit K = 112/11.
- `main_lower_bound_deg34_prefactor`: prefactor form using K = 112/11.
- `main_lower_bound_deg34_from_deg34`: derives K = 112/11 from the
  `(11*n - 6)/112` inequality.
- `main_lower_bound_deg34_cert`: same as above but routes through the JSON
  certificate (`certificates/example.json`).
- `main_lower_bound_deg56_n12_hull3_class`: hull‑3 conditional bound using
  `K_deg56_n12 = 512/37` (requires the hull‑3 charging axioms in
  `Lean/PlaneGraphs/Hull3Balance.lean`).

Counterexamples
---------------
Exact small-n counterexamples are documented in `docs/counterexamples.md` and
proved in `Lean/PlaneGraphs/Counterexample.lean`.

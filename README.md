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

Lean entry points
-----------------
Asymptotic lower bounds are in `Lean/Main.lean`:
- `main_lower_bound_deg34`: shifted bound using explicit K = 112/11.
- `main_lower_bound_deg34_prefactor`: prefactor form using K = 112/11.
- `main_lower_bound_deg34_from_deg34`: derives K = 112/11 from the
  `(11*n - 6)/112` inequality.
- `main_lower_bound_deg34_cert`: same as above but routes through the JSON
  certificate (`certificates/example.json`).

Counterexamples
---------------
Exact small-n counterexamples are documented in `docs/counterexamples.md` and
proved in `Lean/PlaneGraphs/Counterexample.lean`.

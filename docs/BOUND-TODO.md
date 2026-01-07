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

- `scripts/mine_degree_vectors.py` enumerates triangulations for sampled point
  sets and writes degree vectors to JSON. This is the data source for refining
  degree constraints.
- `scripts/optimize_weights.py` uses SciPy to fit charging weights (and a linear
  bound `a*n+b`) against the sampled vectors. By default the weights are fixed
  at their visibility bounds; pass `--free-weights` to let them vary.
- `scripts/solve_rational.py` runs a float LP and then computes the exact
  rational K for the mined vectors, emitting the command to generate a JSON
  certificate.
- `certificates/deg56_sample.json` is a data-driven sample certificate created
  from mined vectors; it is not a proven bound yet.
- `Lean/Main.lean` includes `main_lower_bound_deg56_sample*` entry points that
  accept a hypothetical `avgIso` bound for `K_deg56_sample_main`.

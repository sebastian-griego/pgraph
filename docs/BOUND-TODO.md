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

Certificates
============

This directory holds JSON certificates that Lean can import.

Format
------
Each certificate is a JSON object with a `constants` field mapping names to
integer pairs `[numerator, denominator]`.

Example:

```
{
  "constants": {
    "K_12_15": [243, 20],
    "K_23_32": [583, 25]
  }
}
```

Lean usage
----------
Use the `load_certificate` term elaborator from
`Lean/PlaneGraphs/Certificate.lean` to import a certificate at build time.

Python helper
-------------
Use `scripts/export_certificate.py` to generate a certificate from exact
rational parameters.

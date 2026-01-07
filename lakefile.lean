import Lake
open Lake DSL

package PlaneGraphs where
  srcDir := "Lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.0"

@[default_target]
lean_lib PlaneGraphs where
  roots := #[
    `PlaneGraphs.Basic,
    `PlaneGraphs.Certificate,
    `PlaneGraphs.DegreeCounts,
    `PlaneGraphs.DegreeVectors,
    `PlaneGraphs.Asymptotic,
    `PlaneGraphs.ExpectationLemma,
    `PlaneGraphs.Charging,
    `PlaneGraphs.Counterexample,
    `PlaneGraphs.TrivialLowerBound,
    `Main
  ]

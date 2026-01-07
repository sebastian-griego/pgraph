import Mathlib
import PlaneGraphs.Charging

open Lean
open Lean.Elab Term

namespace PlaneGraphs

structure DegreeVector where
  v3 : Nat
  v4 : Nat
  v5 : Nat
  v6 : Nat
  vL : Nat
  deriving Repr, DecidableEq

instance : ToExpr DegreeVector where
  toExpr v :=
    mkApp5 (mkConst ``DegreeVector.mk)
      (toExpr v.v3) (toExpr v.v4) (toExpr v.v5) (toExpr v.v6) (toExpr v.vL)
  toTypeExpr := mkConst ``DegreeVector

def DegreeVector.n (v : DegreeVector) : Nat :=
  v.v3 + v.v4 + v.v5 + v.v6 + v.vL

def DegreeVector.charge (v : DegreeVector) (w3 w4 w5 w6 wL : ℚ) : ℚ :=
  (v.v3 : ℚ) * w3 + (v.v4 : ℚ) * w4 + (v.v5 : ℚ) * w5 +
    (v.v6 : ℚ) * w6 + (v.vL : ℚ) * wL

def DegreeVector.sumLarge (v : DegreeVector) : ℚ :=
  3 * (v.v3 : ℚ) + 2 * (v.v4 : ℚ) + (v.v5 : ℚ) + 6 * (v.vL : ℚ) - 12

def parseNat (j : Json) : Except String Nat := do
  let i : Int ← fromJson? j
  if i < 0 then
    .error "expected nonnegative integer"
  else
    return Int.toNat i

def parseVector (j : Json) : Except String DegreeVector := do
  match j with
  | .arr #[a, b, c, d, e] =>
      let v3 ← parseNat a
      let v4 ← parseNat b
      let v5 ← parseNat c
      let v6 ← parseNat d
      let vL ← parseNat e
      return { v3 := v3, v4 := v4, v5 := v5, v6 := v6, vL := vL }
  | _ => .error "expected array with five elements"

def parseVectorList (j : Json) : Except String (List DegreeVector) := do
  match j with
  | .arr xs =>
      let mut acc : List DegreeVector := []
      for x in xs do
        let v ← parseVector x
        acc := acc.concat v
      return acc
  | _ => .error "expected array of vectors"

syntax (name := loadVectors) "load_vectors " str : term

@[term_elab loadVectors] def elabLoadVectors : TermElab
  | `(load_vectors $path:str) => fun _ => do
      let data ← liftM <| IO.FS.readFile path.getString
      let json ←
        match Json.parse data with
        | .ok j => pure j
        | .error e => throwError e
      let vectors ←
        match parseVectorList json with
        | .ok xs => pure xs
        | .error e => throwError e
      return toExpr vectors
  | _ => fun _ => Elab.throwUnsupportedSyntax

def deg56SampleVectors : List DegreeVector :=
  load_vectors "data/degree_vectors.json"

def deg56FastVectors : List DegreeVector :=
  load_vectors "data/degree_vectors_new.json"

def deg56Ok (v : DegreeVector) : Prop :=
  v.charge w3_sample w4_sample w5_sample w6_sample wL_sample ≤
    (v.n : ℚ) / K_deg56_sample

instance (v : DegreeVector) : Decidable (deg56Ok v) := by
  dsimp [deg56Ok]
  exact Rat.instDecidableLe _ _

def deg56Balance (v : DegreeVector) : Prop :=
  20 * (v.v3 : ℚ) ≤
    4 * (v.v4 : ℚ) + 16 * (v.v5 : ℚ) + 22 * (v.v6 : ℚ) + 25 * (v.vL : ℚ)

instance (v : DegreeVector) : Decidable (deg56Balance v) := by
  dsimp [deg56Balance]
  exact Rat.instDecidableLe _ _

def AllOkDeg56 : List DegreeVector → Prop
  | [] => True
  | v :: vs => deg56Ok v ∧ AllOkDeg56 vs

instance : Decidable (AllOkDeg56 vs) := by
  induction vs with
  | nil =>
      exact isTrue trivial
  | cons v vs ih =>
      letI : Decidable (deg56Ok v) := inferInstance
      letI : Decidable (AllOkDeg56 vs) := ih
      exact instDecidableAnd

lemma AllOkDeg56.forall_mem : ∀ {vs}, AllOkDeg56 vs → ∀ v ∈ vs, deg56Ok v
  | [], _h => by
      intro v hv
      cases hv
  | v :: vs, h => by
      intro v' hv'
      have h' : deg56Ok v ∧ AllOkDeg56 vs := h
      cases h' with
      | intro hv hvs =>
          have hv' : v' = v ∨ v' ∈ vs := by
            simpa [List.mem_cons] using hv'
          cases hv' with
          | inl hEq =>
              simpa [hEq] using hv
          | inr hMem =>
              exact AllOkDeg56.forall_mem hvs v' hMem

lemma deg56SampleVectors_ok :
    AllOkDeg56 deg56SampleVectors := by
  native_decide

lemma deg56SampleVectors_ok_forall :
    ∀ v ∈ deg56SampleVectors, deg56Ok v := by
  exact AllOkDeg56.forall_mem deg56SampleVectors_ok

lemma deg56Ok_iff_balance (v : DegreeVector) :
    deg56Ok v ↔ deg56Balance v := by
  simpa [deg56Ok, DegreeVector.charge, DegreeVector.n, deg56Balance] using
    (charge_bound_deg56_iff
      (v3 := (v.v3 : ℚ))
      (v4 := (v.v4 : ℚ))
      (v5 := (v.v5 : ℚ))
      (v6 := (v.v6 : ℚ))
      (vL := (v.vL : ℚ)))

def deg56LinearOk (v : DegreeVector) : Prop :=
  45 * (v.v3 : ℚ) + 21 * (v.v4 : ℚ) + 9 * (v.v5 : ℚ) + 3 * (v.v6 : ℚ)
    ≤ 25 * (v.n : ℚ)

instance (v : DegreeVector) : Decidable (deg56LinearOk v) := by
  dsimp [deg56LinearOk]
  exact Rat.instDecidableLe _ _

lemma deg56Balance_iff_linear (v : DegreeVector) :
    deg56Balance v ↔ deg56LinearOk v := by
  have hsum :
      (v.v3 : ℚ) + (v.v4 : ℚ) + (v.v5 : ℚ) + (v.v6 : ℚ) + (v.vL : ℚ) =
        (v.n : ℚ) := by
    simp [DegreeVector.n]
  simpa [deg56Balance, deg56LinearOk, DegreeVector.n] using
    (deg56_balance_iff_linear (v3 := (v.v3 : ℚ)) (v4 := (v.v4 : ℚ))
      (v5 := (v.v5 : ℚ)) (v6 := (v.v6 : ℚ)) (vL := (v.vL : ℚ))
      (n := (v.n : ℚ)) hsum)

def AllBalanceDeg56 : List DegreeVector → Prop
  | [] => True
  | v :: vs => deg56Balance v ∧ AllBalanceDeg56 vs

instance : Decidable (AllBalanceDeg56 vs) := by
  induction vs with
  | nil =>
      exact isTrue trivial
  | cons v vs ih =>
      letI : Decidable (deg56Balance v) := inferInstance
      letI : Decidable (AllBalanceDeg56 vs) := ih
      exact instDecidableAnd

lemma AllBalanceDeg56.forall_mem : ∀ {vs}, AllBalanceDeg56 vs → ∀ v ∈ vs, deg56Balance v
  | [], _h => by
      intro v hv
      cases hv
  | v :: vs, h => by
      intro v' hv'
      have h' : deg56Balance v ∧ AllBalanceDeg56 vs := h
      cases h' with
      | intro hv hvs =>
          have hv' : v' = v ∨ v' ∈ vs := by
            simpa [List.mem_cons] using hv'
          cases hv' with
          | inl hEq =>
              simpa [hEq] using hv
          | inr hMem =>
              exact AllBalanceDeg56.forall_mem hvs v' hMem

lemma deg56SampleVectors_balance :
    AllBalanceDeg56 deg56SampleVectors := by
  native_decide

lemma deg56SampleVectors_balance_forall :
    ∀ v ∈ deg56SampleVectors, deg56Balance v := by
  exact AllBalanceDeg56.forall_mem deg56SampleVectors_balance

lemma deg56SampleVectors_linear_forall :
    ∀ v ∈ deg56SampleVectors, deg56LinearOk v := by
  intro v hv
  have hbal := deg56SampleVectors_balance_forall v hv
  exact (deg56Balance_iff_linear v).1 hbal

lemma deg56FastVectors_ok :
    AllOkDeg56 deg56FastVectors := by
  native_decide

lemma deg56FastVectors_ok_forall :
    ∀ v ∈ deg56FastVectors, deg56Ok v := by
  exact AllOkDeg56.forall_mem deg56FastVectors_ok

lemma deg56FastVectors_balance :
    AllBalanceDeg56 deg56FastVectors := by
  native_decide

lemma deg56FastVectors_balance_forall :
    ∀ v ∈ deg56FastVectors, deg56Balance v := by
  exact AllBalanceDeg56.forall_mem deg56FastVectors_balance

lemma deg56FastVectors_linear_forall :
    ∀ v ∈ deg56FastVectors, deg56LinearOk v := by
  intro v hv
  have hbal := deg56FastVectors_balance_forall v hv
  exact (deg56Balance_iff_linear v).1 hbal

def deg56ShiftVectors : List DegreeVector :=
  deg56SampleVectors.filter (fun v => 9 ≤ v.n)

def deg56ShiftOk (v : DegreeVector) : Prop :=
  v.charge w3_shift_sample w4_shift_sample w5_shift_sample w6_shift_sample wL_shift_sample ≤
    (v.n : ℚ) / K_deg56_shift_sample

instance (v : DegreeVector) : Decidable (deg56ShiftOk v) := by
  dsimp [deg56ShiftOk]
  exact Rat.instDecidableLe _ _

def deg56ShiftBalance (v : DegreeVector) : Prop :=
  22 * (v.v3 : ℚ) ≤
    2 * (v.v4 : ℚ) + 14 * (v.v5 : ℚ) + 20 * (v.v6 : ℚ) + 23 * (v.vL : ℚ)

instance (v : DegreeVector) : Decidable (deg56ShiftBalance v) := by
  dsimp [deg56ShiftBalance]
  exact Rat.instDecidableLe _ _

def AllOk : List DegreeVector → Prop
  | [] => True
  | v :: vs => deg56ShiftOk v ∧ AllOk vs

instance : Decidable (AllOk vs) := by
  induction vs with
  | nil =>
      exact isTrue trivial
  | cons v vs ih =>
      letI : Decidable (deg56ShiftOk v) := inferInstance
      letI : Decidable (AllOk vs) := ih
      exact instDecidableAnd

lemma AllOk.forall_mem : ∀ {vs}, AllOk vs → ∀ v ∈ vs, deg56ShiftOk v
  | [], _h => by
      intro v hv
      cases hv
  | v :: vs, h => by
      intro v' hv'
      have h' : deg56ShiftOk v ∧ AllOk vs := h
      cases h' with
      | intro hv hvs =>
          have hv' : v' = v ∨ v' ∈ vs := by
            simpa [List.mem_cons] using hv'
          cases hv' with
          | inl hEq =>
              simpa [hEq] using hv
          | inr hMem =>
              exact AllOk.forall_mem hvs v' hMem

lemma deg56ShiftVectors_ok :
    AllOk deg56ShiftVectors := by
  native_decide

lemma deg56ShiftVectors_ok_forall :
    ∀ v ∈ deg56ShiftVectors, deg56ShiftOk v := by
  exact AllOk.forall_mem deg56ShiftVectors_ok

lemma deg56ShiftOk_iff_balance (v : DegreeVector) :
    deg56ShiftOk v ↔ deg56ShiftBalance v := by
  simpa [deg56ShiftOk, DegreeVector.charge, DegreeVector.n, deg56ShiftBalance] using
    (charge_bound_deg56_shift_iff
      (v3 := (v.v3 : ℚ))
      (v4 := (v.v4 : ℚ))
      (v5 := (v.v5 : ℚ))
      (v6 := (v.v6 : ℚ))
      (vL := (v.vL : ℚ)))

def deg56ShiftLinearOk (v : DegreeVector) : Prop :=
  45 * (v.v3 : ℚ) + 21 * (v.v4 : ℚ) + 9 * (v.v5 : ℚ) + 3 * (v.v6 : ℚ)
    ≤ 23 * (v.n : ℚ)

instance (v : DegreeVector) : Decidable (deg56ShiftLinearOk v) := by
  dsimp [deg56ShiftLinearOk]
  exact Rat.instDecidableLe _ _

lemma deg56ShiftBalance_iff_linear (v : DegreeVector) :
    deg56ShiftBalance v ↔ deg56ShiftLinearOk v := by
  have hsum :
      (v.v3 : ℚ) + (v.v4 : ℚ) + (v.v5 : ℚ) + (v.v6 : ℚ) + (v.vL : ℚ) =
        (v.n : ℚ) := by
    simp [DegreeVector.n]
  simpa [deg56ShiftBalance, deg56ShiftLinearOk, DegreeVector.n] using
    (deg56_shift_balance_iff_linear (v3 := (v.v3 : ℚ)) (v4 := (v.v4 : ℚ))
      (v5 := (v.v5 : ℚ)) (v6 := (v.v6 : ℚ)) (vL := (v.vL : ℚ))
      (n := (v.n : ℚ)) hsum)

def deg56ShiftSumLargeOk (v : DegreeVector) : Prop :=
  v.sumLarge ≥
    25 * (v.v3 : ℚ) - 13 * (v.v5 : ℚ) - 20 * (v.v6 : ℚ) -
      17 * (v.vL : ℚ) - 12

instance (v : DegreeVector) : Decidable (deg56ShiftSumLargeOk v) := by
  dsimp [deg56ShiftSumLargeOk]
  exact Rat.instDecidableLe _ _

lemma deg56ShiftBalance_iff_sumLarge (v : DegreeVector) :
    deg56ShiftBalance v ↔ deg56ShiftSumLargeOk v := by
  have hsumLarge :
      v.sumLarge =
        3 * (v.v3 : ℚ) + 2 * (v.v4 : ℚ) + (v.v5 : ℚ) +
          6 * (v.vL : ℚ) - 12 := by
    rfl
  simpa [deg56ShiftBalance, deg56ShiftSumLargeOk, DegreeVector.sumLarge] using
    (deg56_shift_balance_iff_sumLarge
      (v3 := (v.v3 : ℚ))
      (v4 := (v.v4 : ℚ))
      (v5 := (v.v5 : ℚ))
      (v6 := (v.v6 : ℚ))
      (vL := (v.vL : ℚ))
      (sumLarge := v.sumLarge)
      hsumLarge)

def AllBalance : List DegreeVector → Prop
  | [] => True
  | v :: vs => deg56ShiftBalance v ∧ AllBalance vs

instance : Decidable (AllBalance vs) := by
  induction vs with
  | nil =>
      exact isTrue trivial
  | cons v vs ih =>
      letI : Decidable (deg56ShiftBalance v) := inferInstance
      letI : Decidable (AllBalance vs) := ih
      exact instDecidableAnd

lemma AllBalance.forall_mem : ∀ {vs}, AllBalance vs → ∀ v ∈ vs, deg56ShiftBalance v
  | [], _h => by
      intro v hv
      cases hv
  | v :: vs, h => by
      intro v' hv'
      have h' : deg56ShiftBalance v ∧ AllBalance vs := h
      cases h' with
      | intro hv hvs =>
          have hv' : v' = v ∨ v' ∈ vs := by
            simpa [List.mem_cons] using hv'
          cases hv' with
          | inl hEq =>
              simpa [hEq] using hv
          | inr hMem =>
              exact AllBalance.forall_mem hvs v' hMem

lemma deg56ShiftVectors_balance :
    AllBalance deg56ShiftVectors := by
  native_decide

lemma deg56ShiftVectors_balance_forall :
    ∀ v ∈ deg56ShiftVectors, deg56ShiftBalance v := by
  exact AllBalance.forall_mem deg56ShiftVectors_balance

lemma deg56ShiftVectors_linear_forall :
    ∀ v ∈ deg56ShiftVectors, deg56ShiftLinearOk v := by
  intro v hv
  have hbal := deg56ShiftVectors_balance_forall v hv
  exact (deg56ShiftBalance_iff_linear v).1 hbal

lemma deg56ShiftVectors_sumLarge :
    ∀ v ∈ deg56ShiftVectors, deg56ShiftSumLargeOk v := by
  intro v hv
  have hbal := deg56ShiftVectors_balance_forall v hv
  exact (deg56ShiftBalance_iff_sumLarge v).1 hbal

end PlaneGraphs

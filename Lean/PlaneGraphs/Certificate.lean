import Mathlib

open Lean
open Lean.Elab Term

namespace PlaneGraphs

structure Certificate where
  constants : List (String × Int × Nat)
  deriving Repr

def Certificate.get? (cert : Certificate) (name : String) : Option (Int × Nat) :=
  cert.constants.findSome? (fun
    | (k, num, den) => if k = name then some (num, den) else none)

def Certificate.getQ? (cert : Certificate) (name : String) : Option ℚ := do
  let (num, den) ← cert.get? name
  if den = 0 then
    none
  else
    some ((num : ℚ) / (den : ℚ))

def parseRatPair (j : Json) : Except String (Int × Nat) := do
  match j with
  | .arr #[a, b] =>
      let num : Int ← fromJson? a
      let den : Nat ← fromJson? b
      if den = 0 then
        .error "certificate denominator must be positive"
      else
        return (num, den)
  | _ => .error "expected array with two elements"

def parseConstObj (j : Json) : Except String (List (String × Int × Nat)) := do
  let obj ← j.getObj?
  let acc : Except String (List (String × Int × Nat)) :=
    RBNode.fold
      (fun (st : Except String (List (String × Int × Nat))) k v =>
        match st with
        | .error e => .error e
        | .ok xs =>
            match parseRatPair v with
            | .ok (num, den) => .ok ((k, num, den) :: xs)
            | .error e => .error e)
      (.ok [])
      obj
  match acc with
  | .ok xs => return xs.reverse
  | .error e => .error e

instance : FromJson Certificate where
  fromJson? j := do
    let constJson ← j.getObjVal? "constants"
    let entries ← parseConstObj constJson
    return { constants := entries }

syntax (name := loadCertificate) "load_certificate " str : term

@[term_elab loadCertificate] def elabLoadCertificate : TermElab
  | `(load_certificate $path:str) => fun _ => do
      let data ← liftM <| IO.FS.readFile path.getString
      let json ←
        match Json.parse data with
        | .ok j => pure j
        | .error e => throwError e
      let cert ←
        match (fromJson? json : Except String Certificate) with
        | .ok c => pure c
        | .error e => throwError e
      let listExpr := toExpr cert.constants
      return mkApp (mkConst ``Certificate.mk) listExpr
  | _ => fun _ => Elab.throwUnsupportedSyntax

def exampleCertificate : Certificate :=
  load_certificate "certificates/example.json"

def deg56SampleCertificate : Certificate :=
  load_certificate "certificates/deg56_sample.json"

def deg56ShiftSampleCertificate : Certificate :=
  load_certificate "certificates/deg56_shift_sample.json"

lemma exampleCertificate_constants :
    exampleCertificate.constants =
      [("K_12_15", 243, 20), ("K_23_32", 583, 25), ("K_deg34", 112, 11)] := by
  rfl

lemma exampleCertificate_getQ_12_15 :
    exampleCertificate.getQ? "K_12_15" = some (243 / 20 : ℚ) := by
  rfl

lemma exampleCertificate_getQ_23_32 :
    exampleCertificate.getQ? "K_23_32" = some (583 / 25 : ℚ) := by
  rfl

lemma exampleCertificate_getQ_deg34 :
    exampleCertificate.getQ? "K_deg34" = some (112 / 11 : ℚ) := by
  rfl

lemma deg56SampleCertificate_constants :
    deg56SampleCertificate.constants =
      [("K_deg56", 96, 7), ("w3", 1, 8), ("w4", 1, 16), ("w5", 1, 32),
        ("w6", 1, 64), ("wL", 1, 128)] := by
  rfl

lemma deg56SampleCertificate_getQ_K_deg56 :
    deg56SampleCertificate.getQ? "K_deg56" = some (96 / 7 : ℚ) := by
  rfl

lemma deg56SampleCertificate_getQ_w3 :
    deg56SampleCertificate.getQ? "w3" = some (1 / 8 : ℚ) := by
  rfl

lemma deg56SampleCertificate_getQ_w4 :
    deg56SampleCertificate.getQ? "w4" = some (1 / 16 : ℚ) := by
  rfl

lemma deg56SampleCertificate_getQ_w5 :
    deg56SampleCertificate.getQ? "w5" = some (1 / 32 : ℚ) := by
  rfl

lemma deg56SampleCertificate_getQ_w6 :
    deg56SampleCertificate.getQ? "w6" = some (1 / 64 : ℚ) := by
  rfl

lemma deg56SampleCertificate_getQ_wL :
    deg56SampleCertificate.getQ? "wL" = some (1 / 128 : ℚ) := by
  rfl

lemma deg56ShiftSampleCertificate_constants :
    deg56ShiftSampleCertificate.constants =
      [("K_deg56_shift", 192, 13), ("w3", 1, 8), ("w4", 1, 16), ("w5", 1, 32),
        ("w6", 1, 64), ("wL", 1, 128)] := by
  rfl

lemma deg56ShiftSampleCertificate_getQ_K_deg56_shift :
    deg56ShiftSampleCertificate.getQ? "K_deg56_shift" = some (192 / 13 : ℚ) := by
  rfl

lemma deg56ShiftSampleCertificate_getQ_w3 :
    deg56ShiftSampleCertificate.getQ? "w3" = some (1 / 8 : ℚ) := by
  rfl

lemma deg56ShiftSampleCertificate_getQ_w4 :
    deg56ShiftSampleCertificate.getQ? "w4" = some (1 / 16 : ℚ) := by
  rfl

lemma deg56ShiftSampleCertificate_getQ_w5 :
    deg56ShiftSampleCertificate.getQ? "w5" = some (1 / 32 : ℚ) := by
  rfl

lemma deg56ShiftSampleCertificate_getQ_w6 :
    deg56ShiftSampleCertificate.getQ? "w6" = some (1 / 64 : ℚ) := by
  rfl

lemma deg56ShiftSampleCertificate_getQ_wL :
    deg56ShiftSampleCertificate.getQ? "wL" = some (1 / 128 : ℚ) := by
  rfl

end PlaneGraphs

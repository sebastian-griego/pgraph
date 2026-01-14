import Mathlib
import PlaneGraphs.Basic

open scoped BigOperators

namespace PlaneGraphs

noncomputable def degree {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : Nat := by
  classical
  exact ∑ s in G, (if incident s v then 1 else 0)

noncomputable def degreeSum {n : ℕ} (G : Finset (Segment n)) : Nat := by
  classical
  exact ∑ v in Finset.univ, degree G v

noncomputable instance {n : ℕ} (s : Segment n) (v : Fin n) : Decidable (incident s v) := by
  classical
  infer_instance

noncomputable def degEqCount {n : ℕ} (G : Finset (Segment n)) (k : Nat) : Nat := by
  classical
  exact ∑ v in Finset.univ, (if degree G v = k then 1 else 0)

noncomputable def degGeCount {n : ℕ} (G : Finset (Segment n)) (k : Nat) : Nat := by
  classical
  exact ∑ v in Finset.univ, (if k ≤ degree G v then 1 else 0)

noncomputable def degGeSum {n : ℕ} (G : Finset (Segment n)) (k : Nat) : Nat := by
  classical
  exact ∑ v in Finset.univ, (if k ≤ degree G v then degree G v else 0)

noncomputable def v3 {n : ℕ} (G : Finset (Segment n)) : Nat :=
  degEqCount G 3

noncomputable def v4 {n : ℕ} (G : Finset (Segment n)) : Nat :=
  degEqCount G 4

noncomputable def v5 {n : ℕ} (G : Finset (Segment n)) : Nat :=
  degEqCount G 5

noncomputable def v6 {n : ℕ} (G : Finset (Segment n)) : Nat :=
  degEqCount G 6

noncomputable def vL {n : ℕ} (G : Finset (Segment n)) : Nat :=
  degGeCount G 7

noncomputable def sumLarge {n : ℕ} (G : Finset (Segment n)) : Nat :=
  degGeSum G 7

noncomputable def sumLargeExcess {n : ℕ} (G : Finset (Segment n)) : Nat :=
  sumLarge G - 7 * vL G

noncomputable def adjacent {n : ℕ} (G : Finset (Segment n)) (u v : Fin n) : Prop :=
  u ≠ v ∧ ∃ s ∈ G, incident s u ∧ incident s v

noncomputable instance {n : ℕ} (G : Finset (Segment n)) (u v : Fin n) :
    Decidable (adjacent G u v) := by
  classical
  infer_instance

lemma adjacent_symm {n : ℕ} {G : Finset (Segment n)} {u v : Fin n} :
    adjacent G u v ↔ adjacent G v u := by
  constructor
  · intro h
    rcases h with ⟨hne, s, hs, hu, hv⟩
    exact ⟨hne.symm, s, hs, hv, hu⟩
  · intro h
    rcases h with ⟨hne, s, hs, hu, hv⟩
    exact ⟨hne.symm, s, hs, hv, hu⟩

lemma adjacent_self_false {n : ℕ} {G : Finset (Segment n)} {v : Fin n} :
    ¬ adjacent G v v := by
  intro h
  exact h.1 rfl

lemma segment_eq_of_incident {n : ℕ} {s t : Segment n} {u v : Fin n} (hne : u ≠ v)
    (hu : incident s u) (hv : incident s v) (hu' : incident t u) (hv' : incident t v) :
    s = t := by
  apply Subtype.ext
  refine Sym2.eq_of_ne_mem hne ?_ ?_ ?_ ?_
  · simpa [incident] using hu
  · simpa [incident] using hv
  · simpa [incident] using hu'
  · simpa [incident] using hv'

lemma adjacent_iff_edge {n : ℕ} {G : Finset (Segment n)} {u v : Fin n} :
    adjacent G u v ↔ u ≠ v ∧ ∃ s ∈ G, (s.1 = Sym2.mk (u, v)) := by
  constructor
  · intro h
    rcases h with ⟨hne, s, hs, hu, hv⟩
    have hmem :
        s.1 = Sym2.mk (u, v) := by
      have hmem' : u ∈ s.1 ∧ v ∈ s.1 := by
        simpa [incident] using And.intro hu hv
      exact (Sym2.mem_and_mem_iff hne).1 hmem'
    exact ⟨hne, s, hs, hmem⟩
  · intro h
    rcases h with ⟨hne, s, hs, hmem⟩
    have hu : incident s u := by
      simp [incident, hmem, Sym2.mem_mk_left]
    have hv : incident s v := by
      simp [incident, hmem, Sym2.mem_mk_right]
    exact ⟨hne, s, hs, hu, hv⟩

noncomputable def deg56Debt {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : ℚ :=
  (33 / 4 : ℚ) * (if degree G v = 3 then 1 else 0) +
  (5 / 4 : ℚ) * (if degree G v = 4 then 1 else 0) +
  (-11 / 4 : ℚ) * (if degree G v = 5 then 1 else 0) +
  (-21 / 4 : ℚ) * (if degree G v = 6 then 1 else 0) +
  (-7 : ℚ) * (if 7 ≤ degree G v then 1 else 0)

noncomputable def deg56Excess {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : ℚ :=
  if 7 ≤ degree G v then (degree G v : ℚ) - 7 else 0

noncomputable def deg56BalanceTerm {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : ℚ :=
  deg56Excess G v - deg56Debt G v

noncomputable def netTransfer {n : ℕ} (transfer : Fin n → Fin n → ℚ) (v : Fin n) : ℚ :=
  ∑ u in Finset.univ, transfer v u

noncomputable def deg56LowerConst {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c3 c4 c5 c6 : ℚ) (v : Fin n) : ℚ :=
  ((-33 / 4 : ℚ) + a3 * c3) * (if degree G v = 3 then 1 else 0) +
  ((-5 / 4 : ℚ) + a4 * c4) * (if degree G v = 4 then 1 else 0) +
  ((11 / 4 : ℚ) + a5 * c5) * (if degree G v = 5 then 1 else 0) +
  ((21 / 4 : ℚ) + a6 * c6) * (if degree G v = 6 then 1 else 0) +
  (1 - (a3 + a4 + a5 + a6)) *
    (if 7 ≤ degree G v then (degree G v : ℚ) else 0)

noncomputable def adjacentLargeCountQ {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : ℚ :=
  ∑ u in Finset.univ, (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)

noncomputable def adjacentDegCountQ {n : ℕ} (G : Finset (Segment n)) (v : Fin n) (k : Nat) : ℚ :=
  ∑ u in Finset.univ, (if adjacent G v u ∧ degree G u = k then (1 : ℚ) else 0)

noncomputable def adjacentCountQ {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : ℚ :=
  ∑ u in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0)

noncomputable def sum_adjacentLargeCountQ_degEq {n : ℕ} (G : Finset (Segment n)) (k : Nat) : ℚ :=
  ∑ v in Finset.univ, (if degree G v = k then adjacentLargeCountQ G v else 0)

noncomputable def sum_adjacentDegCountQ_large {n : ℕ} (G : Finset (Segment n)) (k : Nat) : ℚ :=
  ∑ v in Finset.univ, (if 7 ≤ degree G v then adjacentDegCountQ G v k else 0)

lemma adjacentLargeCountQ_nonneg {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    0 ≤ adjacentLargeCountQ G v := by
  classical
  refine Finset.sum_nonneg ?_
  intro u _
  by_cases h : adjacent G v u ∧ 7 ≤ degree G u
  · simp [adjacentLargeCountQ, h]
  · simp [adjacentLargeCountQ, h]

noncomputable def adjacentSet {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => adjacent G v u)

noncomputable def incidentEdgeSet {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    Finset (Segment n) :=
  G.filter (fun s => incident s v)

noncomputable def transferDeg56Base {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) (v u : Fin n) : ℚ := by
  classical
  exact
    if adjacent G v u ∧ 7 ≤ degree G u ∧ degree G v = 3 then a3
    else if adjacent G v u ∧ 7 ≤ degree G u ∧ degree G v = 4 then a4
    else if adjacent G v u ∧ 7 ≤ degree G u ∧ degree G v = 5 then a5
    else if adjacent G v u ∧ 7 ≤ degree G u ∧ degree G v = 6 then a6
    else 0

noncomputable def transferDeg56 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) (v u : Fin n) : ℚ :=
  transferDeg56Base G a3 a4 a5 a6 v u - transferDeg56Base G a3 a4 a5 a6 u v

lemma transferDeg56_antisym {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) (u v : Fin n) :
    transferDeg56 G a3 a4 a5 a6 u v = - transferDeg56 G a3 a4 a5 a6 v u := by
  simp [transferDeg56]

lemma netTransfer_deg3_eq {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 3) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a3 * ∑ u in Finset.univ,
        (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
  classical
  let p : Fin n → Prop := fun u => adjacent G v u ∧ 7 ≤ degree G u
  have hsum :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        ∑ u in Finset.univ, (if p u then a3 else 0) := by
    simp [netTransfer, transferDeg56, transferDeg56Base, hdeg, p]
  have hsum' :
      ∑ u in Finset.univ, (if p u then a3 else 0) =
        a3 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
    calc
      ∑ u in Finset.univ, (if p u then a3 else 0)
          = ∑ u in Finset.univ, a3 * (if p u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p u <;> simp [hp]
      _ = a3 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p u then (1 : ℚ) else 0) (a := a3)
  simpa [p] using hsum.trans hsum'

lemma netTransfer_deg3_eq_count {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 3) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a3 * adjacentLargeCountQ G v := by
  simpa [adjacentLargeCountQ] using netTransfer_deg3_eq (G := G) a3 a4 a5 a6 hdeg

lemma netTransfer_deg4_eq {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 4) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a4 * ∑ u in Finset.univ,
        (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
  classical
  let p : Fin n → Prop := fun u => adjacent G v u ∧ 7 ≤ degree G u
  have hsum :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        ∑ u in Finset.univ, (if p u then a4 else 0) := by
    simp [netTransfer, transferDeg56, transferDeg56Base, hdeg, p]
  have hsum' :
      ∑ u in Finset.univ, (if p u then a4 else 0) =
        a4 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
    calc
      ∑ u in Finset.univ, (if p u then a4 else 0)
          = ∑ u in Finset.univ, a4 * (if p u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p u <;> simp [hp]
      _ = a4 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p u then (1 : ℚ) else 0) (a := a4)
  simpa [p] using hsum.trans hsum'

lemma netTransfer_deg4_eq_count {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 4) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a4 * adjacentLargeCountQ G v := by
  simpa [adjacentLargeCountQ] using netTransfer_deg4_eq (G := G) a3 a4 a5 a6 hdeg

lemma netTransfer_deg5_eq {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 5) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a5 * ∑ u in Finset.univ,
        (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
  classical
  let p : Fin n → Prop := fun u => adjacent G v u ∧ 7 ≤ degree G u
  have hsum :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        ∑ u in Finset.univ, (if p u then a5 else 0) := by
    simp [netTransfer, transferDeg56, transferDeg56Base, hdeg, p]
  have hsum' :
      ∑ u in Finset.univ, (if p u then a5 else 0) =
        a5 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
    calc
      ∑ u in Finset.univ, (if p u then a5 else 0)
          = ∑ u in Finset.univ, a5 * (if p u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p u <;> simp [hp]
      _ = a5 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p u then (1 : ℚ) else 0) (a := a5)
  simpa [p] using hsum.trans hsum'

lemma netTransfer_deg5_eq_count {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 5) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a5 * adjacentLargeCountQ G v := by
  simpa [adjacentLargeCountQ] using netTransfer_deg5_eq (G := G) a3 a4 a5 a6 hdeg

lemma netTransfer_deg6_eq {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 6) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a6 * ∑ u in Finset.univ,
        (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
  classical
  let p : Fin n → Prop := fun u => adjacent G v u ∧ 7 ≤ degree G u
  have hsum :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        ∑ u in Finset.univ, (if p u then a6 else 0) := by
    simp [netTransfer, transferDeg56, transferDeg56Base, hdeg, p]
  have hsum' :
      ∑ u in Finset.univ, (if p u then a6 else 0) =
        a6 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
    calc
      ∑ u in Finset.univ, (if p u then a6 else 0)
          = ∑ u in Finset.univ, a6 * (if p u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p u <;> simp [hp]
      _ = a6 * ∑ u in Finset.univ, (if p u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p u then (1 : ℚ) else 0) (a := a6)
  simpa [p] using hsum.trans hsum'

lemma netTransfer_deg6_eq_count {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 6) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      a6 * adjacentLargeCountQ G v := by
  simpa [adjacentLargeCountQ] using netTransfer_deg6_eq (G := G) a3 a4 a5 a6 hdeg

lemma netTransfer_deg_ge7_eq_neg_sum_base {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : 7 ≤ degree G v) :
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      - ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v := by
  classical
  have hne3 : degree G v ≠ 3 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 3 < 7) hdeg)
  have hne4 : degree G v ≠ 4 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 4 < 7) hdeg)
  have hne5 : degree G v ≠ 5 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 5 < 7) hdeg)
  have hne6 : degree G v ≠ 6 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 6 < 7) hdeg)
  calc
    netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        ∑ u in Finset.univ,
          (transferDeg56Base G a3 a4 a5 a6 v u -
            transferDeg56Base G a3 a4 a5 a6 u v) := by
          simp [netTransfer, transferDeg56]
    _ = ∑ u in Finset.univ, - transferDeg56Base G a3 a4 a5 a6 u v := by
          refine Finset.sum_congr rfl ?_
          intro u _
          have hzero : transferDeg56Base G a3 a4 a5 a6 v u = 0 := by
            simp [transferDeg56Base, hne3, hne4, hne5, hne6]
          simp [hzero]
    _ = - ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v := by
          simp [Finset.sum_neg_distrib]

lemma sum_netTransfer_zero {n : ℕ} (transfer : Fin n → Fin n → ℚ)
    (hanti : ∀ u v, transfer u v = - transfer v u) :
    (∑ v in Finset.univ, netTransfer transfer v) = 0 := by
  classical
  have hswap :
      (∑ v in Finset.univ, ∑ u in Finset.univ, transfer u v) =
        ∑ u in Finset.univ, ∑ v in Finset.univ, transfer u v := by
    exact Finset.sum_comm
  have hswap_neg :
      - (∑ v in Finset.univ, ∑ u in Finset.univ, transfer u v) =
        - (∑ u in Finset.univ, ∑ v in Finset.univ, transfer u v) := by
    exact congrArg (fun x => -x) hswap
  have hsum :
      (∑ v in Finset.univ, ∑ u in Finset.univ, transfer v u) =
        - (∑ v in Finset.univ, ∑ u in Finset.univ, transfer v u) := by
    calc
      (∑ v in Finset.univ, ∑ u in Finset.univ, transfer v u)
          = ∑ v in Finset.univ, ∑ u in Finset.univ, - transfer u v := by
              refine Finset.sum_congr rfl ?_
              intro v _
              refine Finset.sum_congr rfl ?_
              intro u _
              exact hanti v u
      _ = - (∑ v in Finset.univ, ∑ u in Finset.univ, transfer u v) := by
            simp
      _ = - (∑ v in Finset.univ, ∑ u in Finset.univ, transfer v u) := by
            simpa using hswap_neg
  have hzero : (∑ v in Finset.univ, ∑ u in Finset.univ, transfer v u) = 0 := by
    linarith [hsum]
  simpa [netTransfer] using hzero

lemma sum_balanceTerm_ge_of_transfer {n : ℕ} (G : Finset (Segment n))
    (transfer : Fin n → Fin n → ℚ)
    (hanti : ∀ u v, transfer u v = - transfer v u)
    (lower : Fin n → ℚ)
    (hlower : ∀ v, deg56BalanceTerm G v + netTransfer transfer v ≥ lower v) :
    ∑ v in Finset.univ, deg56BalanceTerm G v ≥ ∑ v in Finset.univ, lower v := by
  have hsum :
      ∑ v in Finset.univ, lower v ≤
        ∑ v in Finset.univ, (deg56BalanceTerm G v + netTransfer transfer v) := by
    refine Finset.sum_le_sum ?_
    intro v _
    exact hlower v
  have hnet : ∑ v in Finset.univ, netTransfer transfer v = 0 :=
    sum_netTransfer_zero transfer hanti
  have hsum' :
      ∑ v in Finset.univ, (deg56BalanceTerm G v + netTransfer transfer v) =
        ∑ v in Finset.univ, deg56BalanceTerm G v := by
    calc
      ∑ v in Finset.univ, (deg56BalanceTerm G v + netTransfer transfer v)
          = ∑ v in Finset.univ, deg56BalanceTerm G v +
            ∑ v in Finset.univ, netTransfer transfer v := by
              simpa [Finset.sum_add_distrib]
      _ = ∑ v in Finset.univ, deg56BalanceTerm G v := by
            simp [hnet]
  have hsum'' :
      ∑ v in Finset.univ, lower v ≤ ∑ v in Finset.univ, deg56BalanceTerm G v := by
    simpa [hsum'] using hsum
  exact hsum''

lemma deg56BalanceTerm_eq_deg3 {n : ℕ} {G : Finset (Segment n)} {v : Fin n}
    (h : degree G v = 3) :
    deg56BalanceTerm G v = (-33 / 4 : ℚ) := by
  have h' : deg56BalanceTerm G v = (-(33 / 4 : ℚ)) := by
    simp [deg56BalanceTerm, deg56Excess, deg56Debt, h]
  nlinarith [h']

lemma deg56BalanceTerm_eq_deg4 {n : ℕ} {G : Finset (Segment n)} {v : Fin n}
    (h : degree G v = 4) :
    deg56BalanceTerm G v = (-5 / 4 : ℚ) := by
  have h' : deg56BalanceTerm G v = (-(5 / 4 : ℚ)) := by
    simp [deg56BalanceTerm, deg56Excess, deg56Debt, h]
  nlinarith [h']

lemma deg56BalanceTerm_eq_deg5 {n : ℕ} {G : Finset (Segment n)} {v : Fin n}
    (h : degree G v = 5) :
    deg56BalanceTerm G v = (11 / 4 : ℚ) := by
  have h' : deg56BalanceTerm G v = -(-11 / 4 : ℚ) := by
    simp [deg56BalanceTerm, deg56Excess, deg56Debt, h]
  nlinarith [h']

lemma deg56BalanceTerm_eq_deg6 {n : ℕ} {G : Finset (Segment n)} {v : Fin n}
    (h : degree G v = 6) :
    deg56BalanceTerm G v = (21 / 4 : ℚ) := by
  have h' : deg56BalanceTerm G v = -(-21 / 4 : ℚ) := by
    simp [deg56BalanceTerm, deg56Excess, deg56Debt, h]
  nlinarith [h']

lemma deg56BalanceTerm_eq_deg_ge7 {n : ℕ} {G : Finset (Segment n)} {v : Fin n}
    (h : 7 ≤ degree G v) :
    deg56BalanceTerm G v = (degree G v : ℚ) := by
  have hne3 : degree G v ≠ 3 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 3 < 7) h)
  have hne4 : degree G v ≠ 4 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 4 < 7) h)
  have hne5 : degree G v ≠ 5 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 5 < 7) h)
  have hne6 : degree G v ≠ 6 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 6 < 7) h)
  have h' : deg56BalanceTerm G v = (degree G v : ℚ) - 7 - (-7) := by
    simp [deg56BalanceTerm, deg56Excess, deg56Debt, h, hne3, hne4, hne5, hne6]
  nlinarith [h']

lemma deg56BalanceTerm_transfer_ge_deg3 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c : ℚ) (ha3 : 0 ≤ a3) {v : Fin n} (hdeg : degree G v = 3)
    (hcount : adjacentLargeCountQ G v ≥ c) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v ≥
      (-33 / 4 : ℚ) + a3 * c := by
  have hterm : deg56BalanceTerm G v = (-33 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg3 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a3 * adjacentLargeCountQ G v :=
    netTransfer_deg3_eq_count (G := G) a3 a4 a5 a6 hdeg
  have hbase :
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        (-33 / 4 : ℚ) + a3 * adjacentLargeCountQ G v := by
    linarith [hterm, hnet]
  have hmul : a3 * c ≤ a3 * adjacentLargeCountQ G v :=
    mul_le_mul_of_nonneg_left hcount ha3
  linarith [hbase, hmul]

lemma deg56BalanceTerm_transfer_ge_deg4 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c : ℚ) (ha4 : 0 ≤ a4) {v : Fin n} (hdeg : degree G v = 4)
    (hcount : adjacentLargeCountQ G v ≥ c) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v ≥
      (-5 / 4 : ℚ) + a4 * c := by
  have hterm : deg56BalanceTerm G v = (-5 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg4 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a4 * adjacentLargeCountQ G v :=
    netTransfer_deg4_eq_count (G := G) a3 a4 a5 a6 hdeg
  have hbase :
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        (-5 / 4 : ℚ) + a4 * adjacentLargeCountQ G v := by
    linarith [hterm, hnet]
  have hmul : a4 * c ≤ a4 * adjacentLargeCountQ G v :=
    mul_le_mul_of_nonneg_left hcount ha4
  linarith [hbase, hmul]

lemma deg56BalanceTerm_transfer_ge_deg5 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c : ℚ) (ha5 : 0 ≤ a5) {v : Fin n} (hdeg : degree G v = 5)
    (hcount : adjacentLargeCountQ G v ≥ c) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v ≥
      (11 / 4 : ℚ) + a5 * c := by
  have hterm : deg56BalanceTerm G v = (11 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg5 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a5 * adjacentLargeCountQ G v :=
    netTransfer_deg5_eq_count (G := G) a3 a4 a5 a6 hdeg
  have hbase :
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        (11 / 4 : ℚ) + a5 * adjacentLargeCountQ G v := by
    linarith [hterm, hnet]
  have hmul : a5 * c ≤ a5 * adjacentLargeCountQ G v :=
    mul_le_mul_of_nonneg_left hcount ha5
  linarith [hbase, hmul]

lemma deg56BalanceTerm_transfer_ge_deg6 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c : ℚ) (ha6 : 0 ≤ a6) {v : Fin n} (hdeg : degree G v = 6)
    (hcount : adjacentLargeCountQ G v ≥ c) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v ≥
      (21 / 4 : ℚ) + a6 * c := by
  have hterm : deg56BalanceTerm G v = (21 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg6 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a6 * adjacentLargeCountQ G v :=
    netTransfer_deg6_eq_count (G := G) a3 a4 a5 a6 hdeg
  have hbase :
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        (21 / 4 : ℚ) + a6 * adjacentLargeCountQ G v := by
    linarith [hterm, hnet]
  have hmul : a6 * c ≤ a6 * adjacentLargeCountQ G v :=
    mul_le_mul_of_nonneg_left hcount ha6
  linarith [hbase, hmul]

lemma deg56BalanceTerm_transfer_eq_deg3 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 3) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      (-33 / 4 : ℚ) + a3 * adjacentLargeCountQ G v := by
  have hterm : deg56BalanceTerm G v = (-33 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg3 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a3 * adjacentLargeCountQ G v :=
    netTransfer_deg3_eq_count (G := G) a3 a4 a5 a6 hdeg
  linarith [hterm, hnet]

lemma deg56BalanceTerm_transfer_eq_deg4 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 4) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      (-5 / 4 : ℚ) + a4 * adjacentLargeCountQ G v := by
  have hterm : deg56BalanceTerm G v = (-5 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg4 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a4 * adjacentLargeCountQ G v :=
    netTransfer_deg4_eq_count (G := G) a3 a4 a5 a6 hdeg
  linarith [hterm, hnet]

lemma deg56BalanceTerm_transfer_eq_deg5 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 5) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      (11 / 4 : ℚ) + a5 * adjacentLargeCountQ G v := by
  have hterm : deg56BalanceTerm G v = (11 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg5 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a5 * adjacentLargeCountQ G v :=
    netTransfer_deg5_eq_count (G := G) a3 a4 a5 a6 hdeg
  linarith [hterm, hnet]

lemma deg56BalanceTerm_transfer_eq_deg6 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : degree G v = 6) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      (21 / 4 : ℚ) + a6 * adjacentLargeCountQ G v := by
  have hterm : deg56BalanceTerm G v = (21 / 4 : ℚ) :=
    deg56BalanceTerm_eq_deg6 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        a6 * adjacentLargeCountQ G v :=
    netTransfer_deg6_eq_count (G := G) a3 a4 a5 a6 hdeg
  linarith [hterm, hnet]

lemma deg56BalanceTerm_transfer_eq_deg_ge7 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : 7 ≤ degree G v) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      (degree G v : ℚ) - ∑ u in Finset.univ,
        transferDeg56Base G a3 a4 a5 a6 u v := by
  have hterm : deg56BalanceTerm G v = (degree G v : ℚ) :=
    deg56BalanceTerm_eq_deg_ge7 (G := G) hdeg
  have hnet :
      netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        - ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v :=
    netTransfer_deg_ge7_eq_neg_sum_base (G := G) a3 a4 a5 a6 hdeg
  linarith [hterm, hnet]

lemma sum_transferDeg56Base_large_eq {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : 7 ≤ degree G v) :
    ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v =
      a3 * adjacentDegCountQ G v 3 + a4 * adjacentDegCountQ G v 4 +
      a5 * adjacentDegCountQ G v 5 + a6 * adjacentDegCountQ G v 6 := by
  classical
  let p3 : Fin n → Prop := fun u => adjacent G v u ∧ degree G u = 3
  let p4 : Fin n → Prop := fun u => adjacent G v u ∧ degree G u = 4
  let p5 : Fin n → Prop := fun u => adjacent G v u ∧ degree G u = 5
  let p6 : Fin n → Prop := fun u => adjacent G v u ∧ degree G u = 6
  have hterm :
      ∀ u : Fin n,
        transferDeg56Base G a3 a4 a5 a6 u v =
          (if p3 u then a3 else 0) +
          (if p4 u then a4 else 0) +
          (if p5 u then a5 else 0) +
          (if p6 u then a6 else 0) := by
    intro u
    by_cases h3 : degree G u = 3
    · simp [transferDeg56Base, hdeg, p3, p4, p5, p6, h3, adjacent_symm]
    · by_cases h4 : degree G u = 4
      · simp [transferDeg56Base, hdeg, p3, p4, p5, p6, h3, h4, adjacent_symm]
      · by_cases h5 : degree G u = 5
        · simp [transferDeg56Base, hdeg, p3, p4, p5, p6, h3, h4, h5, adjacent_symm]
        · by_cases h6 : degree G u = 6
          · simp [transferDeg56Base, hdeg, p3, p4, p5, p6, h3, h4, h5, h6, adjacent_symm]
          · simp [transferDeg56Base, hdeg, p3, p4, p5, p6, h3, h4, h5, h6, adjacent_symm]
  have hsum :
      ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v =
        ∑ u in Finset.univ, (if p3 u then a3 else 0) +
        ∑ u in Finset.univ, (if p4 u then a4 else 0) +
        ∑ u in Finset.univ, (if p5 u then a5 else 0) +
        ∑ u in Finset.univ, (if p6 u then a6 else 0) := by
    calc
      ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v
          = ∑ u in Finset.univ,
              ((if p3 u then a3 else 0) +
               (if p4 u then a4 else 0) +
               (if p5 u then a5 else 0) +
               (if p6 u then a6 else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            exact hterm u
      _ = (∑ u in Finset.univ, (if p3 u then a3 else 0)) +
          (∑ u in Finset.univ, (if p4 u then a4 else 0)) +
          (∑ u in Finset.univ, (if p5 u then a5 else 0)) +
          (∑ u in Finset.univ, (if p6 u then a6 else 0)) := by
            simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
  have hsum3 :
      ∑ u in Finset.univ, (if p3 u then a3 else 0) =
        a3 * adjacentDegCountQ G v 3 := by
    calc
      ∑ u in Finset.univ, (if p3 u then a3 else 0)
          = ∑ u in Finset.univ, a3 * (if p3 u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p3 u <;> simp [hp]
      _ = a3 * ∑ u in Finset.univ, (if p3 u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p3 u then (1 : ℚ) else 0) (a := a3)
      _ = a3 * adjacentDegCountQ G v 3 := by
            simp [adjacentDegCountQ, p3]
  have hsum4 :
      ∑ u in Finset.univ, (if p4 u then a4 else 0) =
        a4 * adjacentDegCountQ G v 4 := by
    calc
      ∑ u in Finset.univ, (if p4 u then a4 else 0)
          = ∑ u in Finset.univ, a4 * (if p4 u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p4 u <;> simp [hp]
      _ = a4 * ∑ u in Finset.univ, (if p4 u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p4 u then (1 : ℚ) else 0) (a := a4)
      _ = a4 * adjacentDegCountQ G v 4 := by
            simp [adjacentDegCountQ, p4]
  have hsum5 :
      ∑ u in Finset.univ, (if p5 u then a5 else 0) =
        a5 * adjacentDegCountQ G v 5 := by
    calc
      ∑ u in Finset.univ, (if p5 u then a5 else 0)
          = ∑ u in Finset.univ, a5 * (if p5 u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p5 u <;> simp [hp]
      _ = a5 * ∑ u in Finset.univ, (if p5 u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p5 u then (1 : ℚ) else 0) (a := a5)
      _ = a5 * adjacentDegCountQ G v 5 := by
            simp [adjacentDegCountQ, p5]
  have hsum6 :
      ∑ u in Finset.univ, (if p6 u then a6 else 0) =
        a6 * adjacentDegCountQ G v 6 := by
    calc
      ∑ u in Finset.univ, (if p6 u then a6 else 0)
          = ∑ u in Finset.univ, a6 * (if p6 u then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              by_cases hp : p6 u <;> simp [hp]
      _ = a6 * ∑ u in Finset.univ, (if p6 u then (1 : ℚ) else 0) := by
            symm
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun u => if p6 u then (1 : ℚ) else 0) (a := a6)
      _ = a6 * adjacentDegCountQ G v 6 := by
            simp [adjacentDegCountQ, p6]
  linarith [hsum, hsum3, hsum4, hsum5, hsum6]

lemma deg56BalanceTerm_transfer_eq_deg_ge7_adjacent {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) {v : Fin n} (hdeg : 7 ≤ degree G v) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
      (degree G v : ℚ) -
        (a3 * adjacentDegCountQ G v 3 + a4 * adjacentDegCountQ G v 4 +
          a5 * adjacentDegCountQ G v 5 + a6 * adjacentDegCountQ G v 6) := by
  have hbase :
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        (degree G v : ℚ) - ∑ u in Finset.univ,
          transferDeg56Base G a3 a4 a5 a6 u v :=
    deg56BalanceTerm_transfer_eq_deg_ge7 (G := G) a3 a4 a5 a6 hdeg
  have hsum :
      ∑ u in Finset.univ, transferDeg56Base G a3 a4 a5 a6 u v =
        a3 * adjacentDegCountQ G v 3 + a4 * adjacentDegCountQ G v 4 +
        a5 * adjacentDegCountQ G v 5 + a6 * adjacentDegCountQ G v 6 :=
    sum_transferDeg56Base_large_eq (G := G) a3 a4 a5 a6 hdeg
  linarith [hbase, hsum]

lemma card_filter_eq_sum_ite {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x in s, (if p x then 1 else 0) := by
  classical
  simpa using (Finset.card_filter (p := p) (s := s))

lemma adjacentCountQ_eq_card {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    adjacentCountQ G v = ((adjacentSet G v).card : ℚ) := by
  classical
  have hnat :
      (adjacentSet G v).card =
        ∑ u in Finset.univ, (if adjacent G v u then 1 else 0) := by
    simpa [adjacentSet] using
      (card_filter_eq_sum_ite (s := (Finset.univ : Finset (Fin n)))
        (p := fun u => adjacent G v u))
  have hq :
      ((adjacentSet G v).card : ℚ) =
        ∑ u in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0) := by
    exact_mod_cast hnat
  simpa [adjacentCountQ] using hq.symm

lemma incidentEdgeSet_card_eq_degree {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    (incidentEdgeSet G v).card = degree G v := by
  classical
  simpa [incidentEdgeSet, degree] using
    (card_filter_eq_sum_ite (s := G) (p := fun s => incident s v))

lemma adjacentSet_card_eq_incidentEdgeSet_card {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    (adjacentSet G v).card = (incidentEdgeSet G v).card := by
  classical
  let i : ∀ s ∈ incidentEdgeSet G v, Fin n :=
    fun s hs => Sym2.Mem.other ((Finset.mem_filter.mp hs).2)
  have hi :
      ∀ s hs, i s hs ∈ adjacentSet G v := by
    intro s hs
    have hsG : s ∈ G := (Finset.mem_filter.mp hs).1
    have hinc : incident s v := (Finset.mem_filter.mp hs).2
    have hne : i s hs ≠ v := by
      have hne' : Sym2.Mem.other hinc ≠ v :=
        Sym2.other_ne (a := v) (z := s.1) s.property hinc
      simpa [i] using hne'
    have hinc_other : incident s (i s hs) := by
      have hinc_other' : incident s (Sym2.Mem.other hinc) := by
        simpa [incident] using (Sym2.other_mem hinc)
      simpa [i] using hinc_other'
    have hadj : adjacent G v (i s hs) :=
      ⟨hne.symm, s, hsG, hinc, hinc_other⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
  have hinj :
      ∀ s1 hs1 s2 hs2, i s1 hs1 = i s2 hs2 → s1 = s2 := by
    intro s1 hs1 s2 hs2 hEq
    have hinc1 : incident s1 v := (Finset.mem_filter.mp hs1).2
    have hinc2 : incident s2 v := (Finset.mem_filter.mp hs2).2
    have hinc1_other : incident s1 (i s1 hs1) := by
      have hinc1_other' : incident s1 (Sym2.Mem.other hinc1) := by
        simpa [incident] using (Sym2.other_mem hinc1)
      simpa [i] using hinc1_other'
    have hinc2_other : incident s2 (i s2 hs2) := by
      have hinc2_other' : incident s2 (Sym2.Mem.other hinc2) := by
        simpa [incident] using (Sym2.other_mem hinc2)
      simpa [i] using hinc2_other'
    have hne : i s1 hs1 ≠ v := by
      have hne' : Sym2.Mem.other hinc1 ≠ v :=
        Sym2.other_ne (a := v) (z := s1.1) s1.property hinc1
      simpa [i] using hne'
    have hinc2_other' : incident s2 (i s1 hs1) := by
      simpa [hEq] using hinc2_other
    exact segment_eq_of_incident (u := i s1 hs1) (v := v)
      hne hinc1_other hinc1 hinc2_other' hinc2
  have hsurj :
      ∀ u ∈ adjacentSet G v, ∃ s hs, i s hs = u := by
    intro u hu
    have hu' : adjacent G v u := (Finset.mem_filter.mp hu).2
    rcases hu' with ⟨hne, s, hsG, hincv, hincu⟩
    have hs : s ∈ incidentEdgeSet G v := by
      exact Finset.mem_filter.mpr ⟨hsG, hincv⟩
    have hseg : s.1 = Sym2.mk (v, u) := by
      exact (Sym2.mem_and_mem_iff (x := v) (y := u) (z := s.1) (hne := hne)).1
        ⟨hincv, hincu⟩
    have hother : Sym2.Mem.other hincv = u := by
      have hspec' : Sym2.mk (v, Sym2.Mem.other hincv) = Sym2.mk (v, u) := by
        simpa [hseg] using (Sym2.other_spec hincv)
      exact (Sym2.congr_right (a := v) (b := Sym2.Mem.other hincv) (c := u)).1 hspec'
    have hother_eq : i s hs = Sym2.Mem.other hincv := by
      have hspec1 :
          Sym2.mk (v, i s hs) = s.1 := by
        have : Sym2.mk (v, Sym2.Mem.other ((Finset.mem_filter.mp hs).2)) = s.1 :=
          Sym2.other_spec ((Finset.mem_filter.mp hs).2)
        simpa [i] using this
      have hpair : Sym2.mk (v, i s hs) = Sym2.mk (v, Sym2.Mem.other hincv) := by
        calc
          Sym2.mk (v, i s hs) = s.1 := hspec1
          _ = Sym2.mk (v, Sym2.Mem.other hincv) := by
              simpa using (Sym2.other_spec hincv).symm
      exact (Sym2.congr_right (a := v) (b := i s hs) (c := Sym2.Mem.other hincv)).1 hpair
    refine ⟨s, hs, ?_⟩
    calc
      i s hs = Sym2.Mem.other hincv := hother_eq
      _ = u := hother
  have hcard :
      (incidentEdgeSet G v).card = (adjacentSet G v).card := by
    exact Finset.card_bij i hi hinj hsurj
  simpa using hcard.symm

lemma adjacentCountQ_eq_degree {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    adjacentCountQ G v = (degree G v : ℚ) := by
  classical
  have hcard :
      ((adjacentSet G v).card : ℚ) = ((incidentEdgeSet G v).card : ℚ) := by
    exact_mod_cast (adjacentSet_card_eq_incidentEdgeSet_card (G := G) (v := v))
  have hdeg :
      ((incidentEdgeSet G v).card : ℚ) = (degree G v : ℚ) := by
    exact_mod_cast (incidentEdgeSet_card_eq_degree (G := G) (v := v))
  calc
    adjacentCountQ G v = ((adjacentSet G v).card : ℚ) :=
      adjacentCountQ_eq_card (G := G) (v := v)
    _ = ((incidentEdgeSet G v).card : ℚ) := hcard
    _ = (degree G v : ℚ) := hdeg

lemma adjacentLargeCountQ_le_adjacentCountQ {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    adjacentLargeCountQ G v ≤ adjacentCountQ G v := by
  classical
  refine Finset.sum_le_sum ?_
  intro u _
  by_cases hlarge : adjacent G v u ∧ 7 ≤ degree G u
  · have hadj : adjacent G v u := hlarge.1
    simp [hlarge, hadj]
  · by_cases hadj : adjacent G v u
    ·
      have hdeg : ¬ 7 ≤ degree G u := by
        intro hdeg
        exact hlarge ⟨hadj, hdeg⟩
      simpa [hlarge, hadj, hdeg] using (zero_le_one : (0 : ℚ) ≤ 1)
    · simp [hlarge, hadj]

lemma adjacentDegCountQ_le_adjacentCountQ {n : ℕ} (G : Finset (Segment n)) (v : Fin n) (k : Nat) :
    adjacentDegCountQ G v k ≤ adjacentCountQ G v := by
  classical
  refine Finset.sum_le_sum ?_
  intro u _
  by_cases hdeg : degree G u = k
  · by_cases hadj : adjacent G v u
    · simp [adjacentDegCountQ, adjacentCountQ, hdeg, hadj]
    · simp [adjacentDegCountQ, adjacentCountQ, hdeg, hadj]
  · by_cases hadj : adjacent G v u
    · simp [adjacentDegCountQ, adjacentCountQ, hdeg, hadj]
    · simp [adjacentDegCountQ, adjacentCountQ, hdeg, hadj]

lemma adjacentLargeCountQ_le_degree {n : ℕ} (G : Finset (Segment n)) (v : Fin n) :
    adjacentLargeCountQ G v ≤ (degree G v : ℚ) := by
  have hle : adjacentLargeCountQ G v ≤ adjacentCountQ G v :=
    adjacentLargeCountQ_le_adjacentCountQ (G := G) (v := v)
  have hdeg : adjacentCountQ G v = (degree G v : ℚ) :=
    adjacentCountQ_eq_degree (G := G) (v := v)
  have hdeg' : adjacentCountQ G v ≤ (degree G v : ℚ) := by
    simpa [hdeg]
  exact le_trans hle hdeg'

lemma adjacentDegCountQ_le_degree {n : ℕ} (G : Finset (Segment n)) (v : Fin n) (k : Nat) :
    adjacentDegCountQ G v k ≤ (degree G v : ℚ) := by
  have hle : adjacentDegCountQ G v k ≤ adjacentCountQ G v :=
    adjacentDegCountQ_le_adjacentCountQ (G := G) (v := v) (k := k)
  have hdeg : adjacentCountQ G v = (degree G v : ℚ) :=
    adjacentCountQ_eq_degree (G := G) (v := v)
  have hdeg' : adjacentCountQ G v ≤ (degree G v : ℚ) := by
    simpa [hdeg]
  exact le_trans hle hdeg'

lemma deg56BalanceTerm_transfer_ge_deg_ge7 {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 : ℚ) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5) (ha6 : 0 ≤ a6)
    {v : Fin n} (hdeg : 7 ≤ degree G v) :
    deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v ≥
      (1 - (a3 + a4 + a5 + a6)) * (degree G v : ℚ) := by
  have hbase :
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v =
        (degree G v : ℚ) -
          (a3 * adjacentDegCountQ G v 3 + a4 * adjacentDegCountQ G v 4 +
            a5 * adjacentDegCountQ G v 5 + a6 * adjacentDegCountQ G v 6) :=
    deg56BalanceTerm_transfer_eq_deg_ge7_adjacent (G := G) a3 a4 a5 a6 hdeg
  have h3 :
      a3 * adjacentDegCountQ G v 3 ≤ a3 * (degree G v : ℚ) := by
    have hcount := adjacentDegCountQ_le_degree (G := G) (v := v) (k := 3)
    exact mul_le_mul_of_nonneg_left hcount ha3
  have h4 :
      a4 * adjacentDegCountQ G v 4 ≤ a4 * (degree G v : ℚ) := by
    have hcount := adjacentDegCountQ_le_degree (G := G) (v := v) (k := 4)
    exact mul_le_mul_of_nonneg_left hcount ha4
  have h5 :
      a5 * adjacentDegCountQ G v 5 ≤ a5 * (degree G v : ℚ) := by
    have hcount := adjacentDegCountQ_le_degree (G := G) (v := v) (k := 5)
    exact mul_le_mul_of_nonneg_left hcount ha5
  have h6 :
      a6 * adjacentDegCountQ G v 6 ≤ a6 * (degree G v : ℚ) := by
    have hcount := adjacentDegCountQ_le_degree (G := G) (v := v) (k := 6)
    exact mul_le_mul_of_nonneg_left hcount ha6
  have hsum :
      a3 * adjacentDegCountQ G v 3 + a4 * adjacentDegCountQ G v 4 +
        a5 * adjacentDegCountQ G v 5 + a6 * adjacentDegCountQ G v 6 ≤
        (a3 + a4 + a5 + a6) * (degree G v : ℚ) := by
    linarith [h3, h4, h5, h6]
  linarith [hbase, hsum]

lemma degree_ge7_of_ge3_and_ne {d : Nat} (hge : 3 ≤ d)
    (h3 : d ≠ 3) (h4 : d ≠ 4) (h5 : d ≠ 5) (h6 : d ≠ 6) : 7 ≤ d := by
  by_contra h7
  have hle : d ≤ 6 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h7)
  interval_cases d <;> simp at hge hle h3 h4 h5 h6

lemma deg56BalanceTerm_transfer_ge_lowerConst {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c3 c4 c5 c6 : ℚ)
    (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5) (ha6 : 0 ≤ a6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (h3 : ∀ v, degree G v = 3 → adjacentLargeCountQ G v ≥ c3)
    (h4 : ∀ v, degree G v = 4 → adjacentLargeCountQ G v ≥ c4)
    (h5 : ∀ v, degree G v = 5 → adjacentLargeCountQ G v ≥ c5)
    (h6 : ∀ v, degree G v = 6 → adjacentLargeCountQ G v ≥ c6) :
    ∀ v,
      deg56BalanceTerm G v + netTransfer (transferDeg56 G a3 a4 a5 a6) v ≥
        deg56LowerConst G a3 a4 a5 a6 c3 c4 c5 c6 v := by
  intro v
  by_cases hdeg3 : degree G v = 3
  · have hcount := h3 v hdeg3
    have hbase := deg56BalanceTerm_transfer_ge_deg3 (G := G) a3 a4 a5 a6 c3 ha3 hdeg3 hcount
    simpa [deg56LowerConst, hdeg3] using hbase
  by_cases hdeg4 : degree G v = 4
  · have hcount := h4 v hdeg4
    have hbase := deg56BalanceTerm_transfer_ge_deg4 (G := G) a3 a4 a5 a6 c4 ha4 hdeg4 hcount
    simpa [deg56LowerConst, hdeg3, hdeg4] using hbase
  by_cases hdeg5 : degree G v = 5
  · have hcount := h5 v hdeg5
    have hbase := deg56BalanceTerm_transfer_ge_deg5 (G := G) a3 a4 a5 a6 c5 ha5 hdeg5 hcount
    simpa [deg56LowerConst, hdeg3, hdeg4, hdeg5] using hbase
  by_cases hdeg6 : degree G v = 6
  · have hcount := h6 v hdeg6
    have hbase := deg56BalanceTerm_transfer_ge_deg6 (G := G) a3 a4 a5 a6 c6 ha6 hdeg6 hcount
    simpa [deg56LowerConst, hdeg3, hdeg4, hdeg5, hdeg6] using hbase
  have hge7 : 7 ≤ degree G v :=
    degree_ge7_of_ge3_and_ne (d := degree G v) (hge := hmin v)
      (h3 := hdeg3) (h4 := hdeg4) (h5 := hdeg5) (h6 := hdeg6)
  have hbase := deg56BalanceTerm_transfer_ge_deg_ge7 (G := G) a3 a4 a5 a6
    ha3 ha4 ha5 ha6 hge7
  simpa [deg56LowerConst, hdeg3, hdeg4, hdeg5, hdeg6, hge7] using hbase

lemma sum_if_degree_eq_mul {n : ℕ} (G : Finset (Segment n)) (k : Nat) (c : ℚ) :
    ∑ v in Finset.univ, (if degree G v = k then c else 0) =
      c * (degEqCount G k : ℚ) := by
  classical
  calc
    ∑ v in Finset.univ, (if degree G v = k then c else 0)
        = ∑ v in Finset.univ, c * (if degree G v = k then (1 : ℚ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro v _
            by_cases h : degree G v = k <;> simp [h]
    _ = c * ∑ v in Finset.univ, (if degree G v = k then (1 : ℚ) else 0) := by
          symm
          exact (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun v : Fin n => if degree G v = k then (1 : ℚ) else 0) (a := c))
    _ = c * (degEqCount G k : ℚ) := by
          have hnat :
              ∑ v in Finset.univ, (if degree G v = k then (1 : ℚ) else 0) =
                (degEqCount G k : ℚ) := by
            symm
            exact_mod_cast
              (rfl : degEqCount G k =
                ∑ v in Finset.univ, (if degree G v = k then 1 else 0))
          simpa [hnat]

lemma sum_if_degGe_degree_mul {n : ℕ} (G : Finset (Segment n)) (k : Nat) (c : ℚ) :
    ∑ v in Finset.univ, (if k ≤ degree G v then c * (degree G v : ℚ) else 0) =
      c * (degGeSum G k : ℚ) := by
  classical
  calc
    ∑ v in Finset.univ, (if k ≤ degree G v then c * (degree G v : ℚ) else 0)
        = ∑ v in Finset.univ, c * (if k ≤ degree G v then (degree G v : ℚ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro v _
            by_cases h : k ≤ degree G v <;> simp [h, mul_comm]
    _ = c * ∑ v in Finset.univ, (if k ≤ degree G v then (degree G v : ℚ) else 0) := by
          symm
          exact (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun v : Fin n => if k ≤ degree G v then (degree G v : ℚ) else 0) (a := c))
    _ = c * (degGeSum G k : ℚ) := by
          have hnat :
              ∑ v in Finset.univ, (if k ≤ degree G v then (degree G v : ℚ) else 0) =
                (degGeSum G k : ℚ) := by
            symm
            exact_mod_cast
              (rfl : degGeSum G k =
                ∑ v in Finset.univ, (if k ≤ degree G v then degree G v else 0))
          simpa [hnat]

lemma sum_deg56LowerConst_eq {n : ℕ} (G : Finset (Segment n))
    (a3 a4 a5 a6 c3 c4 c5 c6 : ℚ) :
    ∑ v in Finset.univ, deg56LowerConst G a3 a4 a5 a6 c3 c4 c5 c6 v =
      ((-33 / 4 : ℚ) + a3 * c3) * (v3 G : ℚ) +
        ((-5 / 4 : ℚ) + a4 * c4) * (v4 G : ℚ) +
        ((11 / 4 : ℚ) + a5 * c5) * (v5 G : ℚ) +
        ((21 / 4 : ℚ) + a6 * c6) * (v6 G : ℚ) +
        (1 - (a3 + a4 + a5 + a6)) * (sumLarge G : ℚ) := by
  classical
  have h3 :
      ∑ v in Finset.univ,
          (if degree G v = 3 then ((-33 / 4 : ℚ) + a3 * c3) else 0) =
        ((-33 / 4 : ℚ) + a3 * c3) * (v3 G : ℚ) := by
    simpa [v3] using
      (sum_if_degree_eq_mul (G := G) (k := 3) (c := (-33 / 4 : ℚ) + a3 * c3))
  have h4 :
      ∑ v in Finset.univ,
          (if degree G v = 4 then ((-5 / 4 : ℚ) + a4 * c4) else 0) =
        ((-5 / 4 : ℚ) + a4 * c4) * (v4 G : ℚ) := by
    simpa [v4] using
      (sum_if_degree_eq_mul (G := G) (k := 4) (c := (-5 / 4 : ℚ) + a4 * c4))
  have h5 :
      ∑ v in Finset.univ,
          (if degree G v = 5 then ((11 / 4 : ℚ) + a5 * c5) else 0) =
        ((11 / 4 : ℚ) + a5 * c5) * (v5 G : ℚ) := by
    simpa [v5] using
      (sum_if_degree_eq_mul (G := G) (k := 5) (c := (11 / 4 : ℚ) + a5 * c5))
  have h6 :
      ∑ v in Finset.univ,
          (if degree G v = 6 then ((21 / 4 : ℚ) + a6 * c6) else 0) =
        ((21 / 4 : ℚ) + a6 * c6) * (v6 G : ℚ) := by
    simpa [v6] using
      (sum_if_degree_eq_mul (G := G) (k := 6) (c := (21 / 4 : ℚ) + a6 * c6))
  have hL :
      ∑ v in Finset.univ,
          (if 7 ≤ degree G v then (1 - (a3 + a4 + a5 + a6)) * (degree G v : ℚ) else 0) =
        (1 - (a3 + a4 + a5 + a6)) * (sumLarge G : ℚ) := by
    simpa [sumLarge] using
      (sum_if_degGe_degree_mul (G := G) (k := 7)
        (c := 1 - (a3 + a4 + a5 + a6)))
  have hL' :
      ∑ v in Finset.univ,
          (if 7 ≤ degree G v then (1 - (a3 + (a4 + (a5 + a6)))) * (degree G v : ℚ) else 0) =
        (1 - (a3 + (a4 + (a5 + a6)))) * (sumLarge G : ℚ) := by
    simpa [add_assoc] using hL
  calc
    ∑ v in Finset.univ, deg56LowerConst G a3 a4 a5 a6 c3 c4 c5 c6 v
        =
          ∑ v in Finset.univ,
            ((-33 / 4 : ℚ) + a3 * c3) * (if degree G v = 3 then 1 else 0) +
          ∑ v in Finset.univ,
            ((-5 / 4 : ℚ) + a4 * c4) * (if degree G v = 4 then 1 else 0) +
          ∑ v in Finset.univ,
            ((11 / 4 : ℚ) + a5 * c5) * (if degree G v = 5 then 1 else 0) +
          ∑ v in Finset.univ,
            ((21 / 4 : ℚ) + a6 * c6) * (if degree G v = 6 then 1 else 0) +
          ∑ v in Finset.univ,
            (1 - (a3 + a4 + a5 + a6)) *
              (if 7 ≤ degree G v then (degree G v : ℚ) else 0) := by
          simp [deg56LowerConst, Finset.sum_add_distrib, add_assoc]
    _ = ((-33 / 4 : ℚ) + a3 * c3) * (v3 G : ℚ) +
        ((-5 / 4 : ℚ) + a4 * c4) * (v4 G : ℚ) +
        ((11 / 4 : ℚ) + a5 * c5) * (v5 G : ℚ) +
        ((21 / 4 : ℚ) + a6 * c6) * (v6 G : ℚ) +
        (1 - (a3 + a4 + a5 + a6)) * (sumLarge G : ℚ) := by
          simp [h3, h4, h5, h6, hL', add_assoc]

lemma sum_adjacentDegCountQ_large_le_sumLarge {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    sum_adjacentDegCountQ_large G k ≤ (sumLarge G : ℚ) := by
  classical
  have hsumLarge :
      (sumLarge G : ℚ) =
        ∑ v in Finset.univ, (if 7 ≤ degree G v then (degree G v : ℚ) else 0) := by
    have hNat :
        sumLarge G = ∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0) := by
      rfl
    exact_mod_cast hNat
  have hsumle :
      ∑ v in Finset.univ, (if 7 ≤ degree G v then adjacentDegCountQ G v k else 0) ≤
        ∑ v in Finset.univ, (if 7 ≤ degree G v then (degree G v : ℚ) else 0) := by
    refine Finset.sum_le_sum ?_
    intro v _
    by_cases hlarge : 7 ≤ degree G v
    · have hcount := adjacentDegCountQ_le_degree (G := G) (v := v) (k := k)
      simpa [hlarge] using hcount
    · simp [hlarge]
  calc
    sum_adjacentDegCountQ_large G k
        = ∑ v in Finset.univ, (if 7 ≤ degree G v then adjacentDegCountQ G v k else 0) := by
            rfl
    _ ≤ ∑ v in Finset.univ, (if 7 ≤ degree G v then (degree G v : ℚ) else 0) := hsumle
    _ = (sumLarge G : ℚ) := by
          symm
          exact hsumLarge

lemma sum_adjacentLargeCountQ_eq_sumLarge {n : ℕ} (G : Finset (Segment n)) :
    (∑ v in Finset.univ, adjacentLargeCountQ G v) = (sumLarge G : ℚ) := by
  classical
  have hinner :
      ∀ u,
        ∑ v in Finset.univ,
            (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) =
          if 7 ≤ degree G u then adjacentCountQ G u else 0 := by
    intro u
    by_cases hlarge : 7 ≤ degree G u
    · have h1 :
        ∑ v in Finset.univ,
            (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) =
          ∑ v in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases hadj : adjacent G v u
          · simp [hadj, hlarge]
          · simp [hadj, hlarge]
      have h2 :
        ∑ v in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0) =
          ∑ v in Finset.univ, (if adjacent G u v then (1 : ℚ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases hadj : adjacent G v u
          · have hadj' : adjacent G u v := (adjacent_symm).1 hadj
            simp [hadj, hadj']
          · have hadj' : ¬ adjacent G u v := by
              intro h
              exact hadj ((adjacent_symm).2 h)
            simp [hadj, hadj']
      calc
        ∑ v in Finset.univ,
            (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)
            = ∑ v in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0) := h1
        _ = ∑ v in Finset.univ, (if adjacent G u v then (1 : ℚ) else 0) := h2
        _ = adjacentCountQ G u := by simp [adjacentCountQ]
        _ = if 7 ≤ degree G u then adjacentCountQ G u else 0 := by simp [hlarge]
    · simp [hlarge]
  have hsum' :
      ∑ v in Finset.univ, adjacentLargeCountQ G v =
        ∑ u in Finset.univ, (if 7 ≤ degree G u then adjacentCountQ G u else 0) := by
    calc
      ∑ v in Finset.univ, adjacentLargeCountQ G v
          = ∑ v in Finset.univ, ∑ u in Finset.univ,
              (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
                simp [adjacentLargeCountQ]
      _ = ∑ u in Finset.univ, ∑ v in Finset.univ,
            (if adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
              exact Finset.sum_comm
      _ = ∑ u in Finset.univ, (if 7 ≤ degree G u then adjacentCountQ G u else 0) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            exact hinner u
  have hsum'' :
      ∑ u in Finset.univ, (if 7 ≤ degree G u then adjacentCountQ G u else 0) =
        ∑ u in Finset.univ, (if 7 ≤ degree G u then (degree G u : ℚ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro u _
    by_cases hlarge : 7 ≤ degree G u
    · simp [hlarge, adjacentCountQ_eq_degree (G := G) (v := u)]
    · simp [hlarge]
  have hsumLarge :
      (sumLarge G : ℚ) =
        ∑ u in Finset.univ, (if 7 ≤ degree G u then (degree G u : ℚ) else 0) := by
    have hNat :
        sumLarge G = ∑ u in Finset.univ, (if 7 ≤ degree G u then degree G u else 0) := by
          rfl
    exact_mod_cast hNat
  calc
    ∑ v in Finset.univ, adjacentLargeCountQ G v
        = ∑ u in Finset.univ, (if 7 ≤ degree G u then adjacentCountQ G u else 0) := hsum'
    _ = ∑ u in Finset.univ, (if 7 ≤ degree G u then (degree G u : ℚ) else 0) := hsum''
    _ = (sumLarge G : ℚ) := by
          symm
          exact hsumLarge

lemma sum_adjacentLargeCountQ_degEq_eq_sum_adjacentDegCountQ_large {n : ℕ}
    (G : Finset (Segment n)) (k : Nat) :
    sum_adjacentLargeCountQ_degEq G k = sum_adjacentDegCountQ_large G k := by
  classical
  have hsum1 :
      sum_adjacentLargeCountQ_degEq G k =
        ∑ v in Finset.univ, ∑ u in Finset.univ,
          (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases hdeg : degree G v = k
    · simp [sum_adjacentLargeCountQ_degEq, adjacentLargeCountQ, hdeg, and_left_comm, and_assoc]
    · simp [sum_adjacentLargeCountQ_degEq, adjacentLargeCountQ, hdeg]
  have hsum2 :
      ∑ v in Finset.univ, ∑ u in Finset.univ,
          (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) =
        ∑ u in Finset.univ, ∑ v in Finset.univ,
          (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
    exact Finset.sum_comm
  have hsum3 :
      ∑ u in Finset.univ, ∑ v in Finset.univ,
          (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) =
        ∑ u in Finset.univ, (if 7 ≤ degree G u then adjacentDegCountQ G u k else 0) := by
    refine Finset.sum_congr rfl ?_
    intro u _
    by_cases hlarge : 7 ≤ degree G u
    · have hinner :
          ∑ v in Finset.univ,
              (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)
            = adjacentDegCountQ G u k := by
          have hswap :
              ∑ v in Finset.univ,
                  (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)
                = ∑ v in Finset.univ,
                    (if degree G v = k ∧ adjacent G u v ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro v _
            by_cases hadj : adjacent G v u
            · have hadj' : adjacent G u v := (adjacent_symm).1 hadj
              simp [hadj, hadj', hlarge, and_left_comm, and_assoc]
            · have hadj' : ¬ adjacent G u v := by
                intro h
                exact hadj ((adjacent_symm).2 h)
              simp [hadj, hadj', hlarge, and_left_comm, and_assoc]
          calc
            ∑ v in Finset.univ,
                (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)
                = ∑ v in Finset.univ,
                    (if degree G v = k ∧ adjacent G u v ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := hswap
            _ = ∑ v in Finset.univ,
                    (if adjacent G u v ∧ degree G v = k then (1 : ℚ) else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro v _
                  by_cases hdeg : degree G v = k
                  · simp [hdeg, hlarge, and_left_comm, and_assoc]
                  · simp [hdeg, hlarge, and_left_comm, and_assoc]
            _ = adjacentDegCountQ G u k := by
                  simp [adjacentDegCountQ]
      calc
        ∑ v in Finset.univ,
            (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)
            = adjacentDegCountQ G u k := hinner
        _ = if 7 ≤ degree G u then adjacentDegCountQ G u k else 0 := by
              simp [hlarge]
    · have hzero :
          (∑ v in Finset.univ,
              (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)) = 0 := by
        simp [hlarge]
      calc
        ∑ v in Finset.univ,
            (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0)
            = 0 := hzero
        _ = if 7 ≤ degree G u then adjacentDegCountQ G u k else 0 := by
              simp [hlarge]
  calc
    sum_adjacentLargeCountQ_degEq G k
        = ∑ v in Finset.univ, ∑ u in Finset.univ,
            (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := hsum1
    _ = ∑ u in Finset.univ, ∑ v in Finset.univ,
            (if degree G v = k ∧ adjacent G v u ∧ 7 ≤ degree G u then (1 : ℚ) else 0) := hsum2
    _ = ∑ u in Finset.univ, (if 7 ≤ degree G u then adjacentDegCountQ G u k else 0) := hsum3
    _ = sum_adjacentDegCountQ_large G k := by rfl

lemma sum_adjacentLargeCountQ_degEq_le_sumLarge {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    sum_adjacentLargeCountQ_degEq G k ≤ (sumLarge G : ℚ) := by
  have hsum :=
    sum_adjacentDegCountQ_large_le_sumLarge (G := G) (k := k)
  simpa [sum_adjacentLargeCountQ_degEq_eq_sum_adjacentDegCountQ_large] using hsum

lemma incident_sum_eq_two {n : ℕ} (s : Segment n) :
    ∑ v in Finset.univ, (if incident s v then 1 else 0) = 2 := by
  classical
  cases' s with s hs
  revert hs
  refine Sym2.inductionOn s ?_
  intro a b hs
  let seg : Segment n := ⟨Sym2.mk (a, b), hs⟩
  have hneq : a ≠ b := by
    intro hEq
    apply hs
    exact (Sym2.mk_isDiag_iff).2 hEq
  have hset :
      (Finset.univ.filter fun v : Fin n => v = a ∨ v = b) = {a, b} := by
    ext v
    simp [Finset.mem_insert, Finset.mem_singleton, or_left_comm, or_assoc, or_comm]
  have hcard : ({a, b} : Finset (Fin n)).card = 2 := by
    simp [hneq]
  have hsum :
      ∑ v in Finset.univ, (if v = a ∨ v = b then 1 else 0)
        = (Finset.univ.filter fun v : Fin n => v = a ∨ v = b).card := by
    simpa using
      (card_filter_eq_sum_ite (Finset.univ : Finset (Fin n))
        (fun v : Fin n => v = a ∨ v = b)).symm
  have hsum' :
      ∑ v in Finset.univ, (if incident seg v then 1 else 0)
        = ∑ v in Finset.univ, (if v = a ∨ v = b then 1 else 0) := by
    simp [seg, incident, Sym2.mem_iff]
  calc
    ∑ v in Finset.univ, (if incident seg v then 1 else 0)
        = ∑ v in Finset.univ, (if v = a ∨ v = b then 1 else 0) := hsum'
    _ = (Finset.univ.filter fun v : Fin n => v = a ∨ v = b).card := hsum
    _ = 2 := by simpa [hset] using hcard

lemma degreeSum_eq_twice_card {n : ℕ} (G : Finset (Segment n)) :
    degreeSum G = 2 * G.card := by
  classical
  have hsum :
      degreeSum G =
        ∑ v in Finset.univ, ∑ s in G, (if incident s v then 1 else 0) := by
    classical
    simp [degreeSum, degree]
  have hsum' :
      ∑ v in Finset.univ, ∑ s in G, (if incident s v then 1 else 0)
        = ∑ s in G, ∑ v in Finset.univ, (if incident s v then 1 else 0) := by
    exact Finset.sum_comm
  have hsum'' :
      ∑ s in G, ∑ v in Finset.univ, (if incident s v then 1 else 0)
        = ∑ s in G, 2 := by
    refine Finset.sum_congr rfl ?_
    intro s _
    exact incident_sum_eq_two s
  have hsum''' : (∑ s in G, 2) = 2 * G.card := by
    simp [mul_comm]
  calc
    degreeSum G
        = ∑ v in Finset.univ, ∑ s in G, (if incident s v then 1 else 0) := hsum
    _ = ∑ s in G, ∑ v in Finset.univ, (if incident s v then 1 else 0) := hsum'
    _ = ∑ s in G, 2 := hsum''
    _ = 2 * G.card := hsum'''

lemma degEqCount_eq_card_filter {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    degEqCount G k = (Finset.univ.filter fun v : Fin n => degree G v = k).card := by
  classical
  simpa [degEqCount] using
    (card_filter_eq_sum_ite (s := (Finset.univ : Finset (Fin n)))
      (p := fun v : Fin n => degree G v = k)).symm

lemma degGeCount_eq_card_filter {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    degGeCount G k = (Finset.univ.filter fun v : Fin n => k ≤ degree G v).card := by
  classical
  simpa [degGeCount] using
    (card_filter_eq_sum_ite (s := (Finset.univ : Finset (Fin n)))
      (p := fun v : Fin n => k ≤ degree G v)).symm

lemma degGeSum_eq_sum {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    degGeSum G k = ∑ v in Finset.univ, (if k ≤ degree G v then degree G v else 0) := by
  rfl

lemma degree_ge_weighted (d : Nat) :
    (if d = 3 then 3 else 0) +
        (if d = 4 then 4 else 0) +
        (if d = 5 then 5 else 0) +
        (if d = 6 then 6 else 0) +
        (if 7 ≤ d then 7 else 0) ≤ d := by
  by_cases h7 : 7 ≤ d
  ·
    have h3 : d ≠ 3 := by
      have : (3 : Nat) < d := lt_of_lt_of_le (by decide : 3 < 7) h7
      exact ne_of_gt this
    have h4 : d ≠ 4 := by
      have : (4 : Nat) < d := lt_of_lt_of_le (by decide : 4 < 7) h7
      exact ne_of_gt this
    have h5 : d ≠ 5 := by
      have : (5 : Nat) < d := lt_of_lt_of_le (by decide : 5 < 7) h7
      exact ne_of_gt this
    have h6 : d ≠ 6 := by
      have : (6 : Nat) < d := lt_of_lt_of_le (by decide : 6 < 7) h7
      exact ne_of_gt this
    simpa [h7, h3, h4, h5, h6] using h7
  ·
    have h6 : d ≤ 6 := by
      have hlt : d < 7 := Nat.lt_of_not_ge h7
      exact (Nat.lt_succ_iff.mp hlt)
    interval_cases d <;> simp

lemma degree_partition_ge3 (d : Nat) (h : 3 ≤ d) :
    (if d = 3 then 1 else 0) +
        (if d = 4 then 1 else 0) +
        (if d = 5 then 1 else 0) +
        (if d = 6 then 1 else 0) +
        (if 7 ≤ d then 1 else 0) = 1 := by
  by_cases h7 : 7 ≤ d
  ·
    have h3 : d ≠ 3 := by
      have : (3 : Nat) < d := lt_of_lt_of_le (by decide : 3 < 7) h7
      exact ne_of_gt this
    have h4 : d ≠ 4 := by
      have : (4 : Nat) < d := lt_of_lt_of_le (by decide : 4 < 7) h7
      exact ne_of_gt this
    have h5 : d ≠ 5 := by
      have : (5 : Nat) < d := lt_of_lt_of_le (by decide : 5 < 7) h7
      exact ne_of_gt this
    have h6 : d ≠ 6 := by
      have : (6 : Nat) < d := lt_of_lt_of_le (by decide : 6 < 7) h7
      exact ne_of_gt this
    simp [h7, h3, h4, h5, h6]
  ·
    have hlt : d < 7 := Nat.lt_of_not_ge h7
    have hle : d ≤ 6 := Nat.lt_succ_iff.mp hlt
    interval_cases d <;> simp at h <;> simp

lemma v_sum_eq_n {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    v3 G + v4 G + v5 G + v6 G + vL G = n := by
  classical
  have hsum :
      v3 G + v4 G + v5 G + v6 G + vL G =
        ∑ v in Finset.univ,
          ((if degree G v = 3 then 1 else 0) +
           (if degree G v = 4 then 1 else 0) +
           (if degree G v = 5 then 1 else 0) +
           (if degree G v = 6 then 1 else 0) +
           (if 7 ≤ degree G v then 1 else 0)) := by
    simp [v3, v4, v5, v6, vL, degEqCount, degGeCount,
      Finset.sum_add_distrib]
  have hsum' :
      ∑ v in Finset.univ,
          ((if degree G v = 3 then 1 else 0) +
           (if degree G v = 4 then 1 else 0) +
           (if degree G v = 5 then 1 else 0) +
           (if degree G v = 6 then 1 else 0) +
           (if 7 ≤ degree G v then 1 else 0))
        = n := by
    have hpoint :
        ∀ v : Fin n,
          (if degree G v = 3 then 1 else 0) +
            (if degree G v = 4 then 1 else 0) +
            (if degree G v = 5 then 1 else 0) +
            (if degree G v = 6 then 1 else 0) +
            (if 7 ≤ degree G v then 1 else 0) = 1 := by
      intro v
      exact degree_partition_ge3 (degree G v) (hmin v)
    calc
      ∑ v in Finset.univ,
          ((if degree G v = 3 then 1 else 0) +
           (if degree G v = 4 then 1 else 0) +
           (if degree G v = 5 then 1 else 0) +
           (if degree G v = 6 then 1 else 0) +
           (if 7 ≤ degree G v then 1 else 0))
          = ∑ _v in Finset.univ, (1 : Nat) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              simpa using hpoint v
      _ = n := by
          simp
  simpa [hsum] using hsum'

lemma v_sum_eq_n_q {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) = (n : ℚ) := by
  exact_mod_cast (v_sum_eq_n (G := G) hmin)

lemma mul_degEqCount_eq_sum {n : ℕ} (G : Finset (Segment n)) (k a : Nat) :
    a * degEqCount G k =
      ∑ v in Finset.univ, (if degree G v = k then a else 0) := by
  classical
  calc
    a * degEqCount G k =
        a * ∑ v in Finset.univ, (if degree G v = k then 1 else 0) := by
          rfl
    _ = ∑ v in Finset.univ, a * (if degree G v = k then 1 else 0) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun v : Fin n => if degree G v = k then 1 else 0) (a := a))
    _ = ∑ v in Finset.univ, (if degree G v = k then a else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          by_cases h : degree G v = k <;> simp [h]

lemma mul_degGeCount_eq_sum {n : ℕ} (G : Finset (Segment n)) (k a : Nat) :
    a * degGeCount G k =
      ∑ v in Finset.univ, (if k ≤ degree G v then a else 0) := by
  classical
  calc
    a * degGeCount G k =
        a * ∑ v in Finset.univ, (if k ≤ degree G v then 1 else 0) := by
          rfl
    _ = ∑ v in Finset.univ, a * (if k ≤ degree G v then 1 else 0) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun v : Fin n => if k ≤ degree G v then 1 else 0) (a := a))
    _ = ∑ v in Finset.univ, (if k ≤ degree G v then a else 0) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          by_cases h : k ≤ degree G v <;> simp [h]

lemma sum_adjacentDegCountQ_eq_mul {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    (∑ v in Finset.univ, adjacentDegCountQ G v k) =
      (k : ℚ) * (degEqCount G k : ℚ) := by
  classical
  have hinner :
      ∀ u,
        ∑ v in Finset.univ,
            (if adjacent G v u ∧ degree G u = k then (1 : ℚ) else 0) =
          if degree G u = k then adjacentCountQ G u else 0 := by
    intro u
    by_cases hdeg : degree G u = k
    ·
      have h1 :
          ∑ v in Finset.univ,
              (if adjacent G v u ∧ degree G u = k then (1 : ℚ) else 0) =
            ∑ v in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro v _
        by_cases hadj : adjacent G v u
        · simp [hadj, hdeg]
        · simp [hadj, hdeg]
      have h2 :
          ∑ v in Finset.univ, (if adjacent G v u then (1 : ℚ) else 0) =
            adjacentCountQ G u := by
        refine Finset.sum_congr rfl ?_
        intro v _
        by_cases hadj : adjacent G v u
        ·
          have hadj' : adjacent G u v := (adjacent_symm).1 hadj
          simp [adjacentCountQ, hadj, hadj']
        ·
          have hadj' : ¬ adjacent G u v := by
            intro h
            exact hadj ((adjacent_symm).2 h)
          simp [adjacentCountQ, hadj, hadj']
      simpa [hdeg] using h1.trans h2
    · simp [hdeg]
  have hsum' :
      ∑ v in Finset.univ, adjacentDegCountQ G v k =
        ∑ u in Finset.univ, (if degree G u = k then adjacentCountQ G u else 0) := by
    calc
      ∑ v in Finset.univ, adjacentDegCountQ G v k
          = ∑ v in Finset.univ, ∑ u in Finset.univ,
              (if adjacent G v u ∧ degree G u = k then (1 : ℚ) else 0) := by
                simp [adjacentDegCountQ]
      _ = ∑ u in Finset.univ, ∑ v in Finset.univ,
            (if adjacent G v u ∧ degree G u = k then (1 : ℚ) else 0) := by
              exact Finset.sum_comm
      _ = ∑ u in Finset.univ, (if degree G u = k then adjacentCountQ G u else 0) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            exact hinner u
  have hsum'' :
      ∑ u in Finset.univ, (if degree G u = k then adjacentCountQ G u else 0) =
        ∑ u in Finset.univ, (if degree G u = k then (degree G u : ℚ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro u _
    by_cases hdeg : degree G u = k
    · simp [hdeg, adjacentCountQ_eq_degree (G := G) (v := u)]
    · simp [hdeg]
  have hsumk :
      (k : ℚ) * (degEqCount G k : ℚ) =
        ∑ u in Finset.univ, (if degree G u = k then (k : ℚ) else 0) := by
    exact_mod_cast (mul_degEqCount_eq_sum (G := G) (k := k) (a := k))
  calc
    ∑ v in Finset.univ, adjacentDegCountQ G v k
        = ∑ u in Finset.univ, (if degree G u = k then adjacentCountQ G u else 0) := hsum'
    _ = ∑ u in Finset.univ, (if degree G u = k then (degree G u : ℚ) else 0) := hsum''
    _ = ∑ u in Finset.univ, (if degree G u = k then (k : ℚ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u _
          by_cases hdeg : degree G u = k
          · simp [hdeg]
          · simp [hdeg]
    _ = (k : ℚ) * (degEqCount G k : ℚ) := by
          symm
          exact hsumk

lemma degGeSum_ge {n : ℕ} (G : Finset (Segment n)) (k : Nat) :
    k * degGeCount G k ≤ degGeSum G k := by
  classical
  have hsum :
      k * degGeCount G k =
        ∑ v in Finset.univ, (if k ≤ degree G v then k else 0) := by
    simpa using (mul_degGeCount_eq_sum (G := G) (k := k) (a := k))
  have hsum_le :
      ∑ v in Finset.univ, (if k ≤ degree G v then k else 0)
        ≤ ∑ v in Finset.univ, (if k ≤ degree G v then degree G v else 0) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    by_cases h : k ≤ degree G v
    · simp [h, h]
    · simp [h]
  calc
    k * degGeCount G k
        = ∑ v in Finset.univ, (if k ≤ degree G v then k else 0) := hsum
    _ ≤ ∑ v in Finset.univ, (if k ≤ degree G v then degree G v else 0) := hsum_le
    _ = degGeSum G k := by rfl

lemma sumLarge_ge {n : ℕ} (G : Finset (Segment n)) :
    7 * vL G ≤ sumLarge G := by
  simpa [vL, sumLarge] using (degGeSum_ge (G := G) (k := 7))

lemma sumLarge_ge_q {n : ℕ} (G : Finset (Segment n)) :
    (7 : ℚ) * (vL G : ℚ) ≤ (sumLarge G : ℚ) := by
  exact_mod_cast (sumLarge_ge (G := G))

lemma degree_ge_split (d : Nat) :
    (if d = 3 then 3 else 0) +
        (if d = 4 then 4 else 0) +
        (if d = 5 then 5 else 0) +
        (if d = 6 then 6 else 0) +
        (if 7 ≤ d then d else 0) ≤ d := by
  by_cases h7 : 7 ≤ d
  ·
    have h3 : d ≠ 3 := by
      have : (3 : Nat) < d := lt_of_lt_of_le (by decide : 3 < 7) h7
      exact ne_of_gt this
    have h4 : d ≠ 4 := by
      have : (4 : Nat) < d := lt_of_lt_of_le (by decide : 4 < 7) h7
      exact ne_of_gt this
    have h5 : d ≠ 5 := by
      have : (5 : Nat) < d := lt_of_lt_of_le (by decide : 5 < 7) h7
      exact ne_of_gt this
    have h6 : d ≠ 6 := by
      have : (6 : Nat) < d := lt_of_lt_of_le (by decide : 6 < 7) h7
      exact ne_of_gt this
    simpa [h7, h3, h4, h5, h6] using (le_rfl : d ≤ d)
  ·
    have hlt : d < 7 := Nat.lt_of_not_ge h7
    have hle : d ≤ 6 := Nat.lt_succ_iff.mp hlt
    interval_cases d <;> simp

lemma degree_split_eq (d : Nat) (h : 3 ≤ d) :
    (if d = 3 then 3 else 0) +
        (if d = 4 then 4 else 0) +
        (if d = 5 then 5 else 0) +
        (if d = 6 then 6 else 0) +
        (if 7 ≤ d then d else 0) = d := by
  by_cases h7 : 7 ≤ d
  ·
    have h3 : d ≠ 3 := by
      have : (3 : Nat) < d := lt_of_lt_of_le (by decide : 3 < 7) h7
      exact ne_of_gt this
    have h4 : d ≠ 4 := by
      have : (4 : Nat) < d := lt_of_lt_of_le (by decide : 4 < 7) h7
      exact ne_of_gt this
    have h5 : d ≠ 5 := by
      have : (5 : Nat) < d := lt_of_lt_of_le (by decide : 5 < 7) h7
      exact ne_of_gt this
    have h6 : d ≠ 6 := by
      have : (6 : Nat) < d := lt_of_lt_of_le (by decide : 6 < 7) h7
      exact ne_of_gt this
    simp [h7, h3, h4, h5, h6]
  ·
    have hlt : d < 7 := Nat.lt_of_not_ge h7
    have hle : d ≤ 6 := Nat.lt_succ_iff.mp hlt
    interval_cases d <;> simp at h <;> simp
lemma degreeSum_ge_weighted_counts {n : ℕ} (G : Finset (Segment n)) :
    3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G ≤ degreeSum G := by
  classical
  have hsum :
      3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G =
        ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then 7 else 0)) := by
    simp [v3, v4, v5, v6, vL, mul_degEqCount_eq_sum, mul_degGeCount_eq_sum,
      Finset.sum_add_distrib]
  have hsum_le :
      ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then 7 else 0))
        ≤ ∑ v in Finset.univ, degree G v := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact degree_ge_weighted (degree G v)
  have hsum_def : ∑ v in Finset.univ, degree G v = degreeSum G := by
    simp [degreeSum]
  calc
    3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G
        = ∑ v in Finset.univ,
            ((if degree G v = 3 then 3 else 0) +
             (if degree G v = 4 then 4 else 0) +
             (if degree G v = 5 then 5 else 0) +
             (if degree G v = 6 then 6 else 0) +
             (if 7 ≤ degree G v then 7 else 0)) := hsum
    _ ≤ ∑ v in Finset.univ, degree G v := hsum_le
    _ = degreeSum G := hsum_def

lemma degreeSum_ge_split {n : ℕ} (G : Finset (Segment n)) :
    3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G ≤ degreeSum G := by
  classical
  have hv3 :
      3 * v3 G = ∑ v in Finset.univ, (if degree G v = 3 then 3 else 0) := by
    simpa [v3] using (mul_degEqCount_eq_sum (G := G) (k := 3) (a := 3))
  have hv4 :
      4 * v4 G = ∑ v in Finset.univ, (if degree G v = 4 then 4 else 0) := by
    simpa [v4] using (mul_degEqCount_eq_sum (G := G) (k := 4) (a := 4))
  have hv5 :
      5 * v5 G = ∑ v in Finset.univ, (if degree G v = 5 then 5 else 0) := by
    simpa [v5] using (mul_degEqCount_eq_sum (G := G) (k := 5) (a := 5))
  have hv6 :
      6 * v6 G = ∑ v in Finset.univ, (if degree G v = 6 then 6 else 0) := by
    simpa [v6] using (mul_degEqCount_eq_sum (G := G) (k := 6) (a := 6))
  have hlarge :
      sumLarge G = ∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0) := by
    rfl
  have hsum' :
      ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then degree G v else 0)) =
        (∑ v in Finset.univ, (if degree G v = 3 then 3 else 0)) +
        (∑ v in Finset.univ, (if degree G v = 4 then 4 else 0)) +
        (∑ v in Finset.univ, (if degree G v = 5 then 5 else 0)) +
        (∑ v in Finset.univ, (if degree G v = 6 then 6 else 0)) +
        (∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0)) := by
    simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
  have hsum :
      3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G =
        ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then degree G v else 0)) := by
    calc
      3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G
          = (∑ v in Finset.univ, (if degree G v = 3 then 3 else 0)) +
            (∑ v in Finset.univ, (if degree G v = 4 then 4 else 0)) +
            (∑ v in Finset.univ, (if degree G v = 5 then 5 else 0)) +
            (∑ v in Finset.univ, (if degree G v = 6 then 6 else 0)) +
            (∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0)) := by
              simp [hv3, hv4, hv5, hv6, hlarge, add_assoc, add_left_comm, add_comm]
      _ = ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then degree G v else 0)) := by
              symm
              exact hsum'
  have hsum_le :
      ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then degree G v else 0))
        ≤ ∑ v in Finset.univ, degree G v := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact degree_ge_split (degree G v)
  have hsum_def : ∑ v in Finset.univ, degree G v = degreeSum G := by
    simp [degreeSum]
  calc
    3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G
        = ∑ v in Finset.univ,
            ((if degree G v = 3 then 3 else 0) +
             (if degree G v = 4 then 4 else 0) +
             (if degree G v = 5 then 5 else 0) +
             (if degree G v = 6 then 6 else 0) +
             (if 7 ≤ degree G v then degree G v else 0)) := hsum
    _ ≤ ∑ v in Finset.univ, degree G v := hsum_le
    _ = degreeSum G := hsum_def

lemma degreeSum_eq_split {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    degreeSum G = 3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G := by
  classical
  have hsum :
      3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G =
        ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then degree G v else 0)) := by
    have hv3 :
        3 * v3 G = ∑ v in Finset.univ, (if degree G v = 3 then 3 else 0) := by
      simpa [v3] using (mul_degEqCount_eq_sum (G := G) (k := 3) (a := 3))
    have hv4 :
        4 * v4 G = ∑ v in Finset.univ, (if degree G v = 4 then 4 else 0) := by
      simpa [v4] using (mul_degEqCount_eq_sum (G := G) (k := 4) (a := 4))
    have hv5 :
        5 * v5 G = ∑ v in Finset.univ, (if degree G v = 5 then 5 else 0) := by
      simpa [v5] using (mul_degEqCount_eq_sum (G := G) (k := 5) (a := 5))
    have hv6 :
        6 * v6 G = ∑ v in Finset.univ, (if degree G v = 6 then 6 else 0) := by
      simpa [v6] using (mul_degEqCount_eq_sum (G := G) (k := 6) (a := 6))
    have hlarge :
        sumLarge G = ∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0) := by
      rfl
    have hsum' :
        ∑ v in Finset.univ,
            ((if degree G v = 3 then 3 else 0) +
             (if degree G v = 4 then 4 else 0) +
             (if degree G v = 5 then 5 else 0) +
             (if degree G v = 6 then 6 else 0) +
             (if 7 ≤ degree G v then degree G v else 0)) =
          (∑ v in Finset.univ, (if degree G v = 3 then 3 else 0)) +
          (∑ v in Finset.univ, (if degree G v = 4 then 4 else 0)) +
          (∑ v in Finset.univ, (if degree G v = 5 then 5 else 0)) +
          (∑ v in Finset.univ, (if degree G v = 6 then 6 else 0)) +
          (∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0)) := by
      simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    calc
      3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G
          = (∑ v in Finset.univ, (if degree G v = 3 then 3 else 0)) +
            (∑ v in Finset.univ, (if degree G v = 4 then 4 else 0)) +
            (∑ v in Finset.univ, (if degree G v = 5 then 5 else 0)) +
            (∑ v in Finset.univ, (if degree G v = 6 then 6 else 0)) +
            (∑ v in Finset.univ, (if 7 ≤ degree G v then degree G v else 0)) := by
              simp [hv3, hv4, hv5, hv6, hlarge, add_assoc, add_left_comm, add_comm]
      _ = ∑ v in Finset.univ,
          ((if degree G v = 3 then 3 else 0) +
           (if degree G v = 4 then 4 else 0) +
           (if degree G v = 5 then 5 else 0) +
           (if degree G v = 6 then 6 else 0) +
           (if 7 ≤ degree G v then degree G v else 0)) := by
              symm
              exact hsum'
  have hsum_deg :
      ∑ v in Finset.univ,
        ((if degree G v = 3 then 3 else 0) +
         (if degree G v = 4 then 4 else 0) +
         (if degree G v = 5 then 5 else 0) +
         (if degree G v = 6 then 6 else 0) +
         (if 7 ≤ degree G v then degree G v else 0))
        = ∑ v in Finset.univ, degree G v := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    exact degree_split_eq (degree G v) (hmin v)
  have hsum_def : ∑ v in Finset.univ, degree G v = degreeSum G := by
    simp [degreeSum]
  calc
    degreeSum G = ∑ v in Finset.univ, degree G v := by
      symm
      exact hsum_def
    _ = ∑ v in Finset.univ,
        ((if degree G v = 3 then 3 else 0) +
         (if degree G v = 4 then 4 else 0) +
         (if degree G v = 5 then 5 else 0) +
         (if degree G v = 6 then 6 else 0) +
         (if 7 ≤ degree G v then degree G v else 0)) := by
      symm
      exact hsum_deg
    _ = 3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G := by
      symm
      exact hsum

lemma sumLarge_eq_degreeSum_sub {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    sumLarge G = degreeSum G - (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G) := by
  have hsplit : degreeSum G = 3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G :=
    degreeSum_eq_split (G := G) hmin
  calc
    sumLarge G = (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G) -
        (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G) := by
          simp [Nat.add_sub_cancel_left, Nat.add_sub_cancel]
    _ = degreeSum G - (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G) := by
          simpa [hsplit]

lemma degreeSum_eq_twice_card_q {n : ℕ} (G : Finset (Segment n)) :
    (degreeSum G : ℚ) = 2 * (G.card : ℚ) := by
  exact_mod_cast (degreeSum_eq_twice_card (G := G))

lemma degreeSum_eq_sixn_minus12_q {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6) :
    (degreeSum G : ℚ) = 6 * (n : ℚ) - 12 := by
  calc
    (degreeSum G : ℚ) = 2 * (G.card : ℚ) := degreeSum_eq_twice_card_q (G := G)
    _ = 2 * (3 * (n : ℚ) - 6) := by simpa [hcard]
    _ = 6 * (n : ℚ) - 12 := by ring

lemma sumLarge_eq_q {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hsum : (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) = (n : ℚ)) :
    (sumLarge G : ℚ) =
      3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) + 6 * (vL G : ℚ) - 12 := by
  have hdeg :
      (degreeSum G : ℚ) = 6 * (n : ℚ) - 12 :=
    degreeSum_eq_sixn_minus12_q (G := G) hcard
  have hsplit :
      (degreeSum G : ℚ) =
        (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G : ℚ) := by
    exact_mod_cast (degreeSum_eq_split (G := G) hmin)
  have hsum' :
      6 * (n : ℚ) - 12 =
        (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + sumLarge G : ℚ) := by
    simpa [hdeg] using hsplit
  have hrewrite :
      (sumLarge G : ℚ) =
        6 * (n : ℚ) - 12 -
          (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G : ℚ) := by
    linarith [hsum']
  calc
    (sumLarge G : ℚ) =
        6 * (n : ℚ) - 12 -
          (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G : ℚ) := hrewrite
    _ = 3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) + 6 * (vL G : ℚ) - 12 := by
      calc
        6 * (n : ℚ) - 12 -
            (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G : ℚ)
            = 6 * (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) - 12 -
                (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G : ℚ) := by
                  simpa [hsum]
        _ = 3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) + 6 * (vL G : ℚ) - 12 := by
                  ring

lemma sumLargeExcess_eq_q {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hsum : (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) = (n : ℚ)) :
    (sumLargeExcess G : ℚ) =
      3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) - (vL G : ℚ) - 12 := by
  have hsumLarge := sumLarge_eq_q (G := G) hcard hmin hsum
  have hle : 7 * vL G ≤ sumLarge G := sumLarge_ge (G := G)
  have hcast' :
      ((sumLarge G - 7 * vL G : Nat) : ℚ) =
        (sumLarge G : ℚ) - ((7 * vL G : Nat) : ℚ) := by
    exact (Nat.cast_sub (R := ℚ) hle)
  have hmul : ((7 * vL G : Nat) : ℚ) = 7 * (vL G : ℚ) := by
    simpa using (Nat.cast_mul (R := ℚ) 7 (vL G))
  have hcast :
      ((sumLarge G - 7 * vL G : Nat) : ℚ) =
        (sumLarge G : ℚ) - 7 * (vL G : ℚ) := by
    simpa [hmul] using hcast'
  have hdef : (sumLargeExcess G : ℚ) = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := by
    -- Cast the natural subtraction using the lower bound on sumLarge.
    calc
      (sumLargeExcess G : ℚ) = ((sumLarge G - 7 * vL G : Nat) : ℚ) := by
        simp [sumLargeExcess]
      _ = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := hcast
  calc
    (sumLargeExcess G : ℚ)
        = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := hdef
    _ = 3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) + 6 * (vL G : ℚ) - 12 -
          7 * (vL G : ℚ) := by simpa [hsumLarge]
    _ = 3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) - (vL G : ℚ) - 12 := by
          ring

lemma sumLargeExcess_eq_sum_excess_q {n : ℕ} (G : Finset (Segment n)) :
    (sumLargeExcess G : ℚ) =
      ∑ v in Finset.univ, deg56Excess G v := by
  classical
  have hle : 7 * vL G ≤ sumLarge G := sumLarge_ge (G := G)
  have hcast' :
      ((sumLarge G - 7 * vL G : Nat) : ℚ) =
        (sumLarge G : ℚ) - ((7 * vL G : Nat) : ℚ) := by
    exact (Nat.cast_sub (R := ℚ) hle)
  have hmul : ((7 * vL G : Nat) : ℚ) = 7 * (vL G : ℚ) := by
    simpa using (Nat.cast_mul (R := ℚ) 7 (vL G))
  have hdef : (sumLargeExcess G : ℚ) = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := by
    calc
      (sumLargeExcess G : ℚ) = ((sumLarge G - 7 * vL G : Nat) : ℚ) := by
        simp [sumLargeExcess]
      _ = (sumLarge G : ℚ) - ((7 * vL G : Nat) : ℚ) := hcast'
      _ = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := by simpa [hmul]
  have hsumLarge :
      (sumLarge G : ℚ) =
        ∑ v in Finset.univ, (if 7 ≤ degree G v then (degree G v : ℚ) else 0) := by
    simpa [sumLarge, degGeSum] using
      (Nat.cast_sum (s := Finset.univ)
        (f := fun v => if 7 ≤ degree G v then degree G v else 0))
  have hvL :
      (vL G : ℚ) =
        ∑ v in Finset.univ, (if 7 ≤ degree G v then (1 : ℚ) else 0) := by
    simpa [vL, degGeCount] using
      (Nat.cast_sum (s := Finset.univ)
        (f := fun v => if 7 ≤ degree G v then 1 else 0))
  have hmulv :
      7 * (vL G : ℚ) =
        ∑ v in Finset.univ, (if 7 ≤ degree G v then (7 : ℚ) else 0) := by
    calc
      7 * (vL G : ℚ)
          = 7 * ∑ v in Finset.univ, (if 7 ≤ degree G v then (1 : ℚ) else 0) := by
              rw [hvL]
      _ = ∑ v in Finset.univ, (7 * (if 7 ≤ degree G v then (1 : ℚ) else 0)) := by
            exact (Finset.mul_sum (s := Finset.univ)
              (f := fun v => if 7 ≤ degree G v then (1 : ℚ) else 0) (a := (7 : ℚ)))
      _ = ∑ v in Finset.univ, (if 7 ≤ degree G v then (7 : ℚ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro v _
            by_cases h : 7 ≤ degree G v
            · simp [h]
            · simp [h]
  have hdiff :
      (sumLarge G : ℚ) - 7 * (vL G : ℚ) =
        ∑ v in Finset.univ,
          ((if 7 ≤ degree G v then (degree G v : ℚ) else 0) -
            (if 7 ≤ degree G v then (7 : ℚ) else 0)) := by
    calc
      (sumLarge G : ℚ) - 7 * (vL G : ℚ)
          = ∑ v in Finset.univ, (if 7 ≤ degree G v then (degree G v : ℚ) else 0) -
            ∑ v in Finset.univ, (if 7 ≤ degree G v then (7 : ℚ) else 0) := by
                simpa [hsumLarge, hmulv]
      _ = ∑ v in Finset.univ,
            ((if 7 ≤ degree G v then (degree G v : ℚ) else 0) -
              (if 7 ≤ degree G v then (7 : ℚ) else 0)) := by
            simpa [Finset.sum_sub_distrib]
  calc
    (sumLargeExcess G : ℚ)
        = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := hdef
    _ = ∑ v in Finset.univ,
          ((if 7 ≤ degree G v then (degree G v : ℚ) else 0) -
            (if 7 ≤ degree G v then (7 : ℚ) else 0)) := hdiff
    _ = ∑ v in Finset.univ, deg56Excess G v := by
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases h : 7 ≤ degree G v
          · simp [deg56Excess, h]
          · simp [deg56Excess, h]

lemma sumLargeExcess_eq_sumLarge_sub_q {n : ℕ} (G : Finset (Segment n)) :
    (sumLargeExcess G : ℚ) = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := by
  classical
  have hle : 7 * vL G ≤ sumLarge G := sumLarge_ge (G := G)
  have hcast' :
      ((sumLarge G - 7 * vL G : Nat) : ℚ) =
        (sumLarge G : ℚ) - ((7 * vL G : Nat) : ℚ) := by
    exact (Nat.cast_sub (R := ℚ) hle)
  have hmul : ((7 * vL G : Nat) : ℚ) = 7 * (vL G : ℚ) := by
    simpa using (Nat.cast_mul (R := ℚ) 7 (vL G))
  calc
    (sumLargeExcess G : ℚ) = ((sumLarge G - 7 * vL G : Nat) : ℚ) := by
      simp [sumLargeExcess]
    _ = (sumLarge G : ℚ) - ((7 * vL G : Nat) : ℚ) := hcast'
    _ = (sumLarge G : ℚ) - 7 * (vL G : ℚ) := by simpa [hmul]

lemma sum_deg56Debt_eq_counts {n : ℕ} (G : Finset (Segment n)) :
    ∑ v in Finset.univ, deg56Debt G v =
      (33 / 4 : ℚ) * (degEqCount G 3 : ℚ) + (5 / 4 : ℚ) * (degEqCount G 4 : ℚ) -
        (11 / 4 : ℚ) * (degEqCount G 5 : ℚ) - (21 / 4 : ℚ) * (degEqCount G 6 : ℚ) -
        (7 : ℚ) * (degGeCount G 7 : ℚ) := by
  classical
  have h3ind :
      ∑ v in Finset.univ, (if degree G v = 3 then (1 : ℚ) else 0) =
        (degEqCount G 3 : ℚ) := by
    have h3nat :
        degEqCount G 3 = ∑ v in Finset.univ, (if degree G v = 3 then 1 else 0) := by
      simpa using (mul_degEqCount_eq_sum (G := G) (k := 3) (a := 1))
    exact_mod_cast h3nat.symm
  have h4ind :
      ∑ v in Finset.univ, (if degree G v = 4 then (1 : ℚ) else 0) =
        (degEqCount G 4 : ℚ) := by
    have h4nat :
        degEqCount G 4 = ∑ v in Finset.univ, (if degree G v = 4 then 1 else 0) := by
      simpa using (mul_degEqCount_eq_sum (G := G) (k := 4) (a := 1))
    exact_mod_cast h4nat.symm
  have h5ind :
      ∑ v in Finset.univ, (if degree G v = 5 then (1 : ℚ) else 0) =
        (degEqCount G 5 : ℚ) := by
    have h5nat :
        degEqCount G 5 = ∑ v in Finset.univ, (if degree G v = 5 then 1 else 0) := by
      simpa using (mul_degEqCount_eq_sum (G := G) (k := 5) (a := 1))
    exact_mod_cast h5nat.symm
  have h6ind :
      ∑ v in Finset.univ, (if degree G v = 6 then (1 : ℚ) else 0) =
        (degEqCount G 6 : ℚ) := by
    have h6nat :
        degEqCount G 6 = ∑ v in Finset.univ, (if degree G v = 6 then 1 else 0) := by
      simpa using (mul_degEqCount_eq_sum (G := G) (k := 6) (a := 1))
    exact_mod_cast h6nat.symm
  have hLind :
      ∑ v in Finset.univ, (if 7 ≤ degree G v then (1 : ℚ) else 0) =
        (degGeCount G 7 : ℚ) := by
    have hLnat :
        degGeCount G 7 = ∑ v in Finset.univ, (if 7 ≤ degree G v then 1 else 0) := by
      simpa using (mul_degGeCount_eq_sum (G := G) (k := 7) (a := 1))
    exact_mod_cast hLnat.symm
  have h3c :
      ∑ v in Finset.univ, (if degree G v = 3 then (33 / 4 : ℚ) else 0) =
        (33 / 4 : ℚ) * (degEqCount G 3 : ℚ) := by
    calc
      ∑ v in Finset.univ, (if degree G v = 3 then (33 / 4 : ℚ) else 0)
          = ∑ v in Finset.univ,
              (33 / 4 : ℚ) * (if degree G v = 3 then (1 : ℚ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro v _
                by_cases h : degree G v = 3 <;> simp [h]
      _ = (33 / 4 : ℚ) * ∑ v in Finset.univ,
            (if degree G v = 3 then (1 : ℚ) else 0) := by
              symm
              exact (Finset.mul_sum (s := Finset.univ)
                (f := fun v => if degree G v = 3 then (1 : ℚ) else 0) (a := (33 / 4 : ℚ)))
      _ = (33 / 4 : ℚ) * (degEqCount G 3 : ℚ) := by
            simp [h3ind]
  have h4c :
      ∑ v in Finset.univ, (if degree G v = 4 then (5 / 4 : ℚ) else 0) =
        (5 / 4 : ℚ) * (degEqCount G 4 : ℚ) := by
    calc
      ∑ v in Finset.univ, (if degree G v = 4 then (5 / 4 : ℚ) else 0)
          = ∑ v in Finset.univ,
              (5 / 4 : ℚ) * (if degree G v = 4 then (1 : ℚ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro v _
                by_cases h : degree G v = 4 <;> simp [h]
      _ = (5 / 4 : ℚ) * ∑ v in Finset.univ,
            (if degree G v = 4 then (1 : ℚ) else 0) := by
              symm
              exact (Finset.mul_sum (s := Finset.univ)
                (f := fun v => if degree G v = 4 then (1 : ℚ) else 0) (a := (5 / 4 : ℚ)))
      _ = (5 / 4 : ℚ) * (degEqCount G 4 : ℚ) := by
            simp [h4ind]
  have h5c :
      ∑ v in Finset.univ, (if degree G v = 5 then (-11 / 4 : ℚ) else 0) =
        (-11 / 4 : ℚ) * (degEqCount G 5 : ℚ) := by
    calc
      ∑ v in Finset.univ, (if degree G v = 5 then (-11 / 4 : ℚ) else 0)
          = ∑ v in Finset.univ,
              (-11 / 4 : ℚ) * (if degree G v = 5 then (1 : ℚ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro v _
                by_cases h : degree G v = 5 <;> simp [h]
      _ = (-11 / 4 : ℚ) * ∑ v in Finset.univ,
            (if degree G v = 5 then (1 : ℚ) else 0) := by
              symm
              exact (Finset.mul_sum (s := Finset.univ)
                (f := fun v => if degree G v = 5 then (1 : ℚ) else 0) (a := (-11 / 4 : ℚ)))
      _ = (-11 / 4 : ℚ) * (degEqCount G 5 : ℚ) := by
            simp [h5ind]
  have h6c :
      ∑ v in Finset.univ, (if degree G v = 6 then (-21 / 4 : ℚ) else 0) =
        (-21 / 4 : ℚ) * (degEqCount G 6 : ℚ) := by
    calc
      ∑ v in Finset.univ, (if degree G v = 6 then (-21 / 4 : ℚ) else 0)
          = ∑ v in Finset.univ,
              (-21 / 4 : ℚ) * (if degree G v = 6 then (1 : ℚ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro v _
                by_cases h : degree G v = 6 <;> simp [h]
      _ = (-21 / 4 : ℚ) * ∑ v in Finset.univ,
            (if degree G v = 6 then (1 : ℚ) else 0) := by
              symm
              exact (Finset.mul_sum (s := Finset.univ)
                (f := fun v => if degree G v = 6 then (1 : ℚ) else 0) (a := (-21 / 4 : ℚ)))
      _ = (-21 / 4 : ℚ) * (degEqCount G 6 : ℚ) := by
            simp [h6ind]
  have hLc :
      ∑ v in Finset.univ, (if 7 ≤ degree G v then (-7 : ℚ) else 0) =
        (-7 : ℚ) * (degGeCount G 7 : ℚ) := by
    calc
      ∑ v in Finset.univ, (if 7 ≤ degree G v then (-7 : ℚ) else 0)
          = ∑ v in Finset.univ,
              (-7 : ℚ) * (if 7 ≤ degree G v then (1 : ℚ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro v _
                by_cases h : 7 ≤ degree G v <;> simp [h]
      _ = (-7 : ℚ) * ∑ v in Finset.univ,
            (if 7 ≤ degree G v then (1 : ℚ) else 0) := by
              symm
              exact (Finset.mul_sum (s := Finset.univ)
                (f := fun v => if 7 ≤ degree G v then (1 : ℚ) else 0) (a := (-7 : ℚ)))
      _ = (-7 : ℚ) * (degGeCount G 7 : ℚ) := by
            simp [hLind]
  calc
    ∑ v in Finset.univ, deg56Debt G v =
        (∑ v in Finset.univ, (if degree G v = 3 then (33 / 4 : ℚ) else 0)) +
        (∑ v in Finset.univ, (if degree G v = 4 then (5 / 4 : ℚ) else 0)) +
        (∑ v in Finset.univ, (if degree G v = 5 then (-11 / 4 : ℚ) else 0)) +
        (∑ v in Finset.univ, (if degree G v = 6 then (-21 / 4 : ℚ) else 0)) +
        (∑ v in Finset.univ, (if 7 ≤ degree G v then (-7 : ℚ) else 0)) := by
          simp [deg56Debt, Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
    _ =
        (33 / 4 : ℚ) * (degEqCount G 3 : ℚ) + (5 / 4 : ℚ) * (degEqCount G 4 : ℚ) -
          (11 / 4 : ℚ) * (degEqCount G 5 : ℚ) - (21 / 4 : ℚ) * (degEqCount G 6 : ℚ) -
          (7 : ℚ) * (degGeCount G 7 : ℚ) := by
          simp [h3c, h4c, h5c, h6c, hLc]
          ring

lemma sum_deg56Debt_eq {n : ℕ} (G : Finset (Segment n)) :
    ∑ v in Finset.univ, deg56Debt G v =
      (33 / 4 : ℚ) * (v3 G : ℚ) + (5 / 4 : ℚ) * (v4 G : ℚ) -
        (11 / 4 : ℚ) * (v5 G : ℚ) - (21 / 4 : ℚ) * (v6 G : ℚ) -
        (7 : ℚ) * (vL G : ℚ) := by
  simpa [v3, v4, v5, v6, vL] using sum_deg56Debt_eq_counts (G := G)

lemma sum_deg56BalanceTerm_eq {n : ℕ} (G : Finset (Segment n)) :
    ∑ v in Finset.univ, deg56BalanceTerm G v =
      (sumLargeExcess G : ℚ) - ∑ v in Finset.univ, deg56Debt G v := by
  classical
  have hsumEx := sumLargeExcess_eq_sum_excess_q (G := G)
  calc
    ∑ v in Finset.univ, deg56BalanceTerm G v =
        ∑ v in Finset.univ, (deg56Excess G v - deg56Debt G v) := by
          rfl
    _ = ∑ v in Finset.univ, deg56Excess G v -
          ∑ v in Finset.univ, deg56Debt G v := by
          simpa [Finset.sum_sub_distrib]
    _ = (sumLargeExcess G : ℚ) - ∑ v in Finset.univ, deg56Debt G v := by
          simpa [hsumEx]

lemma deg56_sumLarge_iff_excess_debt {n : ℕ} (G : Finset (Segment n)) :
    4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57
      ↔ (sumLargeExcess G : ℚ) + (57 / 4 : ℚ) ≥
        ∑ v in Finset.univ, deg56Debt G v := by
  have hEx : (sumLargeExcess G : ℚ) = (sumLarge G : ℚ) - 7 * (vL G : ℚ) :=
    sumLargeExcess_eq_sumLarge_sub_q (G := G)
  have hDebt := sum_deg56Debt_eq (G := G)
  constructor
  · intro h
    have h' :
        4 * (sumLargeExcess G : ℚ) + 57 ≥
          4 * (∑ v in Finset.univ, deg56Debt G v) := by
      nlinarith [h, hEx, hDebt]
    nlinarith [h']
  · intro h
    have h' :
        4 * (sumLargeExcess G : ℚ) + 57 ≥
          4 * (∑ v in Finset.univ, deg56Debt G v) := by
      nlinarith [h]
    nlinarith [h', hEx, hDebt]

lemma deg56_sumLarge_iff_balance_terms {n : ℕ} (G : Finset (Segment n)) :
    4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57
      ↔ ∑ v in Finset.univ, deg56BalanceTerm G v ≥ -(57 / 4 : ℚ) := by
  have hiff := deg56_sumLarge_iff_excess_debt (G := G)
  have hsum := sum_deg56BalanceTerm_eq (G := G)
  constructor
  · intro h
    have h' := (hiff.mp h)
    have h'' :
        (sumLargeExcess G : ℚ) - ∑ v in Finset.univ, deg56Debt G v ≥ -(57 / 4 : ℚ) := by
      linarith [h']
    simpa [hsum] using h''
  · intro h
    have h' :
        (sumLargeExcess G : ℚ) - ∑ v in Finset.univ, deg56Debt G v ≥ -(57 / 4 : ℚ) := by
      simpa [hsum] using h
    have h'' :
        (sumLargeExcess G : ℚ) + (57 / 4 : ℚ) ≥ ∑ v in Finset.univ, deg56Debt G v := by
      linarith [h']
    exact hiff.mpr h''

lemma deg56_sumLarge_of_transfer {n : ℕ} (G : Finset (Segment n))
    (transfer : Fin n → Fin n → ℚ)
    (hanti : ∀ u v, transfer u v = - transfer v u)
    (lower : Fin n → ℚ)
    (hlower : ∀ v, deg56BalanceTerm G v + netTransfer transfer v ≥ lower v)
    (hsum : ∑ v in Finset.univ, lower v = -(57 / 4 : ℚ)) :
    4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57 := by
  have hbal :
      ∑ v in Finset.univ, deg56BalanceTerm G v ≥ -(57 / 4 : ℚ) := by
    have hge :=
      sum_balanceTerm_ge_of_transfer (G := G) (transfer := transfer)
        (hanti := hanti) (lower := lower) hlower
    simpa [hsum] using hge
  exact (deg56_sumLarge_iff_balance_terms (G := G)).2 hbal

lemma deg56_sumLarge_of_transfer_ge {n : ℕ} (G : Finset (Segment n))
    (transfer : Fin n → Fin n → ℚ)
    (hanti : ∀ u v, transfer u v = - transfer v u)
    (lower : Fin n → ℚ)
    (hlower : ∀ v, deg56BalanceTerm G v + netTransfer transfer v ≥ lower v)
    (hsum : ∑ v in Finset.univ, lower v ≥ -(57 / 4 : ℚ)) :
    4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57 := by
  have hge :
      ∑ v in Finset.univ, lower v ≤ ∑ v in Finset.univ, deg56BalanceTerm G v := by
    exact (sum_balanceTerm_ge_of_transfer (G := G) (transfer := transfer)
      (hanti := hanti) (lower := lower) hlower)
  have hsum' : (-(57 / 4 : ℚ)) ≤ ∑ v in Finset.univ, lower v := by
    linarith [hsum]
  have hbal : ∑ v in Finset.univ, deg56BalanceTerm G v ≥ -(57 / 4 : ℚ) := by
    exact le_trans hsum' hge
  exact (deg56_sumLarge_iff_balance_terms (G := G)).2 hbal

lemma deg56_balance_iff_sumLarge {v3 v4 v5 v6 vL sumLarge : ℚ}
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12) :
    (20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vL) ↔
      (sumLarge ≥ 23 * v3 - 2 * v4 - 15 * v5 - 22 * v6 - 19 * vL - 12) := by
  constructor
  · intro h
    linarith [hsumLarge, h]
  · intro h
    linarith [hsumLarge, h]

lemma deg56_balance_iff_linear {v3 v4 v5 v6 vL n : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n) :
    (20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vL) ↔
      (45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 25 * n) := by
  constructor
  · intro h
    linarith [hsum, h]
  · intro h
    linarith [hsum, h]

lemma deg56_shift_balance_iff_sumLarge {v3 v4 v5 v6 vL sumLarge : ℚ}
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12) :
    (22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vL) ↔
      (sumLarge ≥ 25 * v3 - 13 * v5 - 20 * v6 - 17 * vL - 12) := by
  constructor
  · intro h
    linarith [hsumLarge, h]
  · intro h
    linarith [hsumLarge, h]

lemma deg56_shift_balance_iff_linear {v3 v4 v5 v6 vL n : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n) :
    (22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vL) ↔
      (45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 23 * n) := by
  constructor
  · intro h
    linarith [hsum, h]
  · intro h
    linarith [hsum, h]

lemma deg56_balance_of_linear {v3 v4 v5 v6 vL n : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n)
    (hlin : 45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 25 * n) :
    20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vL := by
  exact (deg56_balance_iff_linear hsum).2 hlin

lemma deg56_shift_balance_of_linear {v3 v4 v5 v6 vL n : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n)
    (hlin : 45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 23 * n) :
    22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vL := by
  exact (deg56_shift_balance_iff_linear hsum).2 hlin

lemma deg56_n12_linear_of_small {v3 v4 v5 v6 n : ℚ}
    (hn : (12 : ℚ) ≤ n)
    (hlin : 15 * v3 + 7 * v4 + 3 * v5 + v6 ≤ 8 * n + 3) :
    60 * v3 + 28 * v4 + 12 * v5 + 4 * v6 ≤ 33 * n := by
  have h1 :
      60 * v3 + 28 * v4 + 12 * v5 + 4 * v6 ≤ 32 * n + 12 := by
    nlinarith [hlin]
  have h2 : 32 * n + 12 ≤ 33 * n := by
    nlinarith [hn]
  exact le_trans h1 h2

lemma deg56_linear8_iff_sumLarge {v3 v4 v5 v6 vL n sumLarge : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n)
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12) :
    (15 * v3 + 7 * v4 + 3 * v5 + v6 ≤ 8 * n + 3) ↔
      (4 * sumLarge ≥ 33 * v3 + 5 * v4 - 11 * v5 - 21 * v6 - 57) := by
  constructor
  · intro h
    linarith [hsum, hsumLarge, h]
  · intro h
    linarith [hsum, hsumLarge, h]

lemma deg56_linear8_iff_balance_simple {v3 v4 v5 v6 vL n : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n) :
    (15 * v3 + 7 * v4 + 3 * v5 + v6 ≤ 8 * n + 3) ↔
      (7 * v3 ≤ v4 + 5 * v5 + 7 * v6 + 8 * vL + 3) := by
  constructor
  · intro h
    linarith [hsum, h]
  · intro h
    linarith [hsum, h]

lemma deg56_sumLarge_iff_balance_simple {v3 v4 v5 v6 vL sumLarge : ℚ}
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12) :
    (4 * sumLarge ≥ 33 * v3 + 5 * v4 - 11 * v5 - 21 * v6 - 57) ↔
      (7 * v3 ≤ v4 + 5 * v5 + 7 * v6 + 8 * vL + 3) := by
  constructor
  · intro h
    linarith [hsumLarge, h]
  · intro h
    linarith [hsumLarge, h]

lemma deg56_linear8_of_sumLarge {v3 v4 v5 v6 vL n sumLarge : ℚ}
    (hsum : v3 + v4 + v5 + v6 + vL = n)
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12)
    (hlarge : 4 * sumLarge ≥ 33 * v3 + 5 * v4 - 11 * v5 - 21 * v6 - 57) :
    15 * v3 + 7 * v4 + 3 * v5 + v6 ≤ 8 * n + 3 := by
  exact (deg56_linear8_iff_sumLarge hsum hsumLarge).2 hlarge

lemma deg56_balance_of_sumLarge {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hsum : (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) = (n : ℚ))
    (hlarge :
      (sumLarge G : ℚ) ≥
        23 * (v3 G : ℚ) - 2 * (v4 G : ℚ) - 15 * (v5 G : ℚ) -
          22 * (v6 G : ℚ) - 19 * (vL G : ℚ) - 12) :
    20 * (v3 G : ℚ) ≤
      4 * (v4 G : ℚ) + 16 * (v5 G : ℚ) + 22 * (v6 G : ℚ) + 25 * (vL G : ℚ) := by
  have hsumLarge :=
    sumLarge_eq_q (G := G) hcard hmin hsum
  have hiff :=
    deg56_balance_iff_sumLarge (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
      (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
      (sumLarge := (sumLarge G : ℚ)) hsumLarge
  exact (hiff).2 hlarge

lemma deg56_shift_balance_of_sumLarge {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hsum : (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) = (n : ℚ))
    (hlarge :
      (sumLarge G : ℚ) ≥
        25 * (v3 G : ℚ) - 13 * (v5 G : ℚ) - 20 * (v6 G : ℚ) -
          17 * (vL G : ℚ) - 12) :
    22 * (v3 G : ℚ) ≤
      2 * (v4 G : ℚ) + 14 * (v5 G : ℚ) + 20 * (v6 G : ℚ) + 23 * (vL G : ℚ) := by
  have hsumLarge :=
    sumLarge_eq_q (G := G) hcard hmin hsum
  have hiff :=
    deg56_shift_balance_iff_sumLarge (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
      (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
      (sumLarge := (sumLarge G : ℚ)) hsumLarge
  exact (hiff).2 hlarge

lemma deg56_balance_of_sumLarge_graph {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hlarge :
      (sumLarge G : ℚ) ≥
        23 * (v3 G : ℚ) - 2 * (v4 G : ℚ) - 15 * (v5 G : ℚ) -
          22 * (v6 G : ℚ) - 19 * (vL G : ℚ) - 12) :
    20 * (v3 G : ℚ) ≤
      4 * (v4 G : ℚ) + 16 * (v5 G : ℚ) + 22 * (v6 G : ℚ) + 25 * (vL G : ℚ) := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  exact deg56_balance_of_sumLarge (G := G) hcard hmin hsum hlarge

lemma deg56_shift_balance_of_sumLarge_graph {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hlarge :
      (sumLarge G : ℚ) ≥
        25 * (v3 G : ℚ) - 13 * (v5 G : ℚ) - 20 * (v6 G : ℚ) -
          17 * (vL G : ℚ) - 12) :
    22 * (v3 G : ℚ) ≤
      2 * (v4 G : ℚ) + 14 * (v5 G : ℚ) + 20 * (v6 G : ℚ) + 23 * (vL G : ℚ) := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  exact deg56_shift_balance_of_sumLarge (G := G) hcard hmin hsum hlarge

lemma deg56_linear8_of_sumLarge_graph {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v)
    (hlarge :
      4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57) :
    15 * (v3 G : ℚ) + 7 * (v4 G : ℚ) + 3 * (v5 G : ℚ) + (v6 G : ℚ)
      ≤ 8 * (n : ℚ) + 3 := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  have hsumLarge := sumLarge_eq_q (G := G) hcard hmin hsum
  have hiff :=
    deg56_linear8_iff_sumLarge (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
      (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
      (n := (n : ℚ)) (sumLarge := (sumLarge G : ℚ)) hsum hsumLarge
  exact (hiff).2 hlarge

lemma deg56_balance_terms_iff_linear_graph {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hmin : ∀ v, 3 ≤ degree G v) :
    (∑ v in Finset.univ, deg56BalanceTerm G v ≥ -(57 / 4 : ℚ)) ↔
      (15 * (v3 G : ℚ) + 7 * (v4 G : ℚ) + 3 * (v5 G : ℚ) + (v6 G : ℚ)
        ≤ 8 * (n : ℚ) + 3) := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  have hsumLarge := sumLarge_eq_q (G := G) hcard hmin hsum
  have hiff1 := deg56_sumLarge_iff_balance_terms (G := G)
  have hiff2 :=
    deg56_linear8_iff_sumLarge (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
      (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
      (n := (n : ℚ)) (sumLarge := (sumLarge G : ℚ)) hsum hsumLarge
  constructor
  · intro hbal
    have hlarge : 4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57 := (hiff1).2 hbal
    exact (hiff2).2 hlarge
  · intro hlin
    have hlarge : 4 * (sumLarge G : ℚ) ≥
        33 * (v3 G : ℚ) + 5 * (v4 G : ℚ) - 11 * (v5 G : ℚ) -
          21 * (v6 G : ℚ) - 57 := (hiff2).1 hlin
    exact (hiff1).1 hlarge

lemma deg56_balance_simple_graph {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    (15 * (v3 G : ℚ) + 7 * (v4 G : ℚ) + 3 * (v5 G : ℚ) + (v6 G : ℚ)
        ≤ 8 * (n : ℚ) + 3) ↔
      (7 * (v3 G : ℚ) ≤
        (v4 G : ℚ) + 5 * (v5 G : ℚ) + 7 * (v6 G : ℚ) +
          8 * (vL G : ℚ) + 3) := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  simpa using
    (deg56_linear8_iff_balance_simple (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
      (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
      (n := (n : ℚ)) hsum)

lemma deg56_balance_iff_linear_graph {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    (20 * (v3 G : ℚ) ≤
        4 * (v4 G : ℚ) + 16 * (v5 G : ℚ) + 22 * (v6 G : ℚ) + 25 * (vL G : ℚ)) ↔
      (45 * (v3 G : ℚ) + 21 * (v4 G : ℚ) + 9 * (v5 G : ℚ) + 3 * (v6 G : ℚ)
          ≤ 25 * (n : ℚ)) := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  simpa using (deg56_balance_iff_linear (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
    (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
    (n := (n : ℚ)) hsum)

lemma deg56_balance_of_linear_graph {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v)
    (hlin :
      45 * (v3 G : ℚ) + 21 * (v4 G : ℚ) + 9 * (v5 G : ℚ) + 3 * (v6 G : ℚ)
        ≤ 25 * (n : ℚ)) :
    20 * (v3 G : ℚ) ≤
      4 * (v4 G : ℚ) + 16 * (v5 G : ℚ) + 22 * (v6 G : ℚ) + 25 * (vL G : ℚ) := by
  have hiff := deg56_balance_iff_linear_graph (G := G) hmin
  exact (hiff).2 hlin

lemma deg56_shift_balance_iff_linear_graph {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v) :
    (22 * (v3 G : ℚ) ≤
        2 * (v4 G : ℚ) + 14 * (v5 G : ℚ) + 20 * (v6 G : ℚ) + 23 * (vL G : ℚ)) ↔
      (45 * (v3 G : ℚ) + 21 * (v4 G : ℚ) + 9 * (v5 G : ℚ) + 3 * (v6 G : ℚ)
          ≤ 23 * (n : ℚ)) := by
  have hsum := v_sum_eq_n_q (G := G) hmin
  simpa using (deg56_shift_balance_iff_linear (v3 := (v3 G : ℚ)) (v4 := (v4 G : ℚ))
    (v5 := (v5 G : ℚ)) (v6 := (v6 G : ℚ)) (vL := (vL G : ℚ))
    (n := (n : ℚ)) hsum)

lemma deg56_shift_balance_of_linear_graph {n : ℕ} (G : Finset (Segment n))
    (hmin : ∀ v, 3 ≤ degree G v)
    (hlin :
      45 * (v3 G : ℚ) + 21 * (v4 G : ℚ) + 9 * (v5 G : ℚ) + 3 * (v6 G : ℚ)
        ≤ 23 * (n : ℚ)) :
    22 * (v3 G : ℚ) ≤
      2 * (v4 G : ℚ) + 14 * (v5 G : ℚ) + 20 * (v6 G : ℚ) + 23 * (vL G : ℚ) := by
  have hiff := deg56_shift_balance_iff_linear_graph (G := G) hmin
  exact (hiff).2 hlin

lemma euler_balance_lower_of_sumLarge {v3 v4 v5 vL sumLarge : ℚ}
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12)
    (hlarge : 7 * vL ≤ sumLarge) :
    12 ≤ 3 * v3 + 2 * v4 + v5 - vL := by
  have h' : 7 * vL ≤ 3 * v3 + 2 * v4 + v5 + 6 * vL - 12 := by
    simpa [hsumLarge] using hlarge
  linarith [h']

lemma euler_balance_lower {n : ℕ} (G : Finset (Segment n))
    (hcard : (G.card : ℚ) = 3 * (n : ℚ) - 6)
    (hsum : (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) = (n : ℚ)) :
    12 ≤
      3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) - (vL G : ℚ) := by
  have hdeg :
      (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ)
        ≤ (degreeSum G : ℚ) := by
    exact_mod_cast (degreeSum_ge_weighted_counts (G := G))
  have hdeg' :
      (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ)
        ≤ 6 * (n : ℚ) - 12 := by
    calc
      (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ)
          ≤ (degreeSum G : ℚ) := hdeg
      _ = 6 * (n : ℚ) - 12 := degreeSum_eq_sixn_minus12_q (G := G) hcard
  have h12 :
      12 ≤ 6 * (n : ℚ) -
        (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ) := by
    linarith [hdeg']
  have hrewrite :
      6 * (n : ℚ) -
        (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ)
          = 3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) - (vL G : ℚ) := by
    calc
      6 * (n : ℚ) -
          (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ)
          = 6 * (v3 G + v4 G + v5 G + v6 G + vL G : ℚ) -
              (3 * v3 G + 4 * v4 G + 5 * v5 G + 6 * v6 G + 7 * vL G : ℚ) := by
              simpa [hsum]
      _ = 3 * (v3 G : ℚ) + 2 * (v4 G : ℚ) + (v5 G : ℚ) - (vL G : ℚ) := by
              ring
  simpa [hrewrite] using h12

end PlaneGraphs

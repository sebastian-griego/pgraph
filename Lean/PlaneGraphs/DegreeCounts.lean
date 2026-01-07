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

lemma card_filter_eq_sum_ite {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x in s, (if p x then 1 else 0) := by
  classical
  simpa using (Finset.card_filter (p := p) (s := s))

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

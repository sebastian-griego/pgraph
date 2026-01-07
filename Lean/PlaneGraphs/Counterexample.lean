import PlaneGraphs.Basic

namespace PlaneGraphs

lemma segment_empty_one : IsEmpty (Segment 1) := by
  classical
  refine ⟨?_⟩
  intro s
  cases' s with s hs
  revert hs
  refine Sym2.inductionOn s ?_
  intro a b hs
  have hEq : a = b := Subsingleton.elim a b
  apply hs
  exact (Sym2.mk_isDiag_iff).2 hEq

lemma pg_one (P : PointSet 1) : pg P = 1 := by
  classical
  have hseg : (Finset.univ : Finset (Segment 1)) = ∅ := by
    ext s
    exact (segment_empty_one.elim s)
  have hInd : isIndependent (crossingGraph P) (∅ : Finset (Segment 1)) := by
    intro u _ hu _ _
    have : False := (Finset.not_mem_empty u) hu
    exact this.elim
  have hplane : planeGraphs P = {∅} := by
    ext s
    have hs : s = (∅ : Finset (Segment 1)) := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x _
      exact (segment_empty_one.elim x)
    subst hs
    simp [planeGraphs, hseg, hInd]
  simp [pg, hplane]

lemma pg_le_pow_two_segments {n : ℕ} (P : PointSet n) :
    pg P ≤ 2 ^ Fintype.card (Segment n) := by
  classical
  have hcard :
      (planeGraphs P).card ≤
        (Finset.univ.powerset : Finset (Finset (Segment n))).card := by
    simpa [planeGraphs] using
      (Finset.card_filter_le
        (s := (Finset.univ.powerset))
        (p := fun s => isIndependent (crossingGraph P) s))
  have hpow :
      (Finset.univ.powerset : Finset (Finset (Segment n))).card =
        2 ^ Fintype.card (Segment n) := by
    simp
  simpa [pg, hpow] using hcard

lemma card_segment_five : Fintype.card (Segment 5) = 10 := by
  have h :
      Fintype.card (Segment 5) = Nat.choose 5 2 := by
    simpa [Segment] using (Sym2.card_subtype_not_diag (α := Fin 5))
  have h' : Nat.choose 5 2 = 10 := by
    decide
  exact h.trans h'

lemma pg_le_two_pow_ten (P : PointSet 5) : pg P ≤ 2 ^ 10 := by
  simpa [card_segment_five] using (pg_le_pow_two_segments (P := P))

lemma counterexample_23_32_n5 (P : PointSet 5) :
    (pg P : ℚ) < (583 / 25 : ℚ) ^ (5 : ℕ) := by
  have hpg : (pg P : ℚ) ≤ (2 : ℚ) ^ (10 : ℕ) := by
    exact_mod_cast (pg_le_two_pow_ten P)
  have hpow : (2 : ℚ) ^ (10 : ℕ) < (583 / 25 : ℚ) ^ (5 : ℕ) := by
    norm_num
  exact lt_of_le_of_lt hpg hpow

lemma counterexample_12_15_n5 (P : PointSet 5) :
    (pg P : ℚ) < (243 / 20 : ℚ) ^ (5 : ℕ) := by
  have hpg : (pg P : ℚ) ≤ (2 : ℚ) ^ (10 : ℕ) := by
    exact_mod_cast (pg_le_two_pow_ten P)
  have hpow : (2 : ℚ) ^ (10 : ℕ) < (243 / 20 : ℚ) ^ (5 : ℕ) := by
    norm_num
  exact lt_of_le_of_lt hpg hpow

def singlePoint : PointSet 1 :=
  fun _ => (0, 0)

def trianglePoints : PointSet 3 :=
  fun i =>
    match i.1 with
    | 0 => (0, 0)
    | 1 => (1, 0)
    | _ => (0, 1)

set_option linter.unnecessarySeqFocus false in
lemma pair_intersect_fin3 {a b c d : Fin 3} (hab : a ≠ b) (hcd : c ≠ d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp at hab hcd <;> try cases hab <;> try cases hcd <;> decide

lemma no_cross_triangle :
    ∀ s t : Segment 3, ¬ segmentCrosses trianglePoints s t := by
  classical
  intro s t
  cases' s with s hs
  cases' t with t ht
  revert hs ht
  refine Sym2.inductionOn₂ s t ?_
  intro a b c d hs ht hcross
  have hab : a ≠ b := by
    intro hEq
    apply hs
    exact (Sym2.mk_isDiag_iff).2 hEq
  have hcd : c ≠ d := by
    intro hEq
    apply ht
    exact (Sym2.mk_isDiag_iff).2 hEq
  have hshare : a = c ∨ a = d ∨ b = c ∨ b = d :=
    pair_intersect_fin3 hab hcd
  rcases hcross with ⟨hac, had, hbc, hbd, _, _, _, _, _, _⟩
  rcases hshare with h | h | h | h
  ·
    have hpc : trianglePoints a = trianglePoints c := by
      simpa using congrArg trianglePoints h
    exact (hac hpc).elim
  ·
    have hpd : trianglePoints a = trianglePoints d := by
      simpa using congrArg trianglePoints h
    exact (had hpd).elim
  ·
    have hpc : trianglePoints b = trianglePoints c := by
      simpa using congrArg trianglePoints h
    exact (hbc hpc).elim
  ·
    have hpd : trianglePoints b = trianglePoints d := by
      simpa using congrArg trianglePoints h
    exact (hbd hpd).elim

lemma planeGraphs_trianglePoints :
    planeGraphs trianglePoints =
      (Finset.univ.powerset : Finset (Finset (Segment 3))) := by
  classical
  ext s
  constructor
  · intro hs
    exact (Finset.mem_filter.mp hs).1
  · intro hs
    have hind : isIndependent (crossingGraph trianglePoints) s := by
      intro u v _ _ _
      exact no_cross_triangle u v
    exact (Finset.mem_filter).2 ⟨hs, hind⟩

lemma card_segment_three : Fintype.card (Segment 3) = 3 := by
  have h :
      Fintype.card (Segment 3) = Nat.choose 3 2 := by
    simpa [Segment] using (Sym2.card_subtype_not_diag (α := Fin 3))
  have h' : Nat.choose 3 2 = 3 := by
    decide
  exact h.trans h'

lemma pg_trianglePoints : pg trianglePoints = 8 := by
  classical
  have hpow :
      (Finset.univ.powerset : Finset (Finset (Segment 3))).card =
        2 ^ Fintype.card (Segment 3) := by
    simp
  calc
    pg trianglePoints =
        (Finset.univ.powerset : Finset (Finset (Segment 3))).card := by
      simp [pg, planeGraphs_trianglePoints]
    _ = 2 ^ Fintype.card (Segment 3) := hpow
    _ = 8 := by
      rw [card_segment_three]
      decide

lemma counterexample_12_15_n3 :
    (pg trianglePoints : ℚ) < (243 / 20 : ℚ) ^ (3 : ℕ) := by
  have hpg : pg trianglePoints = 8 := pg_trianglePoints
  simp [hpg]
  norm_num

lemma counterexample_23_32_n3 :
    (pg trianglePoints : ℚ) < (583 / 25 : ℚ) ^ (3 : ℕ) := by
  have hpg : pg trianglePoints = 8 := pg_trianglePoints
  simp [hpg]
  norm_num

lemma counterexample_23_32 :
    (pg singlePoint : ℚ) < (583 / 25 : ℚ) ^ (1 : ℕ) := by
  have hpg : pg singlePoint = 1 := pg_one singlePoint
  simp [hpg]
  norm_num

lemma counterexample_12_15 :
    (pg singlePoint : ℚ) < (243 / 20 : ℚ) ^ (1 : ℕ) := by
  have hpg : pg singlePoint = 1 := pg_one singlePoint
  simp [hpg]
  norm_num

end PlaneGraphs

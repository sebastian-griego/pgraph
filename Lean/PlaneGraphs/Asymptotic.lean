import PlaneGraphs.ExpectationLemma

namespace PlaneGraphs

lemma pg_min_class_lower_bound_at {n : ℕ} {K : ℚ} (hK : 0 < K)
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C)
    (havg : ∀ P : PointSet (n + 1), C (n + 1) P → avgIso P ≤ (n + 1 : ℚ) / K) :
    (pg_min_class C hgood (n + 1) : ℚ) ≥ K * (pg_min_class C hgood n : ℚ) := by
  rcases pg_min_class_spec C hgood (n + 1) with ⟨P0, hgoodP0, hpg⟩
  have hmin :
      ∀ v : Fin (n + 1), (pg (deletePoint P0 v) : ℚ) ≥
        (pg_min_class C hgood n : ℚ) := by
    intro v
    have hgooddel : C n (deletePoint P0 v) := hdel P0 hgoodP0 v
    exact_mod_cast (pg_min_class_le C hgood (n := n) (P := deletePoint P0 v) hgooddel)
  have hbound :
      (pg P0 : ℚ) ≥ K * (pg_min_class C hgood n : ℚ) := by
    exact
      pg_lower_bound_of_avgIso (P := P0) (K := K) (m := (pg_min_class C hgood n : ℚ)) hK
        (havg P0 hgoodP0) hmin
  have hP0' : (pg P0 : ℚ) = (pg_min_class C hgood (n + 1) : ℚ) := by
    exact_mod_cast hpg
  simpa [hP0'] using hbound

lemma pg_min_class_shifted_aux {K : ℚ} (hK : 0 < K)
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (havg : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P → avgIso P ≤ (n : ℚ) / K) :
    ∀ k : ℕ,
      (pg_min_class C hgood (N + k) : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K ^ k := by
  classical
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep :
          (pg_min_class C hgood (N + k + 1) : ℚ) ≥
            K * (pg_min_class C hgood (N + k) : ℚ) := by
        have hN : N ≤ N + k + 1 := by
          exact
            Nat.le_trans (Nat.le_add_right N k) (Nat.le_add_right (N + k) 1)
        refine pg_min_class_lower_bound_at (n := N + k) (K := K) (hK := hK) (C := C)
          (hgood := hgood) (hdel := hdel) (havg := ?_)
        intro P hP
        have hbound := havg (n := N + k + 1) hN (P := P) hP
        simpa [Nat.add_assoc, add_assoc, add_left_comm, add_comm] using hbound
      have hKnonneg : 0 ≤ K := le_of_lt hK
      have hmul :
          K * ((pg_min_class C hgood N : ℚ) * K ^ k) ≤
            K * (pg_min_class C hgood (N + k) : ℚ) := by
        exact mul_le_mul_of_nonneg_left ih hKnonneg
      have hchain :
          K * ((pg_min_class C hgood N : ℚ) * K ^ k) ≤
            (pg_min_class C hgood (N + k + 1) : ℚ) :=
        le_trans hmul hstep
      simpa [Nat.add_assoc, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hchain

lemma pg_min_class_shifted {K : ℚ} (hK : 0 < K)
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (havg : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P → avgIso P ≤ (n : ℚ) / K) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K ^ (n - N) := by
  intro n hn
  have hsum : N + (n - N) = n := by
    have h := Nat.sub_add_cancel hn
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have haux := pg_min_class_shifted_aux (K := K) (hK := hK) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (k := n - N)
  simpa [hsum] using haux

lemma pg_min_class_prefactor {K : ℚ} (hK : 0 < K)
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (havg : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P → avgIso P ≤ (n : ℚ) / K) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / K ^ N) * K ^ n := by
  intro n hn
  have hshift := pg_min_class_shifted (K := K) (hK := hK) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (n := n) hn
  have hKne : (K : ℚ) ≠ 0 := ne_of_gt hK
  have hKneN : (K ^ N : ℚ) ≠ 0 := by
    exact pow_ne_zero _ hKne
  have hdecomp : n - N + N = n := by
    exact Nat.sub_add_cancel hn
  have hpow1 : K ^ n = K ^ (n - N + N) := by
    exact (congrArg (fun m => K ^ m) hdecomp).symm
  have hpow : K ^ n = K ^ (n - N) * K ^ N := by
    calc
      K ^ n = K ^ (n - N + N) := hpow1
      _ = K ^ (n - N) * K ^ N := by
        exact pow_add K (n - N) N
  have hrewrite :
      (pg_min_class C hgood N : ℚ) * K ^ (n - N) =
        ((pg_min_class C hgood N : ℚ) / K ^ N) * K ^ n := by
    symm
    calc
      (pg_min_class C hgood N : ℚ) / K ^ N * K ^ n =
          (pg_min_class C hgood N : ℚ) * (K ^ N)⁻¹ * K ^ n := by
            rw [div_eq_mul_inv, mul_assoc]
      _ = (pg_min_class C hgood N : ℚ) * (K ^ N)⁻¹ * (K ^ (n - N) * K ^ N) := by
            rw [hpow]
      _ = (pg_min_class C hgood N : ℚ) * K ^ (n - N) * ((K ^ N)⁻¹ * K ^ N) := by
            ring
      _ = (pg_min_class C hgood N : ℚ) * K ^ (n - N) := by
            simp [hKneN, mul_assoc]
  have hshift' :
      (pg_min_class C hgood N : ℚ) * K ^ (n - N) ≤
        (pg_min_class C hgood n : ℚ) := by
    simpa using hshift
  have hrewrite' :
      ((pg_min_class C hgood N : ℚ) / K ^ N) * K ^ n =
        (pg_min_class C hgood N : ℚ) * K ^ (n - N) := by
    symm
    exact hrewrite
  exact (le_of_eq_of_le hrewrite' hshift')

end PlaneGraphs

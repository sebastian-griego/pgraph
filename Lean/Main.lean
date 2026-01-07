import PlaneGraphs.Asymptotic
import PlaneGraphs.Charging
import PlaneGraphs.Counterexample

open scoped BigOperators

namespace PlaneGraphs

def H : Nat := 3
def K_deg34_cert : ℚ := (exampleCertificate.getQ? "K_deg34").getD 0
def K_deg56_sample_main : ℚ := K_deg56_sample
def K_deg56_shift_sample_main : ℚ := K_deg56_shift_sample

lemma K_deg34_cert_pos : 0 < K_deg34_cert := by
  simp [K_deg34_cert, exampleCertificate_getQ_deg34]

lemma K_deg56_sample_main_pos : 0 < K_deg56_sample_main := by
  simpa [K_deg56_sample_main] using K_deg56_sample_pos

lemma K_deg56_shift_sample_main_pos : 0 < K_deg56_shift_sample_main := by
  simpa [K_deg56_shift_sample_main] using K_deg56_shift_sample_pos

theorem counterexample_12_15_with_hull (_h : HullSize trianglePoints ≤ H) :
    (pg trianglePoints : ℚ) < (243 / 20 : ℚ) ^ (3 : ℕ) := by
  simpa using counterexample_12_15_n3

theorem counterexample_23_32_with_hull (_h : HullSize trianglePoints ≤ H) :
    (pg trianglePoints : ℚ) < (583 / 25 : ℚ) ^ (3 : ℕ) := by
  simpa using counterexample_23_32_n3

theorem main_lower_bound_deg34
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ)) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * (112 / 11 : ℚ) ^ (n - N) := by
  intro n hn
  exact pg_min_class_shifted (K := (112 / 11 : ℚ)) (hK := by norm_num)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg34_prefactor
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ)) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / (112 / 11 : ℚ) ^ N) *
          (112 / 11 : ℚ) ^ n := by
  intro n hn
  exact pg_min_class_prefactor (K := (112 / 11 : ℚ)) (hK := by norm_num)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg34_from_deg34
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ) (hN1 : 1 ≤ N)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * (112 / 11 : ℚ) ^ (n - N) := by
  intro n hn
  have hav' :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ) := by
    intro n hn' P hP
    have hn1 : 1 ≤ n := le_trans hN1 hn'
    have hcert :
        avgIso P ≤ (n : ℚ) / ((exampleCertificate.getQ? "K_deg34").getD 0) :=
      avgIso_le_deg34_bound_cert (P := P) hn1 (hav hn' P hP)
    simpa [exampleCertificate_getQ_deg34] using hcert
  exact main_lower_bound_deg34 (C := C) (hgood := hgood) (hdel := hdel) (N := N)
    (hav := hav') (n := n) hn

theorem main_lower_bound_deg34_prefactor_from_deg34
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ) (hN1 : 1 ≤ N)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / (112 / 11 : ℚ) ^ N) *
          (112 / 11 : ℚ) ^ n := by
  intro n hn
  have hav' :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ) := by
    intro n hn' P hP
    have hn1 : 1 ≤ n := le_trans hN1 hn'
    have hcert :
        avgIso P ≤ (n : ℚ) / ((exampleCertificate.getQ? "K_deg34").getD 0) :=
      avgIso_le_deg34_bound_cert (P := P) hn1 (hav hn' P hP)
    simpa [exampleCertificate_getQ_deg34] using hcert
  exact main_lower_bound_deg34_prefactor (C := C) (hgood := hgood) (hdel := hdel) (N := N)
    (hav := hav') (n := n) hn

theorem main_lower_bound_deg34_cert
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ) (hN1 : 1 ≤ N)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg34_cert ^ (n - N) := by
  intro n hn
  have hav' :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg34_cert := by
    intro n hn' P hP
    have hn1 : 1 ≤ n := le_trans hN1 hn'
    exact avgIso_le_deg34_bound_cert (P := P) hn1 (hav hn' P hP)
  exact pg_min_class_shifted (K := K_deg34_cert) (hK := K_deg34_cert_pos)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav') (n := n) hn

theorem main_lower_bound_deg34_prefactor_cert
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ) (hN1 : 1 ≤ N)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / K_deg34_cert ^ N) * K_deg34_cert ^ n := by
  intro n hn
  have hav' :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg34_cert := by
    intro n hn' P hP
    have hn1 : 1 ≤ n := le_trans hN1 hn'
    exact avgIso_le_deg34_bound_cert (P := P) hn1 (hav hn' P hP)
  exact pg_min_class_prefactor (K := K_deg34_cert) (hK := K_deg34_cert_pos)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav') (n := n) hn

theorem main_lower_bound_deg34_product
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ) (hN1 : 1 ≤ N)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) *
          ∏ i in Finset.range (n - N), K_deg34_step (N + i + 1) := by
  intro n hn
  have hKpos : ∀ {n}, n ≥ N + 1 → 0 < K_deg34_step n := by
    intro n hn'
    have hN1' : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    have hn1 : 1 ≤ n := le_trans hN1' hn'
    exact K_deg34_step_pos hn1
  have hav' :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg34_step n := by
    intro n hn' P hP
    have hn1 : 1 ≤ n := le_trans hN1 hn'
    exact avgIso_le_deg34_step (P := P) hn1 (hav hn' P hP)
  exact pg_min_class_shifted_prod (K := K_deg34_step) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (hKpos := hKpos) (havg := hav') (n := n) hn

#print axioms main_lower_bound_deg34

theorem main_lower_bound_deg56_sample
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / K_deg56_sample_main) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_sample_main ^ (n - N) := by
  intro n hn
  exact pg_min_class_shifted (K := K_deg56_sample_main) (hK := K_deg56_sample_main_pos)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg56_sample_prefactor
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / K_deg56_sample_main) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / K_deg56_sample_main ^ N) *
          K_deg56_sample_main ^ n := by
  intro n hn
  exact pg_min_class_prefactor (K := K_deg56_sample_main) (hK := K_deg56_sample_main_pos)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg56_shift_sample
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / K_deg56_shift_sample_main) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_shift_sample_main ^ (n - N) := by
  intro n hn
  exact pg_min_class_shifted (K := K_deg56_shift_sample_main)
    (hK := K_deg56_shift_sample_main_pos) (C := C) (hgood := hgood) (hdel := hdel)
    (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg56_shift_sample_prefactor
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / K_deg56_shift_sample_main) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / K_deg56_shift_sample_main ^ N) *
          K_deg56_shift_sample_main ^ n := by
  intro n hn
  exact pg_min_class_prefactor (K := K_deg56_shift_sample_main)
    (hK := K_deg56_shift_sample_main_pos) (C := C) (hgood := hgood) (hdel := hdel)
    (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg56_shift_balance
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hdata : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      ∃ v3 v4 v5 v6 vL : ℚ,
        avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
          v6 * w6_shift_sample + vL * wL_shift_sample ∧
        v3 + v4 + v5 + v6 + vL = (n : ℚ) ∧
        22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vL) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_shift_sample_main ^ (n - N) := by
  intro n hn
  have havg :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg56_shift_sample_main := by
    intro n hn' P hP
    rcases hdata hn' P hP with ⟨v3, v4, v5, v6, vL, havg, hsum, hbal⟩
    have hbound :=
      avgIso_le_deg56_shift_of_balance (P := P) (v3 := v3) (v4 := v4)
        (v5 := v5) (v6 := v6) (vlarge := vL) havg hsum hbal
    simpa [K_deg56_shift_sample_main] using hbound
  exact pg_min_class_shifted (K := K_deg56_shift_sample_main)
    (hK := K_deg56_shift_sample_main_pos) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (n := n) hn

theorem main_lower_bound_deg56_shift_sumLarge
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hdata : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      ∃ v3 v4 v5 v6 vL sumLarge : ℚ,
        avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
          v6 * w6_shift_sample + vL * wL_shift_sample ∧
        v3 + v4 + v5 + v6 + vL = (n : ℚ) ∧
        sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12 ∧
        sumLarge ≥ 25 * v3 - 13 * v5 - 20 * v6 - 17 * vL - 12) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_shift_sample_main ^ (n - N) := by
  intro n hn
  have havg :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg56_shift_sample_main := by
    intro n hn' P hP
    rcases hdata hn' P hP with ⟨v3, v4, v5, v6, vL, sumLarge, havg, hsum, hsumLarge, hlarge⟩
    have hbound :=
      avgIso_le_deg56_shift_of_sumLarge (P := P) (v3 := v3) (v4 := v4)
        (v5 := v5) (v6 := v6) (vL := vL) (sumLarge := sumLarge)
        havg hsum hsumLarge hlarge
    simpa [K_deg56_shift_sample_main] using hbound
  exact pg_min_class_shifted (K := K_deg56_shift_sample_main)
    (hK := K_deg56_shift_sample_main_pos) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (n := n) hn

theorem main_lower_bound_deg56_linear
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hdata : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      ∃ v3 v4 v5 v6 vL : ℚ,
        avgIso P ≤ v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
          v6 * w6_sample + vL * wL_sample ∧
        v3 + v4 + v5 + v6 + vL = (n : ℚ) ∧
        45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 25 * (n : ℚ)) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_sample_main ^ (n - N) := by
  intro n hn
  have havg :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg56_sample_main := by
    intro n hn' P hP
    rcases hdata hn' P hP with ⟨v3, v4, v5, v6, vL, havg, hsum, hlin⟩
    have hbound :=
      avgIso_le_deg56_of_linear (P := P) (v3 := v3) (v4 := v4)
        (v5 := v5) (v6 := v6) (vlarge := vL)
        havg hsum hlin
    simpa [K_deg56_sample_main] using hbound
  exact pg_min_class_shifted (K := K_deg56_sample_main)
    (hK := K_deg56_sample_main_pos) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (n := n) hn

theorem main_lower_bound_deg56_shift_linear
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hdata : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      ∃ v3 v4 v5 v6 vL : ℚ,
        avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
          v6 * w6_shift_sample + vL * wL_shift_sample ∧
        v3 + v4 + v5 + v6 + vL = (n : ℚ) ∧
        45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 23 * (n : ℚ)) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_shift_sample_main ^ (n - N) := by
  intro n hn
  have havg :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg56_shift_sample_main := by
    intro n hn' P hP
    rcases hdata hn' P hP with ⟨v3, v4, v5, v6, vL, havg, hsum, hlin⟩
    have hbound :=
      avgIso_le_deg56_shift_of_linear (P := P) (v3 := v3) (v4 := v4)
        (v5 := v5) (v6 := v6) (vlarge := vL)
        havg hsum hlin
    simpa [K_deg56_shift_sample_main] using hbound
  exact pg_min_class_shifted (K := K_deg56_shift_sample_main)
    (hK := K_deg56_shift_sample_main_pos) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (n := n) hn

theorem main_lower_bound_deg56_sumLarge
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hdata : ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
      ∃ v3 v4 v5 v6 vL sumLarge : ℚ,
        avgIso P ≤ v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
          v6 * w6_sample + vL * wL_sample ∧
        v3 + v4 + v5 + v6 + vL = (n : ℚ) ∧
        sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12 ∧
        sumLarge ≥ 23 * v3 - 2 * v4 - 15 * v5 - 22 * v6 - 19 * vL - 12) :
    ∀ {n}, n ≥ N →
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * K_deg56_sample_main ^ (n - N) := by
  intro n hn
  have havg :
      ∀ {n}, n ≥ N → ∀ (P : PointSet n), C n P →
        avgIso P ≤ (n : ℚ) / K_deg56_sample_main := by
    intro n hn' P hP
    rcases hdata hn' P hP with ⟨v3, v4, v5, v6, vL, sumLarge, havg, hsum, hsumLarge, hlarge⟩
    have hbound :=
      avgIso_le_deg56_of_sumLarge (P := P) (v3 := v3) (v4 := v4)
        (v5 := v5) (v6 := v6) (vL := vL) (sumLarge := sumLarge)
        havg hsum hsumLarge hlarge
    simpa [K_deg56_sample_main] using hbound
  exact pg_min_class_shifted (K := K_deg56_sample_main)
    (hK := K_deg56_sample_main_pos) (C := C) (hgood := hgood)
    (hdel := hdel) (N := N) (havg := havg) (n := n) hn

end PlaneGraphs

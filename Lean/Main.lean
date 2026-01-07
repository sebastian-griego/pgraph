import PlaneGraphs.Asymptotic
import PlaneGraphs.Charging
import PlaneGraphs.Counterexample

namespace PlaneGraphs

def H : Nat := 3

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

#print axioms main_lower_bound_deg34

end PlaneGraphs

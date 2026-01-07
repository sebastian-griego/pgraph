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
    (hav : ∀ {n} (hn : n ≥ N) (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ)) :
    ∀ {n} (hn : n ≥ N),
      (pg_min_class C hgood n : ℚ) ≥
        (pg_min_class C hgood N : ℚ) * (112 / 11 : ℚ) ^ (n - N) := by
  intro n hn
  exact pg_min_class_shifted (K := (112 / 11 : ℚ)) (hK := by norm_num)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav) (n := n) hn

theorem main_lower_bound_deg34_prefactor
    (C : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, C n P)
    (hdel : ClosedUnderDelete C) (N : ℕ)
    (hav : ∀ {n} (hn : n ≥ N) (P : PointSet n), C n P →
      avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ)) :
    ∀ {n} (hn : n ≥ N),
      (pg_min_class C hgood n : ℚ) ≥
        ((pg_min_class C hgood N : ℚ) / (112 / 11 : ℚ) ^ N) *
          (112 / 11 : ℚ) ^ n := by
  intro n hn
  exact pg_min_class_prefactor (K := (112 / 11 : ℚ)) (hK := by norm_num)
    (C := C) (hgood := hgood) (hdel := hdel) (N := N) (havg := hav) (n := n) hn

#print axioms main_lower_bound_deg34

end PlaneGraphs

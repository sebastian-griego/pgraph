import PlaneGraphs.Counterexample
import PlaneGraphs.TrivialLowerBound

namespace PlaneGraphs

def H : Nat := 3

theorem trivial_lower_bound {n : ℕ} (P : PointSet (n + 1)) :
    (pg P : ℚ) ≥ (2 : ℚ) ^ n := by
  have h : (2 ^ n : ℕ) ≤ pg P := pg_ge_two_pow (P := P)
  exact_mod_cast h

theorem counterexample_12_15_with_hull (_h : HullSize trianglePoints ≤ H) :
    (pg trianglePoints : ℚ) < (243 / 20 : ℚ) ^ (3 : ℕ) := by
  simpa using counterexample_12_15_n3

theorem counterexample_23_32_with_hull (_h : HullSize trianglePoints ≤ H) :
    (pg trianglePoints : ℚ) < (583 / 25 : ℚ) ^ (3 : ℕ) := by
  simpa using counterexample_23_32_n3

theorem main_lower_bound {n : ℕ} (P : PointSet (n + 1)) (_ : HullSize P ≤ H) :
    (pg P : ℚ) ≥ (2 : ℚ) ^ n := by
  exact trivial_lower_bound (P := P)

#print axioms main_lower_bound

end PlaneGraphs

import Mathlib
import PlaneGraphs.ExpectationLemma
import PlaneGraphs.Certificate

open scoped BigOperators

namespace PlaneGraphs

/-- A charging function on plane graphs. -/
def Charge {n : ℕ} := Finset (Segment n) → ℚ

lemma avgIso_le_of_charge {n : ℕ} (P : PointSet n) (charge : Charge) {K : ℚ}
    (hconserve : ∑ G in planeGraphs P, charge G =
        ∑ G in planeGraphs P, (isoCount G : ℚ))
    (hupper : ∀ G ∈ planeGraphs P, charge G ≤ (n : ℚ) / K) :
    avgIso P ≤ (n : ℚ) / K := by
  classical
  have hsum_le :
      ∑ G in planeGraphs P, charge G ≤
        ∑ _G in planeGraphs P, (n : ℚ) / K := by
    refine Finset.sum_le_sum ?_
    intro G hG
    exact hupper G hG
  have hsum_const :
      ∑ _G in planeGraphs P, (n : ℚ) / K = (pg P : ℚ) * ((n : ℚ) / K) := by
    simp [pg]
  have hsum_le' :
      ∑ G in planeGraphs P, charge G ≤ (pg P : ℚ) * ((n : ℚ) / K) := by
    simpa [hsum_const] using hsum_le
  have hpg_pos : (0 : ℚ) < (pg P : ℚ) := by
    exact_mod_cast (pg_pos P)
  have hdiv :
      (∑ G in planeGraphs P, charge G) / (pg P : ℚ) ≤ (n : ℚ) / K := by
    exact (div_le_iff' hpg_pos).2 hsum_le'
  have havg : avgIso P = (∑ G in planeGraphs P, charge G) / (pg P : ℚ) := by
    simp [avgIso, hconserve]
  simpa [havg] using hdiv

end PlaneGraphs

namespace PlaneGraphs

lemma avgIso_le_deg34_bound {n : ℕ} (P : PointSet n) (hn : 1 ≤ n)
    (havg : avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    avgIso P ≤ (n : ℚ) / (112 / 11 : ℚ) := by
  have hnq : (1 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hineq : (11 * (n : ℚ) - 6) / 112 ≤ (n : ℚ) / (112 / 11 : ℚ) := by
    linarith [hnq]
  exact le_trans havg hineq

lemma example_cert_deg34_bound {n : ℕ} (hn : 1 ≤ n) :
    (11 * (n : ℚ) - 6) / 112 ≤
      (n : ℚ) / ((exampleCertificate.getQ? "K_deg34").getD 0) := by
  have hnq : (1 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  simp [exampleCertificate_getQ_deg34] at *
  linarith [hnq]

lemma charge_bound_deg34 {n v3 v4 vlarge : ℚ}
    (hvlarge : 0 ≤ vlarge)
    (hsum : v3 + v4 + vlarge = n)
    (hv4 : v4 ≤ (6 * n - 9 * v3 - 6) / 2) :
    v3 / 8 + v4 / 16 + vlarge / 32 ≤ (11 * n - 6) / 112 := by
  have hsum' : vlarge = n - v3 - v4 := by
    linarith
  have hexpr :
      v3 / 8 + v4 / 16 + vlarge / 32 = (n + 3 * v3 + v4) / 32 := by
    calc
      v3 / 8 + v4 / 16 + vlarge / 32
          = v3 / 8 + v4 / 16 + (n - v3 - v4) / 32 := by
              simp [hsum']
      _ = (n + 3 * v3 + v4) / 32 := by
              ring
  by_cases h : v3 ≤ (4 * n - 6) / 7
  ·
    have hv4' : v4 ≤ n - v3 := by
      linarith
    have hbound : (n + 3 * v3 + v4) / 32 ≤ (11 * n - 6) / 112 := by
      linarith [h, hv4']
    simpa [hexpr] using hbound
  ·
    have hge : (4 * n - 6) / 7 ≤ v3 := by
      exact le_of_lt (lt_of_not_ge h)
    have hbound : (n + 3 * v3 + v4) / 32 ≤ (11 * n - 6) / 112 := by
      linarith [hge, hv4]
    simpa [hexpr] using hbound

end PlaneGraphs

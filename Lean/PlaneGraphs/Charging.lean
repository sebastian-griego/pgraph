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

def K_deg34_step (n : ℕ) : ℚ :=
  (112 * (n : ℚ)) / (11 * (n : ℚ) - 6)

lemma K_deg34_step_pos {n : ℕ} (hn : 1 ≤ n) : 0 < K_deg34_step n := by
  have hnq : (1 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hnum : 0 < 112 * (n : ℚ) := by
    linarith [hnq]
  have hden : 0 < 11 * (n : ℚ) - 6 := by
    linarith [hnq]
  exact div_pos hnum hden

lemma deg34_step_eq {n : ℕ} (hn : 1 ≤ n) :
    (n : ℚ) / K_deg34_step n = (11 * (n : ℚ) - 6) / 112 := by
  have hnq : (n : ℚ) ≠ 0 := by
    have hnq' : (1 : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast hn
    have hnpos : 0 < (n : ℚ) := by
      linarith [hnq']
    exact ne_of_gt hnpos
  have hden : 11 * (n : ℚ) - 6 ≠ 0 := by
    have hnq' : (1 : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast hn
    have hpos : 0 < 11 * (n : ℚ) - 6 := by
      linarith [hnq']
    exact ne_of_gt hpos
  field_simp [K_deg34_step, hnq, hden]
  ring

lemma avgIso_le_deg34_step {n : ℕ} (P : PointSet n) (hn : 1 ≤ n)
    (havg : avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    avgIso P ≤ (n : ℚ) / K_deg34_step n := by
  simpa [deg34_step_eq (n := n) hn] using havg

lemma example_cert_deg34_bound {n : ℕ} (hn : 1 ≤ n) :
    (11 * (n : ℚ) - 6) / 112 ≤
      (n : ℚ) / ((exampleCertificate.getQ? "K_deg34").getD 0) := by
  have hnq : (1 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  simp [exampleCertificate_getQ_deg34] at *
  linarith [hnq]

lemma avgIso_le_deg34_bound_cert {n : ℕ} (P : PointSet n) (hn : 1 ≤ n)
    (havg : avgIso P ≤ (11 * (n : ℚ) - 6) / 112) :
    avgIso P ≤ (n : ℚ) / ((exampleCertificate.getQ? "K_deg34").getD 0) := by
  exact le_trans havg (example_cert_deg34_bound (n := n) hn)

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

lemma avgIso_le_deg34_of_split {n : ℕ} (P : PointSet n) {v3 v4 vlarge : ℚ}
    (hvlarge : 0 ≤ vlarge)
    (hsum : v3 + v4 + vlarge = (n : ℚ))
    (hv4 : v4 ≤ (6 * (n : ℚ) - 9 * v3 - 6) / 2)
    (havg : avgIso P ≤ v3 / 8 + v4 / 16 + vlarge / 32) :
    avgIso P ≤ (11 * (n : ℚ) - 6) / 112 := by
  have hbound :=
    charge_bound_deg34 (n := (n : ℚ)) (v3 := v3) (v4 := v4) (vlarge := vlarge)
      hvlarge hsum hv4
  exact le_trans havg hbound

end PlaneGraphs

namespace PlaneGraphs

def K_deg56_sample : ℚ :=
  (deg56SampleCertificate.getQ? "K_deg56").getD 0

def w3_sample : ℚ := (deg56SampleCertificate.getQ? "w3").getD 0
def w4_sample : ℚ := (deg56SampleCertificate.getQ? "w4").getD 0
def w5_sample : ℚ := (deg56SampleCertificate.getQ? "w5").getD 0
def w6_sample : ℚ := (deg56SampleCertificate.getQ? "w6").getD 0
def wL_sample : ℚ := (deg56SampleCertificate.getQ? "wL").getD 0

lemma K_deg56_sample_pos : 0 < K_deg56_sample := by
  simp [K_deg56_sample, deg56SampleCertificate_getQ_K_deg56]

lemma avgIso_le_deg56_of_split {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vlarge * wL_sample)
    (hbound :
      v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vlarge * wL_sample ≤ (n : ℚ) / K_deg56_sample) :
    avgIso P ≤ (n : ℚ) / K_deg56_sample := by
  exact le_trans havg hbound

end PlaneGraphs

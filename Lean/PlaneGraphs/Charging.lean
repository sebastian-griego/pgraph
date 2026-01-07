import Mathlib
import PlaneGraphs.ExpectationLemma
import PlaneGraphs.Certificate
import PlaneGraphs.DegreeCounts

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

lemma charge_bound_deg56_iff {v3 v4 v5 v6 vL : ℚ} :
    v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vL * wL_sample
      ≤ (v3 + v4 + v5 + v6 + vL) / K_deg56_sample
      ↔ 20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vL := by
  have hK : K_deg56_sample = (96 / 7 : ℚ) := by
    simp [K_deg56_sample, deg56SampleCertificate_getQ_K_deg56]
  have hw3 : w3_sample = (1 / 8 : ℚ) := by
    simp [w3_sample, deg56SampleCertificate_getQ_w3]
  have hw4 : w4_sample = (1 / 16 : ℚ) := by
    simp [w4_sample, deg56SampleCertificate_getQ_w4]
  have hw5 : w5_sample = (1 / 32 : ℚ) := by
    simp [w5_sample, deg56SampleCertificate_getQ_w5]
  have hw6 : w6_sample = (1 / 64 : ℚ) := by
    simp [w6_sample, deg56SampleCertificate_getQ_w6]
  have hwL : wL_sample = (1 / 128 : ℚ) := by
    simp [wL_sample, deg56SampleCertificate_getQ_wL]
  constructor
  · intro h
    have h' :
        v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128
          ≤ (v3 + v4 + v5 + v6 + vL) * (7 / 96 : ℚ) := by
      simpa [hK, hw3, hw4, hw5, hw6, hwL, div_eq_mul_inv] using h
    have h'' :
        384 * (v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128)
          ≤ 384 * ((v3 + v4 + v5 + v6 + vL) * (7 / 96 : ℚ)) :=
      (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℚ) ≤ 384))
    have h''' :
        48 * v3 + 24 * v4 + 12 * v5 + 6 * v6 + 3 * vL
          ≤ 28 * (v3 + v4 + v5 + v6 + vL) := by
      nlinarith [h'']
    linarith [h''']
  · intro h
    have h' :
        48 * v3 + 24 * v4 + 12 * v5 + 6 * v6 + 3 * vL
          ≤ 28 * (v3 + v4 + v5 + v6 + vL) := by
      linarith
    have h'' :
        384 * (v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128)
          ≤ 384 * ((v3 + v4 + v5 + v6 + vL) * (7 / 96 : ℚ)) := by
      nlinarith [h']
    have h''' :
        v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128
          ≤ (v3 + v4 + v5 + v6 + vL) * (7 / 96 : ℚ) := by
      nlinarith [h'']
    simpa [hK, hw3, hw4, hw5, hw6, hwL, div_eq_mul_inv] using h'''

lemma avgIso_le_deg56_of_balance {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vlarge * wL_sample)
    (hsum : v3 + v4 + v5 + v6 + vlarge = (n : ℚ))
    (hbal : 20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vlarge) :
    avgIso P ≤ (n : ℚ) / K_deg56_sample := by
  have hbound :
      v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vlarge * wL_sample ≤ (n : ℚ) / K_deg56_sample := by
    have hbalance :
        v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
          v6 * w6_sample + vlarge * wL_sample
            ≤ (v3 + v4 + v5 + v6 + vlarge) / K_deg56_sample := by
      exact (charge_bound_deg56_iff (v3 := v3) (v4 := v4) (v5 := v5)
        (v6 := v6) (vL := vlarge)).2 hbal
    simpa [hsum] using hbalance
  exact le_trans havg hbound

lemma avgIso_le_deg56_of_linear {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vlarge * wL_sample)
    (hsum : v3 + v4 + v5 + v6 + vlarge = (n : ℚ))
    (hlin : 45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 25 * (n : ℚ)) :
    avgIso P ≤ (n : ℚ) / K_deg56_sample := by
  have hbal :
      20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vlarge := by
    exact deg56_balance_of_linear (v3 := v3) (v4 := v4) (v5 := v5)
      (v6 := v6) (vL := vlarge) (n := (n : ℚ)) hsum hlin
  exact avgIso_le_deg56_of_balance (P := P) (v3 := v3) (v4 := v4) (v5 := v5)
    (v6 := v6) (vlarge := vlarge) havg hsum hbal

lemma avgIso_le_deg56_of_sumLarge {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vL sumLarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_sample + v4 * w4_sample + v5 * w5_sample +
        v6 * w6_sample + vL * wL_sample)
    (hsum : v3 + v4 + v5 + v6 + vL = (n : ℚ))
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12)
    (hlarge :
      sumLarge ≥ 23 * v3 - 2 * v4 - 15 * v5 - 22 * v6 - 19 * vL - 12) :
    avgIso P ≤ (n : ℚ) / K_deg56_sample := by
  have hbal :
      20 * v3 ≤ 4 * v4 + 16 * v5 + 22 * v6 + 25 * vL := by
    exact (deg56_balance_iff_sumLarge (v3 := v3) (v4 := v4) (v5 := v5)
      (v6 := v6) (vL := vL) (sumLarge := sumLarge) hsumLarge).2 hlarge
  exact avgIso_le_deg56_of_balance (P := P) (v3 := v3) (v4 := v4) (v5 := v5)
    (v6 := v6) (vlarge := vL) havg hsum hbal

def K_deg56_n12_sample : ℚ :=
  (deg56N12SampleCertificate.getQ? "K_deg56_n12").getD 0

def w3_n12_sample : ℚ := (deg56N12SampleCertificate.getQ? "w3").getD 0
def w4_n12_sample : ℚ := (deg56N12SampleCertificate.getQ? "w4").getD 0
def w5_n12_sample : ℚ := (deg56N12SampleCertificate.getQ? "w5").getD 0
def w6_n12_sample : ℚ := (deg56N12SampleCertificate.getQ? "w6").getD 0
def wL_n12_sample : ℚ := (deg56N12SampleCertificate.getQ? "wL").getD 0

lemma K_deg56_n12_sample_pos : 0 < K_deg56_n12_sample := by
  simp [K_deg56_n12_sample, deg56N12SampleCertificate_getQ_K_deg56_n12]

lemma avgIso_le_deg56_n12_of_split {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_n12_sample + v4 * w4_n12_sample + v5 * w5_n12_sample +
        v6 * w6_n12_sample + vlarge * wL_n12_sample)
    (hbound :
      v3 * w3_n12_sample + v4 * w4_n12_sample + v5 * w5_n12_sample +
        v6 * w6_n12_sample + vlarge * wL_n12_sample ≤ (n : ℚ) / K_deg56_n12_sample) :
    avgIso P ≤ (n : ℚ) / K_deg56_n12_sample := by
  exact le_trans havg hbound

lemma charge_bound_deg56_n12_iff {v3 v4 v5 v6 vL : ℚ} :
    v3 * w3_n12_sample + v4 * w4_n12_sample + v5 * w5_n12_sample +
        v6 * w6_n12_sample + vL * wL_n12_sample
      ≤ (v3 + v4 + v5 + v6 + vL) / K_deg56_n12_sample
      ↔ 64 * v3 + 32 * v4 + 16 * v5 + 8 * v6 + 4 * vL ≤
          37 * (v3 + v4 + v5 + v6 + vL) := by
  have hK : K_deg56_n12_sample = (512 / 37 : ℚ) := by
    simp [K_deg56_n12_sample, deg56N12SampleCertificate_getQ_K_deg56_n12]
  have hw3 : w3_n12_sample = (1 / 8 : ℚ) := by
    simp [w3_n12_sample, deg56N12SampleCertificate_getQ_w3]
  have hw4 : w4_n12_sample = (1 / 16 : ℚ) := by
    simp [w4_n12_sample, deg56N12SampleCertificate_getQ_w4]
  have hw5 : w5_n12_sample = (1 / 32 : ℚ) := by
    simp [w5_n12_sample, deg56N12SampleCertificate_getQ_w5]
  have hw6 : w6_n12_sample = (1 / 64 : ℚ) := by
    simp [w6_n12_sample, deg56N12SampleCertificate_getQ_w6]
  have hwL : wL_n12_sample = (1 / 128 : ℚ) := by
    simp [wL_n12_sample, deg56N12SampleCertificate_getQ_wL]
  constructor
  · intro h
    have h1 :
        v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128
          ≤ (v3 + v4 + v5 + v6 + vL) * (37 / 512 : ℚ) := by
      simpa [hK, hw3, hw4, hw5, hw6, hwL, div_eq_mul_inv] using h
    have h2 :
        512 * (v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128)
          ≤ 512 * ((v3 + v4 + v5 + v6 + vL) * (37 / 512 : ℚ)) :=
      (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℚ) ≤ 512))
    nlinarith [h2]
  · intro h
    have h1 :
        512 * (v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128)
          ≤ 512 * ((v3 + v4 + v5 + v6 + vL) * (37 / 512 : ℚ)) := by
      nlinarith [h]
    have h2 :
        v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128
          ≤ (v3 + v4 + v5 + v6 + vL) * (37 / 512 : ℚ) := by
      nlinarith [h1]
    simpa [hK, hw3, hw4, hw5, hw6, hwL, div_eq_mul_inv] using h2

def K_deg56_shift_sample : ℚ :=
  (deg56ShiftSampleCertificate.getQ? "K_deg56_shift").getD 0

def w3_shift_sample : ℚ := (deg56ShiftSampleCertificate.getQ? "w3").getD 0
def w4_shift_sample : ℚ := (deg56ShiftSampleCertificate.getQ? "w4").getD 0
def w5_shift_sample : ℚ := (deg56ShiftSampleCertificate.getQ? "w5").getD 0
def w6_shift_sample : ℚ := (deg56ShiftSampleCertificate.getQ? "w6").getD 0
def wL_shift_sample : ℚ := (deg56ShiftSampleCertificate.getQ? "wL").getD 0

lemma K_deg56_shift_sample_pos : 0 < K_deg56_shift_sample := by
  simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]

lemma avgIso_le_deg56_shift_of_split {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vlarge * wL_shift_sample)
    (hbound :
      v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vlarge * wL_shift_sample ≤ (n : ℚ) / K_deg56_shift_sample) :
    avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
  exact le_trans havg hbound

lemma charge_bound_deg56_shift_iff {v3 v4 v5 v6 vL : ℚ} :
    v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vL * wL_shift_sample
      ≤ (v3 + v4 + v5 + v6 + vL) / K_deg56_shift_sample
      ↔ 22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vL := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  have hw3 : w3_shift_sample = (1 / 8 : ℚ) := by
    simp [w3_shift_sample, deg56ShiftSampleCertificate_getQ_w3]
  have hw4 : w4_shift_sample = (1 / 16 : ℚ) := by
    simp [w4_shift_sample, deg56ShiftSampleCertificate_getQ_w4]
  have hw5 : w5_shift_sample = (1 / 32 : ℚ) := by
    simp [w5_shift_sample, deg56ShiftSampleCertificate_getQ_w5]
  have hw6 : w6_shift_sample = (1 / 64 : ℚ) := by
    simp [w6_shift_sample, deg56ShiftSampleCertificate_getQ_w6]
  have hwL : wL_shift_sample = (1 / 128 : ℚ) := by
    simp [wL_shift_sample, deg56ShiftSampleCertificate_getQ_wL]
  constructor
  · intro h
    have h' :
        v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128
          ≤ (v3 + v4 + v5 + v6 + vL) * (13 / 192 : ℚ) := by
      simpa [hK, hw3, hw4, hw5, hw6, hwL, div_eq_mul_inv] using h
    have h'' :
        384 * (v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128)
          ≤ 384 * ((v3 + v4 + v5 + v6 + vL) * (13 / 192 : ℚ)) :=
      (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℚ) ≤ 384))
    have h''' :
        48 * v3 + 24 * v4 + 12 * v5 + 6 * v6 + 3 * vL
          ≤ 26 * (v3 + v4 + v5 + v6 + vL) := by
      nlinarith [h'']
    linarith [h''']
  · intro h
    have h' :
        48 * v3 + 24 * v4 + 12 * v5 + 6 * v6 + 3 * vL
          ≤ 26 * (v3 + v4 + v5 + v6 + vL) := by
      linarith
    have h'' :
        384 * (v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128)
          ≤ 384 * ((v3 + v4 + v5 + v6 + vL) * (13 / 192 : ℚ)) := by
      nlinarith [h']
    have h''' :
        v3 / 8 + v4 / 16 + v5 / 32 + v6 / 64 + vL / 128
          ≤ (v3 + v4 + v5 + v6 + vL) * (13 / 192 : ℚ) := by
      nlinarith [h'']
    simpa [hK, hw3, hw4, hw5, hw6, hwL, div_eq_mul_inv] using h'''

lemma avgIso_le_deg56_shift_of_balance {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vlarge * wL_shift_sample)
    (hsum : v3 + v4 + v5 + v6 + vlarge = (n : ℚ))
    (hbal : 22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vlarge) :
    avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
  have hbound :
      v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vlarge * wL_shift_sample
        ≤ (v3 + v4 + v5 + v6 + vlarge) / K_deg56_shift_sample := by
    exact (charge_bound_deg56_shift_iff (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6)
      (vL := vlarge)).2 hbal
  have hbound' :
      v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vlarge * wL_shift_sample ≤ (n : ℚ) / K_deg56_shift_sample := by
    simpa [hsum] using hbound
  exact le_trans havg hbound'

lemma avgIso_le_deg56_shift_of_linear {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vlarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vlarge * wL_shift_sample)
    (hsum : v3 + v4 + v5 + v6 + vlarge = (n : ℚ))
    (hlin : 45 * v3 + 21 * v4 + 9 * v5 + 3 * v6 ≤ 23 * (n : ℚ)) :
    avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
  have hbal :
      22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vlarge := by
    exact deg56_shift_balance_of_linear (v3 := v3) (v4 := v4) (v5 := v5)
      (v6 := v6) (vL := vlarge) (n := (n : ℚ)) hsum hlin
  exact avgIso_le_deg56_shift_of_balance (P := P) (v3 := v3) (v4 := v4) (v5 := v5)
    (v6 := v6) (vlarge := vlarge) havg hsum hbal

lemma avgIso_le_deg56_shift_of_sumLarge {n : ℕ} (P : PointSet n)
    {v3 v4 v5 v6 vL sumLarge : ℚ}
    (havg :
      avgIso P ≤ v3 * w3_shift_sample + v4 * w4_shift_sample + v5 * w5_shift_sample +
        v6 * w6_shift_sample + vL * wL_shift_sample)
    (hsum : v3 + v4 + v5 + v6 + vL = (n : ℚ))
    (hsumLarge : sumLarge = 3 * v3 + 2 * v4 + v5 + 6 * vL - 12)
    (hlarge :
      sumLarge ≥ 25 * v3 - 13 * v5 - 20 * v6 - 17 * vL - 12) :
    avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
  have hbal :
      22 * v3 ≤ 2 * v4 + 14 * v5 + 20 * v6 + 23 * vL := by
    exact (deg56_shift_balance_iff_sumLarge (v3 := v3) (v4 := v4) (v5 := v5)
      (v6 := v6) (vL := vL) (sumLarge := sumLarge) hsumLarge).2 hlarge
  exact avgIso_le_deg56_shift_of_balance (P := P) (v3 := v3) (v4 := v4) (v5 := v5)
    (v6 := v6) (vlarge := vL) havg hsum hbal

end PlaneGraphs

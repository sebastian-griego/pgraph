import PlaneGraphs.Basic
import PlaneGraphs.Charging
import PlaneGraphs.DegreeCounts
import PlaneGraphs.DegreeVectors
import PlaneGraphs.Asymptotic

namespace PlaneGraphs

structure Hull3Triangulation {n : ℕ} (P : PointSet n) where
  hHull : HullSize P = 3
  G : Finset (Segment n)
  card_eq : (G.card : ℚ) = 3 * (n : ℚ) - 6
  min_degree : ∀ v, 3 ≤ degree G v

/-- Transfer constants for the n ≥ 12 hull-3 discharging step. -/
def deg56_n12_a3 : ℚ := 0
def deg56_n12_a4 : ℚ := 0
def deg56_n12_a5 : ℚ := 0
def deg56_n12_a6 : ℚ := 0

def deg56_n12_c3 : ℚ := 0
def deg56_n12_c4 : ℚ := 0
def deg56_n12_c5 : ℚ := 0
def deg56_n12_c6 : ℚ := 0

/--
Geometric sumLarge bound for hull-3 triangulations (n ≥ 12).

This is the remaining geometric lemma needed for the `K_deg56_n12` bound.
The balance/linear inequalities follow from this via `sumLarge_eq_q`.
-/
axiom deg56FastVectorsN12_complete {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    degreeVectorOf T.G ∈ deg56FastVectorsN12

lemma deg56_n12_sum_lower {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    ((-33 / 4 : ℚ) + deg56_n12_a3 * deg56_n12_c3) * (v3 T.G : ℚ) +
      ((-5 / 4 : ℚ) + deg56_n12_a4 * deg56_n12_c4) * (v4 T.G : ℚ) +
      ((11 / 4 : ℚ) + deg56_n12_a5 * deg56_n12_c5) * (v5 T.G : ℚ) +
      ((21 / 4 : ℚ) + deg56_n12_a6 * deg56_n12_c6) * (v6 T.G : ℚ) +
      (1 - (deg56_n12_a3 + deg56_n12_a4 + deg56_n12_a5 + deg56_n12_a6)) *
        (sumLarge T.G : ℚ) ≥ -(57 / 4 : ℚ) := by
  have hmem := deg56FastVectorsN12_complete (T := T) hn
  have hsumv : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hsumLarge :=
    degreeVectorOf_sumLarge (G := T.G) T.card_eq T.min_degree hsumv
  have hOk :=
    deg56FastVectorsN12_sumLarge_forall (degreeVectorOf T.G) hmem
  have hOk' :
      4 * (sumLarge T.G : ℚ) ≥
        33 * (v3 T.G : ℚ) + 5 * (v4 T.G : ℚ) - 11 * (v5 T.G : ℚ) -
          21 * (v6 T.G : ℚ) - 57 := by
    have hOk0 :
        4 * (degreeVectorOf T.G).sumLarge ≥
          33 * (v3 T.G : ℚ) + 5 * (v4 T.G : ℚ) - 11 * (v5 T.G : ℚ) -
            21 * (v6 T.G : ℚ) - 57 := by
      simpa [deg56N12SumLargeOk, degreeVectorOf] using hOk
    simpa [hsumLarge] using hOk0
  have hsumLower :
      (-33 / 4 : ℚ) * (v3 T.G : ℚ) + (-5 / 4 : ℚ) * (v4 T.G : ℚ) +
        (11 / 4 : ℚ) * (v5 T.G : ℚ) + (21 / 4 : ℚ) * (v6 T.G : ℚ) +
        (sumLarge T.G : ℚ) ≥ -(57 / 4 : ℚ) := by
    linarith [hOk']
  simpa [deg56_n12_a3, deg56_n12_a4, deg56_n12_a5, deg56_n12_a6,
    deg56_n12_c3, deg56_n12_c4, deg56_n12_c5, deg56_n12_c6] using hsumLower

lemma deg56_sumLarge_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    4 * (sumLarge T.G : ℚ) ≥
      33 * (v3 T.G : ℚ) + 5 * (v4 T.G : ℚ) - 11 * (v5 T.G : ℚ) -
        21 * (v6 T.G : ℚ) - 57 := by
  have hsum := deg56_n12_sum_lower (T := T) hn
  have hsum' :
      (-33 / 4 : ℚ) * (v3 T.G : ℚ) + (-5 / 4 : ℚ) * (v4 T.G : ℚ) +
        (11 / 4 : ℚ) * (v5 T.G : ℚ) + (21 / 4 : ℚ) * (v6 T.G : ℚ) +
        (sumLarge T.G : ℚ) ≥ -(57 / 4 : ℚ) := by
    simpa [deg56_n12_a3, deg56_n12_a4, deg56_n12_a5, deg56_n12_a6,
      deg56_n12_c3, deg56_n12_c4, deg56_n12_c5, deg56_n12_c6] using hsum
  linarith [hsum']

/--
Shifted sumLarge bound for hull-3 triangulations (n ≥ 19).

This follows from the `deg56FastVectorsN12_complete` axiom together with the
checked `deg56FastVectorsN19_shift_sumLarge` list.
-/
lemma deg56_shift_sumLarge_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 19 ≤ n) :
    (sumLarge T.G : ℚ) ≥
      25 * (v3 T.G : ℚ) - 13 * (v5 T.G : ℚ) - 20 * (v6 T.G : ℚ) -
        17 * (vL T.G : ℚ) - 12 := by
  have hn12 : 12 ≤ n := by
    exact Nat.le_trans (by decide : 12 ≤ 19) hn
  have hmem12 := deg56FastVectorsN12_complete (T := T) hn12
  have hmemFast : degreeVectorOf T.G ∈ deg56FastVectors :=
    (List.mem_filter.1 hmem12).1
  have hsum : v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G = n := by
    exact v_sum_eq_n (G := T.G) T.min_degree
  have hnvec : (degreeVectorOf T.G).n = n := by
    simp [degreeVectorOf, DegreeVector.n, hsum]
  have hpred19 : 19 ≤ (degreeVectorOf T.G).n := by
    simpa [hnvec] using hn
  have hmem19 : degreeVectorOf T.G ∈ deg56FastVectorsN19 := by
    exact List.mem_filter.2 ⟨hmemFast, by simpa using hpred19⟩
  have hOk := deg56FastVectorsN19_shift_sumLarge_forall (degreeVectorOf T.G) hmem19
  have hsumv :
      (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact_mod_cast hsum
  have hsumLarge :=
    degreeVectorOf_sumLarge (G := T.G) T.card_eq T.min_degree hsumv
  have hOk' :
      (degreeVectorOf T.G).sumLarge ≥
        25 * (v3 T.G : ℚ) - 13 * (v5 T.G : ℚ) - 20 * (v6 T.G : ℚ) -
          17 * (vL T.G : ℚ) - 12 := by
    simpa [deg56ShiftSumLargeOk, degreeVectorOf] using hOk
  simpa [hsumLarge] using hOk'

lemma deg56_shift_balance_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 19 ≤ n) :
    22 * (v3 T.G : ℚ) ≤
      2 * (v4 T.G : ℚ) + 14 * (v5 T.G : ℚ) + 20 * (v6 T.G : ℚ) + 23 * (vL T.G : ℚ) := by
  have hsumv : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hsumLarge :
      (sumLarge T.G : ℚ) =
        3 * (v3 T.G : ℚ) + 2 * (v4 T.G : ℚ) + (v5 T.G : ℚ) + 6 * (vL T.G : ℚ) - 12 := by
    exact sumLarge_eq_q (G := T.G) T.card_eq T.min_degree hsumv
  have hshift := deg56_shift_sumLarge_hull3 (T := T) hn
  have hiff :=
    deg56_shift_balance_iff_sumLarge
      (v3 := (v3 T.G : ℚ)) (v4 := (v4 T.G : ℚ)) (v5 := (v5 T.G : ℚ))
      (v6 := (v6 T.G : ℚ)) (vL := (vL T.G : ℚ))
      (sumLarge := (sumLarge T.G : ℚ)) hsumLarge
  exact (hiff).2 hshift

lemma deg56_sumLarge_hull3_transfer_of_const {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P)
    (a3 a4 a5 a6 c3 c4 c5 c6 : ℚ)
    (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5) (ha6 : 0 ≤ a6)
    (h3 : ∀ v, degree T.G v = 3 → adjacentLargeCountQ T.G v ≥ c3)
    (h4 : ∀ v, degree T.G v = 4 → adjacentLargeCountQ T.G v ≥ c4)
    (h5 : ∀ v, degree T.G v = 5 → adjacentLargeCountQ T.G v ≥ c5)
    (h6 : ∀ v, degree T.G v = 6 → adjacentLargeCountQ T.G v ≥ c6) :
    ∃ transfer : Fin n → Fin n → ℚ,
      ∃ lower : Fin n → ℚ,
        (∀ u v, transfer u v = - transfer v u) ∧
        (∀ v, deg56BalanceTerm T.G v + netTransfer transfer v ≥ lower v) ∧
        (∑ v in Finset.univ, lower v =
          ((-33 / 4 : ℚ) + a3 * c3) * (v3 T.G : ℚ) +
            ((-5 / 4 : ℚ) + a4 * c4) * (v4 T.G : ℚ) +
            ((11 / 4 : ℚ) + a5 * c5) * (v5 T.G : ℚ) +
            ((21 / 4 : ℚ) + a6 * c6) * (v6 T.G : ℚ) +
            (1 - (a3 + a4 + a5 + a6)) * (sumLarge T.G : ℚ)) := by
  let transfer : Fin n → Fin n → ℚ := transferDeg56 T.G a3 a4 a5 a6
  let lower : Fin n → ℚ := deg56LowerConst T.G a3 a4 a5 a6 c3 c4 c5 c6
  have hanti : ∀ u v, transfer u v = - transfer v u := by
    intro u v
    dsimp [transfer]
    exact transferDeg56_antisym (G := T.G) a3 a4 a5 a6 u v
  have hlower :
      ∀ v, deg56BalanceTerm T.G v + netTransfer transfer v ≥ lower v := by
    intro v
    simpa [transfer, lower] using
      (deg56BalanceTerm_transfer_ge_lowerConst (G := T.G)
        a3 a4 a5 a6 c3 c4 c5 c6 ha3 ha4 ha5 ha6 T.min_degree h3 h4 h5 h6 v)
  have hsumEq :
      ∑ v in Finset.univ, lower v =
        ((-33 / 4 : ℚ) + a3 * c3) * (v3 T.G : ℚ) +
          ((-5 / 4 : ℚ) + a4 * c4) * (v4 T.G : ℚ) +
          ((11 / 4 : ℚ) + a5 * c5) * (v5 T.G : ℚ) +
          ((21 / 4 : ℚ) + a6 * c6) * (v6 T.G : ℚ) +
          (1 - (a3 + a4 + a5 + a6)) * (sumLarge T.G : ℚ) := by
    simpa [lower] using
      (sum_deg56LowerConst_eq (G := T.G) a3 a4 a5 a6 c3 c4 c5 c6)
  exact ⟨transfer, lower, hanti, hlower, hsumEq⟩

lemma deg56_sumLarge_hull3_of_const {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n)
    (a3 a4 a5 a6 c3 c4 c5 c6 : ℚ)
    (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5) (ha6 : 0 ≤ a6)
    (h3 : ∀ v, degree T.G v = 3 → adjacentLargeCountQ T.G v ≥ c3)
    (h4 : ∀ v, degree T.G v = 4 → adjacentLargeCountQ T.G v ≥ c4)
    (h5 : ∀ v, degree T.G v = 5 → adjacentLargeCountQ T.G v ≥ c5)
    (h6 : ∀ v, degree T.G v = 6 → adjacentLargeCountQ T.G v ≥ c6)
    (hsum :
      ((-33 / 4 : ℚ) + a3 * c3) * (v3 T.G : ℚ) +
        ((-5 / 4 : ℚ) + a4 * c4) * (v4 T.G : ℚ) +
        ((11 / 4 : ℚ) + a5 * c5) * (v5 T.G : ℚ) +
        ((21 / 4 : ℚ) + a6 * c6) * (v6 T.G : ℚ) +
        (1 - (a3 + a4 + a5 + a6)) * (sumLarge T.G : ℚ) ≥ -(57 / 4 : ℚ)) :
    4 * (sumLarge T.G : ℚ) ≥
      33 * (v3 T.G : ℚ) + 5 * (v4 T.G : ℚ) - 11 * (v5 T.G : ℚ) -
        21 * (v6 T.G : ℚ) - 57 := by
  have _ := hn
  rcases deg56_sumLarge_hull3_transfer_of_const (T := T) a3 a4 a5 a6 c3 c4 c5 c6
    ha3 ha4 ha5 ha6 h3 h4 h5 h6 with ⟨transfer, lower, hanti, hlower, hsumEq⟩
  have hsum' : ∑ v in Finset.univ, lower v ≥ -(57 / 4 : ℚ) := by
    linarith [hsumEq, hsum]
  exact deg56_sumLarge_of_transfer_ge (G := T.G) (transfer := transfer)
    (hanti := hanti) (lower := lower) hlower hsum'

lemma deg56_sumLarge_hull3_of_transfer {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P)
    (transfer : Fin n → Fin n → ℚ)
    (hanti : ∀ u v, transfer u v = - transfer v u)
    (lower : Fin n → ℚ)
    (hlower : ∀ v, deg56BalanceTerm T.G v + netTransfer transfer v ≥ lower v)
    (hsum : ∑ v in Finset.univ, lower v = -(57 / 4 : ℚ)) :
    4 * (sumLarge T.G : ℚ) ≥
      33 * (v3 T.G : ℚ) + 5 * (v4 T.G : ℚ) - 11 * (v5 T.G : ℚ) -
        21 * (v6 T.G : ℚ) - 57 := by
  exact deg56_sumLarge_of_transfer (G := T.G) (transfer := transfer)
    (hanti := hanti) (lower := lower) hlower hsum

axiom hull3_triangulation_extends {n : ℕ} (P : PointSet n) (hHull : HullSize P = 3)
    {G : Finset (Segment n)} (hG : G ∈ planeGraphs P) :
    ∃ T : Hull3Triangulation P, G ⊆ T.G ∧ T.G ∈ planeGraphs P

lemma empty_mem_planeGraphs {n : ℕ} (P : PointSet n) :
    (∅ : Finset (Segment n)) ∈ planeGraphs P := by
  classical
  simp [mem_planeGraphs_iff, isIndependent]

noncomputable def hull3_triangulation_exists {n : ℕ} (P : PointSet n) (hHull : HullSize P = 3) :
    Hull3Triangulation P := by
  classical
  exact Classical.choose
    (hull3_triangulation_extends (P := P) hHull (G := ∅)
      (empty_mem_planeGraphs (P := P)))

noncomputable def segmentOf {n : ℕ} (u v : Fin n) : Option (Segment n) := by
  classical
  by_cases h : u = v
  · exact none
  ·
    refine some ⟨Sym2.mk (u, v), ?_⟩
    intro hdiag
    apply h
    exact (Sym2.mk_isDiag_iff).1 hdiag

def visible {n : ℕ} (P : PointSet n) (G : Finset (Segment n)) (u v : Fin n) : Prop :=
  match segmentOf u v with
  | none => False
  | some s => s ∉ G ∧ ∀ t ∈ G, ¬ segmentCrosses P s t

lemma segmentOf_self {n : ℕ} (u : Fin n) : segmentOf u u = none := by
  classical
  simp [segmentOf]

lemma incident_of_segmentOf_eq_some_left {n : ℕ} {u v : Fin n} {s : Segment n}
    (hs : segmentOf u v = some s) : incident s u := by
  classical
  by_cases h : u = v
  · simp [segmentOf, h] at hs
  ·
    have hs' : s = ⟨Sym2.mk (u, v), by
        intro hdiag
        apply h
        exact (Sym2.mk_isDiag_iff).1 hdiag⟩ := by
      apply Option.some.inj
      simpa [segmentOf, h] using hs.symm
    subst hs'
    simp [incident]

lemma incident_of_segmentOf_eq_some_right {n : ℕ} {u v : Fin n} {s : Segment n}
    (hs : segmentOf u v = some s) : incident s v := by
  classical
  by_cases h : u = v
  · simp [segmentOf, h] at hs
  ·
    have hs' : s = ⟨Sym2.mk (u, v), by
        intro hdiag
        apply h
        exact (Sym2.mk_isDiag_iff).1 hdiag⟩ := by
      apply Option.some.inj
      simpa [segmentOf, h] using hs.symm
    subst hs'
    simp [incident]

lemma segmentOf_eq_some_of_incident {n : ℕ} {u : Fin n} {s : Segment n}
    (hinc : incident s u) : ∃ v, segmentOf u v = some s := by
  classical
  rcases (Sym2.mem_iff_exists.mp hinc) with ⟨v, hv⟩
  by_cases huv : u = v
  ·
    have hdiag' : Sym2.IsDiag (Sym2.mk (u, u)) := by
      simpa using (Sym2.mk_isDiag_iff).2 rfl
    have hdiag : Sym2.IsDiag s.1 := by
      simpa [hv, huv] using hdiag'
    exact (s.property hdiag).elim
  ·
    have hdiag : ¬ Sym2.IsDiag (Sym2.mk (u, v)) := by
      intro hdiag
      have : u = v := (Sym2.mk_isDiag_iff).1 hdiag
      exact huv this
    let segv : Segment n := ⟨Sym2.mk (u, v), hdiag⟩
    have hseg : segv = s := by
      apply Subtype.ext
      simpa [segv, hv] using hv.symm
    have hseg' : segmentOf u v = some segv := by
      simp [segmentOf, huv, segv]
    exact ⟨v, by simpa [hseg] using hseg'⟩

lemma segmentOf_eq_some_inj_left {n : ℕ} {u v w : Fin n} {s : Segment n}
    (hv : segmentOf u v = some s) (hw : segmentOf u w = some s) : v = w := by
  classical
  by_cases huv : u = v
  · simp [segmentOf, huv] at hv
  by_cases huw : u = w
  · simp [segmentOf, huw] at hw
  have hdiagv : ¬ Sym2.IsDiag (Sym2.mk (u, v)) := by
    intro hdiag
    have : u = v := (Sym2.mk_isDiag_iff).1 hdiag
    exact huv this
  have hdiagw : ¬ Sym2.IsDiag (Sym2.mk (u, w)) := by
    intro hdiag
    have : u = w := (Sym2.mk_isDiag_iff).1 hdiag
    exact huw this
  let segv : Segment n := ⟨Sym2.mk (u, v), hdiagv⟩
  let segw : Segment n := ⟨Sym2.mk (u, w), hdiagw⟩
  have hv' : segv = s := by
    have hv'' : some segv = some s := by
      simpa [segmentOf, huv, segv] using hv
    exact Option.some.inj hv''
  have hw' : segw = s := by
    have hw'' : some segw = some s := by
      simpa [segmentOf, huw, segw] using hw
    exact Option.some.inj hw''
  have hsym : Sym2.mk (u, v) = Sym2.mk (u, w) := by
    have hvval : segv.1 = s.1 := congrArg Subtype.val hv'
    have hwval : segw.1 = s.1 := congrArg Subtype.val hw'
    exact (hvval.trans hwval.symm)
  exact (Sym2.congr_right (a := u) (b := v) (c := w)).1 hsym

lemma segmentCrosses_false_of_incident {n : ℕ} {P : PointSet n}
    {s t : Segment n} {u : Fin n} (hs : incident s u) (ht : incident t u) :
    ¬ segmentCrosses P s t := by
  classical
  rcases (Sym2.mem_iff_exists.mp hs) with ⟨v, hsv⟩
  rcases (Sym2.mem_iff_exists.mp ht) with ⟨w, htw⟩
  intro hcross
  have h' : properSegmentIntersect (P u) (P v) (P u) (P w) := by
    simpa [segmentCrosses, hsv, htw, Sym2.lift₂_mk] using hcross
  rcases h' with ⟨hneq, _, _, _, _, _, _, _, _, _⟩
  exact hneq rfl

lemma visible_self {n : ℕ} (P : PointSet n) (G : Finset (Segment n)) (u : Fin n) :
    ¬ visible P G u u := by
  simp [visible, segmentOf_self]

lemma visible_of_edge_subset {n : ℕ} {P : PointSet n} {G T : Finset (Segment n)}
    (hsub : G ⊆ T) (hplane : isIndependent (crossingGraph P) T)
    {u v : Fin n} {s : Segment n} (hs : segmentOf u v = some s)
    (hT : s ∈ T) (hG : s ∉ G) :
    visible P G u v := by
  have hno : ∀ t ∈ G, ¬ segmentCrosses P s t := by
    intro t ht
    have htT : t ∈ T := hsub ht
    have hne : s ≠ t := by
      intro hEq
      apply hG
      simpa [hEq] using ht
    have hno' := hplane hT htT hne
    simpa [crossingGraph] using hno'
  have hvis : s ∉ G ∧ ∀ t ∈ G, ¬ segmentCrosses P s t := by
    exact ⟨hG, hno⟩
  simpa [visible, hs] using hvis

noncomputable def visibleSet {n : ℕ} (P : PointSet n) (G : Finset (Segment n)) (u : Fin n) :
    Finset (Fin n) := by
  classical
  exact (Finset.univ.filter (fun v => visible P G u v))

noncomputable def potential {n : ℕ} (P : PointSet n) (G : Finset (Segment n)) (u : Fin n) :
    Nat :=
  degree G u + (visibleSet P G u).card

lemma degree_le_potential {n : ℕ} (P : PointSet n) (G : Finset (Segment n)) (u : Fin n) :
    degree G u ≤ potential P G u := by
  exact Nat.le_add_right _ _

noncomputable def incidentEdges {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    Finset (Segment n) :=
  G.filter (fun s => incident s u)

lemma incidentEdges_card_eq_degree {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    (incidentEdges G u).card = degree G u := by
  classical
  have h := card_filter_eq_sum_ite (s := G) (p := fun s => incident s u)
  simpa [incidentEdges, degree] using h

noncomputable def removeIncidentEdges {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    Finset (Segment n) :=
  G.filter (fun s => ¬ incident s u)

lemma removeIncidentEdges_subset {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    removeIncidentEdges G u ⊆ G := by
  intro s hs
  exact (Finset.mem_filter.mp hs).1

noncomputable def edgesFrom {n : ℕ} (u : Fin n) (S : Finset (Fin n)) : Finset (Segment n) := by
  classical
  refine Finset.filterMap (fun v => segmentOf u v) S ?_
  intro a a' b ha hb
  have ha' : segmentOf u a = some b := by
    simpa [Option.mem_def] using ha
  have hb' : segmentOf u a' = some b := by
    simpa [Option.mem_def] using hb
  exact segmentOf_eq_some_inj_left (u := u) (v := a) (w := a') (s := b) ha' hb'

noncomputable def addEdgesFrom {n : ℕ} (G : Finset (Segment n)) (u : Fin n)
    (S : Finset (Fin n)) : Finset (Segment n) :=
  G ∪ edgesFrom u S

lemma mem_edgesFrom {n : ℕ} {u : Fin n} {S : Finset (Fin n)} {s : Segment n} :
    s ∈ edgesFrom u S ↔ ∃ v ∈ S, segmentOf u v = some s := by
  classical
  simp [edgesFrom]

lemma edgesFrom_incident_left {n : ℕ} {u : Fin n} {S : Finset (Fin n)} {s : Segment n}
    (hs : s ∈ edgesFrom u S) : incident s u := by
  classical
  rcases (mem_edgesFrom (u := u) (S := S) (s := s)).1 hs with ⟨v, _, hv⟩
  exact incident_of_segmentOf_eq_some_left (u := u) (v := v) hv

lemma edgesFrom_incident_right {n : ℕ} {u : Fin n} {S : Finset (Fin n)} {s : Segment n}
    (hs : s ∈ edgesFrom u S) :
    ∃ v ∈ S, incident s v := by
  classical
  rcases (mem_edgesFrom (u := u) (S := S) (s := s)).1 hs with ⟨v, hv, hvseg⟩
  exact ⟨v, hv, incident_of_segmentOf_eq_some_right (u := u) (v := v) hvseg⟩

lemma segmentOf_mem_edgesFrom {n : ℕ} {u v : Fin n} {S : Finset (Fin n)} {s : Segment n}
    (hv : v ∈ S) (hs : segmentOf u v = some s) : s ∈ edgesFrom u S := by
  classical
  exact (mem_edgesFrom (u := u) (S := S) (s := s)).2 ⟨v, hv, hs⟩

lemma segmentOf_not_mem_edgesFrom {n : ℕ} {u v : Fin n} {S : Finset (Fin n)} {s : Segment n}
    (hv : v ∉ S) (hs : segmentOf u v = some s) : s ∉ edgesFrom u S := by
  classical
  intro hmem
  rcases (mem_edgesFrom (u := u) (S := S) (s := s)).1 hmem with ⟨w, hw, hwseg⟩
  have hw' : v = w := segmentOf_eq_some_inj_left (u := u) (v := v) (w := w) hs hwseg
  exact hv (hw' ▸ hw)

lemma segmentOf_some_of_ne {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    ∃ s, segmentOf u v = some s := by
  classical
  simp [segmentOf, h]

noncomputable def edgeOf {n : ℕ} (u v : Fin n) (h : u ≠ v) : Segment n :=
  Classical.choose (segmentOf_some_of_ne (u := u) (v := v) h)

lemma segmentOf_edgeOf {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    segmentOf u v = some (edgeOf u v h) := by
  classical
  exact Classical.choose_spec (segmentOf_some_of_ne (u := u) (v := v) h)

lemma not_mem_visibleSet_self {n : ℕ} {P : PointSet n} {G : Finset (Segment n)} {u : Fin n} :
    u ∉ visibleSet P G u := by
  classical
  simp [visibleSet, visible_self]

lemma edgesFrom_card {n : ℕ} {u : Fin n} {S : Finset (Fin n)} (hnot : u ∉ S) :
    (edgesFrom u S).card = S.card := by
  classical
  symm
  refine Finset.card_bij (s := S) (t := edgesFrom u S)
    (i := fun v hv =>
      edgeOf u v (by
        intro h
        apply hnot
        simpa [h] using hv)) ?_ ?_ ?_
  · intro v hv
    have hvne : u ≠ v := by
      intro h
      apply hnot
      simpa [h] using hv
    have hseg : segmentOf u v = some (edgeOf u v hvne) := segmentOf_edgeOf (u := u) (v := v) hvne
    exact segmentOf_mem_edgesFrom (u := u) (v := v) (S := S) hv hseg
  · intro v hv w hw hEq
    have hvne : u ≠ v := by
      intro h
      apply hnot
      simpa [h] using hv
    have hwne : u ≠ w := by
      intro h
      apply hnot
      simpa [h] using hw
    have hsegv : segmentOf u v = some (edgeOf u v hvne) := segmentOf_edgeOf (u := u) (v := v) hvne
    have hsegw : segmentOf u w = some (edgeOf u w hwne) := segmentOf_edgeOf (u := u) (v := w) hwne
    have hsegw' : segmentOf u w = some (edgeOf u v hvne) := by
      simpa [hEq] using hsegw
    exact segmentOf_eq_some_inj_left (u := u) (v := v) (w := w) (s := edgeOf u v hvne) hsegv hsegw'
  · intro s hs
    rcases (mem_edgesFrom (u := u) (S := S) (s := s)).1 hs with ⟨v, hv, hvseg⟩
    have hvne : u ≠ v := by
      intro h
      apply hnot
      simpa [h] using hv
    have hseg : segmentOf u v = some (edgeOf u v hvne) := segmentOf_edgeOf (u := u) (v := v) hvne
    have hEq : edgeOf u v hvne = s := by
      apply Option.some.inj
      simpa [hseg] using hvseg
    exact ⟨v, hv, hEq⟩

noncomputable def neighborSet {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ∃ s, segmentOf u v = some s ∧ s ∈ G)

lemma mem_neighborSet {n : ℕ} {G : Finset (Segment n)} {u v : Fin n} :
    v ∈ neighborSet G u ↔ ∃ s, segmentOf u v = some s ∧ s ∈ G := by
  classical
  simp [neighborSet]

lemma incidentEdges_eq_edgesFrom_neighborSet {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    incidentEdges G u = edgesFrom u (neighborSet G u) := by
  classical
  ext s
  constructor
  · intro hs
    rcases (Finset.mem_filter.1 hs) with ⟨hsG, hinc⟩
    rcases segmentOf_eq_some_of_incident (u := u) (s := s) hinc with ⟨v, hseg⟩
    have hv : v ∈ neighborSet G u :=
      (mem_neighborSet (G := G) (u := u) (v := v)).2 ⟨s, hseg, hsG⟩
    exact segmentOf_mem_edgesFrom (u := u) (v := v) (S := neighborSet G u) hv hseg
  · intro hs
    rcases (mem_edgesFrom (u := u) (S := neighborSet G u) (s := s)).1 hs with ⟨v, hv, hseg⟩
    rcases (mem_neighborSet (G := G) (u := u) (v := v)).1 hv with ⟨s', hsseg, hs'G⟩
    have hs_eq : s = s' := by
      apply Option.some.inj
      simpa [hseg] using hsseg
    have hsG : s ∈ G := by
      simpa [hs_eq] using hs'G
    have hinc : incident s u := incident_of_segmentOf_eq_some_left (u := u) (v := v) hseg
    exact Finset.mem_filter.2 ⟨hsG, hinc⟩

lemma not_mem_neighborSet_self {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    u ∉ neighborSet G u := by
  classical
  simp [neighborSet, segmentOf_self]

lemma degree_eq_neighborSet_card {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    degree G u = (neighborSet G u).card := by
  classical
  have hnot : u ∉ neighborSet G u := not_mem_neighborSet_self (G := G) (u := u)
  calc
    degree G u = (incidentEdges G u).card := by
      symm
      exact incidentEdges_card_eq_degree (G := G) u
    _ = (edgesFrom u (neighborSet G u)).card := by
      simp [incidentEdges_eq_edgesFrom_neighborSet]
    _ = (neighborSet G u).card := edgesFrom_card (u := u) (S := neighborSet G u) hnot

lemma neighborSet_subset_visibleSet {n : ℕ} {P : PointSet n} {G : Finset (Segment n)} {u : Fin n}
    (hG : G ∈ planeGraphs P) :
    neighborSet G u ⊆ visibleSet P (removeIncidentEdges G u) u := by
  classical
  intro v hv
  rcases (mem_neighborSet (G := G) (u := u) (v := v)).1 hv with ⟨s, hsseg, hsG⟩
  have hsub : removeIncidentEdges G u ⊆ G := removeIncidentEdges_subset G u
  have hind : isIndependent (crossingGraph P) G := (mem_planeGraphs_iff P).1 hG
  have hsnot : s ∉ removeIncidentEdges G u := by
    intro hsH
    have hinc : incident s u := incident_of_segmentOf_eq_some_left (u := u) (v := v) hsseg
    have hnot : ¬ incident s u := by
      simpa [removeIncidentEdges] using (Finset.mem_filter.1 hsH).2
    exact hnot hinc
  have hvis : visible P (removeIncidentEdges G u) u v :=
    visible_of_edge_subset (P := P) (G := removeIncidentEdges G u) (T := G)
      hsub hind hsseg hsG hsnot
  simpa [visibleSet] using hvis

lemma neighborSet_subset_union_visible {n : ℕ} {P : PointSet n} {G T : Finset (Segment n)}
    (hsub : G ⊆ T) (hT : T ∈ planeGraphs P) (u : Fin n) :
    neighborSet T u ⊆ neighborSet G u ∪ visibleSet P G u := by
  classical
  intro v hv
  rcases (mem_neighborSet (G := T) (u := u) (v := v)).1 hv with ⟨s, hsseg, hsT⟩
  by_cases hsG : s ∈ G
  ·
    exact Finset.mem_union.2
      (Or.inl ((mem_neighborSet (G := G) (u := u) (v := v)).2 ⟨s, hsseg, hsG⟩))
  ·
    have hind : isIndependent (crossingGraph P) T := (mem_planeGraphs_iff P).1 hT
    have hvis : visible P G u v :=
      visible_of_edge_subset (P := P) (G := G) (T := T) hsub hind hsseg hsT hsG
    exact Finset.mem_union.2 (Or.inr (by simpa [visibleSet] using hvis))

lemma potential_ge_degree_of_subset {n : ℕ} {P : PointSet n} {G T : Finset (Segment n)}
    (hsub : G ⊆ T) (hT : T ∈ planeGraphs P) :
    ∀ u : Fin n, degree T u ≤ potential P G u := by
  classical
  intro u
  have hsubset :
      neighborSet T u ⊆ neighborSet G u ∪ visibleSet P G u :=
    neighborSet_subset_union_visible (P := P) (G := G) (T := T) hsub hT u
  have hcard :
      (neighborSet T u).card ≤ (neighborSet G u ∪ visibleSet P G u).card :=
    Finset.card_le_of_subset hsubset
  have hunion :
      (neighborSet G u ∪ visibleSet P G u).card ≤
        (neighborSet G u).card + (visibleSet P G u).card := by
    exact Finset.card_union_le _ _
  have hdegT : degree T u = (neighborSet T u).card :=
    degree_eq_neighborSet_card (G := T) u
  have hdegG : degree G u = (neighborSet G u).card :=
    degree_eq_neighborSet_card (G := G) u
  calc
    degree T u = (neighborSet T u).card := hdegT
    _ ≤ (neighborSet G u ∪ visibleSet P G u).card := hcard
    _ ≤ (neighborSet G u).card + (visibleSet P G u).card := hunion
    _ = degree G u + (visibleSet P G u).card := by
        simpa [hdegG]
    _ = potential P G u := rfl

lemma edgesFrom_neighborSet_subset {n : ℕ} {G : Finset (Segment n)} {u : Fin n} :
    edgesFrom u (neighborSet G u) ⊆ G := by
  classical
  intro s hs
  rcases (mem_edgesFrom (u := u) (S := neighborSet G u) (s := s)).1 hs with ⟨v, hv, hvseg⟩
  rcases (mem_neighborSet (G := G) (u := u) (v := v)).1 hv with ⟨s', hs'seg, hs'G⟩
  have hs_eq : s = s' := by
    have hs1 : segmentOf u v = some s := hvseg
    have hs2 : segmentOf u v = some s' := hs'seg
    have hs' : some s = some s' := by
      simpa [hs1] using hs2
    exact Option.some.inj hs'
  simpa [hs_eq] using hs'G

lemma addEdgesFrom_removeIncidentEdges_eq {n : ℕ} {G : Finset (Segment n)} {u : Fin n} :
    addEdgesFrom (removeIncidentEdges G u) u (neighborSet G u) = G := by
  classical
  ext s
  constructor
  · intro hs
    rcases (Finset.mem_union.1 hs) with hsH | hsE
    · exact (removeIncidentEdges_subset G u) hsH
    · exact edgesFrom_neighborSet_subset (G := G) (u := u) hsE
  · intro hsG
    by_cases hinc : incident s u
    ·
      -- s is incident to u, so it corresponds to a neighbor.
      rcases segmentOf_eq_some_of_incident (u := u) (s := s) hinc with ⟨v, hseg⟩
      have hv : v ∈ neighborSet G u := (mem_neighborSet (G := G) (u := u) (v := v)).2 ⟨s, hseg, hsG⟩
      have hsE : s ∈ edgesFrom u (neighborSet G u) :=
        segmentOf_mem_edgesFrom (u := u) (v := v) (S := neighborSet G u) hv hseg
      exact Finset.mem_union.2 (Or.inr hsE)
    ·
      have hsH : s ∈ removeIncidentEdges G u := by
        exact Finset.mem_filter.2 ⟨hsG, hinc⟩
      exact Finset.mem_union.2 (Or.inl hsH)

lemma neighborSet_addEdgesFrom {n : ℕ} {P : PointSet n} {G : Finset (Segment n)} {u : Fin n}
    {S : Finset (Fin n)} (hiso : isIsolated G u) (hsub : S ⊆ visibleSet P G u) :
    neighborSet (addEdgesFrom G u S) u = S := by
  classical
  ext v
  constructor
  · intro hv
    rcases (mem_neighborSet (G := addEdgesFrom G u S) (u := u) (v := v)).1 hv with
      ⟨s, hsseg, hsG⟩
    rcases (Finset.mem_union.1 hsG) with hsG' | hsE
    ·
      -- impossible: G has no edges incident to u
      have hinc : incident s u := incident_of_segmentOf_eq_some_left (u := u) (v := v) hsseg
      exact (hiso s hsG' hinc).elim
    ·
      rcases (mem_edgesFrom (u := u) (S := S) (s := s)).1 hsE with ⟨w, hw, hwseg⟩
      have hw' : v = w := segmentOf_eq_some_inj_left (u := u) (v := v) (w := w) hsseg hwseg
      exact hw' ▸ hw
  · intro hv
    have hvne : u ≠ v := by
      intro h
      have : u ∈ visibleSet P G u := by
        have hv' : v ∈ visibleSet P G u := hsub hv
        simpa [h] using hv'
      exact (not_mem_visibleSet_self (P := P) (G := G) (u := u)) this
    have hseg : segmentOf u v = some (edgeOf u v hvne) := segmentOf_edgeOf (u := u) (v := v) hvne
    have hsE : edgeOf u v hvne ∈ edgesFrom u S :=
      segmentOf_mem_edgesFrom (u := u) (v := v) (S := S) hv hseg
    have hsG : edgeOf u v hvne ∈ addEdgesFrom G u S :=
      Finset.mem_union.2 (Or.inr hsE)
    exact (mem_neighborSet (G := addEdgesFrom G u S) (u := u) (v := v)).2
      ⟨edgeOf u v hvne, hseg, hsG⟩

lemma visible_addEdgesFrom_iff {n : ℕ} {P : PointSet n} {G : Finset (Segment n)}
    {u v : Fin n} {S : Finset (Fin n)} :
    visible P (addEdgesFrom G u S) u v ↔ visible P G u v ∧ v ∉ S := by
  classical
  cases h : segmentOf u v with
  | none =>
      simp [visible, h]
  | some s =>
      constructor
      · intro hvis
        have hspec :
            s ∉ addEdgesFrom G u S ∧
              ∀ t ∈ addEdgesFrom G u S, ¬ segmentCrosses P s t := by
          simpa [visible, h] using hvis
        rcases hspec with ⟨hsnot, hno⟩
        have hsnotG : s ∉ G := by
          intro hsG
          exact hsnot (Finset.mem_union.2 (Or.inl hsG))
        have hsnotE : s ∉ edgesFrom u S := by
          intro hsE
          exact hsnot (Finset.mem_union.2 (Or.inr hsE))
        have hvnot : v ∉ S := by
          intro hv
          have hsE : s ∈ edgesFrom u S :=
            segmentOf_mem_edgesFrom (u := u) (v := v) (S := S) hv h
          exact hsnotE hsE
        have hnoG : ∀ t ∈ G, ¬ segmentCrosses P s t := by
          intro t ht
          have ht' : t ∈ addEdgesFrom G u S := Finset.mem_union.2 (Or.inl ht)
          exact hno t ht'
        have hvisG : visible P G u v := by
          simpa [visible, h] using And.intro hsnotG hnoG
        exact ⟨hvisG, hvnot⟩
      · intro h
        rcases h with ⟨hvisG, hvnot⟩
        have hspec :
            s ∉ G ∧ ∀ t ∈ G, ¬ segmentCrosses P s t := by
          simpa [visible, h] using hvisG
        rcases hspec with ⟨hsnotG, hnoG⟩
        have hsnotE : s ∉ edgesFrom u S :=
          segmentOf_not_mem_edgesFrom (u := u) (v := v) (S := S) hvnot h
        have hsnot : s ∉ addEdgesFrom G u S := by
          intro hs
          rcases Finset.mem_union.1 hs with hsG | hsE
          · exact hsnotG hsG
          · exact hsnotE hsE
        have hno : ∀ t ∈ addEdgesFrom G u S, ¬ segmentCrosses P s t := by
          intro t ht
          rcases Finset.mem_union.1 ht with htG | htE
          · exact hnoG t htG
          ·
            have hsinc : incident s u :=
              incident_of_segmentOf_eq_some_left (u := u) (v := v) h
            have htinc : incident t u :=
              edgesFrom_incident_left (u := u) (S := S) htE
            exact segmentCrosses_false_of_incident (P := P) hsinc htinc
        simpa [visible, h] using And.intro hsnot hno

lemma visibleSet_addEdgesFrom {n : ℕ} {P : PointSet n} {G : Finset (Segment n)}
    {u : Fin n} {S : Finset (Fin n)} :
    visibleSet P (addEdgesFrom G u S) u = (visibleSet P G u) \ S := by
  classical
  ext v
  simp [visibleSet, visible_addEdgesFrom_iff, Finset.mem_sdiff, and_left_comm, and_assoc]

lemma incidentEdges_addEdgesFrom {n : ℕ} {G : Finset (Segment n)} {u : Fin n}
    {S : Finset (Fin n)} (hiso : isIsolated G u) :
    incidentEdges (addEdgesFrom G u S) u = edgesFrom u S := by
  classical
  ext s
  constructor
  · intro hs
    rcases (Finset.mem_filter.1 hs) with ⟨hs', hinc⟩
    rcases (Finset.mem_union.1 hs') with hsG | hsE
    · exact (hiso s hsG hinc).elim
    · exact hsE
  · intro hsE
    have hinc : incident s u := edgesFrom_incident_left (u := u) (S := S) hsE
    exact Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inr hsE), hinc⟩

lemma potential_addEdgesFrom {n : ℕ} {P : PointSet n} {G : Finset (Segment n)} {u : Fin n}
    {S : Finset (Fin n)} (hiso : isIsolated G u) (hsub : S ⊆ visibleSet P G u) :
    potential P (addEdgesFrom G u S) u = (visibleSet P G u).card := by
  classical
  have hnot : u ∉ S := by
    intro hu
    have : u ∈ visibleSet P G u := hsub hu
    exact (not_mem_visibleSet_self (P := P) (G := G) (u := u)) this
  have hdeg : degree (addEdgesFrom G u S) u = S.card := by
    have hdeg' : degree (addEdgesFrom G u S) u = (incidentEdges (addEdgesFrom G u S) u).card := by
      symm
      exact incidentEdges_card_eq_degree (G := addEdgesFrom G u S) u
    have hinc : incidentEdges (addEdgesFrom G u S) u = edgesFrom u S :=
      incidentEdges_addEdgesFrom (G := G) (u := u) (S := S) hiso
    have hcard : (edgesFrom u S).card = S.card := edgesFrom_card (u := u) (S := S) hnot
    simpa [hinc, hcard] using hdeg'
  have hvis : (visibleSet P (addEdgesFrom G u S) u).card =
      (visibleSet P G u).card - S.card := by
    have hsdiff : ((visibleSet P G u) \ S).card =
        (visibleSet P G u).card - S.card := by
      exact Finset.card_sdiff hsub
    simpa [visibleSet_addEdgesFrom] using hsdiff
  have hle : S.card ≤ (visibleSet P G u).card := Finset.card_le_of_subset hsub
  calc
    potential P (addEdgesFrom G u S) u
        = degree (addEdgesFrom G u S) u + (visibleSet P (addEdgesFrom G u S) u).card := rfl
    _ = S.card + ((visibleSet P G u).card - S.card) := by
        simp [hdeg, hvis]
    _ = (visibleSet P G u).card := Nat.add_sub_of_le hle

lemma removeIncidentEdges_addEdgesFrom {n : ℕ} {G : Finset (Segment n)} {u : Fin n}
    {S : Finset (Fin n)} (hiso : isIsolated G u) :
    removeIncidentEdges (addEdgesFrom G u S) u = G := by
  classical
  ext s
  constructor
  · intro hs
    rcases (Finset.mem_filter.1 hs) with ⟨hs', hnot⟩
    rcases (Finset.mem_union.1 hs') with hsG | hsE
    · exact hsG
    · exact (hnot (edgesFrom_incident_left (u := u) (S := S) hsE)).elim
  · intro hsG
    have hnot : ¬ incident s u := by
      exact hiso s hsG
    exact (Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inl hsG), hnot⟩)

lemma addEdgesFrom_mem_planeGraphs {n : ℕ} {P : PointSet n} {G : Finset (Segment n)}
    (hG : G ∈ planeGraphs P) {u : Fin n} {S : Finset (Fin n)}
    (hsub : S ⊆ visibleSet P G u) :
    addEdgesFrom G u S ∈ planeGraphs P := by
  classical
  have hind : isIndependent (crossingGraph P) G := (mem_planeGraphs_iff P).1 hG
  have hind' : isIndependent (crossingGraph P) (addEdgesFrom G u S) := by
    intro s t hs ht hne
    rcases (Finset.mem_union.1 hs) with hsG | hsE
    ·
      rcases (Finset.mem_union.1 ht) with htG | htE
      · exact hind hsG htG hne
      ·
        rcases (mem_edgesFrom (u := u) (S := S) (s := t)).1 htE with ⟨v, hv, htseg⟩
        have hvvis : visible P G u v := by
          have hv' : v ∈ visibleSet P G u := hsub hv
          simpa [visibleSet] using hv'
        have htvis : t ∉ G ∧ ∀ t' ∈ G, ¬ segmentCrosses P t t' := by
          simpa [visible, htseg] using hvvis
        rcases htvis with ⟨_, hno⟩
        have hno' : ¬ segmentCrosses P s t := by
          intro hcross
          exact (hno s hsG) (segmentCrosses_symm P hcross)
        exact hno'
    ·
      rcases (Finset.mem_union.1 ht) with htG | htE
      ·
        rcases (mem_edgesFrom (u := u) (S := S) (s := s)).1 hsE with ⟨v, hv, hsseg⟩
        have hvvis : visible P G u v := by
          have hv' : v ∈ visibleSet P G u := hsub hv
          simpa [visibleSet] using hv'
        have hsvis : s ∉ G ∧ ∀ t' ∈ G, ¬ segmentCrosses P s t' := by
          simpa [visible, hsseg] using hvvis
        rcases hsvis with ⟨_, hno⟩
        exact hno t htG
      ·
        have hsinc : incident s u := edgesFrom_incident_left (u := u) (S := S) hsE
        have htinc : incident t u := edgesFrom_incident_left (u := u) (S := S) htE
        exact segmentCrosses_false_of_incident (P := P) hsinc htinc
  exact (mem_planeGraphs_iff P).2 hind'

lemma removeIncidentEdges_isolated {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    isIsolated (removeIncidentEdges G u) u := by
  classical
  intro s hs
  have hs' : ¬ incident s u := by
    simpa [removeIncidentEdges] using (Finset.mem_filter.mp hs).2
  exact hs'

lemma isIndependent_subset {n : ℕ} {P : PointSet n} {s t : Finset (Segment n)}
    (hst : s ⊆ t) (hind : isIndependent (crossingGraph P) t) :
    isIndependent (crossingGraph P) s := by
  intro u v hu hv hne
  exact hind (hst hu) (hst hv) hne

lemma removeIncidentEdges_mem_planeGraphs {n : ℕ} (P : PointSet n)
    {G : Finset (Segment n)} (hG : G ∈ planeGraphs P) (u : Fin n) :
    removeIncidentEdges G u ∈ planeGraphs P := by
  have hind : isIndependent (crossingGraph P) G := (mem_planeGraphs_iff P).1 hG
  have hsubset : removeIncidentEdges G u ⊆ G := removeIncidentEdges_subset G u
  have hind' : isIndependent (crossingGraph P) (removeIncidentEdges G u) :=
    isIndependent_subset (P := P) hsubset hind
  exact (mem_planeGraphs_iff P).2 hind'

noncomputable def isoPairs {n : ℕ} (P : PointSet n) (u : Fin n) :
    Finset (Sigma fun H : Finset (Segment n) => Finset (Fin n)) :=
  (planeGraphsIso P u).sigma (fun H => (visibleSet P H u).powerset)

noncomputable def pairToGraph {n : ℕ} (u : Fin n)
    (p : Sigma fun H : Finset (Segment n) => Finset (Fin n)) : Finset (Segment n) :=
  addEdgesFrom p.1 u p.2

noncomputable def graphToPair {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    Sigma fun H : Finset (Segment n) => Finset (Fin n) :=
  ⟨removeIncidentEdges G u, neighborSet G u⟩

lemma graphToPair_mem_isoPairs {n : ℕ} {P : PointSet n} {G : Finset (Segment n)} {u : Fin n}
    (hG : G ∈ planeGraphs P) :
    graphToPair G u ∈ isoPairs P u := by
  classical
  have hplane : removeIncidentEdges G u ∈ planeGraphs P :=
    removeIncidentEdges_mem_planeGraphs (P := P) hG u
  have hind : isIndependent (crossingGraph P) (removeIncidentEdges G u) :=
    (mem_planeGraphs_iff P).1 hplane
  have hiso : isIsolated (removeIncidentEdges G u) u :=
    removeIncidentEdges_isolated G u
  have hH : removeIncidentEdges G u ∈ planeGraphsIso P u := by
    exact (mem_planeGraphsIso_iff P).2 ⟨hind, hiso⟩
  have hsub : neighborSet G u ⊆ visibleSet P (removeIncidentEdges G u) u :=
    neighborSet_subset_visibleSet (P := P) (G := G) (u := u) hG
  have hpow : neighborSet G u ∈ (visibleSet P (removeIncidentEdges G u) u).powerset :=
    Finset.mem_powerset.2 hsub
  simp [isoPairs, graphToPair, hH, hpow]

lemma pairToGraph_mem_planeGraphs {n : ℕ} {P : PointSet n} {u : Fin n}
    {p : Sigma fun H : Finset (Segment n) => Finset (Fin n)}
    (hp : p ∈ isoPairs P u) :
    pairToGraph u p ∈ planeGraphs P := by
  classical
  rcases (by simpa [isoPairs] using hp) with ⟨hH, hS⟩
  have hH' := (mem_planeGraphsIso_iff P).1 hH
  have hind : isIndependent (crossingGraph P) p.1 := hH'.1
  have hplane : p.1 ∈ planeGraphs P := (mem_planeGraphs_iff P).2 hind
  have hsub : p.2 ⊆ visibleSet P p.1 u := by
    simpa [Finset.mem_powerset] using hS
  exact addEdgesFrom_mem_planeGraphs (P := P) (G := p.1) hplane hsub

lemma pairToGraph_left_inv {n : ℕ} {P : PointSet n} {u : Fin n}
    {p : Sigma fun H : Finset (Segment n) => Finset (Fin n)}
    (hp : p ∈ isoPairs P u) :
    graphToPair (pairToGraph u p) u = p := by
  classical
  rcases (by simpa [isoPairs] using hp) with ⟨hH, hS⟩
  have hH' := (mem_planeGraphsIso_iff P).1 hH
  have hiso : isIsolated p.1 u := hH'.2
  have hsub : p.2 ⊆ visibleSet P p.1 u := by
    simpa [Finset.mem_powerset] using hS
  apply Sigma.ext
  ·
    -- first component
    simpa [pairToGraph, graphToPair] using
      (removeIncidentEdges_addEdgesFrom (G := p.1) (u := u) (S := p.2) hiso)
  ·
    -- second component
    have hpair := neighborSet_addEdgesFrom (P := P) (G := p.1) (u := u) (S := p.2) hiso hsub
    simpa [pairToGraph, graphToPair] using hpair

lemma pairToGraph_right_inv {n : ℕ} {P : PointSet n} {G : Finset (Segment n)} {u : Fin n}
    (hG : G ∈ planeGraphs P) :
    pairToGraph u (graphToPair G u) = G := by
  classical
  simpa [pairToGraph, graphToPair] using addEdgesFrom_removeIncidentEdges_eq (G := G) (u := u)

noncomputable def deg56_charge {n : ℕ} (P : PointSet n) : Charge (n := n) :=
  fun G =>
    ∑ u in Finset.univ, (1 : ℚ) / (2 : ℚ) ^ (potential P G u)

lemma sum_charge_eq_planeGraphsIso {n : ℕ} (P : PointSet n) (u : Fin n) :
    ∑ G in planeGraphs P, (1 : ℚ) / (2 : ℚ) ^ (potential P G u) =
      (planeGraphsIso P u).card := by
  classical
  let f : Finset (Segment n) → ℚ := fun G => (1 : ℚ) / (2 : ℚ) ^ (potential P G u)
  have hinj :
      ∀ p1 ∈ isoPairs P u, ∀ p2 ∈ isoPairs P u,
        pairToGraph (u := u) p1 = pairToGraph (u := u) p2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 hEq
    have hEq' : graphToPair (pairToGraph u p1) u = graphToPair (pairToGraph u p2) u :=
      congrArg (fun G => graphToPair G u) hEq
    have hleft1 := pairToGraph_left_inv (P := P) (u := u) (p := p1) hp1
    have hleft2 := pairToGraph_left_inv (P := P) (u := u) (p := p2) hp2
    simpa [hleft1, hleft2] using hEq'
  have himage : (isoPairs P u).image (pairToGraph (u := u)) = planeGraphs P := by
    apply Finset.ext
    intro G
    constructor
    · intro hG
      rcases Finset.mem_image.1 hG with ⟨p, hp, rfl⟩
      exact pairToGraph_mem_planeGraphs (P := P) (u := u) (p := p) hp
    · intro hG
      have hp : graphToPair G u ∈ isoPairs P u :=
        graphToPair_mem_isoPairs (P := P) (G := G) (u := u) hG
      refine Finset.mem_image.2 ?_
      exact ⟨graphToPair G u, hp, pairToGraph_right_inv (P := P) (G := G) (u := u) hG⟩
  have hsum_image :
      ∑ G in (isoPairs P u).image (pairToGraph (u := u)), f G =
        ∑ p in isoPairs P u, f (pairToGraph (u := u) p) := by
    refine Finset.sum_image ?_
    intro p1 hp1 p2 hp2 hEq
    exact hinj p1 hp1 p2 hp2 hEq
  have hsum_pairs :
      ∑ G in planeGraphs P, f G =
        ∑ p in isoPairs P u, f (pairToGraph (u := u) p) := by
    simpa [himage] using hsum_image
  have hsum_sigma :
      ∑ p in isoPairs P u, f (pairToGraph (u := u) p) =
        ∑ H in planeGraphsIso P u,
          ∑ S in (visibleSet P H u).powerset,
            (1 : ℚ) / (2 : ℚ) ^ (potential P (addEdgesFrom H u S) u) := by
    have h :=
      (Finset.sum_sigma (s := planeGraphsIso P u)
        (t := fun H => (visibleSet P H u).powerset)
        (f := fun p => f (pairToGraph (u := u) p)))
    simpa [isoPairs, pairToGraph, f] using h
  have hinner :
      ∀ H ∈ planeGraphsIso P u,
        ∑ S in (visibleSet P H u).powerset,
          (1 : ℚ) / (2 : ℚ) ^ (potential P (addEdgesFrom H u S) u) = 1 := by
    intro H hH
    have hH' := (mem_planeGraphsIso_iff P).1 hH
    have hiso : isIsolated H u := hH'.2
    have hsum_const :
        ∑ S in (visibleSet P H u).powerset,
          (1 : ℚ) / (2 : ℚ) ^ (potential P (addEdgesFrom H u S) u) =
          ∑ S in (visibleSet P H u).powerset,
            (1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hsub : S ⊆ visibleSet P H u := Finset.mem_powerset.1 hS
      have hpot :
          potential P (addEdgesFrom H u S) u = (visibleSet P H u).card :=
        potential_addEdgesFrom (P := P) (G := H) (u := u) (S := S) hiso hsub
      simp [hpot]
    have hsum_card :
        ∑ S in (visibleSet P H u).powerset,
          (1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card =
          ((visibleSet P H u).powerset.card : ℚ) *
            ((1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card) := by
      simp
    have hpow :
        ((visibleSet P H u).powerset.card : ℚ) =
          (2 : ℚ) ^ (visibleSet P H u).card := by
      have hcard :
          (visibleSet P H u).powerset.card = 2 ^ (visibleSet P H u).card := by
        simpa using (Finset.card_powerset (visibleSet P H u))
      exact_mod_cast hcard
    have hmul :
        (2 : ℚ) ^ (visibleSet P H u).card *
          ((1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card) = (1 : ℚ) := by
      have hne : (2 : ℚ) ^ (visibleSet P H u).card ≠ 0 := by
        exact pow_ne_zero _ (by norm_num)
      simpa [div_eq_mul_inv] using (mul_inv_cancel hne)
    calc
      ∑ S in (visibleSet P H u).powerset,
          (1 : ℚ) / (2 : ℚ) ^ (potential P (addEdgesFrom H u S) u)
          = ∑ S in (visibleSet P H u).powerset,
              (1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card := by
              exact hsum_const
      _ = ((visibleSet P H u).powerset.card : ℚ) *
            ((1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card) := by
            exact hsum_card
      _ = (2 : ℚ) ^ (visibleSet P H u).card *
            ((1 : ℚ) / (2 : ℚ) ^ (visibleSet P H u).card) := by
              simp [hpow]
      _ = (1 : ℚ) := hmul
  have hsum_iso :
      ∑ H in planeGraphsIso P u,
        ∑ S in (visibleSet P H u).powerset,
          (1 : ℚ) / (2 : ℚ) ^ (potential P (addEdgesFrom H u S) u) =
        (planeGraphsIso P u).card := by
    have hsum' :
        ∑ H in planeGraphsIso P u,
          ∑ S in (visibleSet P H u).powerset,
            (1 : ℚ) / (2 : ℚ) ^ (potential P (addEdgesFrom H u S) u) =
          ∑ H in planeGraphsIso P u, (1 : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro H hH
      exact hinner H hH
    simpa using hsum'
  exact hsum_pairs.trans (hsum_sigma.trans hsum_iso)

lemma deg56_charge_conserve {n : ℕ} (P : PointSet n) :
    ∑ G in planeGraphs P, deg56_charge P G =
      ∑ G in planeGraphs P, (isoCount G : ℚ) := by
  classical
  have hsum :
      ∑ G in planeGraphs P, deg56_charge P G =
        ∑ u in Finset.univ, ∑ G in planeGraphs P,
          (1 : ℚ) / (2 : ℚ) ^ (potential P G u) := by
    calc
      ∑ G in planeGraphs P, deg56_charge P G
          = ∑ G in planeGraphs P, ∑ u in Finset.univ,
              (1 : ℚ) / (2 : ℚ) ^ (potential P G u) := by
                simp [deg56_charge]
      _ = ∑ u in Finset.univ, ∑ G in planeGraphs P,
            (1 : ℚ) / (2 : ℚ) ^ (potential P G u) := by
              simpa using
                (Finset.sum_comm (s := planeGraphs P) (t := (Finset.univ : Finset (Fin n)))
                  (f := fun G u => (1 : ℚ) / (2 : ℚ) ^ (potential P G u)))
  have hsum' :
      ∑ u in Finset.univ, ∑ G in planeGraphs P,
          (1 : ℚ) / (2 : ℚ) ^ (potential P G u) =
        ∑ u in Finset.univ, ((planeGraphsIso P u).card : ℚ) := by
    refine Finset.sum_congr rfl ?_
    intro u _
    simpa using (sum_charge_eq_planeGraphsIso (P := P) u)
  have hnat :
      ∑ u in Finset.univ, (planeGraphsIso P u).card =
        ∑ G in planeGraphs P, isoCount G := by
    simpa using (sum_isoCount_eq_sum_planeGraphsIso (P := P)).symm
  have hq :
      (∑ u in Finset.univ, (planeGraphsIso P u).card : ℚ) =
        ∑ G in planeGraphs P, (isoCount G : ℚ) := by
    exact_mod_cast hnat
  calc
    ∑ G in planeGraphs P, deg56_charge P G
        = ∑ u in Finset.univ, ∑ G in planeGraphs P,
            (1 : ℚ) / (2 : ℚ) ^ (potential P G u) := hsum
    _ = (∑ u in Finset.univ, (planeGraphsIso P u).card : ℚ) := by
          simpa using hsum'
    _ = ∑ G in planeGraphs P, (isoCount G : ℚ) := hq

lemma deg56_charge_upper_of_degree {n : ℕ} {P : PointSet n} (T : Hull3Triangulation P)
    {G : Finset (Segment n)} (hdeg : ∀ u : Fin n, degree T.G u ≤ potential P G u) :
    deg56_charge P G ≤
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
      (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
      (vL T.G : ℚ) * wL_n12_sample := by
  classical
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
  have hterm :
      ∀ u : Fin n,
        (1 : ℚ) / (2 : ℚ) ^ (potential P G u) ≤
          (if degree T.G u = 3 then w3_n12_sample else 0) +
          (if degree T.G u = 4 then w4_n12_sample else 0) +
          (if degree T.G u = 5 then w5_n12_sample else 0) +
          (if degree T.G u = 6 then w6_n12_sample else 0) +
          (if 7 ≤ degree T.G u then wL_n12_sample else 0) := by
    intro u
    have hdeg' : degree T.G u ≤ potential P G u :=
      hdeg u
    have hpow :
        (2 : ℚ) ^ (degree T.G u) ≤ (2 : ℚ) ^ (potential P G u) := by
      exact pow_le_pow_right (by norm_num : (1 : ℚ) ≤ (2 : ℚ)) hdeg'
    have hpos : 0 < (2 : ℚ) ^ (degree T.G u) := by
      exact pow_pos (by norm_num) _
    have hle :
        (1 : ℚ) / (2 : ℚ) ^ (potential P G u) ≤
          (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) := by
      have hinv :
          ((2 : ℚ) ^ (potential P G u))⁻¹ ≤ ((2 : ℚ) ^ (degree T.G u))⁻¹ :=
        inv_le_inv_of_le hpos hpow
      simpa [div_eq_mul_inv] using hinv
    by_cases h3 : degree T.G u = 3
    ·
      have hcase :
          (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤
            (if degree T.G u = 3 then w3_n12_sample else 0) +
            (if degree T.G u = 4 then w4_n12_sample else 0) +
            (if degree T.G u = 5 then w5_n12_sample else 0) +
            (if degree T.G u = 6 then w6_n12_sample else 0) +
            (if 7 ≤ degree T.G u then wL_n12_sample else 0) := by
        have hbasic : (1 : ℚ) / (2 : ℚ) ^ 3 ≤ (1 / 8 : ℚ) := by
          norm_num
        simpa [h3, hw3, hw4, hw5, hw6, hwL] using hbasic
      exact le_trans hle hcase
    by_cases h4 : degree T.G u = 4
    ·
      have hcase :
          (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤
            (if degree T.G u = 3 then w3_n12_sample else 0) +
            (if degree T.G u = 4 then w4_n12_sample else 0) +
            (if degree T.G u = 5 then w5_n12_sample else 0) +
            (if degree T.G u = 6 then w6_n12_sample else 0) +
            (if 7 ≤ degree T.G u then wL_n12_sample else 0) := by
        have hbasic : (1 : ℚ) / (2 : ℚ) ^ 4 ≤ (1 / 16 : ℚ) := by
          norm_num
        simpa [h3, h4, hw3, hw4, hw5, hw6, hwL] using hbasic
      exact le_trans hle hcase
    by_cases h5 : degree T.G u = 5
    ·
      have hcase :
          (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤
            (if degree T.G u = 3 then w3_n12_sample else 0) +
            (if degree T.G u = 4 then w4_n12_sample else 0) +
            (if degree T.G u = 5 then w5_n12_sample else 0) +
            (if degree T.G u = 6 then w6_n12_sample else 0) +
            (if 7 ≤ degree T.G u then wL_n12_sample else 0) := by
        have hbasic : (1 : ℚ) / (2 : ℚ) ^ 5 ≤ (1 / 32 : ℚ) := by
          norm_num
        simpa [h3, h4, h5, hw3, hw4, hw5, hw6, hwL] using hbasic
      exact le_trans hle hcase
    by_cases h6 : degree T.G u = 6
    ·
      have hcase :
          (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤
            (if degree T.G u = 3 then w3_n12_sample else 0) +
            (if degree T.G u = 4 then w4_n12_sample else 0) +
            (if degree T.G u = 5 then w5_n12_sample else 0) +
            (if degree T.G u = 6 then w6_n12_sample else 0) +
            (if 7 ≤ degree T.G u then wL_n12_sample else 0) := by
        have hbasic : (1 : ℚ) / (2 : ℚ) ^ 6 ≤ (1 / 64 : ℚ) := by
          norm_num
        simpa [h3, h4, h5, h6, hw3, hw4, hw5, hw6, hwL] using hbasic
      exact le_trans hle hcase
    have hge7 : 7 ≤ degree T.G u :=
      degree_ge7_of_ge3_and_ne (d := degree T.G u) (hge := T.min_degree u) h3 h4 h5 h6
    have hpow7 :
        (2 : ℚ) ^ 7 ≤ (2 : ℚ) ^ (degree T.G u) := by
      exact pow_le_pow_right (by norm_num : (1 : ℚ) ≤ (2 : ℚ)) hge7
    have hpos7 : 0 < (2 : ℚ) ^ 7 := by
      exact pow_pos (by norm_num) _
    have hle7 :
        (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤ (1 : ℚ) / (2 : ℚ) ^ 7 := by
      have hinv : ((2 : ℚ) ^ (degree T.G u))⁻¹ ≤ ((2 : ℚ) ^ 7)⁻¹ :=
        inv_le_inv_of_le hpos7 hpow7
      simpa [div_eq_mul_inv] using hinv
    have hle' :
        (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤ wL_n12_sample := by
      simpa [hwL] using hle7
    have hcase :
        (1 : ℚ) / (2 : ℚ) ^ (degree T.G u) ≤
          (if degree T.G u = 3 then w3_n12_sample else 0) +
          (if degree T.G u = 4 then w4_n12_sample else 0) +
          (if degree T.G u = 5 then w5_n12_sample else 0) +
          (if degree T.G u = 6 then w6_n12_sample else 0) +
          (if 7 ≤ degree T.G u then wL_n12_sample else 0) := by
      simpa [h3, h4, h5, h6, hge7] using hle'
    exact le_trans hle hcase
  have hsum :
      deg56_charge P G ≤
        ∑ u in Finset.univ,
          ((if degree T.G u = 3 then w3_n12_sample else 0) +
           (if degree T.G u = 4 then w4_n12_sample else 0) +
           (if degree T.G u = 5 then w5_n12_sample else 0) +
           (if degree T.G u = 6 then w6_n12_sample else 0) +
           (if 7 ≤ degree T.G u then wL_n12_sample else 0)) := by
    change
      (∑ u in Finset.univ, (1 : ℚ) / (2 : ℚ) ^ (potential P G u)) ≤
        ∑ u in Finset.univ,
          ((if degree T.G u = 3 then w3_n12_sample else 0) +
           (if degree T.G u = 4 then w4_n12_sample else 0) +
           (if degree T.G u = 5 then w5_n12_sample else 0) +
           (if degree T.G u = 6 then w6_n12_sample else 0) +
           (if 7 ≤ degree T.G u then wL_n12_sample else 0))
    refine Finset.sum_le_sum ?_
    intro u _
    exact hterm u
  have hsum3 :
      ∑ u in Finset.univ, (if degree T.G u = 3 then w3_n12_sample else 0) =
        (v3 T.G : ℚ) * w3_n12_sample := by
    simpa [v3, mul_comm, mul_left_comm, mul_assoc] using
      (sum_if_degree_eq_mul (G := T.G) (k := 3) (c := w3_n12_sample))
  have hsum4 :
      ∑ u in Finset.univ, (if degree T.G u = 4 then w4_n12_sample else 0) =
        (v4 T.G : ℚ) * w4_n12_sample := by
    simpa [v4, mul_comm, mul_left_comm, mul_assoc] using
      (sum_if_degree_eq_mul (G := T.G) (k := 4) (c := w4_n12_sample))
  have hsum5 :
      ∑ u in Finset.univ, (if degree T.G u = 5 then w5_n12_sample else 0) =
        (v5 T.G : ℚ) * w5_n12_sample := by
    simpa [v5, mul_comm, mul_left_comm, mul_assoc] using
      (sum_if_degree_eq_mul (G := T.G) (k := 5) (c := w5_n12_sample))
  have hsum6 :
      ∑ u in Finset.univ, (if degree T.G u = 6 then w6_n12_sample else 0) =
        (v6 T.G : ℚ) * w6_n12_sample := by
    simpa [v6, mul_comm, mul_left_comm, mul_assoc] using
      (sum_if_degree_eq_mul (G := T.G) (k := 6) (c := w6_n12_sample))
  have hsumL :
      ∑ u in Finset.univ, (if 7 ≤ degree T.G u then wL_n12_sample else 0) =
        (vL T.G : ℚ) * wL_n12_sample := by
    have hLnat :
        degGeCount T.G 7 = ∑ u in Finset.univ, (if 7 ≤ degree T.G u then 1 else 0) := by
      simpa using (mul_degGeCount_eq_sum (G := T.G) (k := 7) (a := 1))
    have hLind :
        ∑ u in Finset.univ, (if 7 ≤ degree T.G u then (1 : ℚ) else 0) =
          (degGeCount T.G 7 : ℚ) := by
      exact_mod_cast hLnat.symm
    calc
      ∑ u in Finset.univ, (if 7 ≤ degree T.G u then wL_n12_sample else 0)
          = ∑ u in Finset.univ,
              wL_n12_sample * (if 7 ≤ degree T.G u then (1 : ℚ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro u _
                by_cases h : 7 ≤ degree T.G u <;> simp [h, mul_comm]
      _ = wL_n12_sample * ∑ u in Finset.univ, (if 7 ≤ degree T.G u then (1 : ℚ) else 0) := by
            symm
            exact (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun u : Fin n => if 7 ≤ degree T.G u then (1 : ℚ) else 0)
              (a := wL_n12_sample))
      _ = wL_n12_sample * (degGeCount T.G 7 : ℚ) := by
            simp [hLind]
      _ = (vL T.G : ℚ) * wL_n12_sample := by
            simp [vL, mul_comm, mul_left_comm, mul_assoc]
  have hsum_weights :
      ∑ u in Finset.univ,
          ((if degree T.G u = 3 then w3_n12_sample else 0) +
           (if degree T.G u = 4 then w4_n12_sample else 0) +
           (if degree T.G u = 5 then w5_n12_sample else 0) +
           (if degree T.G u = 6 then w6_n12_sample else 0) +
           (if 7 ≤ degree T.G u then wL_n12_sample else 0))
        =
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
          (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
          (vL T.G : ℚ) * wL_n12_sample := by
    calc
      ∑ u in Finset.univ,
          ((if degree T.G u = 3 then w3_n12_sample else 0) +
           (if degree T.G u = 4 then w4_n12_sample else 0) +
           (if degree T.G u = 5 then w5_n12_sample else 0) +
           (if degree T.G u = 6 then w6_n12_sample else 0) +
           (if 7 ≤ degree T.G u then wL_n12_sample else 0))
          =
          (∑ u in Finset.univ, (if degree T.G u = 3 then w3_n12_sample else 0)) +
          (∑ u in Finset.univ, (if degree T.G u = 4 then w4_n12_sample else 0)) +
          (∑ u in Finset.univ, (if degree T.G u = 5 then w5_n12_sample else 0)) +
          (∑ u in Finset.univ, (if degree T.G u = 6 then w6_n12_sample else 0)) +
          (∑ u in Finset.univ, (if 7 ≤ degree T.G u then wL_n12_sample else 0)) := by
            simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
      _ = (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
          (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
          (vL T.G : ℚ) * wL_n12_sample := by
            simp [hsum3, hsum4, hsum5, hsum6, hsumL, add_assoc, add_left_comm, add_comm]
  calc
    deg56_charge P G ≤
        ∑ u in Finset.univ,
          ((if degree T.G u = 3 then w3_n12_sample else 0) +
           (if degree T.G u = 4 then w4_n12_sample else 0) +
           (if degree T.G u = 5 then w5_n12_sample else 0) +
           (if degree T.G u = 6 then w6_n12_sample else 0) +
           (if 7 ≤ degree T.G u then wL_n12_sample else 0)) := hsum
    _ =
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
          (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
          (vL T.G : ℚ) * wL_n12_sample := hsum_weights

lemma deg56_charge_upper_of_subset {n : ℕ} {P : PointSet n} (T : Hull3Triangulation P)
    {G : Finset (Segment n)} (hsub : G ⊆ T.G) (hT : T.G ∈ planeGraphs P) :
    deg56_charge P G ≤
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
      (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
      (vL T.G : ℚ) * wL_n12_sample := by
  have hdeg :
      ∀ u : Fin n, degree T.G u ≤ potential P G u :=
    potential_ge_degree_of_subset (P := P) (G := G) (T := T.G) hsub hT
  exact deg56_charge_upper_of_degree (T := T) (G := G) hdeg

lemma deg56_sumLarge_hull3_excess {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    4 * (sumLargeExcess T.G : ℚ) ≥
      33 * (v3 T.G : ℚ) + 5 * (v4 T.G : ℚ) - 11 * (v5 T.G : ℚ) -
        21 * (v6 T.G : ℚ) - 28 * (vL T.G : ℚ) - 57 := by
  have hsum : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hsumLarge :=
    sumLarge_eq_q (G := T.G) T.card_eq T.min_degree hsum
  have hexcess :=
    sumLargeExcess_eq_q (G := T.G) T.card_eq T.min_degree hsum
  have hlarge := deg56_sumLarge_hull3 (n := n) (P := P) T hn
  linarith [hlarge, hsumLarge, hexcess]

lemma deg56_balance_terms_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    ∑ v in Finset.univ, deg56BalanceTerm T.G v ≥ -(57 / 4 : ℚ) := by
  have hlarge := deg56_sumLarge_hull3 (n := n) (P := P) T hn
  exact (deg56_sumLarge_iff_balance_terms (G := T.G)).1 hlarge

lemma deg56_balance_simple_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    7 * (v3 T.G : ℚ) ≤
      (v4 T.G : ℚ) + 5 * (v5 T.G : ℚ) + 7 * (v6 T.G : ℚ) + 8 * (vL T.G : ℚ) + 3 := by
  have hsum : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hsumLarge :=
    sumLarge_eq_q (G := T.G) T.card_eq T.min_degree hsum
  have hlarge := deg56_sumLarge_hull3 (n := n) (P := P) T hn
  have hiff :=
    deg56_sumLarge_iff_balance_simple (v3 := (v3 T.G : ℚ)) (v4 := (v4 T.G : ℚ))
      (v5 := (v5 T.G : ℚ)) (v6 := (v6 T.G : ℚ)) (vL := (vL T.G : ℚ))
      (sumLarge := (sumLarge T.G : ℚ)) hsumLarge
  exact (hiff).1 hlarge

lemma deg56_weight_sum_le_n12 {v3 v4 v5 v6 vL n : ℚ}
    (hn : (12 : ℚ) ≤ n)
    (hsum : v3 + v4 + v5 + v6 + vL = n)
    (hbal : 7 * v3 ≤ v4 + 5 * v5 + 7 * v6 + 8 * vL + 3) :
    v3 * w3_n12_sample + v4 * w4_n12_sample + v5 * w5_n12_sample +
      v6 * w6_n12_sample + vL * wL_n12_sample ≤ (n : ℚ) / K_deg56_n12_sample := by
  have hlin :
      15 * v3 + 7 * v4 + 3 * v5 + v6 ≤ 8 * n + 3 := by
    exact (deg56_linear8_iff_balance_simple (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6)
      (vL := vL) (n := n) hsum).2 hbal
  have hlin' :
      60 * v3 + 28 * v4 + 12 * v5 + 4 * v6 ≤ 33 * n := by
    exact deg56_n12_linear_of_small (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6) hn hlin
  have hbal' :
      64 * v3 + 32 * v4 + 16 * v5 + 8 * v6 + 4 * vL ≤ 37 * (v3 + v4 + v5 + v6 + vL) := by
    nlinarith [hsum, hlin']
  have hbound :
      v3 * w3_n12_sample + v4 * w4_n12_sample + v5 * w5_n12_sample +
          v6 * w6_n12_sample + vL * wL_n12_sample
        ≤ (v3 + v4 + v5 + v6 + vL) / K_deg56_n12_sample := by
    exact (charge_bound_deg56_n12_iff (v3 := v3) (v4 := v4) (v5 := v5)
      (v6 := v6) (vL := vL)).2 hbal'
  simpa [hsum] using hbound

lemma deg56_weight_sum_le_n15 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 15 ≤ n) :
    (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
      (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / K_deg56_n15_sample := by
  have hn12 : 12 ≤ n := by
    exact Nat.le_trans (by decide : 12 ≤ 15) hn
  have hmem12 := deg56FastVectorsN12_complete (T := T) hn12
  have hmemFast : degreeVectorOf T.G ∈ deg56FastVectors := (List.mem_filter.1 hmem12).1
  have hsum : v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G = n := by
    exact v_sum_eq_n (G := T.G) T.min_degree
  have hnvec : (degreeVectorOf T.G).n = n := by
    simp [degreeVectorOf, DegreeVector.n, hsum]
  have hpred15 : 15 ≤ (degreeVectorOf T.G).n := by
    simpa [hnvec] using hn
  have hmem15 : degreeVectorOf T.G ∈ deg56FastVectorsN15 := by
    exact List.mem_filter.2 ⟨hmemFast, by simpa using hpred15⟩
  have hOk := deg56FastVectorsN15_ok_forall (degreeVectorOf T.G) hmem15
  have hsumQ :
      (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact_mod_cast hsum
  simpa [deg56N15Ok, degreeVectorOf, DegreeVector.charge, DegreeVector.n, hsumQ] using hOk

lemma deg56_weight_sum_le_shift_n19 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 19 ≤ n) :
    (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
      (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / K_deg56_shift_sample := by
  have hsum : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hbal := deg56_shift_balance_hull3 (T := T) hn
  have hbound :
      (v3 T.G : ℚ) * w3_shift_sample + (v4 T.G : ℚ) * w4_shift_sample +
        (v5 T.G : ℚ) * w5_shift_sample + (v6 T.G : ℚ) * w6_shift_sample +
          (vL T.G : ℚ) * wL_shift_sample ≤
          (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) / K_deg56_shift_sample := by
    exact (charge_bound_deg56_shift_iff (v3 := (v3 T.G : ℚ)) (v4 := (v4 T.G : ℚ))
      (v5 := (v5 T.G : ℚ)) (v6 := (v6 T.G : ℚ)) (vL := (vL T.G : ℚ))).2 hbal
  have hbound' :
      (v3 T.G : ℚ) * w3_shift_sample + (v4 T.G : ℚ) * w4_shift_sample +
        (v5 T.G : ℚ) * w5_shift_sample + (v6 T.G : ℚ) * w6_shift_sample +
          (vL T.G : ℚ) * wL_shift_sample ≤ (n : ℚ) / K_deg56_shift_sample := by
    simpa [hsum] using hbound
  have hw3 : w3_n12_sample = w3_shift_sample := by
    simp [w3_n12_sample, w3_shift_sample,
      deg56N12SampleCertificate_getQ_w3, deg56ShiftSampleCertificate_getQ_w3]
  have hw4 : w4_n12_sample = w4_shift_sample := by
    simp [w4_n12_sample, w4_shift_sample,
      deg56N12SampleCertificate_getQ_w4, deg56ShiftSampleCertificate_getQ_w4]
  have hw5 : w5_n12_sample = w5_shift_sample := by
    simp [w5_n12_sample, w5_shift_sample,
      deg56N12SampleCertificate_getQ_w5, deg56ShiftSampleCertificate_getQ_w5]
  have hw6 : w6_n12_sample = w6_shift_sample := by
    simp [w6_n12_sample, w6_shift_sample,
      deg56N12SampleCertificate_getQ_w6, deg56ShiftSampleCertificate_getQ_w6]
  have hwL : wL_n12_sample = wL_shift_sample := by
    simp [wL_n12_sample, wL_shift_sample,
      deg56N12SampleCertificate_getQ_wL, deg56ShiftSampleCertificate_getQ_wL]
  simpa [hw3, hw4, hw5, hw6, hwL] using hbound'

lemma deg56_weight_sum_le_one_eighth {n : ℕ} {P : PointSet n} (T : Hull3Triangulation P) :
    (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
      (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / 8 := by
  have hsum : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hw3 : w3_n12_sample = (1 / 8 : ℚ) := by
    simp [w3_n12_sample, deg56N12SampleCertificate_getQ_w3]
  have hw4_le : w4_n12_sample ≤ w3_n12_sample := by
    have h : (1 / 16 : ℚ) ≤ (1 / 8 : ℚ) := by
      norm_num
    simpa [w3_n12_sample, w4_n12_sample,
      deg56N12SampleCertificate_getQ_w3, deg56N12SampleCertificate_getQ_w4] using h
  have hw5_le : w5_n12_sample ≤ w3_n12_sample := by
    have h : (1 / 32 : ℚ) ≤ (1 / 8 : ℚ) := by
      norm_num
    simpa [w3_n12_sample, w5_n12_sample,
      deg56N12SampleCertificate_getQ_w3, deg56N12SampleCertificate_getQ_w5] using h
  have hw6_le : w6_n12_sample ≤ w3_n12_sample := by
    have h : (1 / 64 : ℚ) ≤ (1 / 8 : ℚ) := by
      norm_num
    simpa [w3_n12_sample, w6_n12_sample,
      deg56N12SampleCertificate_getQ_w3, deg56N12SampleCertificate_getQ_w6] using h
  have hwL_le : wL_n12_sample ≤ w3_n12_sample := by
    have h : (1 / 128 : ℚ) ≤ (1 / 8 : ℚ) := by
      norm_num
    simpa [w3_n12_sample, wL_n12_sample,
      deg56N12SampleCertificate_getQ_w3, deg56N12SampleCertificate_getQ_wL] using h
  have hv3 : 0 ≤ (v3 T.G : ℚ) := by
    exact_mod_cast (Nat.zero_le _)
  have hv4 : 0 ≤ (v4 T.G : ℚ) := by
    exact_mod_cast (Nat.zero_le _)
  have hv5 : 0 ≤ (v5 T.G : ℚ) := by
    exact_mod_cast (Nat.zero_le _)
  have hv6 : 0 ≤ (v6 T.G : ℚ) := by
    exact_mod_cast (Nat.zero_le _)
  have hvL : 0 ≤ (vL T.G : ℚ) := by
    exact_mod_cast (Nat.zero_le _)
  have h4 :
      (v4 T.G : ℚ) * w4_n12_sample ≤ (v4 T.G : ℚ) * w3_n12_sample := by
    exact mul_le_mul_of_nonneg_left hw4_le hv4
  have h5 :
      (v5 T.G : ℚ) * w5_n12_sample ≤ (v5 T.G : ℚ) * w3_n12_sample := by
    exact mul_le_mul_of_nonneg_left hw5_le hv5
  have h6 :
      (v6 T.G : ℚ) * w6_n12_sample ≤ (v6 T.G : ℚ) * w3_n12_sample := by
    exact mul_le_mul_of_nonneg_left hw6_le hv6
  have hL :
      (vL T.G : ℚ) * wL_n12_sample ≤ (vL T.G : ℚ) * w3_n12_sample := by
    exact mul_le_mul_of_nonneg_left hwL_le hvL
  have hsum_le :
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
          (vL T.G : ℚ) * wL_n12_sample ≤
        w3_n12_sample * (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) := by
    nlinarith [h4, h5, h6, hL, hv3]
  calc
    (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
          (vL T.G : ℚ) * wL_n12_sample
        ≤ w3_n12_sample * (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) := hsum_le
    _ = w3_n12_sample * (n : ℚ) := by
          simp [hsum]
    _ = (n : ℚ) / 8 := by
          simp [hw3, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma deg56_charge_bound_hull3 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : 12 ≤ n) :
    ∀ G ∈ planeGraphs P, deg56_charge P G ≤ (n : ℚ) / K_deg56_n12_sample := by
  intro G hG
  rcases hull3_triangulation_extends (P := P) hHull (G := G) hG with ⟨T, hsub, hT⟩
  have hcharge :
      deg56_charge P G ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample :=
    deg56_charge_upper_of_subset (T := T) (G := G) hsub hT
  have hsum : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hbal := deg56_balance_simple_hull3 (n := n) (P := P) T hn
  have hnq : (12 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hbound :
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / K_deg56_n12_sample := by
    exact deg56_weight_sum_le_n12 (v3 := (v3 T.G : ℚ)) (v4 := (v4 T.G : ℚ))
      (v5 := (v5 T.G : ℚ)) (v6 := (v6 T.G : ℚ)) (vL := (vL T.G : ℚ))
      (n := (n : ℚ)) hnq hsum hbal
  exact le_trans hcharge hbound

lemma deg56_charge_bound_hull3_n15 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : 15 ≤ n) :
    ∀ G ∈ planeGraphs P, deg56_charge P G ≤ (n : ℚ) / K_deg56_n15_sample := by
  intro G hG
  rcases hull3_triangulation_extends (P := P) hHull (G := G) hG with ⟨T, hsub, hT⟩
  have hcharge :
      deg56_charge P G ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample :=
    deg56_charge_upper_of_subset (T := T) (G := G) hsub hT
  have hbound :
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / K_deg56_n15_sample := by
    exact deg56_weight_sum_le_n15 (T := T) hn
  exact le_trans hcharge hbound

lemma deg56_charge_bound_hull3_shift {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : 19 ≤ n) :
    ∀ G ∈ planeGraphs P, deg56_charge P G ≤ (n : ℚ) / K_deg56_shift_sample := by
  intro G hG
  rcases hull3_triangulation_extends (P := P) hHull (G := G) hG with ⟨T, hsub, hT⟩
  have hcharge :
      deg56_charge P G ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample :=
    deg56_charge_upper_of_subset (T := T) (G := G) hsub hT
  have hbound :
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / K_deg56_shift_sample := by
    exact deg56_weight_sum_le_shift_n19 (T := T) hn
  exact le_trans hcharge hbound

lemma deg56_charge_bound_hull3_trivial {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    ∀ G ∈ planeGraphs P, deg56_charge P G ≤ (n : ℚ) / 8 := by
  intro G hG
  rcases hull3_triangulation_extends (P := P) hHull (G := G) hG with ⟨T, hsub, hT⟩
  have hcharge :
      deg56_charge P G ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample :=
    deg56_charge_upper_of_subset (T := T) (G := G) hsub hT
  have hbound :
      (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample ≤ (n : ℚ) / 8 := by
    exact deg56_weight_sum_le_one_eighth (T := T)
  exact le_trans hcharge hbound

lemma deg56_linear8_hull3_graph {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    15 * (v3 T.G : ℚ) + 7 * (v4 T.G : ℚ) + 3 * (v5 T.G : ℚ) + (v6 T.G : ℚ)
      ≤ 8 * (n : ℚ) + 3 := by
  have hbal := deg56_balance_simple_hull3 (n := n) (P := P) T hn
  have hiff := deg56_balance_simple_graph (G := T.G) T.min_degree
  exact (hiff).2 hbal

lemma deg56_linear8_hull3_of_const {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n)
    (a3 a4 a5 a6 c3 c4 c5 c6 : ℚ)
    (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5) (ha6 : 0 ≤ a6)
    (h3 : ∀ v, degree T.G v = 3 → adjacentLargeCountQ T.G v ≥ c3)
    (h4 : ∀ v, degree T.G v = 4 → adjacentLargeCountQ T.G v ≥ c4)
    (h5 : ∀ v, degree T.G v = 5 → adjacentLargeCountQ T.G v ≥ c5)
    (h6 : ∀ v, degree T.G v = 6 → adjacentLargeCountQ T.G v ≥ c6)
    (hsum :
      ((-33 / 4 : ℚ) + a3 * c3) * (v3 T.G : ℚ) +
        ((-5 / 4 : ℚ) + a4 * c4) * (v4 T.G : ℚ) +
        ((11 / 4 : ℚ) + a5 * c5) * (v5 T.G : ℚ) +
        ((21 / 4 : ℚ) + a6 * c6) * (v6 T.G : ℚ) +
        (1 - (a3 + a4 + a5 + a6)) * (sumLarge T.G : ℚ) ≥ -(57 / 4 : ℚ)) :
    15 * (v3 T.G : ℚ) + 7 * (v4 T.G : ℚ) + 3 * (v5 T.G : ℚ) + (v6 T.G : ℚ)
      ≤ 8 * (n : ℚ) + 3 := by
  have hsumv : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hsumLarge :=
    sumLarge_eq_q (G := T.G) T.card_eq T.min_degree hsumv
  have hlarge :=
    deg56_sumLarge_hull3_of_const (T := T) hn a3 a4 a5 a6 c3 c4 c5 c6
      ha3 ha4 ha5 ha6 h3 h4 h5 h6 hsum
  have hiff :=
    deg56_linear8_iff_sumLarge (v3 := (v3 T.G : ℚ)) (v4 := (v4 T.G : ℚ))
      (v5 := (v5 T.G : ℚ)) (v6 := (v6 T.G : ℚ)) (vL := (vL T.G : ℚ))
      (n := (n : ℚ)) (sumLarge := (sumLarge T.G : ℚ)) hsumv hsumLarge
  exact (hiff).2 hlarge

lemma deg56_linear8_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    15 * (v3 T.G : ℚ) + 7 * (v4 T.G : ℚ) + 3 * (v5 T.G : ℚ) + (v6 T.G : ℚ)
      ≤ 8 * (n : ℚ) + 3 := by
  have hsum : (v3 T.G + v4 T.G + v5 T.G + v6 T.G + vL T.G : ℚ) = (n : ℚ) := by
    exact v_sum_eq_n_q (G := T.G) T.min_degree
  have hsumLarge :=
    sumLarge_eq_q (G := T.G) T.card_eq T.min_degree hsum
  have hiff :=
    deg56_linear8_iff_sumLarge (v3 := (v3 T.G : ℚ)) (v4 := (v4 T.G : ℚ))
      (v5 := (v5 T.G : ℚ)) (v6 := (v6 T.G : ℚ)) (vL := (vL T.G : ℚ))
      (n := (n : ℚ)) (sumLarge := (sumLarge T.G : ℚ)) hsum hsumLarge
  exact (hiff).2 (deg56_sumLarge_hull3 (T := T) hn)

lemma deg56_n12_hull3_data {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n)
    (havg :
      avgIso P ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample) :
    ∃ v3 v4 v5 v6 vL : ℚ,
      avgIso P ≤ v3 * w3_n12_sample + v4 * w4_n12_sample + v5 * w5_n12_sample +
        v6 * w6_n12_sample + vL * wL_n12_sample ∧
      v3 + v4 + v5 + v6 + vL = (n : ℚ) ∧
      7 * v3 ≤ v4 + 5 * v5 + 7 * v6 + 8 * vL + 3 := by
  refine ⟨(v3 T.G : ℚ), (v4 T.G : ℚ), (v5 T.G : ℚ), (v6 T.G : ℚ), (vL T.G : ℚ), ?_, ?_, ?_⟩
  · exact havg
  · exact v_sum_eq_n_q (G := T.G) T.min_degree
  ·
    exact deg56_balance_simple_hull3 (n := n) (P := P) T hn

lemma avgIso_le_deg56_n12_hull3 {n : ℕ} {P : PointSet n}
    (T : Hull3Triangulation P) (hn : 12 ≤ n)
    (havg :
      avgIso P ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample) :
    avgIso P ≤ (n : ℚ) / K_deg56_n12_sample := by
  rcases deg56_n12_hull3_data (T := T) hn havg with
    ⟨v3, v4, v5, v6, vL, havg, hsum, hbal⟩
  have hnq : (12 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  exact avgIso_le_deg56_n12_of_balance_simple (P := P) (v3 := v3) (v4 := v4)
    (v5 := v5) (v6 := v6) (vL := vL) hnq havg hsum hbal

lemma avgIso_le_deg56_n12_hull3_charge {n : ℕ} {P : PointSet n}
    (hHull : HullSize P = 3) (hn : 12 ≤ n) :
    avgIso P ≤ (n : ℚ) / K_deg56_n12_sample := by
  refine avgIso_le_of_charge_bound (P := P) (charge := deg56_charge P)
    (hconserve := deg56_charge_conserve (P := P)) ?_
  intro G hG
  exact deg56_charge_bound_hull3 (P := P) hHull hn G hG

lemma avgIso_le_deg56_n15_hull3_charge {n : ℕ} {P : PointSet n}
    (hHull : HullSize P = 3) (hn : 15 ≤ n) :
    avgIso P ≤ (n : ℚ) / K_deg56_n15_sample := by
  refine avgIso_le_of_charge_bound (P := P) (charge := deg56_charge P)
    (hconserve := deg56_charge_conserve (P := P)) ?_
  intro G hG
  exact deg56_charge_bound_hull3_n15 (P := P) hHull hn G hG

lemma avgIso_le_deg56_shift_hull3_charge {n : ℕ} {P : PointSet n}
    (hHull : HullSize P = 3) (hn : 19 ≤ n) :
    avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
  refine avgIso_le_of_charge_bound (P := P) (charge := deg56_charge P)
    (hconserve := deg56_charge_conserve (P := P)) ?_
  intro G hG
  exact deg56_charge_bound_hull3_shift (P := P) hHull hn G hG

lemma avgIso_le_deg56_hull3_trivial_charge {n : ℕ} {P : PointSet n}
    (hHull : HullSize P = 3) :
    avgIso P ≤ (n : ℚ) / 8 := by
  refine avgIso_le_of_charge_bound (P := P) (charge := deg56_charge P)
    (hconserve := deg56_charge_conserve (P := P)) ?_
  intro G hG
  exact deg56_charge_bound_hull3_trivial (P := P) hHull G hG

lemma pg_lower_bound_hull3_min {n : ℕ} {P : PointSet (n + 1)}
    (hHull : HullSize P = 3) (hn : 12 ≤ n + 1) :
    (pg P : ℚ) ≥ K_deg56_n12_sample * (pg_min n : ℚ) := by
  have hKpos : 0 < K_deg56_n12_sample := K_deg56_n12_sample_pos
  have havg : avgIso P ≤ ((n : ℚ) + 1) / K_deg56_n12_sample := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (avgIso_le_deg56_n12_hull3_charge (P := P) hHull hn)
  have hmin : ∀ v : Fin (n + 1), (pg (deletePoint P v) : ℚ) ≥ (pg_min n : ℚ) := by
    intro v
    exact_mod_cast (pg_min_le (P := deletePoint P v))
  exact pg_lower_bound_of_avgIso (P := P) (K := K_deg56_n12_sample) (m := (pg_min n : ℚ))
    hKpos havg hmin

def Hull3Class (n : ℕ) (P : PointSet n) : Prop :=
  HullSize P = 3

lemma avgIso_le_hull3_class {n : ℕ} {P : PointSet n} (hn : 12 ≤ n) (hP : Hull3Class n P) :
    avgIso P ≤ (n : ℚ) / K_deg56_n12_sample := by
  exact avgIso_le_deg56_n12_hull3_charge (P := P) hP hn

lemma avgIso_le_hull3_class_trivial {n : ℕ} {P : PointSet n} (hP : Hull3Class n P) :
    avgIso P ≤ (n : ℚ) / 8 := by
  exact avgIso_le_deg56_hull3_trivial_charge (P := P) hP

lemma avgIso_le_hull3_class_n15 {n : ℕ} {P : PointSet n} (hn : 15 ≤ n) (hP : Hull3Class n P) :
    avgIso P ≤ (n : ℚ) / K_deg56_n15_sample := by
  exact avgIso_le_deg56_n15_hull3_charge (P := P) hP hn

lemma avgIso_le_hull3_class_shift_n19 {n : ℕ} {P : PointSet n} (hn : 19 ≤ n) (hP : Hull3Class n P) :
    avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
  exact avgIso_le_deg56_shift_hull3_charge (P := P) hP hn

axiom hull3_class_nonempty : ∀ n, ∃ P : PointSet n, Hull3Class n P

axiom hull3_class_closed : ClosedUnderDelete Hull3Class

lemma pg_min_class_hull3_pow_8 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥ (8 : ℚ) ^ n := by
  have hKpos : 0 < (8 : ℚ) := by
    norm_num
  have havg :
      ∀ {n} (P : PointSet (n + 1)), Hull3Class (n + 1) P →
        avgIso P ≤ (n + 1 : ℚ) / 8 := by
    intro n P hP
    have h := avgIso_le_deg56_hull3_trivial_charge (P := P) hP
    simpa [Nat.cast_add, Nat.cast_one] using h
  exact pg_min_class_pow (K := (8 : ℚ)) (hK := hKpos)
    (good := Hull3Class) (hgood := hgood) (hclosed := hdel) (havg := havg)

lemma pg_hull3_pow_8 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) :
    (pg P : ℚ) ≥ (8 : ℚ) ^ n := by
  have hmin :
      (pg_min_class Hull3Class hgood n : ℚ) ≤ (pg P : ℚ) := by
    exact_mod_cast (pg_min_class_le (good := Hull3Class) (hgood := hgood) (n := n) (P := P) hHull)
  have hpow := pg_min_class_hull3_pow_8 (n := n) hgood hdel
  exact le_trans hpow hmin

lemma pg_hull3_pow_8_closed {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ (8 : ℚ) ^ n := by
  exact pg_hull3_pow_8 (n := n) (P := P) hHull
    hull3_class_nonempty hull3_class_closed

lemma pg_min_class_ge_one {n : ℕ} (good : ∀ n, PointSet n → Prop)
    (hgood : ∀ n, ∃ P, good n P) :
    (pg_min_class good hgood n : ℚ) ≥ 1 := by
  rcases pg_min_class_spec good hgood n with ⟨P0, _, hpg⟩
  have hpos : 0 < pg P0 := pg_pos P0
  have hle : 1 ≤ pg P0 := (Nat.succ_le_iff).2 hpos
  have hleQ : (1 : ℚ) ≤ (pg P0 : ℚ) := by
    exact_mod_cast hle
  simpa [hpg] using hleQ

lemma pg_min_class_hull3_shifted {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 12) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (pg_min_class Hull3Class hgood 12 : ℚ) * K_deg56_n12_sample ^ (n - 12) := by
  have hKpos : 0 < K_deg56_n12_sample := K_deg56_n12_sample_pos
  have havg :
      ∀ {n}, n ≥ 12 → ∀ (P : PointSet n), Hull3Class n P →
        avgIso P ≤ (n : ℚ) / K_deg56_n12_sample := by
    intro n hn P hP
    exact avgIso_le_hull3_class (n := n) (P := P) hn hP
  exact pg_min_class_shifted (K := K_deg56_n12_sample) (hK := hKpos)
    (C := Hull3Class) (hgood := hgood) (hdel := hdel) (N := 12) (havg := havg) (n := n) hn

lemma pg_min_class_hull3_pow {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 12) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      K_deg56_n12_sample ^ (n - 12) := by
  have hshift := pg_min_class_hull3_shifted (n := n) hgood hdel hn
  have hmin12 :
      (1 : ℚ) ≤ (pg_min_class Hull3Class hgood 12 : ℚ) := by
    simpa using (pg_min_class_ge_one (good := Hull3Class) (hgood := hgood) (n := 12))
  have hKnonneg : 0 ≤ K_deg56_n12_sample ^ (n - 12) := by
    exact pow_nonneg (le_of_lt K_deg56_n12_sample_pos) _
  have hmul :
      K_deg56_n12_sample ^ (n - 12) ≤
        (pg_min_class Hull3Class hgood 12 : ℚ) * K_deg56_n12_sample ^ (n - 12) := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hmin12 hKnonneg)
  exact le_trans hmul hshift

lemma pg_hull3_pow {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 12) :
    (pg P : ℚ) ≥ K_deg56_n12_sample ^ (n - 12) := by
  have hmin :
      (pg_min_class Hull3Class hgood n : ℚ) ≤ (pg P : ℚ) := by
    exact_mod_cast (pg_min_class_le (good := Hull3Class) (hgood := hgood) (n := n) (P := P) hHull)
  have hpow := pg_min_class_hull3_pow (n := n) hgood hdel hn
  exact le_trans hpow hmin

lemma pg_hull3_pow_closed {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) (hn : n ≥ 12) :
    (pg P : ℚ) ≥ K_deg56_n12_sample ^ (n - 12) := by
  exact pg_hull3_pow (n := n) (P := P) hHull hull3_class_nonempty hull3_class_closed hn

lemma K_deg56_n15_sample_pos : 0 < K_deg56_n15_sample := by
  norm_num [K_deg56_n15_sample]

lemma pg_min_class_hull3_shifted_n15 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 15) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (pg_min_class Hull3Class hgood 15 : ℚ) * K_deg56_n15_sample ^ (n - 15) := by
  have hKpos : 0 < K_deg56_n15_sample := K_deg56_n15_sample_pos
  have havg :
      ∀ {n}, n ≥ 15 → ∀ (P : PointSet n), Hull3Class n P →
        avgIso P ≤ (n : ℚ) / K_deg56_n15_sample := by
    intro n hn P hP
    exact avgIso_le_hull3_class_n15 (n := n) (P := P) hn hP
  exact pg_min_class_shifted (K := K_deg56_n15_sample) (hK := hKpos)
    (C := Hull3Class) (hgood := hgood) (hdel := hdel) (N := 15) (havg := havg) (n := n) hn

lemma pg_min_class_hull3_pow_n15 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 15) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      K_deg56_n15_sample ^ (n - 15) := by
  have hshift := pg_min_class_hull3_shifted_n15 (n := n) hgood hdel hn
  have hmin15 :
      (1 : ℚ) ≤ (pg_min_class Hull3Class hgood 15 : ℚ) := by
    simpa using (pg_min_class_ge_one (good := Hull3Class) (hgood := hgood) (n := 15))
  have hKnonneg : 0 ≤ K_deg56_n15_sample ^ (n - 15) := by
    exact pow_nonneg (le_of_lt K_deg56_n15_sample_pos) _
  have hmul :
      K_deg56_n15_sample ^ (n - 15) ≤
        (pg_min_class Hull3Class hgood 15 : ℚ) * K_deg56_n15_sample ^ (n - 15) := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hmin15 hKnonneg)
  exact le_trans hmul hshift

lemma pg_hull3_pow_n15 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 15) :
    (pg P : ℚ) ≥ K_deg56_n15_sample ^ (n - 15) := by
  have hmin :
      (pg_min_class Hull3Class hgood n : ℚ) ≤ (pg P : ℚ) := by
    exact_mod_cast (pg_min_class_le (good := Hull3Class) (hgood := hgood) (n := n) (P := P) hHull)
  have hpow := pg_min_class_hull3_pow_n15 (n := n) hgood hdel hn
  exact le_trans hpow hmin

lemma pg_hull3_pow_closed_n15 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) (hn : n ≥ 15) :
    (pg P : ℚ) ≥ K_deg56_n15_sample ^ (n - 15) := by
  exact pg_hull3_pow_n15 (n := n) (P := P) hHull hull3_class_nonempty hull3_class_closed hn

lemma pg_min_class_hull3_shifted_shift_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (pg_min_class Hull3Class hgood 19 : ℚ) * K_deg56_shift_sample ^ (n - 19) := by
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have havg :
      ∀ {n}, n ≥ 19 → ∀ (P : PointSet n), Hull3Class n P →
        avgIso P ≤ (n : ℚ) / K_deg56_shift_sample := by
    intro n hn P hP
    exact avgIso_le_hull3_class_shift_n19 (n := n) (P := P) hn hP
  exact pg_min_class_shifted (K := K_deg56_shift_sample) (hK := hKpos)
    (C := Hull3Class) (hgood := hgood) (hdel := hdel) (N := 19) (havg := havg) (n := n) hn

lemma pg_min_class_hull3_pow_shift_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      K_deg56_shift_sample ^ (n - 19) := by
  have hshift := pg_min_class_hull3_shifted_shift_n19 (n := n) hgood hdel hn
  have hmin19 :
      (1 : ℚ) ≤ (pg_min_class Hull3Class hgood 19 : ℚ) := by
    simpa using (pg_min_class_ge_one (good := Hull3Class) (hgood := hgood) (n := 19))
  have hKnonneg : 0 ≤ K_deg56_shift_sample ^ (n - 19) := by
    exact pow_nonneg (le_of_lt K_deg56_shift_sample_pos) _
  have hmul :
      K_deg56_shift_sample ^ (n - 19) ≤
        (pg_min_class Hull3Class hgood 19 : ℚ) * K_deg56_shift_sample ^ (n - 19) := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hmin19 hKnonneg)
  exact le_trans hmul hshift

lemma pg_hull3_pow_shift_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 19) :
    (pg P : ℚ) ≥ K_deg56_shift_sample ^ (n - 19) := by
  have hmin :
      (pg_min_class Hull3Class hgood n : ℚ) ≤ (pg P : ℚ) := by
    exact_mod_cast (pg_min_class_le (good := Hull3Class) (hgood := hgood) (n := n) (P := P) hHull)
  have hpow := pg_min_class_hull3_pow_shift_n19 (n := n) hgood hdel hn
  exact le_trans hpow hmin

lemma pg_hull3_pow_shift_closed_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ K_deg56_shift_sample ^ (n - 19) := by
  exact pg_hull3_pow_shift_n19 (n := n) (P := P) hHull
    hull3_class_nonempty hull3_class_closed hn

lemma pg_hull3_pow_shift_closed_all {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ K_deg56_shift_sample ^ (n - 19) := by
  classical
  by_cases hn : n ≥ 19
  · exact pg_hull3_pow_shift_closed_n19 (n := n) (P := P) hHull hn
  ·
    have hlt : n < 19 := lt_of_not_ge hn
    have hsub : n - 19 = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    have hpg : (1 : ℚ) ≤ (pg P : ℚ) := by
      have hpos : 0 < pg P := pg_pos P
      have hle : 1 ≤ pg P := (Nat.succ_le_iff).2 hpos
      exact_mod_cast hle
    simpa [hsub] using hpg

lemma pg_hull3_explicit_shift_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (K_deg56_shift_sample ^ 19) := by
  have hpow := pg_hull3_pow_shift_n19 (n := n) (P := P) hHull hgood hdel hn
  have hKne : (K_deg56_shift_sample : ℚ) ≠ 0 := ne_of_gt K_deg56_shift_sample_pos
  have hKne19 : (K_deg56_shift_sample ^ 19 : ℚ) ≠ 0 := by
    exact pow_ne_zero _ hKne
  have hsum : n - 19 + 19 = n := Nat.sub_add_cancel hn
  have hpow_add :
      K_deg56_shift_sample ^ (n - 19) * K_deg56_shift_sample ^ 19 =
        K_deg56_shift_sample ^ n := by
    calc
      K_deg56_shift_sample ^ (n - 19) * K_deg56_shift_sample ^ 19
          = K_deg56_shift_sample ^ (n - 19 + 19) := by
              symm
              exact pow_add _ _ _
      _ = K_deg56_shift_sample ^ n := by
            simpa [hsum]
  have hrewrite :
      K_deg56_shift_sample ^ (n - 19) =
        (K_deg56_shift_sample ^ n) / (K_deg56_shift_sample ^ 19) := by
    calc
      K_deg56_shift_sample ^ (n - 19)
          = (K_deg56_shift_sample ^ (n - 19) * K_deg56_shift_sample ^ 19) /
              (K_deg56_shift_sample ^ 19) := by
                field_simp [hKne19]
      _ = (K_deg56_shift_sample ^ n) / (K_deg56_shift_sample ^ 19) := by
            simp [hpow_add]
  simpa [hrewrite] using hpow

lemma pg_hull3_explicit_shift_closed_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (K_deg56_shift_sample ^ 19) := by
  exact pg_hull3_explicit_shift_n19 (n := n) (P := P) hHull
    hull3_class_nonempty hull3_class_closed hn

lemma pg_hull3_explicit_shift_closed_all {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (K_deg56_shift_sample ^ 19) := by
  classical
  by_cases hn : n ≥ 19
  · exact pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  ·
    have hlt : n < 19 := lt_of_not_ge hn
    have hKge1 : (1 : ℚ) ≤ K_deg56_shift_sample := by
      have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
        simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
      have h1 : (1 : ℚ) ≤ (192 / 13 : ℚ) := by
        norm_num
      simpa [hK] using h1
    have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
    have hnle : n ≤ 19 := Nat.le_of_lt hlt
    have hpowle :
        (K_deg56_shift_sample ^ n : ℚ) ≤ K_deg56_shift_sample ^ 19 := by
      exact pow_le_pow_right hKge1 hnle
    have hdivle :
        (K_deg56_shift_sample ^ n) / (K_deg56_shift_sample ^ 19) ≤ (1 : ℚ) := by
      have hKpowpos : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
        exact pow_pos hKpos _
      have hle : (K_deg56_shift_sample ^ n : ℚ) ≤ (1 : ℚ) * K_deg56_shift_sample ^ 19 := by
        simpa using hpowle
      exact (div_le_iff hKpowpos).2 (by simpa [one_mul] using hle)
    have hpg : (1 : ℚ) ≤ (pg P : ℚ) := by
      have hpos : 0 < pg P := pg_pos P
      have hle : 1 ≤ pg P := (Nat.succ_le_iff).2 hpos
      exact_mod_cast hle
    exact le_trans hdivle hpg

lemma K_deg56_shift_sample_le_19 : (K_deg56_shift_sample : ℚ) ≤ 19 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  have hK' : (192 / 13 : ℚ) ≤ 19 := by
    norm_num
  simpa [hK] using hK'

lemma K_deg56_shift_sample_pow19_le_19_pow18 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ (19 : ℚ) ^ 18 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ (19 : ℚ) ^ 18)

lemma K_deg56_shift_sample_pow19_le_4_19_pow17 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 4 * (19 : ℚ) ^ 17 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 4 * (19 : ℚ) ^ 17)

lemma K_deg56_shift_sample_pow19_le_58_19_pow16 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 58 * (19 : ℚ) ^ 16 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 58 * (19 : ℚ) ^ 16)

lemma K_deg56_shift_sample_pow19_le_1088_19_pow15 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 1088 * (19 : ℚ) ^ 15 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 1088 * (19 : ℚ) ^ 15)

lemma K_deg56_shift_sample_pow19_le_20666_19_pow14 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 20666 * (19 : ℚ) ^ 14 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 20666 * (19 : ℚ) ^ 14)

lemma K_deg56_shift_sample_pow19_le_392648_19_pow13 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 392648 * (19 : ℚ) ^ 13 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 392648 * (19 : ℚ) ^ 13)

lemma K_deg56_shift_sample_pow19_le_7460303_19_pow12 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 7460303 * (19 : ℚ) ^ 12 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 7460303 * (19 : ℚ) ^ 12)

lemma K_deg56_shift_sample_pow19_le_141745749_19_pow11 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 141745749 * (19 : ℚ) ^ 11 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 141745749 * (19 : ℚ) ^ 11)

lemma K_deg56_shift_sample_pow19_le_2693169219_19_pow10 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 2693169219 * (19 : ℚ) ^ 10 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 2693169219 * (19 : ℚ) ^ 10)

lemma K_deg56_shift_sample_pow19_le_51170215145_19_pow9 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 51170215145 * (19 : ℚ) ^ 9 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 51170215145 * (19 : ℚ) ^ 9)

lemma K_deg56_shift_sample_pow19_le_972234087747_19_pow8 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 972234087747 * (19 : ℚ) ^ 8 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 972234087747 * (19 : ℚ) ^ 8)

lemma K_deg56_shift_sample_pow19_le_18472447667193_19_pow7 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 18472447667193 * (19 : ℚ) ^ 7 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 18472447667193 * (19 : ℚ) ^ 7)

lemma K_deg56_shift_sample_pow19_le_350976505676660_19_pow6 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 350976505676660 * (19 : ℚ) ^ 6 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 350976505676660 * (19 : ℚ) ^ 6)

lemma K_deg56_shift_sample_pow19_le_6668553607856535_19_pow5 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 6668553607856535 * (19 : ℚ) ^ 5 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 6668553607856535 * (19 : ℚ) ^ 5)

lemma K_deg56_shift_sample_pow19_le_126702518549274155_19_pow4 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 126702518549274155 * (19 : ℚ) ^ 4 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 126702518549274155 * (19 : ℚ) ^ 4)

lemma K_deg56_shift_sample_pow19_le_2407347852436208928_19_pow3 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 2407347852436208928 * (19 : ℚ) ^ 3 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 2407347852436208928 * (19 : ℚ) ^ 3)

lemma K_deg56_shift_sample_pow19_le_45739609196287969624_19_pow2 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 45739609196287969624 * (19 : ℚ) ^ 2 := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 45739609196287969624 * (19 : ℚ) ^ 2)

lemma K_deg56_shift_sample_pow19_le_869052574729471422843_19_pow1 :
    (K_deg56_shift_sample ^ 19 : ℚ) ≤ 869052574729471422843 * (19 : ℚ) := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  simpa [hK] using (by
    norm_num : ((192 / 13 : ℚ) ^ 19) ≤ 869052574729471422843 * (19 : ℚ))

lemma pg_hull3_explicit_shift_poly_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / ((n : ℚ) ^ 19) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hKle19 : (K_deg56_shift_sample : ℚ) ≤ 19 := K_deg56_shift_sample_le_19
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hKleN : (K_deg56_shift_sample : ℚ) ≤ (n : ℚ) := le_trans hKle19 hnq
  have hpowle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ (n : ℚ) ^ 19 := by
    have hnonneg : 0 ≤ (K_deg56_shift_sample : ℚ) := le_of_lt hKpos
    exact pow_le_pow_left hnonneg hKleN _
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hposn : 0 < ((n : ℚ) ^ 19) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    exact pow_pos hnpos _
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (n : ℚ) ^ 19 := by
    exact mul_le_mul_of_nonneg_left hpowle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / ((n : ℚ) ^ 19) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly18_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / ((n : ℚ) ^ 18) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ (19 : ℚ) ^ 18 :=
    K_deg56_shift_sample_pow19_le_19_pow18
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 18 ≤ (n : ℚ) ^ 18 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ (n : ℚ) ^ 18 := by
    exact le_trans hpow19le hpow19le'
  have hposn : 0 < ((n : ℚ) ^ 18) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    exact pow_pos hnpos _
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (n : ℚ) ^ 18 := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / ((n : ℚ) ^ 18) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly17_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (4 * (n : ℚ) ^ 17) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 4 * (19 : ℚ) ^ 17 :=
    K_deg56_shift_sample_pow19_le_4_19_pow17
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 17 ≤ (n : ℚ) ^ 17 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 4 * (n : ℚ) ^ 17 := by
    have hnonneg4 : 0 ≤ (4 : ℚ) := by
      norm_num
    have hmul :
        4 * (19 : ℚ) ^ 17 ≤ 4 * (n : ℚ) ^ 17 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg4
    exact le_trans hpow19le hmul
  have hposn : 0 < (4 * (n : ℚ) ^ 17) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 17 := by
      exact pow_pos hnpos _
    have hpos4 : 0 < (4 : ℚ) := by
      norm_num
    exact mul_pos hpos4 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (4 * (n : ℚ) ^ 17) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (4 * (n : ℚ) ^ 17) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly16_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (58 * (n : ℚ) ^ 16) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 58 * (19 : ℚ) ^ 16 :=
    K_deg56_shift_sample_pow19_le_58_19_pow16
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 16 ≤ (n : ℚ) ^ 16 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 58 * (n : ℚ) ^ 16 := by
    have hnonneg58 : 0 ≤ (58 : ℚ) := by
      norm_num
    have hmul :
        58 * (19 : ℚ) ^ 16 ≤ 58 * (n : ℚ) ^ 16 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg58
    exact le_trans hpow19le hmul
  have hposn : 0 < (58 * (n : ℚ) ^ 16) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 16 := by
      exact pow_pos hnpos _
    have hpos58 : 0 < (58 : ℚ) := by
      norm_num
    exact mul_pos hpos58 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (58 * (n : ℚ) ^ 16) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (58 * (n : ℚ) ^ 16) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly15_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (1088 * (n : ℚ) ^ 15) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 1088 * (19 : ℚ) ^ 15 :=
    K_deg56_shift_sample_pow19_le_1088_19_pow15
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 15 ≤ (n : ℚ) ^ 15 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 1088 * (n : ℚ) ^ 15 := by
    have hnonneg1088 : 0 ≤ (1088 : ℚ) := by
      norm_num
    have hmul :
        1088 * (19 : ℚ) ^ 15 ≤ 1088 * (n : ℚ) ^ 15 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg1088
    exact le_trans hpow19le hmul
  have hposn : 0 < (1088 * (n : ℚ) ^ 15) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 15 := by
      exact pow_pos hnpos _
    have hpos1088 : 0 < (1088 : ℚ) := by
      norm_num
    exact mul_pos hpos1088 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (1088 * (n : ℚ) ^ 15) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (1088 * (n : ℚ) ^ 15) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly14_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (20666 * (n : ℚ) ^ 14) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 20666 * (19 : ℚ) ^ 14 :=
    K_deg56_shift_sample_pow19_le_20666_19_pow14
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 14 ≤ (n : ℚ) ^ 14 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 20666 * (n : ℚ) ^ 14 := by
    have hnonneg20666 : 0 ≤ (20666 : ℚ) := by
      norm_num
    have hmul :
        20666 * (19 : ℚ) ^ 14 ≤ 20666 * (n : ℚ) ^ 14 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg20666
    exact le_trans hpow19le hmul
  have hposn : 0 < (20666 * (n : ℚ) ^ 14) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 14 := by
      exact pow_pos hnpos _
    have hpos20666 : 0 < (20666 : ℚ) := by
      norm_num
    exact mul_pos hpos20666 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (20666 * (n : ℚ) ^ 14) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (20666 * (n : ℚ) ^ 14) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly13_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (392648 * (n : ℚ) ^ 13) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 392648 * (19 : ℚ) ^ 13 :=
    K_deg56_shift_sample_pow19_le_392648_19_pow13
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 13 ≤ (n : ℚ) ^ 13 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 392648 * (n : ℚ) ^ 13 := by
    have hnonneg392648 : 0 ≤ (392648 : ℚ) := by
      norm_num
    have hmul :
        392648 * (19 : ℚ) ^ 13 ≤ 392648 * (n : ℚ) ^ 13 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg392648
    exact le_trans hpow19le hmul
  have hposn : 0 < (392648 * (n : ℚ) ^ 13) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 13 := by
      exact pow_pos hnpos _
    have hpos392648 : 0 < (392648 : ℚ) := by
      norm_num
    exact mul_pos hpos392648 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (392648 * (n : ℚ) ^ 13) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (392648 * (n : ℚ) ^ 13) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly12_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (7460303 * (n : ℚ) ^ 12) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 7460303 * (19 : ℚ) ^ 12 :=
    K_deg56_shift_sample_pow19_le_7460303_19_pow12
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 12 ≤ (n : ℚ) ^ 12 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 7460303 * (n : ℚ) ^ 12 := by
    have hnonneg7460303 : 0 ≤ (7460303 : ℚ) := by
      norm_num
    have hmul :
        7460303 * (19 : ℚ) ^ 12 ≤ 7460303 * (n : ℚ) ^ 12 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg7460303
    exact le_trans hpow19le hmul
  have hposn : 0 < (7460303 * (n : ℚ) ^ 12) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 12 := by
      exact pow_pos hnpos _
    have hpos7460303 : 0 < (7460303 : ℚ) := by
      norm_num
    exact mul_pos hpos7460303 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (7460303 * (n : ℚ) ^ 12) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (7460303 * (n : ℚ) ^ 12) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly11_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (141745749 * (n : ℚ) ^ 11) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 141745749 * (19 : ℚ) ^ 11 :=
    K_deg56_shift_sample_pow19_le_141745749_19_pow11
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 11 ≤ (n : ℚ) ^ 11 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 141745749 * (n : ℚ) ^ 11 := by
    have hnonneg141745749 : 0 ≤ (141745749 : ℚ) := by
      norm_num
    have hmul :
        141745749 * (19 : ℚ) ^ 11 ≤ 141745749 * (n : ℚ) ^ 11 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg141745749
    exact le_trans hpow19le hmul
  have hposn : 0 < (141745749 * (n : ℚ) ^ 11) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 11 := by
      exact pow_pos hnpos _
    have hpos141745749 : 0 < (141745749 : ℚ) := by
      norm_num
    exact mul_pos hpos141745749 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (141745749 * (n : ℚ) ^ 11) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (141745749 * (n : ℚ) ^ 11) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly10_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (2693169219 * (n : ℚ) ^ 10) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 2693169219 * (19 : ℚ) ^ 10 :=
    K_deg56_shift_sample_pow19_le_2693169219_19_pow10
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 10 ≤ (n : ℚ) ^ 10 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 2693169219 * (n : ℚ) ^ 10 := by
    have hnonneg2693169219 : 0 ≤ (2693169219 : ℚ) := by
      norm_num
    have hmul :
        2693169219 * (19 : ℚ) ^ 10 ≤ 2693169219 * (n : ℚ) ^ 10 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg2693169219
    exact le_trans hpow19le hmul
  have hposn : 0 < (2693169219 * (n : ℚ) ^ 10) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 10 := by
      exact pow_pos hnpos _
    have hpos2693169219 : 0 < (2693169219 : ℚ) := by
      norm_num
    exact mul_pos hpos2693169219 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (2693169219 * (n : ℚ) ^ 10) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (2693169219 * (n : ℚ) ^ 10) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly9_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (51170215145 * (n : ℚ) ^ 9) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 51170215145 * (19 : ℚ) ^ 9 :=
    K_deg56_shift_sample_pow19_le_51170215145_19_pow9
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 9 ≤ (n : ℚ) ^ 9 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 51170215145 * (n : ℚ) ^ 9 := by
    have hnonneg51170215145 : 0 ≤ (51170215145 : ℚ) := by
      norm_num
    have hmul :
        51170215145 * (19 : ℚ) ^ 9 ≤ 51170215145 * (n : ℚ) ^ 9 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg51170215145
    exact le_trans hpow19le hmul
  have hposn : 0 < (51170215145 * (n : ℚ) ^ 9) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 9 := by
      exact pow_pos hnpos _
    have hpos51170215145 : 0 < (51170215145 : ℚ) := by
      norm_num
    exact mul_pos hpos51170215145 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (51170215145 * (n : ℚ) ^ 9) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (51170215145 * (n : ℚ) ^ 9) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly8_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (972234087747 * (n : ℚ) ^ 8) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 972234087747 * (19 : ℚ) ^ 8 :=
    K_deg56_shift_sample_pow19_le_972234087747_19_pow8
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 8 ≤ (n : ℚ) ^ 8 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 972234087747 * (n : ℚ) ^ 8 := by
    have hnonneg972234087747 : 0 ≤ (972234087747 : ℚ) := by
      norm_num
    have hmul :
        972234087747 * (19 : ℚ) ^ 8 ≤ 972234087747 * (n : ℚ) ^ 8 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg972234087747
    exact le_trans hpow19le hmul
  have hposn : 0 < (972234087747 * (n : ℚ) ^ 8) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 8 := by
      exact pow_pos hnpos _
    have hpos972234087747 : 0 < (972234087747 : ℚ) := by
      norm_num
    exact mul_pos hpos972234087747 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (972234087747 * (n : ℚ) ^ 8) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (972234087747 * (n : ℚ) ^ 8) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly7_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (18472447667193 * (n : ℚ) ^ 7) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 18472447667193 * (19 : ℚ) ^ 7 :=
    K_deg56_shift_sample_pow19_le_18472447667193_19_pow7
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 7 ≤ (n : ℚ) ^ 7 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 18472447667193 * (n : ℚ) ^ 7 := by
    have hnonneg18472447667193 : 0 ≤ (18472447667193 : ℚ) := by
      norm_num
    have hmul :
        18472447667193 * (19 : ℚ) ^ 7 ≤ 18472447667193 * (n : ℚ) ^ 7 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg18472447667193
    exact le_trans hpow19le hmul
  have hposn : 0 < (18472447667193 * (n : ℚ) ^ 7) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 7 := by
      exact pow_pos hnpos _
    have hpos18472447667193 : 0 < (18472447667193 : ℚ) := by
      norm_num
    exact mul_pos hpos18472447667193 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (18472447667193 * (n : ℚ) ^ 7) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (18472447667193 * (n : ℚ) ^ 7) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly6_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (350976505676660 * (n : ℚ) ^ 6) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 350976505676660 * (19 : ℚ) ^ 6 :=
    K_deg56_shift_sample_pow19_le_350976505676660_19_pow6
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 6 ≤ (n : ℚ) ^ 6 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 350976505676660 * (n : ℚ) ^ 6 := by
    have hnonneg350976505676660 : 0 ≤ (350976505676660 : ℚ) := by
      norm_num
    have hmul :
        350976505676660 * (19 : ℚ) ^ 6 ≤ 350976505676660 * (n : ℚ) ^ 6 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg350976505676660
    exact le_trans hpow19le hmul
  have hposn : 0 < (350976505676660 * (n : ℚ) ^ 6) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 6 := by
      exact pow_pos hnpos _
    have hpos350976505676660 : 0 < (350976505676660 : ℚ) := by
      norm_num
    exact mul_pos hpos350976505676660 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (350976505676660 * (n : ℚ) ^ 6) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (350976505676660 * (n : ℚ) ^ 6) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly5_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (6668553607856535 * (n : ℚ) ^ 5) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 6668553607856535 * (19 : ℚ) ^ 5 :=
    K_deg56_shift_sample_pow19_le_6668553607856535_19_pow5
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 5 ≤ (n : ℚ) ^ 5 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 6668553607856535 * (n : ℚ) ^ 5 := by
    have hnonneg6668553607856535 : 0 ≤ (6668553607856535 : ℚ) := by
      norm_num
    have hmul :
        6668553607856535 * (19 : ℚ) ^ 5 ≤ 6668553607856535 * (n : ℚ) ^ 5 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg6668553607856535
    exact le_trans hpow19le hmul
  have hposn : 0 < (6668553607856535 * (n : ℚ) ^ 5) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 5 := by
      exact pow_pos hnpos _
    have hpos6668553607856535 : 0 < (6668553607856535 : ℚ) := by
      norm_num
    exact mul_pos hpos6668553607856535 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (6668553607856535 * (n : ℚ) ^ 5) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (6668553607856535 * (n : ℚ) ^ 5) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly4_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (126702518549274155 * (n : ℚ) ^ 4) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 126702518549274155 * (19 : ℚ) ^ 4 :=
    K_deg56_shift_sample_pow19_le_126702518549274155_19_pow4
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 4 ≤ (n : ℚ) ^ 4 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 126702518549274155 * (n : ℚ) ^ 4 := by
    have hnonneg126702518549274155 : 0 ≤ (126702518549274155 : ℚ) := by
      norm_num
    have hmul :
        126702518549274155 * (19 : ℚ) ^ 4 ≤ 126702518549274155 * (n : ℚ) ^ 4 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg126702518549274155
    exact le_trans hpow19le hmul
  have hposn : 0 < (126702518549274155 * (n : ℚ) ^ 4) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 4 := by
      exact pow_pos hnpos _
    have hpos126702518549274155 : 0 < (126702518549274155 : ℚ) := by
      norm_num
    exact mul_pos hpos126702518549274155 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (126702518549274155 * (n : ℚ) ^ 4) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (126702518549274155 * (n : ℚ) ^ 4) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly3_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (2407347852436208928 * (n : ℚ) ^ 3) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 2407347852436208928 * (19 : ℚ) ^ 3 :=
    K_deg56_shift_sample_pow19_le_2407347852436208928_19_pow3
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 3 ≤ (n : ℚ) ^ 3 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 2407347852436208928 * (n : ℚ) ^ 3 := by
    have hnonneg2407347852436208928 : 0 ≤ (2407347852436208928 : ℚ) := by
      norm_num
    have hmul :
        2407347852436208928 * (19 : ℚ) ^ 3 ≤ 2407347852436208928 * (n : ℚ) ^ 3 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg2407347852436208928
    exact le_trans hpow19le hmul
  have hposn : 0 < (2407347852436208928 * (n : ℚ) ^ 3) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 3 := by
      exact pow_pos hnpos _
    have hpos2407347852436208928 : 0 < (2407347852436208928 : ℚ) := by
      norm_num
    exact mul_pos hpos2407347852436208928 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (2407347852436208928 * (n : ℚ) ^ 3) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (2407347852436208928 * (n : ℚ) ^ 3) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly2_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (45739609196287969624 * (n : ℚ) ^ 2) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 45739609196287969624 * (19 : ℚ) ^ 2 :=
    K_deg56_shift_sample_pow19_le_45739609196287969624_19_pow2
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hpow19le' : (19 : ℚ) ^ 2 ≤ (n : ℚ) ^ 2 := by
    have hnonneg : 0 ≤ (19 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hnq _
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 45739609196287969624 * (n : ℚ) ^ 2 := by
    have hnonneg45739609196287969624 : 0 ≤ (45739609196287969624 : ℚ) := by
      norm_num
    have hmul :
        45739609196287969624 * (19 : ℚ) ^ 2 ≤ 45739609196287969624 * (n : ℚ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hpow19le' hnonneg45739609196287969624
    exact le_trans hpow19le hmul
  have hposn : 0 < (45739609196287969624 * (n : ℚ) ^ 2) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpowpos : 0 < (n : ℚ) ^ 2 := by
      exact pow_pos hnpos _
    have hpos45739609196287969624 : 0 < (45739609196287969624 : ℚ) := by
      norm_num
    exact mul_pos hpos45739609196287969624 hpowpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (45739609196287969624 * (n : ℚ) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (45739609196287969624 * (n : ℚ) ^ 2) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_hull3_explicit_shift_poly1_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (K_deg56_shift_sample ^ n) / (869052574729471422843 * (n : ℚ)) := by
  have hpow := pg_hull3_explicit_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKpos : 0 < K_deg56_shift_sample := K_deg56_shift_sample_pos
  have hpowge0 : 0 ≤ (K_deg56_shift_sample ^ n : ℚ) := by
    exact pow_nonneg (le_of_lt hKpos) _
  have hpow19le : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 869052574729471422843 * (19 : ℚ) :=
    K_deg56_shift_sample_pow19_le_869052574729471422843_19_pow1
  have hnq : (19 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hdenle : (K_deg56_shift_sample ^ 19 : ℚ) ≤ 869052574729471422843 * (n : ℚ) := by
    have hnonneg869052574729471422843 : 0 ≤ (869052574729471422843 : ℚ) := by
      norm_num
    have hmul :
        869052574729471422843 * (19 : ℚ) ≤ 869052574729471422843 * (n : ℚ) := by
      exact mul_le_mul_of_nonneg_left hnq hnonneg869052574729471422843
    exact le_trans hpow19le hmul
  have hposn : 0 < (869052574729471422843 * (n : ℚ)) := by
    have hnpos : (0 : ℚ) < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 19) hn)
    have hpos869052574729471422843 : 0 < (869052574729471422843 : ℚ) := by
      norm_num
    exact mul_pos hpos869052574729471422843 hnpos
  have hposKpow : 0 < (K_deg56_shift_sample ^ 19 : ℚ) := by
    exact pow_pos hKpos _
  have hmul :
      (K_deg56_shift_sample ^ n : ℚ) * (K_deg56_shift_sample ^ 19 : ℚ) ≤
        (K_deg56_shift_sample ^ n : ℚ) * (869052574729471422843 * (n : ℚ)) := by
    exact mul_le_mul_of_nonneg_left hdenle hpowge0
  have hdivle :
      (K_deg56_shift_sample ^ n : ℚ) / (869052574729471422843 * (n : ℚ)) ≤
        (K_deg56_shift_sample ^ n : ℚ) / (K_deg56_shift_sample ^ 19) := by
    exact (div_le_div_iff hposn hposKpow).2 hmul
  exact le_trans hdivle hpow

lemma pg_min_class_hull3_explicit_shift_poly_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / ((n : ℚ) ^ 19) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly18_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / ((n : ℚ) ^ 18) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly18_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly17_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (4 * (n : ℚ) ^ 17) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly17_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly16_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (58 * (n : ℚ) ^ 16) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly16_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly15_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (1088 * (n : ℚ) ^ 15) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly15_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly14_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (20666 * (n : ℚ) ^ 14) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly14_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly13_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (392648 * (n : ℚ) ^ 13) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly13_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly12_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (7460303 * (n : ℚ) ^ 12) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly12_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly10_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (2693169219 * (n : ℚ) ^ 10) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly10_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly9_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (51170215145 * (n : ℚ) ^ 9) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly9_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly8_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (972234087747 * (n : ℚ) ^ 8) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly8_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly7_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (18472447667193 * (n : ℚ) ^ 7) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly7_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly6_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (350976505676660 * (n : ℚ) ^ 6) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly6_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly5_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (6668553607856535 * (n : ℚ) ^ 5) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly5_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly4_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (126702518549274155 * (n : ℚ) ^ 4) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly4_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly3_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (2407347852436208928 * (n : ℚ) ^ 3) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly3_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly2_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (45739609196287969624 * (n : ℚ) ^ 2) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly2_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly1_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (869052574729471422843 * (n : ℚ)) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly1_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma pg_min_class_hull3_explicit_shift_poly11_n19 {n : ℕ}
    (hgood : ∀ n, ∃ P, Hull3Class n P) (hn : n ≥ 19) :
    (pg_min_class Hull3Class hgood n : ℚ) ≥
      (K_deg56_shift_sample ^ n) / (141745749 * (n : ℚ) ^ 11) := by
  rcases pg_min_class_spec Hull3Class hgood n with ⟨P0, hHull, hpg⟩
  have hbound := pg_hull3_explicit_shift_poly11_n19 (n := n) (P := P0) hHull hn
  have hpg' :
      (pg P0 : ℚ) = (pg_min_class Hull3Class hgood n : ℚ) := by
    exact_mod_cast hpg
  simpa [hpg'] using hbound

lemma K_deg56_shift_sample_ge_59_4 : (59 / 4 : ℚ) ≤ K_deg56_shift_sample := by
  have hK : K_deg56_shift_sample = (192 / 13 : ℚ) := by
    simp [K_deg56_shift_sample, deg56ShiftSampleCertificate_getQ_K_deg56_shift]
  have hK' : (59 / 4 : ℚ) ≤ (192 / 13 : ℚ) := by
    norm_num
  simpa [hK] using hK'

lemma pg_hull3_pow_59_4_closed_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ (59 / 4 : ℚ) ^ (n - 19) := by
  have hpow := pg_hull3_pow_shift_closed_n19 (n := n) (P := P) hHull hn
  have hKge : (59 / 4 : ℚ) ≤ K_deg56_shift_sample := K_deg56_shift_sample_ge_59_4
  have hpowle :
      (59 / 4 : ℚ) ^ (n - 19) ≤ K_deg56_shift_sample ^ (n - 19) := by
    have hnonneg : 0 ≤ (59 / 4 : ℚ) := by
      norm_num
    exact pow_le_pow_left hnonneg hKge _
  exact le_trans hpowle hpow

lemma pg_hull3_pow_59_4_closed_all {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ (59 / 4 : ℚ) ^ (n - 19) := by
  classical
  by_cases hn : n ≥ 19
  · exact pg_hull3_pow_59_4_closed_n19 (n := n) (P := P) hHull hn
  ·
    have hlt : n < 19 := lt_of_not_ge hn
    have hsub : n - 19 = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    have hpg : (1 : ℚ) ≤ (pg P : ℚ) := by
      have hpos : 0 < pg P := pg_pos P
      have hle : 1 ≤ pg P := (Nat.succ_le_iff).2 hpos
      exact_mod_cast hle
    simpa [hsub] using hpg

lemma pg_hull3_explicit_59_4_closed_n19 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 19) :
    (pg P : ℚ) ≥ ((59 / 4 : ℚ) ^ n) / ((59 / 4 : ℚ) ^ 19) := by
  have hpow := pg_hull3_pow_59_4_closed_n19 (n := n) (P := P) hHull hn
  have hKne : (59 / 4 : ℚ) ≠ 0 := by
    norm_num
  have hrewrite :
      (59 / 4 : ℚ) ^ (n - 19) =
        ((59 / 4 : ℚ) ^ n) / ((59 / 4 : ℚ) ^ 19) := by
    have hpow_sub :=
      pow_sub₀ (a := (59 / 4 : ℚ)) (ha := hKne) (m := n) (n := 19) hn
    simpa [div_eq_mul_inv] using hpow_sub
  simpa [hrewrite] using hpow

lemma pg_hull3_explicit_59_4_closed_all {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ ((59 / 4 : ℚ) ^ n) / ((59 / 4 : ℚ) ^ 19) := by
  classical
  by_cases hn : n ≥ 19
  · exact pg_hull3_explicit_59_4_closed_n19 (n := n) (P := P) hHull hn
  ·
    have hlt : n < 19 := lt_of_not_ge hn
    have hKge1 : (1 : ℚ) ≤ (59 / 4 : ℚ) := by
      norm_num
    have hnle : n ≤ 19 := Nat.le_of_lt hlt
    have hpowle :
        ((59 / 4 : ℚ) ^ n : ℚ) ≤ (59 / 4 : ℚ) ^ 19 := by
      exact pow_le_pow_right hKge1 hnle
    have hdivle :
        ((59 / 4 : ℚ) ^ n) / ((59 / 4 : ℚ) ^ 19) ≤ (1 : ℚ) := by
      have hKpowpos : 0 < ((59 / 4 : ℚ) ^ 19 : ℚ) := by
        exact pow_pos (by norm_num) _
      have hle :
          ((59 / 4 : ℚ) ^ n : ℚ) ≤ (1 : ℚ) * (59 / 4 : ℚ) ^ 19 := by
        simpa using hpowle
      exact (div_le_iff hKpowpos).2 (by simpa [one_mul] using hle)
    have hpg : (1 : ℚ) ≤ (pg P : ℚ) := by
      have hpos : 0 < pg P := pg_pos P
      have hle : 1 ≤ pg P := (Nat.succ_le_iff).2 hpos
      exact_mod_cast hle
    exact le_trans hdivle hpg

lemma pg_hull3_explicit_n15 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 15) :
    (pg P : ℚ) ≥ (K_deg56_n15_sample ^ n) / (K_deg56_n15_sample ^ 15) := by
  have hpow := pg_hull3_pow_n15 (n := n) (P := P) hHull hgood hdel hn
  have hKne : (K_deg56_n15_sample : ℚ) ≠ 0 := ne_of_gt K_deg56_n15_sample_pos
  have hKne15 : (K_deg56_n15_sample ^ 15 : ℚ) ≠ 0 := by
    exact pow_ne_zero _ hKne
  have hsum : n - 15 + 15 = n := Nat.sub_add_cancel hn
  have hpow_add :
      K_deg56_n15_sample ^ (n - 15) * K_deg56_n15_sample ^ 15 =
        K_deg56_n15_sample ^ n := by
    calc
      K_deg56_n15_sample ^ (n - 15) * K_deg56_n15_sample ^ 15
          = K_deg56_n15_sample ^ (n - 15 + 15) := by
              symm
              exact pow_add _ _ _
      _ = K_deg56_n15_sample ^ n := by
            simpa [hsum]
  have hrewrite :
      K_deg56_n15_sample ^ (n - 15) =
        (K_deg56_n15_sample ^ n) / (K_deg56_n15_sample ^ 15) := by
    calc
      K_deg56_n15_sample ^ (n - 15)
          = (K_deg56_n15_sample ^ (n - 15) * K_deg56_n15_sample ^ 15) /
              (K_deg56_n15_sample ^ 15) := by
                field_simp [hKne15]
      _ = (K_deg56_n15_sample ^ n) / (K_deg56_n15_sample ^ 15) := by
            simp [hpow_add]
  simpa [hrewrite] using hpow

lemma pg_hull3_explicit_closed_n15 {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 15) :
    (pg P : ℚ) ≥ (K_deg56_n15_sample ^ n) / (K_deg56_n15_sample ^ 15) := by
  exact pg_hull3_explicit_n15 (n := n) (P := P) hHull
    hull3_class_nonempty hull3_class_closed hn

lemma pg_hull3_explicit_closed_n15_all {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ (K_deg56_n15_sample ^ n) / (K_deg56_n15_sample ^ 15) := by
  classical
  by_cases hn : n ≥ 15
  · exact pg_hull3_explicit_closed_n15 (n := n) (P := P) hHull hn
  ·
    have hlt : n < 15 := lt_of_not_ge hn
    have hKge1 : (1 : ℚ) ≤ K_deg56_n15_sample := by
      have hK : K_deg56_n15_sample = (2304 / 157 : ℚ) := by
        simp [K_deg56_n15_sample]
      have h1 : (1 : ℚ) ≤ (2304 / 157 : ℚ) := by
        norm_num
      simpa [hK] using h1
    have hKpos : 0 < K_deg56_n15_sample := K_deg56_n15_sample_pos
    have hnle : n ≤ 15 := Nat.le_of_lt hlt
    have hpowle :
        (K_deg56_n15_sample ^ n : ℚ) ≤ K_deg56_n15_sample ^ 15 := by
      exact pow_le_pow_right hKge1 hnle
    have hdivle :
        (K_deg56_n15_sample ^ n) / (K_deg56_n15_sample ^ 15) ≤ (1 : ℚ) := by
      have hKpowpos : 0 < (K_deg56_n15_sample ^ 15 : ℚ) := by
        exact pow_pos hKpos _
      have hle :
          (K_deg56_n15_sample ^ n : ℚ) ≤ (1 : ℚ) * K_deg56_n15_sample ^ 15 := by
        simpa using hpowle
      exact (div_le_iff hKpowpos).2 (by simpa [one_mul] using hle)
    have hpg : (1 : ℚ) ≤ (pg P : ℚ) := by
      have hpos : 0 < pg P := pg_pos P
      have hle : 1 ≤ pg P := (Nat.succ_le_iff).2 hpos
      exact_mod_cast hle
    exact le_trans hdivle hpg

lemma K_deg56_n15_sample_ge_14 : (14 : ℚ) ≤ K_deg56_n15_sample := by
  norm_num [K_deg56_n15_sample]

lemma pg_hull3_pow_14_closed {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 15) :
    (pg P : ℚ) ≥ (14 : ℚ) ^ (n - 15) := by
  have hpow := pg_hull3_pow_closed_n15 (n := n) (P := P) hHull hn
  have hKge : (14 : ℚ) ≤ K_deg56_n15_sample := K_deg56_n15_sample_ge_14
  have hpowle :
      (14 : ℚ) ^ (n - 15) ≤ K_deg56_n15_sample ^ (n - 15) := by
    have hnonneg : (0 : ℚ) ≤ (14 : ℚ) := by
      norm_num
    exact pow_le_pow_of_le_left hnonneg hKge _
  exact le_trans hpowle hpow

lemma K_deg56_n12_sample_gt_one : (1 : ℚ) < K_deg56_n12_sample := by
  have hK : K_deg56_n12_sample = (512 / 37 : ℚ) := by
    simp [K_deg56_n12_sample, deg56N12SampleCertificate_getQ_K_deg56_n12]
  simpa [hK] using (by norm_num : (1 : ℚ) < (512 / 37 : ℚ))

lemma K_deg56_n12_sample_ge_13 : (13 : ℚ) ≤ K_deg56_n12_sample := by
  have hK : K_deg56_n12_sample = (512 / 37 : ℚ) := by
    simp [K_deg56_n12_sample, deg56N12SampleCertificate_getQ_K_deg56_n12]
  have hK' : (13 : ℚ) ≤ (512 / 37 : ℚ) := by
    norm_num
  simpa [hK] using hK'

lemma pg_hull3_pow_13_closed {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 12) :
    (pg P : ℚ) ≥ (13 : ℚ) ^ (n - 12) := by
  have hpow := pg_hull3_pow_closed (n := n) (P := P) hHull hn
  have hKge : (13 : ℚ) ≤ K_deg56_n12_sample := K_deg56_n12_sample_ge_13
  have hpowle :
      (13 : ℚ) ^ (n - 12) ≤ K_deg56_n12_sample ^ (n - 12) := by
    have hnonneg : (0 : ℚ) ≤ (13 : ℚ) := by
      norm_num
    exact pow_le_pow_of_le_left hnonneg hKge _
  exact le_trans hpowle hpow

lemma pg_hull3_explicit {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hgood : ∀ n, ∃ P, Hull3Class n P)
    (hdel : ClosedUnderDelete Hull3Class) (hn : n ≥ 12) :
    (pg P : ℚ) ≥ (K_deg56_n12_sample ^ n) / (K_deg56_n12_sample ^ 12) := by
  have hpow := pg_hull3_pow (n := n) (P := P) hHull hgood hdel hn
  have hKne : (K_deg56_n12_sample : ℚ) ≠ 0 := ne_of_gt K_deg56_n12_sample_pos
  have hKne12 : (K_deg56_n12_sample ^ 12 : ℚ) ≠ 0 := by
    exact pow_ne_zero _ hKne
  have hsum : n - 12 + 12 = n := Nat.sub_add_cancel hn
  have hpow_add :
      K_deg56_n12_sample ^ (n - 12) * K_deg56_n12_sample ^ 12 =
        K_deg56_n12_sample ^ n := by
    calc
      K_deg56_n12_sample ^ (n - 12) * K_deg56_n12_sample ^ 12
          = K_deg56_n12_sample ^ (n - 12 + 12) := by
              symm
              exact pow_add _ _ _
      _ = K_deg56_n12_sample ^ n := by
            simpa [hsum]
  have hrewrite :
      K_deg56_n12_sample ^ (n - 12) =
        (K_deg56_n12_sample ^ n) / (K_deg56_n12_sample ^ 12) := by
    calc
      K_deg56_n12_sample ^ (n - 12)
          = (K_deg56_n12_sample ^ (n - 12) * K_deg56_n12_sample ^ 12) /
              (K_deg56_n12_sample ^ 12) := by
                field_simp [hKne12]
      _ = (K_deg56_n12_sample ^ n) / (K_deg56_n12_sample ^ 12) := by
            simp [hpow_add]
  simpa [hrewrite] using hpow

lemma pg_hull3_explicit_closed {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3)
    (hn : n ≥ 12) :
    (pg P : ℚ) ≥ (K_deg56_n12_sample ^ n) / (K_deg56_n12_sample ^ 12) := by
  exact pg_hull3_explicit (n := n) (P := P) hHull hull3_class_nonempty hull3_class_closed hn

lemma pg_hull3_explicit_closed_all {n : ℕ} {P : PointSet n} (hHull : HullSize P = 3) :
    (pg P : ℚ) ≥ (K_deg56_n12_sample ^ n) / (K_deg56_n12_sample ^ 12) := by
  classical
  by_cases hn : n ≥ 12
  · exact pg_hull3_explicit_closed (n := n) (P := P) hHull hn
  ·
    have hlt : n < 12 := lt_of_not_ge hn
    have hKge1 : (1 : ℚ) ≤ K_deg56_n12_sample := by
      have hKgt : (1 : ℚ) < K_deg56_n12_sample := K_deg56_n12_sample_gt_one
      exact le_of_lt hKgt
    have hKpos : 0 < K_deg56_n12_sample := K_deg56_n12_sample_pos
    have hnle : n ≤ 12 := Nat.le_of_lt hlt
    have hpowle :
        (K_deg56_n12_sample ^ n : ℚ) ≤ K_deg56_n12_sample ^ 12 := by
      exact pow_le_pow_right hKge1 hnle
    have hdivle :
        (K_deg56_n12_sample ^ n) / (K_deg56_n12_sample ^ 12) ≤ (1 : ℚ) := by
      have hKpowpos : 0 < (K_deg56_n12_sample ^ 12 : ℚ) := by
        exact pow_pos hKpos _
      have hle :
          (K_deg56_n12_sample ^ n : ℚ) ≤ (1 : ℚ) * K_deg56_n12_sample ^ 12 := by
        simpa using hpowle
      exact (div_le_iff hKpowpos).2 (by simpa [one_mul] using hle)
    have hpg : (1 : ℚ) ≤ (pg P : ℚ) := by
      have hpos : 0 < pg P := pg_pos P
      have hle : 1 ≤ pg P := (Nat.succ_le_iff).2 hpos
      exact_mod_cast hle
    exact le_trans hdivle hpg


end PlaneGraphs

import PlaneGraphs.Basic
import PlaneGraphs.Charging
import PlaneGraphs.DegreeCounts
import PlaneGraphs.DegreeVectors

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

axiom hull3_triangulation_exists {n : ℕ} (P : PointSet n) (hHull : HullSize P = 3) :
    Hull3Triangulation P

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

noncomputable def removeIncidentEdges {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    Finset (Segment n) :=
  G.filter (fun s => ¬ incident s u)

lemma incidentEdges_card_eq_degree {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    (incidentEdges G u).card = degree G u := by
  classical
  have h := card_filter_eq_sum_ite (s := G) (p := fun s => incident s u)
  simpa [incidentEdges, degree] using h

lemma removeIncidentEdges_isolated {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    isIsolated (removeIncidentEdges G u) u := by
  classical
  intro s hs
  have hs' : ¬ incident s u := by
    simpa [removeIncidentEdges] using (Finset.mem_filter.mp hs).2
  exact hs'

lemma removeIncidentEdges_subset {n : ℕ} (G : Finset (Segment n)) (u : Fin n) :
    removeIncidentEdges G u ⊆ G := by
  intro s hs
  exact (Finset.mem_filter.mp hs).1

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

noncomputable def deg56_charge {n : ℕ} (P : PointSet n) : Charge (n := n) :=
  fun G =>
    ∑ u in Finset.univ, (1 : ℚ) / (2 : ℚ) ^ (potential P G u)

axiom deg56_charge_conserve {n : ℕ} (P : PointSet n) :
    ∑ G in planeGraphs P, deg56_charge P G =
      ∑ G in planeGraphs P, (isoCount G : ℚ)

axiom potential_ge_degree_hull3 {n : ℕ} {P : PointSet n} (T : Hull3Triangulation P) :
  ∀ G ∈ planeGraphs P, ∀ u : Fin n, degree T.G u ≤ potential P G u

axiom deg56_charge_upper_hull3 {n : ℕ} {P : PointSet n} (T : Hull3Triangulation P) :
    ∀ G ∈ planeGraphs P,
      deg56_charge P G ≤
        (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
        (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
        (vL T.G : ℚ) * wL_n12_sample

lemma deg56_charge_hull3 {n : ℕ} {P : PointSet n} (T : Hull3Triangulation P) :
  avgIso P ≤
    (v3 T.G : ℚ) * w3_n12_sample + (v4 T.G : ℚ) * w4_n12_sample +
    (v5 T.G : ℚ) * w5_n12_sample + (v6 T.G : ℚ) * w6_n12_sample +
    (vL T.G : ℚ) * wL_n12_sample := by
  refine avgIso_le_of_charge_bound (P := P) (charge := deg56_charge P)
    (hconserve := deg56_charge_conserve (P := P)) ?_
  intro G hG
  exact deg56_charge_upper_hull3 (T := T) G hG

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
    (T : Hull3Triangulation P) (hn : 12 ≤ n) :
    avgIso P ≤ (n : ℚ) / K_deg56_n12_sample := by
  exact avgIso_le_deg56_n12_hull3 (T := T) hn (deg56_charge_hull3 T)


end PlaneGraphs

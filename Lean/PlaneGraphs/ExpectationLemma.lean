import Mathlib
import PlaneGraphs.Basic

open scoped BigOperators

namespace PlaneGraphs


def isIsolated {n : ℕ} (G : Finset (Segment n)) (v : Fin n) : Prop :=
  ∀ s ∈ G, ¬ incident s v


noncomputable def isoCount {n : ℕ} (G : Finset (Segment n)) : Nat := by
  classical
  exact (Finset.univ.filter (fun v => isIsolated G v)).card


noncomputable def planeGraphsIso {n : ℕ} (P : PointSet n) (v : Fin n) : Finset (Finset (Segment n)) := by
  classical
  exact (planeGraphs P).filter (fun G => isIsolated G v)

lemma mem_planeGraphs_iff {n : ℕ} (P : PointSet n) {G : Finset (Segment n)} :
    G ∈ planeGraphs P ↔ isIndependent (crossingGraph P) G := by
  classical
  simp [planeGraphs]

lemma mem_planeGraphsIso_iff {n : ℕ} (P : PointSet n) {v : Fin n} {G : Finset (Segment n)} :
    G ∈ planeGraphsIso P v ↔
      isIndependent (crossingGraph P) G ∧ isIsolated G v := by
  classical
  simp [planeGraphsIso, mem_planeGraphs_iff]

noncomputable def succAboveInv {n : ℕ} (v : Fin (n + 1)) (i : Fin (n + 1)) (h : i ≠ v) : Fin n :=
  Classical.choose (Fin.exists_succAbove_eq (x := i) (y := v) h)

lemma succAboveInv_spec {n : ℕ} (v : Fin (n + 1)) (i : Fin (n + 1)) (h : i ≠ v) :
    v.succAbove (succAboveInv v i h) = i :=
  Classical.choose_spec (Fin.exists_succAbove_eq (x := i) (y := v) h)

lemma not_incident_segmentMap {n : ℕ} (v : Fin (n + 1)) (s : Segment n) :
    ¬ incident (segmentMap v s) v := by
  classical
  intro hv
  have hv' : v ∈ Sym2.map v.succAbove s.1 := by
    simpa [segmentMap, incident] using hv
  rcases (Sym2.mem_map (f := v.succAbove) (b := v) (z := s.1)).1 hv' with ⟨a, _, hEq⟩
  exact (Fin.succAbove_ne v a hEq).elim

lemma segmentCrosses_deletePoint_iff {n : ℕ} (P : PointSet (n + 1)) (v : Fin (n + 1))
    (s t : Segment n) :
    segmentCrosses (deletePoint P v) s t ↔
      segmentCrosses P (segmentMap v s) (segmentMap v t) := by
  classical
  cases' s with s hs
  cases' t with t ht
  revert hs ht
  refine Sym2.inductionOn₂ s t ?_
  intro a b c d _ _
  simp [segmentCrosses, segmentMap, deletePoint, Sym2.map_pair_eq]

def segmentMapFinset {n : ℕ} (v : Fin (n + 1)) (s : Finset (Segment n)) :
    Finset (Segment (n + 1)) :=
  s.map ⟨segmentMap v, segmentMap_injective v⟩

lemma mem_segmentMapFinset {n : ℕ} {v : Fin (n + 1)} {s : Finset (Segment n)}
    {x : Segment (n + 1)} :
    x ∈ segmentMapFinset v s ↔ ∃ y ∈ s, segmentMap v y = x := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Finset.mem_map.2 ⟨y, hy, rfl⟩

lemma isIsolated_segmentMapFinset {n : ℕ} (v : Fin (n + 1)) (s : Finset (Segment n)) :
    isIsolated (segmentMapFinset v s) v := by
  classical
  intro t ht
  rcases (mem_segmentMapFinset (v := v) (s := s) (x := t)).1 ht with ⟨y, _, rfl⟩
  exact not_incident_segmentMap v y

lemma isIndependent_map_iff {n : ℕ} (P : PointSet (n + 1)) (v : Fin (n + 1))
    (s : Finset (Segment n)) :
    isIndependent (crossingGraph (deletePoint P v)) s ↔
      isIndependent (crossingGraph P) (segmentMapFinset v s) := by
  classical
  constructor
  · intro h u v' hu hv hne
    rcases (mem_segmentMapFinset (v := v) (s := s) (x := u)).1 hu with ⟨u', hu', rfl⟩
    rcases (mem_segmentMapFinset (v := v) (s := s) (x := v')).1 hv with ⟨v'', hv'', rfl⟩
    have hne' : u' ≠ v'' := by
      intro h'
      apply hne
      simp [h']
    have hno := h hu' hv'' hne'
    intro hcross
    exact hno ((segmentCrosses_deletePoint_iff P v u' v'').2 hcross)
  · intro h u v' hu hv hne
    have hu' : segmentMap v u ∈ segmentMapFinset v s :=
      (mem_segmentMapFinset (v := v) (s := s)).2 ⟨u, hu, rfl⟩
    have hv' : segmentMap v v' ∈ segmentMapFinset v s :=
      (mem_segmentMapFinset (v := v) (s := s)).2 ⟨v', hv, rfl⟩
    have hne' : segmentMap v u ≠ segmentMap v v' := by
      intro h'
      apply hne
      exact segmentMap_injective v h'
    have hno := h hu' hv' hne'
    intro hcross
    exact hno ((segmentCrosses_deletePoint_iff P v u v').1 hcross)

lemma exists_segmentMap_eq {n : ℕ} (v : Fin (n + 1)) (s : Segment (n + 1))
    (h : ¬ incident s v) : ∃ t : Segment n, segmentMap v t = s := by
  classical
  cases' s with s hs
  revert hs h
  refine Sym2.inductionOn s ?_
  intro a b hs h
  have ha : a ≠ v := by
    intro hEq
    apply h
    have : v ∈ s(a, b) := (Sym2.mem_iff' (a := v) (b := a) (c := b)).2 (Or.inl hEq.symm)
    simpa [incident] using this
  have hb : b ≠ v := by
    intro hEq
    apply h
    have : v ∈ s(a, b) := (Sym2.mem_iff' (a := v) (b := a) (c := b)).2 (Or.inr hEq.symm)
    simpa [incident] using this
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (x := a) (y := v) ha
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (x := b) (y := v) hb
  have hab : a ≠ b := by
    intro hEq
    apply hs
    exact (Sym2.mk_isDiag_iff).2 hEq
  have hab' : a' ≠ b' := by
    intro hEq
    apply hab
    have : v.succAbove a' = v.succAbove b' := by
      simp [hEq]
    simpa [ha', hb'] using this
  refine ⟨⟨s(a', b'), by
    simpa [Sym2.mk_isDiag_iff] using hab'⟩, ?_⟩
  apply Subtype.ext
  simp [segmentMap, Sym2.map_pair_eq, ha', hb']

noncomputable def segmentUnmap {n : ℕ} (v : Fin (n + 1)) (s : Segment (n + 1))
    (h : ¬ incident s v) : Segment n :=
  Classical.choose (exists_segmentMap_eq v s h)

lemma segmentMap_segmentUnmap {n : ℕ} (v : Fin (n + 1)) (s : Segment (n + 1))
    (h : ¬ incident s v) : segmentMap v (segmentUnmap v s h) = s :=
  Classical.choose_spec (exists_segmentMap_eq v s h)

lemma segmentUnmap_map {n : ℕ} (v : Fin (n + 1)) (s : Segment n) :
    segmentUnmap v (segmentMap v s) (not_incident_segmentMap v s) = s := by
  apply segmentMap_injective v
  simpa [segmentUnmap] using
    (segmentMap_segmentUnmap (v := v) (s := segmentMap v s)
      (h := not_incident_segmentMap v s))

noncomputable def preimageSegmentMap {n : ℕ} (v : Fin (n + 1))
    (G : Finset (Segment (n + 1))) : Finset (Segment n) :=
  G.preimage (segmentMap v) (segmentMap_injective v).injOn

lemma segmentMapFinset_preimage {n : ℕ} (v : Fin (n + 1)) (G : Finset (Segment (n + 1)))
    (h : isIsolated G v) : segmentMapFinset v (preimageSegmentMap v G) = G := by
  classical
  have hsubset : (↑G : Set (Segment (n + 1))) ⊆ Set.range (segmentMap v) := by
    intro s hs
    have hs' : ¬ incident s v := by
      exact h s (by simpa using hs)
    rcases exists_segmentMap_eq v s hs' with ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have hbij : Set.BijOn (segmentMap v) (segmentMap v ⁻¹' (↑G : Set _)) (↑G : Set _) := by
    refine ⟨?maps, ?inj, ?surj⟩
    · intro x hx
      exact hx
    · intro x _ y _ hxy
      exact segmentMap_injective v hxy
    · intro y hy
      rcases hsubset hy with ⟨x, rfl⟩
      exact ⟨x, hy, rfl⟩
  have himage :
      Finset.image (segmentMap v) (preimageSegmentMap v G) = G := by
    simpa [preimageSegmentMap] using
      (Finset.image_preimage_of_bij (f := segmentMap v) (s := G) hbij)
  simpa [segmentMapFinset, Finset.map_eq_image] using himage

lemma planeGraphsIso_card_eq_pg_deletePoint {n : ℕ} (P : PointSet (n + 1)) (v : Fin (n + 1)) :
    (planeGraphsIso P v).card = pg (deletePoint P v) := by
  classical
  have hbij := Finset.card_bij' (s := planeGraphs (deletePoint P v)) (t := planeGraphsIso P v)
    (i := fun G _ => segmentMapFinset v G)
    (j := fun G _ => preimageSegmentMap v G)
    (hi := by
      intro G hG
      have hInd : isIndependent (crossingGraph (deletePoint P v)) G :=
        (mem_planeGraphs_iff (deletePoint P v)).1 hG
      have hInd' : isIndependent (crossingGraph P) (segmentMapFinset v G) :=
        (isIndependent_map_iff P v G).1 hInd
      have hIso : isIsolated (segmentMapFinset v G) v :=
        isIsolated_segmentMapFinset v G
      exact (mem_planeGraphsIso_iff (P := P) (v := v)).2 ⟨hInd', hIso⟩)
    (hj := by
      intro G hG
      rcases (mem_planeGraphsIso_iff (P := P) (v := v)).1 hG with ⟨hInd, hIso⟩
      have hMapInd :
          isIndependent (crossingGraph P) (segmentMapFinset v (preimageSegmentMap v G)) := by
        simpa [segmentMapFinset_preimage v G hIso] using hInd
      have hInd' :
          isIndependent (crossingGraph (deletePoint P v)) (preimageSegmentMap v G) :=
        (isIndependent_map_iff P v (preimageSegmentMap v G)).2 hMapInd
      exact (mem_planeGraphs_iff (deletePoint P v)).2 hInd')
    (left_inv := by
      intro G hG
      simpa [preimageSegmentMap, segmentMapFinset] using
        (Finset.preimage_map (f := ⟨segmentMap v, segmentMap_injective v⟩) (s := G)))
    (right_inv := by
      intro G hG
      rcases (mem_planeGraphsIso_iff (P := P) (v := v)).1 hG with ⟨_, hIso⟩
      simp [segmentMapFinset_preimage v G hIso])
  simpa [pg] using hbij.symm

lemma sum_isoCount_eq_sum_planeGraphsIso {n : ℕ} (P : PointSet n) :
    (∑ G in planeGraphs P, isoCount G) = ∑ v in Finset.univ, (planeGraphsIso P v).card := by
  classical
  have h_iso : ∀ G : Finset (Segment n),
      isoCount G = ∑ v in Finset.univ, (if isIsolated G v then 1 else 0) := by
    intro G
    classical
    calc
      isoCount G
          = (Finset.univ.filter (fun v => isIsolated G v)).card := by
              rfl
      _ = ∑ _v in (Finset.univ.filter (fun v => isIsolated G v)), (1 : Nat) := by
              exact (Finset.card_eq_sum_ones (s := Finset.univ.filter (fun v => isIsolated G v)))
      _ = ∑ v in Finset.univ, (if isIsolated G v then 1 else 0) := by
              exact (Finset.sum_filter (s := Finset.univ) (p := fun v => isIsolated G v)
                (f := fun _ => (1 : Nat)))
  calc
    ∑ G in planeGraphs P, isoCount G
        = ∑ G in planeGraphs P, ∑ v in Finset.univ, (if isIsolated G v then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro G _
            exact h_iso G
    _ = ∑ v in Finset.univ, ∑ G in planeGraphs P, (if isIsolated G v then 1 else 0) := by
            exact Finset.sum_comm
    _ = ∑ v in Finset.univ, (planeGraphsIso P v).card := by
            refine Finset.sum_congr rfl ?_
            intro v _
            have hsum :
                ∑ G in planeGraphs P, (if isIsolated G v then 1 else 0) =
                ∑ _G in (planeGraphs P).filter (fun G => isIsolated G v), (1 : Nat) := by
                symm
                exact
                  (Finset.sum_filter (s := planeGraphs P) (p := fun G => isIsolated G v)
                    (f := fun _ => (1 : Nat)))
            have hcard :
                (planeGraphsIso P v).card =
                  ∑ _G in (planeGraphs P).filter (fun G => isIsolated G v), (1 : Nat) := by
                simp [planeGraphsIso]
            exact hsum.trans hcard.symm

lemma pg_pos {n : ℕ} (P : PointSet n) : 0 < pg P := by
  classical
  have hInd : isIndependent (crossingGraph P) (∅ : Finset (Segment n)) := by
    intro u _ hu _ _
    have : False := (Finset.not_mem_empty u) hu
    exact this.elim
  have hmem : (∅ : Finset (Segment n)) ∈ planeGraphs P := by
    simp [planeGraphs, hInd]
  simpa [pg] using (Finset.card_pos.mpr ⟨∅, hmem⟩)

noncomputable def avgIso {n : ℕ} (P : PointSet n) : ℚ :=
  (∑ G in planeGraphs P, (isoCount G : ℚ)) / (pg P : ℚ)

lemma avgIso_mul_pg {n : ℕ} (P : PointSet n) :
    avgIso P * (pg P : ℚ) = ∑ G in planeGraphs P, (isoCount G : ℚ) := by
  have hpg : (pg P : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pg_pos P))
  simp [avgIso, hpg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma sum_isoCount_eq_sum_pg_delete {n : ℕ} (P : PointSet (n + 1)) :
    (∑ G in planeGraphs P, isoCount G) = ∑ v in Finset.univ, pg (deletePoint P v) := by
  classical
  have h := sum_isoCount_eq_sum_planeGraphsIso (P := P)
  refine h.trans ?_
  refine Finset.sum_congr rfl ?_
  intro v _
  exact planeGraphsIso_card_eq_pg_deletePoint P v

lemma pg_lower_bound_of_avgIso {n : ℕ} (P : PointSet (n + 1)) {K m : ℚ}
    (hK : 0 < K) (havg : avgIso P ≤ (n + 1 : ℚ) / K)
    (hmin : ∀ v : Fin (n + 1), (pg (deletePoint P v) : ℚ) ≥ m) :
    (pg P : ℚ) ≥ K * m := by
  have hsum_ge :
      (n + 1 : ℚ) * m ≤ ∑ v in Finset.univ, (pg (deletePoint P v) : ℚ) := by
    have hmin' : ∀ v ∈ (Finset.univ : Finset (Fin (n + 1))),
        m ≤ (pg (deletePoint P v) : ℚ) := by
      intro v _
      exact hmin v
    have hsum := Finset.sum_le_sum hmin'
    simpa using hsum
  have hsum_eq :
      (∑ G in planeGraphs P, (isoCount G : ℚ)) =
        ∑ v in Finset.univ, (pg (deletePoint P v) : ℚ) := by
    exact_mod_cast (sum_isoCount_eq_sum_pg_delete (P := P))
  have hsum_le :
      (∑ G in planeGraphs P, (isoCount G : ℚ)) ≤ (n + 1 : ℚ) / K * (pg P : ℚ) := by
    have hpg_nonneg : 0 ≤ (pg P : ℚ) := by
      exact_mod_cast (Nat.zero_le _)
    have hmul := mul_le_mul_of_nonneg_right havg hpg_nonneg
    simpa [avgIso_mul_pg] using hmul
  have hchain :
      (n + 1 : ℚ) * m ≤ (n + 1 : ℚ) / K * (pg P : ℚ) := by
    exact hsum_ge.trans (by simpa [hsum_eq] using hsum_le)
  have hpos : (0 : ℚ) < (n + 1 : ℚ) := by
    exact_mod_cast (Nat.succ_pos _)
  have hpos' : 0 ≤ (1 / (n + 1 : ℚ)) := by
    exact one_div_nonneg.mpr (le_of_lt hpos)
  have hdiv := mul_le_mul_of_nonneg_left hchain hpos'
  have hposne : (n + 1 : ℚ) ≠ 0 := ne_of_gt hpos
  have hdiv' : m ≤ (1 / K) * (pg P : ℚ) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hposne] using hdiv
  have hKpos : 0 ≤ K := le_of_lt hK
  have hmul := mul_le_mul_of_nonneg_left hdiv' hKpos
  have hKne : (K : ℚ) ≠ 0 := ne_of_gt hK
  have hmul' : K * m ≤ (pg P : ℚ) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hKne] using hmul
  exact hmul'

def basePointSet (n : ℕ) : PointSet n :=
  fun _ => (0, 0)

lemma exists_pg_val (n : ℕ) : ∃ m, ∃ P : PointSet n, pg P = m := by
  refine ⟨pg (basePointSet n), basePointSet n, rfl⟩

noncomputable def pg_min (n : ℕ) : Nat := by
  classical
  exact Nat.find (exists_pg_val n)

lemma pg_min_spec (n : ℕ) : ∃ P : PointSet n, pg P = pg_min n := by
  classical
  exact Nat.find_spec (exists_pg_val n)

lemma pg_min_le {n : ℕ} (P : PointSet n) : pg_min n ≤ pg P := by
  classical
  have h : ∃ P' : PointSet n, pg P' = pg P := ⟨P, rfl⟩
  exact Nat.find_min' (H := exists_pg_val n) (m := pg P) h

lemma pg_min_lower_bound {n : ℕ} {K : ℚ}
    (hK : 0 < K)
    (havg : ∀ P : PointSet (n + 1), avgIso P ≤ (n + 1 : ℚ) / K) :
    (pg_min (n + 1) : ℚ) ≥ K * (pg_min n : ℚ) := by
  rcases pg_min_spec (n + 1) with ⟨P0, hP0⟩
  have hmin :
      ∀ v : Fin (n + 1), (pg (deletePoint P0 v) : ℚ) ≥ (pg_min n : ℚ) := by
    intro v
    exact_mod_cast (pg_min_le (P := deletePoint P0 v))
  have hbound :
      (pg P0 : ℚ) ≥ K * (pg_min n : ℚ) := by
    exact
      pg_lower_bound_of_avgIso (P := P0) (K := K) (m := (pg_min n : ℚ)) hK
        (havg P0) hmin
  have hP0' : (pg P0 : ℚ) = (pg_min (n + 1) : ℚ) := by
    exact_mod_cast hP0
  simpa [hP0'] using hbound

lemma pg_min_pow {n : ℕ} {K : ℚ} (hK : 0 < K)
    (havg : ∀ {n} (P : PointSet (n + 1)), avgIso P ≤ (n + 1 : ℚ) / K) :
    (pg_min n : ℚ) ≥ K ^ n := by
  induction n with
  | zero =>
      rcases pg_min_spec 0 with ⟨P0, hP0⟩
      have hpos : 0 < pg P0 := pg_pos P0
      have hle : 1 ≤ pg_min 0 := by
        have hle' : 1 ≤ pg P0 := (Nat.succ_le_iff).2 hpos
        simpa [hP0] using hle'
      have hleQ : (pg_min 0 : ℚ) ≥ 1 := by
        exact_mod_cast hle
      simpa using hleQ
  | succ n ih =>
      have hstep :
          (pg_min (n + 1) : ℚ) ≥ K * (pg_min n : ℚ) := by
        exact pg_min_lower_bound (n := n) (K := K) hK (fun P => havg (n := n) P)
      have hmul :
          K * (K ^ n) ≤ K * (pg_min n : ℚ) := by
        have hKnonneg : 0 ≤ K := le_of_lt hK
        exact mul_le_mul_of_nonneg_left ih hKnonneg
      have hchain : K * (K ^ n) ≤ (pg_min (n + 1) : ℚ) :=
        le_trans hmul hstep
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hchain

lemma exists_pg_val_good {n : ℕ} (good : PointSet n → Prop) (hgood : ∃ P, good P) :
    ∃ m, ∃ P : PointSet n, good P ∧ pg P = m := by
  rcases hgood with ⟨P, hP⟩
  exact ⟨pg P, P, hP, rfl⟩

noncomputable def pg_min_class (good : ∀ n, PointSet n → Prop)
    (hgood : ∀ n, ∃ P, good n P) (n : ℕ) : Nat := by
  classical
  exact Nat.find (exists_pg_val_good (good n) (hgood n))

lemma pg_min_class_spec (good : ∀ n, PointSet n → Prop)
    (hgood : ∀ n, ∃ P, good n P) (n : ℕ) :
    ∃ P : PointSet n, good n P ∧ pg P = pg_min_class good hgood n := by
  classical
  exact Nat.find_spec (exists_pg_val_good (good n) (hgood n))

lemma pg_min_class_le (good : ∀ n, PointSet n → Prop)
    (hgood : ∀ n, ∃ P, good n P) {n : ℕ} {P : PointSet n} (hP : good n P) :
    pg_min_class good hgood n ≤ pg P := by
  classical
  have h : ∃ P' : PointSet n, good n P' ∧ pg P' = pg P := ⟨P, hP, rfl⟩
  exact Nat.find_min' (H := exists_pg_val_good (good n) (hgood n)) (m := pg P) h

def ClosedUnderDelete (good : ∀ n, PointSet n → Prop) : Prop :=
  ∀ {n} (P : PointSet (n + 1)), good (n + 1) P → ∀ v, good n (deletePoint P v)

lemma pg_min_class_lower_bound {n : ℕ} {K : ℚ} (hK : 0 < K)
    (good : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, good n P)
    (hclosed : ClosedUnderDelete good)
    (havg : ∀ {n} (P : PointSet (n + 1)), good (n + 1) P →
      avgIso P ≤ (n + 1 : ℚ) / K) :
    (pg_min_class good hgood (n + 1) : ℚ) ≥ K * (pg_min_class good hgood n : ℚ) := by
  rcases pg_min_class_spec good hgood (n + 1) with ⟨P0, hgoodP0, hpg⟩
  have hmin :
      ∀ v : Fin (n + 1), (pg (deletePoint P0 v) : ℚ) ≥
        (pg_min_class good hgood n : ℚ) := by
    intro v
    have hgooddel : good n (deletePoint P0 v) := hclosed P0 hgoodP0 v
    exact_mod_cast (pg_min_class_le good hgood (n := n) (P := deletePoint P0 v) hgooddel)
  have hbound :
      (pg P0 : ℚ) ≥ K * (pg_min_class good hgood n : ℚ) := by
    exact
      pg_lower_bound_of_avgIso (P := P0) (K := K) (m := (pg_min_class good hgood n : ℚ)) hK
        (havg (P := P0) hgoodP0) hmin
  have hP0' : (pg P0 : ℚ) = (pg_min_class good hgood (n + 1) : ℚ) := by
    exact_mod_cast hpg
  simpa [hP0'] using hbound

lemma pg_min_class_pow {n : ℕ} {K : ℚ} (hK : 0 < K)
    (good : ∀ n, PointSet n → Prop) (hgood : ∀ n, ∃ P, good n P)
    (hclosed : ClosedUnderDelete good)
    (havg : ∀ {n} (P : PointSet (n + 1)), good (n + 1) P →
      avgIso P ≤ (n + 1 : ℚ) / K) :
    (pg_min_class good hgood n : ℚ) ≥ K ^ n := by
  induction n with
  | zero =>
      rcases pg_min_class_spec good hgood 0 with ⟨P0, _, hpg⟩
      have hpos : 0 < pg P0 := pg_pos P0
      have hle : 1 ≤ pg_min_class good hgood 0 := by
        have hle' : 1 ≤ pg P0 := (Nat.succ_le_iff).2 hpos
        simpa [hpg] using hle'
      have hleQ : (pg_min_class good hgood 0 : ℚ) ≥ 1 := by
        exact_mod_cast hle
      simpa using hleQ
  | succ n ih =>
      have hstep :
          (pg_min_class good hgood (n + 1) : ℚ) ≥
            K * (pg_min_class good hgood n : ℚ) := by
        exact pg_min_class_lower_bound (n := n) (K := K) (hK := hK) (good := good)
          (hgood := hgood) (hclosed := hclosed) (havg := havg)
      have hmul :
          K * (K ^ n) ≤ K * (pg_min_class good hgood n : ℚ) := by
        have hKnonneg : 0 ≤ K := le_of_lt hK
        exact mul_le_mul_of_nonneg_left ih hKnonneg
      have hchain : K * (K ^ n) ≤ (pg_min_class good hgood (n + 1) : ℚ) :=
        le_trans hmul hstep
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hchain

end PlaneGraphs

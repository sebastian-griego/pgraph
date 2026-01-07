import PlaneGraphs.Basic

namespace PlaneGraphs

def starSegment {n : ℕ} (i : Fin n) : Segment (n + 1) :=
  ⟨Sym2.mk (0, Fin.succ i), by
    intro hdiag
    have hEq : (0 : Fin (n + 1)) = Fin.succ i :=
      (Sym2.mk_isDiag_iff).1 hdiag
    exact (Fin.succ_ne_zero i) hEq.symm⟩

lemma starSegment_injective {n : ℕ} : Function.Injective (@starSegment n) := by
  intro i j h
  have h' : Sym2.mk (0, Fin.succ i) = Sym2.mk (0, Fin.succ j) := by
    simpa [starSegment] using congrArg Subtype.val h
  have h'' : Fin.succ i = Fin.succ j := by
    exact
      (Sym2.congr_right (a := (0 : Fin (n + 1))) (b := Fin.succ i) (c := Fin.succ j)).1 h'
  exact (Fin.succ_injective (n := n)) h''

def starImage {n : ℕ} (s : Finset (Fin n)) : Finset (Segment (n + 1)) :=
  s.image (@starSegment n)

lemma star_no_cross {n : ℕ} (P : PointSet (n + 1)) (i j : Fin n) :
    ¬ segmentCrosses P (starSegment i) (starSegment j) := by
  intro h
  have h' :
      properSegmentIntersect (P 0) (P (Fin.succ i)) (P 0) (P (Fin.succ j)) := by
    simpa [segmentCrosses, starSegment] using h
  rcases h' with ⟨h0, _, _, _, _, _, _, _, _, _⟩
  exact (h0 rfl).elim

lemma starImage_independent {n : ℕ} (P : PointSet (n + 1)) (s : Finset (Fin n)) :
    isIndependent (crossingGraph P) (starImage s) := by
  classical
  intro u v hu hv _
  rcases Finset.mem_image.mp hu with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
  exact star_no_cross P i j

lemma starImage_mem_planeGraphs {n : ℕ} (P : PointSet (n + 1)) (s : Finset (Fin n)) :
    starImage s ∈ planeGraphs P := by
  classical
  have hmem :
      starImage s ∈ (Finset.univ.powerset : Finset (Finset (Segment (n + 1)))) := by
    refine (Finset.mem_powerset).2 ?_
    intro x _
    exact Finset.mem_univ x
  have hind : isIndependent (crossingGraph P) (starImage s) :=
    starImage_independent P s
  exact (Finset.mem_filter).2 ⟨hmem, hind⟩

lemma pg_ge_two_pow {n : ℕ} (P : PointSet (n + 1)) : 2 ^ n ≤ pg P := by
  classical
  let S : Finset (Finset (Fin n)) := Finset.univ.powerset
  have hsubset :
      S.image (starImage (n := n)) ⊆ planeGraphs P := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨t, _, rfl⟩
    exact starImage_mem_planeGraphs (P := P) t
  have hcard_le : (S.image (starImage (n := n))).card ≤ (planeGraphs P).card :=
    Finset.card_le_card hsubset
  have hinj : Function.Injective (starImage (n := n)) :=
    Finset.image_injective (starSegment_injective (n := n))
  have hcard_image : (S.image (starImage (n := n))).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hcardS : S.card = 2 ^ n := by
    simp [S]
  have hle : 2 ^ n ≤ (planeGraphs P).card := by
    have hcard_image' : (S.image (starImage (n := n))).card = 2 ^ n := by
      simpa [hcardS] using hcard_image
    simpa [hcard_image'] using hcard_le
  simpa [pg] using hle

end PlaneGraphs

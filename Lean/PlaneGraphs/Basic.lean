import Mathlib

open scoped BigOperators

namespace PlaneGraphs

abbrev Point := ℤ × ℤ

abbrev PointSet (n : ℕ) := Fin n → Point

opaque HullSize {n : ℕ} : PointSet n → Nat

abbrev Segment (n : ℕ) := { s : Sym2 (Fin n) // ¬ Sym2.IsDiag s }

def incident {n : ℕ} (s : Segment n) (v : Fin n) : Prop :=
  v ∈ s.1

def deletePoint {n : ℕ} (P : PointSet (n + 1)) (v : Fin (n + 1)) : PointSet n :=
  fun i => P (v.succAbove i)

def segmentMap {n : ℕ} (v : Fin (n + 1)) (s : Segment n) : Segment (n + 1) :=
  ⟨Sym2.map v.succAbove s.1, by
    intro hdiag
    have hdiag' :
        Sym2.IsDiag s.1 :=
      (Sym2.isDiag_map (e := s.1) (hf := Fin.succAbove_right_injective)).1 hdiag
    exact s.property hdiag'⟩

lemma segmentMap_injective {n : ℕ} (v : Fin (n + 1)) : Function.Injective (segmentMap v) := by
  intro s t h
  apply Subtype.ext
  have h' : Sym2.map v.succAbove s.1 = Sym2.map v.succAbove t.1 :=
    congrArg Subtype.val h
  exact Sym2.map.injective (Fin.succAbove_right_injective) h'

def orient (a b c : Point) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

lemma orient_swap_left (a b c : Point) : orient b a c = -orient a b c := by
  simp [orient]
  ring

def properSegmentIntersect (a b c d : Point) : Prop :=
  a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
  orient a b c ≠ 0 ∧ orient a b d ≠ 0 ∧
  orient c d a ≠ 0 ∧ orient c d b ≠ 0 ∧
  orient a b c * orient a b d < 0 ∧
  orient c d a * orient c d b < 0

noncomputable instance (a b c d : Point) : Decidable (properSegmentIntersect a b c d) := by
  classical
  infer_instance

lemma orient_swap_left_ne {a b c : Point} (h : orient a b c ≠ 0) : orient b a c ≠ 0 := by
  intro hzero
  apply h
  have hEq : orient b a c = -orient a b c := orient_swap_left a b c
  have : -orient a b c = 0 := by
    simpa [hEq] using hzero
  exact neg_eq_zero.mp this

lemma properSegmentIntersect_symm (a b c d : Point) :
    properSegmentIntersect a b c d ↔ properSegmentIntersect c d a b := by
  constructor
  · intro h
    rcases h with ⟨hac, had, hbc, hbd, h1, h2, h3, h4, h5, h6⟩
    exact ⟨hac.symm, hbc.symm, had.symm, hbd.symm, h3, h4, h1, h2, h6, h5⟩
  · intro h
    rcases h with ⟨hca, hcb, hda, hdb, h1, h2, h3, h4, h5, h6⟩
    exact ⟨hca.symm, hda.symm, hcb.symm, hdb.symm, h3, h4, h1, h2, h6, h5⟩

lemma properSegmentIntersect_swap_left (a b c d : Point) :
    properSegmentIntersect a b c d ↔ properSegmentIntersect b a c d := by
  constructor
  · intro h
    rcases h with ⟨hac, had, hbc, hbd, h1, h2, h3, h4, h5, h6⟩
    have h1' : orient b a c ≠ 0 := orient_swap_left_ne h1
    have h2' : orient b a d ≠ 0 := orient_swap_left_ne h2
    have h5' : orient b a c * orient b a d < 0 := by
      have hEq1 : orient b a c = -orient a b c := orient_swap_left a b c
      have hEq2 : orient b a d = -orient a b d := orient_swap_left a b d
      simpa [hEq1, hEq2] using h5
    have h6' : orient c d b * orient c d a < 0 := by
      simpa [mul_comm] using h6
    exact ⟨hbc, hbd, hac, had, h1', h2', h4, h3, h5', h6'⟩
  · intro h
    rcases h with ⟨hbc, hbd, hac, had, h1, h2, h3, h4, h5, h6⟩
    have h1' : orient a b c ≠ 0 := orient_swap_left_ne (a := b) (b := a) (c := c) h1
    have h2' : orient a b d ≠ 0 := orient_swap_left_ne (a := b) (b := a) (c := d) h2
    have h5' : orient a b c * orient a b d < 0 := by
      have hEq1 : orient a b c = -orient b a c := orient_swap_left b a c
      have hEq2 : orient a b d = -orient b a d := orient_swap_left b a d
      simpa [hEq1, hEq2] using h5
    have h6' : orient c d a * orient c d b < 0 := by
      simpa [mul_comm] using h6
    exact ⟨hac, had, hbc, hbd, h1', h2', h4, h3, h5', h6'⟩

lemma properSegmentIntersect_swap_right (a b c d : Point) :
    properSegmentIntersect a b c d ↔ properSegmentIntersect a b d c := by
  constructor
  · intro h
    rcases h with ⟨hac, had, hbc, hbd, h1, h2, h3, h4, h5, h6⟩
    have h3' : orient d c a ≠ 0 := orient_swap_left_ne (a := c) (b := d) (c := a) h3
    have h4' : orient d c b ≠ 0 := orient_swap_left_ne (a := c) (b := d) (c := b) h4
    have h6' : orient d c a * orient d c b < 0 := by
      have hEq1 : orient d c a = -orient c d a := orient_swap_left c d a
      have hEq2 : orient d c b = -orient c d b := orient_swap_left c d b
      simpa [hEq1, hEq2] using h6
    have h5' : orient a b d * orient a b c < 0 := by
      simpa [mul_comm] using h5
    exact ⟨had, hac, hbd, hbc, h2, h1, h3', h4', h5', h6'⟩
  · intro h
    rcases h with ⟨had, hac, hbd, hbc, h1, h2, h3, h4, h5, h6⟩
    have h3' : orient c d a ≠ 0 := orient_swap_left_ne (a := d) (b := c) (c := a) h3
    have h4' : orient c d b ≠ 0 := orient_swap_left_ne (a := d) (b := c) (c := b) h4
    have h6' : orient c d a * orient c d b < 0 := by
      have hEq1 : orient c d a = -orient d c a := orient_swap_left d c a
      have hEq2 : orient c d b = -orient d c b := orient_swap_left d c b
      simpa [hEq1, hEq2] using h6
    have h5' : orient a b c * orient a b d < 0 := by
      simpa [mul_comm] using h5
    exact ⟨hac, had, hbc, hbd, h2, h1, h3', h4', h5', h6'⟩

def segmentCrosses {n : ℕ} (P : PointSet n) : Segment n → Segment n → Prop :=
  fun s t =>
    Sym2.lift₂
      ⟨fun a b c d => properSegmentIntersect (P a) (P b) (P c) (P d),
        fun a b c d => by
          constructor
          · apply propext
            exact properSegmentIntersect_swap_left _ _ _ _
          · apply propext
            exact properSegmentIntersect_swap_right _ _ _ _⟩
      s.1 t.1

lemma segmentCrosses_symm {n : ℕ} (P : PointSet n) : Symmetric (segmentCrosses P) := by
  intro s t h
  cases' s with s hs
  cases' t with t ht
  have h' :
      Sym2.lift₂
        ⟨fun a b c d => properSegmentIntersect (P a) (P b) (P c) (P d),
          fun a b c d => by
            constructor
            · apply propext
              exact properSegmentIntersect_swap_left _ _ _ _
            · apply propext
              exact properSegmentIntersect_swap_right _ _ _ _⟩
        s t := by
    simpa [segmentCrosses] using h
  have h'' :
      Sym2.lift₂
        ⟨fun a b c d => properSegmentIntersect (P a) (P b) (P c) (P d),
          fun a b c d => by
            constructor
            · apply propext
              exact properSegmentIntersect_swap_left _ _ _ _
            · apply propext
              exact properSegmentIntersect_swap_right _ _ _ _⟩
        t s := by
    refine Sym2.inductionOn₂ s t ?_ h'
    intro a b c d h''
    have hsym : properSegmentIntersect (P c) (P d) (P a) (P b) :=
      (properSegmentIntersect_symm (P a) (P b) (P c) (P d)).1 h''
    simpa using hsym
  simpa [segmentCrosses] using h''


def crossingGraph {n : ℕ} (P : PointSet n) : SimpleGraph (Segment n) where
  Adj := segmentCrosses P
  symm := by
    intro s t h
    exact segmentCrosses_symm P h
  loopless := by
    intro s h
    cases' s with s hs
    have h' :
        Sym2.lift₂
          ⟨fun a b c d => properSegmentIntersect (P a) (P b) (P c) (P d),
            fun a b c d => by
              constructor
              · apply propext
                exact properSegmentIntersect_swap_left _ _ _ _
              · apply propext
                exact properSegmentIntersect_swap_right _ _ _ _⟩
          s s := by
      simpa [segmentCrosses] using h
    revert h'
    refine Sym2.inductionOn s ?_
    intro a b h'
    have h'' : properSegmentIntersect (P a) (P b) (P a) (P b) := by
      simpa using h'
    rcases h'' with ⟨h1, _, _, _, _, _, _, _, _, _⟩
    exact (h1 rfl).elim


def isIndependent {n : ℕ} (G : SimpleGraph (Segment n)) (s : Finset (Segment n)) : Prop :=
  ∀ ⦃u v⦄, u ∈ s → v ∈ s → u ≠ v → ¬ G.Adj u v


noncomputable def planeGraphs {n : ℕ} (P : PointSet n) : Finset (Finset (Segment n)) := by
  classical
  exact (Finset.univ.powerset).filter (fun s => isIndependent (crossingGraph P) s)


noncomputable def pg {n : ℕ} (P : PointSet n) : Nat :=
  (planeGraphs P).card

end PlaneGraphs

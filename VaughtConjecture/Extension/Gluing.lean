/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Bountiful

/-!
# Gluing lawful labellings, and capped lifting across two faces

Roadmap, Layer 3 (the coatom extension construction: the bountifulness of the rows it builds,
[Kni26, Lemma 4.3.2], and the boundary extension shared with row 1 of the table of 3.4) and
Layer 1 (bountifulness); semantic contract, item 3 (bountifulness is a statement about cap balls,
cap by cap, not simultaneous preservation).

Everything here holds for arbitrary semantic rows `R` of an arbitrary cell scheme `D`; no
consistency, bountifulness, or completeness of `R` is assumed unless it is a hypothesis.

* **Lawfulness below a pair, pointwise** (`Rows.isLawfulBelow_iff_forall`): a labelling `w` of
  all cells is lawful below `X` exactly when the order, locality, and availability laws hold at the
  cells below `X`, with the rows of `D` itself.  In particular lawfulness is local, and labellings
  lawful below `U` and below `V` glue to one lawful below any `Y` whose cells are covered by those
  below `U` and `V` (`Rows.IsLawfulBelow.glue`).
* **Lifting within a face** (`Rows.cappedLift_of_fst_eq`): for pairs `X ≤ Y` on the same face,
  any rows lift capped from `X` to `Y`: keep the prescription below `X` and cap the ambient labels
  above it.  This is the case `B = C` of the proof of [Kni26, Lemma 4.3.20].
* **Bountifulness at a fixed grade** (`Rows.isBountiful_iff_forall_cappedLift_fst`): rows are
  bountiful exactly when they lift capped from every graded face `X` to `(C, grade of X)`, for every
  graded face `(C, j)` above `X`.
* **The boundary lift** (`Rows.cappedLift_of_union`): if the cells below `Y` are those below `U`
  or below `V`, and those below both lie below `O`, then capped lifts from `I` to `U` and from `O`
  to `V` compose to a capped lift from `I` to `Y`: lift in `U`, then lift its trace on `O` in `V`,
  and glue.  No lift at `Y` itself is assumed.
* **Coatoms and the full face** (`Rows.isBountiful_of_coatoms`): on a ground set `A` whose faces
  other than `A` lie in one of the two coatoms `A \ {a}`, `A \ {b}`, rows that lift capped below
  the proper faces and from each coatom to the full face at every grade are bountiful.  When no
  cell has scope `A`, the lifts to the full face are boundary lifts
  (`Rows.cappedLift_coatom_full`), which is [Kni26, Lemma 4.3.2]: the union of the semantics of two
  bountiful coatom domains is bountiful (`Rows.isBountiful_of_coatoms_of_scope_ne`).

## Placement

`Rows.isLawfulBelow_iff_forall` and `Rows.IsLawfulBelow.glue` belong in
`VaughtConjecture.Scheme.Row`, after the lawful sections, and `Label.transformsTo_comp_equiv_iff`
in `VaughtConjecture.Label.Transform`, beside `TransformsTo.reindex`; the lifting statements belong
in `VaughtConjecture.Scheme.Bountiful`, after `CellScheme.Rows.CappedLift.trans`.  They are stated
here so that those files are unchanged.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the union of the semantics of two domains on the
coatoms `A \ {a}` and `A \ {b}` is consistent and bountiful by [Kni26, Lemma 4.3.2], and the case
`B = C` is in the proof of [Kni26, Lemma 4.3.20], for R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

namespace VaughtConjecture

open Finset Label

/-- A transformation relation is unchanged by reindexing its cells along an equivalence. -/
theorem Label.transformsTo_comp_equiv_iff {D D' : Type*} (e : D' ≃ D) {grade : D → ℕ}
    {p q : D → Label.{u}} :
    TransformsTo (grade ∘ e) (p ∘ e) (q ∘ e) ↔ TransformsTo grade p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex e⟩
  have h' := h.reindex e.symm
  simpa only [Function.comp_assoc, e.self_comp_symm, Function.comp_id] using h'

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-! ### Lawfulness below a pair, pointwise -/

/-- A cell below a cell below `X` is below `X`. -/
private theorem mem_below_of_le {X : Finset α × ℕ} {d s : ι}
    (hd : D.gradedIndex d ≤ D.gradedIndex s) (hs : s ∈ D.below X) : d ∈ D.below X :=
  (le_trans hd hs : D.gradedIndex d ≤ X)

/-- A cell whose scope lies in that of a cell below `X`, at the same grade, is below `X`. -/
private theorem mem_below_of_scope_subset {X : Finset α × ℕ} {s t : ι}
    (hst : D.scope s ⊆ D.scope t) (hg : D.grade s = D.grade t) (ht : t ∈ D.below X) :
    s ∈ D.below X :=
  mem_below_of_le ((D.gradedIndex_le_iff).mpr ⟨hst, hg.le⟩) ht

/-- **Lawfulness below a pair, pointwise.**  A labelling `w` of all cells is lawful below `X`
exactly when every cell below `X` has a label self-visible at its grade, the row of every cell
`s` below `X` transforms to `d ↦ min (w d) (w s)` on the cells below `s`, and availability holds
for every target cell below `X`. -/
theorem isLawfulBelow_iff_forall {X : Finset α × ℕ} {w : ι → Label.{u}} :
    R.IsLawfulBelow X (fun d ↦ w d) ↔
      (∀ d ∈ D.below X, IsSelfVisible (D.grade d) (w d)) ∧
      (∀ s ∈ D.below X, TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (w d) (w s))) ∧
      (∀ s t, t ∈ D.below X → D.scope s ⊆ D.scope t → D.grade s = D.grade t →
        ∃ u, D.gradedIndex u = D.gradedIndex t ∧ w s ≤ w u) := by
  constructor
  · intro h
    refine ⟨fun d hd ↦ h.orderly ⟨d, hd⟩, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · exact (h.locality ⟨s, hs⟩).reindex fun d : D.below (D.gradedIndex s) ↦
        ⟨⟨d.1, mem_below_of_le d.2 hs⟩, d.2⟩
    · obtain ⟨u, hu, hle⟩ :=
        h.availability ⟨s, mem_below_of_scope_subset hst hg ht⟩ ⟨t, ht⟩ hst hg
      exact ⟨u, hu, hle⟩
  · rintro ⟨ho, hl, ha⟩
    refine ⟨fun d ↦ ho d d.2, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
    · exact (hl s s.2).reindex (D' := (D.reindex ((↑) : D.below X → ι)).below
        ((D.reindex ((↑) : D.below X → ι)).gradedIndex s)) fun t ↦ ⟨t.1.1, t.2⟩
    · obtain ⟨u, hu, hle⟩ := ha s t t.2 hst hg
      exact ⟨⟨u, mem_below_of_le hu.le t.2⟩, hu, hle⟩

/-- **Gluing lawful labellings.**  If a labelling of all cells is lawful below `U` and below `V`,
it is lawful below every pair `Y` whose cells lie below `U` or below `V`. -/
theorem IsLawfulBelow.glue {U V Y : Finset α × ℕ} {w : ι → Label.{u}}
    (hU : R.IsLawfulBelow U (fun d ↦ w d)) (hV : R.IsLawfulBelow V (fun d ↦ w d))
    (hY : ∀ d ∈ D.below Y, d ∈ D.below U ∨ d ∈ D.below V) :
    R.IsLawfulBelow Y (fun d ↦ w d) := by
  obtain ⟨hoU, hlU, haU⟩ := isLawfulBelow_iff_forall.mp hU
  obtain ⟨hoV, hlV, haV⟩ := isLawfulBelow_iff_forall.mp hV
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht ↦ ?_⟩
  · exact (hY d hd).elim (hoU d) (hoV d)
  · exact (hY s hs).elim (hlU s) (hlV s)
  · exact (hY t ht).elim (haU s t) (haV s t)

/-! ### Extension by bottom -/

open Classical in
/-- The extension by bottom of a labelling of the cells below `X` to all cells. -/
noncomputable def extendBot (X : Finset α × ℕ) (q : D.below X → Label.{u}) (d : ι) :
    Label.{u} :=
  if h : d ∈ D.below X then q ⟨d, h⟩ else ⊥

/-- The extension by bottom agrees with the labelling below `X`. -/
theorem extendBot_of_mem {X : Finset α × ℕ} (q : D.below X → Label.{u}) {d : ι}
    (h : d ∈ D.below X) : extendBot X q d = q ⟨d, h⟩ := dite_eq_left h

/-- Restricting the extension by bottom back to the cells below `X` recovers the labelling. -/
theorem restrict_extendBot {X : Finset α × ℕ} (q : D.below X → Label.{u}) :
    (fun d : D.below X ↦ extendBot X q d) = q :=
  funext fun d ↦ extendBot_of_mem q d.2

/-! ### Lifting within a face -/

variable {X Y I U V O : Finset α × ℕ}

/-- **Lifting within a face.**  For pairs `X ≤ Y` on the same face, any rows lift capped from `X`
to `Y`: keep the prescription below `X` and cap the ambient labels at every other cell. -/
theorem cappedLift_of_fst_eq (h : X ≤ Y) (hXY : X.1 = Y.1) : R.CappedLift h := by
  classical
  refine (cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  -- Below `X` keep `p`; above it, cap `q` at `c`.
  let w : ι → Label.{u} := fun d ↦
    if hd : d ∈ D.below X then p ⟨d, hd⟩ else min (extendBot Y q d) c
  have hwX (d : ι) (hd : d ∈ D.below X) : w d = p ⟨d, hd⟩ := dite_eq_left hd
  have hwY (d : ι) (hd : d ∈ D.below Y) (hdX : d ∉ D.below X) : w d = min (q ⟨d, hd⟩) c := by
    simp only [w, dite_eq_right hdX, extendBot_of_mem q hd]
  -- A cell below `Y` and not below `X` has grade above that of `X`.
  have hgrade (d : ι) (hd : d ∈ D.below Y) (hdX : d ∉ D.below X) : X.2 < D.grade d := by
    by_contra hle
    exact hdX ⟨hXY ▸ hd.1, not_lt.mp hle⟩
  -- Capped observations agree with those of `q` at every cell below `Y`.
  have hcap (d : ι) (hd : d ∈ D.below Y) : min (w d) c = min (q ⟨d, hd⟩) c := by
    by_cases hdX : d ∈ D.below X
    · rw [hwX d hdX, ← hpq ⟨d, hdX⟩]
    · rw [hwY d hd hdX, min_assoc, min_self]
  obtain ⟨hoq, hlq, haq⟩ := isLawfulBelow_iff_forall.mp
    (show R.IsLawfulBelow Y (fun d ↦ extendBot Y q d) by rwa [restrict_extendBot])
  obtain ⟨hop, hlp, hap⟩ := isLawfulBelow_iff_forall.mp
    (show R.IsLawfulBelow X (fun d ↦ extendBot X p d) by rwa [restrict_extendBot])
  have hl : R.IsLawfulBelow Y (fun d ↦ w d) := by
    refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · by_cases hdX : d ∈ D.below X
      · rw [hwX d hdX, ← extendBot_of_mem p hdX]
        exact hop d hdX
      · rw [hwY d hd hdX, ← extendBot_of_mem q hd]
        exact (hoq d hd).min (hc.mono hd.2)
    · by_cases hsX : s ∈ D.below X
      · -- Every cell below `s` lies below `X`, where `w` is `p`.
        have he : (fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s)) =
            fun d : D.below (D.gradedIndex s) ↦ min (extendBot X p d.1) (extendBot X p s) := by
          funext d
          have hdX : d.1 ∈ D.below X := mem_below_of_le d.2 hsX
          rw [hwX _ hdX, hwX _ hsX, extendBot_of_mem p hdX, extendBot_of_mem p hsX]
        rw [he]
        exact hlp s hsX
      · -- Above `X`, the target is the ambient target capped at `c`.
        have he : (fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s)) =
            fun d : D.below (D.gradedIndex s) ↦
              min (min (extendBot Y q d.1) (extendBot Y q s)) c := by
          funext d
          have hdY : d.1 ∈ D.below Y := mem_below_of_le d.2 hs
          rw [hwY s hs hsX, extendBot_of_mem q hdY, extendBot_of_mem q hs,
            show min (w d) (min (q ⟨s, hs⟩) c) = min (min (w d) c) (q ⟨s, hs⟩) by ac_rfl,
            hcap d.1 hdY]
          ac_rfl
        rw [he]
        exact (hlq s hs).min_const (fun d ↦ d.2.2) (hc.mono hs.2)
    · by_cases htX : t ∈ D.below X
      · obtain ⟨u, hu, hle⟩ := hap s t htX hst hg
        have hsX : s ∈ D.below X := mem_below_of_scope_subset hst hg htX
        have huX : u ∈ D.below X := mem_below_of_le hu.le htX
        refine ⟨u, hu, ?_⟩
        rwa [hwX s hsX, hwX u huX, ← extendBot_of_mem p hsX, ← extendBot_of_mem p huX]
      · have hsY : s ∈ D.below Y := mem_below_of_scope_subset hst hg ht
        have hsX : s ∉ D.below X := fun hsX ↦ (hgrade t ht htX).not_ge (hg ▸ hsX.2)
        obtain ⟨u, hu, hle⟩ := haq s t ht hst hg
        have huY : u ∈ D.below Y := mem_below_of_le hu.le ht
        have huX : u ∉ D.below X := fun huX ↦ htX (mem_below_of_le hu.ge huX)
        refine ⟨u, hu, ?_⟩
        rw [hwY s hsY hsX, hwY u huY huX]
        rw [extendBot_of_mem q hsY, extendBot_of_mem q huY] at hle
        exact min_le_min_right c hle
  refine ⟨fun d ↦ w d, hl, fun d ↦ hcap d d.2, fun d ↦ ?_⟩
  exact hwX _ d.2

/-! ### Bountifulness at a fixed grade -/

/-- **Bountifulness at a fixed grade.**  Rows are bountiful exactly when, for all graded faces
`X ≤ Y`, they lift capped from `X` to the pair `(Y.1, X.2)` on the face of `Y` at the grade of
`X`.  The remaining lift, from `(Y.1, X.2)` to `Y`, is within a face. -/
theorem isBountiful_iff_forall_cappedLift_fst :
    R.IsBountiful ↔ ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, R.CappedLift (X := X) (Y := (Y.1, X.2)) ⟨h.1, le_rfl⟩ := by
  refine ⟨fun hR X Y hX hY h ↦
    hR (Y := (Y.1, X.2)) hX ⟨hY.1, hX.2.1, h.2.trans hY.2.2⟩ ⟨h.1, le_rfl⟩, fun hR ↦ ?_⟩
  intro X Y hX hY h
  exact (hR hX hY h).trans (cappedLift_of_fst_eq (X := (Y.1, X.2)) (Y := Y) ⟨Subset.rfl, h.2⟩ rfl)

/-! ### The boundary lift -/

/-- **The boundary lift.**  Let the cells below `Y` be those below `U` or below `V`, and let the
cells below both `U` and `V` lie below `O ≤ U, V`.  Capped lifts from `I` to `U` and from `O` to
`V` give a capped lift from `I` to `Y`: lift the prescription in `U`, lift its trace on `O` in
`V`, and glue the two.  Every ambient observation at the cap is preserved. -/
theorem cappedLift_of_union (hIU : I ≤ U) (hOU : O ≤ U) (hOV : O ≤ V) (hUY : U ≤ Y)
    (hVY : V ≤ Y) (hcover : ∀ d ∈ D.below Y, d ∈ D.below U ∨ d ∈ D.below V)
    (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hIU) (hright : R.CappedLift hOV) : R.CappedLift (hIU.trans hUY) := by
  classical
  refine (cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  -- Lift the prescription within `U`.
  obtain ⟨u, hu, hucap, hup⟩ := (cappedLift_iff_forall_exists hIU).mp hleft c (hc.mono hUY.2) p
    (q ∘ Set.inclusion (D.below_mono hUY)) hp (hq.mono hUY) hpq
  -- Lift the trace of that lift on `O` within `V`.
  obtain ⟨v, hv, hvcap, hvo⟩ := (cappedLift_iff_forall_exists hOV).mp hright c (hc.mono hVY.2)
    (u ∘ Set.inclusion (D.below_mono hOU)) (q ∘ Set.inclusion (D.below_mono hVY))
    (hu.mono hOU) (hq.mono hVY) fun d ↦ (hucap (Set.inclusion (D.below_mono hOU) d)).symm
  -- Glue: below `U` read `u`, elsewhere read `v`.
  let w : ι → Label.{u} := fun d ↦ if hd : d ∈ D.below U then u ⟨d, hd⟩ else extendBot V v d
  have hwU (d : ι) (hd : d ∈ D.below U) : w d = u ⟨d, hd⟩ := dite_eq_left hd
  have hwV (d : ι) (hd : d ∈ D.below V) : w d = v ⟨d, hd⟩ := by
    by_cases hdU : d ∈ D.below U
    · rw [hwU d hdU]
      exact (hvo ⟨d, hinter d hdU hd⟩).symm
    · simp only [w, dite_eq_right hdU, extendBot_of_mem v hd]
  have hlU : R.IsLawfulBelow U (fun d ↦ w d) := by
    convert hu using 1
    exact funext fun d ↦ hwU d d.2
  have hlV : R.IsLawfulBelow V (fun d ↦ w d) := by
    convert hv using 1
    exact funext fun d ↦ hwV d d.2
  refine ⟨fun d ↦ w d, IsLawfulBelow.glue hlU hlV hcover, fun d ↦ ?_, fun d ↦ ?_⟩
  · rcases hcover d d.2 with hd | hd
    · change min (w d.1) c = _
      rw [hwU d hd]
      exact hucap ⟨d, hd⟩
    · change min (w d.1) c = _
      rw [hwV d hd]
      exact hvcap ⟨d, hd⟩
  · change w d.1 = p d
    rw [hwU d.1 (D.below_mono hIU d.2)]
    exact hup d

/-! ### Coatoms and the full face -/

section Coatoms

variable [DecidableEq α] {A : Finset α} {a b : α}

/-- **Lifting from a coatom to the full face**, when no cell has the full scope.  On a
well-formed scheme whose faces other than `A` lie in `A \ {a}` or `A \ {b}`, rows lifting capped
below the proper faces lift capped from `(A \ {a}, j)` to `(A, j)` for every grade `j` at most the
size of `A \ {a}`.  This is the boundary lift through the coatom `A \ {b}`. -/
theorem cappedLift_coatom_full (hD : D.IsWellFormed) (ha : a ∈ A) (hb : b ∈ A)
    (hfaces : ∀ B ∈ D.faces, B ≠ A → B ⊆ A.erase a ∨ B ⊆ A.erase b)
    (hbF : A.erase b ∈ D.faces) (habF : (A.erase a).erase b ∈ D.faces)
    (hproper : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, Y.1 ≠ A → R.CappedLift h)
    (hscope : ∀ d, D.scope d ≠ A) {j : ℕ} (hj : j ≤ #(A.erase a)) :
    R.CappedLift (X := (A.erase a, j)) (Y := (A, j)) ⟨erase_subset a A, le_rfl⟩ := by
  set C := (A.erase a).erase b
  have hCa : C ⊆ A.erase a := erase_subset _ _
  have hCb : C ⊆ A.erase b := erase_subset_erase b (erase_subset a A)
  have hOU : (C, min j #C) ≤ (A.erase a, j) := ⟨hCa, min_le_left _ _⟩
  have hOV : (C, min j #C) ≤ (A.erase b, j) := ⟨hCb, min_le_left _ _⟩
  have hjb : j ≤ #(A.erase b) := by
    rwa [card_erase_of_mem hb, ← card_erase_of_mem ha]
  refine cappedLift_of_union (I := (A.erase a, j)) (U := (A.erase a, j)) (V := (A.erase b, j))
    (O := (C, min j #C)) (Y := (A, j)) le_rfl hOU hOV ⟨erase_subset a A, le_rfl⟩
    ⟨erase_subset b A, le_rfl⟩ ?_ ?_ (cappedLift_refl _) ?_
  · intro d hd
    have hs : D.scope d ⊆ A.erase a ∨ D.scope d ⊆ A.erase b :=
      hfaces _ (hD.scope_mem d) (hscope d)
    exact hs.imp (fun h ↦ ⟨h, hd.2⟩) (fun h ↦ ⟨h, hd.2⟩)
  · intro d hdU hdV
    have hsC : D.scope d ⊆ C := fun x hx ↦ mem_erase.mpr
      ⟨(mem_erase.mp (hdV.1 hx)).1, hdU.1 hx⟩
    exact ⟨hsC, le_min hdU.2 ((hD.grade_le_card d).trans (card_le_card hsC))⟩
  · by_cases h0 : min j #C = 0
    · exact hD.cappedLift R (Or.inl h0) hOV
    · refine hproper ⟨habF, Nat.pos_of_ne_zero h0, min_le_right _ _⟩
        ⟨hbF, (Nat.pos_of_ne_zero h0).trans_le (min_le_left _ _), hjb⟩ hOV fun he ↦ ?_
      exact notMem_erase b A (show b ∈ A.erase b by rw [show A.erase b = A from he]; exact hb)

/-- **Bountifulness from the coatoms.**  On a scheme whose faces other than `A` lie in
`A \ {a}` or `A \ {b}`, rows are bountiful if they lift capped between graded faces with a proper
face on top, and from each coatom to the full face at every grade at most the size of the
coatom. -/
theorem isBountiful_of_coatoms (ha : a ∈ A) (hb : b ∈ A)
    (hfaces : ∀ B ∈ D.faces, B ≠ A → B ⊆ A.erase a ∨ B ⊆ A.erase b)
    (haF : A.erase a ∈ D.faces) (hbF : A.erase b ∈ D.faces)
    (hproper : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, Y.1 ≠ A → R.CappedLift h)
    (hfulla : ∀ j ≤ #(A.erase a), R.CappedLift (X := (A.erase a, j)) (Y := (A, j))
      ⟨erase_subset a A, le_rfl⟩)
    (hfullb : ∀ j ≤ #(A.erase b), R.CappedLift (X := (A.erase b, j)) (Y := (A, j))
      ⟨erase_subset b A, le_rfl⟩) :
    R.IsBountiful := by
  refine isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  obtain ⟨B, k⟩ := Y
  by_cases hYA : B = A
  · subst hYA
    by_cases hXA : X.1 = B
    · exact cappedLift_of_fst_eq _ hXA
    -- Pass through the coatom containing the face of `X`.
    rcases hfaces _ hX.1 hXA with hXa | hXb
    · have hj : X.2 ≤ #(B.erase a) := hX.2.2.trans (card_le_card hXa)
      refine (hproper (Y := (B.erase a, X.2)) hX ⟨haF, hX.2.1, hj⟩ ⟨hXa, le_rfl⟩
        fun he ↦ ?_).trans (hfulla X.2 hj)
      exact notMem_erase a B (show a ∈ B.erase a by rw [show B.erase a = B from he]; exact ha)
    · have hj : X.2 ≤ #(B.erase b) := hX.2.2.trans (card_le_card hXb)
      refine (hproper (Y := (B.erase b, X.2)) hX ⟨hbF, hX.2.1, hj⟩ ⟨hXb, le_rfl⟩
        fun he ↦ ?_).trans (hfullb X.2 hj)
      exact notMem_erase b B (show b ∈ B.erase b by rw [show B.erase b = B from he]; exact hb)
  · exact hproper (Y := (B, X.2)) hX ⟨hY.1, hX.2.1, h.2.trans hY.2.2⟩ _ hYA

/-- **The union of two bountiful coatom semantics is bountiful** [Kni26, Lemma 4.3.2].  On a
well-formed scheme on `A` whose faces other than `A` lie in `A \ {a}` or `A \ {b}`, and in which no
cell has the full scope, rows that lift capped between graded faces with a proper face on top are
bountiful: the lifts to the full face are boundary lifts. -/
theorem isBountiful_of_coatoms_of_scope_ne (hD : D.IsWellFormed) (ha : a ∈ A) (hb : b ∈ A)
    (hfaces : ∀ B ∈ D.faces, B ≠ A → B ⊆ A.erase a ∨ B ⊆ A.erase b)
    (haF : A.erase a ∈ D.faces) (hbF : A.erase b ∈ D.faces) (habF : (A.erase a).erase b ∈ D.faces)
    (hproper : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, Y.1 ≠ A → R.CappedLift h)
    (hscope : ∀ d, D.scope d ≠ A) : R.IsBountiful := by
  have hfaces' : ∀ B ∈ D.faces, B ≠ A → B ⊆ A.erase b ∨ B ⊆ A.erase a :=
    fun B hB hBA ↦ (hfaces B hB hBA).symm
  have hbaF : (A.erase b).erase a ∈ D.faces := by rwa [erase_right_comm]
  exact isBountiful_of_coatoms ha hb hfaces haF hbF hproper
    (fun _ hj ↦ cappedLift_coatom_full hD ha hb hfaces hbF habF hproper hscope hj)
    (fun _ hj ↦ cappedLift_coatom_full hD hb ha hfaces' haF hbaF hproper hscope hj)

end Coatoms

end CellScheme.Rows

end VaughtConjecture

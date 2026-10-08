/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapTopReading
import VaughtConjecture.Extension.PinnedExtension

/-!
# Top-reading pinned extensions from the coatom step

Roadmap, Layer 3 ((R2) of the table of 3.4, row 6, the exact pinned extension); the top-reading
pinned extensions of `VaughtConjecture.Continuation.SourceGapTopReading`.

The root of a source-gap context `t'` misses the lost point, so it lies in a closed **coatom** of
`t'`, a closed face missing exactly one point (`StageType.exists_coatom_of_ne_univ`, from the
accessibility of plans).  The exact pinned extension carries the donor `d` from the root to the
coatom (`StageType.exists_pinned_extension`, under the coatom extension property): it gives a
legal one-point coface `d'` of the coatom whose face along the root followed by the new point is
`d`.  What remains is **one coatom step**: a legal one-point coface `D'` of `t'` with face `d'`
along the coatom followed by the new point, reading the new tops of `d` at the tops.

**The coatom step** (`StageType.HasTopReadingCoatomSteps α`; defined, open).  For every legal
source-gap context `t'` of grade `K` along `h`, every closed coatom `f` of `t'` and `g` with
`g.trans f = h`, every legal one-point coface `d'` of the face of `t'` along `f`, and every face
`d` of `d'` along `g` followed by the new point of top grade at most `K`, one legal one-point
coface `D'` of `t'` has face `d'` along `f` followed by the new point and reads each new top of `d`
along `h` at its tops (`StageType.ReadsEachNewTopAtTops`).  The donor `d'` of the step is
arbitrary: it is the output of the exact pinned extension; the reading is asked only for the new
tops of `d`.  Compiled instances: the coatom `Fin.castSuccEmb` with the donor `d' = t'`, at every
arity (`StageType.exists_coatomStep_self_succ`,
`VaughtConjecture.Continuation.SourceGapDoubledTower`); donors other than `t'` are open.

**The reduction** (`StageType.hasTopReadingPinnedExtensions_of_coatomSteps`, compiled in this
repository): the coatom extension property and the coatom step at stage `α` give the top-reading
pinned extension property at `α`.  So, for (R2), the roots smaller than a coatom reduce to the
coatom step, with the coatom extension property for the inner extensions.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **A closed face other than the whole set lies in a closed coatom.** -/
theorem exists_coatom_of_ne_univ (t : StageType.{u} α (k + 1)) {B : Finset (Fin (k + 1))}
    (hB : B ∈ t.toCellScheme.faces) (hne : B ≠ univ) :
    ∃ C ∈ t.toCellScheme.faces, B ⊆ C ∧ #C = k := by
  have hplan := t.isPlan
  induction hm : k - #B using Nat.strong_induction_on generalizing B with
  | _ m ih =>
    have hBk : #B ≤ k := by
      have := card_lt_card (ssubset_univ_iff.mpr hne)
      simpa using this
    by_cases hBc : #B = k
    · exact ⟨B, hB, Subset.rfl, hBc⟩
    obtain ⟨x, hx, hxB⟩ := hplan.exists_insert_mem hB hne
    have hcard : #(insert x B) = #B + 1 := card_insert_of_notMem hx
    have hne' : insert x B ≠ univ := by
      intro he
      have := congrArg card he
      rw [hcard, card_univ, Fintype.card_fin] at this
      omega
    obtain ⟨C, hC, hBC, hCk⟩ := ih (k - #(insert x B)) (by omega) hxB hne' rfl
    exact ⟨C, hC, (subset_insert x B).trans hBC, hCk⟩

variable (α) in
/-- The **top-reading coatom step** at stage `α`.  Defined; open. -/
def HasTopReadingCoatomSteps : Prop :=
  ∀ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (h : Fin n ↪ Fin (k + 1)) (l : Fin (k + 1))
    (o r : Fin t'.card), t'.IsLegal → t'.IsSourceGapContextAt K h l o r →
    ∀ (f : Fin k ↪ Fin (k + 1)) (g : Fin n ↪ Fin k), g.trans f = h →
    ∀ p : StageType.{u} α k, restrictFace f t' = some p → ∀ d' ∈ p.cofaces,
    ∀ d : StageType.{u} α (n + 1), restrictFace (extendByLast g) d' = some d → d.topGrade ≤ K →
      ∃ (D' : StageType.{u} α (k + 2)) (hD' : D' ∈ t'.cofaces),
        restrictFace (extendByLast f) D' = some d' ∧ ReadsEachNewTopAtTops hD'.2 h

/-- **Top-reading pinned extensions from the coatom step**: under the coatom extension property,
the top-reading coatom step gives the top-reading pinned extension property.  The root lies in a
closed coatom (`exists_coatom_of_ne_univ`); the exact pinned extension carries the donor to the
coatom (`exists_pinned_extension`); the coatom step gives the coface. -/
theorem hasTopReadingPinnedExtensions_of_coatomSteps (hext : HasCoatomExtensions.{u} α)
    (hstep : HasTopReadingCoatomSteps α) : HasTopReadingPinnedExtensions α := by
  intro K n k t' h l o r ht' hs t ht d hd hdK
  obtain _ | k := k
  · exact l.elim0
  -- the root is a closed face other than the whole set
  have hhF : univ.map h ∈ t'.toCellScheme.faces := ((restrictFace_eq_some_iff t' h).mp ht).1
  have hhne : univ.map h ≠ univ := fun he ↦ hs.notMem_range (by
    have hl : l ∈ univ.map h := he ▸ mem_univ l
    obtain ⟨i, -, hi⟩ := mem_map.mp hl
    exact ⟨i, hi⟩)
  obtain ⟨C, hC, hhC, hCk⟩ := t'.exists_coatom_of_ne_univ hhF hhne
  -- the coatom, enumerated
  set f : Fin k ↪ Fin (k + 1) := (C.orderEmbOfFin hCk).toEmbedding
  have hfC : univ.map f = C := by
    ext y
    simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact C.orderEmbOfFin_mem hCk i
    · intro hy
      have : y ∈ Set.range (C.orderEmbOfFin hCk) := by
        rw [Finset.range_orderEmbOfFin]
        exact hy
      exact this
  have hfF : univ.map f ∈ t'.toCellScheme.faces := hfC ▸ hC
  set p := t'.comap f hfF
  have hp : restrictFace f t' = some p := restrictFace_of_mem _ _ hfF
  -- the root through the coatom
  obtain ⟨g, hg⟩ := Function.Embedding.exists_trans_eq (e := f) (g := h) fun i ↦ by
    have : h i ∈ C := hhC (mem_map_of_mem _ (mem_univ i))
    rw [← hfC] at this
    obtain ⟨j, -, hj⟩ := mem_map.mp this
    exact ⟨j, hj⟩
  have hpg : restrictFace g p = some t := by
    rw [restrictFace_trans t' f g hp, hg, ht]
  -- the exact pinned extension carries `d` to the coatom
  obtain ⟨d', hd', hd'p, hd'd⟩ :=
    exists_pinned_extension hext (ht'.restrictFace f hp) hpg hd.1 hd.2
  obtain ⟨D', hD', hD'd', hrd⟩ := hstep t' h l o r ht' hs f g hg p hp d' ⟨hd', hd'p⟩ d hd'd hdK
  refine ⟨D', hD', ?_, hrd⟩
  -- the face along the root followed by the new point, through the coatom
  rw [← hg, ← extendByLast_trans, ← restrictFace_trans D' _ _ hD'd', hd'd]

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.LadderBase
import VaughtConjecture.Extension.LowerRestriction
import VaughtConjecture.Extension.Seed

/-!
# The attachment of a donor to a context, inside a seed

Roadmap, Layer 3 ((R3) and (R4), the base of the replicated carrier).

For a seed `I` and a root `g` of the context inside its first coatom, the **attachment**
(`Seed.attachment I g`) is the restriction of the amalgam to its cells whose scope lies in the
context face or in the donor face (the root followed by the new point): the cells of the context
and the new cells of the donor, with the plan of the amalgam.  Its mixed faces carry no cell; they
receive the copies of the cells of full scope in the replicated carrier.

* It is well formed, coded and consistent, and no cell has full scope
  (`Seed.isWellFormed_attachment`, `Seed.isCoded_attachment`, `Seed.isConsistent_attachment`,
  `Seed.noFullOne_attachment`).
* Its faces along the context and along the donor face are those of the amalgam, literally
  (`Seed.comap_left_attachment`, `Seed.comap_donor_attachment`).

## References

The amalgam is [Kni26, Definition 4.3.1].
-/

universe u

namespace VaughtConjecture

open Finset

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

open Classical in
/-- The cells of the amalgam whose scope lies in the context face or in the donor face. -/
noncomputable def attachmentCells : Finset (Fin I.amalgam.card) :=
  univ.filter fun c ↦
    I.amalgam.toCellScheme.scope c ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      I.amalgam.toCellScheme.scope c ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))

theorem mem_attachmentCells {c : Fin I.amalgam.card} :
    c ∈ I.attachmentCells g ↔
      I.amalgam.toCellScheme.scope c ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        I.amalgam.toCellScheme.scope c ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
  classical
  simp only [attachmentCells, mem_filter, mem_univ, true_and]

theorem attachmentCells_lower (c : Fin I.amalgam.card) (hc : c ∈ I.attachmentCells g)
    (d : Fin I.amalgam.card)
    (hd : I.amalgam.toCellScheme.gradedIndex d ≤ I.amalgam.toCellScheme.gradedIndex c) :
    d ∈ I.attachmentCells g := by
  rw [mem_attachmentCells] at hc ⊢
  exact hc.imp (fun h ↦ hd.1.trans h) fun h ↦ hd.1.trans h

/-- **The attachment**: the amalgam restricted to its cells whose scope lies in the context face
or in the donor face. -/
noncomputable abbrev attachment : Scheme.{u} (m + 2) :=
  I.amalgam.toScheme.restrictLower (I.attachmentCells g) (I.attachmentCells_lower g)

theorem isWellFormed_attachment : (I.attachment g).IsWellFormed :=
  Scheme.isWellFormed_restrictLower I.amalgam.isWellFormed

theorem isCoded_attachment : (I.attachment g).IsCoded :=
  Scheme.isCoded_restrictLower I.amalgam.isCoded

theorem isConsistent_attachment : (I.attachment g).rows.IsConsistent :=
  Scheme.isConsistent_restrictLower I.isConsistent

/-- **No cell of the attachment has full scope.** -/
theorem noFullOne_attachment : (I.attachment g).NoFullOne := fun _ h ↦
  I.scope_ne_univ _ (univ_subset_iff.mp h.1)

/-- The face of the attachment along a proper face whose visible cells are attachment cells is
that of the amalgam. -/
theorem comap_attachment {k : ℕ} (f : Fin k ↪ Fin (m + 2))
    (hf : ∀ c : Fin I.amalgam.card,
      (I.amalgam.toCellScheme.scope c : Set (Fin (m + 2))) ⊆ Set.range f →
        c ∈ I.attachmentCells g) :
    (I.attachment g).comap f = I.amalgam.toScheme.comap f :=
  (Scheme.comap_eq_of_strictMono f (S := I.attachment g) (T := I.amalgam.toScheme)
    (φ := I.amalgam.toScheme.lowerEmb (I.attachmentCells g))
    (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)).strictMono
    (Scheme.isLowerEmbedding_lowerEmb _ _ (I.attachmentCells_lower g)) (fun _ ↦ rfl) rfl rfl rfl
    fun z hz ↦ by
      have hzL := hf z hz
      have h := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hzL)
      exact h).symm

/-- **The context face of the attachment is that of the amalgam.** -/
theorem comap_left_attachment :
    (I.attachment g).comap Fin.castSuccEmb = I.amalgam.toScheme.comap Fin.castSuccEmb :=
  I.comap_attachment g _ fun c hc ↦ (I.mem_attachmentCells g).mpr (.inl fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hc (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))

/-- **The donor face of the attachment is that of the amalgam.** -/
theorem comap_donor_attachment :
    (I.attachment g).comap (extendByLast (g.trans Fin.castSuccEmb)) =
      I.amalgam.toScheme.comap (extendByLast (g.trans Fin.castSuccEmb)) :=
  I.comap_attachment g _ fun c hc ↦ (I.mem_attachmentCells g).mpr (.inr fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hc (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))

end Seed

end VaughtConjecture

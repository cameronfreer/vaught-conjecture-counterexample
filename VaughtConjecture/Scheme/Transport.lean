/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Bountiful

/-!
# Transport of bountifulness

Roadmap, Layer 1 (bountifulness; restriction, transport, and pullback); semantic contract, item 3
(capping is not stage reduction, and capped vectors need not be lawful: bountifulness is
transported cap by cap, through lawful labellings, never by transporting a capped observation as
a lawful labelling); the expositions, §2.

Bountifulness (`CellScheme.Rows.IsBountiful`) passes to the rows pulled back along a lower
embedding `φ` of `E` into `D`, provided the graded faces of `E` are sent to graded faces of `D` by
a map of faces `g`, monotone on the faces of `E` (grades unchanged), under which `φ` maps the
cells below each graded face `X` of `E` onto the cells below its image
(`IsBountiful.comap_of_image_eq`).  The cells below `X` and below its image are then identified
by an equivalence (`IsLowerEmbedding.belowEquiv`, in `VaughtConjecture.Scheme.Cell`) that is a
lower embedding of the schemes of cells below them in both directions, so lawfulness below `X` is
lawfulness below the image (`Rows.isLawfulBelow_comap_iff`, in `VaughtConjecture.Scheme.Row`) and
cap balls correspond.

Instances:

* the pullback along an embedding `f : β ↪ α` of ground sets (`IsBountiful.comap`), with the
  faces `(C, j) ↦ (f '' C, j)` (`Prod.map (Finset.map f) id`): the graded faces of `D.comap f` are
  those whose image is a graded face of `D` (`mem_gradedFaces_comap`), and the cells below a pair
  in the pullback are the cells below its image (`image_val_below_comap`).  No well-formedness of
  the pullback is needed;
* reindexing along an equivalence of cells (`IsBountiful.reindex`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the restriction of a semantics to a face of the plan
is [Kni26, Lemma 2.5.5], and its transport along a one-to-one map is clause 5 of
[Kni26, Proposition 2.6.3].
-/

universe u

namespace VaughtConjecture.CellScheme

open Finset

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β} {φ : κ → ι}

namespace Rows

variable {R : D.Rows.{u}}

/-! ### Transport of bountifulness -/

/-- **Transport of bountifulness.**  Let `φ` be a lower embedding of `E` into `D` and `g` a
map of faces, monotone on the faces of `E`, such that, for every graded face `X = (C, j)` of
`E`, the pair `(g C, j)` is a graded face of `D` and `φ` maps the cells below `X` onto the cells
below `(g C, j)`.  Then the pullback of bountiful rows along `φ` is bountiful. -/
theorem IsBountiful.comap_of_image_eq (hR : R.IsBountiful) (hφ : E.IsLowerEmbedding D φ)
    {g : Finset β → Finset α} (hg : MonotoneOn g E.faces)
    (hfaces : ∀ X ∈ E.gradedFaces, Prod.map g id X ∈ D.gradedFaces)
    (himage : ∀ X ∈ E.gradedFaces, φ '' E.below X = D.below (Prod.map g id X)) :
    (R.comap hφ).IsBountiful := by
  intro X Y hX hY hXY c hc q hq p ⟨hp, hpq⟩
  set eX := hφ.belowEquiv (himage X hX)
  set eY := hφ.belowEquiv (himage Y hY)
  have hle : Prod.map g id X ≤ Prod.map g id Y := ⟨hg hX.1 hY.1 hXY.1, hXY.2⟩
  have hinc (t : E.below X) :
      eY (Set.inclusion (E.below_mono hXY) t) = Set.inclusion (D.below_mono hle) (eX t) :=
    Subtype.ext (by simp [eX, eY])
  have hinc' (d : D.below (Prod.map g id X)) :
      eY.symm (Set.inclusion (D.below_mono hle) d) = Set.inclusion (E.below_mono hXY) (eX.symm d) :=
    eY.symm_apply_eq.mpr (by rw [hinc, eX.apply_symm_apply])
  have hq' : R.IsLawfulBelow _ (q ∘ eY.symm) :=
    (isLawfulBelow_comap_iff hφ (himage Y hY)).mp (by simpa [eY, Function.comp_assoc] using hq)
  have hp' : R.IsLawfulBelow _ (p ∘ eX.symm) :=
    (isLawfulBelow_comap_iff hφ (himage X hX)).mp (by simpa [eX, Function.comp_assoc] using hp)
  obtain ⟨q', ⟨hl, he⟩, hr⟩ := hR (hfaces X hX) (hfaces Y hY) hle c hc _ hq'
    ⟨hp', fun d ↦ by simpa [hinc'] using hpq (eX.symm d)⟩
  refine ⟨q' ∘ eY, ⟨(isLawfulBelow_comap_iff hφ (himage Y hY)).mpr hl,
    fun d ↦ by simpa using he (eY d)⟩, funext fun t ↦ ?_⟩
  simpa [hinc] using congrFun hr (eX t)

/-- **Pullback along an embedding of ground sets.**  The pullback of bountiful rows along the
inclusion of the cells visible through an embedding `f : β ↪ α` is bountiful. -/
theorem IsBountiful.comap (hR : R.IsBountiful) (f : β ↪ α) :
    (R.comap (IsLowerEmbedding.comap D f)).IsBountiful :=
  hR.comap_of_image_eq _ (fun _ _ _ _ h ↦ map_subset_map.mpr h)
    (fun _ hX ↦ (mem_gradedFaces_comap D f).mp hX) fun X _ ↦ image_val_below_comap D f X

/-- **Reindexing along an equivalence of cells.**  Bountifulness is preserved by reindexing the
cells along an equivalence. -/
theorem IsBountiful.reindex (hR : R.IsBountiful) (e : κ ≃ ι) :
    (R.comap (IsLowerEmbedding.reindex D e)).IsBountiful :=
  hR.comap_of_image_eq _ (monotone_id.monotoneOn _) (fun _ hX ↦ hX) fun X _ ↦
    e.image_preimage (D.below X)

end Rows

end VaughtConjecture.CellScheme

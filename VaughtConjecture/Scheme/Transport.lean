/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Bountiful

/-!
# Transport of capped lifts and of bountifulness

Roadmap, Layer 1 (bountifulness; restriction, transport, and pullback); semantic contract, item 3
(capping is not stage reduction, and capped vectors need not be lawful: bountifulness is
transported cap by cap, through lawful labellings, never by transporting a capped observation as
a lawful labelling); the expositions, §2.

**Capped lifts.**  A capped lift (`CellScheme.Rows.CappedLift`) transports along equivalences of
the lower sets that commute with restriction, preserve lawfulness, and do not raise the target
grade (`CappedLift.of_equiv`).  In particular, if a lower embedding `φ` of `E` into `D` maps the
cells below `X'` and `Y'` onto the cells below `X` and `Y`, the cells below them are identified by
the equivalences `IsLowerEmbedding.belowEquiv` (in `VaughtConjecture.Scheme.Cell`), which commute
with restriction and under which lawfulness below `X'` is lawfulness below `X`
(`Rows.isLawfulBelow_comap_iff`, in `VaughtConjecture.Scheme.Row`), so lifts transport in both
directions (`CappedLift.comap`, `CappedLift.of_comap`, `cappedLift_comap_iff`).  No bountifulness
is assumed: a lift at one pair is a property of that pair alone.

**Bountifulness.**  Bountifulness (`CellScheme.Rows.IsBountiful`) is capped lifting at every pair
of graded faces, so it passes to the rows pulled back along a lower embedding `φ` of `E` into `D`,
provided the graded faces of `E` are sent to graded faces of `D` by a map of faces `g`, monotone
on the faces of `E` (grades unchanged), under which `φ` maps the cells below each graded face `X`
of `E` onto the cells below its image (`IsBountiful.comap_of_image_eq`, from `CappedLift.comap` at
every pair).  Instances:

* the pullback along an embedding `f : β ↪ α` of ground sets (`IsBountiful.comap`), with the
  faces `(C, j) ↦ (f '' C, j)` (`Prod.map (Finset.map f) id`): the graded faces of `D.comap f` are
  those whose image is a graded face of `D` (`mem_gradedFaces_comap`), and the cells below a pair
  in the pullback are the cells below its image (`image_val_below_comap`).  No well-formedness of
  the pullback is needed;
* reindexing along an equivalence of cells (`IsBountiful.reindex`);
* the restriction to a face `B` (`IsBountiful.restrict`), with the identity map of faces: the
  cells below a pair inside `B` are the same in the restriction and in the scheme
  (`image_val_below_restrict`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the restriction of a semantics to a face of the plan
is [Kni26, Lemma 2.5.5], and its transport along a one-to-one map is clause 5 of
[Kni26, Proposition 2.6.3].
-/

universe u

namespace VaughtConjecture.CellScheme

open Finset

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

namespace Rows

variable {R : D.Rows.{u}} {X Y : Finset α × ℕ}

/-! ### Transport of capped lifts -/

/-- **Transport of lifts along equivalences of lower sets.**  Let `R'` be rows of a scheme `E`
and `X' ≤ Y'` pairs of `E`, with equivalences from the cells below `X'` and `Y'` to the cells
below `X` and `Y` that commute with restriction, carry labellings lawful below `X` to labellings
lawful below `X'`, and identify the labellings lawful below `Y` and `Y'`.  If the grade of `Y'` is
at most that of `Y`, a capped lift from `X'` to `Y'` gives one from `X` to `Y`. -/
theorem CappedLift.of_equiv {R' : E.Rows.{u}} {X' Y' : Finset β × ℕ} {h' : X' ≤ Y'} {h : X ≤ Y}
    (eX : E.below X' ≃ D.below X) (eY : E.below Y' ≃ D.below Y)
    (hsq : ∀ d, eY (Set.inclusion (E.below_mono h') d) = Set.inclusion (D.below_mono h) (eX d))
    (hgrade : Y'.2 ≤ Y.2) (hX : ∀ p, R.IsLawfulBelow X p → R'.IsLawfulBelow X' (p ∘ eX))
    (hY : ∀ q, R.IsLawfulBelow Y q ↔ R'.IsLawfulBelow Y' (q ∘ eY)) (hl : R'.CappedLift h') :
    R.CappedLift h := by
  intro c hc q hq p ⟨hp, hpq⟩
  obtain ⟨r, ⟨hr, hrc⟩, hrp⟩ := hl c (hc.mono hgrade) (q ∘ eY) ((hY q).mp hq)
    ⟨hX p hp, fun d ↦ by simpa [hsq] using hpq (eX d)⟩
  refine ⟨r ∘ eY.symm, ⟨(hY _).mpr (by simpa [Function.comp_assoc] using hr),
    fun d ↦ by simpa using hrc (eY.symm d)⟩, funext fun d ↦ ?_⟩
  have he : eY.symm (Set.inclusion (D.below_mono h) d) =
      Set.inclusion (E.below_mono h') (eX.symm d) :=
    eY.symm_apply_eq.mpr (by rw [hsq, eX.apply_symm_apply])
  simpa [he] using congrFun hrp (eX.symm d)

section LowerEmbedding

variable {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ) {X' Y' : Finset β × ℕ} {h' : X' ≤ Y'}
  {h : X ≤ Y} (hX : φ '' E.below X' = D.below X) (hY : φ '' E.below Y' = D.below Y)
include hX hY

/-- **Pullback of lifts along a lower embedding.**  If `φ` maps the cells below `X'` and `Y'`
onto the cells below `X` and `Y`, and the grade of `Y` is at most that of `Y'`, a capped lift of
`R` from `X` to `Y` pulls back to a capped lift of the pulled-back rows from `X'` to `Y'`. -/
theorem CappedLift.comap (hgrade : Y.2 ≤ Y'.2) (hl : R.CappedLift h) :
    (R.comap hφ).CappedLift h' := by
  refine hl.of_equiv (hφ.belowEquiv hX).symm (hφ.belowEquiv hY).symm (fun d ↦ ?_) hgrade
    (fun p hp ↦ (isLawfulBelow_comap_iff hφ hX).mp (by simpa [Function.comp_assoc] using hp))
    fun q ↦ ?_
  · rw [Equiv.symm_apply_eq, hφ.belowEquiv_inclusion h' h hX hY, Equiv.apply_symm_apply]
  · rw [← isLawfulBelow_comap_iff hφ hY]
    simp [Function.comp_assoc]

/-- **Pushforward of lifts along a lower embedding.**  If `φ` maps the cells below `X'` and `Y'`
onto the cells below `X` and `Y`, and the grade of `Y'` is at most that of `Y`, a capped lift of
the pulled-back rows from `X'` to `Y'` gives a capped lift of `R` from `X` to `Y`. -/
theorem CappedLift.of_comap (hgrade : Y'.2 ≤ Y.2) (hl : (R.comap hφ).CappedLift h') :
    R.CappedLift h :=
  hl.of_equiv (hφ.belowEquiv hX) (hφ.belowEquiv hY) (hφ.belowEquiv_inclusion h' h hX hY) hgrade
    (fun _ hp ↦ (isLawfulBelow_comap_iff hφ hX).mpr hp)
    fun _ ↦ (isLawfulBelow_comap_iff hφ hY).symm

/-- Along a lower embedding mapping the cells below `X'` and `Y'` onto the cells below `X` and
`Y`, with `Y` and `Y'` of the same grade, the pulled-back rows lift capped from `X'` to `Y'`
exactly when the rows lift capped from `X` to `Y`. -/
theorem cappedLift_comap_iff (hgrade : Y'.2 = Y.2) :
    (R.comap hφ).CappedLift h' ↔ R.CappedLift h :=
  ⟨CappedLift.of_comap hφ hX hY hgrade.le, CappedLift.comap hφ hX hY hgrade.ge⟩

end LowerEmbedding

/-! ### Transport of bountifulness -/

/-- **Transport of bountifulness.**  Let `φ` be a lower embedding of `E` into `D` and `g` a
map of faces, monotone on the faces of `E`, such that, for every graded face `X = (C, j)` of
`E`, the pair `(g C, j)` is a graded face of `D` and `φ` maps the cells below `X` onto the cells
below `(g C, j)`.  Then the pullback of bountiful rows along `φ` is bountiful: the capped lift
between the images of two graded faces pulls back (`CappedLift.comap`). -/
theorem IsBountiful.comap_of_image_eq {φ : κ → ι} {R : D.Rows.{u}} (hR : R.IsBountiful)
    (hφ : E.IsLowerEmbedding D φ) {g : Finset β → Finset α} (hg : MonotoneOn g E.faces)
    (hfaces : ∀ X ∈ E.gradedFaces, Prod.map g id X ∈ D.gradedFaces)
    (himage : ∀ X ∈ E.gradedFaces, φ '' E.below X = D.below (Prod.map g id X)) :
    (R.comap hφ).IsBountiful := fun X Y hX hY h ↦
  (hR (hfaces X hX) (hfaces Y hY) ⟨hg hX.1 hY.1 h.1, h.2⟩).comap hφ (himage X hX) (himage Y hY)
    le_rfl

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

variable (R) in
/-- **Restriction to a face.**  The restriction of bountiful rows to a face is bountiful. -/
theorem IsBountiful.restrict [DecidableEq α] (hR : R.IsBountiful) (B : Finset α) :
    (R.restrict B).IsBountiful :=
  hR.comap_of_image_eq (g := id) _ (monotone_id.monotoneOn _)
    (fun _ hX ↦ ⟨(Geometry.mem_restrict.mp hX.1).1, hX.2⟩)
    fun _ hX ↦ D.image_val_below_restrict (Geometry.mem_restrict.mp hX.1).2

end Rows

end VaughtConjecture.CellScheme

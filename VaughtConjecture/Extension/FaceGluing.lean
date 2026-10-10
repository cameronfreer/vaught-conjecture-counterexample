/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.PinnedExtension

/-!
# Gluing lawful sections over two faces covering the cells

Roadmap, Layer 3 ((R3) and (R4), admitted completions over the attachment).

* **Lawfulness from two lower embeddings covering the cells**
  (`CellScheme.Rows.isLawful_of_cover`): a labelling whose pullbacks along two lower embeddings are
  lawful, every cell lying in the image of one of them, is lawful.  Locality at a cell is that of
  its preimage (every cell below it is in the same image), and availability is witnessed in the
  face of the target cell.
* **The joint extension over a one-point extension covered by its two faces**
  (`StageType.exists_joint_extension`): if every cell of `D` lies in the context face (along
  `Fin.castSuccEmb`) or in the donor face (along `extendByLast e`), then lawful sections of the
  context and of the donor agreeing on the root glue to a lawful section of `D`.  The root cells are
  reached through both faces (`StageType.faceCell_faceCell`).

The intended instance is the attachment of a donor to a context: its mixed faces carry no cell,
so it is covered by the context and donor faces, and the joint extension holds outright.

## References

Lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-- Lawfulness passes to an equal scheme, along the cast of the cells. -/
theorem Scheme.isLawful_of_eq {n : ℕ} {S T : Scheme.{u} n} (h : S = T)
    {v : Fin T.card → Label.{u}} (hv : T.rows.IsLawful v) :
    S.rows.IsLawful fun i ↦ v (Fin.cast (congrArg Scheme.card h) i) := by
  subst h
  exact hv

namespace CellScheme.Rows

variable {ι κ₁ κ₂ α β₁ β₂ : Type*} {D : CellScheme ι α} {E₁ : CellScheme κ₁ β₁}
  {E₂ : CellScheme κ₂ β₂}
  {φ₁ : κ₁ → ι} {φ₂ : κ₂ → ι}

/-- Lawfulness at the cells in the image of one lower embedding, from the pullback. -/
private theorem lawful_parts {κ β : Type*} {E : CellScheme κ β} {φ : κ → ι} {R : D.Rows.{u}}
    (hφ : E.IsLowerEmbedding D φ) {w : ι → Label.{u}} (hw : (R.comap hφ).IsLawful (w ∘ φ))
    (e : κ) :
    IsSelfVisible (D.grade (φ e)) (w (φ e)) ∧
      TransformsTo (fun t : D.below (D.gradedIndex (φ e)) ↦ D.grade t) (R.row (φ e))
        (fun t ↦ min (w t) (w (φ e))) ∧
      ∀ s, D.scope s ⊆ D.scope (φ e) → D.grade s = D.grade (φ e) →
        ∃ u, D.gradedIndex u = D.gradedIndex (φ e) ∧ w s ≤ w u := by
  classical
  refine ⟨(hφ.grade_eq e).symm ▸ hw.orderly e, ?_, fun s hst hg ↦ ?_⟩
  · -- every cell below the image is in the image
    have hpre (t : D.below (D.gradedIndex (φ e))) : ∃ t' : κ, φ t' = t.1 :=
      hφ.mem_range e t.1 t.2
    let ψ : D.below (D.gradedIndex (φ e)) → E.below (E.gradedIndex e) := fun t ↦
      ⟨(hpre t).choose, (hφ.le_iff _ e).mp (by rw [(hpre t).choose_spec]; exact t.2)⟩
    have hψ (t : D.below (D.gradedIndex (φ e))) : φ (ψ t).1 = t.1 := (hpre t).choose_spec
    have h := (hw.locality e).reindex ψ
    convert h using 1
    · funext t
      simp only [Function.comp_apply]
      rw [← hφ.grade_eq, hψ]
    · funext t
      simp only [Function.comp_apply, comap_row]
      exact R.row_congr rfl (hψ t).symm
    · funext t
      simp only [Function.comp_apply]
      rw [hψ]
  · obtain ⟨s', rfl⟩ := hφ.mem_range e s ⟨hst, hg.le⟩
    have hle : E.gradedIndex s' ≤ E.gradedIndex e := (hφ.le_iff s' e).mp ⟨hst, hg.le⟩
    obtain ⟨u', hu', hle'⟩ := hw.availability s' e hle.1
      (by rw [← hφ.grade_eq, ← hφ.grade_eq]; exact hg)
    refine ⟨φ u', le_antisymm ((hφ.le_iff u' e).mpr hu'.le) ((hφ.le_iff e u').mpr hu'.ge), hle'⟩

/-- **Lawfulness from two lower embeddings covering the cells.** -/
theorem isLawful_of_cover {R : D.Rows.{u}} (hφ₁ : E₁.IsLowerEmbedding D φ₁)
    (hφ₂ : E₂.IsLowerEmbedding D φ₂) (hcover : ∀ c, c ∈ Set.range φ₁ ∨ c ∈ Set.range φ₂)
    {w : ι → Label.{u}} (hw₁ : (R.comap hφ₁).IsLawful (w ∘ φ₁))
    (hw₂ : (R.comap hφ₂).IsLawful (w ∘ φ₂)) : R.IsLawful w := by
  have hpart (c : ι) :
      IsSelfVisible (D.grade c) (w c) ∧
        TransformsTo (fun t : D.below (D.gradedIndex c) ↦ D.grade t) (R.row c)
          (fun t ↦ min (w t) (w c)) ∧
        ∀ s, D.scope s ⊆ D.scope c → D.grade s = D.grade c →
          ∃ u, D.gradedIndex u = D.gradedIndex c ∧ w s ≤ w u := by
    rcases hcover c with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact lawful_parts hφ₁ hw₁ e
    · exact lawful_parts hφ₂ hw₂ e
  exact ⟨fun c ↦ (hpart c).1, fun c ↦ (hpart c).2.1, fun s t hst hg ↦ (hpart t).2.2 s hst hg⟩

end CellScheme.Rows

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ} {D : StageType.{u} α (k + 1)} {t' : StageType.{u} α k}
  {e : Fin n ↪ Fin k} {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
  (h₁ : restrictFace Fin.castSuccEmb D = some t') (h₂ : restrictFace (extendByLast e) D = some d)
  (ht : restrictFace e t' = some p) (hd : restrictFace Fin.castSuccEmb d = some p)

/-- A set of points of `Fin (k + 1)` without the last point lies in the range of
`Fin.castSuccEmb`. -/
theorem subset_range_castSucc_iff {k : ℕ} (s : Finset (Fin (k + 1))) :
    (s : Set (Fin (k + 1))) ⊆ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) ↔
      Fin.last k ∉ s := by
  constructor
  · intro h hl
    obtain ⟨y, hy⟩ := h (mem_coe.mpr hl)
    simp at hy
  · intro h x hx
    have hx' : x ≠ Fin.last k := fun he ↦ h (he ▸ mem_coe.mp hx)
    obtain ⟨y, rfl⟩ := Fin.exists_castSucc_eq.mpr hx'
    exact ⟨y, rfl⟩

include h₁ h₂ ht hd in
/-- **The joint extension over a one-point extension covered by its two faces**: if every cell of
`D` lies in the context face or in the donor face, lawful sections of the context and of the donor
agreeing on the root glue to a lawful section of `D`. -/
theorem exists_joint_extension
    (hcover : ∀ c, c ∈ D.toScheme.visibleCells Fin.castSuccEmb ∨
      c ∈ D.toScheme.visibleCells (extendByLast e))
    {u : Fin t'.card → Label.{u}} {w : Fin d.card → Label.{u}} (hu : t'.rows.IsLawful u)
    (hw : d.rows.IsLawful w) (hroot : ∀ i, w (d.faceCell hd i) = u (t'.faceCell ht i)) :
    ∃ R : Fin D.card → Label.{u}, D.rows.IsLawful R ∧ (∀ x, R (D.faceCell h₁ x) = u x) ∧
      ∀ j, R (D.faceCell h₂ j) = w j := by
  classical
  have hC₁ := comap_toScheme_of_restrictFace h₁
  have hC₂ := comap_toScheme_of_restrictFace h₂
  -- the index of a cell in each face
  have hidx₁ (c : Fin D.card) (hc : c ∈ D.toScheme.visibleCells Fin.castSuccEmb) :
      ∃ x, D.faceCell h₁ x = c := D.toScheme.exists_faceCell_eq hC₁ hc
  have hidx₂ (c : Fin D.card) (hc : c ∈ D.toScheme.visibleCells (extendByLast e)) :
      ∃ j, D.faceCell h₂ j = c := D.toScheme.exists_faceCell_eq hC₂ hc
  have hinj₁ : Function.Injective (D.faceCell h₁) := fun x y hxy ↦ by
    have h := (D.toScheme.cellMap Fin.castSuccEmb).injective hxy
    exact Fin.cast_injective _ h
  have hinj₂ : Function.Injective (D.faceCell h₂) := fun x y hxy ↦ by
    have h := (D.toScheme.cellMap (extendByLast e)).injective hxy
    exact Fin.cast_injective _ h
  let R : Fin D.card → Label.{u} := fun c ↦
    if hc : c ∈ D.toScheme.visibleCells Fin.castSuccEmb then u (hidx₁ c hc).choose
    else w (hidx₂ c ((hcover c).resolve_left hc)).choose
  have hR₁ (x : Fin t'.card) : R (D.faceCell h₁ x) = u x := by
    have hv : D.faceCell h₁ x ∈ D.toScheme.visibleCells Fin.castSuccEmb :=
      D.toScheme.faceCell_mem_visibleCells hC₁ x
    simp only [R]
    rw [dite_eq_left hv]
    exact congrArg u (hinj₁ (hidx₁ _ hv).choose_spec)
  have hR₂ (j : Fin d.card) : R (D.faceCell h₂ j) = w j := by
    by_cases hv : D.faceCell h₂ j ∈ D.toScheme.visibleCells Fin.castSuccEmb
    · -- a root cell
      have hl : Fin.last k ∉ D.toCellScheme.scope (D.faceCell h₂ j) :=
        (subset_range_castSucc_iff _).mp (Scheme.mem_visibleCells.mp hv)
      rw [last_mem_scope_faceCell_iff h₂] at hl
      have hjv : j ∈ d.toScheme.visibleCells Fin.castSuccEmb :=
        Scheme.mem_visibleCells.mpr ((subset_range_castSucc_iff _).mpr hl)
      obtain ⟨i, rfl⟩ := d.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hd) hjv
      have hfc := faceCell_faceCell h₁ h₂ ht hd i
      change R (D.faceCell h₂ (d.faceCell hd i)) = w (d.faceCell hd i)
      rw [← hfc, hR₁, hroot]
    · simp only [R]
      rw [dite_eq_right hv]
      exact congrArg w (hinj₂ (hidx₂ _ ((hcover _).resolve_left hv)).choose_spec)
  clear_value R
  refine ⟨R, ?_, hR₁, hR₂⟩
  refine CellScheme.Rows.isLawful_of_cover (D.toScheme.isLowerEmbedding_comap Fin.castSuccEmb)
    (D.toScheme.isLowerEmbedding_comap (extendByLast e)) (fun c ↦ ?_) ?_ ?_
  · rcases hcover c with hc | hc
    · left; rw [Scheme.range_cellMap]; exact mem_coe.mpr hc
    · right; rw [Scheme.range_cellMap]; exact mem_coe.mpr hc
  · have h := Scheme.isLawful_of_eq hC₁ hu
    have h' : (D.toScheme.comap Fin.castSuccEmb).rows.IsLawful
        (R ∘ D.toScheme.cellMap Fin.castSuccEmb) := by
      have hfun : (R ∘ D.toScheme.cellMap Fin.castSuccEmb) =
          fun i ↦ u (Fin.cast (congrArg Scheme.card hC₁) i) :=
        funext fun i ↦ hR₁ (Fin.cast (congrArg Scheme.card hC₁) i)
      rw [hfun]
      exact h
    exact h'
  · have h := Scheme.isLawful_of_eq hC₂ hw
    have h' : (D.toScheme.comap (extendByLast e)).rows.IsLawful
        (R ∘ D.toScheme.cellMap (extendByLast e)) := by
      have hfun : (R ∘ D.toScheme.cellMap (extendByLast e)) =
          fun i ↦ w (Fin.cast (congrArg Scheme.card hC₂) i) :=
        funext fun i ↦ hR₂ (Fin.cast (congrArg Scheme.card hC₂) i)
      rw [hfun]
      exact h
    exact h'

end StageType

end VaughtConjecture

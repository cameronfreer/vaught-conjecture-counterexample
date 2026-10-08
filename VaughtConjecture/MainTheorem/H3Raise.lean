/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Class

/-!
# The raise of the new tops over a root labelling (work file for `h3`)

Work file (placement later), for the input (S2) of `VaughtConjecture.MainTheorem.H3Class`.
Compiled in this repository (theorem named):

* **A face labelling below its graded face** (`StageType.faceExtend`,
  `StageType.isLawfulBelow_faceExtend`): a lawful labelling of the face of `D` along `f`, extended
  by `⊥`, is lawful below the graded face `(univ.map f, m)` of `D`.
* **The lift of a root labelling relative to a lawful labelling**
  (`StageType.exists_isLawful_faceLift`): for `ψ` lawful on the face `t` of `d` and `q` lawful
  on `d` agreeing with `ψ` on the face capped at a label `θ` self-visible at `n + 1`, some
  labelling lawful on `d` is `ψ` on the face and agrees with `q` capped at `θ` (bountifulness).
* **The base of the raise** (`StageType.exists_isLawful_raise`): let `d` be legal on `n + 1` points
  with face `t` along the first `n` points, `ψ` lawful on `t`, `Φ` a witness bounded by a grade at
  least `n + 1` sending no label of `d` other than `⊥` to `⊥`, and `θ` self-visible at `n + 1`
  with `Φ ∘ t.label` and `ψ` agreeing capped at `θ`.  Then some labelling lawful on `d` is `ψ` on
  the face and agrees with `Φ ∘ d.label` capped at `θ`: the capped lift of `d` (bountifulness) from
  the face to the whole, relative to the lawful `Φ ∘ d.label`
  (`CellScheme.Rows.IsLawful.map_of_apply_eq_bot`).  In particular it is at least `θ` at every cell
  labelled `⊤` when `θ ≤ Φ ⊤`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A labelling of the face of `D` along `f`, extended by `⊥` to the cells of `D`. -/
noncomputable def faceExtend {D : StageType.{u} α n} {f : Fin m ↪ Fin n} {t : StageType.{u} α m}
    (h : restrictFace f D = some t) (ψ : Fin t.card → Label.{u}) : Fin D.card → Label.{u} :=
  fun z ↦ if hz : ∃ i, faceCell h i = z then ψ hz.choose else ⊥

theorem faceExtend_faceCell {D : StageType.{u} α n} {f : Fin m ↪ Fin n} {t : StageType.{u} α m}
    (h : restrictFace f D = some t) (ψ : Fin t.card → Label.{u}) (i : Fin t.card) :
    faceExtend h ψ (faceCell h i) = ψ i := by
  unfold faceExtend
  split_ifs with hz
  · exact congrArg ψ (D.toScheme.faceCell_injective _ hz.choose_spec)
  · exact absurd ⟨i, rfl⟩ hz

/-- **A lawful labelling of a face, extended by `⊥`, is lawful below the graded face.** -/
theorem isLawfulBelow_faceExtend {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (h : restrictFace f D = some t) {ψ : Fin t.card → Label.{u}}
    (hψ : t.rows.IsLawful ψ) :
    D.rows.IsLawfulBelow ((univ : Finset (Fin m)).map f, m) fun z ↦ faceExtend h ψ z := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  have key := (Scheme.isLawfulBelow_comap_cellMap_iff (S := D.toScheme) f
    ((univ : Finset (Fin m)), m) (faceExtend h ψ)).mp
  refine key ((Rows.isLawfulBelow_congr (w := ψ)
    (w' := fun i ↦ faceExtend h ψ (D.toScheme.cellMap f i)) fun i _ ↦ ?_).mp
      (hψ.isLawfulBelow _))
  exact (faceExtend_faceCell h ψ i).symm

/-- **The lift of a root labelling relative to a lawful labelling.**  Let `d` be legal on
`n + 1` points with face `t` along the first `n` points, `ψ` lawful on `t`, `q` lawful on `d`, and
`θ` self-visible at `n + 1` with `q` and `ψ` agreeing on the face capped at `θ`.  Then some
labelling lawful on `d` is `ψ` on the face and agrees with `q` capped at `θ`: the capped lift of
`d` (bountifulness) from the face to the whole. -/
theorem exists_isLawful_faceLift {d : StageType.{u} α (n + 1)} (hd : d.IsLegal)
    {t : StageType.{u} α n} (ht : restrictFace Fin.castSuccEmb d = some t)
    {ψ : Fin t.card → Label.{u}} (hψ : t.rows.IsLawful ψ) {q : Fin d.card → Label.{u}}
    (hq : d.rows.IsLawful q) {θ : Label.{u}} (hθ : IsSelfVisible (n + 1) θ)
    (hroot : ∀ x, min (q (faceCell ht x)) θ = min (ψ x) θ) :
    ∃ v : Fin d.card → Label.{u}, d.rows.IsLawful v ∧ (∀ x, v (faceCell ht x) = ψ x) ∧
      ∀ z, min (v z) θ = min (q z) θ := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨q, hq, fun x ↦ ?_, fun _ ↦ rfl⟩
    have h1 := t.isWellFormed.isWellFormed.grade_pos x
    have h2 := t.grade_le x
    omega
  obtain ⟨hf, -⟩ := (restrictFace_eq_some_iff d Fin.castSuccEmb).mp ht
  set X : Finset (Fin (n + 1)) × ℕ := ((univ : Finset (Fin n)).map Fin.castSuccEmb, n)
  set Y : Finset (Fin (n + 1)) × ℕ := ((univ : Finset (Fin (n + 1))), n + 1)
  have hX : X ∈ d.toCellScheme.gradedFaces := ⟨hf, hn, by simp [X]⟩
  have hY : Y ∈ d.toCellScheme.gradedFaces := ⟨d.univ_mem_faces, Nat.succ_pos n, by simp [Y]⟩
  have hXY : X ≤ Y := Prod.mk_le_mk.mpr ⟨subset_univ _, Nat.le_succ n⟩
  have hall (z : Fin d.card) : z ∈ d.toCellScheme.below Y :=
    ⟨subset_univ _, d.grade_le z⟩
  obtain ⟨q', hq', hq'c, hq'p⟩ :=
    ((VaughtConjecture.CellScheme.Rows.isBountiful_iff_forall_exists (R := d.rows)).mp
    hd.isBountiful) hX hY hXY θ hθ (fun z ↦ faceExtend ht ψ z) (fun z ↦ q z)
    (isLawfulBelow_faceExtend ht hψ) (hq.isLawfulBelow Y) fun z ↦ by
      obtain ⟨x, hx⟩ := exists_faceCell_eq ht (Scheme.mem_visibleCells.mpr fun y hy ↦ by
        obtain ⟨w, -, hw⟩ := mem_map.mp (z.2.1 hy)
        exact ⟨w, hw⟩)
      change min (q z.1) θ = min (faceExtend ht ψ z.1) θ
      rw [← hx, faceExtend_faceCell]
      exact hroot x
  refine ⟨fun z ↦ q' ⟨z, hall z⟩, hq'.isLawful hall, fun x ↦ ?_, fun z ↦ hq'c ⟨z, hall z⟩⟩
  have hxX : faceCell ht x ∈ d.toCellScheme.below X := by
    refine ⟨?_, ?_⟩
    · change d.toCellScheme.scope (faceCell ht x) ⊆ (univ : Finset (Fin n)).map Fin.castSuccEmb
      rw [scope_faceCell]
      exact map_subset_map.mpr (subset_univ _)
    · change d.toCellScheme.grade (faceCell ht x) ≤ n
      rw [grade_faceCell]
      exact t.grade_le x
  have h := hq'p ⟨faceCell ht x, hxX⟩
  change q' ⟨faceCell ht x, _⟩ = faceExtend ht ψ (faceCell ht x) at h
  rw [faceExtend_faceCell] at h
  exact h

/-- **The base of the raise.**  Let `d` be legal on `n + 1` points with face `t` along the first
`n` points, `ψ` lawful on `t`, `Φ` a witness bounded by a grade `K ≥ n + 1` that sends no label of
`d` other than `⊥` to `⊥`, and `θ` self-visible at `n + 1`, with `Φ ∘ t.label` and `ψ` agreeing
capped at `θ`.  Then some labelling lawful on `d` is `ψ` on the face and agrees with `Φ ∘ d.label`
capped at `θ` (`StageType.exists_isLawful_faceLift` relative to `Φ ∘ d.label`). -/
theorem exists_isLawful_raise {d : StageType.{u} α (n + 1)} (hd : d.IsLegal)
    {t : StageType.{u} α n} (ht : restrictFace Fin.castSuccEmb d = some t)
    {ψ : Fin t.card → Label.{u}} (hψ : t.rows.IsLawful ψ) {K : ℕ} (hK : n + 1 ≤ K)
    {Φ : Label.{u} → Label.{u}} (hΦ : IsWitness (stepSuppressor K) Φ)
    (hΦbot : ∀ z, Φ (d.label z) = ⊥ → d.label z = ⊥) {θ : Label.{u}}
    (hθ : IsSelfVisible (n + 1) θ) (hroot : ∀ x, min (Φ (t.label x)) θ = min (ψ x) θ) :
    ∃ v : Fin d.card → Label.{u}, d.rows.IsLawful v ∧ (∀ x, v (faceCell ht x) = ψ x) ∧
      ∀ z, min (v z) θ = min (Φ (d.label z)) θ :=
  exists_isLawful_faceLift hd ht hψ
    (d.isLawful.map_of_apply_eq_bot (fun z ↦ (d.grade_le z).trans hK) hΦ hΦbot) hθ
    fun x ↦ by
      change min (Φ (d.label (faceCell ht x))) θ = _
      rw [label_faceCell]
      exact hroot x

end StageType

end VaughtConjecture

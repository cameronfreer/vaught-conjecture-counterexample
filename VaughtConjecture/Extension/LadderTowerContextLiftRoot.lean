/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRelativeLift
import VaughtConjecture.Extension.LadderTowerContextLift

/-!
# The root lift of a legal donor at a grade

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the recognizing growth carrier).

A legal donor `d` on `n + 1` points with root face `p` (`0 < n`) lifts capped from the root face
to the full face at every grade `K` with `1 ≤ K ≤ n + 1`, at every cap self-visible at `K`
(bountifulness).  **The root lift at a grade** (`StageType.IsLegal.exists_rootLift_le`): a lawful
section `ρ` of the root face vanishing above `K` and a lawful section `v` of `d` agreeing with it
capped at `γ` on the root cells of grade at most `K` give a lawful section of `d` equal to `ρ` on
the root, vanishing above `K`, with the observation of `v` at `γ` at every cell of grade at most
`K`.  At `K = n + 1` it is `StageType.IsLegal.exists_rootLift` with a cap self-visible at the
arity; here the cap need only be self-visible at `K`.

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The root lift of a legal donor at a grade `K`**, with a cap self-visible at `K`. -/
theorem IsLegal.exists_rootLift_le {d : StageType.{u} α (n + 1)} (hd : d.IsLegal) (hn : 0 < n)
    {p : StageType.{u} α n}
    (hdp : VaughtConjecture.StageType.restrictFace Fin.castSuccEmb d = some p)
    {v : Fin d.card → Label.{u}} (hv : d.rows.IsLawful v) {ρ : Fin p.card → Label.{u}}
    (hρ : p.rows.IsLawful ρ) {K : ℕ} (hK1 : 1 ≤ K) (hKn : K ≤ n + 1)
    (hρK : ∀ i, K < p.toCellScheme.grade i → ρ i = ⊥) {γ : Label.{u}} (hγ : IsSelfVisible K γ)
    (hag : ∀ i, p.toCellScheme.grade i ≤ K → min (ρ i) γ = min (v (d.faceCell hdp i)) γ) :
    ∃ v' : Fin d.card → Label.{u}, d.rows.IsLawful v' ∧ (∀ i, v' (d.faceCell hdp i) = ρ i) ∧
      (∀ j, K < d.toCellScheme.grade j → v' j = ⊥) ∧
      ∀ j, d.toCellScheme.grade j ≤ K → min (v' j) γ = min (v j) γ := by
  classical
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff d _).mp hdp
  set K' := min K n with hK'
  set X : Finset (Fin (n + 1)) × ℕ := (univ.map Fin.castSuccEmb, K')
  set Y : Finset (Fin (n + 1)) × ℕ := ((univ : Finset (Fin (n + 1))), K)
  have hXY : X ≤ Y := ⟨subset_univ _, min_le_left _ _⟩
  have hφ := d.toScheme.isLowerEmbedding_comap Fin.castSuccEmb
  have himg : d.toScheme.cellMap Fin.castSuccEmb ''
      (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
        ((univ : Finset (Fin n)), K') = d.toCellScheme.below X := by
    rw [Scheme.image_cellMap_below]
    rfl
  let r : d.toCellScheme.below X → Label.{u} := fun x ↦ ρ ((hφ.belowEquiv himg).symm x).1
  have hr : d.rows.IsLawfulBelow X r := by
    rw [← CellScheme.Rows.isLawfulBelow_comap_iff hφ himg]
    have h1 : (d.rows.comap hφ).IsLawfulBelow ((univ : Finset (Fin n)), K') fun x ↦ ρ x.1 :=
      hρ.isLawfulBelow _
    convert h1 using 1
    funext x
    simp [r]
  have hsymm (i : Fin (d.comap Fin.castSuccEmb hf).card)
      (hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below ((univ : Finset (Fin n)), K'))
      (hm : d.toScheme.cellMap Fin.castSuccEmb i ∈ d.toCellScheme.below X) :
      ((hφ.belowEquiv himg).symm ⟨_, hm⟩).1 = i := by
    have : (hφ.belowEquiv himg) ⟨i, hi⟩ = ⟨_, hm⟩ := Subtype.ext rfl
    rw [← this, Equiv.symm_apply_apply]
  have hmemX (i : Fin (d.comap Fin.castSuccEmb hf).card)
      (hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
        ((univ : Finset (Fin n)), K')) :
      d.toScheme.cellMap Fin.castSuccEmb i ∈ d.toCellScheme.below X := by
    rw [← himg]
    exact ⟨i, hi, rfl⟩
  have hlift : d.rows.CappedLift hXY :=
    hd.isBountiful.cappedLift ⟨hf, lt_min (by omega) hn,
      by rw [card_map, card_univ, Fintype.card_fin]; exact min_le_right _ _⟩
      ⟨d.univ_mem_faces, (by omega : 0 < K), by rw [card_univ, Fintype.card_fin]; exact hKn⟩ hXY
  obtain ⟨q', hq', hq'cap, hq'r⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    hlift γ hγ r (fun x ↦ v x) hr (hv.isLawfulBelow _) (fun x ↦ by
      obtain ⟨x, hx⟩ := x
      have hx' := hx
      rw [← himg] at hx'
      obtain ⟨i, hi, rfl⟩ := hx'
      simp only [r]
      rw [hsymm i hi (hmemX i hi), hag i (hi.2.trans (min_le_left _ _))]
      rfl)
  let w : Fin d.card → Label.{u} := fun j ↦
    if h : d.toCellScheme.grade j ≤ K then q' ⟨j, ⟨subset_univ _, h⟩⟩ else ⊥
  have hw_le (j : Fin d.card) (h : d.toCellScheme.grade j ≤ K) :
      w j = q' ⟨j, ⟨subset_univ _, h⟩⟩ := by simp only [w, h, dite_true]
  have hw_lt (j : Fin d.card) (h : K < d.toCellScheme.grade j) : w j = ⊥ := by
    simp only [w, not_le.mpr h, dite_false]
  have hwY : (fun t : d.toCellScheme.below Y ↦ w t) = q' := funext fun t ↦ hw_le t.1 t.2.2
  have hwl : d.rows.IsLawfulBelow Y fun t ↦ w t := by rw [hwY]; exact hq'
  have hext := CellScheme.Rows.isLawfulBelow_extendAbove (K := n + 1) hwl
  have hext' : d.rows.IsLawfulBelow ((univ : Finset (Fin (n + 1))), n + 1) fun j ↦ w j := by
    refine (CellScheme.Rows.isLawfulBelow_congr (w := fun j ↦ if d.toCellScheme.grade j ≤ K
      then w j else ⊥) fun j _ ↦ ?_).mp hext
    by_cases h : d.toCellScheme.grade j ≤ K
    · exact ite_eq_left h
    · rw [ite_eq_right h, hw_lt j (not_le.mp h)]
  have hwL : d.rows.IsLawful w :=
    CellScheme.Rows.isLawful_of_isLawfulBelow (fun j ↦ by exact ⟨subset_univ _, d.grade_le j⟩)
      hext'
  refine ⟨w, hwL, fun i ↦ ?_, hw_lt, fun j hj ↦ ?_⟩
  · have hgi : (d.comap Fin.castSuccEmb hf).toCellScheme.grade i ≤ n :=
      (d.comap Fin.castSuccEmb hf).grade_le i
    have hgc : d.toCellScheme.grade (d.toScheme.cellMap Fin.castSuccEmb i) =
        (d.comap Fin.castSuccEmb hf).toCellScheme.grade i := rfl
    by_cases hik : (d.comap Fin.castSuccEmb hf).toCellScheme.grade i ≤ K
    · have hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
          ((univ : Finset (Fin n)), K') := ⟨subset_univ _, le_min hik hgi⟩
      change w (d.toScheme.cellMap Fin.castSuccEmb i) = ρ i
      rw [hw_le _ (hgc ▸ hik)]
      have h1 := hq'r ⟨_, hmemX i hi⟩
      simp only [r] at h1
      rw [hsymm i hi (hmemX i hi)] at h1
      exact h1
    · change w (d.toScheme.cellMap Fin.castSuccEmb i) = ρ i
      rw [hw_lt _ (hgc ▸ not_le.mp hik), hρK i (not_le.mp hik)]
  · rw [hw_le j hj]
    exact hq'cap ⟨j, ⟨subset_univ _, hj⟩⟩

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.RepairedTieLift

/-!
# The tie input with agreement heights in the grid alone

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme: the old scheme beside
the repaired one).

The height sets are a parameter of the replicated scheme (`Seed.replicated`, default
`Scheme.heightSet Γ B'`); the height sets of the empty set of values are the grid alone
(`Scheme.heightSet_empty`).  This module states the obstruction of the grid alone at the tie input
of `Seed.exists_lift_of_tie`, as an executable statement beside the repaired lift.

* **The tie value is pinned when it is not a height** (`Seed.not_exists_lift_of_tie_of_pin`): with
  agreement heights in the height sets of values `Γh`, if every height at the grade `k` at least
  the tie value `m + 2` lies strictly above it, then at the tie input (a complete lawful admitted
  state `P₀` with `⊥ < P₀ a₂ < P₀ a₁` at two cells of grade `k` below the context coatom, the cap
  `m + 2`, the ambient the writing of the positive constant `m + 2` on the support of `P₀`, the
  prescription a code of `P₀` shifted by one block) no labelling lawful below `(univ, k)` keeps
  the ambient at the cap and is the prescription below the context coatom
  (`Seed.not_lawful_of_pin`, with the tied cell pinned).
* **In the grid alone the tie value is pinned** (`Seed.tieValue_lt_of_mem_grid`): the grid points
  at a grade `k ≤ m + 1` are `⊥` and labels of finite part `k`, none equal to `m + 2`.
* With heights in `Scheme.heightSet Γ B'` and `Γ` containing the code set the tie value is a height,
  the pin fails, and the lift exists (`Seed.exists_lift_of_tie`).

**Scope.**  An obstruction to the earlier constructions (the replicated scheme over the height-set
tower, or carriers with admitted controllers), or a step of one; not used by the main theorem
through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept as the compiled
reason that construction was replaced.

## References

Lawful sections and bountifulness are [Kni26, Definitions 2.5.4 and 2.5.14]; agreement heights
are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Scheme

/-- **The height sets of no values are the grid.** -/
theorem heightSet_empty (B' k : ℕ) : heightSet (∅ : Finset Label.{u}) B' k = grid k B' := by
  ext x
  rw [mem_heightSet]
  exact ⟨fun h ↦ h.resolve_right fun h' ↦ Finset.notMem_empty x h'.1, .inl⟩

end Scheme

namespace Seed

/-- A grid point at a grade `k` is not a label self-visible at a larger grade. -/
theorem gridPoint_ne_of_isSelfVisible {k K : ℕ} (hk : k < K) (b : ℕ) {y : Label.{u}}
    (hy : IsSelfVisible K y) : gridPoint k b ≠ y := by
  rintro rfl
  rw [gridPoint, isSelfVisible_coe, finNat_spec,
    finNat_add_natCast (isSuccPrelimit_omega0_mul (b : Ordinal.{u}))] at hy
  exact absurd (by exact_mod_cast hy) (not_le.mpr hk)

/-- **In the grid alone the tie value is pinned**: every height of the empty set of values at a
grade `k ≤ m + 1` at least the tie value `m + 2` lies strictly above it. -/
theorem tieValue_lt_of_mem_grid {m k B' : ℕ} (hk : k ≤ m + 1) {x : Label.{u}}
    (hx : x ∈ Scheme.heightSet (∅ : Finset Label.{u}) B' k) (hxy : tieValue m ≤ x) :
    tieValue m < x := by
  rw [Scheme.heightSet_empty] at hx
  refine lt_of_le_of_ne hxy fun he ↦ ?_
  rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
  · exact tieValue_ne_bot m he
  · exact gridPoint_ne_of_isSelfVisible (by omega) b (isSelfVisible_tieValue m) he.symm

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ Γh : Finset Label.{u}} {B' : ℕ} {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The tie value pinned defeats the lift at the tie input**: with agreement heights in the
height sets of values `Γh`, if every height at the grade `k` at least the tie value `m + 2` lies
strictly above it, then at the tie input no labelling lawful below `(univ, k)` keeps the ambient
(the writing of the positive constant `m + 2` on the support of `P₀`) at the cap `m + 2` and is the
prescription (a code `(RP, σ)` of `P₀` shifted by one block) below the context coatom: the cell
`a₁` is pinned (`Seed.not_lawful_of_pin`, with `a₃ = a₁`, the ambient tying `a₁` and `a₂`). -/
theorem not_exists_lift_of_tie_of_pin (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hk2 : 2 ≤ k)
    (hkm : k ≤ m + 1) (hpin : ∀ x ∈ Scheme.heightSet Γh B' k, tieValue m ≤ x → tieValue m < x)
    {P₀ : Fin (I.attachment g).card → Label.{u}} (hP₀ : (I.attachment g).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits g hd Q (m + 2) P₀) {a₁ a₂ : Fin (I.attachment g).card}
    (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k)
    (hs₁ : (I.attachment g).toCellScheme.scope a₁ ⊆ ctxCoatom m)
    (hs₂ : (I.attachment g).toCellScheme.scope a₂ ⊆ ctxCoatom m) (h20 : P₀ a₂ ≠ ⊥)
    (h21 : P₀ a₂ < P₀ a₁) {RP : Fin (I.attachment g).card → Label.{u}}
    (hRP : RP ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2))
    {σ : Label.{u} → Label.{u}} (hσR : ∀ a, σ (RP a) = omegaShift (P₀ a)) :
    ¬ ∃ q' : (I.replicated g H Γ (I.attachAdmits g hd Q) B'
        (fun k ↦ Scheme.heightSet Γh B' k)).toCellScheme.below
          ((univ : Finset (Fin (m + 2))), k) → Label.{u},
      (I.replicated g H Γ (I.attachAdmits g hd Q) B'
        (fun k ↦ Scheme.heightSet Γh B' k)).rows.IsLawfulBelow
          ((univ : Finset (Fin (m + 2))), k) q' ∧
      (∀ e, min (q' e) (tieValue m) = min (I.replicatedWritingOn g H Γ (I.attachAdmits g hd Q) B'
        (fun k ↦ Scheme.heightSet Γh B' k) (posConst (tieValue m) ∘ P₀) e.1) (tieValue m)) ∧
      ∀ e : (I.replicated g H Γ (I.attachAdmits g hd Q) B'
          (fun k ↦ Scheme.heightSet Γh B' k)).toCellScheme.below
            (univ.erase (Fin.last (m + 1)), k),
        q' (Set.inclusion ((I.replicated g H Γ (I.attachAdmits g hd Q) B'
          (fun k ↦ Scheme.heightSet Γh B' k)).toCellScheme.below_mono
          (show ((univ.erase (Fin.last (m + 1)), k) : Finset (Fin (m + 2)) × ℕ) ≤
            ((univ : Finset (Fin (m + 2))), k) from ⟨erase_subset _ _, le_rfl⟩)) e) =
          σ (I.replicatedWritingOn g H Γ (I.attachAdmits g hd Q) B'
            (fun k ↦ Scheme.heightSet Γh B' k) RP e.1) := by
  rintro ⟨q', hq', hq'q, hq'p⟩
  have hA : ∀ k R, I.attachAdmits g hd Q (k + 3) R → I.attachAdmits g hd Q (k + 2) R :=
    fun k R h ↦ I.attachAdmits_succ g hd Q k R h
  have h10 : P₀ a₁ ≠ ⊥ := fun h ↦ absurd (h ▸ h21) not_lt_bot
  have hR' := posConst_mem_towerCat hd hQ hΓc hP₀ hP₀A
  have hRPl : (I.attachment g).rows.IsLawful RP := (Scheme.LadderBaseData.mem_towerCat.mp hRP).2.1
  have hmem (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k)
      (hs : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom m) :
      I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a ∈
        (I.replicated g H Γ (I.attachAdmits g hd Q) B'
          (fun k ↦ Scheme.heightSet Γh B' k)).toCellScheme.below
          (univ.erase (Fin.last (m + 1)), k) :=
    (attachEmb_mem_below_iff a _).mpr ⟨hs, ha.le⟩
  have hval (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k)
      (hs : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom m) (e)
      (he : e.1 = I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a) :
      q' e = omegaShift (P₀ a) := by
    have h := hq'p ⟨_, hmem a ha hs⟩
    rw [show (Set.inclusion _ ⟨_, hmem a ha hs⟩ : (I.replicated g H Γ (I.attachAdmits g hd Q)
      B' (fun k ↦ Scheme.heightSet Γh B' k)).toCellScheme.below
        ((univ : Finset (Fin (m + 2))), k)) = e from Subtype.ext he.symm] at h
    rw [h]
    change σ (I.replicatedWritingOn g H Γ (I.attachAdmits g hd Q) B'
      (fun k ↦ Scheme.heightSet Γh B' k) RP (I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a)) = _
    exact (congrArg σ (replicatedWritingOn_attachEmb hcard hRPl a)).trans (hσR a)
  have hy₁ : (posConst (tieValue m) ∘ P₀) a₁ = tieValue m := by
    change posConst _ (P₀ a₁) = _; rw [posConst, ite_eq_right h10]
  have hy₂ : (posConst (tieValue m) ∘ P₀) a₂ = tieValue m := by
    change posConst _ (P₀ a₂) = _; rw [posConst, ite_eq_right h20]
  exact not_lawful_of_pin (Γh := Γh) (R' := posConst (tieValue m) ∘ P₀) (σ := id)
    (c := tieValue m) (a := a₁) (a₁ := a₂) (a₃ := a₁) hcard hA hk2 le_rfl hkm hR' ha₁.le ha₂.le
    ha₁ (by rw [hy₁, hy₂]) (fun x hx hxy ↦ by rw [hy₁]; exact hpin x hx hxy) le_rfl
    (omegaShift_strictMono h21)
    (not_le.mpr ((tieValue_le_omegaShift m h20).trans_lt (omegaShift_strictMono h21))) hq'
    (fun e he ↦ hval a₁ ha₁ hs₁ e he) (fun e he ↦ hval a₂ ha₂ hs₂ e he)
    (fun e he ↦ hval a₁ ha₁ hs₁ e he) hq'q

end Seed

end VaughtConjecture

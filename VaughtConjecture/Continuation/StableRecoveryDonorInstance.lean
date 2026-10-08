/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryDonorApex

/-!
# A donor other than the input: the coupled-gate type with the private type `P`

Roadmap, Layer 3, 3.3 (the (R4) cap) and Layer 4 (stable recovery schemes); an instance of
`VaughtConjecture.Continuation.StableRecoveryDonorApex` with `D ≠ T`.

**The common face.**  The coupled-gate type `T` (`CoupledGatedExtensionCounterexample.P`) and the
private type `D` (`GatedExtensionCounterexample.P`) have the same face along `Fin.castSuccEmb`
(`DonorPair.restrictFace_eq`): both faces are the face of the scheme `DonorPair.S0` with one dead
cell of graded index `({0}, 1)`, whose cell is the cell `0` of either type
(`Scheme.comap_eq_of_strictMono`), labelled `⊥` in both.

**The seed** `DonorPair.seedTD α hα` of `T` and `D` over that face, and the donor data
`DonorPair.capTD R hR`: cap the full cell `4` of `T`, marker its cell `z₂ = 3` (labelled `⊤`),
references `0`, bottom class `{0, 1}`.

* `DonorPair.isLegalBelowFullGrade_donorLayer_TD`: the admitted layer with the donor `D` is legal
  below the full grade.
* `DonorPair.isStableRecoveryScheme_donorApex_TD`: at every block stage `λ_{ξ+1}` and every `γ`, the
  donor coface is a stable recovery scheme for `T`, `Fin.castSuccEmb`, the donor `D` and `γ`.
* `DonorPair.left_ne_right`: the two coatom types are different (`T` has a cell of grade `1`
  labelled `1`; `D` has none).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace DonorPair

/-- The cells of the common face: one cell of graded index `({0}, 1)` on two points. -/
def cells0 : CellScheme (Fin 1) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ {0}, fun _ ↦ 1⟩

/-- The scheme of the common face, on two points: one cell reading itself at `⊥`. -/
noncomputable def S0 : Scheme.{u} 2 := ⟨1, cells0, ⟨fun _ _ ↦ ⊥⟩⟩

theorem fin_S0 (a : Fin S0.{u}.card) : (a : ℕ) = 0 := by
  have := a.2
  change (a : ℕ) < 1 at this
  omega

/-! ### The coupled-gate type -/

section T

variable (α : Ordinal.{u}) (hα : 1 < α)

private theorem cellScope_T :
    ∀ z : Fin 5, z ≠ 0 → (1 : Fin 2) ∈ CoupledGatedExtensionCounterexample.cellScope z := by
  decide

private theorem eq_zero_T {z : Fin (CoupledGatedExtensionCounterexample.P α hα).card}
    (hz : ((CoupledGatedExtensionCounterexample.P α hα).toCellScheme.scope z : Set (Fin 2)) ⊆
      Set.range (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) :
    z = ((0 : Fin 5) : Fin (CoupledGatedExtensionCounterexample.P α hα).card) := by
  by_contra h0
  have h1 : (1 : Fin 2) ∈ (CoupledGatedExtensionCounterexample.P α hα).toCellScheme.scope z :=
    cellScope_T z h0
  obtain ⟨y, hy⟩ := hz (mem_coe.mpr h1)
  have : (y : ℕ) = 1 := congrArg Fin.val hy
  omega

private theorem isLowerEmbedding_T :
    S0.{u}.toCellScheme.IsLowerEmbedding (CoupledGatedExtensionCounterexample.P α hα).toCellScheme
      (fun _ ↦ ((0 : Fin 5) : Fin (CoupledGatedExtensionCounterexample.P α hα).card)) where
  injective a b _ := Fin.ext ((fin_S0 a).trans (fin_S0 b).symm)
  grade_eq _ := rfl
  le_iff _ _ := ⟨fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  mem_range _ d hd := by
    refine ⟨⟨0, by change 0 < 1; omega⟩, (eq_zero_T α hα (z := d) fun x hx ↦ ?_).symm⟩
    have hsub : (CoupledGatedExtensionCounterexample.P α hα).toCellScheme.scope d ⊆ {0} := hd.1
    obtain rfl := mem_singleton.mp (hsub (mem_coe.mp hx))
    exact ⟨0, rfl⟩

private theorem comap_T :
    (CoupledGatedExtensionCounterexample.P α hα).toScheme.comap Fin.castSuccEmb =
      S0.{u}.comap Fin.castSuccEmb :=
  Scheme.comap_eq_of_strictMono (S := S0)
    (φ := fun _ ↦ ((0 : Fin 5) : Fin (CoupledGatedExtensionCounterexample.P α hα).card))
    Fin.castSuccEmb (fun a b h ↦ absurd h (by rw [Fin.lt_def, fin_S0 a, fin_S0 b]; omega))
    (isLowerEmbedding_T α hα) (fun _ ↦ rfl) (by ext s t; rfl) rfl rfl
    fun z hz ↦ ⟨⟨0, by change 0 < 1; omega⟩, (eq_zero_T α hα hz).symm⟩

end T

/-! ### The private type -/

section D

variable (α : Ordinal.{u})

private theorem cellScope_D :
    ∀ z : Fin 5, z ≠ 0 → (1 : Fin 2) ∈ GatedExtensionCounterexample.cellScope z := by
  decide

private theorem eq_zero_D {z : Fin (GatedExtensionCounterexample.P α).card}
    (hz : ((GatedExtensionCounterexample.P α).toCellScheme.scope z : Set (Fin 2)) ⊆
      Set.range (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) :
    z = ((0 : Fin 5) : Fin (GatedExtensionCounterexample.P α).card) := by
  by_contra h0
  have h1 : (1 : Fin 2) ∈ (GatedExtensionCounterexample.P α).toCellScheme.scope z :=
    cellScope_D z h0
  obtain ⟨y, hy⟩ := hz (mem_coe.mpr h1)
  have : (y : ℕ) = 1 := congrArg Fin.val hy
  omega

private theorem isLowerEmbedding_D :
    S0.{u}.toCellScheme.IsLowerEmbedding (GatedExtensionCounterexample.P α).toCellScheme
      (fun _ ↦ ((0 : Fin 5) : Fin (GatedExtensionCounterexample.P α).card)) where
  injective a b _ := Fin.ext ((fin_S0 a).trans (fin_S0 b).symm)
  grade_eq _ := rfl
  le_iff _ _ := ⟨fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  mem_range _ d hd := by
    refine ⟨⟨0, by change 0 < 1; omega⟩, (eq_zero_D α (z := d) fun x hx ↦ ?_).symm⟩
    have hsub : (GatedExtensionCounterexample.P α).toCellScheme.scope d ⊆ {0} := hd.1
    obtain rfl := mem_singleton.mp (hsub (mem_coe.mp hx))
    exact ⟨0, rfl⟩

private theorem comap_D :
    (GatedExtensionCounterexample.P α).toScheme.comap Fin.castSuccEmb =
      S0.{u}.comap Fin.castSuccEmb :=
  Scheme.comap_eq_of_strictMono (S := S0)
    (φ := fun _ ↦ ((0 : Fin 5) : Fin (GatedExtensionCounterexample.P α).card))
    Fin.castSuccEmb (fun a b h ↦ absurd h (by rw [Fin.lt_def, fin_S0 a, fin_S0 b]; omega))
    (isLowerEmbedding_D α) (fun _ ↦ rfl) (by ext s t; rfl) rfl rfl
    fun z hz ↦ ⟨⟨0, by change 0 < 1; omega⟩, (eq_zero_D α hz).symm⟩

end D

/-! ### The common face and the seed -/

variable (α : Ordinal.{u}) (hα : 1 < α)

/-- **The common face**: the faces of `T` and `D` along `Fin.castSuccEmb` are equal. -/
theorem restrictFace_eq :
    StageType.restrictFace Fin.castSuccEmb (GatedExtensionCounterexample.P α) =
      some ((CoupledGatedExtensionCounterexample.P α hα).comap Fin.castSuccEmb
        (CoupledGatedExtensionCounterexample.mem_faces_castSuccEmb α hα)) := by
  rw [restrictFace_of_mem _ _ (GatedExtensionCounterexample.mem_faces_castSuccEmb α)]
  refine congrArg some (StageType.ext ((comap_D α).trans (comap_T α hα).symm) fun i j _ ↦ ?_)
  rw [comap_label, comap_label,
    eq_zero_D α (Scheme.mem_visibleCells.mp (Scheme.cellMap_mem _ _ i)),
    eq_zero_T α hα (Scheme.mem_visibleCells.mp (Scheme.cellMap_mem _ _ j))]
  rfl

/-- **The seed of the coupled-gate type `T` and the private type `D`** over their common face. -/
noncomputable abbrev seedTD : Seed.{u} α 1 :=
  Seed.ofCoatoms (CoupledGatedExtensionCounterexample.isLegal_P α hα)
    (GatedExtensionCounterexample.isLegal_P α)
    (restrictFace_of_mem _ _ (CoupledGatedExtensionCounterexample.mem_faces_castSuccEmb α hα))
    (restrictFace_eq α hα)

/-- **The two coatom types differ**: `T` has a cell labelled `1`, every label of `D` is `⊥` or
`⊤`. -/
theorem left_ne_right : (seedTD α hα).left ≠ (seedTD α hα).right := by
  intro h'
  change CoupledGatedExtensionCounterexample.P α hα = GatedExtensionCounterexample.P α at h'
  have hbt : ∀ z, (CoupledGatedExtensionCounterexample.P α hα).label z = ⊥ ∨
      (CoupledGatedExtensionCounterexample.P α hα).label z = ⊤ := by
    rw [h']
    change ∀ z : Fin 5, GatedExtensionCounterexample.labelling ⊤ ⊤ z = ⊥ ∨
      GatedExtensionCounterexample.labelling ⊤ ⊤ z = ⊤
    intro z
    fin_cases z <;> simp [GatedExtensionCounterexample.labelling]
  exact (CoupledGatedExtensionCounterexample.not_botTop_P α hα).1 hbt

/-- **The donor data**: cap the full cell `4` of `T`, marker its cell `z₂ = 3` (labelled `⊤`),
references `0`, bottom class `{0, 1}`. -/
def capTD (R : ℕ) (hR : R < 2) : (seedTD α hα).DonorCap where
  cap := ((4 : Fin 5) : Fin (CoupledGatedExtensionCounterexample.P α hα).card)
  marker := ((3 : Fin 5) : Fin (CoupledGatedExtensionCounterexample.P α hα).card)
  R := R
  R_lt_two := hR
  ref _ := ((0 : Fin 5) : Fin (CoupledGatedExtensionCounterexample.P α hα).card)
  botCells := ({0, 1} : Set (Fin 5))

/-- The hypotheses of the donor completion hold at the pair. -/
theorem donorHyp_TD (R : ℕ) (hR : R < 2) : (seedTD α hα).DonorHyp (capTD α hα R hR) where
  legalT := CoupledGatedExtensionCounterexample.isLegal_P α hα
  legalD := GatedExtensionCounterexample.isLegal_P α
  cap_grade := rfl
  dead := GatedExtensionCounterexample.hasDeadLowCells_P α
  botTop := by
    change ∀ z : Fin 5, GatedExtensionCounterexample.labelling ⊤ ⊤ z = ⊥ ∨
      GatedExtensionCounterexample.labelling ⊤ ⊤ z = ⊤
    intro z
    fin_cases z <;> simp [GatedExtensionCounterexample.labelling]

/-- **The admitted layer with the donor `D ≠ T` is legal below the full grade.** -/
theorem isLegalBelowFullGrade_donorLayer_TD (R : ℕ) (hR : R < 2) :
    ((seedTD α hα).donorLayer (capTD α hα R hR)).IsLegalBelowFullGrade :=
  have hc := donorHyp_TD α hα R hR
  Seed.isLegalBelowFullGrade_donorLayer hc.legalT hc.legalD hc.cap_grade hc.dead hc.botTop
    (StageType.hasFullRaiseFrom_of_bot_top hc.cap_grade hc.botTop _)

private theorem one_lt_blockStage' (ξ : Ordinal.{u}) : 1 < blockStage ξ :=
  Ordinal.one_lt_omega0.trans_le (omega0_le_blockStage ξ)

/-- **Stable recovery of the donor `D ≠ T`**, at every block stage `λ_{ξ+1}` and every `γ`. -/
theorem isStableRecoveryScheme_donorApex_TD (ξ : Ordinal.{u}) (R : ℕ) (hR : R < 2)
    (γ : Ordinal.{u}) :
    (seedTD (blockStage (ξ + 1)) (one_lt_blockStage' _)).left.IsStableRecoveryScheme
      Fin.castSuccEmb (seedTD (blockStage (ξ + 1)) (one_lt_blockStage' _)).right γ
      (Seed.donorApex (seedTD (blockStage (ξ + 1)) (one_lt_blockStage' _))
        (capTD _ (one_lt_blockStage' _) R hR)
        (donorHyp_TD _ (one_lt_blockStage' _) R hR)).toScheme :=
  Seed.isStableRecoveryScheme_donorApex _ rfl
    (by
      change ∀ z : Fin 5, CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ z = ⊥ ↔ z = 0 ∨ z = 1
      intro z
      fin_cases z <;> simp [CoupledGatedExtensionCounterexample.lab])
    (by rintro z (rfl | rfl) <;> rfl)
    (by
      change (γ : Label.{u}) < visibilityReplace 2 R ⊤
      rw [visibilityReplace_top]
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))

end DonorPair

end VaughtConjecture

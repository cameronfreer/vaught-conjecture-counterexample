/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CapRequestsRecovery
import VaughtConjecture.Continuation.CapRequestsDonorFace
import VaughtConjecture.MainTheorem.CutoffCoatomChosenDonor
import VaughtConjecture.Continuation.TopReadingApexSeed
import VaughtConjecture.Continuation.CapRequestsPrivateMarker

/-!
# Work on h4: first-coatom completions for the calibrated (R4) inputs

Work file (placement later).

**The common face condition forces the cap to the top grade** (`StageType.lt_of_hface`):
for a legal `T⁺` on `m + 1` points with a face along the first `m` points, completeness gives a
cell of every grade `0 < N ≤ m` with scope that face; so the condition `hface` of
`StageType.hasCutoffFirstCoatomCompletions'_of_capFills` (every cell avoiding the last point has
grade below that of the cap) holds only when the cap has grade `m + 1`, the number of points of
`T⁺`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {m : ℕ}

/-- **Completeness puts a cell of every grade `0 < N ≤ m` on the face along the first `m`
points.** -/
theorem exists_grade_eq_of_restrictFace {Tp : StageType.{u} α (m + 1)}
    {p : StageType.{u} α m} (hT : Tp.IsLegal) (hp : restrictFace Fin.castSuccEmb Tp = some p)
    {N : ℕ} (hN0 : 0 < N) (hNm : N ≤ m) :
    ∃ x : Fin Tp.card, Fin.last m ∉ Tp.toCellScheme.scope x ∧ Tp.toCellScheme.grade x = N := by
  obtain ⟨hf, -⟩ := (restrictFace_eq_some_iff Tp Fin.castSuccEmb).mp hp
  obtain ⟨x, hx⟩ := hT.isComplete (univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)), N)
    ⟨hf, hN0, by rw [card_map, card_univ, Fintype.card_fin]; exact hNm⟩
  refine ⟨x, ?_, congrArg Prod.snd hx⟩
  rw [show Tp.toCellScheme.scope x = univ.map Fin.castSuccEmb from congrArg Prod.fst hx]
  simp

/-- **The common face condition forces the cap to the top grade**: if every cell of a legal `T⁺`
on `m + 1` points avoiding its last point has grade below `N > 0`, and `T⁺` has a face along its
first `m` points, then `m < N`. -/
theorem lt_of_hface {Tp : StageType.{u} α (m + 1)} {p : StageType.{u} α m} (hT : Tp.IsLegal)
    (hp : restrictFace Fin.castSuccEmb Tp = some p) {N : ℕ} (hN0 : 0 < N)
    (hface : ∀ x : Fin Tp.card, Fin.last m ∉ Tp.toCellScheme.scope x →
      Tp.toCellScheme.grade x < N) : m < N := by
  by_contra hle
  obtain ⟨x, hx, hxN⟩ := exists_grade_eq_of_restrictFace hT hp hN0 (not_lt.mp hle)
  exact absurd (hface x hx) (by omega)

/-- **A cap at the top grade satisfies the common face condition**: every cell of `T⁺` avoiding its
last point has grade at most `m`, below the grade `m + 1` of the cap. -/
theorem hface_of_grade_eq {Tp : StageType.{u} α (m + 1)} {c : Fin Tp.card}
    (hc : Tp.toCellScheme.grade c = m + 1) (x : Fin Tp.card)
    (hx : Fin.last m ∉ Tp.toCellScheme.scope x) :
    Tp.toCellScheme.grade x < Tp.toCellScheme.grade c := by
  have h1 := Tp.isWellFormed.isWellFormed.grade_le_card x
  have h2 : #(Tp.toCellScheme.scope x) ≤ #((univ : Finset (Fin (m + 1))).erase (Fin.last m)) :=
    card_le_card fun y hy ↦ mem_erase.mpr ⟨fun h ↦ hx (h ▸ hy), mem_univ y⟩
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
  omega

/-- A cell of grade the number of points has full scope. -/
theorem scope_eq_univ_of_grade_eq {n : ℕ} {t : StageType.{u} α n} {c : Fin t.card}
    (hc : t.toCellScheme.grade c = n) : t.toCellScheme.scope c = univ :=
  eq_univ_of_card _ (le_antisymm (card_le_univ _) (by
    have := t.isWellFormed.isWellFormed.grade_le_card c
    rw [Fintype.card_fin]
    omega))

end StageType

/-! ### The apex calibration -/

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

variable (ξ) in
/-- The **apex calibration**: the margin calibration with a floor
(`StageType.GradedCapMarginCalibration'`) together with an **apex cap**, a cell of grade the number
of points of `T⁺` labelled at least `λ_ξ` plus that number.  The clauses of the floor calibration
at a cap of grade `N` hold at every grade at least `N`, so the apex cap carries them all
(`StageType.ApexCapCalibration.exists_floorCapData`). -/
def ApexCapCalibration ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  GradedCapMarginCalibration' ξ Tp f D γ ∧
    ∃ b : Fin Tp.card, Tp.toCellScheme.grade b = m ∧
      ((blockStage ξ + m : Ordinal.{u}) : Label.{u}) ≤ Tp.label b

/-- The root offsets below a grade lie below every larger grade. -/
theorem RootOffsetsBelow.mono {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} {h : Fin k ↪ Fin n}
    {N N' : ℕ} (hr : t.RootOffsetsBelow h N) (hNN : N ≤ N') : t.RootOffsetsBelow h N' :=
  fun y hy μ f hμ hl ↦ (hr y hy μ f hμ hl).trans_le hNN

/-- **The apex calibration gives cap data with a floor at the top grade.** -/
theorem ApexCapCalibration.exists_floorCapData
    {Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)} {f : Fin k ↪ Fin (m + 1)}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} (hT : Tp.IsLegal)
    (h : ApexCapCalibration ξ Tp f D γ) :
    ∃ c : FloorCapData Tp f D γ, Tp.toCellScheme.grade c.cap = m + 1 := by
  obtain ⟨hC, b, hb, hbl⟩ := h
  obtain ⟨c₀⟩ := hC.nonempty_floorCapData hT
  have hN : Tp.toCellScheme.grade c₀.cap ≤ Tp.toCellScheme.grade b := by
    rw [hb]
    exact Tp.grade_le _
  refine ⟨{ c₀ with
    cap := b
    scope_cap := scope_eq_univ_of_grade_eq hb
    le_label_cap := by rw [hb]; exact hbl
    lt_grade_cap := c₀.lt_grade_cap.trans_le hN
    R_lt := c₀.R_lt.trans_le hN
    i_lt := c₀.i_lt.trans_le hN
    grade_marker_le := c₀.grade_marker_le.trans hN
    ref_spec := fun j o ho ↦ by
      obtain ⟨μ, i', hμ, hon, h1, h2, h3, h4⟩ := c₀.ref_spec j o ho
      exact ⟨μ, i', hμ, hon, h1.trans_le hN, h2.trans_le hN, h3.trans hN, h4⟩
    three_le := c₀.three_le.trans hN
    succ_lt := c₀.succ_lt.trans_le hN
    rootOffsetsBelow := c₀.rootOffsetsBelow.mono hN }, hb⟩

/-- **First-coatom completions for the apex calibration from the fills at the top grade** (h4 of
the receiving route at the apex calibration).  At every input at the first coatom satisfying the
apex calibration, for the cap data with a floor at the top grade, the fills from the private coatom
at the grade `m + 1` give first-coatom completions; the common face condition holds at the top
grade (`StageType.hface_of_grade_eq`) and the fills are needed at that grade only. -/
theorem hasCutoffFirstCoatomCompletions_apex_of_topFills
    (h : ∀ ⦃m k : ℕ⦄ (X : FirstCoatomInput.{u} ξ m k) (γ : Ordinal.{u}), 0 < k →
      γ < blockStage (ξ + 1) → ApexCapCalibration ξ X.Tp (X.f.trans Fin.castSuccEmb) X.D γ →
      ∀ c : FloorCapData X.Tp (X.f.trans Fin.castSuccEmb) X.D γ,
        X.Tp.toCellScheme.grade c.cap = m + 1 →
        CapRequests.CapFillBotAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) (m + 1) ∧
          CapRequests.CapFillPosAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) (m + 1)) :
    HasCutoffFirstCoatomCompletions ξ (ApexCapCalibration ξ) := by
  intro m k Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC
  let X : FirstCoatomInput.{u} ξ m k := ⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩
  obtain ⟨c, hc⟩ := hC.exists_floorCapData hT
  obtain ⟨hbot, hpos⟩ := h X γ hk hγ hC c hc
  have hk' (k' : ℕ) (h₁ : X.Tp.toCellScheme.grade c.cap ≤ k') (h₂ : k' ≤ m + 1) : k' = m + 1 := by
    change Tp.toCellScheme.grade c.cap = m + 1 at hc
    change Tp.toCellScheme.grade c.cap ≤ k' at h₁
    omega
  exact X.exists_isCutoffStableRecovery c.toMarginCapData c.three_le (hface_of_grade_eq hc)
    (fun k' h₁ h₂ ↦ hk' k' h₁ h₂ ▸ hbot) fun k' h₁ h₂ ↦ hk' k' h₁ h₂ ▸ hpos

end StageType

/-! ### h4 at the floor calibration, from the fills at the grades from the cap -/

namespace StageType

variable {ξ : Ordinal.{u}}

/-- **First-coatom completions for the margin calibration with a floor from the lift provisions of
the donor coatom and the private fills** (h4 at `StageType.GradedCapMarginCalibration'`, caps of
any grade `N ≥ 3`).  At every calibrated input, some cap data with a floor has, at every grade
`N ≤ k' ≤ m + 1`, the lift provisions from the donor coatom (`univ.erase (castSucc (last m))`) and
the fills from the private coatom; no condition on the common face. -/
theorem hasCutoffFirstCoatomCompletions'_of_fills
    (h : ∀ ⦃m k : ℕ⦄ (X : FirstCoatomInput.{u} ξ m k) (γ : Ordinal.{u}), 0 < k →
      γ < blockStage (ξ + 1) →
      GradedCapMarginCalibration' ξ X.Tp (X.f.trans Fin.castSuccEmb) X.D γ →
      ∃ c : FloorCapData X.Tp (X.f.trans Fin.castSuccEmb) X.D γ,
        ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
          (ProfileTower.BotLiftProvisionOf (X.requests c.toMarginCapData).IsCorrect k'
              (Fin.castSucc (Fin.last m)) ∧
            ProfileTower.CapLiftProvisionOf (X.requests c.toMarginCapData).IsCorrect k'
              (Fin.castSucc (Fin.last m))) ∧
          CapRequests.CapFillBotAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) k' ∧
            CapRequests.CapFillPosAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) k') :
    HasCutoffFirstCoatomCompletions ξ (GradedCapMarginCalibration' ξ) := by
  intro m k Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC
  let X : FirstCoatomInput.{u} ξ m k := ⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩
  obtain ⟨c, hc⟩ := h X γ hk hγ hC
  exact X.exists_isCutoffStableRecovery' c.toMarginCapData c.three_le
    (fun k' h₁ h₂ ↦ (hc k' h₁ h₂).1) (fun k' h₁ h₂ ↦ (hc k' h₁ h₂).2.1)
    fun k' h₁ h₂ ↦ (hc k' h₁ h₂).2.2

/-- **h4 at the floor calibration over a common face dead above the cap**: the lift provisions of
the donor coatom hold when the common face of the seed is dead above the grade of the cap
(`CapRequests.botLiftProvisionOf_donor_le'`, `CapRequests.capLiftProvisionOf_donor_le'`), so only
the private fills remain. -/
theorem hasCutoffFirstCoatomCompletions'_of_fills_isDeadAbove
    (h : ∀ ⦃m k : ℕ⦄ (X : FirstCoatomInput.{u} ξ m k) (γ : Ordinal.{u}), 0 < k →
      γ < blockStage (ξ + 1) →
      GradedCapMarginCalibration' ξ X.Tp (X.f.trans Fin.castSuccEmb) X.D γ →
      ∃ c : FloorCapData X.Tp (X.f.trans Fin.castSuccEmb) X.D γ,
        CapRequests.IsDeadAbove X.seed (Fin.last (m + 1)) (Fin.castSucc (Fin.last m))
          (X.Tp.toCellScheme.grade c.cap) ∧
        ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
          CapRequests.CapFillBotAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) k' ∧
            CapRequests.CapFillPosAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) k') :
    HasCutoffFirstCoatomCompletions ξ (GradedCapMarginCalibration' ξ) := by
  refine hasCutoffFirstCoatomCompletions'_of_fills fun m k X γ hk hγ hC ↦ ?_
  obtain ⟨c, hdead, hc⟩ := h X γ hk hγ hC
  refine ⟨c, fun k' h₁ h₂ ↦ ⟨?_, hc k' h₁ h₂⟩⟩
  have hNm : X.Tp.toCellScheme.grade c.cap ≤ m + 1 := X.Tp.grade_le c.cap
  have hm : 0 < m := by have := c.three_le; omega
  have hxp : Fin.last (m + 1) ∈ (ProfileTower.Pts : Finset (Fin (m + 2))) := by
    simp [ProfileTower.Pts]
  have hxd : Fin.castSucc (Fin.last m) ∈ (ProfileTower.Pts : Finset (Fin (m + 2))) := by
    simp [ProfileTower.Pts]
  have hne : Fin.castSucc (Fin.last m) ≠ Fin.last (m + 1) := Fin.castSucc_ne_last _
  have hgN := X.grade_requests_cap c.toMarginCapData
  rw [← hgN] at h₁ hdead
  exact ⟨CapRequests.botLiftProvisionOf_donor_le' hm (X.scope_requests_cap _) h₁ h₂ hdead hxp
      hxd hne (X.requests_isGraded _),
    CapRequests.capLiftProvisionOf_donor_le' hm (X.requests_isGraded _) (X.scope_requests_cap _)
      h₁ h₂ hdead hxp hxd hne⟩

end StageType

/-! ### h4 with a chosen intermediate coface -/

namespace StageType

variable {ξ : Ordinal.{u}}

namespace FirstCoatomInput

variable {m k : ℕ} (X : FirstCoatomInput.{u} ξ m k) {γ : Ordinal.{u}}

/-- **The lift provisions and fills at an input**, for cap data `c`: at every grade
`N ≤ k' ≤ m + 1` from the grade of the cap, the lift provisions from the donor coatom and the fills
from the private coatom, for the requests of `c`. -/
def HasFills (c : MarginCapData X.Tp X.D γ) : Prop :=
  ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
    (ProfileTower.BotLiftProvisionOf (X.requests c).IsCorrect k' (Fin.castSucc (Fin.last m)) ∧
      ProfileTower.CapLiftProvisionOf (X.requests c).IsCorrect k' (Fin.castSucc (Fin.last m))) ∧
    CapRequests.CapFillBotAt (X.requests c) (Fin.last (m + 1)) k' ∧
      CapRequests.CapFillPosAt (X.requests c) (Fin.last (m + 1)) k'

end FirstCoatomInput

/-- **First-coatom completions with a chosen coface for the margin calibration with a floor**, from
the lift provisions of the donor coatom and the private fills at a chosen intermediate coface. -/
theorem hasCutoffFirstCoatomCompletionsEx'_of_fills
    (h : ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1))
      (p : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
      (P : StageType.{u} (blockStage (ξ + 1)) k) (hT : Tp.IsLegal)
      (hp : restrictFace Fin.castSuccEmb Tp = some p), 0 < k →
      ∀ (hP : restrictFace f p = some P) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1))
        (hD : D ∈ P.cofaces) (γ : Ordinal.{u}), γ < blockStage (ξ + 1) →
      GradedCapMarginCalibration' ξ Tp (f.trans Fin.castSuccEmb) D γ →
      ∃ (tb : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (htb : tb ∈ p.cofaces)
        (htbD : restrictFace (extendByLast f) tb = some D)
        (c : FloorCapData Tp (f.trans Fin.castSuccEmb) D γ),
        (⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩ : FirstCoatomInput.{u} ξ m k).HasFills
          c.toMarginCapData) :
    HasCutoffFirstCoatomCompletionsEx ξ (GradedCapMarginCalibration' ξ) := by
  intro m k Tp p f P hT hp hk hP D hD γ hγ hC
  obtain ⟨tb, htb, htbD, c, hc⟩ := h Tp p f P hT hp hk hP D hD γ hγ hC
  let X : FirstCoatomInput.{u} ξ m k := ⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩
  exact ⟨tb, htb, htbD, X.exists_isCutoffStableRecovery' c.toMarginCapData c.three_le
    (fun k' h₁ h₂ ↦ (hc k' h₁ h₂).1) (fun k' h₁ h₂ ↦ (hc k' h₁ h₂).2.1)
    fun k' h₁ h₂ ↦ (hc k' h₁ h₂).2.2⟩

end StageType

/-! ### Domination by the cap is a condition on the context -/

namespace StageType.FirstCoatomInput

variable {ξ : Ordinal.{u}} {m k : ℕ} (X : FirstCoatomInput.{u} ξ m k) {γ : Ordinal.{u}}
  (c : MarginCapData X.Tp X.D γ)

/-- **The cap of the requests dominates a cell of `T⁺` exactly when it does so in `T⁺`**: the cells
of the graded index of the cap in the amalgam are the cells of `T⁺` of the graded index of the cap,
with the rows of `T⁺`.  So domination by the cap (`CapRequests.CapDominates`), which breaks the lift
at `⊥` from the donor coatom (`CapRequests.not_botLiftProvisionOf_donor`), does not depend on the
intermediate coface `tb`. -/
theorem capDominates_leftCell_iff (a : Fin X.Tp.card) :
    (X.requests c).CapDominates (X.leftCell a) ↔
      ∀ u : Fin X.Tp.card, X.Tp.toCellScheme.gradedIndex u = X.Tp.toCellScheme.gradedIndex c.cap →
        X.Tp.toScheme.rowAt u a ≤ X.Tp.toScheme.rowAt u c.cap := by
  have hrow (u b : Fin X.Tp.card) :
      X.seed.amalgam.toScheme.rowAt (X.leftCell u) (X.leftCell b) = X.Tp.toScheme.rowAt u b := by
    exact rowAt_faceCell X.restrictFace_amalgam_left u b
  have hgi (u : Fin X.Tp.card) : X.seed.amalgam.toCellScheme.gradedIndex (X.leftCell u) =
      ((X.Tp.toCellScheme.scope u).map (Coatom.left m), X.Tp.toCellScheme.grade u) :=
    Prod.ext (X.scope_leftCell u) (X.grade_leftCell u)
  have hgi_iff (u : Fin X.Tp.card) :
      X.seed.amalgam.toCellScheme.gradedIndex (X.leftCell u) =
          X.seed.amalgam.toCellScheme.gradedIndex (X.leftCell c.cap) ↔
        X.Tp.toCellScheme.gradedIndex u = X.Tp.toCellScheme.gradedIndex c.cap := by
    rw [hgi, hgi, Prod.mk.injEq, Prod.mk.injEq, map_inj]
    rfl
  constructor
  · intro hdom u hu
    have h := hdom (X.leftCell u) ((hgi_iff u).mpr hu)
    change _ ≤ X.seed.amalgam.toScheme.rowAt (X.leftCell u) (X.leftCell c.cap) at h
    rwa [hrow, hrow] at h
  · intro h u' hu'
    have hvis : u' ∈ X.seed.amalgam.toScheme.visibleCells (Coatom.left m) := by
      rw [Scheme.mem_visibleCells]
      intro y hy
      have hy' : y ∈ X.seed.amalgam.toCellScheme.scope (X.leftCell c.cap) := by
        have := congrArg Prod.fst hu'
        change X.seed.amalgam.toCellScheme.scope u' =
          X.seed.amalgam.toCellScheme.scope (X.leftCell c.cap) at this
        rw [← this]
        exact mem_coe.mp hy
      rw [scope_leftCell] at hy'
      obtain ⟨z, -, rfl⟩ := mem_map.mp hy'
      exact ⟨z, rfl⟩
    obtain ⟨b₀, rfl⟩ := X.seed.amalgam.toScheme.exists_faceCell_eq
      (comap_toScheme_of_restrictFace X.restrictFace_amalgam_left) hvis
    set b : Fin X.Tp.card := b₀
    change X.seed.amalgam.toCellScheme.gradedIndex (X.leftCell b) = _ at hu'
    change X.seed.amalgam.toScheme.rowAt (X.leftCell b) (X.leftCell a) ≤
      X.seed.amalgam.toScheme.rowAt (X.leftCell b) (X.leftCell c.cap)
    rw [hrow, hrow]
    exact h b ((hgi_iff b).mp hu')

end StageType.FirstCoatomInput

/-! ### The context clause excluding domination -/

namespace StageType

variable {α : Ordinal.{u}} {m : ℕ}

/-- **The cap dominates no live cell of the first coatom** (a clause on the context `T⁺` on `m + 1`
points with cap `b`): for every cell `a` avoiding the last point, of grade at least that of `b`,
reading itself other than `⊥`, and every cell `G` of full scope and the grade of `a`, some cell of
the graded index of `G` reads `b` strictly below `a`. -/
def CapNonDominating (Tp : StageType.{u} α (m + 1)) (b : Fin Tp.card) : Prop :=
  ∀ a G : Fin Tp.card, Fin.last m ∉ Tp.toCellScheme.scope a → Tp.toCellScheme.scope G = univ →
    Tp.toCellScheme.grade a = Tp.toCellScheme.grade G →
    Tp.toCellScheme.grade b ≤ Tp.toCellScheme.grade a → Tp.toScheme.rowAt a a ≠ ⊥ →
      ∃ u, Tp.toCellScheme.gradedIndex u = Tp.toCellScheme.gradedIndex G ∧
        Tp.toScheme.rowAt u b < Tp.toScheme.rowAt u a

namespace FirstCoatomInput

variable {ξ : Ordinal.{u}} {k : ℕ} (X : FirstCoatomInput.{u} ξ m k) {γ : Ordinal.{u}}
  (c : MarginCapData X.Tp X.D γ)

/-- **Under the clause, no live common-face cell is dominated by the cap at its grade**: the input
of the obstructions `CapRequests.not_botLiftProvisionOf_donor` and
`CapRequests.not_botLiftProvisionOf_donor_of_markerCovers` (at the graded index of the cap and, by
`CapRequests.le_cap_of_capDominatesAt`, above it) does not occur. -/
theorem not_capDominatesAt_of_capNonDominating (hnd : X.Tp.CapNonDominating c.cap)
    {a G : Fin X.Tp.card} (ha : Fin.last m ∉ X.Tp.toCellScheme.scope a)
    (hG : X.Tp.toCellScheme.scope G = univ)
    (hag : X.Tp.toCellScheme.grade a = X.Tp.toCellScheme.grade G)
    (hNa : X.Tp.toCellScheme.grade c.cap ≤ X.Tp.toCellScheme.grade a)
    (hlive : X.Tp.toScheme.rowAt a a ≠ ⊥) :
    ¬ (X.requests c).CapDominatesAt (X.leftCell a) (X.leftCell G) := by
  intro hdom
  obtain ⟨u, hu, hlt⟩ := hnd a G ha hG hag hNa hlive
  have hrow (v b : Fin X.Tp.card) :
      X.seed.amalgam.toScheme.rowAt (X.leftCell v) (X.leftCell b) = X.Tp.toScheme.rowAt v b :=
    rowAt_faceCell X.restrictFace_amalgam_left v b
  have hgi : X.seed.amalgam.toCellScheme.gradedIndex (X.leftCell u) =
      X.seed.amalgam.toCellScheme.gradedIndex (X.leftCell G) := by
    rw [Prod.ext_iff] at hu
    refine Prod.ext ?_ ?_
    · change X.seed.amalgam.toCellScheme.scope (X.leftCell u) =
        X.seed.amalgam.toCellScheme.scope (X.leftCell G)
      rw [scope_leftCell, scope_leftCell]
      exact congrArg _ hu.1
    · change X.seed.amalgam.toCellScheme.grade (X.leftCell u) =
        X.seed.amalgam.toCellScheme.grade (X.leftCell G)
      rw [grade_leftCell, grade_leftCell]
      exact hu.2
  have h := hdom (X.leftCell u) hgi
  change _ ≤ X.seed.amalgam.toScheme.rowAt (X.leftCell u) (X.leftCell c.cap) at h
  rw [hrow, hrow] at h
  exact absurd h (not_le.mpr hlt)

end FirstCoatomInput

end StageType

end VaughtConjecture

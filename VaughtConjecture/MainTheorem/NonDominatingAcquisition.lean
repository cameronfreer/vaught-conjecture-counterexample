/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.WorkH4

/-!
# Acquiring a context whose caps dominate no live cell, through a completion

Roadmap, Layer 4 (acquisition) and Layer 3 ((R4) of the table of 3.4).

The donor obstruction (`CapRequests.not_botLiftProvisionOf_donor_of_markerCovers`) is excluded by
a clause on the context, `StageType.CapNonDominating`: no cap of full scope dominates a live cell
of the first coatom at its grade.  The clause depends only on the scheme.  This file acquires it
the way the root bottoms were acquired: the context is a one-point extension, realized by the
saturation clause of a model, whose scheme is the completion of the seed of the type of the
occurrence with itself.  Compiled in this repository (theorem named):

* **The clause on a scheme** (`Scheme.CapNonDominatingAt`): at a point `x` and a cell `c`, every
  cell `a` avoiding `x`, of grade at least that of `c`, reading itself other than `⊥`, is read
  strictly above `c` by some cell of every graded index `(univ, grade a)` present in the scheme.
* **Completions dominating no live cell** (`CompletionNonDominating`, a named hypothesis on seeds,
  not on models): every seed has a completion below the full grade whose completion (with the apex)
  satisfies the clause at the last point for every cell of full scope.  Its same-layer part is
  `ProfileTower.Lvl.Good.rowAt_nextS_natAdd_lt_of_not_agree`; the cross-layer readings and the
  profiles largest at a cell are open.
* **The margin calibration with a non-dominating cap** (`StageType.GradedCapMarginCalibrationND`):
  the margin calibration with a floor, a last point `x` off the root with `univ.erase x` a face,
  and the clause at `x` for every cell of full scope.
* **The calibration with a floor passes to cofaces**
  (`StageType.GradedCapMarginCalibration'.of_restrictFace`).
* **Acquisition** (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMarginND`): a model
  that is not cover-hollow, with top-grade supremum `⊤`, acquires calibrated contexts for the
  calibration with a non-dominating cap, under `CompletionNonDominating`: acquire the margin
  calibration with a floor at an occurrence `w`; extend `w` by one point (high-arity dominance at
  `0`) to an occurrence of type `q₀`; take the completion of the seed of `q₀` with itself given by
  the hypothesis; realize over the extension a coface of `q₀` on its scheme (saturation).  The
  stable type of the realized tuple has face the stable type of `w` along the first points (the
  calibration passes), its last point is new, and its scheme is that of the completion.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ}

/-- **The cell `c` dominates no live cell off the point `x`**: for every cell `a` whose scope
avoids `x`, of grade at least that of `c`, reading itself other than `⊥`, and every cell `G` of
full scope and the grade of `a`, some cell of the graded index of `G` reads `c` strictly below
`a`. -/
def CapNonDominatingAt (S : Scheme.{u} n) (x : Fin n) (c : Fin S.card) : Prop :=
  ∀ a G : Fin S.card, x ∉ S.toCellScheme.scope a → S.toCellScheme.scope G = univ →
    S.toCellScheme.grade a = S.toCellScheme.grade G →
    S.toCellScheme.grade c ≤ S.toCellScheme.grade a → S.rowAt a a ≠ ⊥ →
      ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex G ∧ S.rowAt u c < S.rowAt u a

end Scheme

/-- `StageType.CapNonDominating` is the clause on the scheme at the last point. -/
theorem StageType.capNonDominating_iff {α : Ordinal.{u}} {m : ℕ} (Tp : StageType.{u} α (m + 1))
    (b : Fin Tp.card) : Tp.CapNonDominating b ↔ Tp.toScheme.CapNonDominatingAt (Fin.last m) b :=
  Iff.rfl

/-- **Completions dominating no live cell** (a named hypothesis on seeds): every seed has a
completion below the full grade whose completion, at every limit stage, satisfies
`Scheme.CapNonDominatingAt` at the last point for every cell of full scope. -/
def CompletionNonDominating : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (I : Seed.{u} α m), ∃ F : CompletionBelowFullGrade I,
    ∀ (hα : Order.IsSuccPrelimit α) (c : Fin (F.completion hα).card),
      (F.completion hα).toCellScheme.scope c = univ →
        (F.completion hα).toScheme.CapNonDominatingAt (Fin.last (m + 1)) c

namespace StageType

variable {ξ : Ordinal.{u}}

variable (ξ) in
/-- **The margin calibration with a non-dominating cap**: the margin calibration with a floor
(`StageType.GradedCapMarginCalibration'`), a last point `x` off the root whose complement is a
face, and no cell of full scope dominating a live cell off `x`. -/
def GradedCapMarginCalibrationND ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  GradedCapMarginCalibration' ξ Tp f D γ ∧
    ∃ x : Fin m, (x : ℕ) + 1 = m ∧ (∀ i, f i ≠ x) ∧ univ.erase x ∈ Tp.toCellScheme.faces ∧
      ∀ c : Fin Tp.card, Tp.toCellScheme.scope c = univ → Tp.toScheme.CapNonDominatingAt x c

/-- **The margin calibration with a floor passes to cofaces**: if `T` has face `W` along `e`, the
calibration of `W` along `f` is that of `T` along `f.trans e` (the cells of `W` are cells of `T`
with their labels and grades, and the cells visible through `f.trans e` are those of `W` visible
through `f`). -/
theorem GradedCapMarginCalibration'.of_restrictFace {m n k : ℕ}
    {T : StageType.{u} (blockStage (ξ + 1)) n} {W : StageType.{u} (blockStage (ξ + 1)) m}
    {e : Fin m ↪ Fin n} (he : restrictFace e T = some W) {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibration' ξ W f D γ) :
    GradedCapMarginCalibration' ξ T (f.trans e) D γ := by
  obtain ⟨b, hb, hk, h3, ⟨R, hR, hγ⟩, ⟨a, i, hi, ha, hal⟩, href, hoff⟩ := h
  have hg (z : Fin W.card) := grade_faceCell he z
  have hl (z : Fin W.card) := label_faceCell he z
  refine ⟨faceCell he b, by rw [hg, hl]; exact hb, by rw [hg]; exact hk, by rw [hg]; exact h3,
    ⟨R, by rw [hg]; exact hR, hγ⟩, ⟨faceCell he a, i, by rw [hg]; exact hi,
      by rw [hg, hg]; exact ha, by rw [hl]; exact hal⟩, fun j o ho ↦ ?_, fun y hy μ f' hμ hyl ↦ ?_⟩
  · obtain ⟨μ, n', i', c, hμ, ho', hn, hi', hc, hcl⟩ := href j o ho
    exact ⟨μ, n', i', faceCell he c, hμ, ho', by rw [hg]; exact hn, by rw [hg]; exact hi',
      by rw [hg, hg]; exact hc, by rw [hl]; exact hcl⟩
  · -- a cell visible through `f.trans e` is a cell of `W` visible through `f`
    have hye : y ∈ T.visibleCells e := by
      rw [Scheme.mem_visibleCells] at hy ⊢
      intro z hz
      obtain ⟨w, hw⟩ := hy hz
      exact ⟨f w, hw⟩
    have hfc : ∃ y', faceCell he y' = y :=
      T.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace he) hye
    obtain ⟨y', rfl⟩ := hfc
    have hy' : y' ∈ W.visibleCells f := by
      rw [Scheme.mem_visibleCells] at hy ⊢
      intro z hz
      have hz' : e z ∈ (T.toCellScheme.scope (faceCell he y') : Set (Fin n)) := by
        rw [scope_faceCell]
        exact mem_coe.mpr (mem_map_of_mem _ (mem_coe.mp hz))
      obtain ⟨w, hw⟩ := hy hz'
      exact ⟨w, e.injective hw⟩
    rw [hg]
    exact hoff y' hy' μ f' hμ (by rw [← hl]; exact hyl)

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Acquisition of the margin calibration with a non-dominating cap**, under
`CompletionNonDominating`, for a model `R` at `λ_ξ` that is not cover-hollow and has top-grade
supremum `⊤`. -/
theorem IsModel.acquiresCalibratedContexts_gradedCapMarginND (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (hND : CompletionNonDominating.{u}) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapMarginCalibrationND ξ) R
      hR.isStablyLawful := by
  intro x hx D hD γ hγ
  have hβ := isSuccLimit_blockStage ξ
  obtain ⟨w, f, hf, hC⟩ := hR.acquiresCalibratedContexts_gradedCapMargin' hnh hgrow x hx D hD γ hγ
  -- one point more, by high-arity dominance at `0`
  obtain ⟨u, hu, q₀, ⟨⟨hq₀l, hq₀f⟩, -⟩, he₀⟩ :=
    (hR.dominance w 0 hβ.bot_lt).inter_cofaces hR.isConsistent hR.isLegal
  set Z₁ : R.Occurrence := ⟨w.arity + 1, u, q₀, he₀⟩
  -- the completion of the seed of `q₀` with itself
  obtain ⟨F, hF⟩ := hND (Seed.ofCoatoms hq₀l hq₀l hq₀f hq₀f)
  set qs := F.completion hβ.isSuccPrelimit
  have hqs : qs ∈ q₀.cofaces :=
    ⟨F.isLegal_completion _, F.restrictFace_left_completion hβ.isSuccPrelimit⟩
  have hne : (Z₁.type.cofaces ∩ StageType.saturationFamily qs.toScheme).Nonempty := ⟨qs, hqs, rfl⟩
  obtain ⟨v, hv, q, ⟨⟨-, hqf⟩, hqS⟩, hev⟩ :=
    (hR.saturation Z₁ qs.toScheme hne).inter_cofaces hR.isConsistent hR.isLegal
  set V : R.Occurrence := ⟨w.arity + 2, v, q, hev⟩
  set g : Fin w.arity ↪ Fin (w.arity + 2) := Fin.castSuccEmb.trans Fin.castSuccEmb
  have hgv : g.trans v = w.tuple := by
    rw [Function.Embedding.trans_assoc, hv]
    exact hu
  -- the stable type of `V` has face the stable type of `w` along the first points
  have hface : StageType.restrictFace g
      (R.stableType hR.isStablyLawful v q hev) =
        some (R.stableType hR.isStablyLawful w.tuple w.type w.eval_tuple) := by
    rw [← isConsistent_stableCandidate hR.isConsistent hR.isCovering v _ g
      (stableCandidate_eval_of_eval hev), hgv]
    exact stableCandidate_eval_of_eval w.eval_tuple
  refine ⟨V, f.trans g, ?_, hC.of_restrictFace hface, Fin.last _, rfl, fun i ↦ ?_, ?_, ?_⟩
  · rw [Function.Embedding.trans_assoc, hgv, hf]
  · simp only [g, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
    exact Fin.castSucc_ne_last _
  · -- the first points span a face: the face of `q` along the first points is the type of `Z₁`
    have h := ((StageType.restrictFace_eq_some_iff q Fin.castSuccEmb).mp hqf).1
    change univ.erase (Fin.last (w.arity + 1)) ∈ q.toCellScheme.faces
    convert h using 1
    exact (Coatom.univ_map_left (m := w.arity)).symm
  · -- the clause holds on the scheme of the completion
    have key : ∀ S : Scheme.{u} (w.arity + 2), S = qs.toScheme → ∀ c : Fin S.card,
        S.toCellScheme.scope c = univ → S.CapNonDominatingAt (Fin.last _) c := by
      rintro S rfl c hc
      exact hF hβ.isSuccPrelimit c hc
    exact key _ hqS
end Realization

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRootBottom
import VaughtConjecture.Continuation.RootBottomDetermination
import VaughtConjecture.Continuation.MarkedCap

/-!
# Acquisition of contexts with the cap at the top grade, conditional on full-top saturation

Roadmap, Layer 3 ((R3) of the table of 3.4) and Layer 4 (cover-hollowness).

**Conditional on `Realization.HollowFullTopSaturation`, a clause on hollow models that is not a
clause of `Realization.IsModel`** (prospective):

* `Realization.fullTopFamily S ρ`: the stage types with scheme `S` labelled `⊤` at every cell of
  full grade at which `ρ` is `⊤`.
* `Realization.HasFullTopSaturation R`: if some one-point coface of the type of an occurrence lies
  in `fullTopFamily S ρ`, a member of that family is realized over the occurrence.
* `Realization.HollowFullTopSaturation`: every model at a limit stage, cover-hollow at a block
  stage, with unbounded growth, has full-top saturation.

These three definitions are those of the raise-test lane (`Continuation/TiedRootCapAcquisition`
there), with the same names and statements.

Compiled in this repository (theorem named):

* `TiedRootCapRelabel.MarkedCapContextBelowTop'`: a context respecting the root bottoms
  (`TiedRootCapRelabel.MarkedCapContextBelow'`) whose top grade is the number of its points (the
  cap is at the top grade).  It is not surjective, and it is invariant under relabelling
  (`Realization.markedCapContextBelowTop'_routeInputs`).
* `StageType.markedCapContextBelowTop'_of_addApex`: a relabelling of an apex type, `⊤` at the apex
  and literal on the root, with the root offsets below the grade of the apex, is such a context.
* `Realization.hollowAcquisition_markedCapContextBelowTop'`: conditional on
  `HollowFullTopSaturation`, hollow acquisition of these contexts: the construction of
  `Realization.rootBottomAcquisition_of_botKeeping` with the realization of the completion of the
  seed of the extended type with itself, `⊤` at its apex, by full-top saturation in place of the
  bottom-pattern clause.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type w}

/-- The **full-top family** of a scheme `S` on `n + 1` points and a labelling `ρ` of its cells:
the stage types with scheme `S` labelled `⊤` at every cell of full grade `n + 1` at which `ρ` is
`⊤`. -/
def fullTopFamily {n : ℕ} (S : Scheme.{u} (n + 1)) (ρ : Fin S.card → Label.{u}) :
    Set (StageType.{u} α (n + 1)) :=
  {q | q.toScheme = S ∧ ∀ (i : Fin q.card) (j : Fin S.card), (i : ℕ) = j →
    q.toCellScheme.grade i = n + 1 → ρ j = ⊤ → q.label i = ⊤}

/-- **Full-top saturation** of a realization (a named clause, prospective: not a clause of
`Realization.IsModel`): generalized saturation (clause 4(a)i) keeping the formal top at the cells
of full grade.  If some one-point coface of the type of an occurrence lies in the full-top family
of `S` and `ρ`, a member of that family is realized over the occurrence.  The bottom-pattern
clause 4(a)ii is the analogue for `⊥` at the cells of grade at most the arity. -/
def HasFullTopSaturation (R : Realization.{u, w} α M) : Prop :=
  ∀ (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) (ρ : Fin S.card → Label.{u}),
    (x.type.cofaces ∩ fullTopFamily S ρ).Nonempty → R.RealizesOver x.tuple (fullTopFamily S ρ)

/-- **Full-top saturation of the hollow models** (a named statement, prospective): every model at
a limit stage that is cover-hollow at a block stage and has unbounded growth has full-top
saturation. -/
def HollowFullTopSaturation : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ (R : Realization.{u, w} α M), Order.IsSuccLimit α →
    R.IsModel → R.IsCoverHollowAtBlock → R.topGradeSup = ⊤ → R.HasFullTopSaturation

end Realization

namespace TiedRootCapRelabel

/-- **Contexts with the cap at the top grade**: contexts respecting the root bottoms whose top
grade is the number of points. -/
def MarkedCapContextBelowTop' {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k)
    (h : Fin n ↪ Fin k) : Prop :=
  MarkedCapContextBelow' t' h ∧ t'.topGrade = k

end TiedRootCapRelabel

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **A relabelling of an apex type, `⊤` at the apex and literal on the root, is a context with
the cap at the top grade**, when the root offsets lie below the grade of the apex. -/
theorem markedCapContextBelowTop'_of_addApex {t₀ : StageType.{u} α k}
    (ht₀ : t₀.IsLegalBelowFullGrade) (hk : 0 < k) {q : StageType.{u} α k}
    (hS : q.toScheme = (t₀.addApex ht₀ hk).toScheme)
    (htop : ∀ (i : Fin q.card) (j : Fin (t₀.addApex ht₀ hk).card), (i : ℕ) = j →
      q.toCellScheme.grade i = k → (t₀.addApex ht₀ hk).label j = ⊤ → q.label i = ⊤)
    {h : Fin n ↪ Fin k} (hn : n + 1 < k)
    (hl : ∀ (i : Fin q.card) (j : Fin (t₀.addApex ht₀ hk).card), (i : ℕ) = j →
      i ∈ q.visibleCells h → q.label i = (t₀.addApex ht₀ hk).label j)
    (hoff : ∀ y ∈ (t₀.addApex ht₀ hk).visibleCells h, ∀ (μ : Ordinal.{u}) (f : ℕ),
      Order.IsSuccPrelimit μ → (t₀.addApex ht₀ hk).label y = ((μ + f : Ordinal.{u}) : Label.{u}) →
        f < k) :
    TiedRootCapRelabel.MarkedCapContextBelowTop' q h := by
  obtain ⟨S, ℓ, h₁, h₂, h₃, h₄⟩ := q
  change S = _ at hS
  subst hS
  have hl' (i : Fin (t₀.addApex ht₀ hk).card) (hi : i ∈ (t₀.addApex ht₀ hk).visibleCells h) :
      ℓ i = (t₀.addApex ht₀ hk).label i := hl i i rfl hi
  have hg : (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _) = k :=
    congrArg Prod.snd (addApex_gradedIndex_last ht₀ hk)
  have hc : ℓ (Fin.last _) = ⊤ := htop _ _ rfl hg (addApex_label_last ht₀ hk)
  obtain ⟨r, hr⟩ := exists_isMarker (q := ⟨_, ℓ, h₁, h₂, h₃, h₄⟩) (c := Fin.last _) hc
  have hcap : (⟨_, ℓ, h₁, h₂, h₃, h₄⟩ : StageType.{u} α k).IsTopCap (Fin.last _) := by
    refine ⟨addApex_scope_last ht₀ hk, hc, fun x _ ↦ ?_⟩
    change (t₀.addApex ht₀ hk).toCellScheme.grade x ≤
      (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _)
    rw [hg]
    exact (t₀.addApex ht₀ hk).grade_le x
  refine ⟨⟨Fin.last _, r, ⟨hcap, hr, ?_, fun a ha hat ↦ ?_⟩, fun y hy μ f hμ hf ↦ ?_,
    fun y hy hyb ↦ ?_⟩, ?_⟩
  · change n + 1 < (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _)
    rw [hg]
    exact hn
  · have haA : (t₀.addApex ht₀ hk).label a = ⊤ := (hl' a ha).symm.trans hat
    change visibilityReplace ((t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _)) (n + 1)
      ((t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) r) ≤
      (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) a
    rw [hg, rowAt_addApex_last, rowAt_addApex_last, haA]
    exact visibilityReplace_le_of_le hn.le (isSelfVisible_blockEncode_top le_rfl)
      (blockEncode_le_blockEncode_top _)
  · change (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _) > f
    rw [hg]
    exact hoff y hy μ f hμ ((hl' y hy).symm.trans hf)
  · change (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) y = ⊥
    exact (rowAt_addApex_last_eq_bot_iff ht₀ hk y).mpr ((hl' y hy).symm.trans hyb)
  · rw [← hcap.grade_eq_topGrade]
    exact hg

/-- Two stage types on one scheme with the same face along `f` agree at the cells visible through
`f`. -/
theorem label_eq_of_restrictFace_eq' {q D : StageType.{u} α k} (hS : q.toScheme = D.toScheme)
    {f : Fin n ↪ Fin k} {T : StageType.{u} α n} (hq : restrictFace f q = some T)
    (hD : restrictFace f D = some T) (i : Fin q.card) (j : Fin D.card) (hij : (i : ℕ) = j)
    (hi : i ∈ q.visibleCells f) : q.label i = D.label j := by
  obtain ⟨S, ℓ, h₁, h₂, h₃, h₄⟩ := q
  change S = _ at hS
  subst hS
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨z, rfl⟩ := exists_faceCell_eq hq hi
  exact (label_faceCell hq z).trans (label_faceCell hD z).symm

end StageType

namespace Realization

/-- **Hollow acquisition of contexts with the cap at the top grade**, conditional on
`HollowFullTopSaturation`, a clause on hollow models that is not a clause of `IsModel`.  The
construction of `Realization.rootBottomAcquisition_of_botKeeping`: synchronize the root to an
occurrence `Z` of top grade above `n + 1` and the root offsets, extend it by one point (high-arity
dominance at `0`) to `Z₁` of type `q₀`, complete the seed of `q₀` with itself; full-top saturation
realizes over `Z₁` a type on the scheme of the completion, `⊤` at its apex, whose face along the
first points is `q₀`, literal on the root. -/
theorem hollowAcquisition_markedCapContextBelowTop' (hsat : HollowFullTopSaturation.{u, w}) :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelowTop' t' h) where
  exists_context α M R hα hR hH htop n t c hc := by
    have hsatR := hsat R hα hR hH htop
    obtain ⟨ξ, rfl, hhol⟩ := hH
    have hβ := isSuccLimit_blockStage ξ
    set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨K, hK⟩ := StageType.exists_offset_bound t
    obtain ⟨Z, g, hg, hNZ, hKZ, -⟩ := hR.exists_forcing_floor hhol htop K x
    have htZ : StageType.restrictFace g Z.type = some t :=
      Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hg
    have hZtop : Z.type.topGrade ≤ Z.arity := by
      have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
        rw [← StageType.topGrade_eq_zero_iff] at htf
        omega
      obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap (hR.isLegal _ _ Z.eval_tuple) hnt
      rw [← hcc.grade_eq_topGrade]
      exact Z.type.grade_le cc
    -- one point more, by high-arity dominance at `0`
    obtain ⟨u, hu, q₀, ⟨⟨hq₀l, hq₀f⟩, -⟩, he₀⟩ :=
      (hR.dominance Z 0 hβ.bot_lt).inter_cofaces hR.isConsistent hR.isLegal
    set Z₁ : R.Occurrence := ⟨Z.arity + 1, u, q₀, he₀⟩
    -- a completion of the seed of `q₀` with itself
    obtain ⟨F⟩ := (Seed.ofCoatoms hq₀l hq₀l hq₀f hq₀f).nonempty_completionBelowFullGrade
    set qs := F.completion hβ.isSuccPrelimit
    have hqs : qs ∈ q₀.cofaces :=
      ⟨F.isLegal_completion _, F.restrictFace_left_completion hβ.isSuccPrelimit⟩
    -- full-top saturation over `Z₁`
    obtain ⟨v, hv, q, ⟨hqS, hqtop⟩, hev⟩ := hsatR Z₁ qs.toScheme qs.label
      ⟨qs, hqs, rfl, fun i j hij _ hj ↦ by obtain rfl := Fin.ext hij; exact hj⟩
    have hqq₀ : StageType.restrictFace Fin.castSuccEmb q = some q₀ := by
      rw [← hR.isConsistent _ _ _ hev, hv]
      exact Z₁.eval_tuple
    -- the root along `g` followed by the first points
    have hp : StageType.restrictFace (g.trans Fin.castSuccEmb) q₀ = some t := by
      rw [← StageType.restrictFace_trans _ _ _ hq₀f]
      exact htZ
    have hqroot : StageType.restrictFace ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) q =
        some t := by
      rw [← StageType.restrictFace_trans _ _ _ hqq₀]
      exact hp
    have hsroot : StageType.restrictFace ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) qs =
        some t := by
      rw [← StageType.restrictFace_trans _ _ _ hqs.2]
      exact hp
    refine ⟨Z.arity + 2, q, v, (g.trans Fin.castSuccEmb).trans Fin.castSuccEmb,
      covers_of_eval _ hev, ?_, ?_⟩
    · funext i
      have h₁ := DFunLike.congr_fun hv (Fin.castSucc (g i))
      have h₂ := DFunLike.congr_fun hu (g i)
      have h₃ := DFunLike.congr_fun hg i
      simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb] at h₁ h₂ h₃ ⊢
      change v (Fin.castSucc (Fin.castSucc (g i))) = c i
      rw [h₁, h₂, h₃]
      rfl
    · have hl : ∀ (i : Fin q.card) (j : Fin qs.card), (i : ℕ) = j →
          i ∈ q.visibleCells ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) →
            q.label i = qs.label j :=
        StageType.label_eq_of_restrictFace_eq' hqS hqroot hsroot
      refine StageType.markedCapContextBelowTop'_of_addApex (t₀ := F.truncate hβ.isSuccPrelimit)
        F.isLegalBelowFullGrade (Nat.succ_pos _) hqS hqtop
        (by have hx : x.arity = n := rfl; omega) hl fun y hy μ f hμ hf ↦ ?_
      obtain ⟨z, rfl⟩ := StageType.exists_faceCell_eq hsroot hy
      have hf' : qs.label (StageType.faceCell hsroot z) = ((μ + f : Ordinal.{u}) : Label.{u}) := hf
      rw [StageType.label_faceCell] at hf'
      have := hK z μ f hμ hf'
      omega

/-- **The route inputs at the contexts with the cap at the top grade**, conditional on
`HollowFullTopSaturation`, a clause on hollow models that is not a clause of `IsModel`: hollow
acquisition, non-surjectivity, invariance under relabelling. -/
theorem markedCapContextBelowTop'_routeInputs (hsat : HollowFullTopSaturation.{u, w}) :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock
        (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelowTop' t' h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
        TiedRootCapRelabel.MarkedCapContextBelowTop' t' h → ¬ Function.Surjective h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
        (σ : Equiv.Perm (Fin k)), TiedRootCapRelabel.MarkedCapContextBelowTop' t' h →
          TiedRootCapRelabel.MarkedCapContextBelowTop' (t'.reindex σ)
            (h.trans σ.symm.toEmbedding)) :=
  ⟨hollowAcquisition_markedCapContextBelowTop' hsat,
    fun _ _ _ _ _ ht ↦ ht.1.not_surjective,
    fun _ _ _ t' _ σ ht ↦ ⟨ht.1.reindex σ, (StageType.topGrade_reindex t' σ).trans ht.2⟩⟩

end Realization

end VaughtConjecture

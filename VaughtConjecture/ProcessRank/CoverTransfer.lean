/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Karp.PotentialIso
import VaughtConjecture.AlephOne.ChartDefinability

/-!
# Covers at `ω₁` transfer along back-and-forth equivalence of the base structures

For receiving model expansions `R` of `M` and `S` of `N` to stage `ω₁`, on carriers in any two
universes, the covers are read off the base structures at every countable level: a tuple `x` of
`M` back-and-forth equivalent at every countable level to a cover `y` of `p` in `S` is a cover of
`p` in `R` (`ProcessRank.covers_of_forall_bfEquiv`, proved).  This holds for every stage type
`p`, with or without cells labelled `⊤`.

**The proof.**  At each countable block index `η`, the cover `y` of `p` reduces to a cover of the
reduction of `p` to `λ_η` in the reduction of `S`, so it satisfies the block formula of that
reduction (`realizeBlockFormulaOfIsReceivingModelTarget`, valid for every stage type), a formula
of quantifier rank at most `ω · η < ω₁`.  Back-and-forth equivalence at that level carries the
formula to `x` (`BFEquiv_implies_agreeQR`), which is therefore a cover of the same reduction in the
reduction of `R`.  So `x` is injective and typed in `R`, and its type has the reductions of `p`
at every countable block stage; a stage type at `ω₁` is determined by these reductions
(`StageType.eq_of_forall_reduce_blockStage_eq_omega_one`, proved, from
`Label.eq_of_forall_reduce_blockStage_eq` at the limit `ω₁`, since `ω₁ ≤ λ_{ω₁}`).  No formula of
uncountable rank is used.

**Consequences** (proved).

* Matched tuples of a potential isomorphism of the base structures cover the same stage types
  (`ProcessRank.covers_iff_of_mem_family`): matched tuples are back-and-forth equivalent at every
  level (`PotentialIso.family_bfEquiv`).
* **The realized age is an invariant of the base structure**
  (`ProcessRank.exists_covers_iff_of_potentialIso`): if the base structures are potentially
  isomorphic, `R` and `S` cover the same stage types at `ω₁`.  Every tuple on either side is
  matched (`PotentialIso.exists_right`, `PotentialIso.exists_left`).  With the identity potential
  isomorphism, two receiving expansions of one base structure cover the same stage types.

## Placement

The process-rank companion programme (the files `VaughtConjecture/ProcessRank/*.lean`).  This
module imports only the chart definability at `ω₁` and InfinitaryLogic's back-and-forth
equivalence, so that the other parts of the programme can use it alone.
-/

universe u w w'

namespace VaughtConjecture

open Ordinal Order FirstOrder Language

/-- **A stage type at `ω₁` is determined by its reductions to the countable block stages.**  The
labels of a stage type at `ω₁` occur at `λ_{ω₁} ≥ ω₁`, so `Label.eq_of_forall_reduce_blockStage_eq`
applies at the limit `ω₁`. -/
theorem StageType.eq_of_forall_reduce_blockStage_eq_omega_one {k : ℕ}
    {s t : StageType.{u} (ω₁ : Ordinal.{u}) k}
    (h : ∀ ξ < (ω₁ : Ordinal.{u}),
      s.reduce (isSuccPrelimit_blockStage ξ) = t.reduce (isSuccPrelimit_blockStage ξ)) :
    s = t := by
  have hω : IsSuccLimit (ω₁ : Ordinal.{u}) := Cardinal.isSuccLimit_omega 1
  have hle : (ω₁ : Ordinal.{u}) ≤ blockStage ω₁ := le_blockStage _
  have hs := congrArg StageType.toScheme (h 0 hω.pos)
  refine StageType.ext hs fun i j hij ↦ ?_
  exact Label.eq_of_forall_reduce_blockStage_eq hω ((s.atStage i).mono hle)
    ((t.atStage j).mono hle) fun ξ hξ ↦ StageType.label_congr (h ξ hξ) hij

namespace ProcessRank

variable {M : Type w} {N : Type w'} [baseLanguage.{0}.Structure M]
  [baseLanguage.{0}.Structure N] {R : ModelExpansion M ω₁} {S : ModelExpansion N ω₁}

/-- **Covers transfer along back-and-forth equivalence at every countable level.**  For receiving
model expansions `R` of `M` and `S` of `N` to `ω₁`, a tuple `x` of `M` back-and-forth equivalent
in the base language, at every countable level, to a cover `y` of `p` in `S` is a cover of `p` in
`R`. -/
theorem covers_of_forall_bfEquiv (hR : R.1.IsReceivingModel) (hS : S.1.IsReceivingModel)
    {k : ℕ} {x : Fin k → M} {y : Fin k → N}
    (hxy : ∀ ξ < (ω₁ : Ordinal.{0}), BFEquiv (L := baseLanguage.{0}) ξ k x y)
    {p : StageType.{0} (ω₁ : Ordinal.{0}) k} (hy : S.1.Covers p y) : R.1.Covers p x := by
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hred : ∀ η < (ω₁ : Ordinal.{0}), (R.1.reduce (isSuccPrelimit_blockStage η)).Covers
      (p.reduce (isSuccPrelimit_blockStage η)) x := by
    intro η hη
    have hlt : ω * η < (ω₁ : Ordinal.{0}) :=
      (le_add_self : ω * η ≤ ω + ω * η).trans_lt (blockStage_lt_omega_one hη)
    have hφ := (realizeBlockFormulaOfIsReceivingModelTarget S hS hη _ y).2
      (hy.reduce (isSuccPrelimit_blockStage η))
    exact (realizeBlockFormulaOfIsReceivingModelTarget R hR hη _ x).1
      ((BFEquiv_implies_agreeQR _ x y (hxy _ hlt) _ (qrank_blockFormula_le _ hη _)).2 hφ)
  obtain ⟨hinj, h0⟩ := hred 0 hω.pos
  refine ⟨hinj, ?_⟩
  rw [Realization.reduce_eval] at h0
  cases he : R.1.eval ⟨x, hinj⟩ with
  | none => rw [he] at h0; simp at h0
  | some q =>
    refine congrArg some (StageType.eq_of_forall_reduce_blockStage_eq_omega_one fun η hη ↦ ?_)
    obtain ⟨hinj', hη'⟩ := hred η hη
    rw [Realization.reduce_eval, he, Option.map_some] at hη'
    exact Option.some_injective _ hη'

/-- **Matched tuples cover the same stage types**: for a potential isomorphism `P` of the base
structures and receiving model expansions `R` of `M` and `S` of `N` to `ω₁`, the tuples of a pair
of the family of `P` cover the same stage types at `ω₁`. -/
theorem covers_iff_of_mem_family (P : PotentialIso baseLanguage.{0} M N)
    (hR : R.1.IsReceivingModel) (hS : S.1.IsReceivingModel) {k : ℕ} {x : Fin k → M}
    {y : Fin k → N} (hmem : (⟨k, x, y⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family)
    (p : StageType.{0} (ω₁ : Ordinal.{0}) k) : R.1.Covers p x ↔ S.1.Covers p y :=
  ⟨covers_of_forall_bfEquiv hS hR fun ξ _ ↦ (P.family_bfEquiv ξ hmem).symm,
    covers_of_forall_bfEquiv hR hS fun ξ _ ↦ P.family_bfEquiv ξ hmem⟩

/-- **The realized age is an invariant of the base structure**: if the base structures are
potentially isomorphic, receiving model expansions `R` of `M` and `S` of `N` to `ω₁` cover the
same stage types.  Every tuple on either side is matched in the family. -/
theorem exists_covers_iff_of_potentialIso (P : PotentialIso baseLanguage.{0} M N)
    (hR : R.1.IsReceivingModel) (hS : S.1.IsReceivingModel) {k : ℕ}
    (p : StageType.{0} (ω₁ : Ordinal.{0}) k) :
    (∃ x : Fin k → M, R.1.Covers p x) ↔ ∃ y : Fin k → N, S.1.Covers p y := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hmem⟩ := P.exists_right x
    exact ⟨y, (covers_iff_of_mem_family P hR hS hmem p).1 hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hmem⟩ := P.exists_left y
    exact ⟨x, (covers_iff_of_mem_family P hR hS hmem p).2 hy⟩

end ProcessRank

end VaughtConjecture

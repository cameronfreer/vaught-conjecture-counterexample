/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.RankComparison
import InfinitaryLogic.Scott.InternalRankBounds

/-!
# Process rank and internal Scott rank at a limit

Companion programme over the density sentence, process rank `ω₁`: the rank conventions.  For a
structure `M : Type w` of a relational language and a tuple `a` of `M` (repeated coordinates
allowed), write

* `r(a) = orbitRank a`, InfinitaryLogic's orbit rank (a back-and-forth rank; no automorphism
  orbit is meant);
* `R(M) = sup_a (r(a))`, the **process rank**: the rank of every long enough initial segment of
  the semantic Scott process of `M`.  The formal definition is the rank of InfinitaryLogic's
  semantic Scott process, and the identification with the supremum is the theorem
  `isRank_iff_lift_eq_iSup_orbitRank` of the module `InfinitaryLogic.ScottProcess.RankComparison`
  (whose module documentation gives the literature reference).  The supremum is kept explicit,
  `⨆ x, orbitRank x.2`, as in that module;
* `S(M) = sup_a (r(a) + 1) = internalScottRank M`.

Both suprema live in `Ordinal.{w}`.  Always `R(M) ≤ S(M) ≤ R(M) + 1`.  At a limit `λ` (for the
programme, `λ` is the lift of `ω₁`), whether some tuple attains the supremum is exactly what
separates the two values of `S(M)` (InfinitaryLogic's `lift_rank_add_one_eq_internalScottRank_iff`
and `lift_rank_eq_internalScottRank_iff`):

* `S(M) = λ` iff `R(M) = λ` and `r(a) < λ` for every `a`
  (`internalScottRank_eq_iff_of_isSuccLimit`);
* `S(M) = λ + 1` iff `R(M) = λ` and `r(a) = λ` for some `a`
  (`internalScottRank_eq_add_one_iff_of_isSuccLimit`).

So the structures with `R(M) = λ` are exactly those with `S(M) = λ` or `S(M) = λ + 1`
(`iSup_orbitRank_eq_iff_of_isSuccLimit`).  The semantic Scott process of a length `δ > ω₁ + 1`
has rank `ω₁` exactly when `R(M)` is the lift of `ω₁` (`isRank_omegaOne_iff`), and a countable
structure has `R(M)` below the lift of `ω₁` (`iSup_orbitRank_lt_omegaOne_of_countable`).

**Results.**  All proved.
-/

universe u v w

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- **Internal Scott rank at a limit**: for a limit `λ`, the internal Scott rank is `λ` iff the
supremum of the orbit ranks is `λ` and every orbit rank is below `λ`. -/
theorem internalScottRank_eq_iff_of_isSuccLimit {lam : Ordinal.{w}} (hlam : IsSuccLimit lam) :
    internalScottRank (L := L) M = lam ↔
      (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) = lam ∧
        ∀ n (a : Fin n → M), orbitRank (L := L) a < lam := by
  constructor
  · intro hS
    have hlt : ∀ n (a : Fin n → M), orbitRank (L := L) a < lam := fun n a ↦
      (lt_add_one _).trans_le ((orbitRank_add_one_le_internalScottRank a).trans hS.le)
    refine ⟨le_antisymm (iSup_orbitRank_le_iff.2 fun n a ↦ (hlt n a).le) ?_, hlt⟩
    refine le_of_not_gt fun h ↦ ?_
    have h1 := hlam.succ_lt h
    rw [succ_eq_add_one] at h1
    exact (internalScottRank_le_iSup_orbitRank_add_one.trans_lt h1).ne hS
  · rintro ⟨hR, hlt⟩
    refine le_antisymm (internalScottRank_le fun n a ↦ add_one_le_of_lt (hlt n a)) ?_
    exact hR ▸ iSup_orbitRank_le_internalScottRank

/-- **Internal Scott rank one above a limit**: for a limit `λ`, the internal Scott rank is
`λ + 1` iff the supremum of the orbit ranks is `λ` and some orbit rank is `λ`. -/
theorem internalScottRank_eq_add_one_iff_of_isSuccLimit {lam : Ordinal.{w}}
    (hlam : IsSuccLimit lam) :
    internalScottRank (L := L) M = lam + 1 ↔
      (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) = lam ∧
        ∃ (n : ℕ) (a : Fin n → M), orbitRank (L := L) a = lam := by
  constructor
  · intro hS
    have hle : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ lam := fun n a ↦ by
      have h := (orbitRank_add_one_le_internalScottRank (L := L) a).trans hS.le
      rwa [← succ_eq_add_one, ← succ_eq_add_one, succ_le_succ_iff] at h
    have hR : (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) = lam := by
      refine le_antisymm (iSup_orbitRank_le_iff.2 hle) ?_
      have h := hS.symm.le.trans (internalScottRank_le_iSup_orbitRank_add_one (L := L) (M := M))
      rwa [← succ_eq_add_one, ← succ_eq_add_one, succ_le_succ_iff] at h
    refine ⟨hR, by_contra fun hne ↦ ?_⟩
    push Not at hne
    have hlt : ∀ n (a : Fin n → M), orbitRank (L := L) a < lam :=
      fun n a ↦ (hle n a).lt_of_ne (hne n a)
    have h := ((internalScottRank_eq_iff_of_isSuccLimit hlam).2 ⟨hR, hlt⟩).symm.trans hS
    exact (lt_add_one lam).ne h
  · rintro ⟨hR, n, a, ha⟩
    refine le_antisymm ?_ (ha ▸ orbitRank_add_one_le_internalScottRank a)
    exact hR ▸ internalScottRank_le_iSup_orbitRank_add_one

/-- **Process rank at a limit is internal Scott rank `λ` or `λ + 1`**: for a limit `λ`, the
supremum of the orbit ranks is `λ` iff the internal Scott rank is `λ` or `λ + 1`; the first case
is the non-attained one, the second the attained one. -/
theorem iSup_orbitRank_eq_iff_of_isSuccLimit {lam : Ordinal.{w}} (hlam : IsSuccLimit lam) :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) = lam ↔
      internalScottRank (L := L) M = lam ∨ internalScottRank (L := L) M = lam + 1 := by
  rw [internalScottRank_eq_iff_of_isSuccLimit hlam,
    internalScottRank_eq_add_one_iff_of_isSuccLimit hlam]
  refine ⟨fun hR ↦ ?_, fun h ↦ h.elim (fun h ↦ h.1) fun h ↦ h.1⟩
  by_cases h : ∃ (n : ℕ) (a : Fin n → M), orbitRank (L := L) a = lam
  · exact .inr ⟨hR, h⟩
  · push Not at h
    exact .inl ⟨hR, fun n a ↦ (hR ▸ orbitRank_le_iSup_orbitRank a).lt_of_ne (h n a)⟩

/-- **The process of a length beyond `ω₁ + 1` has rank `ω₁`** iff the supremum of the orbit ranks
is the lift of `ω₁` (InfinitaryLogic's `isRank_iff_lift_eq_iSup_orbitRank`). -/
theorem isRank_omegaOne_iff [L.IsRelational] [Infinite M] {δ : Ordinal.{0}}
    (hδ : (ω₁ : Ordinal.{0}) + 1 < δ) :
    (scottProcessOf L M δ (zero_le.trans_lt hδ)).IsRank ω₁ ↔
      (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) =
        Ordinal.lift.{w} (ω₁ : Ordinal.{0}) := by
  rw [isRank_iff_lift_eq_iSup_orbitRank]
  exact ⟨fun h ↦ h.2.symm, fun h ↦ ⟨hδ, h.symm⟩⟩

/-- **A countable structure has countable process rank**: the supremum of the orbit ranks is at
most the lift of the Scott height (InfinitaryLogic's `orbitRank_le_lift_scottHeight`), which is
below `ω₁` (`scottHeight_lt_omega1`). -/
theorem iSup_orbitRank_lt_omegaOne_of_countable [L.IsRelational] [Countable (Σ l, L.Relations l)]
    [Countable M] :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) <
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) :=
  (iSup_orbitRank_le_iff.2 fun _ a ↦ orbitRank_le_lift_scottHeight a).trans_lt
    (Ordinal.lift_lt.2 (scottHeight_lt_omega1 (L := L) M))

end VaughtConjecture.ProcessRank

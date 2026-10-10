/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderBase
import VaughtConjecture.Label.GradeOneInterpolation

/-!
# Rank vectors of lawful states and their tables

Roadmap, Layer 3 ((R3) and (R4), the members of the padded grade-one base).

The **value rank** of a label `x` in a labelling `R` of a finite family (`Label.valueRank`) is the
number of distinct values of `R` other than `⊥` at most `x`; the **rank vector** of `R` reads it at
the values of `R` (`Label.rankVector`).  The value rank is monotone, `0` at `⊥`, positive at every
value of `R` other than `⊥`, and at most the size of the family.

**The rank tables of a lawful state are lawful** (`Scheme.isLawful_rankTable`): for a lawful
section `R` of a well-formed scheme and a positive table `f` (monotone, `⊥` at `0`, self-visible
at `1`, positive at the ranks `1, …, H` with the ranks at most `H`), the labelling that reads `f`
at the rank of `R` on the cells of grade one and is `⊥` above is lawful.  Locality at a cell of
grade one is order interpolation (`Label.TransformsTo.comp_one`): the target is the image of the
target of `R` under the monotone map `f ∘ valueRank R`, with the same zero set.  Hence the
compatibility hypothesis of the ladder base holds for members given by rank vectors of lawful states
(`Scheme.rankTablesLawful_rankVector`), and the base on such members is consistent
(`Scheme.isConsistent_ladderBase_rankVector`).

## References

Lawful sections are [Kni26, Definition 2.5.4]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset

namespace Label

variable {ι : Type*} [Fintype ι] (R : ι → Label.{u})

/-- The **rank vector** of `R`: the value rank of `R` (`Label.valueRank`) at each of its values. -/
noncomputable def rankVector (d : ι) : ℕ := valueRank R (R d)

variable {R}

@[simp] theorem valueRank_bot : valueRank R ⊥ = 0 := by
  classical
  simp only [valueRank, card_eq_zero, filter_eq_empty_iff]
  exact fun y _ h ↦ h.1 (le_bot_iff.mp h.2)

theorem rankVector_le (d : ι) : rankVector R d ≤ Fintype.card ι := valueRank_le_card _ _

/-- The rank of a value of `R` is `0` exactly when the value is `⊥`. -/
theorem rankVector_eq_zero_iff (d : ι) : rankVector R d = 0 ↔ R d = ⊥ := by
  classical
  refine ⟨fun h ↦ by_contra fun hd ↦ ?_, fun h ↦ by rw [rankVector, h, valueRank_bot]⟩
  have hmem : R d ∈ (univ.image R).filter fun y ↦ y ≠ ⊥ ∧ y ≤ R d :=
    mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), hd, le_rfl⟩
  rw [rankVector, valueRank, card_eq_zero] at h
  rw [h] at hmem
  exact absurd hmem (notMem_empty _)

/-- The rank vector is monotone along the values. -/
theorem rankVector_le_rankVector {d e : ι} (h : R d ≤ R e) : rankVector R d ≤ rankVector R e :=
  monotone_valueRank R h

end Label

namespace Scheme

open Label

variable {n : ℕ} {S : Scheme.{u} n}

/-- **The rank tables of a lawful state are lawful**: for a lawful section `R` of a well-formed
scheme and a positive table `f` at ranks at most `H`, the labelling reading `f` at the ranks of
`R` on the cells of grade one, `⊥` above, is a lawful section. -/
theorem isLawful_rankTable (hwf : S.IsWellFormed) {R : Fin S.card → Label.{u}}
    (hR : S.rows.IsLawful R) {H : ℕ} (hH : ∀ d, rankVector R d ≤ H) {f : ℕ → Label.{u}}
    (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, IsSelfVisible 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then f (rankVector R d) else ⊥ := by
  have hfb (d : Fin S.card) : f (rankVector R d) = ⊥ ↔ R d = ⊥ := by
    rw [← rankVector_eq_zero_iff (R := R)]
    refine ⟨fun h ↦ by_contra fun h' ↦ hp _ (Nat.pos_of_ne_zero h') (hH d) h, fun h ↦ ?_⟩
    rw [h, h0]
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- order
    split_ifs with hd
    · rw [hd]; exact hv _
    · exact isSelfVisible_bot _
  · -- locality
    by_cases hs : S.toCellScheme.grade s = 1
    swap
    · have hz : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
          min ((fun d ↦ if S.toCellScheme.grade d = 1 then f (rankVector R d) else ⊥) d.1)
            (if S.toCellScheme.grade s = 1 then f (rankVector R s) else ⊥)) = fun _ ↦ ⊥ := by
        funext d; rw [ite_eq_right hs, min_bot_right]
      rw [hz]
      exact TransformsTo.bot _ _
    have hg1 (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        S.toCellScheme.grade d = 1 := by
      have h1 : S.toCellScheme.grade d ≤ 1 := hs ▸ d.2.2
      have h2 := hwf.isWellFormed.grade_pos d.1
      omega
    have hloc := hR.locality s
    have hgr : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
        S.toCellScheme.grade d) = fun _ ↦ 1 := funext hg1
    rw [hgr] at hloc ⊢
    have hvis (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) : IsSelfVisible 1 (R d) :=
      hd ▸ hR.orderly d
    have hqv (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        IsSelfVisible 1 (min (R d) (R s)) := (hvis _ (hg1 d)).min (hvis _ hs)
    have hmin (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        f (valueRank R (min (R d) (R s))) = min (f (rankVector R d)) (f (rankVector R s)) := by
      rw [(monotone_valueRank R).map_min, hf.map_min]; rfl
    have h := hloc.comp_one hqv (θ := fun y ↦ f (valueRank R y)) (hf.comp (monotone_valueRank R))
      (fun d ↦ by rw [hmin]; exact (hv _).min (hv _)) fun d ↦ by
        rcases min_choice (R d) (R s) with h | h <;> rw [h]
        · exact hfb d
        · exact hfb s
    convert h using 2 with d
    rw [hmin, ite_eq_left (hg1 d), ite_eq_left hs]
  · -- availability
    by_cases ht : S.toCellScheme.grade t = 1
    · obtain ⟨u, hu, hle⟩ := hR.availability s t hst hg
      have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
      refine ⟨u, hu, ?_⟩
      simp only [ite_eq_left (hg.trans ht), ite_eq_left hgu]
      exact hf (rankVector_le_rankVector hle)
    · refine ⟨t, rfl, ?_⟩
      simp only [ite_eq_right (hg ▸ ht : ¬ S.toCellScheme.grade s = 1)]
      exact bot_le

/-- **The rank tables of lawful states are lawful at grade one**: members whose rank vectors are
those of lawful sections of a well-formed scheme, with ranks at most `H`, satisfy the
compatibility hypothesis of the ladder base. -/
theorem rankTablesLawful_rankVector {Q : Type} (hwf : S.IsWellFormed)
    {R : Q → Fin S.card → Label.{u}}
    (hR : ∀ a, S.rows.IsLawful (R a)) {H : ℕ} (hH : ∀ a d, rankVector (R a) d ≤ H) :
    RankTablesLawful S H fun a ↦ rankVector (R a) :=
  fun a _ hf h0 hv hp ↦ isLawful_rankTable hwf (hR a) (hH a) hf h0 hv hp

/-- **The ladder base over rank vectors of lawful states is consistent**, at a height at least the
number of cells. -/
theorem isConsistent_ladderBase_rankVector {Q : Type} [Fintype Q] (hS : S.NoFullOne)
    (hwf : S.IsWellFormed) (hcons : S.rows.IsConsistent) {R : Q → Fin S.card → Label.{u}}
    (hR : ∀ a, S.rows.IsLawful (R a)) {H : ℕ} (hH : 0 < H) (hcard : S.card ≤ H) :
    (ladderBase H (fun a ↦ rankVector (R a)) hS).rows.IsConsistent := by
  have hle (a : Q) (d : Fin S.card) : rankVector (R a) d ≤ H :=
    (rankVector_le d).trans (by simpa using hcard)
  exact isConsistent_ladderBase hwf hcons hH hle (rankTablesLawful_rankVector hwf hR hle)

end Scheme

end VaughtConjecture

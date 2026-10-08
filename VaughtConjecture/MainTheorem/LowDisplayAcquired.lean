/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LowDisplayReadingRoute

/-!
# The acquired contexts carry ordinal labels above their grade

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

LOW displays are compiled on the class `StageType.LowBotClass` of the LOW families whose two faces
are labelled `⊥` at every grade in `(K, k]` (`StageType.hasLowDisplaysOn_lowBot`), and the
completed display fails outside it when `K < k` (`StageType.not_lowReadingFamily`).  This file
decides whether the acquisition of (R2) stays in that class: it does not.

**Ordinal labels above the top-grade supremum**
(`Realization.IsModel.exists_occurrence_label_above`, compiled in this repository). In a model at a
positive stage whose top-grade supremum is `K`, for every `N ≥ K` some occurrence of arity `N + 1`
has a cell of grade `N + 1` labelled by an ordinal, neither `⊥` nor `⊤`: the high-arity dominance
clause at `γ = 0` over an occurrence of arity `N` gives a cell of grade `N + 1` labelled above `0`,
and it is not `⊤` since its grade is above the top-grade supremum.

**Every context over it keeps that label** (`Realization.exists_label_above_of_covers`).  By exact
consistency, a cover `c'` of a type `t'` on `k + 1` points extending the occurrence along a root
`h` that is not onto has the type of the occurrence as its face along `h`; the cell of grade `N + 1`
is a cell of `t'`, of grade in `(K, k]`, with the same label.

**The acquisition leaves the class** (`Realization.exists_acquired_not_lowBotClass`, compiled in
this repository).  At a limit stage, in a model with no globally rigid core and top-grade supremum
`K`, the compiled acquisition (`Realization.exists_covers_isSourceGapContextAt`) applied to that
occurrence gives a lost-point-last source-gap context `t'` of grade `K` on `k + 1` points with a
cell of grade in `(K, k]` labelled by an ordinal; no LOW family with this private context lies in
`StageType.LowBotClass` (`Realization.not_lowBotClass_of_label`).  The label belongs to the
context, a type of the model, which a LOW display must have as a face literally, so no truncation
of the display or of the donor removes it: the restriction to `StageType.LowBotClass` does not
compose with the acquisition, and (R2) needs LOW displays at families with ordinal labels above
`K`, where the completed display carries no separator labelled `⊤`
(`StageType.not_lowReadingFamily`).

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace Realization

open StageType

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M}

/-- **Ordinal labels above the top-grade supremum**: in a model at a positive stage with top-grade
supremum `K`, for every `N ≥ K` some occurrence of arity `N + 1` has a cell of grade `N + 1`
labelled neither `⊥` nor `⊤` (the high-arity dominance clause at `γ = 0`). -/
theorem IsModel.exists_occurrence_label_above (hR : R.IsModel) (hα : 0 < α) {K : ℕ}
    (hK : R.topGradeSup = K) {N : ℕ} (hN : K ≤ N) :
    ∃ x : R.Occurrence, x.arity = N + 1 ∧ ∃ d : Fin x.type.card,
      x.type.toCellScheme.grade d = N + 1 ∧ x.type.label d ≠ ⊥ ∧ x.type.label d ≠ ⊤ := by
  obtain ⟨y, rfl⟩ := hR.exists_arity_eq hα N
  obtain ⟨u, -, q, ⟨d, hd, hlt⟩, he⟩ := hR.dominance y 0 hα
  refine ⟨⟨y.arity + 1, u, q, he⟩, rfl, d, hd, ne_bot_of_gt hlt, fun htop ↦ ?_⟩
  have h1 := Occurrence.topGrade_le_topGradeSup (R := R) ⟨y.arity + 1, u, q, he⟩
  rw [hK] at h1
  have h2 : q.toCellScheme.grade d ≤ q.topGrade := grade_le_topGrade htop
  have h3 : q.topGrade ≤ K := by exact_mod_cast h1
  omega

/-- **Every context over an occurrence keeps its cells**: a cover `c'` of `t'` on `k + 1` points
extending the tuple of an occurrence along a root `h` that is not onto has, for every cell of the
occurrence of grade `N + 1`, a cell of the same grade and label, and `N + 1 ≤ k`. -/
theorem exists_label_above_of_covers (hR : R.IsModel) {N : ℕ} (x : R.Occurrence)
    (hx : x.arity = N + 1) {d : Fin x.type.card} {k : ℕ} {t' : StageType.{u} α (k + 1)}
    {c' : Fin (k + 1) → M} {h : Fin x.arity ↪ Fin (k + 1)} (hc' : R.Covers t' c')
    (hcc : c' ∘ h = x.tuple) (hh : ¬ Function.Surjective h) :
    ∃ z : Fin t'.card, t'.toCellScheme.grade z = x.type.toCellScheme.grade d ∧
      t'.label z = x.type.label d ∧ N + 1 ≤ k := by
  have he := hc'.eval_comp hR.isConsistent h.injective
  have hcc' : (⟨c' ∘ h, hc'.injective.comp h.injective⟩ : Fin x.arity ↪ M) = x.tuple :=
    Function.Embedding.ext fun i ↦ congrFun hcc i
  rw [hcc', x.eval_tuple] at he
  have hface : restrictFace h t' = some x.type := he.symm
  refine ⟨faceCell hface d, grade_faceCell hface d, label_faceCell hface d, ?_⟩
  by_contra hlt
  have hcard := Fintype.card_le_of_injective h h.injective
  simp only [Fintype.card_fin] at hcard
  apply hh
  refine ((Fintype.bijective_iff_injective_and_card h).mpr ⟨h.injective, ?_⟩).2
  simp only [Fintype.card_fin]
  omega

/-- **A context with an ordinal label above `K` is outside the class of the faces `⊥` above
`K`.** -/
theorem not_lowBotClass_of_label {K k : ℕ} {t' tb : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {o r : Fin t'.card} {z : Fin t'.card}
    (hzK : K < t'.toCellScheme.grade z) (hzk : t'.toCellScheme.grade z ≤ k)
    (hz : t'.label z ≠ ⊥) : ¬ LowBotClass α K k t' tb p o r :=
  fun ⟨_, _, hl, _⟩ ↦ hz (hl z hzK hzk)

/-- **The acquisition leaves the class of the faces `⊥` above `K`**: at a limit stage, in a model
with no globally rigid core and top-grade supremum `K`, the compiled acquisition
(`exists_covers_isSourceGapContextAt`) applied to an occurrence of arity `K + 1` with a cell of
grade `K + 1` labelled by an ordinal gives a lost-point-last source-gap context of grade `K` on
`k + 1` points with a cell of grade in `(K, k]` not labelled `⊥`; no LOW family with this
private context lies in `StageType.LowBotClass`. -/
theorem exists_acquired_not_lowBotClass (hα : Order.IsSuccLimit α) (hR : R.IsModel)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c) {K : ℕ} (hK : R.topGradeSup = K) :
    ∃ (k : ℕ) (t' : StageType.{u} α (k + 1)) (c' : Fin (k + 1) → M) (n : ℕ)
      (e : Fin n ↪ Fin k), R.Covers t' c' ∧
      (∃ o r, t'.IsSourceGapContextAt K (e.trans Fin.castSuccEmb) (Fin.last k) o r) ∧
      ∃ z : Fin t'.card, K < t'.toCellScheme.grade z ∧ t'.toCellScheme.grade z ≤ k ∧
        t'.label z ≠ ⊥ ∧
        ∀ (tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k) (o r : Fin t'.card),
          ¬ LowBotClass α K k t' tb p o r := by
  obtain ⟨x, hx, d, hd, hb, -⟩ := hR.exists_occurrence_label_above hα.bot_lt hK le_rfl
  obtain ⟨k, t', c', e, hc', hcc', -, o, r, hs⟩ :=
    exists_covers_isSourceGapContextAt hα hR hcore hK (covers_of_eval x.tuple x.eval_tuple)
  have hns : ¬ Function.Surjective (e.trans Fin.castSuccEmb) := fun hsurj ↦ by
    obtain ⟨i, hi⟩ := hsurj (Fin.last k)
    exact (Fin.castSucc_lt_last (e i)).ne hi
  obtain ⟨z, hzg, hzl, hk⟩ := exists_label_above_of_covers hR x hx hc' hcc' hns (d := d)
  refine ⟨k, t', c', _, e, hc', ⟨o, r, hs⟩, z, by omega, by omega, hzl ▸ hb, fun tb p o r ↦
    not_lowBotClass_of_label (by omega) (by omega) (hzl ▸ hb)⟩

end Realization

end VaughtConjecture

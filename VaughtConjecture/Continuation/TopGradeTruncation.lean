/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.Stage.CapGrade

/-!
# Truncation above a top grade

**Truncation above a grade** (`StageType.exists_truncation_topGrade_le`).  At a limit stage, every
stage type `Q₀` and every grade `K` give a stage type `Q` with the scheme of `Q₀` (so legal exactly
when `Q₀` is), of top grade at most `K` (`StageType.topGrade`), and with every face of `Q₀` of top
grade at most `K` as a face along the same embedding, literally.  It is `Q₀` capped above `K`
(`StageType.capAbove`, in `VaughtConjecture.Stage.CapGrade`; its top grade is at most `K`,
`StageType.topGrade_capAbove_le`) at a cap above every label of `Q₀` other than `⊤`
(`StageType.exists_cap_ne_top`), a lawful section by [Kni26, Lemma 2.5.8], which keeps every face
whose cells labelled `⊤` have grade at most `K` (`StageType.restrictFace_capAbove`).

Truncating the exact pinned extension gives the bounded pinned extension
(`StageType.exists_pinned_extension_topGrade_le`, in
`VaughtConjecture.MainTheorem.CoatomExtensionTheorem`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`, beside the top grade
(`VaughtConjecture.Continuation.Terminal`).

## References

Capping a lawful section is [Kni26, Lemma 2.5.8].
-/

universe u

namespace VaughtConjecture

open Label

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **A type capped above `K` has top grade at most `K`.** -/
theorem topGrade_capAbove_le {t : StageType.{u} α n} {K : ℕ} {c : Ordinal.{u}}
    {hc : IsSelfVisible n (c : Label)} {hcα : c < α} :
    (t.capAbove K c hc hcα).topGrade ≤ K :=
  -- the cells of the capped type are those of `t` (same scheme), so `d` is passed as a cell of `t`
  topGrade_le_iff.mpr fun d hd ↦ (capAbove_label_eq_top_iff (t := t) (d := d)).mp hd |>.2

/-- **Truncation above a grade**: at a limit stage, a stage type `t` and a grade `K` give a stage
type with the scheme of `t`, legal exactly when `t` is, of top grade at most `K`, and with every
face of `t` of top grade at most `K` as a face along the same embedding, labels included. -/
theorem exists_truncation_topGrade_le (hα : Order.IsSuccLimit α) (t : StageType.{u} α n) (K : ℕ) :
    ∃ q : StageType.{u} α n, q.toScheme = t.toScheme ∧ (q.IsLegal ↔ t.IsLegal) ∧
      q.topGrade ≤ K ∧ ∀ ⦃m : ℕ⦄ (f : Fin m ↪ Fin n) (p : StageType.{u} α m),
        restrictFace f t = some p → p.topGrade ≤ K → restrictFace f q = some p := by
  obtain ⟨c, hcα, hc, hct⟩ := exists_cap_ne_top hα t n
  exact ⟨t.capAbove K c hc hcα, rfl, Iff.rfl, topGrade_capAbove_le,
    fun _ _ _ hp hpK ↦ restrictFace_capAbove hct hp fun _ hi ↦ (grade_le_topGrade hi).trans hpK⟩

end StageType

end VaughtConjecture

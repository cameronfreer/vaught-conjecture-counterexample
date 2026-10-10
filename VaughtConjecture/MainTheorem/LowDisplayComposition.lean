/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowFullGradeAll
import VaughtConjecture.MainTheorem.LowDisplayRoute

/-!
# LOW displays for the LOW families with `K ≥ k`

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

The owner of a LOW family `(t', tb)` on `k + 1` points has grade `K ≤ k + 1`
(`StageType.IsLowFamily.grade_le_succ`).  The two cases with `K ≥ k` are compiled here with no
hypothesis (`StageType.hasLowDisplaysOn_ge`):

* `K = k + 1` (the owner of full grade): `StageType.hasLowDisplaysOn_fullGradeAll`;
* `K = k`: `StageType.hasLowDisplaysOn_eq`, from `StageType.hasLowDisplaysOn_lowBotAll` (there is
  no grade in `(K, k]`, so the faces are vacuously `⊥` there).

The case `K < k` is the padded tower (`StageType.hasLowDisplaysOn_lt`), and
`StageType.hasLowDisplays_of_padded` assembles the two
(`VaughtConjecture.MainTheorem.LowPaddedRoute`).
The earlier conditional forms of this file, from the lifts of the state tower
(`StageType.hasLowDisplays_of_stateTowerLifts`) and from the steps for states above the
controllers (`StageType.hasLowDisplays_of_stateStepsAbove`), whose conclusion
`StageType.HasLowDisplays` is now proved with no hypothesis, remain on the research branch
`research/port-low-padded`.

## References

The LOW construction is that of [AFK26]; the displays and generalized saturation are those of
[Kni26, §4.3].
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {k : ℕ}

/-- **The owner of a LOW family has grade at most `k + 1`.** -/
theorem IsLowFamily.grade_le_succ {K : ℕ} {t' tb : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {o r : Fin t'.card} (hF : IsLowFamily K t' tb p o r) : K ≤ k + 1 :=
  hF.isSourceGapContextAt.grade_owner ▸ t'.grade_le o

/-- **LOW displays at `K = k`, for every family**: there is no grade in `(K, k]`
(`StageType.hasLowDisplaysOn_lowBotAll`). -/
theorem hasLowDisplaysOn_eq : HasLowDisplaysOn.{u} fun _ K k _ _ _ _ _ ↦ K = k := by
  intro α K k t' tb p o r hα hF hKk
  subst hKk
  exact hasLowDisplaysOn_lowBotAll t' tb p o r hα hF
    ⟨le_rfl, fun _ h1 h2 ↦ absurd (h1.trans_le h2) (lt_irrefl _),
      fun _ h1 h2 ↦ absurd (h1.trans_le h2) (lt_irrefl _)⟩

/-- **LOW displays at `K ≥ k`, for every family** (`K = k + 1`:
`StageType.hasLowDisplaysOn_fullGradeAll`; `K = k`: `StageType.hasLowDisplaysOn_eq`). -/
theorem hasLowDisplaysOn_ge : HasLowDisplaysOn.{u} fun _ K k _ _ _ _ _ ↦ k ≤ K := by
  intro α K k t' tb p o r hα hF hkK
  rcases Nat.lt_or_eq_of_le (hF.grade_le_succ) with hlt | heq
  · exact hasLowDisplaysOn_eq t' tb p o r hα hF (by omega)
  · exact hasLowDisplaysOn_fullGradeAll t' tb p o r hα hF heq

end VaughtConjecture.StageType

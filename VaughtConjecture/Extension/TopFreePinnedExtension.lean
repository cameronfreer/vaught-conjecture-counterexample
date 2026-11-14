/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Stage.Cap

/-!
# The top-free pinned extension at a limit stage

**The exact pinned extension, capped.**  At a limit stage `α`, let `P` be a legal top-free stage
type on `n` points, `f` a closed face of `P` with restriction `p`, and `d` a legal top-free
one-point coface of `p`.  Some legal top-free stage type `Q` on `n + 1` points restricts to `P`
along the initial segment and to `d` along `extendByLast f`
(`StageType.exists_isTopFree_pinned_extension`): both faces are kept literally, labels included.

The proof is the exact pinned extension (`StageType.exists_pinned_extension`, with the coatom
extension property of `StageType.hasApexCoatomExtensions`, compiled at every stage that is zero or
a limit) capped at an ordinal below `α`, self-visible at `n + 1` and above every label of `P` and
of `d` (`StageType.exists_cap`, `StageType.restrictFace_cap`); it is the composition of
`StageType.exists_isTopFree_amalgam` (`VaughtConjecture.ClassicalLimit.Amalgamation`) with the
pinned extension in place of the amalgam.

Both top-freeness hypotheses are used: the cap bounds the labels of `P` and of `d`, and a cap
below a top label of `d` would change `d`.  The stage is a limit (`Order.IsSuccLimit α`), so that
it is zero or a limit for the pinned extension and nonzero for the cap.

## Placement

This file belongs to Layer 3 of `roadmap/README.md` (row 6 of the table of Layer 3, 3.4, with a
top-free donor); it is the finite step of the exact countable attachment of the `ℵ₁` companion
construction (`VaughtConjecture.AlephOne.OptionAttachment`).
-/

universe u

namespace VaughtConjecture.StageType

/-- **Target: the top-free pinned extension at a limit stage.**  At a limit stage `α`, for a
legal top-free stage type `P` on `n` points, a closed face `f` of `P` with restriction `p`, and a
legal top-free one-point coface `d` of `p`, some legal top-free stage type `Q` on `n + 1` points
restricts to `P` along the initial segment and to `d` along `extendByLast f`.  Proved
(`StageType.isTopFreePinnedExtensionTarget`). -/
def IsTopFreePinnedExtensionTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄, Order.IsSuccLimit α →
    ∀ ⦃P : StageType.{u} α n⦄, P.IsLegal → P.IsTopFree →
    ∀ ⦃f : Fin m ↪ Fin n⦄ ⦃p : StageType.{u} α m⦄ ⦃d : StageType.{u} α (m + 1)⦄,
      restrictFace f P = some p → d.IsLegal → d.IsTopFree →
      restrictFace Fin.castSuccEmb d = some p →
        ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ Q.IsTopFree ∧
          restrictFace Fin.castSuccEmb Q = some P ∧ restrictFace (extendByLast f) Q = some d

/-- **The top-free pinned extension at a limit stage**: the exact pinned extension
(`StageType.exists_pinned_extension`) capped at an ordinal below `α`, self-visible at `n + 1` and
above every label of `P` and of `d` (`StageType.exists_cap`); capping keeps legality
(`StageType.isLegal_cap`), makes the extension top-free (`StageType.isTopFree_cap`) and keeps both
faces (`StageType.restrictFace_cap`). -/
theorem exists_isTopFree_pinned_extension {α : Ordinal.{u}} {n m : ℕ}
    (hα : Order.IsSuccLimit α) {P : StageType.{u} α n} (hP : P.IsLegal) (hPt : P.IsTopFree)
    {f : Fin m ↪ Fin n} {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)}
    (hPf : restrictFace f P = some p) (hd : d.IsLegal) (hdt : d.IsTopFree)
    (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ Q.IsTopFree ∧
      restrictFace Fin.castSuccEmb Q = some P ∧ restrictFace (extendByLast f) Q = some d := by
  obtain ⟨Q₀, hQ₀, hQP, hQd⟩ := exists_pinned_extension
    (hasApexCoatomExtensions hα.isSuccPrelimit).hasCoatomExtensions hP hPf hd hdp
  obtain ⟨c, hcα, hc, hPc, hdc⟩ := exists_cap hα.isSuccPrelimit
    (by simpa [Ordinal.bot_eq_zero] using hα.bot_lt) hPt hdt (n + 1)
  exact ⟨Q₀.cap c hc hcα, hQ₀, isTopFree_cap, restrictFace_cap hQP hPc, restrictFace_cap hQd hdc⟩

/-- **The top-free pinned extension at a limit stage**, the target form
(`StageType.exists_isTopFree_pinned_extension`). -/
theorem isTopFreePinnedExtensionTarget : IsTopFreePinnedExtensionTarget.{u} :=
  fun _ _ _ hα _ hP hPt _ _ _ hPf hd hdt hdp ↦
    exists_isTopFree_pinned_extension hα hP hPt hPf hd hdt hdp

end VaughtConjecture.StageType

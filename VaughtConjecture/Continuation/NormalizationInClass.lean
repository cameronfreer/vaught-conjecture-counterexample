/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Continuation.StableReceiving
import VaughtConjecture.Realization.ReceivingInClass

/-!
# Normalization in a class of stage types

Roadmap, Layer 4, outputs 1–2 of higher-stage reconstruction, restricted to a class of stage types
(`VaughtConjecture.Realization.ReceivingInClass`); semantic contract, items 7 and 12.  All results
here are native constructions of this repository.

Write `λ_η = blockStage η`.  The normalization interface of
`VaughtConjecture.Continuation.Normalization` uses finite-extension receiving for every legal donor
and forcing donors that are only legal.  Here both are restricted to a class `𝒮` of stage types
(`𝒮 : ∀ {α n}, StageType α n → Prop`):

* **forcing donors in `𝒮`** (`ForcingDonorsIn 𝒮 η`): `ForcingDonors η` for inputs in `𝒮`, with
  donors in `𝒮`; for the class of legal stage types this is `ForcingDonors η`
  (`forcingDonorsIn_isLegal_iff`);
* the realization at `λ_{η+1}` has its types in `𝒮` (`∀ x : R.Occurrence, 𝒮 x.type`) and
  finite-extension receiving in `𝒮` (`Realization.HasFiniteExtensionReceivingIn 𝒮`).

Under these, with exact consistency and legal types, the statements of the normalization interface
hold with the same conclusions: the threshold lemma
(`Realization.le_label_iff_exists_forcesThreshold_in`), normalization of labels
(`Realization.label_eq_stableLabel_in`), determination by the reduction
(`Realization.eq_of_reduce_eq_of_forcingDonorsIn`), and the identification of the realization with
the stable candidate of its reduction (`Realization.eq_stableCandidate_of_reduce_eq_in`, and, with
covering, the stable lawfulness of the reduction derived from exact consistency, covering and legal
types, `Realization.eq_stableCandidate_of_reduce_eq_in_of_isCovering`).  The stable offset and its
family of rooted covers (`Realization.stableOffset`, `Realization.ExtendsToCover`) are those of
`VaughtConjecture.Continuation.Normalization`, unchanged: only the donors are restricted.

The proofs are those of the unrestricted statements.  The class of the input `t` comes from the
class of the types of the realization (`t` is the type of the occurrence `c`), and the donor `D`
given by forcing donors in `𝒮` is received by finite-extension receiving in `𝒮`
(`Realization.HasFiniteExtensionReceivingIn.extendsToCover_reduce`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Ordinal

/-! ### Forcing donors in a class -/

/-- **Forcing donors in a class** `𝒮` at the block index `η`: for every legal stage type `t` at
`λ_{η+1}` in `𝒮`, every cell `d` of `t` reducing to the formal top at `λ_η` and every `n` with
`λ_η + n ≤ t.label d`, some legal stage type `D` at `λ_{η+1}` in `𝒮` has `t` as its face along some
`g`, and `(D↓λ_η, g)` forces `n` at `d`. -/
def ForcingDonorsIn (𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop)
    (η : Ordinal.{u}) : Prop :=
  ∀ ⦃k : ℕ⦄ (t : StageType.{u} (blockStage (η + 1)) k), t.IsLegal → 𝒮 t → ∀ d : Fin t.card,
    (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤ → ∀ n : ℕ,
      ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d →
        ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin k ↪ Fin m),
          D.IsLegal ∧ 𝒮 D ∧ StageType.restrictFace g D = some t ∧
          StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
            (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η)) d n

/-- **Forcing donors in the class of legal stage types are forcing donors.** -/
theorem forcingDonorsIn_isLegal_iff {η : Ordinal.{u}} :
    ForcingDonorsIn (fun t ↦ t.IsLegal) η ↔ ForcingDonors.{u} η := by
  refine ⟨fun h k t ht d hd n hn ↦ ?_, fun h k t ht _ d hd n hn ↦ ?_⟩
  · obtain ⟨m, D, g, hD, -, hg, hF⟩ := h t ht ht d hd n hn
    exact ⟨m, D, g, hD, hg, hF⟩
  · obtain ⟨m, D, g, hD, hg, hF⟩ := h t ht d hd n hn
    exact ⟨m, D, g, hD, hD, hg, hF⟩

namespace Realization

variable {α β : Ordinal.{u}} {M : Type v} {k : ℕ}
  {𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop}

/-- **Realizing a donor's reduction in a class**: as
`Realization.HasFiniteExtensionReceiving.extendsToCover_reduce`, for a donor in the class `𝒮` and
finite-extension receiving in `𝒮`. -/
theorem HasFiniteExtensionReceivingIn.extendsToCover_reduce {R : Realization.{u, v} α M}
    (hrec : R.HasFiniteExtensionReceivingIn 𝒮) (hβ : Order.IsSuccPrelimit β)
    (hβα : Label.IsPermittedCutoff α (β : Label.{u})) {t : StageType.{u} α k} {c : Fin k → M}
    (hc : R.Covers t c) {m : ℕ} {D : StageType.{u} α m} {g : Fin k ↪ Fin m} (hD : D.IsLegal)
    (hD𝒮 : 𝒮 D) (hg : StageType.restrictFace g D = some t) :
    (R.reduce hβ).ExtendsToCover c ⟨m, D.reduce hβ, g⟩ := by
  obtain ⟨u, hu, Q, hQ, huQ⟩ := hrec ⟨c, hc.injective⟩ t hc.eval_eq D g hD hD𝒮 hg β hβα
  refine ⟨u, funext fun i ↦ DFunLike.congr_fun hu i, covers_of_eval u ?_⟩
  rw [reduce_eval, huQ, Option.map_some, StageType.reduce_eq_of_mem_receivingFamily hβ hQ]

/-- The type of a cover is the type of an occurrence, hence in a class containing the types of
the realization. -/
theorem Covers.mem_of_forall_occurrence {R : Realization.{u, v} α M} {t : StageType.{u} α k}
    {c : Fin k → M} (hc : R.Covers t c) (h𝒮 : ∀ x : R.Occurrence, 𝒮 x.type) : 𝒮 t :=
  h𝒮 ⟨k, ⟨c, hc.injective⟩, t, hc.eval_eq⟩

/-! ### The threshold lemma and normalization in a class -/

section Threshold

variable {η : Ordinal.{u}} {R : Realization.{u, v} (blockStage (η + 1)) M}
  {t : StageType.{u} (blockStage (η + 1)) k} {c : Fin k → M}

/-- **The threshold lemma in a class** (native construction): as
`Realization.le_label_iff_exists_forcesThreshold`, for a realization whose types are in the class
`𝒮`, with finite-extension receiving in `𝒮` and forcing donors in `𝒮` at `η`.  Hypotheses by use:
`hR` (soundness, from right to left); `hl`, `h𝒮`, `hd` and `hF` (the donor, from left to right);
`hrec` (realizing the donor's reduction, from left to right); `hc` (both directions). -/
theorem le_label_iff_exists_forcesThreshold_in (hR : R.IsConsistent) (hl : R.HasLegalTypes)
    (h𝒮 : ∀ x : R.Occurrence, 𝒮 x.type) (hrec : R.HasFiniteExtensionReceivingIn 𝒮)
    (hF : ForcingDonorsIn 𝒮 η) (hc : R.Covers t c) (d : Fin t.card)
    (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) (n : ℕ) :
    ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d ↔
      ∃ x : Σ m : ℕ, StageType.{u} (blockStage η) m × (Fin k ↪ Fin m),
        StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) x.2.1 x.2.2
          (t.reduce (isSuccPrelimit_blockStage η)) d n ∧
        (R.reduce (isSuccPrelimit_blockStage η)).ExtendsToCover c x := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hcov⟩ ↦ hc.le_label_of_forcesThreshold hR _ hx hcov⟩
  obtain ⟨m, D, g, hD, hD𝒮, hg, hforce⟩ :=
    hF t (hl _ t hc.eval_eq) (hc.mem_of_forall_occurrence h𝒮) d hd n h
  exact ⟨⟨m, D.reduce _, g⟩, hforce,
    hrec.extendsToCover_reduce _ (isPermittedCutoff_blockStage η) hc hD hD𝒮 hg⟩

/-- **Normalization of labels in a class** (native construction): as
`Realization.label_eq_stableLabel`, for a realization whose types are in the class `𝒮`, with
finite-extension receiving in `𝒮` and forcing donors in `𝒮` at `η`.  The stable label is that of
`VaughtConjecture.Continuation.Normalization`, over all rooted covers. -/
theorem label_eq_stableLabel_in (hR : R.IsConsistent) (hl : R.HasLegalTypes)
    (h𝒮 : ∀ x : R.Occurrence, 𝒮 x.type) (hrec : R.HasFiniteExtensionReceivingIn 𝒮)
    (hF : ForcingDonorsIn 𝒮 η) (hc : R.Covers t c) (d : Fin t.card)
    (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) :
    t.label d = (R.reduce (isSuccPrelimit_blockStage η)).stableLabel (blockStage (η + 1))
      (isSuccPrelimit_blockStage η) c (t.reduce (isSuccPrelimit_blockStage η)) d :=
  Label.eq_of_forall_threshold_iff (t.label_mem_block hd).1 (t.label_mem_block hd).2
    Label.le_ofOffset Label.atStage_ofOffset fun n ↦
      (le_label_iff_exists_forcesThreshold_in hR hl h𝒮 hrec hF hc d hd n).trans
        (coe_add_le_stableLabel_iff (hc.reduce _) hd).symm

end Threshold

section Determination

variable {η : Ordinal.{u}} {R : Realization.{u, v} (blockStage (η + 1)) M}

/-- **Determination by the reduction in a class** (native construction): as
`Realization.eq_of_reduce_eq_of_forcingDonors`, for two realizations at `λ_{η+1}` whose types are
in the class `𝒮`, with finite-extension receiving in `𝒮`, given forcing donors in `𝒮` at `η`. -/
theorem eq_of_reduce_eq_of_forcingDonorsIn (hF : ForcingDonorsIn 𝒮 η)
    {R' : Realization.{u, v} (blockStage (η + 1)) M} (hR : R.IsConsistent)
    (hR' : R'.IsConsistent) (hl : R.HasLegalTypes) (hl' : R'.HasLegalTypes)
    (h𝒮 : ∀ x : R.Occurrence, 𝒮 x.type) (h𝒮' : ∀ x : R'.Occurrence, 𝒮 x.type)
    (hrec : R.HasFiniteExtensionReceivingIn 𝒮) (hrec' : R'.HasFiniteExtensionReceivingIn 𝒮)
    (h : R.reduce (isSuccPrelimit_blockStage η) = R'.reduce (isSuccPrelimit_blockStage η)) :
    R = R' := by
  refine Realization.ext fun u ↦ ?_
  have hu : (R.eval u).map (StageType.reduce · (isSuccPrelimit_blockStage η)) =
      (R'.eval u).map (StageType.reduce · (isSuccPrelimit_blockStage η)) := by
    rw [← reduce_eval, ← reduce_eval, h]
  cases ht : R.eval u with
  | none =>
    rw [ht, Option.map_none] at hu
    exact (Option.map_eq_none_iff.mp hu.symm).symm
  | some t =>
    rw [ht, Option.map_some] at hu
    obtain ⟨t', ht', htt'⟩ := Option.map_eq_some_iff.mp hu.symm
    rw [ht']
    refine congrArg some (StageType.eq_of_reduce_eq_of_threshold_iff htt'.symm
      fun i j hij hi n ↦ ?_)
    have hj : (t'.reduce (isSuccPrelimit_blockStage η)).label j = ⊤ :=
      (StageType.label_congr htt'.symm hij).symm.trans hi
    rw [label_eq_stableLabel_in hR hl h𝒮 hrec hF (covers_of_eval u ht) i hi,
      label_eq_stableLabel_in hR' hl' h𝒮' hrec' hF (covers_of_eval u ht') j hj, h,
      stableLabel_congr htt'.symm hij]

end Determination

/-! ### The stable candidate in a class -/

section Candidate

variable {ξ : Ordinal.{u}} {R : Realization.{u, v} (blockStage ξ) M} {hlaw : R.IsStablyLawful}

/-- **A realization in a class is the candidate of its reduction** (native construction): as
`Realization.eq_stableCandidate_of_reduce_eq`, for an exactly consistent realization `R'` at
`λ_{ξ+1}` with legal types in the class `𝒮`, finite-extension receiving in `𝒮` and reduction `R`,
given forcing donors in `𝒮` at `ξ`. -/
theorem eq_stableCandidate_of_reduce_eq_in (hF : ForcingDonorsIn 𝒮 ξ)
    {R' : Realization.{u, v} (blockStage (ξ + 1)) M} (hR' : R'.IsConsistent)
    (hl' : R'.HasLegalTypes) (h𝒮' : ∀ x : R'.Occurrence, 𝒮 x.type)
    (hrec' : R'.HasFiniteExtensionReceivingIn 𝒮)
    (h : R'.reduce (isSuccPrelimit_blockStage ξ) = R) : R' = R.stableCandidate hlaw := by
  subst h
  refine Realization.ext fun u ↦ ?_
  cases hT : R'.eval u with
  | none =>
    refine (stableCandidate_eval_eq_none_iff.mpr ?_).symm
    rw [reduce_eval, hT, Option.map_none]
  | some T =>
    have hTu : (R'.reduce (isSuccPrelimit_blockStage ξ)).eval u =
        some (T.reduce (isSuccPrelimit_blockStage ξ)) := by
      rw [reduce_eval, hT, Option.map_some]
    rw [stableCandidate_eval_of_eval hTu]
    have heq : (R'.reduce (isSuccPrelimit_blockStage ξ)).stableSection u
        (T.reduce (isSuccPrelimit_blockStage ξ)) = T.label := funext fun d ↦ by
      by_cases hd : (T.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤
      · rw [stableSection_of_eq_top hd]
        exact (label_eq_stableLabel_in hR' hl' h𝒮' hrec' hF (covers_of_eval u hT) d hd).symm
      · rw [stableSection_of_ne_top hd]
        have hlt : Label.reduce (blockStage ξ) (T.label d) < blockStage ξ :=
          ((T.reduce _).atStage d).resolve_right hd
        exact Label.reduce_of_lt (Label.reduce_lt_iff.mp hlt)
    refine congrArg some (StageType.ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    exact (congrFun heq i).symm

/-- **A realization in a class is the candidate of its reduction, with stable lawfulness derived**
(native construction): for an exactly consistent, covering realization `R'` at `λ_{ξ+1}` with legal
types in the class `𝒮` and finite-extension receiving in `𝒮`, given forcing donors in `𝒮` at `ξ`,
the reduction of `R'` to `λ_ξ` is stably lawful (`Realization.isStablyLawful_of_hasLegalTypes`,
from exact consistency, covering and legal types of the reduction) and `R'` is its candidate. -/
theorem eq_stableCandidate_of_reduce_eq_in_of_isCovering (hF : ForcingDonorsIn 𝒮 ξ)
    {R' : Realization.{u, v} (blockStage (ξ + 1)) M} (h𝒮' : ∀ x : R'.Occurrence, 𝒮 x.type)
    (hR' : R'.IsConsistent) (hcov' : R'.IsCovering) (hl' : R'.HasLegalTypes)
    (hrec' : R'.HasFiniteExtensionReceivingIn 𝒮) :
    R' = (R'.reduce (isSuccPrelimit_blockStage ξ)).stableCandidate
      (isStablyLawful_of_hasLegalTypes (hR'.reduce _) (hcov'.reduce _) (hl'.reduce _)) :=
  eq_stableCandidate_of_reduce_eq_in hF hR' hl' h𝒮' hrec' rfl

end Candidate

end Realization

end VaughtConjecture

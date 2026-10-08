/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRequests
import VaughtConjecture.Continuation.GrowthStableRelativeLift
import VaughtConjecture.Label.BlockReading

/-!
# The requests read at stable labels

Roadmap, Layer 3 ((R4), the stable evaluation of the growth carrier).

The stable evaluation (`StageType.HasStableGrowthCarriers`) reads a growth carrier over a legal
stage type `T⁺` at `λ_{ξ+1}`, the stable type of an actual context, through its own labels.  Its
calibration (`StageType.GradedCapMarginCalibration`) gives a cap `b` of grade `N > k` labelled at
least `λ_ξ + N`, `γ < λ_ξ + N`, a marker `λ_ξ + i` and, for each ordinal label `μ + n` of the
donor `D`, `n < N`, a reference cell `μ + i`, `i < N`, of grade at most `N`.

* **The cap has full scope** (`StageType.exists_gradedIndex_univ_le_label`): completeness of `T⁺`
  gives a cell of graded index `(univ, N)`, and availability one labelled at least `b`.
* **The stable reads** (`StageType.GrowthRequests.StableReads`): requests on the scheme of `D` with
  that cap, the marker at the **marker offset `N`** (the threshold itself), and the references of
  the calibration.  The donor's ordinal labels `μ + n` all lie below `λ_ξ + N`, so the reads at the
  labels of `T⁺` are the donor's labels (`StableReads.readExact_label`) and the marker read is
  `λ_ξ + N` (`StableReads.readMarker_label`).  No slack between the donor's finite parts and the
  threshold is needed: the marker read sits at the threshold, above every finite part `n < N`.
* **Admission of the actual state** (`StableReads.correctAt_label`): the labels of `T⁺` and of
  `D` read the requests.  This is the admitted state (the stable private labels with the chosen
  donor); it is a different object from the encoded template of
  `VaughtConjecture.Continuation.GrowthStableTemplate`.
* **The capped relation** (`StableReads.cappedRelation`): every label reading the requests from
  the labels of `T⁺` satisfies the capped relation of `D` at `γ`
  (`StageType.GrowthRequests.cappedRelation_of_correctAt`).
* **Calibration on the class** (`StableReads.classCalibrated`).

`StageType.GradedCapMarginCalibration.exists_stableReads`: the calibration gives stable reads.

## References

The stable labels are those of the continuation of a model at a limit stage, [Kni26, §4.3]; the
reading through a cap is the growth step of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace StageType

variable {α : Ordinal.{u}} {m : ℕ}

/-- **A cap of full scope**: in a legal stage type, every cell `b` lies below a cell of graded index
`(univ, grade b)` labelled at least the label of `b` (completeness and availability). -/
theorem exists_gradedIndex_univ_le_label {T : StageType.{u} α m} (hT : T.IsLegal) (b : Fin T.card) :
    ∃ c : Fin T.card, T.toCellScheme.gradedIndex c = (univ, T.toCellScheme.grade b) ∧
      T.label b ≤ T.label c := by
  have hwf := T.isWellFormed
  have hmem : ((univ : Finset (Fin m)), T.toCellScheme.grade b) ∈ T.toCellScheme.gradedFaces := by
    refine ⟨hwf.univ_mem_faces, hwf.isWellFormed.grade_pos b, ?_⟩
    have h1 := hwf.isWellFormed.grade_le_card b
    exact h1.trans (card_le_card (subset_univ _))
  obtain ⟨w, hw⟩ := hT.isComplete _ hmem
  obtain ⟨c, hc, hle⟩ := T.isLawful.availability b w
    (by rw [show T.toCellScheme.scope w = univ from congrArg Prod.fst hw]; exact subset_univ _)
    (congrArg Prod.snd hw).symm
  exact ⟨c, hc.trans hw, hle⟩

end StageType

namespace StageType.GrowthRequests

variable {ξ : Ordinal.{u}} {m k : ℕ} {Tp : StageType.{u} (blockStage (ξ + 1)) m}
  {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)}

/-- A block start `μ ≤ λ_ξ` plus `x < N` lies below `λ_ξ + N`. -/
theorem add_natCast_lt_blockStage_add {μ : Ordinal.{u}} (hμ : μ ≤ blockStage ξ) {x N : ℕ}
    (hx : x < N) : μ + x < blockStage ξ + N := by
  rcases hμ.lt_or_eq with h | rfl
  · exact ((isSuccPrelimit_blockStage ξ).add_natCast_lt h x).trans_le le_self_add
  · exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hx)

/-- The block start of an ordinal label at `λ_{ξ+1}` is at most `λ_ξ`. -/
theorem le_blockStage_of_add {μ o : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {n : ℕ}
    (ho : o = μ + n) (hlt : o < blockStage (ξ + 1)) : μ ≤ blockStage ξ := by
  by_contra! h
  rw [blockStage_add_one] at hlt
  have hμo : μ < blockStage ξ + ω := (le_self_add.trans ho.ge).trans_lt hlt
  obtain ⟨n', hn'⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 h.le hμo
  have h1 := hμ.add_natCast_lt h n'
  rw [← hn'] at h1
  exact lt_irrefl _ h1

variable (ξ) in
/-- **The stable reads** of a donor `D` at a stage type `T⁺` at `λ_{ξ+1}`: the bottom, exact and
high requests are the cells of `D` labelled `⊥`, an ordinal and `⊤`; the cap has full scope and is
labelled at least `λ_ξ + N` (`N` the threshold, above the root arity `k`); the marker has grade at
most `N`, is labelled `λ_ξ + i` with `i < N`, and is read at the offset `N`; each exact request has
a reference of grade at most `N` labelled `μ + i`, `μ ≤ λ_ξ` zero or a limit, `i < N`, and the
donor's label `μ + n` with `n < N` its offset. -/
structure StableReads (Q : GrowthRequests Tp D.toScheme) : Prop where
  /-- The bottom requests are the cells labelled `⊥`. -/
  mem_bottoms : ∀ j, j ∈ Q.bottoms ↔ D.label j = ⊥
  /-- The exact requests are the cells with an ordinal label. -/
  mem_exacts : ∀ j, j ∈ Q.exacts ↔ D.label j ≠ ⊥ ∧ D.label j ≠ ⊤
  /-- The high requests are the cells labelled `⊤`. -/
  mem_highs : ∀ j, j ∈ Q.highs ↔ D.label j = ⊤
  /-- The cap has full scope. -/
  scope_cap : Tp.toCellScheme.scope Q.cap = univ
  /-- The cap is labelled at least `λ_ξ` plus the threshold. -/
  le_label_cap : ((blockStage ξ + Q.threshold : Ordinal.{u}) : Label.{u}) ≤ Tp.label Q.cap
  /-- The threshold is above the root arity. -/
  arity : k + 1 ≤ Q.threshold
  /-- The marker is read at the threshold. -/
  markerOffset_eq : Q.markerOffset = Q.threshold
  /-- The marker has grade at most the threshold. -/
  grade_marker : Tp.toCellScheme.grade Q.marker ≤ Q.threshold
  /-- The marker is labelled `λ_ξ + i`, `i` below the threshold. -/
  label_marker : ∃ i < Q.threshold,
    Tp.label Q.marker = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})
  /-- The references and offsets of the exact requests. -/
  ref : ∀ j ∈ Q.exacts, Tp.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
    Q.offset j < Q.threshold ∧ ∃ (μ : Ordinal.{u}) (i : ℕ), Order.IsSuccPrelimit μ ∧
      μ ≤ blockStage ξ ∧ i < Q.threshold ∧
      Tp.label (Q.ref j) = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
      D.label j = ((μ + Q.offset j : Ordinal.{u}) : Label.{u})

namespace StableReads

variable {Q : GrowthRequests Tp D.toScheme} (hQ : Q.StableReads ξ)
include hQ

/-- Every `μ + x`, `μ ≤ λ_ξ` a block start, `x` below the threshold, is below the cap's label. -/
theorem lt_label_cap {μ : Ordinal.{u}} (hμ : μ ≤ blockStage ξ) {x : ℕ} (hx : x < Q.threshold) :
    ((μ + x : Ordinal.{u}) : Label.{u}) < Tp.label Q.cap :=
  lt_of_lt_of_le (Label.coe_lt_coe_iff.mpr (add_natCast_lt_blockStage_add hμ hx)) hQ.le_label_cap

/-- The cap is not labelled `⊥`. -/
theorem label_cap_ne_bot : Tp.label Q.cap ≠ ⊥ :=
  ne_bot_of_gt (hQ.lt_label_cap (μ := 0) zero_le (x := 0) (by have := hQ.arity; omega))

/-- **The marker read at the labels of `T⁺`** is `λ_ξ + N`. -/
theorem readMarker_label :
    Q.readMarker Tp.label = ((blockStage ξ + Q.threshold : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨i, hi, hm⟩ := hQ.label_marker
  rw [readMarker, hm, hQ.markerOffset_eq,
    visibilityReplace_add_natCast (isSuccPrelimit_blockStage ξ) hi, min_eq_left hQ.le_label_cap]

/-- **The exact reads at the labels of `T⁺`** are the donor's labels. -/
theorem readExact_label {j : Fin D.card} (hj : j ∈ Q.exacts) :
    Q.readExact Tp.label j = D.label j := by
  obtain ⟨-, hoff, μ, i, hμ, hμξ, hi, hr, hd⟩ := hQ.ref j hj
  rw [readExact, hr, visibilityReplace_add_natCast hμ hi, hd,
    min_eq_left (hQ.lt_label_cap hμξ hoff).le]

/-- The donor's label at an exact request is below the cap's label. -/
theorem label_lt_label_cap {j : Fin D.card} (hj : j ∈ Q.exacts) : D.label j < Tp.label Q.cap := by
  obtain ⟨-, hoff, μ, -, -, hμξ, -, -, hd⟩ := hQ.ref j hj
  rw [hd]
  exact hQ.lt_label_cap hμξ hoff

/-- **Admission of the actual state**: the labels of `T⁺` and of `D` read the requests.  The
admitted state is this pair, not the encoded template. -/
theorem correctAt_label (j : Fin D.card) : Q.CorrectAt Tp.label j (D.label j) := by
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [(hQ.mem_bottoms j).mp hz, min_eq_left bot_le]
  · rw [hQ.readExact_label hf, min_eq_left (hQ.label_lt_label_cap hf).le]
  · rw [(hQ.mem_highs j).mp hy, min_eq_right le_top, readMarker]
    exact min_le_right _ _

/-- **The capped relation from the stable reads**: if `γ < λ_ξ + N`, every label reading the
requests from the labels of `T⁺` satisfies the capped relation of `D` at `γ`. -/
theorem cappedRelation {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + Q.threshold) {j : Fin D.card}
    {ℓ : Label.{u}} (h : Q.CorrectAt Tp.label j ℓ) : CappedRelation D γ j ℓ := by
  have hγc : (γ : Label.{u}) <
      ((blockStage ξ + Q.threshold : Ordinal.{u}) : Label.{u}) := Label.coe_lt_coe_iff.mpr hγ
  refine Q.cappedRelation_of_correctAt (hγc.trans_le hQ.le_label_cap)
    (fun j hj ↦ (hQ.mem_bottoms j).mpr hj) (fun j o ho ↦ ?_)
    (fun j hj ↦ ⟨(hQ.mem_highs j).mpr hj, hQ.readMarker_label ▸ hγc⟩) h
  have hj : j ∈ Q.exacts := (hQ.mem_exacts j).mpr ⟨by rw [ho]; exact WithBot.coe_ne_bot,
    by rw [ho]; exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne⟩
  exact ⟨hj, (hQ.readExact_label hj).trans ho, ho ▸ hQ.label_lt_label_cap hj⟩

/-- **The stable reads are calibrated on the class**, along a root `f` of `T⁺` with face `P`. -/
theorem classCalibrated {f : Fin k ↪ Fin m} {P : StageType.{u} (blockStage (ξ + 1)) k}
    (hP : restrictFace f Tp = some P) : Q.ClassCalibrated hP := by
  refine ⟨fun j ↦ ?_, hQ.scope_cap, hQ.label_cap_ne_bot, fun j hj ↦ ?_,
    ⟨hQ.grade_marker, hQ.markerOffset_eq.le, ?_⟩, fun i ↦ ?_, hQ.arity⟩
  · by_cases hb : D.label j = ⊥
    · exact Or.inl ((hQ.mem_bottoms j).mpr hb)
    by_cases ht : D.label j = ⊤
    · exact Or.inr (Or.inr ((hQ.mem_highs j).mpr ht))
    · exact Or.inr (Or.inl ((hQ.mem_exacts j).mpr ⟨hb, ht⟩))
  · obtain ⟨hg, hoff, μ, i, -, -, -, hr, -⟩ := hQ.ref j hj
    exact ⟨hg, hoff.le, by rw [hr]; exact WithBot.coe_ne_bot⟩
  · obtain ⟨i, -, hm⟩ := hQ.label_marker
    rw [hm]
    exact WithBot.coe_ne_bot
  · rw [grade_faceCell]
    exact (P.grade_le i).trans (by have := hQ.arity; omega)

end StableReads

end StageType.GrowthRequests

namespace StageType

open GrowthRequests

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- **The stable reads from the margin calibration**: at a legal stage type `T⁺` at `λ_{ξ+1}`
calibrated for `D` and `γ` (`StageType.GradedCapMarginCalibration`), some requests on the scheme of
`D` are stable reads with `γ < λ_ξ + N`.  The cap is a cell of full scope above the calibration's
cap (`StageType.exists_gradedIndex_univ_le_label`); the marker and the references are the
calibration's. -/
theorem GradedCapMarginCalibration.exists_stableReads {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (hT : Tp.IsLegal) (hC : GradedCapMarginCalibration ξ Tp f D γ) :
    ∃ Q : GrowthRequests Tp D.toScheme, Q.StableReads ξ ∧ γ < blockStage ξ + Q.threshold := by
  classical
  obtain ⟨b, hb, hk, ⟨R, hR, hγR⟩, ⟨a, i, hi, hga, hal⟩, href⟩ := hC
  set N := Tp.toCellScheme.grade b with hN
  obtain ⟨c, hc, hbc⟩ := exists_gradedIndex_univ_le_label hT b
  have hcN : Tp.toCellScheme.grade c = N := congrArg Prod.snd hc
  -- references and offsets, per donor cell
  have hsel : ∀ j : Fin D.card, ∃ (μ : Ordinal.{u}) (n i' : ℕ) (a' : Fin Tp.card),
      ∀ o : Ordinal.{u}, D.label j = o → Order.IsSuccPrelimit μ ∧ o = μ + n ∧ n < N ∧
        i' < N ∧ Tp.toCellScheme.grade a' ≤ N ∧
        Tp.label a' = ((μ + i' : Ordinal.{u}) : Label.{u}) := by
    intro j
    by_cases hj : ∃ o : Ordinal.{u}, D.label j = o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨μ, n, i', a', hμ, hon, hn, hi', hga', hal'⟩ := href j o ho
      refine ⟨μ, n, i', a', fun o' ho' ↦ ?_⟩
      have : o' = o := Label.coe_inj'.mp (ho'.symm.trans ho)
      subst this
      exact ⟨hμ, hon, hn, hi', hga', hal'⟩
    · exact ⟨0, 0, 0, b, fun o ho ↦ absurd ⟨o, ho⟩ hj⟩
  choose μ n i' a' hsel using hsel
  let Q : GrowthRequests Tp D.toScheme :=
    { cap := c, marker := a, markerOffset := N, bottoms := {j | D.label j = ⊥},
      exacts := {j | D.label j ≠ ⊥ ∧ D.label j ≠ ⊤}, highs := {j | D.label j = ⊤}, ref := a',
      offset := n }
  have hQN : Q.threshold = N := hcN
  refine ⟨Q, ⟨fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl, congrArg Prod.fst hc,
    ?_, ?_, hQN.symm, ?_, ⟨i, ?_⟩, fun j hj ↦ ?_⟩, ?_⟩
  · rw [hQN]; exact hb.trans hbc
  · rw [hQN]; exact hk
  · rw [hQN]; exact hga
  · rw [hQN]; exact ⟨hi, hal⟩
  · -- an exact request
    obtain ⟨hjb, hjt⟩ := hj
    obtain ⟨o, ho⟩ : ∃ o : Ordinal.{u}, D.label j = o := by
      rcases atStage_iff.mp (D.atStage j) with h | ⟨o, -, h⟩ | h
      · exact absurd h hjb
      · exact ⟨o, h.symm⟩
      · exact absurd h hjt
    have hlt : o < blockStage (ξ + 1) := by
      rcases atStage_iff.mp (D.atStage j) with h | ⟨o', ho', h⟩ | h
      · exact absurd h hjb
      · rw [ho] at h
        exact (Label.coe_inj'.mp h) ▸ ho'
      · exact absurd h hjt
    obtain ⟨hμ, hon, hnN, hiN, hgN, hlab⟩ := hsel j o ho
    rw [hQN]
    refine ⟨hgN, hnN, μ j, i' j, hμ, le_blockStage_of_add hμ hon hlt, hiN, hlab, ?_⟩
    rw [ho, hon]
  · rw [hQN]
    exact hγR.trans ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hR))

end StageType

end VaughtConjecture

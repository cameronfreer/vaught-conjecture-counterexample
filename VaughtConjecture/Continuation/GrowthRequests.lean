/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthReferenceCalibration
import VaughtConjecture.Continuation.GrowthStableCarrier

/-!
# Requests read through a cap: the calibration layer of the growth carrier

Roadmap, Layer 3 ((R3) and (R4), the recovered relation).  A growth carrier recovers, from a
section `s` of the context, a relation on the donor that is read through the **cap** `c` of the
context, of grade `N`: every donor cell is a **request** of one of three kinds.

* a **bottom request** `z`: `min (v z) (s c) = ⊥`;
* an **exact request** `f`, read through a **reference cell** `ρ f` of the context at an
  **offset** `off f`: `min (v f) (s c) = min (visibilityReplace N (off f) (s (ρ f))) (s c)`;
* a **high request** `y`, read through a **marker** `a` at the **marker offset** `R`:
  `min (visibilityReplace N R (s a)) (s c) ≤ min (v y) (s c)`.

This is the relation `StageType.GrowthRequests.CorrectAt s`.  It is the same for the two
evaluations; they differ only in the section `s`.

* **Actual labels** (`StageType.HollowReferenceCalibration'.exists_requests`): at the context of
  the hollow reference calibration the cap and the marker are labelled `⊤`, and the references
  `μ + r'` have `r' < N`; so the relation at the labels of the context is exactly
  `ℓ = d j`, the formal top included.
* **Stable labels** (`StageType.GrowthRequests.cappedRelation_of_correctAt`): when the cap's value
  exceeds `γ`, the exact reads are below the cap's value and equal the donor's ordinal labels, and
  the marker reads above `γ`, the relation gives the capped relation of (R4).

## Main statements

* `StageType.GrowthRequests.eq_bot_of_correctAt`, `eq_of_correctAt`, `lt_of_correctAt`: the three
  reads.
* `StageType.HollowReferenceCalibration'.exists_requests`: requests at the hollow reference
  calibration whose relation at the context's labels is exact recovery.
* `StageType.GrowthRequests.cappedRelation_of_correctAt`: the capped relation from the requests.

## References

Visibility replacement is [Kni26, Definition 2.2.3]; the reading through a cap is the growth step
of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Requests** of a donor scheme `D` on `n + 1` points at a context `t'` on `k` points: a cap
and a marker of the context, a marker offset, the bottom, exact and high donor cells, and for each
exact cell a reference cell of the context and an offset. -/
structure GrowthRequests (t' : StageType.{u} α k) (D : Scheme.{u} (n + 1)) where
  /-- The cap; its grade is the threshold of the reads. -/
  cap : Fin t'.card
  /-- The marker. -/
  marker : Fin t'.card
  /-- The marker offset. -/
  markerOffset : ℕ
  /-- The bottom requests. -/
  bottoms : Set (Fin D.card)
  /-- The exact requests. -/
  exacts : Set (Fin D.card)
  /-- The high requests. -/
  highs : Set (Fin D.card)
  /-- The reference cell of an exact request. -/
  ref : Fin D.card → Fin t'.card
  /-- The offset of an exact request. -/
  offset : Fin D.card → ℕ

namespace GrowthRequests

variable {t' : StageType.{u} α k} {D : Scheme.{u} (n + 1)} (Q : GrowthRequests t' D)

/-- The threshold of the reads: the grade of the cap. -/
def threshold : ℕ := t'.toCellScheme.grade Q.cap

/-- The **exact read** at a donor cell from a section `s` of the context: the reference value with
its finite part replaced by the offset at the threshold, capped by the cap's value. -/
noncomputable def readExact (s : Fin t'.card → Label.{u}) (j : Fin D.card) : Label.{u} :=
  min (visibilityReplace Q.threshold (Q.offset j) (s (Q.ref j))) (s Q.cap)

/-- The **marker read** from a section `s` of the context. -/
noncomputable def readMarker (s : Fin t'.card → Label.{u}) : Label.{u} :=
  min (visibilityReplace Q.threshold Q.markerOffset (s Q.marker)) (s Q.cap)

/-- The **relation of the requests** at a donor cell `j` and a label `ℓ`, from a section `s` of
the context. -/
def CorrectAt (s : Fin t'.card → Label.{u}) (j : Fin D.card) (ℓ : Label.{u}) : Prop :=
  (j ∈ Q.bottoms → min ℓ (s Q.cap) = ⊥) ∧ (j ∈ Q.exacts → min ℓ (s Q.cap) = Q.readExact s j) ∧
    (j ∈ Q.highs → Q.readMarker s ≤ min ℓ (s Q.cap))

variable {Q} {s : Fin t'.card → Label.{u}} {j : Fin D.card} {ℓ : Label.{u}}

/-- **The bottom read**: under a cap value other than `⊥`, a bottom request is read as `⊥`. -/
theorem eq_bot_of_correctAt (h : Q.CorrectAt s j ℓ) (hj : j ∈ Q.bottoms) (hc : s Q.cap ≠ ⊥) :
    ℓ = ⊥ := by
  have h0 := h.1 hj
  rcases min_choice ℓ (s Q.cap) with he | he <;> rw [he] at h0
  · exact h0
  · exact absurd h0 hc

/-- **The exact read**: an exact request whose read value `a` is below the cap's value is read as
`a`. -/
theorem eq_of_correctAt (h : Q.CorrectAt s j ℓ) (hj : j ∈ Q.exacts) {a : Label.{u}}
    (ha : Q.readExact s j = a) (hlt : a < s Q.cap) : ℓ = a := by
  have h0 := (h.2.1 hj).trans ha
  rcases le_total ℓ (s Q.cap) with hle | hle
  · rwa [min_eq_left hle] at h0
  · rw [min_eq_right hle] at h0
    exact absurd h0 hlt.ne'

/-- **The high read**: a high request is read above every label below the marker read. -/
theorem lt_of_correctAt (h : Q.CorrectAt s j ℓ) (hj : j ∈ Q.highs) {a : Label.{u}}
    (ha : a < Q.readMarker s) : a < ℓ :=
  ha.trans_le ((h.2.2 hj).trans (min_le_left _ _))

/-- **Visibility replacement in a block**: in the block of `μ`, zero or a limit, a label `μ + r`
with `r` below the threshold `N` is replaced by `μ + m`. -/
theorem visibilityReplace_add_natCast {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {N r : ℕ}
    (hr : r < N) (m : ℕ) :
    visibilityReplace N m (((μ + r : Ordinal.{u})) : Label.{u}) =
      ((μ + m : Ordinal.{u}) : Label.{u}) := by
  rw [visibilityReplace_coe, Ordinal.visibilityReplace_add hμ, Ordinal.visibilityReplace_natCast]
  simp [hr]

end GrowthRequests

/-! ### The actual evaluation: exact recovery -/

/-- **Requests at the hollow reference calibration**: at a context `t'` calibrated along `h` for
`d`, some requests on the scheme of `d` have, at the labels of `t'`, exactly the relation
`ℓ = d j`, the formal top included: bottom cells are bottom requests, cells labelled `⊤` are high
requests read through the marker (labelled `⊤`), and every other cell `μ + m` is an exact request
read through its reference cell `μ + r'`, `r' < N`, at the offset `m`. -/
theorem HollowReferenceCalibration'.exists_requests {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (hC : HollowReferenceCalibration' t' h d) :
    ∃ Q : GrowthRequests t' d.toScheme, t'.label Q.cap = ⊤ ∧
      ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j := by
  classical
  obtain ⟨jj, g, h₀, c, r, -, hmc, hoff, -, href⟩ := hC
  have hcap : t'.label c = ⊤ := hmc.1.2.1
  have hmark : t'.label r = ⊤ := hmc.2.1.1
  -- references and offsets, for the ordinal labels
  have hsel : ∀ j : Fin d.card, ∃ (a : Fin t'.card) (m : ℕ), ∀ o : Ordinal.{u},
      d.label j = o → visibilityReplace (t'.toCellScheme.grade c) m (t'.label a) = o := by
    intro j
    by_cases hj : ∃ o : Ordinal.{u}, d.label j = o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨μ, m, r', a, hμ, hom, -, ha, hal⟩ := href j o ho
      have hr' : r' < t'.toCellScheme.grade c := hoff a ha μ r' hμ hal
      refine ⟨a, m, fun o' ho' ↦ ?_⟩
      have : o' = o := WithTop.coe_injective (WithBot.coe_injective (ho'.symm.trans ho))
      rw [this, hal, hom, GrowthRequests.visibilityReplace_add_natCast hμ hr']
    · exact ⟨c, 0, fun o ho ↦ absurd ⟨o, ho⟩ hj⟩
  choose a m ham using hsel
  let Q : GrowthRequests t' d.toScheme :=
    { cap := c, marker := r, markerOffset := jj + 1, bottoms := {j | d.label j = ⊥},
      exacts := {j | d.label j ≠ ⊥ ∧ d.label j ≠ ⊤}, highs := {j | d.label j = ⊤}, ref := a,
      offset := m }
  refine ⟨Q, hcap, fun j ℓ ↦ ?_⟩
  have hQc : t'.label Q.cap = ⊤ := hcap
  have hQm : t'.label Q.marker = ⊤ := hmark
  simp only [GrowthRequests.CorrectAt, hQc, min_top_right]
  induction hd : d.label j using Label.recBotCoeTop with
  | bot => simp [Q, hd]
  | top =>
    have hr : Q.readMarker t'.label = ⊤ := by
      simp [GrowthRequests.readMarker, hQc, hQm]
    simp [Q, hd, hr]
  | coe o =>
    have hr : Q.readExact t'.label j = o := by
      simp only [GrowthRequests.readExact, hQc, min_top_right]
      exact ham j o hd
    have hb : (o : Label.{u}) ≠ ⊥ := WithBot.coe_ne_bot
    have ht : (o : Label.{u}) ≠ ⊤ := by simp
    simp [Q, hd, hr, hb, ht]


/-! ### The stable evaluation: capped recovery -/

/-- **The capped relation from the requests**: if the cap's value of a section `s` exceeds `γ`,
the bottom cells of a donor `D` are bottom requests, each ordinal label `o` of `D` is an exact
request read as `o` below the cap's value, and each cell labelled `⊤` is a high request with a
marker read above `γ`, then the relation of the requests at `s` gives the capped relation of
`D` at `γ`. -/
theorem GrowthRequests.cappedRelation_of_correctAt {β : Ordinal.{u}} {D : StageType.{u} β (n + 1)}
    {t' : StageType.{u} α k} (Q : GrowthRequests t' D.toScheme) {s : Fin t'.card → Label.{u}}
    {γ : Ordinal.{u}} (hcap : (γ : Label.{u}) < s Q.cap)
    (hbot : ∀ j, D.label j = ⊥ → j ∈ Q.bottoms)
    (hex : ∀ j (o : Ordinal.{u}), D.label j = o →
      j ∈ Q.exacts ∧ Q.readExact s j = o ∧ (o : Label.{u}) < s Q.cap)
    (hhigh : ∀ j, D.label j = ⊤ → j ∈ Q.highs ∧ (γ : Label.{u}) < Q.readMarker s)
    {j : Fin D.card} {ℓ : Label.{u}} (h : Q.CorrectAt s j ℓ) : CappedRelation D γ j ℓ := by
  have hc : s Q.cap ≠ ⊥ := ne_bot_of_gt hcap
  refine ⟨fun hne ↦ ?_, fun htop ↦ ?_⟩
  · induction hd : D.label j using Label.recBotCoeTop with
    | bot => exact eq_bot_of_correctAt h (hbot j hd) hc
    | top => exact absurd hd hne
    | coe o =>
      obtain ⟨hj, hr, hlt⟩ := hex j o hd
      exact eq_of_correctAt h hj hr hlt
  · obtain ⟨hj, hlt⟩ := hhigh j htop
    exact lt_of_correctAt h hj hlt

end StageType

end VaughtConjecture

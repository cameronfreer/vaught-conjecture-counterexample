/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Continuation.Terminal

/-!
# Cover-hollowness, stable-label fixedness, and terminality

Roadmap, Layer 4 (hollowness and its stable-label fixedness formulation; output 3 of higher-stage
reconstruction, the modelhood criterion, and the cover-hollow half of its converse; output 2,
forcing donors); semantic contract, item 8.

Throughout, `R` is a realization at the block stage `λ_ξ = blockStage ξ` on a carrier `M`, and
`λ_{ξ+1} = λ_ξ + ω` is the next block stage.  Stable offsets and stable labels
(`Realization.stableOffset`, `Realization.stableLabel`, in
`VaughtConjecture.Continuation.Normalization`) are those of `R` itself, read at `λ_{ξ+1}`.

**Anchors at the top.**  Let `x` be an occurrence of `R`, `a` a cell of its type labelled the
formal top, and `N : ℕ`.  The triple `(x, a, N)` is an **anchor at the top**
(`Realization.IsTopAnchor`) when no rooted cover of `x` forces `N` at `a`: for every triple
`y = (m, q, f)` such that the tuple of `x` extends along `f` to a cover of `q` in `R`
(`Realization.ExtendsToCover`; these are the rooted covers compatible with `x`), the pair `(q, f)`
does not force the threshold `N` at `a` (`StageType.ForcesThreshold` at `λ_{ξ+1}`).  The threshold
is read at the transported position of `a`: on the face along `f` of a stage type at `λ_{ξ+1}`
reducing to `q`, at the cell at the position of `a`.  Unfolded, every compatible rooted cover
`(q, f)` satisfies one of two alternatives:

* `q` does not restrict along `f` to the type of `x`; then `(q, f)` forces no threshold, and the
  condition holds for it trivially (without exact consistency such covers can occur);
* `q` restricts along `f` to the type of `x`, and some stage type at `λ_{ξ+1}` reducing to `q`
  has, on its face along `f`, a label below `λ_ξ + N` at the position of `a`.

So the reading by a stage type at `λ_{ξ+1}` with a label below `λ_ξ + N` applies only to the
covers whose type restricts along `f` to the type of `x`.  The bound `N` is chosen before the
quantifier over covers, and the condition refers to all stage types reducing to the types of the
covers.

* `N = 0` never gives an anchor (`Realization.not_isTopAnchor_zero`), and an anchor at `N` is one
  at every larger bound (`Realization.IsTopAnchor.mono`).
* An anchor is exactly a finite bound on the stable offset
  (`Realization.isTopAnchor_iff_not_natCast_le_stableOffset`).

**Cover-hollowness.**  `R` **has an anchor at the top** (`Realization.HasTopAnchor`) when some
anchor at the top exists, and `R` is **cover-hollow** (`Realization.IsCoverHollow`) when it has
none.  A realization whose types are top-free is cover-hollow vacuously
(`Realization.isCoverHollow_of_isTopFree`): cover-hollowness is not the assertion that there are no
cells labelled the formal top.

**Cover-hollowness at a block stage.**  Cover-hollowness is defined at block stages only, while
(R3) of the table of Layer 3 (`Realization.HollowReceiving`, in
`VaughtConjecture.Continuation.Comparison`) takes a predicate on realizations at every stage.  A
realization at `α` is **cover-hollow at a block stage** (`Realization.IsCoverHollowAtBlock`) when
`α = λ_ξ` for some `ξ` and it is cover-hollow there; at `λ_ξ` this is cover-hollowness
(`Realization.isCoverHollowAtBlock_iff`), since the block stages are strictly increasing.  Every
successor-limit stage, the only stages at which (R3) applies, is a block stage
(`exists_blockStage_eq_of_isSuccLimit`), so (R3) for this predicate is (R3) for cover-hollowness at
the block stages.

**Stable-label fixedness** (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`): `R` is
cover-hollow exactly when every cell of an occurrence labelled the formal top has the stable label
`⊤`.  Both directions unfold the thresholds of the stable offset
(`Realization.natCast_le_stableOffset_iff`) and the label of an offset
(`Label.ofOffset_eq_top_iff`); the tuple of an occurrence covers its type, and nothing else is used.
The theorem has **no hypothesis**: no exact consistency, covering, modelhood, finite-extension
receiving, (R1) or forcing donors.  When `R` is not cover-hollow, some cell labelled the formal top
has a proper stable label `λ_ξ + i`
(`Realization.exists_stableLabel_eq_coe_add_of_not_isCoverHollow`).

**Relation to the original definition of hollowness.**  The roadmap retains the original anchor
definition of hollowness (roadmap, Layer 4; semantic contract, item 8), with stable-label fixedness
as a theorem for models.  `IsCoverHollow` is a separate predicate, phrased through rooted covers
and forcing; it is not that definition, and no equivalence with it is claimed here.  The
equivalence of `IsCoverHollow` with the original hollowness is still to be proved.  The countable
cover of terminal classes (condition 2, terminal countability; `VaughtConjecture.Expansion.Losses`)
and the modelhood criterion (output 3, `ContinuationCriterion`) are stated with `IsCoverHollow`
elsewhere.  Classification and receiving for `IsCoverHollow` enter there as separate named
hypotheses, the continuation criterion and (R3); neither follows from anything proved here.

**Cover-hollowness from exact receiving** (`Realization.isCoverHollow_of_exactReceivingWithin`).
A realization at `λ_ξ` with legal types and exact receiving of every legal donor
(`Realization.ExactReceivingWithin`, in `VaughtConjecture.Continuation.ExactAge`) is cover-hollow,
conditional on forcing donors at `ξ` (`ForcingDonors`, in
`VaughtConjecture.Continuation.Normalization`).  Forcing donors is used only at legal stage types
at `λ_ξ` read at `λ_{ξ+1}` (`StageType.castLE`): at a cell labelled the formal top, every threshold
is forced by a legal extension (`StageType.exists_forcesThreshold_of_label_eq_top`).  For a cell
`a` labelled the formal top in an occurrence `x` and a bound `N`, the extension of the type of `x`
forcing `N` at `a` is received over `x`, so `(x, a, N)` is not an anchor at the top.

**Terminality of cover-hollow realizations** (`Realization.IsCoverHollow.isTerminalAt`), with no
hypothesis on `R`: no model at `λ_{ξ+1}` reduces to a cover-hollow `R`
(`Realization.IsTerminalAt`, in `VaughtConjecture.Continuation.Terminal`).  Let `R'` be a model at
`λ_{ξ+1}` reducing to `R`.  Uniformity of `R'` at `γ = λ_ξ` gives a cover `u` of a type `q` with a
label `L` in `[λ_ξ, λ_ξ + ω)` at some cell `d`, which is the formal top in the reduction.  Choose
`N` with `L < λ_ξ + N`.  Since `R` has no anchor at the top, some rooted cover of `u` in `R` forces
the threshold `N` at `d`, and soundness (`Realization.Covers.le_label_of_forcesThreshold`, from
exact consistency of `R'` alone) gives `λ_ξ + N ≤ L`, a contradiction.  This is the cover-hollow
half of the converse of output 3: a realization with a model expansion to `λ_{ξ+1}` is not
cover-hollow.  It extends to every model the special case of the stable candidate
(`Realization.not_isModel_stableCandidate_of_isCoverHollow`, in
`VaughtConjecture.Continuation.Candidate`).

The word *anchor* here is unrelated to the anchor of a donor cell in `Extension/Gate` (a private
cell from which a gate reading reads the label of a donor cell).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Ordinal

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v}

section Definitions

variable (R : Realization.{u, v} (blockStage ξ) M)

/-- An **anchor at the top**: the cell `a` of the type of the occurrence `x` is labelled the
formal top, and no rooted cover compatible with `x` forces the threshold `N` at `a`.  A compatible
rooted cover is a triple `y = (m, q, f)` such that the tuple of `x` extends along `f` to a cover of
`q` in `R`; forcing is read at `λ_{ξ+1}`, at the position of `a` on the face along `f`.  A
compatible rooted cover whose type `q` does not restrict along `f` to the type of `x` never
forces, since the first condition of `StageType.ForcesThreshold` is `restrictFace f q = some _`;
without exact consistency such covers can occur, and the condition above holds for them
trivially. -/
def IsTopAnchor (x : R.Occurrence) (a : Fin x.type.card) (N : ℕ) : Prop :=
  x.type.label a = ⊤ ∧ ∀ y : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin x.arity ↪ Fin m),
    R.ExtendsToCover x.tuple y →
      ¬ StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) y.2.1 y.2.2
        x.type a N

/-- The realization **has an anchor at the top**: some occurrence, cell and bound form one. -/
def HasTopAnchor : Prop :=
  ∃ (x : R.Occurrence) (a : Fin x.type.card) (N : ℕ), R.IsTopAnchor x a N

/-- The realization is **cover-hollow**: it has no anchor at the top.  This is not the original
anchor definition of hollowness of the roadmap; their equivalence is still to be proved. -/
def IsCoverHollow : Prop :=
  ¬ R.HasTopAnchor

end Definitions

/-- A realization at `α` is **cover-hollow at a block stage** when `α` is a block stage `λ_ξ` and
the realization is cover-hollow there. -/
def IsCoverHollowAtBlock {α : Ordinal.{u}} {M : Type w} (R : Realization.{u, w} α M) : Prop :=
  ∃ (ξ : Ordinal.{u}) (h : α = blockStage ξ), (h ▸ R).IsCoverHollow

/-- At a block stage, cover-hollowness at a block stage is cover-hollowness. -/
theorem isCoverHollowAtBlock_iff {ξ : Ordinal.{u}} {M : Type w}
    {R : Realization.{u, w} (blockStage ξ) M} : R.IsCoverHollowAtBlock ↔ R.IsCoverHollow := by
  refine ⟨fun ⟨ξ', h, hR⟩ ↦ ?_, fun h ↦ ⟨ξ, rfl, h⟩⟩
  obtain rfl := blockStage_strictMono.injective h
  exact hR

variable {R : Realization.{u, v} (blockStage ξ) M} {x : R.Occurrence} {a : Fin x.type.card}
  {N N' : ℕ}

/-- An anchor at a bound is an anchor at every larger bound: forcing is downward closed. -/
theorem IsTopAnchor.mono (h : R.IsTopAnchor x a N) (hN : N ≤ N') : R.IsTopAnchor x a N' :=
  ⟨h.1, fun y hy hf ↦ h.2 y hy (hf.mono hN)⟩

/-- **No anchor at the bound `0`**: the trivial rooted cover forces `0` at every cell labelled the
formal top. -/
theorem not_isTopAnchor_zero (x : R.Occurrence) (a : Fin x.type.card) : ¬ R.IsTopAnchor x a 0 :=
  fun ⟨ha, h⟩ ↦ h ⟨x.arity, x.type, Function.Embedding.refl _⟩
    ⟨x.tuple, rfl, covers_of_eval _ x.eval_tuple⟩
    (StageType.forcesThreshold_zero (StageType.restrictFace_refl _) ha)

/-- **An anchor is a finite bound on the stable offset**: at a cell labelled the formal top,
`(x, a, N)` is an anchor at the top exactly when `N` exceeds the stable offset of `a` at `x`. -/
theorem isTopAnchor_iff_not_natCast_le_stableOffset (ha : x.type.label a = ⊤) :
    R.IsTopAnchor x a N ↔ ¬ (N : ℕ∞) ≤
      R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a := by
  rw [natCast_le_stableOffset_iff (covers_of_eval _ x.eval_tuple) ha, IsTopAnchor]
  simp only [ha, true_and, not_exists, not_and]
  exact forall_congr' fun y ↦ ⟨fun h hf hy ↦ h hy hf, fun h hy hf ↦ h hf hy⟩

/-- **Stable-label fixedness**: `R` is cover-hollow exactly when every cell of an occurrence that
is labelled the formal top has the stable label `⊤`.  No hypothesis on `R` is needed. -/
theorem isCoverHollow_iff_forall_stableLabel_eq_top :
    R.IsCoverHollow ↔ ∀ (x : R.Occurrence) (a : Fin x.type.card), x.type.label a = ⊤ →
      R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a = ⊤ := by
  simp only [IsCoverHollow, HasTopAnchor, not_exists, stableLabel, Label.ofOffset_eq_top_iff]
  refine forall_congr' fun x ↦ forall_congr' fun a ↦ ⟨fun h ha ↦ ?_, fun h N hN ↦ ?_⟩
  · refine ENat.eq_top_iff_forall_ge.mpr fun N ↦ ?_
    by_contra hN
    exact h N ((isTopAnchor_iff_not_natCast_le_stableOffset ha).mpr hN)
  · exact (isTopAnchor_iff_not_natCast_le_stableOffset hN.1).mp hN ((h hN.1).symm ▸ le_top)

/-- **The attained proper stable label**: if `R` is not cover-hollow, some cell of an occurrence
that is labelled the formal top has the stable label `λ_ξ + i` for some `i : ℕ`. -/
theorem exists_stableLabel_eq_coe_add_of_not_isCoverHollow (h : ¬ R.IsCoverHollow) :
    ∃ (x : R.Occurrence) (a : Fin x.type.card) (i : ℕ), x.type.label a = ⊤ ∧
      R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a =
        ((blockStage ξ + i : Ordinal.{u}) : Label.{u}) := by
  rw [isCoverHollow_iff_forall_stableLabel_eq_top] at h
  push Not at h
  obtain ⟨x, a, ha, hne⟩ := h
  have ho : R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.tuple x.type a ≠
      ⊤ := fun ho ↦ hne (Label.ofOffset_eq_top_iff.mpr ho)
  exact ⟨x, a, _, ha, (ite_eq_right ho : Label.ofOffset _ _ = _)⟩

/-- **A top-free realization is cover-hollow**, vacuously: no cell is labelled the formal top. -/
theorem isCoverHollow_of_isTopFree (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    R.IsCoverHollow :=
  fun ⟨x, a, _, ha, _⟩ ↦ h x a ha

end Realization

/-! ### Forcing every threshold at a cell labelled the formal top -/

namespace StageType

/-- **Every threshold at a top cell is forced by a legal extension**, conditional on forcing donors
at `η`: for a legal stage type `p` at `λ_η` with a cell `d` labelled the formal top and every `n`,
some legal stage type `D` at `λ_η` restricts to `p` along some `g`, and `(D, g)` forces the
threshold `n` at `d`.  Forcing donors is applied to `p` read at `λ_{η+1}` (`StageType.castLE`),
where the label of `d` is still the formal top, so every threshold is below it.

Forcing donors `ForcingDonors η` is not proved here: it is a finite statement of Layer 4,
output 2, still to be proved. -/
theorem exists_forcesThreshold_of_label_eq_top {η : Ordinal.{u}} (hF : ForcingDonors.{u} η)
    {k : ℕ} {p : StageType.{u} (blockStage η) k} (hp : p.IsLegal) {d : Fin p.card}
    (hd : p.label d = ⊤) (n : ℕ) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage η) m) (g : Fin k ↪ Fin m), D.IsLegal ∧
      restrictFace g D = some p ∧
        ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) D g p d n := by
  have hle := (blockStage_lt_blockStage_add_one η).le
  have hβ := isSuccPrelimit_blockStage η
  have hp' : (p.castLE hle).reduce hβ = p := reduce_eq_castLE p hβ le_rfl
  have htop : ((p.castLE hle).reduce hβ).label d = ⊤ :=
    Label.reduce_of_le (by rw [castLE_label, hd]; exact le_top)
  obtain ⟨m, D, g, hD, hDg, hforce⟩ := hF (p.castLE hle) ((isLegal_castLE_iff p hle).mpr hp) d
    htop n (by rw [castLE_label, hd]; exact le_top)
  refine ⟨m, D.reduce hβ, g, hD.reduce hβ, ?_, hforce.congr_root hp' d rfl⟩
  rw [restrictFace_reduce, hDg, Option.map_some, hp']

end StageType

/-! ### Cover-hollowness from exact receiving, and terminality -/

namespace Realization

section Terminality

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Exact receiving of legal donors makes a realization cover-hollow**, conditional on forcing
donors at `ξ`: at a cell `a` labelled the formal top in an occurrence `x`, every bound `N` is
forced by a legal extension of the type of `x`
(`StageType.exists_forcesThreshold_of_label_eq_top`), which is received over `x`, so `(x, a, N)`
is not an anchor at the top.

Forcing donors `ForcingDonors ξ` is not proved here: it is a finite statement of Layer 4,
output 2, still to be proved. -/
theorem isCoverHollow_of_exactReceivingWithin (hF : ForcingDonors.{u} ξ) (hl : R.HasLegalTypes)
    (h : R.ExactReceivingWithin fun m ↦ {D : StageType.{u} (blockStage ξ) m | D.IsLegal}) :
    R.IsCoverHollow := by
  rintro ⟨x, a, N, ha, hno⟩
  obtain ⟨m, D, g, hD, hDg, hforce⟩ :=
    StageType.exists_forcesThreshold_of_label_eq_top hF (hl _ _ x.eval_tuple) ha N
  obtain ⟨v, hv, hvg⟩ := h x.type x.tuple (covers_of_eval _ x.eval_tuple) D g hD hDg
  exact hno ⟨m, D, g⟩ ⟨v, hvg, hv⟩ hforce

/-- A label in the block `[β, β + ω)` is below `β + n` for some `n`. -/
private theorem exists_lt_coe_add_of_lt_coe_add_omega0 {β : Ordinal.{u}} {L : Label.{u}}
    (h₁ : (β : Label.{u}) ≤ L) (h₂ : L < ((β + ω : Ordinal.{u}) : Label.{u})) :
    ∃ n : ℕ, L < ((β + n : Ordinal.{u}) : Label.{u}) := by
  induction L using WithBot.recBotCoe with
  | bot => exact absurd h₁ (not_le.mpr (WithBot.bot_lt_coe _))
  | coe L =>
    induction L using WithTop.recTopCoe with
    | top => exact absurd h₂ (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe o =>
      have ho : o < β + ω := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h₂)
      obtain ⟨c, hc, hoc⟩ := (Ordinal.lt_add_iff Ordinal.omega0_ne_zero).mp ho
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
      refine ⟨n + 1, WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hoc.trans_lt ?_))⟩
      exact add_lt_add_right (by exact_mod_cast Nat.lt_succ_self n) β

/-- **Cover-hollow realizations are terminal**, with no hypothesis: no model at `λ_{ξ+1}` reduces
to a cover-hollow realization at `λ_ξ`.  Uniformity of such a model `R'` at `γ = λ_ξ` gives a cover
of a type with a label `L` in `[λ_ξ, λ_ξ + ω)` at a cell that is the formal top in the reduction;
cover-hollowness gives, for every `N`, a rooted cover forcing `N` there, and soundness
(`Realization.Covers.le_label_of_forcesThreshold`, from exact consistency of `R'`) gives
`λ_ξ + N ≤ L` for every `N`, which is impossible. -/
theorem IsCoverHollow.isTerminalAt (h : R.IsCoverHollow) : R.IsTerminalAt ξ := by
  intro R' hR' hred
  have hβ := isSuccPrelimit_blockStage ξ
  obtain ⟨x⟩ := hR'.nonempty_occurrence
  obtain ⟨u, -, q, ⟨d, h₁, h₂⟩, hq⟩ :=
    hR'.uniformity x _ hβ (blockStage_lt_blockStage_add_one ξ)
  let y : R.Occurrence := ⟨_, u, q.reduce hβ, by rw [← hred, reduce_eval, hq, Option.map_some]⟩
  obtain ⟨N, hN⟩ := exists_lt_coe_add_of_lt_coe_add_omega0 h₁ h₂
  have hnot : ¬ R.IsTopAnchor y d N := fun hy ↦ h ⟨y, d, N, hy⟩
  simp only [IsTopAnchor, not_and, not_forall, not_not] at hnot
  obtain ⟨z, hz, hforce⟩ := hnot (Label.reduce_of_le h₁)
  have hle := Covers.le_label_of_forcesThreshold hR'.isConsistent hβ (covers_of_eval u hq) hforce
    (hred ▸ hz)
  exact hle.not_gt hN
end Terminality

end Realization

end VaughtConjecture

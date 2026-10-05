/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Candidate
import VaughtConjecture.Continuation.Classification
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.Realization.CapToModel

/-!
# The continuation criterion from stable capped receiving

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion: non-hollow
unbounded top-grade growth makes the stable candidate a model, by (R4) of the table of Layer 3
with its empty-root base case and the cap-to-model theorem); semantic contract, item 8.

Throughout, `R` is a realization at the block stage `λ_ξ = blockStage ξ` on a carrier `M`,
`λ_{ξ+1} = blockStage (ξ + 1) = λ_ξ + ω` is the next block stage, and `R.stableCandidate hlaw` is
the stable candidate of `VaughtConjecture.Continuation.Candidate` at `λ_{ξ+1}`, defined from a
proof `hlaw` that `R` is stably lawful.

**Output 3 is not proved here.**  It is derived conditionally on three hypotheses, each still to
be proved:

* **(R4)**, stable capped receiving (`StableCappedReceiving`), as stated below;
* **the nonempty coface instances at `λ_{ξ+1}`** (`StageType.HasNonemptyCofaceInstances`): the
  amalgam of a legal stage type with a legal stage type on one point over the empty face, and
  nonempty uniformity and dominance instances among the cofaces of every legal stage type.  All
  three follow from the coatom extension property with apex at `λ_{ξ+1}` (in
  `VaughtConjecture.MainTheorem.CapToModel`, which imports the extension constructions that this
  layer does not); that property is not proved;
* **stable lawfulness** of `R` (`Realization.IsStablyLawful`), the argument of the definition of
  the candidate.  The criterion takes it as an explicit hypothesis on the models in its domain
  (`ModelStableLawfulness`: every model at `λ_ξ`, `ξ < ω₁`, that is not cover-hollow and has
  top-grade supremum `⊤` is stably lawful).  It is open, and it is not a side condition (below).

**(R4)** (`StableCappedReceiving`).  For a model `R` at `λ_ξ`, `ξ < ω₁`, stably lawful, not
cover-hollow, with top-grade supremum `⊤`: over every occurrence of the candidate of positive
arity, for every coface `D` of its type and every ordinal `γ < λ_{ξ+1}`, some point extends the
occurrence to one whose candidate type `Q` is on the scheme of `D`, equals `D` at every cell where
`D` is not the formal top (bottom included), and exceeds `γ` at every cell where `D` is the formal
top.  Such a `Q` is in the receiving family of `D` at the cutoff `γ`
(`StageType.mem_receivingFamily_of_capped`), so (R4) is finite-cut receiving of the candidate over
positive roots.  Its proof is to combine the following, none of which is proved or used here:
the acquisition, in `R`, of a private context calibrated to the stable labels (non-hollowness
supplies an attained proper stable value, unbounded growth a private cap whose stable value is
proper and above every requested `γ`); the growth construction with its section theorem, shared
with (R3); the recovery statement of (R3) and (R4) for restriction-compatible labellings,
evaluated on the stable labelling; and the realization of the constructed scheme over the private
context by generalized saturation of `R`.

**The empty root** (`Realization.hasFiniteCutReceiving_of_pos`).  (R4) concerns positive roots
only.  Over the empty root, for a one-point donor `D`, covering gives an occurrence of positive
arity, the amalgam over the empty face combines its type with `D` into a coface `Q`, the
positive-root statement receives `Q` over that occurrence, and exact consistency restricts the
received type to the new point, where it lies in the receiving family of `D`
(`StageType.exists_restrictFace_mem_receivingFamily`).  This is the coatom extension at
`λ_{ξ+1}`, not the padding by high-arity dominance at `λ_ξ` used in (R3).

**The assembly** (`Realization.isModel_stableCandidate`) is the cap-to-model theorem at the nonzero
limit stage `λ_{ξ+1}` (`Realization.isModel_of_hasFiniteCutReceiving`):

* the nonempty carrier, legal types, exact consistency and covering of the candidate come from
  those of the model `R` (`Realization.hasLegalTypes_stableCandidate`,
  `Realization.isConsistent_stableCandidate`, `Realization.isCovering_stableCandidate`);
* finite-cut receiving comes from (R4) over positive roots and the amalgam field of the coface
  instances over the empty root (`Realization.hasFiniteCutReceiving_stableCandidate`);
* the uniformity and dominance instances of the clauses of a model are nonempty by the other two
  fields of the coface instances ([Kni26, Lemmas 4.4.2 and 4.4.3]); given finite-cut receiving,
  only these instances are used (`Realization.isModel_stableCandidate_of_hasFiniteCutReceiving`).

**Where non-hollowness and unbounded growth enter.**  In the assembly they are read only as
hypotheses of (R4).  Their role is the receiving of the clauses of a model at `λ_{ξ+1}` that
concern the new block `[λ_ξ, λ_ξ + ω)`:

* **uniformity at `γ = λ_ξ`** is received at the cutoff `L + 1` from a donor with a label `L` in
  `[λ_ξ, λ_ξ + ω)`, so the candidate needs labels in that block.  The candidate of a cover-hollow
  realization has none and is not a model
  (`Realization.not_isModel_stableCandidate_of_isCoverHollow`); without cover-hollowness the
  attained proper stable label
  (`Realization.exists_stableLabel_eq_coe_add_of_not_isCoverHollow`) is such a label of the
  candidate (`Realization.exists_stableCandidate_label_eq_coe_add`);
* **high-arity dominance at `γ = λ_ξ + K`** is received at the cutoff `γ + 1`, so the candidate
  needs labels above `λ_ξ + K` for every `K`.  If every stable label is at most `λ_ξ + K`, the
  candidate is not a model (`Realization.not_isModel_stableCandidate_of_stableLabel_le`); with
  top-grade supremum `⊤`, the order law gives labels of the candidate above every `λ_ξ + K`
  (`Realization.exists_lt_stableCandidate_label`).

These two lemmas are not used in the assembly; they show that the candidate has the labels that
these clauses require, and (R4) is to realize such labels over every root.

**The criterion** (`ContinuationCriterion.of_stableCappedReceiving`).  From (R4), the coface
instances at every `λ_{ξ+1}` with `ξ < ω₁`, and `ModelStableLawfulness`, the continuation
criterion of `VaughtConjecture.Continuation.Classification` holds: the expansion of a model `R`
that is not cover-hollow and has top-grade supremum `⊤` is its stable candidate, which reduces to
`R` (`Realization.stableCandidate_reduce`).

**Stable lawfulness is the content of the criterion.**  The order law and locality of the stable
section are proved under exact consistency and covering, so only availability can fail, and only
at a pair whose first cell is labelled the formal top.  There, availability is exactly the
transfer of every threshold forced at the first cell over a realized rooted cover to some cell
labelled the formal top at the graded index of the second, over a possibly different realized
rooted cover (`Realization.availability_stableSection_iff`, with no hypothesis on `R`).  It holds

* when no type has two cells labelled the formal top at one graded index
  (`Realization.isStablyLawful_of_injOn_gradedIndex`), and for cover-hollow realizations;
* for the reduction of an exactly consistent realization at `λ_{ξ+1}` with legal types and
  finite-extension receiving, given forcing donors at `ξ`
  (`Realization.isStablyLawful_of_reduce_eq`): in particular for a model with a model expansion
  to `λ_{ξ+1}`, given (R1) there.

So the open case is the terminal one.  Given forcing donors at `ξ` and finite-extension
receiving of the models at `λ_{ξ+1}` ((R1) there, equivalent to finite-cut receiving for models
by `Realization.IsModel.hasFiniteExtensionReceiving_iff`), a realization that is not stably
lawful is terminal at `ξ` (`Realization.isTerminalAt_of_not_isStablyLawful`), and it is never
cover-hollow (`Realization.not_isCoverHollow_of_not_isStablyLawful`).  Hence the criterion, with
forcing donors and (R1), gives stable lawfulness of every model with unbounded top-grade growth at
a countable block (`Realization.isStablyLawful_of_continuationCriterion`,
`ModelStableLawfulness.of_continuationCriterion`); a model with unbounded growth that is not
stably lawful refutes the criterion together with these inputs
(`Realization.not_continuationCriterion_of_not_isStablyLawful`); and, given (R4), the coface
instances, forcing donors and (R1), the criterion is equivalent to `ModelStableLawfulness`
(`continuationCriterion_iff_modelStableLawfulness`).

No compiled statement refutes `ModelStableLawfulness`, and no single clause of a model supplies
it.  The clauses prescribe, for realized covers, schemes, bottom patterns and labels below `λ_ξ`,
all visible below a cap self-visible at the arity of the cover; by bountifulness of a legal cover
(`StageType.exists_isLawful_lift`) a comparison holding in every lawful section that agrees with
the cover below such a cap already holds in every lift of the base type, so it forces no new
threshold.  Only which cells of realized covers are labelled the formal top can transfer forcing
to a twin, and no clause prescribes those.  (This reason is argued here, not compiled.)

The derivation of the criterion uses neither its converse, nor (R1), forcing donors,
normalization, or uniqueness of expansions; (R1) and forcing donors enter only the statements
relating stable lawfulness to the criterion.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3].
-/

universe u v w

namespace VaughtConjecture

open Ordinal Label StageType

/-! ### Receiving families -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- **Faces of members of a receiving family**: if `Q` is in the receiving family of `D` at `c`,
then along every face at which `D` restricts to `d`, `Q` restricts to a member of the receiving
family of `d` at `c`. -/
theorem exists_restrictFace_mem_receivingFamily {D Q : StageType.{u} α n} {c : Label.{u}}
    (hQ : Q ∈ receivingFamily D c) {f : Fin m ↪ Fin n} {d : StageType.{u} α m}
    (hd : restrictFace f D = some d) :
    ∃ q, restrictFace f Q = some q ∧ q ∈ receivingFamily d c := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp hd
  obtain ⟨hS, hl⟩ := hQ
  obtain ⟨S, ℓ, _, _, _, _⟩ := Q
  obtain ⟨S', ℓ', _, _, _, _⟩ := D
  obtain rfl : S = S' := hS
  refine ⟨_, restrictFace_of_mem _ f (by exact hf), rfl, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := Fin.ext hij
  exact hl _ _ rfl

/-- **Capped agreement gives receiving**: a stage type on the scheme of `D` that equals `D` at
every cell where `D` is not the formal top and exceeds `γ` at every cell where `D` is the formal
top is in the receiving family of `D` at the cutoff `γ`. -/
theorem mem_receivingFamily_of_capped {D Q : StageType.{u} α n} {γ : Ordinal.{u}}
    (hS : Q.toScheme = D.toScheme)
    (h : ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
      (D.label j ≠ ⊤ → Q.label i = D.label j) ∧ (D.label j = ⊤ → (γ : Label.{u}) < Q.label i)) :
    Q ∈ receivingFamily D γ := by
  refine ⟨hS, fun i j hij ↦ ?_⟩
  by_cases hD : D.label j = ⊤
  · rw [hD, min_eq_right ((h i j hij).2 hD).le, min_eq_right le_top]
  · rw [(h i j hij).1 hD]

variable (α) in
/-- **Nonempty coface instances** at a stage `α`: the three statements about legal stage types at
`α` used by the cap-to-model theorem at `α` and by the empty-root case of receiving.  Each follows
from the coatom extension property with apex at `α`. -/
structure HasNonemptyCofaceInstances : Prop where
  /-- **The amalgam over the empty face**: a legal stage type `P` on `n` points and a legal stage
  type `d` on one point are the faces, along the first `n` points and along the last point, of
  one coface of `P`. -/
  exists_amalgam_empty ⦃n : ℕ⦄ (P : StageType.{u} α n) (d : StageType.{u} α 1) :
    P.IsLegal → d.IsLegal → ∃ Q ∈ P.cofaces, restrictFace (Fin.natAddEmb n) Q = some d
  /-- **Uniformity instances**: for `γ` zero or a limit below `α`, some coface of a legal stage
  type has a label in `[γ, γ + ω)`. -/
  uniformity ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsLegal → ∀ γ : Ordinal.{u},
    Order.IsSuccPrelimit γ → γ < α → (p.cofaces ∩ uniformityFamily γ).Nonempty
  /-- **Dominance instances**: for `γ` below `α`, some coface of a legal stage type on `n` points
  has a label above `γ` at a cell of grade `n + 1`. -/
  dominance ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsLegal → ∀ γ : Ordinal.{u}, γ < α →
    (p.cofaces ∩ dominanceFamily γ).Nonempty

end StageType

/-! ### Receiving over the empty root -/

namespace Realization

section EmptyRoot

variable {α : Ordinal.{u}} {M : Type v} {C : Realization.{u, v} α M}

/-- **Finite-cut receiving from positive roots**: a realization on a nonempty carrier with legal
types, exactly consistent and covering, that receives over every occurrence of positive arity has
the finite-cut receiving property, provided its stage has the amalgam over the empty face.  Over
the empty root, the one-point donor is amalgamated with the type of an occurrence of positive
arity given by covering, received over that occurrence, and restricted to the new point. -/
theorem hasFiniteCutReceiving_of_pos (hne : Nonempty M) (hl : C.HasLegalTypes)
    (hc : C.IsConsistent) (hcov : C.IsCovering)
    (hamal : ∀ ⦃n : ℕ⦄ (P : StageType.{u} α n) (d : StageType.{u} α 1), P.IsLegal → d.IsLegal →
      ∃ Q ∈ P.cofaces, restrictFace (Fin.natAddEmb n) Q = some d)
    (hpos : ∀ x : C.Occurrence, 0 < x.arity → ∀ D ∈ x.type.cofaces, ∀ c : Label.{u},
      IsPermittedCutoff α c → C.RealizesOver x.tuple (receivingFamily D c)) :
    C.HasFiniteCutReceiving := by
  rintro ⟨_ | n, t, p, ht⟩ D hD c hc'
  · obtain ⟨a⟩ := hne
    obtain ⟨m, u, f, -, hu⟩ :=
      hcov (⟨fun _ ↦ a, fun i j _ ↦ Subsingleton.elim i j⟩ : Fin 1 ↪ M)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hu
    obtain ⟨Q, hQ, hQD⟩ := hamal P D (hl u P hP) hD.1
    obtain ⟨w, -, q, hq, hwq⟩ := hpos ⟨m, u, P, hP⟩ (f 0).pos Q hQ c hc'
    obtain ⟨q', hq', hq'D⟩ := exists_restrictFace_mem_receivingFamily hq hQD
    exact ⟨(Fin.natAddEmb m).trans w, Function.Embedding.ext fun i ↦ i.elim0, q', hq'D,
      (hc w q _ hwq).trans hq'⟩
  · exact hpos ⟨n + 1, t, p, ht⟩ n.succ_pos D hD c hc'

end EmptyRoot

/-! ### The labels of the candidate in the new block -/

section NewBlock

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Non-hollowness gives a label of the candidate in `[λ_ξ, λ_ξ + ω)`**: if `R` is not
cover-hollow, some type of the candidate has the label `λ_ξ + i` for some `i : ℕ`, at a cell
labelled the formal top in `R` (the attained proper stable label). -/
theorem exists_stableCandidate_label_eq_coe_add (hnh : ¬ R.IsCoverHollow)
    (hlaw : R.IsStablyLawful) :
    ∃ (x : (R.stableCandidate hlaw).Occurrence) (a : Fin x.type.card) (i : ℕ),
      x.type.label a = ((blockStage ξ + i : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨x, a, i, ha, h⟩ := exists_stableLabel_eq_coe_add_of_not_isCoverHollow hnh
  exact ⟨⟨x.arity, x.tuple, _, stableCandidate_eval_of_eval x.eval_tuple⟩, a, i,
    (stableSection_of_eq_top ha).trans h⟩

/-- **Unbounded growth gives labels of the candidate above every `λ_ξ + K`**: if the top-grade
supremum of `R` is `⊤`, then for every `K : ℕ` some type of the candidate has a label above
`λ_ξ + K`, at a cell labelled the formal top in `R` of grade above `K` (the order law). -/
theorem exists_lt_stableCandidate_label (hgrow : R.topGradeSup = ⊤) (hlaw : R.IsStablyLawful)
    (K : ℕ) : ∃ (x : (R.stableCandidate hlaw).Occurrence) (a : Fin x.type.card),
      ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) < x.type.label a := by
  obtain ⟨x, hx⟩ : ∃ x : R.Occurrence, K < x.type.topGrade := by
    by_contra! h
    have hle : R.topGradeSup ≤ K := iSup_le fun x ↦ Nat.cast_le.mpr (h x)
    simp [hgrow] at hle
  obtain ⟨d, hd, hKd⟩ : ∃ d, x.type.label d = ⊤ ∧ K < x.type.toCellScheme.grade d := by
    by_contra! h
    exact hx.not_ge (topGrade_le_iff.mpr h)
  refine ⟨⟨x.arity, x.tuple, _, stableCandidate_eval_of_eval x.eval_tuple⟩, d, ?_⟩
  -- the label of the stable type at `d` is the stable section there
  change _ < R.stableSection x.tuple x.type d
  rcases stableSection_eq_top_or_exists x.eval_tuple hd with h | ⟨i, hi, h⟩
  · rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  · rw [h]
    exact_mod_cast add_lt_add_right (Nat.cast_lt.mpr (hKd.trans_le hi)) _

end NewBlock

/-! ### Availability of the stable section and terminality -/

section Availability

variable {ξ : Ordinal.{u}} {M : Type v} {k : ℕ} {R : Realization.{u, v} (blockStage ξ) M}

/-- The label of an offset is monotone in the offset. -/
private theorem ofOffset_mono {β : Ordinal.{u}} {o o' : ℕ∞} (h : o ≤ o') :
    Label.ofOffset β o ≤ Label.ofOffset β o' := by
  induction o' using ENat.recTopCoe with
  | top => exact Label.ofOffset_top ▸ le_top
  | coe m' =>
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top m') h)
    rw [Label.ofOffset_natCast, Label.ofOffset_natCast]
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      (add_le_add_right (Nat.cast_le.mpr (ENat.natCast_le_natCast.mp h)) _))

variable (R) in
/-- **Forcing over a realized rooted cover**: some rooted cover `(m, q, f)` of `u` realized in `R`
(the tuple `u` extends along `f` to a cover of `q`) forces the threshold `n` at the cell `d` of `t`,
read at `λ_{ξ+1}`. -/
def ForcesOverCover (u : Fin k ↪ M) (t : StageType.{u} (blockStage ξ) k) (d : Fin t.card)
    (n : ℕ) : Prop :=
  ∃ x : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin k ↪ Fin m),
    ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) x.2.1 x.2.2 t d n ∧
      R.ExtendsToCover u x

open Finset in
/-- **Availability of the stable section at a cell labelled the formal top**: at a typed tuple `u`
of type `t` and a cell `s₀` labelled the formal top, the availability law of the stable section
for the pair `(s₀, t₀)` holds exactly when every threshold forced at `s₀` over a realized rooted
cover is forced, over a realized rooted cover, at some cell labelled the formal top at the graded
index of `t₀`.  No hypothesis on `R`; the cell may depend on the threshold, and the law takes the
one with the largest stable offset. -/
theorem availability_stableSection_iff {u : Fin k ↪ M} {t : StageType.{u} (blockStage ξ) k}
    (ht : R.eval u = some t) {s₀ t₀ : Fin t.card} (hs₀ : t.label s₀ = ⊤) :
    (∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧
        R.stableSection u t s₀ ≤ R.stableSection u t w) ↔
      ∀ n : ℕ, R.ForcesOverCover u t s₀ n →
        ∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧ t.label w = ⊤ ∧
          R.ForcesOverCover u t w n := by
  have hc : R.Covers t u := covers_of_eval u ht
  constructor
  · rintro ⟨w, hw, hle⟩ n hn
    have h₁ : ((blockStage ξ + n : Ordinal.{u}) : Label.{u}) ≤ R.stableSection u t s₀ := by
      rw [stableSection_of_eq_top hs₀]
      exact (coe_add_le_stableLabel_iff hc hs₀).mpr hn
    have hwt : t.label w = ⊤ := by
      by_contra hwt
      rw [stableSection_of_ne_top hwt] at hle
      exact (h₁.trans hle).not_gt (((t.atStage w).resolve_right hwt).trans_le
        (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)))
    refine ⟨w, hw, hwt, ?_⟩
    have h₂ := h₁.trans hle
    rw [stableSection_of_eq_top hwt] at h₂
    exact (coe_add_le_stableLabel_iff hc hwt).mp h₂
  · intro h
    classical
    set T := univ.filter fun w : Fin t.card ↦
      t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧ t.label w = ⊤
    set o : Fin t.card → ℕ∞ := fun d ↦
      R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d
    have hT : T.Nonempty := by
      obtain ⟨w, hw, hwt, -⟩ := h 0 ⟨⟨k, t, Function.Embedding.refl _⟩,
        forcesThreshold_zero (restrictFace_refl t) hs₀, u, rfl, hc⟩
      exact ⟨w, mem_filter.mpr ⟨mem_univ _, hw, hwt⟩⟩
    obtain ⟨w₀, hw₀, hmax⟩ := T.exists_max_image o hT
    obtain ⟨-, hw₀i, hw₀t⟩ := mem_filter.mp hw₀
    refine ⟨w₀, hw₀i, ?_⟩
    rw [stableSection_of_eq_top hs₀, stableSection_of_eq_top hw₀t]
    refine ofOffset_mono (ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_)
    obtain ⟨w, hw, hwt, hf⟩ := h n ((natCast_le_stableOffset_iff hc hs₀).mp hn)
    exact ((natCast_le_stableOffset_iff hc hwt).mpr hf).trans
      (hmax w (mem_filter.mpr ⟨mem_univ _, hw, hwt⟩))

/-- **A realization that is not stably lawful is not cover-hollow**: cover-hollow realizations are
stably lawful. -/
theorem not_isCoverHollow_of_not_isStablyLawful (h : ¬ R.IsStablyLawful) : ¬ R.IsCoverHollow :=
  fun hh ↦ h (isStablyLawful_of_isCoverHollow hh)

/-- **A realization that is not stably lawful is terminal**, given forcing donors at `ξ` and
finite-extension receiving of the models at `λ_{ξ+1}` on the same carrier ((R1) there): a model
expansion would make it stably lawful (`isStablyLawful_of_reduce_eq`). -/
theorem isTerminalAt_of_not_isStablyLawful (hF : ForcingDonors.{u} ξ)
    (hrec : ∀ R' : Realization.{u, v} (blockStage (ξ + 1)) M, R'.IsModel →
      R'.HasFiniteExtensionReceiving)
    (h : ¬ R.IsStablyLawful) : R.IsTerminalAt ξ := fun R' hR' hred ↦
  h (isStablyLawful_of_reduce_eq hF hR'.isConsistent hR'.isLegal (hrec R' hR') hred)

end Availability

end Realization

/-! ### (R4) and the assembly -/

/-- **Stable capped receiving**, (R4) of the table of Layer 3, still to be proved: for a model `R`
at `λ_ξ`, `ξ < ω₁`, stably lawful, not cover-hollow, with top-grade supremum `⊤`, over every
occurrence of positive arity of the stable candidate, for every coface `D` of its type and every
ordinal `γ < λ_{ξ+1}`, some point extends the occurrence to one whose candidate type is on the
scheme of `D`, equals `D` at every cell where `D` is not the formal top, and exceeds `γ` at every
cell where `D` is the formal top.  It is to be proved by the growth construction shared with (R3),
calibrated to the stable labels and realized by generalized saturation of `R`. -/
structure StableCappedReceiving : Prop where
  /-- Receiving of the stable candidate over positive roots, capped at every `γ < λ_{ξ+1}`. -/
  receive ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) :
    ξ < ω₁ → R.IsModel → ∀ hlaw : R.IsStablyLawful, ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∀ x : (R.stableCandidate hlaw).Occurrence, 0 < x.arity → ∀ D ∈ x.type.cofaces,
        ∀ γ : Ordinal.{0}, γ < blockStage (ξ + 1) →
          ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
            ∃ Q, (R.stableCandidate hlaw).eval u = some Q ∧ Q.toScheme = D.toScheme ∧
              ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
                (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
                  (D.label j = ⊤ → (γ : Label.{0}) < Q.label i)

/-- **Stable lawfulness of the models in the domain of the continuation criterion**, a hypothesis
still to be proved: every model at `λ_ξ`, `ξ < ω₁`, that is not cover-hollow and has top-grade
supremum `⊤` is stably lawful.  It holds for the models without twins
(`Realization.isStablyLawful_of_injOn_gradedIndex`) and for the models with a model expansion to
`λ_{ξ+1}` given forcing donors and (R1) (`Realization.isStablyLawful_of_reduce_eq`); for terminal
models with twins it is open.  Given (R4), the coface instances, forcing donors and (R1), it is
equivalent to the continuation criterion (`continuationCriterion_iff_modelStableLawfulness`).  The
hypothesis that `R` is not cover-hollow is redundant (cover-hollow realizations are stably lawful)
and is kept to match the criterion. -/
structure ModelStableLawfulness : Prop where
  /-- Every model in the domain of the criterion is stably lawful. -/
  isStablyLawful ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) :
    ξ < ω₁ → R.IsModel → ¬ R.IsCoverHollow → R.topGradeSup = ⊤ → R.IsStablyLawful

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **Modelhood of the candidate from finite-cut receiving**: for a model `R`, the stable candidate
with the finite-cut receiving property is a model, given the uniformity and dominance instances of
the coface instances at `λ_{ξ+1}` (the cap-to-model theorem at `λ_{ξ+1}`). -/
theorem isModel_stableCandidate_of_hasFiniteCutReceiving (hR : R.IsModel)
    {hlaw : R.IsStablyLawful}
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hr : (R.stableCandidate hlaw).HasFiniteCutReceiving) : (R.stableCandidate hlaw).IsModel :=
  have hl := hasLegalTypes_stableCandidate (hlaw := hlaw) hR.hasLegalTypes
  isModel_of_hasFiniteCutReceiving (isSuccLimit_blockStage (ξ + 1)) hR.nonempty hl
    (isConsistent_stableCandidate hR.isConsistent hR.isCovering)
    (isCovering_stableCandidate hR.isCovering) hr
    (fun x γ hγ hγα ↦ hinst.uniformity x.type (hl _ _ x.eval_tuple) γ hγ hγα)
    (fun x γ hγα ↦ hinst.dominance x.type (hl _ _ x.eval_tuple) γ hγα)

/-- **Finite-cut receiving of the candidate**, conditional on (R4): over positive roots by (R4) at
the cutoff `γ`, and over the empty root by the amalgam over the empty face at `λ_{ξ+1}` (the field
`exists_amalgam_empty` of the coface instances; the other two fields are not used).
Non-hollowness and unbounded growth are used only as hypotheses of (R4). -/
theorem hasFiniteCutReceiving_stableCandidate (hξ : ξ < ω₁) (hR : R.IsModel)
    (hlaw : R.IsStablyLawful) (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (hR4 : StableCappedReceiving.{w})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hlaw).HasFiniteCutReceiving := by
  refine hasFiniteCutReceiving_of_pos hR.nonempty
    (hasLegalTypes_stableCandidate hR.hasLegalTypes)
    (isConsistent_stableCandidate hR.isConsistent hR.isCovering)
    (isCovering_stableCandidate hR.isCovering) hinst.exists_amalgam_empty
    fun x hx D hD c hc ↦ ?_
  induction c using Label.recBotCoeTop with
  | bot => exact absurd hc not_isPermittedCutoff_bot
  | top => exact absurd hc not_isPermittedCutoff_top
  | coe γ =>
    obtain ⟨u, hu, Q, hQ, hS, hl⟩ :=
      hR4.receive R hξ hR hlaw hnh hgrow x hx D hD γ (isPermittedCutoff_coe.mp hc)
    exact ⟨u, hu, Q, mem_receivingFamily_of_capped hS hl, hQ⟩

/-- **Output 3, conditionally**: the stable candidate of a stably lawful model at `λ_ξ`,
`ξ < ω₁`, that is not cover-hollow and has top-grade supremum `⊤` is a model at `λ_{ξ+1}`,
conditional on (R4) (`hR4`) and the coface instances at `λ_{ξ+1}` (`hinst`), both still to be
proved.  Non-hollowness and unbounded growth enter only through (R4). -/
theorem isModel_stableCandidate (hξ : ξ < ω₁) (hR : R.IsModel) (hlaw : R.IsStablyLawful)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) (hR4 : StableCappedReceiving.{w})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hlaw).IsModel :=
  isModel_stableCandidate_of_hasFiniteCutReceiving hR hinst
    (hasFiniteCutReceiving_stableCandidate hξ hR hlaw hnh hgrow hR4 hinst)

end Realization

/-! ### The continuation criterion -/

/-- **The continuation criterion from stable capped receiving**, conditional on (R4) (`hR4`), the
coface instances at every `λ_{ξ+1}` with `ξ < ω₁` (`hinst`; from the coatom extension property
with apex there), and stable lawfulness of the models in the domain of the criterion (`hlaw`), each
still to be proved: the model expansion is the stable candidate.  The last hypothesis is
equivalent to the conclusion given the first two, forcing donors and (R1)
(`continuationCriterion_iff_modelStableLawfulness`). -/
theorem ContinuationCriterion.of_stableCappedReceiving (hR4 : StableCappedReceiving.{w})
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hlaw : ModelStableLawfulness.{w}) : ContinuationCriterion.{w} :=
  ⟨fun _ _ R hξ hR hnh hgrow ↦
    ⟨_, Realization.isModel_stableCandidate hξ hR (hlaw.isStablyLawful R hξ hR hnh hgrow) hnh
      hgrow hR4 (hinst _ hξ), Realization.stableCandidate_reduce⟩⟩

/-! ### Stable lawfulness from the continuation criterion -/

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **The criterion gives stable lawfulness** of every model at a countable block with top-grade
supremum `⊤`, given forcing donors at `ξ` and finite-extension receiving of the models at
`λ_{ξ+1}` ((R1) there).  No non-hollowness hypothesis is needed: a realization that is not stably
lawful is not cover-hollow, so the criterion gives it a model expansion, against terminality. -/
theorem isStablyLawful_of_continuationCriterion (hcont : ContinuationCriterion.{w})
    (hξ : ξ < ω₁) (hF : ForcingDonors.{0} ξ)
    (hrec : ∀ R' : Realization.{0, w} (blockStage (ξ + 1)) M, R'.IsModel →
      R'.HasFiniteExtensionReceiving)
    (hR : R.IsModel) (hg : R.topGradeSup = ⊤) : R.IsStablyLawful := by
  by_contra h
  obtain ⟨R', hR', hred⟩ :=
    hcont.exists_model R hξ hR (not_isCoverHollow_of_not_isStablyLawful h) hg
  exact isTerminalAt_of_not_isStablyLawful hF hrec h R' hR' hred

/-- **A model that is not stably lawful refutes the criterion** together with forcing donors at
`ξ` and (R1) at `λ_{ξ+1}`, when it has top-grade supremum `⊤` at a countable block. -/
theorem not_continuationCriterion_of_not_isStablyLawful (hξ : ξ < ω₁) (hR : R.IsModel)
    (hg : R.topGradeSup = ⊤) (h : ¬ R.IsStablyLawful) :
    ¬ (ContinuationCriterion.{w} ∧ ForcingDonors.{0} ξ ∧
      ∀ R' : Realization.{0, w} (blockStage (ξ + 1)) M, R'.IsModel →
        R'.HasFiniteExtensionReceiving) :=
  fun ⟨hc, hF, hrec⟩ ↦ h (isStablyLawful_of_continuationCriterion hc hξ hF hrec hR hg)

end Realization

/-- **Stable lawfulness from the continuation criterion**, given forcing donors at every countable
block and (R1) at every `λ_{ξ+1}` with `ξ < ω₁`. -/
theorem ModelStableLawfulness.of_continuationCriterion (hcont : ContinuationCriterion.{w})
    (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hrec : ∀ ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R' : Realization.{0, w} (blockStage (ξ + 1)) M),
      ξ < ω₁ → R'.IsModel → R'.HasFiniteExtensionReceiving) :
    ModelStableLawfulness.{w} :=
  ⟨fun _ _ _ hξ hR _ hg ↦ Realization.isStablyLawful_of_continuationCriterion hcont hξ (hF _ hξ)
    (fun R' hR' ↦ hrec R' hξ hR') hR hg⟩

/-- **The continuation criterion is equivalent to stable lawfulness of the models in its domain**,
given (R4), the coface instances at every `λ_{ξ+1}` with `ξ < ω₁`, forcing donors at every
countable block, and (R1) at every `λ_{ξ+1}` with `ξ < ω₁`, all still to be proved. -/
theorem continuationCriterion_iff_modelStableLawfulness (hR4 : StableCappedReceiving.{w})
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hrec : ∀ ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R' : Realization.{0, w} (blockStage (ξ + 1)) M),
      ξ < ω₁ → R'.IsModel → R'.HasFiniteExtensionReceiving) :
    ContinuationCriterion.{w} ↔ ModelStableLawfulness.{w} :=
  ⟨fun h ↦ .of_continuationCriterion h hF hrec, .of_stableCappedReceiving hR4 hinst⟩

end VaughtConjecture

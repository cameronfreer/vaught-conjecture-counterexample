/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.Tuple.Embedding
import VaughtConjecture.Construction.DenseChain
import VaughtConjecture.Construction.PartialRealization
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Language.Density

/-!
# Countable saturated models from the finite extension statements

Roadmap, Layer 2 (the countable chain construction, with the exact finite extension hypothesis
explicit: countable cofinal requirements and the union theorem, established once) and Layer 3
(the table of extension statements of 3.4: row 6, the exact one-point pinned extension, and the
capped extensions for the uniformity and dominance families, here as hypotheses only); semantic
contract, item 5.

This is [Kni26, Proposition 4.4.5], the existence of countable saturated models at a stage with
countably many ordinals below it, **conditional on the finite extension statements**, which are
hypotheses here and are not proved:

* **(E) exact one-point pinned extension** (`Construction.HasExactPinnedExtensions α`, the
  conclusion of row 6): for a legal stage type `P` on `n` points, a closed face
  `f : Fin m ↪ Fin n` of `P` with restriction `p`, and a coface `d` of `p` (a legal one-point
  extension of `p`), some coface `Q` of `P` has face `d` along `pinnedFace f`, the face `f`
  followed by the new point;
* **(C) capped extension for the families** (`Construction.HasFamilyExtensions α`): every legal
  stage type has a coface in each uniformity family `uniformityFamily γ` for `γ` zero or a limit
  below the stage, and in each dominance family `dominanceFamily γ` for `γ` below the stage.
  These are the nonemptiness statements of [Kni26, Lemmas 4.4.2 and 4.4.3] (the uniformity and
  dominance instances of [Kni26, Lemma 4.4.1]).  The generalized-saturation and bottom-pattern
  clauses of a model are guarded by the nonemptiness of their instances
  (`Realization.IsModel`), and at a stage that is zero or a limit those instances are nonempty by
  `StageType.nonempty_cofaces_inter_saturationFamily` and
  `StageType.nonempty_cofaces_inter_bottomPatternFamily`; they need no hypothesis.

**Saturation: realizing every coface.**  A realization **realizes every coface**
(`Realization.RealizesCofaces`) when over every occurrence it realizes every coface of the type of
the occurrence; for a model this is saturation, [Kni26, Definition 4.1.1].  Such a realization,
legal, exactly consistent, and covering on a nonempty carrier, is a model given (C)
(`Realization.isModel_of_realizesCofaces`): an instance of each family with a member among the
cofaces of the type is realized through that member.  It has the finite-cut receiving property
with no hypothesis (`Realization.hasFiniteCutReceiving_of_realizesCofaces`): a coface lies in
each of its receiving families.

**Requirements.**  A requirement (`Construction.Requirement α`) is either a point `j` of `ℕ`, met
by a condition with more than `j` points (**absorption**), or a pair of a tuple `t` of `ℕ` and a
stage type `q` on one more point, met by a condition that supports `t` and, if `q` is a coface of
the type of `t`, realizes `q` over `t` (`Condition.Meets`).  At a stage with countably many
ordinals below it there are countably many requirements (`Requirement.countable`, from
`StageType.countable`).  Meeting a requirement persists under extension (`Condition.Meets.mono`):
the decision on a supported tuple is final, whether it is typed or supported invisible.  Each
requirement is met above every condition, given (E) (`Condition.exists_le_meets`):

* a new point is added by one application of (E) at the empty face, with the one-point legal
  stage type `StageType.onePoint` as the coface (`Condition.exists_le_card_succ`); finitely many
  such steps absorb the points of a tuple (`Condition.exists_le_isSupported`);
* once `t` is supported, if its type `p` has `q` as a coface, one application of (E) at the face
  of the chart spanned by `t` adds a point realizing `q` over `t`
  (`Condition.exists_le_realizesOver`).  If `t` is unsupported it is absorbed first, and if it
  is supported invisible, or `q` is not a coface of its type, the requirement is already met.

**Generic and exact-family-specific parts.**  All of
`VaughtConjecture.Construction.PartialRealization` is generic: conditions, extension as literal
restriction, the persistence of realized families under extension
(`Construction.Condition.realizesOver_of_le`, for any family), and the union of a chain with its
stabilization, exact consistency, legality, and covering criterion
(`Construction.chainUnion_eval_of_isSupported`, `Construction.isConsistent_chainUnion`,
`Construction.hasLegalTypes_chainUnion`, `Construction.isCovering_chainUnion_iff`) do not depend
on what the chain is asked to realize.  So is the pattern of `Condition.Meets.mono`: a
requirement asks for a decision on a supported tuple, and such a decision is final.  What is
specific to the exact family is the tuple service, from `Construction.Requirement` and
`Condition.Meets` through `Construction.realizesCofaces_chainUnion`: it asks for each coface `q`
of the type of a tuple to be realized over the tuple, that is, for the singleton family `{q}`,
and (E) is exactly the extension statement that serves singletons.  A family of targets
`U : StageType α n → Set (StageType α (n + 1))` would be served by the same requirements with
`{q}` replaced by `U p`, by the same proofs, and with (E) replaced by the extension statement
for `U`; this is not parametrized here, since the families of (C) are served through the
singletons of their members.

**The chain.**  By the Rasiowa–Sikorski lemma (`Construction.exists_monotone_forall_exists_mem`)
there is a chain of conditions, starting at any given condition `c₀`, that meets every requirement
(`Construction.exists_chain_forall_meets`).  Its union (`Construction.chainUnion`) has legal
types, is exactly consistent and covering, and realizes every coface
(`Construction.realizesCofaces_chainUnion`), and it restricts to the partial realization of `c₀`
on the tuples `c₀` supports (`Construction.chainUnion_eval_of_isSupported` at the first index).
Hence:

* `Construction.Condition.exists_realizesCofaces_of_hasExactPinnedExtensions`: given (E), every
  condition extends to a realization on `ℕ` with legal types, exactly consistent, covering, and
  realizing every coface;
* `Construction.Condition.exists_isModel_of_extensions`: given (E) and (C), every condition
  extends to a saturated model on `ℕ`;
* `Construction.exists_realizesCofaces_of_hasExactPinnedExtensions` and
  `Construction.exists_isModel_of_extensions`: the same from the one-point condition
  (`Construction.Condition.onePoint`); the latter is a countable saturated model,
  [Kni26, Proposition 4.4.5], conditionally;
* `Construction.exists_realize_fourFamilySentence_of_extensions`: given (E) and (C) at stage `ω`,
  a countable structure satisfying the four-family sentence;
* `Construction.exists_realize_densitySentence_of_hasExactPinnedExtensions`: given (E) alone at
  stage `ω`, a countable structure satisfying the density sentence.

No hypothesis on the stage beyond the countability of the ordinals below it is used: the stage
enters only through (E) and (C).

**Correspondence with the Layer 3 statement.**  (E) is stated here in the terms of the roadmap.
It is literally the conclusion of the exact pinned extension of Layer 3, row 6, derived there
from the coatom extension property ([Kni26, Corollary 4.3.22]): `Q ∈ P.cofaces` unfolds to
`Q.IsLegal` and `restrictFace Fin.castSuccEmb Q = some P`, `d ∈ p.cofaces` to `d.IsLegal` and
`restrictFace Fin.castSuccEmb d = some p`, and `pinnedFace f` is the embedding that Layer 3 calls
the face `f` followed by the new point.  Nothing about the stage `α` is used in that derivation
either.

## Placement

`StageType.onePoint` and `StageType.isLegal_onePoint` belong in
`VaughtConjecture.Stage.LegalExamples`, where they would replace the private `point` (the same
stage type at stage `0` in universe `0`), and the instance `StageType.instSubsingletonZero` in
`VaughtConjecture.Stage.Basic`.  `Realization.RealizesCofaces` and its two consequences belong in
`VaughtConjecture.Realization.Model` and `VaughtConjecture.Language.Density`.  They are stated here
so that those files are unchanged.

**Overlaps with the coatom-extension branch.**  The Layer 3 development on the coatom-extension
branch states some of the same facts; whichever of the two lands second deletes its copies and
uses the other's:

* the zero-point lemmas there (StageType.card_eq_zero, StageType.faces_eq_of_zero,
  StageType.eq_of_zero, StageType.isSome_restrictFace_of_zero) and the private zero-point helpers
  with the instance `StageType.instSubsingletonZero` here;
* the one-point scheme there (Scheme.onePoint, Scheme.isLegal_onePoint, and its bottom labelling
  Scheme.IsLegal.toStageType) and `StageType.onePoint` with `StageType.isLegal_onePoint` here;
* the one-point extension there (StageType.exists_extension, [Kni26, Proposition 4.3.23]) and
  `Construction.nonempty_cofaces_of_hasExactPinnedExtensions` here;
* the face followed by the new point there (extendByLast, with its lemmas) and
  `Construction.pinnedFace` with its lemmas here, equal by `rfl`.

## References

The construction is that of [Kni26, Proposition 4.4.5] (countable saturated models), with the
nonemptiness of the family instances of [Kni26, Lemma 4.4.1] and the one-point extensions of
[Kni26, Corollary 4.3.22 and Proposition 4.3.23] taken as hypotheses; saturation is
[Kni26, Definition 4.1.1], the uniqueness of the stage type on no points is [Kni26, Lemma 4.2.1],
and models are [Kni26, Definition 3.2.1], for R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v

namespace VaughtConjecture

open Finset StageType

variable {α : Ordinal.{u}} {M : Type v} {k m n : ℕ}

/-! ### Stage types on no points and on one point -/

namespace StageType

/-- A stage type on no points has no cells: a cell would have a positive grade at most the size
of its scope, which is empty. -/
private theorem card_eq_zero_of_zero (t : StageType.{u} α 0) : t.card = 0 := by
  by_contra h
  have d : Fin t.card := ⟨0, Nat.pos_of_ne_zero h⟩
  have hle := t.isWellFormed.isWellFormed.grade_le_card d
  have hpos := t.isWellFormed.isWellFormed.grade_pos d
  rw [eq_empty_of_isEmpty (t.toCellScheme.scope d), card_empty] at hle
  omega

/-- The faces of a stage type on no points: only the empty face. -/
private theorem faces_eq_of_zero (t : StageType.{u} α 0) : t.toCellScheme.faces = {∅} := by
  ext C
  simp only [mem_singleton]
  refine ⟨fun _ ↦ eq_empty_of_isEmpty C, ?_⟩
  rintro rfl
  exact t.isWellFormed.isWellFormed.isPlan.empty_mem

/-- **There is only one stage type on no points** at each stage, [Kni26, Lemma 4.2.1] (stated
there for countable limit stages). -/
instance instSubsingletonZero : Subsingleton (StageType.{u} α 0) where
  allEq t t' := by
    have hc := t.card_eq_zero_of_zero
    have hc' := t'.card_eq_zero_of_zero
    refine ext (Scheme.ext (hc.trans hc'.symm) (by rw [t.isWellFormed.ground_eq,
      t'.isWellFormed.ground_eq]) (by rw [t.faces_eq_of_zero, t'.faces_eq_of_zero])
      (fun i ↦ (hc ▸ i).elim0) (fun i ↦ (hc ▸ i).elim0) (fun s ↦ (hc ▸ s).elim0))
      fun i ↦ (hc ▸ i).elim0

/-- The empty face of a stage type is closed. -/
private theorem isSome_restrictFace_of_isEmpty (t : StageType.{u} α n) (e : Fin 0 ↪ Fin n) :
    (restrictFace e t).isSome := by
  rw [isSome_restrictFace_iff, univ_eq_empty, map_empty]
  exact t.isWellFormed.isWellFormed.isPlan.empty_mem

variable (α) in
/-- The **one-point stage type** at stage `α`: a single cell of scope `{0}` and grade `1`, the
faces `∅` and `{0}`, mute rows, and the bottom label; the one-point scheme with the mute semantics
of the last clause of [Kni26, Lemma 4.2.2]. -/
def onePoint : StageType.{u} α 1 where
  card := 1
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩
  rows := CellScheme.Rows.mute _
  label _ := ⊥
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [CellScheme.gradedIndex]⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isLawful := CellScheme.Rows.isLawful_bot
  atStage _ := Label.atStage_bot

variable (α) in
/-- The one-point stage type is legal: mute rows are consistent and bountiful, and the only graded
face is `({0}, 1)`, the graded index of its cell. -/
theorem isLegal_onePoint : (onePoint α).IsLegal :=
  isLegal_iff.mpr ⟨CellScheme.Rows.isConsistent_mute, CellScheme.Rows.isBountiful_mute,
    fun ⟨C, j⟩ ⟨_, hpos, hle⟩ ↦ ⟨(0 : Fin 1), by
      have hC : #C ≤ 1 := card_le_univ C
      have hC' : C = univ := (card_eq_iff_eq_univ C).mp (by simp only at hpos hle ⊢; simp; omega)
      simp only at hpos hle
      ext <;> simp [CellScheme.gradedIndex, onePoint, hC']
      omega⟩⟩

/-- The one-point stage type is a coface of the stage type on no points. -/
private theorem onePoint_mem_cofaces (p : StageType.{u} α 0) : onePoint α ∈ p.cofaces := by
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp
    ((onePoint α).isSome_restrictFace_of_isEmpty Fin.castSuccEmb)
  exact ⟨isLegal_onePoint α, hp'.trans (congrArg some (Subsingleton.elim p' p))⟩

end StageType

/-! ### The finite extension statements -/

namespace Construction

/-- The face `f : Fin m ↪ Fin n` followed by the new point: the embedding of `Fin (m + 1)` into
`Fin (n + 1)` that is `f` on the old points and sends the last point to the last point.  This is
the embedding that Layer 3 calls the face followed by the new point (extendByLast on the
coatom-extension branch, with the same definition, so equal by `rfl` once both are present). -/
def pinnedFace (f : Fin m ↪ Fin n) : Fin (m + 1) ↪ Fin (n + 1) :=
  Fin.Embedding.snoc (f.trans Fin.castSuccEmb) (a := Fin.last n) fun ⟨i, hi⟩ ↦
    (Fin.castSucc_lt_last (f i)).ne hi

/-- `pinnedFace f` sends an old point `i` to `f i`, as an old point. -/
@[simp] theorem pinnedFace_castSucc (f : Fin m ↪ Fin n) (i : Fin m) :
    pinnedFace f i.castSucc = (f i).castSucc :=
  Fin.Embedding.snoc_castSucc

/-- `pinnedFace f` sends the last point to the last point. -/
@[simp] theorem pinnedFace_last (f : Fin m ↪ Fin n) : pinnedFace f (Fin.last m) = Fin.last n :=
  Fin.Embedding.snoc_last

/-- `pinnedFace f` restricts to `f` on the old points: this is `Fin.Embedding.init_snoc`. -/
theorem castSuccEmb_trans_pinnedFace (f : Fin m ↪ Fin n) :
    Fin.castSuccEmb.trans (pinnedFace f) = f.trans Fin.castSuccEmb :=
  Fin.Embedding.init_snoc _ _

variable (α) in
/-- **(E) The exact one-point pinned extension** at stage `α`, the conclusion of row 6 of the
table of extension statements of Layer 3: for a legal stage type `P` on `n` points, a closed face
`f` of `P` with restriction `p`, and a legal one-point coface `d` of `p`, some legal one-point
extension `Q` of `P` (a coface: its face along `Fin.castSuccEmb` is literally `P`) has face `d`
along `pinnedFace f`.

This is a hypothesis, not a theorem.  It is literally the conclusion of the exact pinned
extension of Layer 3, row 6, derived there from the coatom extension property
([Kni26, Corollary 4.3.22]). -/
def HasExactPinnedExtensions : Prop :=
  ∀ ⦃n m : ℕ⦄ ⦃P : StageType.{u} α n⦄ ⦃f : Fin m ↪ Fin n⦄ ⦃p : StageType.{u} α m⦄,
    P.IsLegal → restrictFace f P = some p →
      ∀ d ∈ p.cofaces, ∃ Q ∈ P.cofaces, restrictFace (pinnedFace f) Q = some d

variable (α) in
/-- **(C) Capped extension for the families** at stage `α`: every legal stage type has a coface in
each uniformity family for `γ` zero or a limit below the stage, and in each dominance family for
`γ` below the stage.  These are the uniformity and dominance instances of [Kni26, Lemma 4.4.1],
[Kni26, Lemmas 4.4.2 and 4.4.3], proved there by amalgamation through
[Kni26, Corollary 4.3.22].

This is a hypothesis, not a theorem.  The generalized-saturation and bottom-pattern instances need
no hypothesis: the corresponding clauses of `Realization.IsModel` are guarded by their
nonemptiness. -/
structure HasFamilyExtensions : Prop where
  /-- Every legal stage type has a coface in each uniformity family for `γ` zero or a limit below
  the stage. -/
  uniformity ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsLegal → ∀ γ : Ordinal.{u},
    Order.IsSuccPrelimit γ → γ < α → (p.cofaces ∩ uniformityFamily γ).Nonempty
  /-- Every legal stage type has a coface in each dominance family for `γ` below the stage. -/
  dominance ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsLegal → ∀ γ : Ordinal.{u}, γ < α →
    (p.cofaces ∩ dominanceFamily γ).Nonempty

/-- **One-point extensions**, from (E): every legal stage type has a coface.  This is (E) at the
empty face, with the one-point stage type as the coface. -/
theorem nonempty_cofaces_of_hasExactPinnedExtensions (hE : HasExactPinnedExtensions.{u} α)
    {P : StageType.{u} α n} (hP : P.IsLegal) : P.cofaces.Nonempty := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_isEmpty (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  obtain ⟨Q, hQ, -⟩ := hE hP hp _ (onePoint_mem_cofaces p)
  exact ⟨Q, hQ⟩

end Construction

/-! ### Realizing every coface -/

namespace Realization

variable (R : Realization.{u, v} α M)

/-- A realization **realizes every coface** when over every occurrence it realizes every coface of
the type of the occurrence.  For a model this is **saturation**, [Kni26, Definition 4.1.1]: if
`x` has type `p` and `q` is a one-point extension of `p`, some `y` has `x⁀y` of type `q`. -/
def RealizesCofaces : Prop :=
  ∀ (x : R.Occurrence), ∀ q ∈ x.type.cofaces, R.RealizesOver x.tuple {q}

variable {R}

/-- A realization that realizes every coface realizes every family with a member among the cofaces
of the type of an occurrence. -/
theorem RealizesCofaces.realizesOver (hs : R.RealizesCofaces) (x : R.Occurrence)
    {U : Set (StageType.{u} α (x.arity + 1))} (hU : (x.type.cofaces ∩ U).Nonempty) :
    R.RealizesOver x.tuple U :=
  let ⟨q, hq, hqU⟩ := hU
  (hs x q hq).mono (Set.singleton_subset_iff.mpr hqU)

/-- **Models from realizing every coface**, given (C): a realization on a nonempty carrier with
legal types that is exactly consistent and covering and realizes every coface is a model. -/
theorem isModel_of_realizesCofaces [Nonempty M] (hl : R.HasLegalTypes) (hR : R.IsConsistent)
    (hc : R.IsCovering) (hs : R.RealizesCofaces) (hC : Construction.HasFamilyExtensions.{u} α) :
    R.IsModel where
  nonempty := ‹_›
  isLegal := hl
  isConsistent := hR
  isCovering := hc
  saturation x _ := hs.realizesOver x
  bottomPattern x _ _ := hs.realizesOver x
  uniformity x γ hγ hγα := hs.realizesOver x (hC.uniformity _ (hl _ _ x.eval_tuple) γ hγ hγα)
  dominance x γ hγα := hs.realizesOver x (hC.dominance _ (hl _ _ x.eval_tuple) γ hγα)

/-- **Receiving from realizing every coface**: a realization that realizes every coface has the
finite-cut receiving property, since a coface lies in each of its receiving families. -/
theorem hasFiniteCutReceiving_of_realizesCofaces (hs : R.RealizesCofaces) :
    R.HasFiniteCutReceiving :=
  fun x d hd c _ ↦ (hs x d hd).mono (Set.singleton_subset_iff.mpr (self_mem_receivingFamily d c))

end Realization

/-! ### Requirements -/

namespace Construction

variable (α) in
/-- The **requirements** at stage `α`: a point `j` of `ℕ` to absorb, or a tuple `t` of `ℕ` with a
stage type `q` on one more point, to be realized over `t` if it is a coface of the type of `t`. -/
def Requirement : Type (u + 1) :=
  ℕ ⊕ Σ n : ℕ, (Fin n ↪ ℕ) × StageType.{u} α (n + 1)

/-- **Countably many requirements** at a stage with countably many ordinals below it. -/
theorem Requirement.countable (hα : (Set.Iio α).Countable) : Countable (Requirement.{u} α) := by
  have := StageType.countable hα
  have (n : ℕ) : Countable (Fin n ↪ ℕ) := Function.Injective.countable DFunLike.coe_injective
  unfold Requirement
  infer_instance

namespace Condition

variable {c d : Condition.{u} α} {t : Fin n ↪ ℕ}

/-- A condition **meets** a requirement: it has more than `j` points, for the absorption of `j`;
it supports `t` and, if `q` is a coface of the type of `t`, realizes `q` over `t`, for a tuple `t`
and a stage type `q`. -/
def Meets (c : Condition.{u} α) : Requirement.{u} α → Prop
  | .inl j => j < c.card
  | .inr ⟨_, t, q⟩ => IsSupported c.card t ∧
      ∀ p, c.realization.eval t = some p → q ∈ p.cofaces → c.realization.RealizesOver t {q}

/-- **Meeting a requirement persists** under extension. -/
theorem Meets.mono (hcd : c ≤ d) : ∀ {r : Requirement.{u} α}, c.Meets r → d.Meets r
  | .inl _, h => h.trans_le (card_le hcd)
  | .inr ⟨_, _, _⟩, ⟨hs, h⟩ => ⟨hs.mono (card_le hcd), fun p hp hq ↦
      realizesOver_of_le hcd (h p ((realization_eval_of_le hcd hs).symm.trans hp) hq)⟩

variable (hE : HasExactPinnedExtensions.{u} α)
include hE

/-- **Absorbing one point**, by one application of (E) at the empty face. -/
theorem exists_le_card_succ (c : Condition.{u} α) : ∃ d, c ≤ d ∧ d.card = c.card + 1 :=
  let ⟨Q, hQ⟩ := nonempty_cofaces_of_hasExactPinnedExtensions hE c.isLegal
  ⟨c.snoc Q hQ, le_snoc Q hQ, rfl⟩

/-- **Absorbing finitely many points**: every condition has an extension with more than `j`
points. -/
theorem exists_le_card_lt (c : Condition.{u} α) (j : ℕ) : ∃ d, c ≤ d ∧ j < d.card := by
  suffices h : ∀ N, ∃ d, c ≤ d ∧ N ≤ d.card from h (j + 1)
  intro N
  induction N with
  | zero => exact ⟨c, le_rfl, Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨d, hcd, hN⟩ := ih
    obtain ⟨e, hde, he⟩ := exists_le_card_succ hE d
    exact ⟨e, hcd.trans hde, by omega⟩

/-- **Absorbing a tuple**: every condition has an extension supporting a given tuple. -/
theorem exists_le_isSupported (c : Condition.{u} α) (t : Fin n ↪ ℕ) :
    ∃ d, c ≤ d ∧ IsSupported d.card t :=
  let ⟨d, hcd, hd⟩ := exists_le_card_lt hE c (univ.sup t)
  ⟨d, hcd, fun i ↦ (le_sup (f := t) (mem_univ i)).trans_lt hd⟩

/-- **Realizing a coface**, by one application of (E) at the face spanned by a supported typed
tuple: the new point, with the tuple, has the prescribed type. -/
theorem exists_le_realizesOver (c : Condition.{u} α) (h : IsSupported c.card t)
    {p : StageType.{u} α n} (hp : c.realization.eval t = some p) {q : StageType.{u} α (n + 1)}
    (hq : q ∈ p.cofaces) : ∃ d, c ≤ d ∧ d.realization.RealizesOver t {q} := by
  rw [realization_eval_of_isSupported h] at hp
  obtain ⟨Q, hQ, hQq⟩ := hE c.isLegal hp q hq
  refine ⟨c.snoc Q hQ, le_snoc Q hQ, (pinnedFace h.face).trans Fin.valEmbedding, ?_, q, rfl, ?_⟩
  · ext i
    simp
  · exact (StageType.chartRealization_eval_trans_valEmbedding _).trans hQq

/-- **Every requirement is met above every condition**, given (E). -/
theorem exists_le_meets (c : Condition.{u} α) : ∀ r : Requirement.{u} α, ∃ d, c ≤ d ∧ d.Meets r
  | .inl j => exists_le_card_lt hE c j
  | .inr ⟨_, t, q⟩ => by
    obtain ⟨d, hcd, hd⟩ := exists_le_isSupported hE c t
    by_cases hx : ∃ p, d.realization.eval t = some p ∧ q ∈ p.cofaces
    · obtain ⟨p, hp, hq⟩ := hx
      obtain ⟨e, hde, he⟩ := exists_le_realizesOver hE d hd hp hq
      exact ⟨e, hcd.trans hde, hd.mono (card_le hde), fun _ _ _ ↦ he⟩
    · exact ⟨d, hcd, hd, fun p hp hq ↦ absurd ⟨p, hp, hq⟩ hx⟩

end Condition

/-! ### The chain and its union -/

namespace Condition

variable (α) in
/-- **The one-point condition**: the one-point chart. -/
def onePoint : Condition.{u} α :=
  ⟨1, StageType.onePoint α, StageType.isLegal_onePoint α⟩

end Condition

/-- **The chain**, given (E) at a stage with countably many ordinals below it: a monotone sequence
of conditions, starting at a given condition `c₀`, that meets every requirement. -/
theorem exists_chain_forall_meets (hα : (Set.Iio α).Countable)
    (hE : HasExactPinnedExtensions.{u} α) (c₀ : Condition.{u} α) :
    ∃ c : ℕ → Condition.{u} α, c 0 = c₀ ∧ Monotone c ∧
      ∀ r : Requirement.{u} α, ∃ i, (c i).Meets r := by
  have := Requirement.countable hα
  exact exists_monotone_forall_exists_mem c₀ (fun r ↦ {c | c.Meets r})
    fun r c _ ↦ let ⟨d, hcd, hd⟩ := Condition.exists_le_meets hE c r; ⟨d, hd, hcd⟩

/-- **The union theorem**: the union of a monotone sequence of conditions meeting every requirement
has legal types, is exactly consistent and covering, and realizes every coface. -/
theorem realizesCofaces_chainUnion {c : ℕ → Condition.{u} α} (hc : Monotone c)
    (h : ∀ r : Requirement.{u} α, ∃ i, (c i).Meets r) :
    (chainUnion c).HasLegalTypes ∧ (chainUnion c).IsConsistent ∧ (chainUnion c).IsCovering ∧
      (chainUnion c).RealizesCofaces := by
  refine ⟨hasLegalTypes_chainUnion hc, isConsistent_chainUnion hc,
    (isCovering_chainUnion_iff hc).mpr fun j ↦ h (.inl j), fun x q hq ↦ ?_⟩
  obtain ⟨i, hs, hi⟩ := h (.inr ⟨x.arity, x.tuple, q⟩)
  have hx : (c i).realization.eval x.tuple = some x.type :=
    (chainUnion_eval_of_isSupported hc hs).symm.trans x.eval_tuple
  obtain ⟨u, hu, q', hq', he⟩ := hi x.type hx hq
  exact ⟨u, hu, q', hq', (chainUnion_eval_of_isSupported hc
    (Condition.isSupported_of_isSome (by rw [he]; rfl))).trans he⟩

/-- **Every condition extends to a realization of every coface**, given (E) at a stage with
countably many ordinals below it: a realization on `ℕ` with legal types that is exactly consistent
and covering, realizes every coface, and gives every tuple supported by `c₀` its type in `c₀`. -/
theorem Condition.exists_realizesCofaces_of_hasExactPinnedExtensions (c₀ : Condition.{u} α)
    (hα : (Set.Iio α).Countable) (hE : HasExactPinnedExtensions.{u} α) :
    ∃ R : Realization.{u, 0} α ℕ,
      R.HasLegalTypes ∧ R.IsConsistent ∧ R.IsCovering ∧ R.RealizesCofaces ∧
        ∀ ⦃n : ℕ⦄ ⦃t : Fin n ↪ ℕ⦄, IsSupported c₀.card t → R.eval t = c₀.realization.eval t := by
  obtain ⟨c, rfl, hc, h⟩ := exists_chain_forall_meets hα hE c₀
  obtain ⟨hl, hR, hcov, hs⟩ := realizesCofaces_chainUnion hc h
  exact ⟨_, hl, hR, hcov, hs, fun _ _ ht ↦ chainUnion_eval_of_isSupported hc ht⟩

/-- **Every condition extends to a countable saturated model**, conditional on the finite
extension statements: given (E) and (C) at a stage with countably many ordinals below it, a model
on `ℕ` that realizes every coface ([Kni26, Definition 4.1.1]) and gives every tuple supported by
`c₀` its type in `c₀`. -/
theorem Condition.exists_isModel_of_extensions (c₀ : Condition.{u} α)
    (hα : (Set.Iio α).Countable) (hE : HasExactPinnedExtensions.{u} α)
    (hC : HasFamilyExtensions.{u} α) :
    ∃ R : Realization.{u, 0} α ℕ, R.IsModel ∧ R.RealizesCofaces ∧
      ∀ ⦃n : ℕ⦄ ⦃t : Fin n ↪ ℕ⦄, IsSupported c₀.card t → R.eval t = c₀.realization.eval t :=
  let ⟨R, hl, hR, hc, hs, h₀⟩ := c₀.exists_realizesCofaces_of_hasExactPinnedExtensions hα hE
  ⟨R, R.isModel_of_realizesCofaces hl hR hc hs hC, hs, h₀⟩

/-- **A countable realization of every coface**, given (E) at a stage with countably many
ordinals below it: a realization on `ℕ` with legal types that is exactly consistent and covering
and realizes every coface.  This is the extension of the one-point condition. -/
theorem exists_realizesCofaces_of_hasExactPinnedExtensions (hα : (Set.Iio α).Countable)
    (hE : HasExactPinnedExtensions.{u} α) :
    ∃ R : Realization.{u, 0} α ℕ,
      R.HasLegalTypes ∧ R.IsConsistent ∧ R.IsCovering ∧ R.RealizesCofaces :=
  let ⟨R, hl, hR, hc, hs, _⟩ :=
    (Condition.onePoint α).exists_realizesCofaces_of_hasExactPinnedExtensions hα hE
  ⟨R, hl, hR, hc, hs⟩

/-- **Countable saturated models** [Kni26, Proposition 4.4.5], **conditional on the finite
extension statements**: given the exact one-point pinned extension (E) and the capped extensions
for the uniformity and dominance families (C), at a stage with countably many ordinals below it
there is a model on `ℕ` that realizes every coface, that is, a saturated model
([Kni26, Definition 4.1.1]).  This is the extension of the one-point condition. -/
theorem exists_isModel_of_extensions (hα : (Set.Iio α).Countable)
    (hE : HasExactPinnedExtensions.{u} α) (hC : HasFamilyExtensions.{u} α) :
    ∃ R : Realization.{u, 0} α ℕ, R.IsModel ∧ R.RealizesCofaces :=
  let ⟨R, hR, hs, _⟩ := (Condition.onePoint α).exists_isModel_of_extensions hα hE hC
  ⟨R, hR, hs⟩

open FirstOrder Language baseLanguage in
/-- **A countable model of the four-family sentence**, conditional on the finite extension
statements (E) and (C) at the base stage `ω`: the structure of the countable saturated model of
`exists_isModel_of_extensions` ([Kni26, Proposition 4.4.5]). -/
theorem exists_realize_fourFamilySentence_of_extensions
    (hE : HasExactPinnedExtensions.{u} Ordinal.omega0)
    (hC : HasFamilyExtensions.{u} Ordinal.omega0) :
    ∃ (M : Type) (_ : Countable M) (_ : baseLanguage.{u}.Structure M),
      fourFamilySentence.Realize M :=
  let ⟨R, hR, _⟩ := exists_isModel_of_extensions (Set.to_countable _) hE hC
  ⟨ℕ, inferInstance, R.toStructure, hR.realize_fourFamilySentence⟩

open FirstOrder Language baseLanguage in
/-- **A countable model of the density sentence**, conditional on the exact one-point pinned
extension (E) alone at the base stage `ω`: the structure of the realization of every coface of
`exists_realizesCofaces_of_hasExactPinnedExtensions`. -/
theorem exists_realize_densitySentence_of_hasExactPinnedExtensions
    (hE : HasExactPinnedExtensions.{u} Ordinal.omega0) :
    ∃ (M : Type) (_ : Countable M) (_ : baseLanguage.{u}.Structure M),
      densitySentence.Realize M := by
  obtain ⟨R, hl, hR, hc, hs⟩ :=
    exists_realizesCofaces_of_hasExactPinnedExtensions (Set.to_countable _) hE
  exact ⟨ℕ, inferInstance, R.toStructure, (realize_toStructure_densitySentence_iff hl).mpr
    ⟨inferInstance, hR, hc, R.hasFiniteCutReceiving_of_realizesCofaces hs⟩⟩

end Construction

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Families
import VaughtConjecture.Realization.Hull
import VaughtConjecture.Realization.Transport

/-!
# Models

Roadmap, Layer 2 (realizations with the four unchanged extension families; isomorphism transport
and reduction of models; directed actual covers); semantic contract, item 5 (the original
nonempty, exact consistency, covering, general-family, bottom-pattern, uniform-block, and
high-arity-dominance clauses; the families demand some suitable coface, not every prescribed
one).

A realization `R` **realizes a member of `U` over a tuple `t`** (`Realization.RealizesOver`) when
some typed tuple `u` on one more point, with `t` as its initial segment, has its type in `U`.  The
new point is automatically off `t`, since `u` is injective, and under exact consistency the type
of `u` is a coface of the type of `t` (`RealizesOver.inter_cofaces`).

A **model** (`Realization.IsModel`) is a realization on a nonempty carrier whose types are legal,
which is exactly consistent and covering, and which realizes, over every occurrence of type `p`, a
member of the families of `VaughtConjecture.Realization.Families`:

* generalized saturation, for every scheme `S` on one more point with a coface of `p` on `S`
  (`IsModel.saturation`);
* the bottom pattern, for every scheme `S` and labelling `ρ` of its cells with a coface of `p` in
  the family (`IsModel.bottomPattern`);
* uniformity, for every `γ` that is zero or a limit and below the stage (`IsModel.uniformity`);
* high-arity dominance, for every `γ` below the stage (`IsModel.dominance`).

**Limit stages and nonempty instances.**  The source defines models only at limit stages
`α ≤ ω₁` ([Kni26, Definition 3.2.1]), and at such stages every instance of the four families is
nonempty ([Kni26, Lemma 4.4.1], proved through [Kni26, Lemmas 4.4.2–4.4.4], the first two by
amalgamation through [Kni26, Corollary 4.3.22], with [Kni26, Lemma 4.2.2] for the seed).  Here
`IsModel` is defined at every stage.  The uniformity and
dominance clauses are stated as in the source, for every `γ` in the range of the source; at a
successor stage they can fail outright: at stage `1` the uniformity family for `γ = 0` is empty,
so there is no model at stage `1` (`VaughtConjecture.Realization.ModelExamples`).  The
generalized-saturation and bottom-pattern clauses are stated guarded, for the instances with a
member among the cofaces of `p`.  At a stage that is zero or a limit the side conditions of the
source make those instances nonempty (`StageType.nonempty_cofaces_inter_saturationFamily`,
`StageType.nonempty_cofaces_inter_bottomPatternFamily`, as in [Kni26, Lemma 4.4.4]), so the
guarded clauses imply those of the source (`IsModel.saturation_of_isLegal`,
`IsModel.bottomPattern_of_isLawful`).  Conversely, a nonempty instance satisfies the side
conditions of the source: for generalized saturation they are exactly its nonemptiness
(`StageType.nonempty_cofaces_inter_saturationFamily_iff`), and a nonempty bottom-pattern family
is that of the labels of any of its members, a lawful section extending the labels of `p`
(`StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`).  So there the guarded clauses are
equivalent to those of the source.  That a model is infinite will use the dominance clause at
`γ = 0` at a positive stage.

**Transport and reduction.**  Modelhood is preserved and reflected by transport along a bijection
of carriers (`isModel_map_iff`), hence invariant under isomorphism (`IsIso.isModel_iff`), where an
isomorphism `R.Iso S` is a bijection of carriers carrying `R` to `S` and isomorphism is an
equivalence relation (`isoSetoid`) preserved by stage reduction (`IsIso.reduce`).  The reduction
of a model at a stage `α` that is zero or a limit to a limit stage `0 < β ≤ α` is a model
(`IsModel.reduce`).  Each family reduces into itself (`StageType.reduce_mem_saturationFamily`, …),
so the uniformity and dominance clauses reduce directly (`IsModel.reduce_uniformity`,
`IsModel.reduce_dominance`): the block `[γ, γ + ω)` of `γ < β` lies below `β`.  For the guarded
clauses, each nonempty instance at `β` lifts to a nonempty instance at `α`: a coface at `β` of the
reduced type lifts, by bountifulness of its scheme, to a coface at `α` with the same scheme and
the same capped observation at a self-visible cap below `β` (`StageType.exists_isLawful_lift`).
The caps are `⊥` for saturation (`IsModel.reduce_saturation`, any `β` that is zero or a limit)
and a positive ordinal below `β` for the bottom pattern (`IsModel.reduce_bottomPattern`, which
therefore needs `β ≠ 0`).  The stage `α` must be zero or a limit so that the lifted labels can be
reduced to stage `α` lawfully; stages of models in the source are limits.

**Directed covers.**  Occurrences are preordered by inclusion of supports; under exact consistency
`x ≤ y` says that `x` is a face of `y` with the restricted type
(`Occurrence.le_iff_exists_restrictFace`).  Under covering the occurrences containing any finite
set are nonempty (`IsCovering.nonempty_setOf_subset_support`) and directed
(`IsCovering.directedOn_setOf_subset_support`); in particular the occurrences form a directed
preorder (`IsCovering.isDirected`).

## Placement

`Realization.Occurrence.comap` and its `simp` lemmas belong in
`VaughtConjecture.Realization.Transport`, beside `Realization.Occurrence.map`.  They are stated
here so that that file is unchanged.

## References

Models are [Kni26, Definition 3.2.1]: its clause 1 (arity: a defined value on `n` points is a type
on `n` points, here a legal stage type) is the legality field, clause 2 is exact consistency,
clause 3 covering, and clause 4 the four existential-closure clauses.  The reduction of a model is
[Kni26, Definition 5.1.1], and that it exists uniquely is [Kni26, Lemma 5.2.1]; the reduction
of a realization is unique by definition, and `IsModel.reduce` is its modelhood, for R. W. Knight,
*A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft, 20 February
2026).
-/

universe u v w x

namespace VaughtConjecture.Realization

open Finset Label StageType

variable {α β : Ordinal.{u}} {M : Type v} {N : Type w} {P : Type x} {n : ℕ}

/-! ### Realizing a family over a tuple -/

section RealizesOver

variable (R : Realization.{u, v} α M)

/-- `R` **realizes a member of `U` over `t`**: some typed tuple on one more point, with `t` as its
initial segment, has its type in `U`. -/
def RealizesOver (t : Fin n ↪ M) (U : Set (StageType.{u} α (n + 1))) : Prop :=
  ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ ∃ q ∈ U, R.eval u = some q

variable {R} {t : Fin n ↪ M} {U U' : Set (StageType.{u} α (n + 1))}

/-- Realizing a member of a family realizes a member of every larger family. -/
theorem RealizesOver.mono (h : R.RealizesOver t U) (hU : U ⊆ U') : R.RealizesOver t U' := by
  obtain ⟨u, hu, q, hq, he⟩ := h
  exact ⟨u, hu, q, hU hq, he⟩

/-- The new point of a realizing tuple is off the old tuple. -/
theorem RealizesOver.exists_notMem (h : R.RealizesOver t U) :
    ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ u (Fin.last n) ∉ Set.range t ∧
      ∃ q ∈ U, R.eval u = some q := by
  obtain ⟨u, rfl, hq⟩ := h
  refine ⟨u, rfl, ?_, hq⟩
  rintro ⟨i, hi⟩
  exact (Fin.castSucc_lt_last i).ne (u.injective hi)

/-- **Realized types are cofaces**: under exact consistency, with legal types, a realized member
over an occurrence is a coface of its type. -/
theorem RealizesOver.inter_cofaces (hR : R.IsConsistent)
    (hl : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (p : StageType.{u} α m), R.eval s = some p → p.IsLegal)
    {y : R.Occurrence} {U : Set (StageType.{u} α (y.arity + 1))} (h : R.RealizesOver y.tuple U) :
    R.RealizesOver y.tuple (y.type.cofaces ∩ U) := by
  obtain ⟨u, hu, q, hq, he⟩ := h
  refine ⟨u, hu, q, ⟨⟨hl u q he, ?_⟩, hq⟩, he⟩
  rw [← hR u q _ he, hu, y.eval_tuple]

/-- Realizing over a tuple of the transport is realizing over its preimage. -/
theorem realizesOver_map_iff (e : M ≃ N) {t : Fin n ↪ N} :
    (R.map e).RealizesOver t U ↔ R.RealizesOver (t.trans e.symm.toEmbedding) U := by
  refine ⟨fun ⟨u, hu, q, hq, he⟩ ↦ ⟨u.trans e.symm.toEmbedding, ?_, q, hq, he⟩,
    fun ⟨u, hu, q, hq, he⟩ ↦ ⟨u.trans e.toEmbedding, ?_, q, hq, by rwa [map_eval_trans]⟩⟩
  · rw [← hu]
    rfl
  · ext i
    simpa using congrArg (e ·) (DFunLike.congr_fun hu i)

/-- Realized members reduce: if every member of `U` reduces into `U'`, a realization of `U` over
`t` gives a realization of `U'` over `t` in the stage reduction. -/
theorem RealizesOver.reduce {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    {U' : Set (StageType.{u} β (n + 1))} (h : R.RealizesOver t U)
    (hU : ∀ q ∈ U, q.reduce hβ ∈ U') : (R.reduce hβ).RealizesOver t U' := by
  obtain ⟨u, hu, q, hq, he⟩ := h
  exact ⟨u, hu, q.reduce hβ, hU q hq, by rw [reduce_eval, he, Option.map_some]⟩

end RealizesOver

/-! ### Models -/

variable (R : Realization.{u, v} α M)

/-- A **model** at stage `α` [Kni26, Definition 3.2.1]: a realization on a nonempty carrier with
legal types that is exactly consistent and covering and that, over every occurrence, realizes a
member of each instance of the four families: of the uniformity and dominance families for every
`γ` in the range of the source, and of the generalized-saturation and bottom-pattern families
whenever the instance has a member among the cofaces of its type.

The source defines models only at limit stages `α`, where every instance is nonempty
[Kni26, Lemma 4.4.1]; here the definition is made at every stage, and at a stage that is zero or
a limit the guarded clauses are equivalent to those of the source: they imply them
(`IsModel.saturation_of_isLegal`, `IsModel.bottomPattern_of_isLawful`), and every nonempty
instance is one of the source (`StageType.nonempty_cofaces_inter_saturationFamily_iff`,
`StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`). -/
structure IsModel : Prop where
  /-- The carrier is nonempty. -/
  nonempty : Nonempty M
  /-- Clause 1: every type is legal. -/
  isLegal ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n) : R.eval t = some p → p.IsLegal
  /-- Clause 2: exact consistency. -/
  isConsistent : R.IsConsistent
  /-- Clause 3: covering. -/
  isCovering : R.IsCovering
  /-- Clause 4(a)i, generalized saturation. -/
  saturation (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) :
    (x.type.cofaces ∩ saturationFamily S).Nonempty → R.RealizesOver x.tuple (saturationFamily S)
  /-- Clause 4(a)ii, the bottom pattern. -/
  bottomPattern (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) (ρ : Fin S.card → Label.{u}) :
    (x.type.cofaces ∩ bottomPatternFamily S ρ).Nonempty →
      R.RealizesOver x.tuple (bottomPatternFamily S ρ)
  /-- Clause 4(b), uniformity, for `γ` that is zero or a limit and below the stage. -/
  uniformity (x : R.Occurrence) (γ : Ordinal.{u}) : Order.IsSuccPrelimit γ → γ < α →
    R.RealizesOver x.tuple (uniformityFamily γ)
  /-- Clause 4(c), high-arity dominance, for `γ` below the stage. -/
  dominance (x : R.Occurrence) (γ : Ordinal.{u}) : γ < α →
    R.RealizesOver x.tuple (dominanceFamily γ)

variable {R}

/-- A model has an occurrence. -/
theorem IsModel.nonempty_occurrence (hR : R.IsModel) : Nonempty R.Occurrence :=
  hR.isCovering.nonempty_occurrence

/-- **The saturation clause of the source**: at a stage that is zero or a limit, a model realizes,
over every occurrence of type `p`, a coface of `p` on every legal scheme `S` whose face along the
initial segment is the scheme of `p`. -/
theorem IsModel.saturation_of_isLegal (hR : R.IsModel) (hα : Order.IsSuccPrelimit α)
    (x : R.Occurrence) {S : Scheme.{u} (x.arity + 1)} (hS : S.IsLegal)
    (hf : univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces)
    (hp : S.comap Fin.castSuccEmb = x.type.toScheme) :
    R.RealizesOver x.tuple (x.type.cofaces ∩ saturationFamily S) :=
  (hR.saturation x S (nonempty_cofaces_inter_saturationFamily hα hS hf hp)).inter_cofaces
    hR.isConsistent hR.isLegal

/-- **The bottom-pattern clause of the source**: at a stage that is zero or a limit, a model
realizes, over every occurrence of type `p`, a coface of `p` on every legal scheme `S` extending
the scheme of `p`, with the bottom pattern of any lawful section of `S` extending the labels of
`p`. -/
theorem IsModel.bottomPattern_of_isLawful (hR : R.IsModel) (hα : Order.IsSuccPrelimit α)
    (x : R.Occurrence) {S : Scheme.{u} (x.arity + 1)} (hS : S.IsLegal)
    (hf : univ.map Fin.castSuccEmb ∈ S.toCellScheme.faces)
    (hp : S.comap Fin.castSuccEmb = x.type.toScheme) {ρ : Fin S.card → Label.{u}}
    (hρ : S.rows.IsLawful ρ)
    (hext : ∀ (i : Fin (S.comap Fin.castSuccEmb).card) (j : Fin x.type.card), (i : ℕ) = j →
      ρ (S.cellMap Fin.castSuccEmb i) = x.type.label j) :
    R.RealizesOver x.tuple (x.type.cofaces ∩ bottomPatternFamily S ρ) :=
  (hR.bottomPattern x S ρ (nonempty_cofaces_inter_bottomPatternFamily hα hS hf hp hρ hext)
    ).inter_cofaces hR.isConsistent hR.isLegal

/-! ### Transport along a bijection of carriers -/

/-- The occurrence of `R` underlying an occurrence of the transport: the preimage tuple with the
same type. -/
def Occurrence.comap (e : M ≃ N) (y : (R.map e).Occurrence) : R.Occurrence where
  arity := y.arity
  tuple := y.tuple.trans e.symm.toEmbedding
  type := y.type
  eval_tuple := y.eval_tuple

/-- The tuple of the underlying occurrence is the preimage tuple. -/
@[simp] theorem Occurrence.comap_tuple (e : M ≃ N) (y : (R.map e).Occurrence) :
    (y.comap e).tuple = y.tuple.trans e.symm.toEmbedding := rfl

/-- The type of the underlying occurrence is unchanged. -/
@[simp] theorem Occurrence.comap_type (e : M ≃ N) (y : (R.map e).Occurrence) :
    (y.comap e).type = y.type := rfl

/-- **Transport of models** along a bijection of carriers. -/
theorem IsModel.map (hR : R.IsModel) (e : M ≃ N) : (R.map e).IsModel where
  nonempty := hR.nonempty.map e
  isLegal _ t p hp := hR.isLegal (t.trans e.symm.toEmbedding) p hp
  isConsistent := hR.isConsistent.map e
  isCovering := hR.isCovering.map e
  saturation y S hne := (realizesOver_map_iff e).mpr (hR.saturation (y.comap e) S hne)
  bottomPattern y S ρ hne := (realizesOver_map_iff e).mpr (hR.bottomPattern (y.comap e) S ρ hne)
  uniformity y γ hγ hγα := (realizesOver_map_iff e).mpr (hR.uniformity (y.comap e) γ hγ hγα)
  dominance y γ hγα := (realizesOver_map_iff e).mpr (hR.dominance (y.comap e) γ hγα)

/-- Modelhood is preserved and reflected by transport. -/
@[simp] theorem isModel_map_iff (e : M ≃ N) : (R.map e).IsModel ↔ R.IsModel :=
  ⟨fun h ↦ map_symm_map R e ▸ h.map e.symm, fun h ↦ h.map e⟩

/-! ### Stage reduction -/

section Reduce

variable (hR : R.IsModel)
include hR

/-- **Saturation reduces**: at every stage `β` that is zero or a limit, the stage reduction of a
model satisfies the saturation clause.  A coface at `β` lifts at the cap `⊥`. -/
theorem IsModel.reduce_saturation (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccPrelimit β)
    (y : (R.reduce hβ).Occurrence) (S : Scheme.{u} (y.arity + 1))
    (hne : (y.type.cofaces ∩ saturationFamily S).Nonempty) :
    (R.reduce hβ).RealizesOver y.tuple (saturationFamily S) := by
  obtain ⟨x, rfl⟩ := Occurrence.exists_reduce_eq hβ y
  obtain ⟨q', hq', hS⟩ := hne
  obtain ⟨ρ, hρ, -, hext⟩ := exists_isLawful_lift (p := x.type) hβ hq'.1 hq'.2
    (isSelfVisible_bot _) bot_le
  exact (hR.saturation x S ⟨_, ofIsLawful_mem_cofaces_of_lift hα hβ hq' hρ hext, hS⟩).reduce hβ
    fun _ ↦ reduce_mem_saturationFamily hβ

/-- **The bottom pattern reduces** to every limit stage `β > 0`.  A coface at `β` lifts at a
positive self-visible cap below `β`, which keeps the bottom pattern. -/
theorem IsModel.reduce_bottomPattern (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccLimit β)
    (y : (R.reduce hβ.isSuccPrelimit).Occurrence) (S : Scheme.{u} (y.arity + 1))
    (ρ : Fin S.card → Label.{u}) (hne : (y.type.cofaces ∩ bottomPatternFamily S ρ).Nonempty) :
    (R.reduce hβ.isSuccPrelimit).RealizesOver y.tuple (bottomPatternFamily S ρ) := by
  obtain ⟨x, rfl⟩ := Occurrence.exists_reduce_eq _ y
  obtain ⟨q', hq', hS, hpat⟩ := hne
  obtain ⟨c, hc0, hcβ, hc⟩ :=
    exists_lt_lt_isSelfVisible hβ.isSuccPrelimit
      (by simpa [Ordinal.bot_eq_zero] using hβ.bot_lt)
      (x.arity + 1)
  obtain ⟨ρ', hρ', hρc, hext⟩ := exists_isLawful_lift (p := x.type) hβ.isSuccPrelimit hq'.1 hq'.2
    hc (by exact_mod_cast hcβ.le)
  have hcb : (c : Label.{u}) ≠ ⊥ := WithBot.coe_ne_bot
  have key (d : Fin q'.card) : ρ' d = ⊥ ↔ q'.label d = ⊥ := by
    simpa only [eq_iff_iff, min_eq_bot, hcb, or_false] using congrArg (· = ⊥) (hρc d)
  exact (hR.bottomPattern x S ρ ⟨_, ofIsLawful_mem_cofaces_of_lift hα hβ.isSuccPrelimit hq' hρ'
    hext, hS, fun i j hij hg ↦ reduce_eq_bot_iff.trans ((key i).trans (hpat i j hij hg))⟩).reduce _
    fun _ ↦ reduce_mem_bottomPatternFamily _

variable {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) (hβα : β ≤ α)
include hβ hβα

/-- **Uniformity reduces** to every stage `β ≤ α` that is zero or a limit: for `γ < β` the block
`[γ, γ + ω)` lies below `β`, so stage reduction keeps a realized member of the family. -/
theorem IsModel.reduce_uniformity (y : (R.reduce hβ).Occurrence) (γ : Ordinal.{u})
    (hγ : Order.IsSuccPrelimit γ) (hγβ : γ < β) :
    (R.reduce hβ).RealizesOver y.tuple (uniformityFamily γ) := by
  obtain ⟨x, rfl⟩ := Occurrence.exists_reduce_eq hβ y
  exact (hR.uniformity x γ hγ (hγβ.trans_le hβα)).reduce hβ fun _ ↦
    reduce_mem_uniformityFamily hβ hγβ

/-- **Dominance reduces** to every stage `β ≤ α` that is zero or a limit: stage reduction never
lowers a label. -/
theorem IsModel.reduce_dominance (y : (R.reduce hβ).Occurrence) (γ : Ordinal.{u}) (hγβ : γ < β) :
    (R.reduce hβ).RealizesOver y.tuple (dominanceFamily γ) := by
  obtain ⟨x, rfl⟩ := Occurrence.exists_reduce_eq hβ y
  exact (hR.dominance x γ (hγβ.trans_le hβα)).reduce hβ fun _ ↦ reduce_mem_dominanceFamily hβ

end Reduce

/-- **Reduction of models** [Kni26, Definition 5.1.1]: the stage reduction of a model at a stage
`α` that is zero or a limit to a limit stage `0 < β ≤ α` is a model; this is [Kni26, Lemma 5.2.1]
for `β ≠ 0`.  The reduction to stage 0 is not covered: the reduction of the bottom-pattern
clause lifts at a positive self-visible cap `c ≤ β`, and there is none when `β = 0`.  The base
stage of the construction is `ω`. -/
theorem IsModel.reduce (hR : R.IsModel) (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccLimit β)
    (hβα : β ≤ α) : (R.reduce hβ.isSuccPrelimit).IsModel where
  nonempty := hR.nonempty
  isLegal _ t p hp := by
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
    exact (hR.isLegal t p' hp').reduce _
  isConsistent := hR.isConsistent.reduce _
  isCovering := hR.isCovering.reduce _
  saturation := hR.reduce_saturation hα _
  bottomPattern := hR.reduce_bottomPattern hα hβ
  uniformity := hR.reduce_uniformity _ hβα
  dominance := hR.reduce_dominance _ hβα

/-! ### Isomorphisms -/

section Iso

variable (R) in
/-- An **isomorphism** from `R` to a realization `S` on `N`: a bijection of carriers carrying `R`
to `S`. -/
def Iso (S : Realization.{u, w} α N) : Type (max v w) :=
  {e : M ≃ N // R.map e = S}

variable (R) in
/-- `R` and `S` are **isomorphic**. -/
def IsIso (S : Realization.{u, w} α N) : Prop :=
  Nonempty (R.Iso S)

variable {S : Realization.{u, w} α N} {T : Realization.{u, x} α P}

variable (R) in
/-- The identity isomorphism. -/
def Iso.refl : R.Iso R :=
  ⟨Equiv.refl M, map_refl R⟩

/-- The inverse of an isomorphism. -/
def Iso.symm (i : R.Iso S) : S.Iso R :=
  ⟨i.1.symm, by obtain ⟨e, rfl⟩ := i; exact map_symm_map R e⟩

/-- The composite of two isomorphisms. -/
def Iso.trans (i : R.Iso S) (j : S.Iso T) : R.Iso T :=
  ⟨i.1.trans j.1, by obtain ⟨e, rfl⟩ := i; obtain ⟨e', rfl⟩ := j; exact (map_map R e e').symm⟩

/-- Transport along `e` is isomorphic to the original realization. -/
theorem isIso_map (e : M ≃ N) : R.IsIso (R.map e) :=
  ⟨⟨e, rfl⟩⟩

/-- Every realization is isomorphic to itself. -/
theorem IsIso.refl (R : Realization.{u, v} α M) : R.IsIso R := ⟨Iso.refl R⟩

/-- Isomorphism is symmetric. -/
theorem IsIso.symm (h : R.IsIso S) : S.IsIso R := h.map Iso.symm

/-- Isomorphism is transitive. -/
theorem IsIso.trans (h : R.IsIso S) (h' : S.IsIso T) : R.IsIso T :=
  h.elim fun i ↦ h'.elim fun j ↦ ⟨i.trans j⟩

variable (α M) in
/-- **Realizations up to isomorphism**: isomorphism as an equivalence relation on the realizations
at stage `α` on the carrier `M`. -/
def isoSetoid : Setoid (Realization.{u, v} α M) where
  r := IsIso
  iseqv := ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

/-- The relation of `isoSetoid` is isomorphism. -/
@[simp] theorem isoSetoid_r {R R' : Realization.{u, v} α M} : (isoSetoid α M).r R R' ↔ R.IsIso R' :=
  Iff.rfl

/-- The stage reduction of an isomorphism. -/
def Iso.reduce (i : R.Iso S) (hβ : Order.IsSuccPrelimit β) : (R.reduce hβ).Iso (S.reduce hβ) :=
  ⟨i.1, by obtain ⟨e, rfl⟩ := i; exact (reduce_map R hβ e).symm⟩

/-- **Stage reduction preserves isomorphism.** -/
theorem IsIso.reduce (h : R.IsIso S) (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).IsIso (S.reduce hβ) :=
  h.map (Iso.reduce · hβ)

/-- **Modelhood is invariant under isomorphism.** -/
theorem IsIso.isModel_iff (h : R.IsIso S) : R.IsModel ↔ S.IsModel := by
  obtain ⟨e, rfl⟩ := h
  exact (isModel_map_iff e).symm

end Iso

/-! ### Directed covers -/

section Directed

/-- Occurrences are preordered by inclusion of supports. -/
instance : Preorder R.Occurrence :=
  Preorder.lift Occurrence.support

/-- One occurrence lies below another when its support is contained in the other's. -/
theorem Occurrence.le_def {y z : R.Occurrence} : y ≤ z ↔ y.support ⊆ z.support :=
  Iff.rfl

/-- **The face preorder**: under exact consistency, `y ≤ z` exactly when `y` is a face of `z`
with the restricted type. -/
theorem Occurrence.le_iff_exists_restrictFace (hR : R.IsConsistent) {y z : R.Occurrence} :
    y ≤ z ↔ ∃ f : Fin y.arity ↪ Fin z.arity, f.trans z.tuple = y.tuple ∧
      StageType.restrictFace f z.type = some y.type := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf, _⟩ ↦ ?_⟩
  · obtain ⟨f, hf⟩ := z.exists_trans_eq h
    exact ⟨f, hf, restrictFace_eq_of_eval hR z.eval_tuple f (hf ▸ y.eval_tuple)⟩
  · rw [le_def, Occurrence.support, Occurrence.support, ← hf, ← Finset.map_map]
    exact map_subset_map.mpr (subset_univ _)

/-- Under covering, some occurrence contains any given finite set. -/
theorem IsCovering.nonempty_setOf_subset_support (hc : R.IsCovering) (F : Finset M) :
    {y : R.Occurrence | F ⊆ y.support}.Nonempty :=
  hc.exists_subset_support F

/-- Under covering, the occurrences containing a finite set are directed. -/
theorem IsCovering.directedOn_setOf_subset_support (hc : R.IsCovering) (F : Finset M) :
    DirectedOn (· ≤ ·) {y : R.Occurrence | F ⊆ y.support} := by
  classical
  intro y hy z _
  obtain ⟨w, hw⟩ := hc.exists_subset_support (y.support ∪ z.support)
  exact ⟨w, hy.trans (subset_union_left.trans hw), subset_union_left.trans hw,
    subset_union_right.trans hw⟩

/-- **Directed covers**: under covering the occurrences form a directed preorder. -/
theorem IsCovering.isDirected (hc : R.IsCovering) : IsDirected R.Occurrence (· ≤ ·) := by
  have h := hc.directedOn_setOf_subset_support ∅
  simp only [Finset.empty_subset, Set.ofPred_true] at h
  exact directedOn_univ_iff.mp h

end Directed

end VaughtConjecture.Realization

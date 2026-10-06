/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.ScottDefinability
import InfinitaryLogic.Descriptive.SentenceSplits
import InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.FiniteSupportClosure
import InfinitaryLogic.TwoGeneratorCardinality
import InfinitaryLogic.OrdinalCountability
import InfinitaryLogic.Scott.OrbitRank
import InfinitaryLogic.Scott.OrbitFormulaThreshold
import InfinitaryLogic.Lomega1omega.LocalAutomorphism
import InfinitaryLogic.ScottProcess.RankComparison
import InfinitaryLogic.Scott.OrbitRankStabilization
import InfinitaryLogic.Descriptive.BFSeparation
import InfinitaryLogic.Lomega1omega.InHierarchy
import InfinitaryLogic.Scott.MontalbanComplexity
import InfinitaryLogic.Scott.ForgetParameters
import InfinitaryLogic.Scott.GradedMatching
import InfinitaryLogic.Scott.Height.Defs
import InfinitaryLogic.Scott.SentenceRecognition
import InfinitaryLogic.Descriptive.BFScattered
import InfinitaryLogic.Descriptive.BFScatteredSentence
import InfinitaryLogic.Topology.Perfect
import InfinitaryLogic.Scott.OrbitParameters
import InfinitaryLogic.Scott.InternalRankBounds
import InfinitaryLogic.Scott.IsolatingLevel
import InfinitaryLogic.UniformFixation
import InfinitaryLogic.OrdinalUtil
import InfinitaryLogic.Descriptive.BFConcentration
import ComputableModelTheory.Classical
import Mathlib.ModelTheory.Fraisse

/-! # Selected interfaces for the implementation roadmap

`IMPLEMENTATION.md` is authoritative; this file is nonexhaustive.  It contains no admitted
proofs or axioms.  The abstract structures below state hypotheses; they are NOT constructions of
the concrete finite objects: an instance of such a structure is never a substitute for the
construction its fields describe.  The file lives outside the build; check it with

  lake env lean -DautoImplicit=false -DwarningAsError=true -Dlinter.mathlibStandardSet=true \
    roadmap/SuggestedInterfaces.lean
-/

namespace Roadmap

universe u v w z

/-- Exact partial face maps, with the option monad recording invisible faces. -/
structure ChartSystem where
  Chart : ℕ → Type u
  restrict : {n m : ℕ} → (Fin n ↪ Fin m) → Chart m → Option (Chart n)
  restrict_id : ∀ {n} (p : Chart n), restrict (Function.Embedding.refl _) p = some p
  restrict_comp : ∀ {k n m} (f : Fin k ↪ Fin n) (g : Fin n ↪ Fin m)
    (p : Chart m) (q : Chart n), restrict g p = some q →
    restrict (f.trans g) p = restrict f q

namespace ChartSystem

variable (C : ChartSystem.{u})

/-- A realization is data; consistency and covering are separate laws. -/
structure Realization (M : Type v) where
  eval : {n : ℕ} → (Fin n ↪ M) → Option (C.Chart n)

variable {C} {M : Type v}

def Consistent (R : C.Realization M) : Prop :=
  ∀ {n m} (t : Fin m ↪ M) (p : C.Chart m) (f : Fin n ↪ Fin m),
    R.eval t = some p → R.eval (f.trans t) = C.restrict f p

def Covering (R : C.Realization M) : Prop :=
  ∀ {n} (t : Fin n ↪ M), ∃ (m : ℕ) (u : Fin m ↪ M) (f : Fin n ↪ Fin m),
    f.trans u = t ∧ (R.eval u).isSome

/-- The equations recording one realization of a diagram over a root must all concern this
same occurrence. -/
structure Occurrence (R : C.Realization M) where
  arity : ℕ
  tuple : Fin arity ↪ M
  chart : C.Chart arity
  eval_eq : R.eval tuple = some chart

@[simp] theorem eval_occurrence {R : C.Realization M} (x : Occurrence R) :
    R.eval x.tuple = some x.chart := x.eval_eq

/-- A visible restriction of an occurrence is actual, with its literal tuple. -/
theorem eval_face {R : C.Realization M} (hR : C.Consistent R) (x : Occurrence R)
    {n : ℕ} (f : Fin n ↪ Fin x.arity) {p : C.Chart n}
    (hf : C.restrict f x.chart = some p) : R.eval (f.trans x.tuple) = some p :=
  (hR x.tuple x.chart f x.eval_eq).trans hf

end ChartSystem

/-- Unique extension (injective restriction) turns per-cap lifts into simultaneous preservation.
Compatibility and the exact extension equation remain explicit; observations need not
themselves be lawful.  Injectivity of restriction is not available in general, and a largest
compatible self-visible cap need not exist; simultaneous preservation is not proved otherwise
and is not needed, since density asks for one extension for each cutoff (see
`IMPLEMENTATION.md`, layer 1). -/
theorem preserves_all_compatible_observations
    {A : Type u} {B : Type v} {Cut : Type w} {O : Type z}
    (restrict : A → B) (observe : Cut → A → O) (compatible : B → A → Cut → Prop)
    (hinj : Function.Injective restrict)
    (hlift : ∀ b a c, compatible b a c →
      ∃ x, restrict x = b ∧ observe c x = observe c a)
    {b : B} {x : A} (hx : restrict x = b) :
    ∀ a c, compatible b a c → observe c x = observe c a := by
  intro a c h
  obtain ⟨y, hy, ho⟩ := hlift b a c h
  exact (congrArg (observe c) (hinj (hx.trans hy.symm))).trans ho

/-- Domains of sentence agreement: countable-stage domains with countable complements, on each
of which every sentence (a predicate `truth θ` on the classes) is eventually constant, together
with separation of distinct classes by a sentence.  Applied AFTER countable-loss induction.
An instance of this structure is not a proof of the countable-loss or receiving constructions
in the README. -/
structure SentenceAgreementDomains (Q : Type 1) (Sent : Type u) (truth : Sent → Q → Prop) where
  /-- The domains, indexed by the countable stages only: no data is carried at or above `ω₁`. -/
  domain : Set.Iio (Cardinal.aleph 1).ord → Set Q
  complement_countable : ∀ η, (domain η)ᶜ.Countable
  homogeneous : ∀ θ, ∃ η, ∀ p ∈ domain η, ∀ q ∈ domain η, (truth θ p ↔ truth θ q)
  separates : ∀ p q, p ≠ q → ∃ θ, ¬ (truth θ p ↔ truth θ q)

namespace SentenceAgreementDomains

variable {Q : Type 1} {Sent : Type u} {truth : Sent → Q → Prop}
variable (F : SentenceAgreementDomains Q Sent truth)

/-- Scott separation makes the persistent core subsingleton; departure is unnecessary. -/
theorem persistent_subsingleton : (⋂ η, F.domain η).Subsingleton := by
  intro p hp q hq
  by_contra hne
  obtain ⟨θ, hθ⟩ := F.separates p q hne
  obtain ⟨η, hh⟩ := F.homogeneous θ
  exact hθ (hh p (Set.mem_iInter.mp hp η) q (Set.mem_iInter.mp hq η))

include F in
/-- Each sentence (the predicate `truth θ` on the classes) has one countable truth side,
without measurability on `Q`.  The library has the underlying split lemma,
`VaughtConjecture.Counting.countable_split_of_uniform_domain`; the proof is repeated here only
because this sketch does not import the library. -/
theorem countable_truth_side (θ : Sent) :
    ({q | truth θ q} : Set Q).Countable ∨ ({q | ¬ truth θ q} : Set Q).Countable := by
  obtain ⟨η, hh⟩ := F.homogeneous θ
  have hc := F.complement_countable η
  by_cases h : ∃ q ∈ F.domain η, truth θ q
  · obtain ⟨q, hq, ht⟩ := h
    exact Or.inr (hc.mono fun p hp hpd => hp ((hh p hpd q hq).mpr ht))
  · exact Or.inl (hc.mono fun q hq hqd => h ⟨q, hqd, hq⟩)

end SentenceAgreementDomains

-- Pinned upstream entry points: these #checks deliberately fail if the chosen APIs disappear.
-- A #check establishes a name and its signature at the pin, not that its hypotheses hold in any
-- setting of the roadmap; an application is claimed only where a compiled theorem applying it
-- is named (`README.md`, Layer 0).
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.ofExtensionFamily
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_sentence_of_countable_of_presentation
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_countable_aElementary_substructure
set_option linter.hashCommand false in
#check InfinitaryLogic.FiniteSupportClosure.setClosure
set_option linter.hashCommand false in
#check InfinitaryLogic.FiniteSupportClosure.mk_le_aleph_one
set_option linter.hashCommand false in
#check FirstOrder.Language.Sentenceω.isThinOnNatModels_of_countable_sentence_splits
set_option linter.hashCommand false in
#check InfinitaryLogic.compl_countable_of_loss
set_option linter.hashCommand false in
#check InfinitaryLogic.mk_eq_aleph_one_of_domains
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank_le_of_orbits_determined

-- InfinitaryLogic at the pin `eb9f12d` (signatures checked): the orbit-formula
-- threshold and rank bound and the preservation of infinitary formulas by maps agreeing locally
-- with automorphisms, imported through the two narrow modules (never `InfinitaryLogic.All`).
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormula.qrank_toLω_lt_omega0
set_option linter.hashCommand false in
#check FirstOrder.Language.orbit_determined_of_orbitFormula
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_finite_orbit_threshold
set_option linter.hashCommand false in
#check FirstOrder.Language.orbitRank_le_lift_qrank_of_orbitFormula
set_option linter.hashCommand false in
#check FirstOrder.Language.orbitRank_lt_omega0_of_orbitFormula
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank_le_omega0_of_orbitFormulas
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.realize_comp_of_localAutomorphisms
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.realize_comp_append_of_localAutomorphisms

-- The rank comparison of the Scott process (InfinitaryLogic, merged at `a640bbb`, contained in
-- the pin `eb9f12d`), through its two modules.
set_option linter.hashCommand false in
#check FirstOrder.Language.selfStabilizesCompletely_iff_orbitRank_le
set_option linter.hashCommand false in
#check FirstOrder.Language.bfStabilizationOrdinal_self_eq_iSup_orbitRank
set_option linter.hashCommand false in
#check InfinitaryLogic.ScottProcess.Semantic.stabilizesAt_of_orbitRank_le
set_option linter.hashCommand false in
#check InfinitaryLogic.ScottProcess.Semantic.rank_le_of_orbitRank_le
set_option linter.hashCommand false in
#check InfinitaryLogic.ScottProcess.Semantic.lift_rank_le_internalScottRank
set_option linter.hashCommand false in
#check InfinitaryLogic.ScottProcess.Semantic.internalScottRank_le_lift_rank_add_one

-- Mathlib's Fraïssé interface, to be applied by the classical limit of the top-free witnesses
-- (expected, not elaborated; `README.md`, Layer 0).  Representative classes, the factorization
-- of tuples through the age, orbit isolation, countable prime structures, and the classical
-- existence theorem of ComputableModelTheory at the pin `a1fe761` are checked below.
set_option linter.hashCommand false in
#check FirstOrder.Language.age
set_option linter.hashCommand false in
#check FirstOrder.Language.Hereditary
set_option linter.hashCommand false in
#check FirstOrder.Language.JointEmbedding
set_option linter.hashCommand false in
#check FirstOrder.Language.Amalgamation
set_option linter.hashCommand false in
#check FirstOrder.Language.IsFraisse
set_option linter.hashCommand false in
#check FirstOrder.Language.IsUltrahomogeneous
set_option linter.hashCommand false in
#check FirstOrder.Language.IsFraisseLimit
set_option linter.hashCommand false in
#check FirstOrder.Language.IsUltrahomogeneous.extend_embedding
set_option linter.hashCommand false in
#check FirstOrder.Language.IsFraisseLimit.nonempty_equiv
set_option linter.hashCommand false in
#check FirstOrder.Language.age.fg_substructure

-- InfinitaryLogic at the pin `eb9f12d` (signatures checked): uniform
-- back-and-forth separation of analytic sets of nonisomorphic pairs of codes
-- (`Descriptive/BFSeparation`); it enters the compiled `isThinOn_of_countable_bfClasses`
-- (`VaughtConjecture.MainTheorem.Scatteredness`; `README.md`, Layer 6) through InfinitaryLogic's
-- `isThinOn_of_bfScattered`, which that theorem quotes.
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_uniform_bfSeparation
set_option linter.hashCommand false in
#check FirstOrder.Language.CodeBFEquiv.monotone
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_uniform_bfSeparation_forall_ge
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_uniform_bfSeparation_of_analyticSets

-- InfinitaryLogic at the pin `eb9f12d` (signatures checked): the forward Karp
-- lemma, agreement on formulas of quantifier rank at most `α` from `BFEquiv α`, for a relational
-- language.  Its application to the expansion domains (condition 3 of `README.md`) is a
-- statement still to be proved; no application of it is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv_implies_agreeQR

-- The ordinal-indexed hierarchy (`Lomega1omega/InHierarchy`), at the pin `eb9f12d`
-- (signatures checked): the signed-traversal classes `IsSigmaIn`/`IsPiIn`, which are syntactic
-- classes, and the normal forms `IsSigmaInNF`/`IsPiInNF`, which lie in them; the converse,
-- up to logical equivalence, is not formalized (`README.md`, Layer 4).  A normal form at level
-- `a` has quantifier rank at most `ω · a` (`IsSigmaInNF.qrank_le`, `IsPiInNF.qrank_le`); the
-- signed classes carry no such bound.
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.inSigned
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsSigmaIn
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsPiIn
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsSigmaIn.isPiIn_add_one
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.isPiIn_einf
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.isSigmaIn_esup
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsSigmaInNF
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsPiInNF
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.NormalFormIn.inSigned
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsSigmaInNF.qrank_le
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.IsPiInNF.qrank_le

-- Montalbán's explicit Scott sentence from a family of orbit formulas and its complexity
-- (InfinitaryLogic, `Scott/MontalbanSentence` and `Scott/MontalbanComplexity`), at the pin
-- `eb9f12d` (signatures checked).  For a countable `M` in
-- a language with countably many relation symbols, a family `Φ n a : L.Formulaω (Fin n)` over
-- all tuples; `D_a` is `atomicDiagram a`, a countable conjunction of atoms and negated atoms
-- (`Π^in_1`).  If `1 ≤ α` and every `Φ n a` is `IsSigmaIn α`, the sentence is `IsPiIn (α + 1)`
-- (no orbit property, no relationality); the Scott-sentence corollaries add `[L.IsRelational]`;
-- orbit formulas in `IsSigmaIn 0` give a Scott sentence in `IsPiIn 2`.  It supplies *a* Scott
-- sentence, not the exact-age sentences of `README.md`, Layer 4; no application is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.atomicDiagram
set_option linter.hashCommand false in
#check FirstOrder.Language.IsOrbitFormulaFamily
set_option linter.hashCommand false in
#check FirstOrder.Language.montalbanSentence
set_option linter.hashCommand false in
#check FirstOrder.Language.realize_montalbanSentence
set_option linter.hashCommand false in
#check FirstOrder.Language.montalbanSentence_self
set_option linter.hashCommand false in
#check FirstOrder.Language.nonempty_equiv_of_realize_montalbanSentence
set_option linter.hashCommand false in
#check FirstOrder.Language.montalbanSentence_characterizes
set_option linter.hashCommand false in
#check FirstOrder.Language.IsOrbitFormulaFamilyPointed
set_option linter.hashCommand false in
#check FirstOrder.Language.montalbanSentencePointed
set_option linter.hashCommand false in
#check FirstOrder.Language.montalbanSentencePointed_characterizes
set_option linter.hashCommand false in
#check FirstOrder.Language.isPiIn_atomicDiagram
set_option linter.hashCommand false in
#check FirstOrder.Language.isPiIn_montalbanSentence
set_option linter.hashCommand false in
#check FirstOrder.Language.isPiIn_montalbanSentencePointed
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isPiIn_scottSentence_of_sigmaIn_orbits
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isPiIn_pointed_of_sigmaIn_orbits
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits

-- Graded matching (InfinitaryLogic, `Scott/GradedMatching`), available at the pin `eb9f12d`
-- (signatures checked).  A family `R α n a b` of relations between tuples, defined at every
-- ordinal, atomic at level `0`, lowering for `β ≤ α ≤ height`, and with forth and back one level
-- down for `α + 1 ≤ height`, relates at a level `α ≤ height` only `BFEquiv α` pairs; any language,
-- no relationality.  It is a generic form of the graded back-and-forth theorem of `README.md`,
-- Layer 0, whose initial match is a pair related at the height (`α = height`); each of its two
-- applications puts the height guard and the selection of coordinates inside `R` (`README.md`,
-- Layer 0).  Both applications are compiled through it in the library, on abstract hypotheses
-- (`VaughtConjecture.Comparison.GradedMatchingApplications`: approximate comparison,
-- `FullPresentation.bfEquiv_comp_of_obs_eq`, and condition 3 in back-and-forth form,
-- `ExpansionMatchData.bfEquiv_of_expansionMatch`); no application is compiled in this sketch.
set_option linter.hashCommand false in
#check FirstOrder.Language.bfEquiv_of_gradedMatching
set_option linter.hashCommand false in
#check FirstOrder.Language.bfEquiv_of_gradedSystem

-- Rank tails and the least level of a cover (InfinitaryLogic, `OrdinalCountability`), available
-- at the pin `eb9f12d` (signatures checked).  For `r : X → Ordinal` below `ω₁` with countable
-- fibres, a set is countable iff its ranks are bounded below `ω₁` (`countable_iff_rank_bounded`),
-- the tails `rankTail r η = {x | η ≤ r x}` have empty intersection below `ω₁`, have nonempty
-- losses cofinally below `ω₁` iff `X` is uncountable, and give `#X ≤ ℵ₁`, with `#X = ℵ₁` for an
-- uncountable `X`.  Domains with countable complements below `ω₁` that every point leaves give
-- `#X ≤ ℵ₁` (`mk_le_aleph_one_of_domains`).  Under the covering hypothesis
-- `hcover : ⋃ α < ω₁, Q α = univ`, the tails of `leastLevel Q` are the complements of the initial
-- unions of `Q`, and countable sets `Q α` give `leastLevel Q` countable fibres.  The generic
-- statements of `Counting/Filtration` and `Counting/Separation` are proved as quotations of these,
-- with their statements kept (`IMPLEMENTATION.md`, "Placement record"); no application is compiled
-- in this sketch.
set_option linter.hashCommand false in
#check InfinitaryLogic.countable_iff_rank_bounded
set_option linter.hashCommand false in
#check InfinitaryLogic.rankTail
set_option linter.hashCommand false in
#check InfinitaryLogic.leastLevel
set_option linter.hashCommand false in
#check InfinitaryLogic.countable_fibers_leastLevel
set_option linter.hashCommand false in
#check InfinitaryLogic.rankTail_leastLevel
set_option linter.hashCommand false in
#check InfinitaryLogic.mk_eq_aleph_one_of_countable_fibers
set_option linter.hashCommand false in
#check InfinitaryLogic.rankTail_cofinal_losses_iff
set_option linter.hashCommand false in
#check InfinitaryLogic.biInter_rankTail_eq_empty
set_option linter.hashCommand false in
#check InfinitaryLogic.mk_le_aleph_one_of_countable_fibers
set_option linter.hashCommand false in
#check InfinitaryLogic.mk_le_aleph_one_of_domains

-- The stabilization ordinal (`Scott/Sentence`) and the Scott height (`Scott/Height/Defs`) of a
-- countable structure, at the pin `eb9f12d` (signatures checked), with the Scott formula's rank
-- bound and characterization: the notions of the prospective one-sided rank comparison
-- (`COMPANIONS.md`, "Further companion results"); `stabilizationOrdinal_spec` and
-- `stabilizationOrdinal_lt_omega1'` (`Scott/RefinementCount`) give the per-class isolation level of
-- the Scott route (`README.md`, manuscript correspondence, item 5).  `stabilizationOrdinal M` is
-- the least level at which empty-tuple back-and-forth equivalence with `M` characterizes `M` among
-- the countable structures in its carrier universe (`StabilizesAt`); `scottHeight M` the least
-- level from which
-- back-and-forth equivalence of tuples of every length no longer refines.  Neither is
-- `internalScottRank`: an infinite pure set has internal Scott rank `1`
-- (`internalScottRank_pureSet`).  No application is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.StabilizesAt
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizationOrdinal
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizationOrdinal_spec
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizationOrdinal_lt_omega1'
set_option linter.hashCommand false in
#check FirstOrder.Language.scottHeight
set_option linter.hashCommand false in
#check FirstOrder.Language.scottHeight_stabilizesCompletely
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv_stabilization_implies_equiv
set_option linter.hashCommand false in
#check FirstOrder.Language.scottFormula_qrank_le
set_option linter.hashCommand false in
#check FirstOrder.Language.realize_scottFormula_iff_BFEquiv
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank_pureSet

-- Forgetting finitely many parameters (InfinitaryLogic, `Scott/ForgetParameters`), available at
-- the pin `eb9f12d` (signatures checked).  The existential closure `existsTuple k φ` of a formula
-- characterizing `(M, c)` is a Scott sentence of `M` among countable structures, and keeps the
-- class `Σ^in_α` for `1 ≤ α`; for a countable `M` in a countable relational language, `Σ^in_α`
-- orbits over a parameter tuple (`1 ≤ α`) give a `Σ^in_{α+2}` Scott sentence, and `Σ^in_1` orbits
-- over parameters a `Σ^in_3` one.  It serves the `Σ^in_3` Scott sentence obtained by
-- existentially quantifying a named rigid core (`README.md`, Layer 4; `COMPANIONS.md`, B4); no
-- application is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.existsTuple_isScott
set_option linter.hashCommand false in
#check FirstOrder.Language.isSigmaIn_existsTuple_iff
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isSigmaIn_three_scottSentence_of_sigmaIn_one_orbits_over

-- Quantifier rank and recognition, at the pin `eb9f12d` (signatures checked): the names cited by
-- the prospective quantitative-reconstruction pathway (`COMPANIONS.md`, "Further companion
-- results").  The rank of a formula (`BoundedFormulaω.qrank`); the existential closure
-- `existsTuple`, one quantifier of which adds one to the rank (`qrank_existsLastVar`; the closure
-- of `k` coordinates adds exactly `k`, `qrank_existsTuple`, checked below); one existential
-- quantifier of `L_{ω₁ω}` adds one (`BoundedFormulaω.qrank_ex`); the finite existential block over
-- the last `k` bound variables (`BoundedFormulaω.existsBlock`), by which the prospective
-- base-reduct orbit formulas are to eliminate the core coordinates while keeping the tuple's
-- coordinates free (its rank equation `qrank (existsBlock φ) = qrank φ + k` is a statement still
-- to be proved), after relabelling them as bound variables (`BoundedFormulaω.relabel`, which
-- preserves the rank, `BoundedFormulaω.qrank_relabel`); the characterization of a countable
-- structure by its Scott sentence among the countable structures in its carrier universe
-- (`scottSentence_characterizes`); and the orbit rank and internal Scott rank of the library.  The
-- rank bounds of the pathway, its recognition statements, and its base-reduct orbit-rank bounds
-- are prospective; no application is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank
set_option linter.hashCommand false in
#check FirstOrder.Language.existsTuple
set_option linter.hashCommand false in
#check FirstOrder.Language.qrank_existsLastVar
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.existsBlock
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank_ex
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.relabel
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank_relabel
set_option linter.hashCommand false in
#check FirstOrder.Language.scottSentence_characterizes
set_option linter.hashCommand false in
#check FirstOrder.Language.orbitRank
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank

-- ComputableModelTheory at the pin `a1fe761` (signatures checked), through the
-- entry module `ComputableModelTheory.Classical` (Mathlib-only imports): classical Fraïssé
-- existence (`ModelTheory/FraisseExistence`), rooted universality and uniqueness
-- (`ModelTheory/RootedExtension`), and isolation and primeness over named finite parameters
-- (`ModelTheory/NamedParameters`); representative classes, extension-rich families and direct
-- limits, the factorization of tuples through the age (`ModelTheory/RepresentativeAge`,
-- `ExtensionRichFamily`, `ExtensionRichDirectLimit`), orbit isolation and countable prime
-- structures (`ModelTheory/OrbitIsolation`, `CountablePrime`).  Of these, the library applies
-- `representativeClass_hereditary`, `representativeClass_countable_quotient`,
-- `isFraisse_representativeClass`, and `exists_isFraisseLimit_representativeClass` to the age of
-- top-free charts (`VaughtConjecture.ClassicalLimit.Age` and `.Amalgamation`; amalgamation and
-- the limit conditional on the coatom extension property); no other application is compiled in
-- this repository.
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_fraisseSequence
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isFraisseLimit_representativeClass
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isFraisseLimit_of_isFraisse
set_option linter.hashCommand false in
#check FirstOrder.Language.ExtendsRepresentatives
set_option linter.hashCommand false in
#check FirstOrder.Language.isExtensionPair_of_age_subset
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_embedding_comp_eq_of_age_subset_of_countable
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_equiv_comp_eq_of_age_subset_of_countable
set_option linter.hashCommand false in
#check FirstOrder.Language.isAtomic_named_of_orbit_formulas
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_elementaryEmbedding_named
set_option linter.hashCommand false in
#check FirstOrder.Language.representativeClass
set_option linter.hashCommand false in
#check FirstOrder.Language.isFraisse_representativeClass
set_option linter.hashCommand false in
#check FirstOrder.Language.representativeClass_countable_quotient
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_factor_tuple_of_age_subset
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_factor_embedding_of_age_subset
set_option linter.hashCommand false in
#check FirstOrder.Language.FGCofinal
set_option linter.hashCommand false in
#check FirstOrder.Language.ExtensionRich
set_option linter.hashCommand false in
#check FirstOrder.Language.isFraisseLimit_of_extensionRich
set_option linter.hashCommand false in
#check FirstOrder.Language.SequenceExtension
set_option linter.hashCommand false in
#check FirstOrder.Language.amalgamationRich_of_sequenceExtension
set_option linter.hashCommand false in
#check FirstOrder.Language.age_directLimit_eq
set_option linter.hashCommand false in
#check FirstOrder.Language.countable_directLimit
set_option linter.hashCommand false in
#check FirstOrder.Language.isFraisseLimit_directLimit
set_option linter.hashCommand false in
#check FirstOrder.Language.IsolatesTuple
set_option linter.hashCommand false in
#check FirstOrder.Language.IsAtomic
set_option linter.hashCommand false in
#check FirstOrder.Language.isolatesTuple_of_orbit_formula
set_option linter.hashCommand false in
#check FirstOrder.Language.isAtomic_of_orbit_formulas
set_option linter.hashCommand false in
#check FirstOrder.Language.IsolatesTuple.realize_iff
set_option linter.hashCommand false in
#check FirstOrder.Language.IsolatesTuple.typesWith_eq_singleton
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_elementaryEmbedding_of_countable_atomic

-- Thinness from countably many back-and-forth classes at every level (InfinitaryLogic,
-- `Descriptive/BFScattered` and `Descriptive/BFScatteredSentence`), available at the pin `eb9f12d`
-- (signatures checked).  `BFScattered K`: for every `η < ω₁` the restriction of
-- `codeBFEquivSetoid L η` (the library's `CodeBFEquiv η` as an equivalence relation) to `K` has
-- countably many classes, with no definability of `K`; for countably many relation symbols such a
-- `K` is thin, and so is a sentence whose coded models fall into countably many classes of
-- `bfEquivSetoid φ η` (the restriction, `bfEquivSetoid_eq_comap`) at every level.  It serves the
-- scatteredness form of thinness (`README.md`, Layer 6), and its compiled applications in this
-- repository are quotations (`MainTheorem/Scatteredness`): `isThinOn_of_countable_bfClasses` of
-- `isThinOn_of_bfScattered` (its hypothesis is `BFScattered K` by definition),
-- `isThinOnNatModels_of_countable_bfClasses` of `Sentenceω.isThinOnNatModels_of_bfScattered`,
-- `bfEquivSetoid_eq_comap` of its namesake, and the local `codeBFEquivSetoid` is this one by
-- definition.
set_option linter.hashCommand false in
#check FirstOrder.Language.BFScattered
set_option linter.hashCommand false in
#check FirstOrder.Language.codeBFEquivSetoid
set_option linter.hashCommand false in
#check FirstOrder.Language.isThinOn_of_bfScattered
set_option linter.hashCommand false in
#check FirstOrder.Language.bfEquivSetoid_eq_comap
set_option linter.hashCommand false in
#check FirstOrder.Language.Sentenceω.isThinOnNatModels_of_bfScattered

-- The cardinality of a nonempty perfect set (InfinitaryLogic, `Topology/Perfect`, a module with
-- Mathlib imports only), available at the pin `eb9f12d` (signatures checked): in a complete,
-- second-countable metric space it is the continuum.  Same name and statement as before its move
-- from `Descriptive/PerfectAntichain`; it is applied in `MainTheorem/Scatteredness`
-- (`not_countable_of_perfect`, a nonempty perfect set of codes is uncountable), a lemma of the
-- scatteredness form of thinness (`README.md`, Layer 6) kept with its statement and no longer used
-- by the thinness theorems, which quote InfinitaryLogic.
set_option linter.hashCommand false in
#check Perfect.mk_eq_continuum

-- Orbit-rank bounds and recognition at the rank of a Scott sentence (InfinitaryLogic,
-- `Scott/OrbitFormulaThreshold` and `Scott/SentenceRecognition`), available at the pin `eb9f12d`
-- (signatures checked; no application compiled in this repository), for relational languages.  An
-- infinitary orbit formula `φ : L.Formulaω (Fin n)` of a tuple bounds its orbit rank by
-- `Ordinal.lift φ.qrank`, and orbit formulas of rank `< α` for every tuple bound the internal Scott
-- rank by `Ordinal.lift α`: the shape of the prospective base-reduct orbit-rank bounds.  A formula
-- on `Fin 0`, read as a sentence (the form of the library's Scott sentences), of rank at most `β`
-- that characterizes a countable `M` among the countable structures in its carrier universe gives
-- `StabilizesAt M β` and `stabilizationOrdinal M ≤ β`: the shape of the prospective recognition of
-- a supplied model, through the empty tuple only.  Both serve the quantitative-reconstruction
-- pathway (`COMPANIONS.md`, "Further companion results").
set_option linter.hashCommand false in
#check FirstOrder.Language.orbitRank_le_lift_qrank_of_infinitaryOrbitFormula
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank_le_of_infinitaryOrbitFormulas
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizesAt_of_formula_rank
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizationOrdinal_le_of_formula_rank

-- Further names of the pin `eb9f12d` cited in `IMPLEMENTATION.md`, "Dependency pins"
-- (signatures checked; no application compiled in this repository).  Isomorphisms
-- transport atomic types and back-and-forth equivalence of tuples (`SameAtomicType.map_equiv` in
-- `Scott/AtomicDiagram`, `BFEquiv.map_equiv` in `Scott/BFEquivRelabel`, same statements as before
-- their move).  The off-diagonal of an analytic set in a Hausdorff space is analytic, and a set of
-- codes with countably many `CodeBFEquiv η`-classes at every level `η < ω₁` carries no Cantor
-- antichain for isomorphism, for every relational language: the two steps of the thinness above
-- before a complete metric is chosen.  A sentence `σ` of rank at most `β` that characterizes a
-- countable `M` among the countable structures in its carrier universe gives `StabilizesAt M β`
-- and `stabilizationOrdinal M ≤ β`: the sentence form of the recognition above.
set_option linter.hashCommand false in
#check FirstOrder.Language.SameAtomicType.map_equiv
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv.map_equiv
set_option linter.hashCommand false in
#check MeasureTheory.AnalyticSet.offDiag
set_option linter.hashCommand false in
#check FirstOrder.Language.not_hasCantorAntichainOn_of_bfScattered
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizesAt_of_sentence_rank
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizationOrdinal_le_of_sentence_rank

-- Thinness from countable back-and-forth observations (InfinitaryLogic, `Descriptive/BFScattered`),
-- available at the pin `eb9f12d` (signatures checked; no application compiled in this
-- repository).  If for every `η < ω₁` a map on a set `C` of codes has countable range and any two
-- codes with the same observation are `CodeBFEquiv η`, then `C` is back-and-forth scattered,
-- carries no Cantor antichain for isomorphism (every relational language), and, for countably
-- many relation symbols, is thin: the observation form of the thinness above.
set_option linter.hashCommand false in
#check FirstOrder.Language.bfScattered_of_countable_bfObservations
set_option linter.hashCommand false in
#check FirstOrder.Language.not_hasCantorAntichainOn_of_countable_bfObservations
set_option linter.hashCommand false in
#check FirstOrder.Language.isThinOn_of_countable_bfObservations

-- Tuple quantifier blocks, eliminating orbit parameters, and the rank of Montalbán's sentences
-- (InfinitaryLogic, `Lomega1omega/QuantifierRank`, `Scott/MontalbanSentence`,
-- `Scott/MontalbanQuantifierRank`, `Scott/OrbitParameters`), available at the pin `eb9f12d`
-- (signatures checked).  Closing the last `n` of `k + n` free variables (`existsTupleFrom k n`),
-- or all `n` of them (`existsTuple n`), adds exactly `n` to the rank, on the right; the
-- existential closure `existsLastVars m` of `VaughtConjecture.Definability.Syntax` agrees with
-- `existsTupleFrom k m`, and its semantics and rank lemmas are these, read through that agreement
-- (compiled in `VaughtConjecture.Definability.BlockFormulasExamples`).  Renaming free variables
-- keeps the rank, and `⊓` and `⊔` take the larger rank: the lemmas `Definability/Syntax` uses.
-- From an orbit formula `θ` of a parameter tuple and a formula `ψ` defining the orbit of a tuple
-- over those parameters, `∃ z̄ (θ(z̄) ∧ ψ(z̄, x̄))` defines its orbit, of rank
-- `max θ.qrank ψ.qrank + k`.  Montalbán's sentence of a family of rank at most `α` has rank at
-- most `α + ω`.  No application of the last two is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.existsTupleFrom
set_option linter.hashCommand false in
#check FirstOrder.Language.realize_existsTupleFrom
set_option linter.hashCommand false in
#check FirstOrder.Language.qrank_existsTupleFrom
set_option linter.hashCommand false in
#check FirstOrder.Language.qrank_existsTuple
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank_mapFreeVars
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank_inf
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank_sup
set_option linter.hashCommand false in
#check FirstOrder.Language.existsOrbitParams
set_option linter.hashCommand false in
#check FirstOrder.Language.realize_existsOrbitParams_iff_orbit
set_option linter.hashCommand false in
#check FirstOrder.Language.qrank_existsOrbitParams
set_option linter.hashCommand false in
#check FirstOrder.Language.qrank_montalbanSentence_le

-- Cross-rank comparisons (InfinitaryLogic, `Scott/InternalRankBounds`), available at the pin
-- `eb9f12d` (signatures checked; no application compiled in this repository).  For a countable
-- structure over a relational language with countably many relation symbols, the lifts of the
-- stabilization ordinal and of the Scott height are at most `internalScottRank M + ω`, attained on
-- the infinite pure set; under `+ ω` the internal Scott rank and the supremum of the orbit ranks
-- agree, for any structure.
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank_add_omega0_eq
set_option linter.hashCommand false in
#check FirstOrder.Language.lift_stabilizationOrdinal_le_internalScottRank_add_omega0
set_option linter.hashCommand false in
#check FirstOrder.Language.lift_scottHeight_le_internalScottRank_add_omega0

-- Uniform fixation for stage projections (InfinitaryLogic, `UniformFixation`), available at the
-- pin `eb9f12d` (signatures checked; no application compiled in this repository).  A stage
-- projection on a label type `I` has `project α` at every `α : Ordinal.{0}` with
-- `project α (project β i) = project (min α β) i`.  Over a countable type of coordinates, stage
-- correctness of the admissible presentations at countable stages and eventual invariance of
-- every coordinate (with an admissible witness at the threshold) give one countable stage fixing
-- every admissible presentation at every countable stage; `labelRank` is the least stage fixing a
-- label, not a Scott rank.  It is the bound for one arity in `README.md`, "Manuscript
-- correspondence (required)", item 5, where its application is prospective.
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection.FixedAt
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection.EventuallyInvariant
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection.labelRank
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection.exists_uniform_fixing_stage
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection.exists_uniform_fixing_stage_of_eventually_const
set_option linter.hashCommand false in
#check InfinitaryLogic.StageProjection.exists_classwise_labelRank_bound

-- A countable isolating level (InfinitaryLogic, `Scott/IsolatingLevel`), available at the pin
-- `eb9f12d` (signatures checked; no application compiled in this repository).  Over a countable
-- relational language, a countable family of countable structures has a level `γ < ω₁` at which
-- empty-tuple `BFEquiv0` between members gives an isomorphism; hence a family with two
-- `BFEquiv0`-related nonisomorphic members at every countable level has an uncountable index: the
-- isolating-level lower bound in back-and-forth form (`IMPLEMENTATION.md`, "The full-presentation
-- route").
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isolating_level
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_isolating_level_iff
set_option linter.hashCommand false in
#check FirstOrder.Language.not_countable_of_forall_unisolated

-- Concentration at back-and-forth levels (InfinitaryLogic, `Descriptive/BFConcentration`),
-- available at the pin `eb9f12d` (signatures checked; no application compiled in this
-- repository).  A class of codes is concentrated when at every level `α < ω₁` all but countably
-- many of its isomorphism classes lie in one `CodeBFEquiv α`-class; a concentrated class is
-- back-and-forth scattered, and thin for countably many relation symbols; for those, and an
-- analytic concentrated class, a relatively Borel split closed under isomorphism within the class
-- has a side meeting countably many isomorphism classes.
set_option linter.hashCommand false in
#check FirstOrder.Language.ConcentratedAtBFLevels
set_option linter.hashCommand false in
#check FirstOrder.Language.ConcentratedAtBFLevels.bfScattered
set_option linter.hashCommand false in
#check FirstOrder.Language.ConcentratedAtBFLevels.isThinOn
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_bfLevel_saturated
set_option linter.hashCommand false in
#check FirstOrder.Language.ConcentratedAtBFLevels.countable_isoClasses_or

-- The greatest attained stage (InfinitaryLogic, `OrdinalUtil`, Mathlib imports only), available
-- at the pin `eb9f12d` (signatures checked; no application compiled in this repository).  A
-- predicate on stages that holds at `0`, is closed downward and under successor limits below
-- `ω₁`, and is bounded on the countable stages by a countable `A` has a greatest stage `ρ ≤ A`,
-- and holds exactly at the stages `ξ ≤ ρ`; the two general forms are on `Ordinal.{u}`, with no
-- countability.  Its intended application is bounded-stage attainment (`IMPLEMENTATION.md`,
-- "Dependency pins"; prospective).
set_option linter.hashCommand false in
#check InfinitaryLogic.exists_greatest_stage_lt_omega1
set_option linter.hashCommand false in
#check InfinitaryLogic.exists_forall_iff_le_of_bounded_of_isSuccLimit_closed
set_option linter.hashCommand false in
#check InfinitaryLogic.exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed

-- Scott separation (InfinitaryLogic, `OrdinalCountability`, `Lomega1omega/QuantifierRank` and
-- `Descriptive/ScottDefinability`), available at the pin `eb9f12d` (signatures checked; no
-- application compiled in this repository).  An observation isolating a point excludes it from
-- every set of two or more points on which the observation is constant; along decreasing domains
-- on which the observations of rank at most the stage agree, a point isolated at countable rank
-- leaves the domains strictly before a countable stage when every domain at a countable stage has
-- two or more points.  Every formula of `Lω₁ω` has countable quantifier rank, so an isolated
-- presentation satisfies the isolation hypothesis.  The bound is the rank of a chosen isolating
-- sentence, not a Scott rank and not an attained stage.  The countable supremum of successors
-- (`iSup_add_one_lt_omega1`) is the step from bounds for countably many classes to one bound.
set_option linter.hashCommand false in
#check InfinitaryLogic.notMem_of_isolating_of_uniform
set_option linter.hashCommand false in
#check InfinitaryLogic.lt_index_of_isolating_of_antitone
set_option linter.hashCommand false in
#check InfinitaryLogic.lt_rank_of_isolating_of_antitone
set_option linter.hashCommand false in
#check InfinitaryLogic.stage_lt_rank_of_isolating
set_option linter.hashCommand false in
#check InfinitaryLogic.exists_countable_strict_stage_bound_of_isolation
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormulaω.qrank_lt_omega1
set_option linter.hashCommand false in
#check FirstOrder.Language.Sentenceω.qrank_lt_omega1
set_option linter.hashCommand false in
#check FirstOrder.Language.IsolatedPresentation.exists_qrank_lt_omega1
set_option linter.hashCommand false in
#check FirstOrder.Language.IsolatedPresentation.exists_countable_strict_stage_bound
set_option linter.hashCommand false in
#check InfinitaryLogic.iSup_add_one_lt_omega1

/- Proposed substantive targets (not declared as axioms or claimed proved here):

FiniteSemantics: construct the concrete ChartSystem and prove countability of charts,
  legal face restriction, stage reduction, lawful lifting at every cap self-visible at the
  target grade (bountifulness, one cap at a time; not the permitted cutoffs of receiving).
Receiving: exact literal root + one actual occurrence + requested capped/LOW equations on it
  (LOW and `Correct`: defined in Layer 3 of README.md, item 3.3).
HullOperations: definable total binary hull operations; generated-substructure closure equals
  hull closure; finite charts are the finite substructures; embeddings preserved and reflected.
ClassicalLimit: finite top-free charts as finite structures; hereditary closure, joint embedding,
  amalgamation with the literal square (before any infinite model); classical existence
  (available at the pin); reconstruction of partial evaluation (finite-age reconstruction,
  SEMANTIC_CONTRACT.md, item 11); consistency, covering, top-freeness from the factorization of
  tuples; receiving from (R5) and ultrahomogeneity (per cutoff for donors with top); modelhood,
  infinitude, terminality.  Statement shapes: `Suggested.lean`, section 3.
ChainConstruction (not used by the main theorem): finite master + root absorption +
  supported-invisible permanence + union; retained for an effective presentation, conditional on
  effective input data.  The saturated model of [Kni26, Proposition 4.4.5] is the classical
  limit of the uncapped age of all legal stage types.
StableLift: consistency-only uniqueness; consistency/covering lawfulness; cap modelhood.
Comparison: finite-donor one-sided transfer; rooted BF; singleton terminal conditions.
Domains: expansion uniqueness + limit existence; terminal losses countable and nonempty.
Counting: from `SentenceAgreementDomains`, `|Q| ≤ ℵ₁` (the persistent core is a subsingleton
  and the remaining classes lie in `ℵ₁ · ℵ₀` many exceptions); a target, not proved here.
MainTheorem: countable-loss induction + the sentence-agreement domains above + Scott/DST library.

Every data definition also needs extensionality, identity/composition, projection and
transport APIs. Use directional simp rules for these; never a transitivity instance for
the nontransitive transformation relation. See SEMANTIC_CONTRACT.md for the semantic boundaries.
-/

end Roadmap

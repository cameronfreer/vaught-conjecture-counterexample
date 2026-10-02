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

-- InfinitaryLogic at our pinned dependency `def5cc0` (signatures checked): the orbit-formula
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
-- `def5cc0`), through its two modules.
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
-- existence theorem of our pinned ComputableModelTheory (`0e9935b`) are checked below.
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

-- InfinitaryLogic at our pinned dependency `def5cc0` (signatures checked): uniform
-- back-and-forth separation of analytic sets of nonisomorphic pairs of codes
-- (`Descriptive/BFSeparation`); its compiled application is `isThinOn_of_countable_bfClasses`
-- (`VaughtConjecture.MainTheorem.Scatteredness`; `README.md`, Layer 6).
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_uniform_bfSeparation
set_option linter.hashCommand false in
#check FirstOrder.Language.CodeBFEquiv.monotone
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_uniform_bfSeparation_forall_ge
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_uniform_bfSeparation_of_analyticSets

-- InfinitaryLogic at our pinned dependency `def5cc0` (signatures checked): the forward Karp
-- lemma, agreement on formulas of quantifier rank at most `α` from `BFEquiv α`, for a relational
-- language.  Its application to the expansion domains (condition 3 of `README.md`) is a
-- statement still to be proved; no application of it is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv_implies_agreeQR

-- The ordinal-indexed hierarchy (`Lomega1omega/InHierarchy`), at our pinned dependency `def5cc0`
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
-- (InfinitaryLogic, `Scott/MontalbanSentence` and `Scott/MontalbanComplexity`), at our pinned
-- dependency `def5cc0` (signatures checked).  For a countable `M` in
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

-- Graded matching (InfinitaryLogic, `Scott/GradedMatching`), available at the pin `def5cc0`
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
-- at the pin `def5cc0` (signatures checked).  For `r : X → Ordinal` below `ω₁` with countable
-- fibres, a set is countable iff its ranks are bounded below `ω₁` (`countable_iff_rank_bounded`),
-- the tails `rankTail r η = {x | η ≤ r x}` have empty intersection below `ω₁`, have nonempty
-- losses cofinally below `ω₁` iff `X` is uncountable, and give `#X ≤ ℵ₁`, with `#X = ℵ₁` for an
-- uncountable `X`.  Domains with countable complements below `ω₁` that every point leaves give
-- `#X ≤ ℵ₁` (`mk_le_aleph_one_of_domains`).  Under the covering hypothesis
-- `hcover : ⋃ α < ω₁, Q α = univ`, the tails of `leastLevel Q` are the complements of the initial
-- unions of `Q`, and countable sets `Q α` give `leastLevel Q` countable fibres.  The statements of
-- `Counting/Filtration` are candidates for one-line quotation of these (`IMPLEMENTATION.md`,
-- "Placement record"); no application is compiled here.
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
-- countable structure, at the pin `def5cc0` (signatures checked), with the Scott formula's rank
-- bound and characterization: the notions of the prospective one-sided rank comparison
-- (`COMPANIONS.md`, "Further companion results").  `stabilizationOrdinal M` is the least level at
-- which empty-tuple back-and-forth equivalence with `M` characterizes `M` among the countable
-- structures in its carrier universe (`StabilizesAt`); `scottHeight M` the least level from which
-- back-and-forth equivalence of tuples of every length no longer refines.  Neither is
-- `internalScottRank`: an infinite pure set has internal Scott rank `1`
-- (`internalScottRank_pureSet`).  No application is compiled here.
set_option linter.hashCommand false in
#check FirstOrder.Language.StabilizesAt
set_option linter.hashCommand false in
#check FirstOrder.Language.stabilizationOrdinal
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
-- the pin `def5cc0` (signatures checked).  The existential closure `existsTuple k φ` of a formula
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

-- ComputableModelTheory at our pinned dependency `0e9935b` (signatures checked), through the
-- entry module `ComputableModelTheory.Classical` (Mathlib-only imports): classical Fraïssé
-- existence (`ModelTheory/FraisseExistence`), rooted universality and uniqueness
-- (`ModelTheory/RootedExtension`), and isolation and primeness over named finite parameters
-- (`ModelTheory/NamedParameters`); representative classes, extension-rich families and direct
-- limits, the factorization of tuples through the age (`ModelTheory/RepresentativeAge`,
-- `ExtensionRichFamily`, `ExtensionRichDirectLimit`), orbit isolation and countable prime
-- structures (`ModelTheory/OrbitIsolation`, `CountablePrime`).  No application of these is
-- compiled in this repository.
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

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

-- InfinitaryLogic at our pinned dependency `cca6949` (signatures checked): the orbit-formula
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

-- The rank comparison of the Scott process (InfinitaryLogic's pull request #140, contained in
-- `cca6949`), through its two modules.
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

-- Mathlib's Fraïssé interface, applied by the classical limit of the top-free witnesses
-- (`README.md`, Layer 0).  The classical existence theorem, representative classes, the
-- factorization of tuples through the age, orbit isolation, and countable prime structures (all
-- in ComputableModelTheory) are prospective: neither available upstream nor pinned, and not
-- checked.
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
  (prospective); reconstruction meeting SEMANTIC_CONTRACT.md, item 11; consistency, covering,
  top-freeness from the factorization of tuples; receiving from row 5 and ultrahomogeneity
  (per cutoff for donors with top); modelhood, infinitude, terminality.  Statement shapes:
  `Suggested.lean`, section 3.
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

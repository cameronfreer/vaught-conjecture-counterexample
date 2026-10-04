/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Types
import Mathlib.ModelTheory.ElementaryMaps
import InfinitaryLogic.Descriptive.ScottDefinability
import InfinitaryLogic.Descriptive.CodeTransport
import InfinitaryLogic.Descriptive.ObservableConstancy
import InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import InfinitaryLogic.Scott.OrbitRank
import InfinitaryLogic.Scott.RefinementCount
import InfinitaryLogic.Scott.OrbitFormulaThreshold
import InfinitaryLogic.Lomega1omega.LocalAutomorphism

/-!
# Selected statements for the companion milestones

`COMPANIONS.md` is authoritative; this file is a nonexhaustive sketch of statements that lie
OUTSIDE the library build and outside the core theorem.  The declarations whose bodies are `sorry`
are deliberate targets: statements still to be proved.  The other declarations are proved here, or
are definitions of properties (never structures whose fields assert the desired conclusions).  No
statement here is a construction of the concrete charts, realizations, or models; the
construction-specific instances of these statements are listed in `COMPANIONS.md`.  Check the
file with

  lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true \
    roadmap/SuggestedCompanions.lean

The three sections correspond to the three milestones: (A) the filtration and the theory `T∞`, (B)
homogeneity of the top-free charts and the orbit theory, (C) the geometric obstruction.  The generic
theorems of B are quoted from the two libraries: from InfinitaryLogic, at the pin `e460cb6`
(signatures checked), as the proved applications at the end of section B; from
ComputableModelTheory, at the pin `a1fe761` (signatures checked, `#check`ed in
`SuggestedInterfaces.lean`), whose `sorry` targets below record their statement shapes
(`IMPLEMENTATION.md`, "Dependency pins").
-/

set_option autoImplicit false
noncomputable section

namespace Roadmap.Companions

universe u v w w' z

open FirstOrder Language

/-! ## A. Filtration and infinitary theory -/

namespace Filtration

/-- The sentences true in all but countably many classes (the theory `T∞` of `COMPANIONS.md`).
Here `truth θ q` is satisfaction of `θ` read through a presentation of the classes. -/
def cocountableTheory {Sent : Type u} {Q : Type v} (truth : Sent → Q → Prop) : Set Sent :=
  {θ | ({q | ¬ truth θ q} : Set Q).Countable}

/-- **Losses have high rank.**  If the domains `D' ⊆ D` are both relevant (a nonempty loss
`D \ D'` and a nonempty `D'`) and the classes of `D` agree on sentences of rank at most `η`, then
a sentence defining the loss has rank strictly above `η`.  No upper bound on the rank of such a
sentence, and no effective choice of it, is asserted. -/
theorem lt_qrank_of_defines_loss {Sent : Type u} {Q : Type v} (truth : Sent → Q → Prop)
    (qrank : Sent → Ordinal.{z}) {D D' : Set Q} {η : Ordinal.{z}} (hsub : D' ⊆ D)
    (hagree : ∀ θ, qrank θ ≤ η → ∀ p ∈ D, ∀ q ∈ D, (truth θ p ↔ truth θ q))
    {ψ : Sent} (hψ : ∀ q, truth ψ q ↔ q ∈ D \ D') (hloss : (D \ D').Nonempty)
    (hne : D'.Nonempty) : η < qrank ψ := by
  by_contra h
  obtain ⟨p, hp⟩ := hloss
  obtain ⟨q, hq⟩ := hne
  have hpq := hagree ψ (not_lt.mp h) p hp.1 q (hsub hq)
  exact ((hψ q).mp (hpq.mp ((hψ p).mpr hp))).2 hq

/-- **Sentencewise convergence on a cocountable domain.**  If a sentence has constant truth value
on a domain with countable complement in an uncountable set of classes, then its value at any
class of the domain is membership in `T∞`.  Applied with `D = D_η` for `η` at least the rank of
the sentence, and with a top-free witness class in `D_η`, this is the witness
convergence of `COMPANIONS.md`: truth converges sentence by sentence, with the rank as threshold.
Nothing is asserted about convergence of codes or of embeddings. -/
theorem truth_iff_mem_cocountableTheory {Sent : Type u} {Q : Type v} (truth : Sent → Q → Prop)
    (huncount : ¬ (Set.univ : Set Q).Countable) {D : Set Q} (hcompl : Dᶜ.Countable) {θ : Sent}
    (hagree : ∀ p ∈ D, ∀ q ∈ D, (truth θ p ↔ truth θ q)) {w : Q} (hw : w ∈ D) :
    truth θ w ↔ θ ∈ cocountableTheory truth := by
  constructor
  · intro ht
    exact hcompl.mono fun q hq hqD => hq ((hagree w hw q hqD).mp ht)
  · intro hc
    by_contra hf
    have hD : D.Countable := hc.mono fun q hqD => fun ht => hf ((hagree w hw q hqD).mpr ht)
    exact huncount (by simpa using hD.union hcompl)

/-- The witness form of the previous lemma: for a family `w` of classes with `w η ∈ D η`, and
domains of countable complement on which sentences of rank at most `η` are constant, the truth of
`θ` at `w η` is membership in `T∞` for every countable `η` at least the rank of `θ`. -/
theorem witness_truth_iff_mem_cocountableTheory {Sent : Type u} {Q : Type v}
    (truth : Sent → Q → Prop) (qrank : Sent → Ordinal.{0})
    (huncount : ¬ (Set.univ : Set Q).Countable) (D : Ordinal.{0} → Set Q)
    (hcompl : ∀ η < Ordinal.omega 1, (D η)ᶜ.Countable)
    (hagree : ∀ η < Ordinal.omega 1, ∀ θ, qrank θ ≤ η →
      ∀ p ∈ D η, ∀ q ∈ D η, (truth θ p ↔ truth θ q))
    (w : Ordinal.{0} → Q) (hw : ∀ η < Ordinal.omega 1, w η ∈ D η)
    {θ : Sent} {η : Ordinal.{0}} (hθη : qrank θ ≤ η) (hη : η < Ordinal.omega 1) :
    truth θ (w η) ↔ θ ∈ cocountableTheory truth :=
  truth_iff_mem_cocountableTheory truth huncount (hcompl η hη) (hagree η hη θ hθη) (hw η hη)

/-- **Exclusivity in the dichotomy.**  A structure satisfying every sentence of `T∞` satisfies no
sentence that isolates a single class: the negation of an isolating sentence lies in `T∞`.  The
Scott sentence of a representative isolates its class
(`isolatedPresentation_of_surjective`), so this is the "at most one" half of the Scott/`T∞`
dichotomy, on an arbitrary carrier. -/
theorem not_realize_isolating_of_cocountableTheory {L : Language.{u, v}} {Q : Type z}
    (truth : L.Sentenceω → Q → Prop)
    (hnot : ∀ φ q, truth φ.not q ↔ ¬ truth φ q) {θ : L.Sentenceω} {q₀ : Q}
    (hθ : ∀ q, truth θ q ↔ q = q₀) {N : Type w'} [L.Structure N]
    (hN : ∀ ψ ∈ cocountableTheory truth, Sentenceω.Realize ψ N) :
    ¬ Sentenceω.Realize θ N := by
  have hmem : θ.not ∈ cocountableTheory truth :=
    (Set.countable_singleton q₀).mono fun q hq => by
      simpa [hnot, hθ] using hq
  have h := hN _ hmem
  rw [Sentenceω.realize_def] at h ⊢
  exact (BoundedFormulaω.realize_not _).mp h

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
variable {X : Type w} {Q : Type z}

/-- **Definable domains.**  On a presentation of the classes by codes, a set of classes with
countable complement (for instance a countable-stage domain `D_η`) is defined by a sentence.  The
sentence is obtained noneffectively, as the negation of a countable disjunction of Scott
sentences; nothing is asserted about its rank.  For losses, which are countable, quote
`exists_sentence_of_countable_of_presentation` directly. -/
theorem exists_sentence_defining_of_compl_countable (codes : X → StructureSpace L)
    (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    {D : Set Q} (hD : Dᶜ.Countable) : ∃ ψ : L.Sentenceω, ∀ q, truth ψ q ↔ q ∈ D := by
  obtain ⟨φ, hφ⟩ :=
    exists_sentence_of_countable_of_presentation codes classOf honto hiso truth htruth hD
  refine ⟨φ.not, fun q => ?_⟩
  rw [truth_not_of_presentation codes classOf honto truth htruth, hφ]
  exact not_not

/-- The Scott sentence of the structure on `ℕ` decoded from a code. -/
def scottSentenceOfCode (c : StructureSpace L) : L.Sentenceω :=
  (@scottSentence L _ ℕ c.toStructure _).toSentenceω

/-- **The Scott/`T∞` dichotomy** (target).  Let the codes present every model of `φ` on `ℕ` up to
isomorphism, let `φ` have no finite models in the universe of `N`, and let `N` be a model of `φ`
on an ARBITRARY carrier.  Then exactly one holds: `N` satisfies the Scott sentence of some
countable model of `φ`, or `N` satisfies every sentence of `T∞`.

Intended proof: exclusivity is `not_realize_isolating_of_cocountableTheory`.  For coverage, if
`N` fails some `ψ ∈ T∞`, the classes failing `ψ` are countably many; take the countable fragment
generated by `φ`, `ψ`, and their Scott sentences, a countable fragment-elementary substructure
`N₀` of `N` (`exists_countable_aElementary_substructure`), code `N₀` on `ℕ`
(`StructureSpaceOn.encodeViaEquiv`), and read off one of the countably many Scott sentences.  The
Scott case gives agreement of `N` with that countable model on every sentence, not an
isomorphism. -/
theorem scott_xor_cocountableTheory (codes : X → StructureSpace L) (classOf : X → Q)
    (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (φ : L.Sentenceω) (hcodes : ∀ x, codes x ∈ ModelsOf φ)
    (hall : ∀ c ∈ ModelsOf φ, ∃ x, (structureIsoSetoid L).r c (codes x))
    {N : Type w'} [L.Structure N]
    (hfin : ∀ (F : Type w') [L.Structure F] [Finite F], ¬ Sentenceω.Realize φ F)
    (hN : Sentenceω.Realize φ N) :
    Xor (∃ x, Sentenceω.Realize (scottSentenceOfCode (codes x)) N)
      (∀ ψ ∈ cocountableTheory truth, Sentenceω.Realize ψ N) := by
  sorry

end Filtration

/-! ## B. Homogeneity of top-free charts and its consequences -/

/- The chart amalgamation and joint embedding properties (B1) belong to the core, step 2 of the
top-free witnesses: `ChartAmalgamation`, `ChartJointEmbedding`, and
`chartJointEmbedding_of_chartAmalgamation` are in `Suggested.lean` (`Roadmap.ClassicalLimit`),
with the finite-age reconstruction predicate. -/

namespace Orbits

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/- The generic consequences of the two interfaces of B are library theorems of InfinitaryLogic,
available at the pin `e460cb6` (signatures checked), and are not reproved here: the
applications at the end of this section quote them.  The construction-side statements are the
orbit formula of a chart (`orbitDefinedBy_chartOrbitFormula`) and the local agreement property
(`agreesLocally_of_hom`).  The narrow modules `Scott/OrbitFormulaThreshold` and
`Lomega1omega/LocalAutomorphism` are imported, never `InfinitaryLogic.All`. -/

/-- The first-order formula `φ` defines the automorphism orbit of `a`. -/
def OrbitDefinedBy {n : ℕ} (a : Fin n → M) (φ : L.Formula (Fin n)) : Prop :=
  ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b

section ChartOrbitFormula

open Structure

variable {Chart : ℕ → Type z} (rel : ∀ {n : ℕ}, Chart n → L.Relations n)

/-- **Literal recovery of chart relations**, with injectivity of labelled tuples (as in
`Suggested.lean`, section 3): the relation of the chart `p` holds at a tuple exactly when the
tuple is injective and its evaluation is `p`. -/
def RecoversRelations (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M) (p : Chart n),
    RelMap (rel p) a ↔ ∃ t : Fin n ↪ M, ⇑t = a ∧ eval t = some p

/-- The **orbit formula of a chart**: `θ(x̄) := ∃ z̄, P_p(z̄) ∧ ⋀_i x_i = z_{b(i)}`, for a chart
`p` on `m` points and the positions `b` of the tuple among its points (repetitions allowed).  It
uses only a chart relation and equality, so it is a formula of the relational stage chart
language. -/
noncomputable def chartOrbitFormula {n m : ℕ} (p : Chart m) (b : Fin n → Fin m) :
    L.Formula (Fin n) :=
  BoundedFormula.exs
    ((rel p).boundedFormula (fun j => Term.var (Sum.inr j)) ⊓
      BoundedFormula.iInf fun i : Fin n =>
        (Term.var (Sum.inl i)).bdEqual (Term.var (Sum.inr (b i))))

/-- **Orbit formulas from finite charts** (B3.1).  Under literal recovery of the chart relations
and chart homogeneity (two actual occurrences of the same chart are carried to each other by an
automorphism), the orbit formula of an actual chart containing the tuple `a` defines its
automorphism orbit.  The empty tuple and repeated coordinates are included.  For a top-free
witness, chart homogeneity follows from ultrahomogeneity of the expansion by the hull
operations, since every automorphism of the expansion is an automorphism of its relational
reduct; only this direction is used (`README.md`, Layer 0). -/
theorem orbitDefinedBy_chartOrbitFormula {eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)}
    (hrec : RecoversRelations rel eval)
    (hhom : ∀ {m : ℕ} (u v : Fin m ↪ M) (p : Chart m), eval u = some p → eval v = some p →
      ∃ e : M ≃[L] M, ⇑e ∘ ⇑u = ⇑v)
    {n m : ℕ} (a : Fin n → M) (u : Fin m ↪ M) (b : Fin n → Fin m) (p : Chart m)
    (hu : ⇑u ∘ b = a) (hp : eval u = some p) :
    OrbitDefinedBy a (chartOrbitFormula rel p b) := by
  have hpu : RelMap (rel p) ⇑u := (hrec u p).2 ⟨u, rfl, hp⟩
  simp only [OrbitDefinedBy, chartOrbitFormula, BoundedFormula.realize_exs,
    BoundedFormula.realize_inf, BoundedFormula.realize_rel, BoundedFormula.realize_iInf,
    BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  intro c
  constructor
  · rintro ⟨z, hz, hc⟩
    obtain ⟨v, hv, hvp⟩ := (hrec _ p).1 hz
    obtain ⟨e, he⟩ := hhom u v p hp hvp
    refine ⟨e, funext fun i => ?_⟩
    have := congrFun he (b i)
    simp only [Function.comp_apply] at this ⊢
    rw [← hu]; simp only [Function.comp_apply]; rw [this, hv]
    exact (hc i).symm
  · rintro ⟨e, rfl⟩
    refine ⟨⇑e ∘ ⇑u, ?_, fun i => ?_⟩
    · exact (e.map_rel (rel p) ⇑u).2 hpu
    · rw [← hu]; rfl

/-- **Covering** of arbitrary tuples (as in `Suggested.lean`, section 3): every tuple, the empty
tuple and repeated coordinates included, factors literally through an actual occurrence. -/
def CoversTuples (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M), ∃ (m : ℕ) (u : Fin m ↪ M) (b : Fin n → Fin m) (p : Chart m),
    ⇑u ∘ b = a ∧ eval u = some p

/-- The **local agreement property** of a self-map `f`: on each finite tuple it agrees with an
automorphism.  For `f` a self-embedding this is the hypothesis of InfinitaryLogic's
`BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms` (at the pin `e460cb6`). -/
def AgreesLocally (f : M → M) : Prop :=
  ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a

/-- **Local agreement from recovery, covering, and homogeneity** (B2).  Cover `a` by an actual
chart `u`; a map preserving the chart relations carries `u` to a tuple satisfying the same chart
relation, which by literal recovery is an actual occurrence of the same chart; homogeneity gives
an automorphism agreeing with the map on `u`, hence on `a`.  Only the preservation of the chart
relations is used: any homomorphism, in particular any self-embedding. -/
theorem agreesLocally_of_hom {eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)}
    (hrec : RecoversRelations rel eval) (hcov : CoversTuples eval)
    (hhom : ∀ {m : ℕ} (u v : Fin m ↪ M) (p : Chart m), eval u = some p → eval v = some p →
      ∃ e : M ≃[L] M, ⇑e ∘ ⇑u = ⇑v)
    (g : M →[L] M) : AgreesLocally (L := L) ⇑g := by
  intro n a
  obtain ⟨m, u, b, p, hu, hp⟩ := hcov a
  have hrel : RelMap (rel p) (⇑g ∘ ⇑u) := g.map_rel (rel p) ⇑u ((hrec u p).2 ⟨u, rfl, hp⟩)
  obtain ⟨v, hv, hvp⟩ := (hrec _ p).1 hrel
  obtain ⟨e, he⟩ := hhom u v p hp hvp
  refine ⟨e, ?_⟩
  rw [← hu, ← Function.comp_assoc, he, hv, Function.comp_assoc]

end ChartOrbitFormula

/-! ### The applications (InfinitaryLogic, at the pin `e460cb6`)

Each statement is a one-line application of a library theorem to the two interfaces; the
hypotheses `OrbitDefinedBy a φ` and `AgreesLocally ⇑g` are, by definition, the library's `hφ` and
`hg`. -/

/-- **A finite threshold from an orbit formula** (B3.3), by `exists_finite_orbit_threshold`. -/
theorem exists_finite_threshold_of_orbitDefinedBy [L.IsRelational] {n : ℕ} {a : Fin n → M}
    {φ : L.Formula (Fin n)} (h : OrbitDefinedBy a φ) :
    ∃ β : Ordinal.{w}, β < Ordinal.omega0 ∧
      ∀ b : Fin n → M, BFEquiv (L := L) β n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b :=
  exists_finite_orbit_threshold h

/-- **Finite orbit rank from an orbit formula** (B3.3), by
`orbitRank_lt_omega0_of_orbitFormula`. -/
theorem orbitRank_lt_omega0_of_orbitDefinedBy [L.IsRelational] {n : ℕ} {a : Fin n → M}
    {φ : L.Formula (Fin n)} (h : OrbitDefinedBy a φ) : orbitRank (L := L) a < Ordinal.omega0 :=
  orbitRank_lt_omega0_of_orbitFormula h

/-- **Internal Scott rank at most `ω`** from an orbit formula for every tuple (B3.3), by
`internalScottRank_le_omega0_of_orbitFormulas`.  The bound is `≤ ω`, not `< ω`, and not an
equality; the internal rank is in the library's convention `⨆ a, orbitRank a + 1`. -/
theorem internalScottRank_le_omega0_of_orbitDefinedBy [L.IsRelational]
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n), OrbitDefinedBy a φ) :
    internalScottRank (L := L) M ≤ Ordinal.omega0 :=
  internalScottRank_le_omega0_of_orbitFormulas h

/-- **Self-embeddings preserve infinitary formulas** (B2), in the orientation
`M ⊨ φ(a) ↔ M ⊨ φ(g ∘ a)`, by `BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms`.
No relationality, countability, infinitude, or nonemptiness. -/
theorem realize_iff_realize_comp_of_agreesLocally (g : M ↪[L] M) (hg : AgreesLocally (L := L) ⇑g)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (a : Fin n → M) :
    φ.Realize Empty.elim a ↔ φ.Realize Empty.elim (⇑g ∘ a) :=
  (BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms g hg φ a).symm

/-- **The same with finitely many parameters** (B2), by
`BoundedFormulaω.realize_comp_append_of_localAutomorphisms`: one automorphism, chosen for the
appended tuple, moves both. -/
theorem realize_comp_append_iff_of_agreesLocally (g : M ↪[L] M) (hg : AgreesLocally (L := L) ⇑g)
    {m n : ℕ} (φ : L.BoundedFormulaω (Fin m) n) (v : Fin m → M) (a : Fin n → M) :
    φ.Realize (⇑g ∘ v) (⇑g ∘ a) ↔ φ.Realize v a :=
  BoundedFormulaω.realize_comp_append_of_localAutomorphisms hg φ v a

variable [Nonempty M]

/-- **A definable orbit isolates the complete type** (target, generic).  If `φ` defines the
automorphism orbit of `a`, then `φ` isolates the complete type of `a` over the complete theory of
`M`: the only complete type containing `φ` is the type of `a`.  Uniqueness of realizations inside
`M` alone is not the statement; the singleton is in the space of complete types, so the universal
implications `∀ x̄, φ → ψ` transfer to every model of the theory.  At the pin; to be quoted as
the composite of ComputableModelTheory's
`isolatesTuple_of_orbit_formula` (under `[Nonempty M]`) and `IsolatesTuple.typesWith_eq_singleton`.
-/
theorem typesWith_eq_singleton_of_orbitDefinedBy {n : ℕ} {a : Fin n → M}
    {φ : L.Formula (Fin n)} (hφ : OrbitDefinedBy a φ) :
    (L.completeTheory M).typesWith (Formula.equivSentence φ) =
      {(L.completeTheory M).typeOf a} := by
  sorry

variable (L M) in
/-- Every finite tuple's complete type over the theory of `M` is isolated by a formula. -/
def TypesIsolated : Prop :=
  ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n),
    (L.completeTheory M).typesWith (Formula.equivSentence φ) = {(L.completeTheory M).typeOf a}

/-- Definable orbits give atomicity. -/
theorem typesIsolated_of_orbitDefinedBy
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n), OrbitDefinedBy a φ) :
    TypesIsolated L M := fun n a =>
  let ⟨φ, hφ⟩ := h n a
  ⟨φ, typesWith_eq_singleton_of_orbitDefinedBy hφ⟩

/-- **Countable atomic implies prime** (target, generic).  A countable structure all of whose types
are isolated embeds elementarily into every model of its complete theory, in an arbitrary universe
and of arbitrary cardinality.  Intended proof: enumerate only `M`, extend finite partial maps
preserving every first-order formula, and take the union.  At the pin: ComputableModelTheory's
`exists_elementaryEmbedding_of_countable_atomic`, with
`TypesIsolated` identified with its `IsAtomic` over the complete theory. -/
theorem nonempty_elementaryEmbedding_of_typesIsolated [Countable M]
    (hM : TypesIsolated L M) (N : Type w') [L.Structure N] [N ⊨ L.completeTheory M] :
    Nonempty (M ↪ₑ[L] N) := by
  sorry

end Orbits

/-! ## C. A geometric obstruction

The generic shape of the two-point bound: an extreme-point map `ext` on sets, commuting at the set
`A` with a set `Aut` of self-maps (for a realization, `ext A` is the set of the two extreme points
of the finite hull of `A`, and `Aut` its automorphisms, which preserve the two intrinsic extremes of
a finite hull).  If a set `A ⊆ S` contains a point that is not extreme and a point that is, then not
every permutation of `S` extends to a map in `Aut`.  Applied to three distinct points, whose hull
has its two extremes among them, it bounds every set of absolute indiscernibles by two. The instance
for a realization, from exact consistency and covering alone, is a statement still to be proved
(`COMPANIONS.md`, C). -/

namespace HullObstruction

variable {M : Type u} (ext : Set M → Set M) (Aut : Set (M → M))

/-- **The swap of a non-extreme and an extreme point.**  With `x` not extreme and `y` extreme in
`A ⊆ S`, the transposition of `x` and `y` does not extend to a map in `Aut` commuting with
`ext` at `A`: such a map sends `A` onto itself and `y` to `x`. -/
theorem false_of_swap_extreme {S A : Set M} (hAS : A ⊆ S)
    (hext : ∀ g ∈ Aut, g '' ext A = ext (g '' A))
    (hperm : ∀ σ : Equiv.Perm S, ∃ g ∈ Aut, ∀ s : S, g s = σ s)
    {x y : M} (hx : x ∈ A) (hy : y ∈ A) (hxe : x ∉ ext A) (hye : y ∈ ext A) : False := by
  classical
  obtain ⟨g, hg, hgσ⟩ := hperm (Equiv.swap ⟨x, hAS hx⟩ ⟨y, hAS hy⟩)
  have hgA : ∀ a ∈ A, g a = Equiv.swap x y a := by
    intro a ha
    have := hgσ ⟨a, hAS ha⟩
    rw [this]
    by_cases hax : a = x
    · subst hax; simp
    · by_cases hay : a = y
      · subst hay; simp
      · rw [Equiv.swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hax)
          (by simpa [Subtype.ext_iff] using hay), Equiv.swap_apply_of_ne_of_ne hax hay]
  have himg : g '' A = A := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [hgA b hb]
      by_cases hbx : b = x
      · subst hbx; simpa using hy
      · by_cases hby : b = y
        · subst hby; simpa using hx
        · rwa [Equiv.swap_apply_of_ne_of_ne hbx hby]
    · intro ha
      refine ⟨Equiv.swap x y a, ?_, ?_⟩
      · by_cases hax : a = x
        · subst hax; simpa using hy
        · by_cases hay : a = y
          · subst hay; simpa using hx
          · rwa [Equiv.swap_apply_of_ne_of_ne hax hay]
      · rw [hgA _ ?_, Equiv.swap_apply_self]
        by_cases hax : a = x
        · subst hax; simpa using hy
        · by_cases hay : a = y
          · subst hay; simpa using hx
          · rwa [Equiv.swap_apply_of_ne_of_ne hax hay]
  have hxmem : x ∈ ext A := by
    rw [← himg, ← hext g hg]
    refine ⟨y, hye, ?_⟩
    rw [hgA y hy, Equiv.swap_apply_right]
  exact hxe hxmem

end HullObstruction

end Roadmap.Companions

-- Pinned upstream ingredients used above or named in `COMPANIONS.md`: these `#check`s fail if a
-- pin bump removes one.
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_countable_aElementary_substructure
set_option linter.hashCommand false in
#check FirstOrder.Language.AElementary.realize_sentence_iff
set_option linter.hashCommand false in
#check FirstOrder.Language.Fragment.generatedTheory_countable
set_option linter.hashCommand false in
#check FirstOrder.Language.Fragment.mem_generatedTheory
set_option linter.hashCommand false in
#check FirstOrder.Language.StructureSpaceOn.encodeViaEquiv
set_option linter.hashCommand false in
#check FirstOrder.Language.LomegaEquiv.of_equiv
set_option linter.hashCommand false in
#check FirstOrder.Language.scottSentence_characterizes
set_option linter.hashCommand false in
#check FirstOrder.Language.isolatedPresentation_of_surjective
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_sentence_of_countable_of_presentation
set_option linter.hashCommand false in
#check FirstOrder.Language.sentence_definable_iff_of_presentation
set_option linter.hashCommand false in
#check FirstOrder.Language.truth_not_of_presentation
set_option linter.hashCommand false in
#check FirstOrder.Language.sentences_constant_off_countable
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.ofExtensionFamily
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.family_bfEquiv
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_automorphism_of_bfEquiv_all
set_option linter.hashCommand false in
#check FirstOrder.Language.realize_scottFormula_iff_BFEquiv
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.countable_toEquiv_graph
set_option linter.hashCommand false in
#check FirstOrder.Language.bfEquiv_orbitRank_iff_exists_automorphism
set_option linter.hashCommand false in
#check FirstOrder.Language.Theory.typeOf
set_option linter.hashCommand false in
#check FirstOrder.Language.Theory.typesWith
set_option linter.hashCommand false in
#check FirstOrder.Language.Formula.equivSentence
set_option linter.hashCommand false in
#check FirstOrder.Language.ElementaryEmbedding

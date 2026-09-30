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
import InfinitaryLogic.Scott.QuantifierRank
import InfinitaryLogic.Scott.RefinementCount

/-!
# Selected statements for the companion milestones

`COMPANIONS.md` is authoritative; this file is a nonexhaustive, human-owned sketch of targets
that lie OUTSIDE the library build and outside the core theorem.  The bodies marked `sorry` are
deliberate targets, still to be proved.  The other declarations are proved here, or are
definitions of properties (never structures whose fields assert the desired conclusions).  No
statement here is a construction of the concrete charts, realizations, or models; the
construction-specific instances of these statements are listed in `COMPANIONS.md`.  Check the
file with

  lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true \
    roadmap/SuggestedCompanions.lean

The three sections correspond to the three milestones: (A) the filtration and the theory `T∞`,
(B) homogeneity of the top-free charts and the orbit theory, (C) the geometric obstruction.
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

namespace Charts

variable (Chart : ℕ → Type u)
variable (restrict : {n m : ℕ} → (Fin n ↪ Fin m) → Chart m → Option (Chart n))

/-- **Amalgamation of charts**, with the literal commuting root equation `f₁.trans g₁ =
f₂.trans g₂`.  Two charts restricting to the same chart along `f₁` and `f₂` are both restrictions
of one chart.  This is not strong amalgamation (the images of `g₁` and `g₂` may overlap outside
the image of the root) and concerns the specified charts only, not arbitrary induced finite
substructures.  The target is to prove it for the top-free finite closed charts. -/
def ChartAmalgamation : Prop :=
  ∀ {k m₁ m₂ : ℕ} (f₁ : Fin k ↪ Fin m₁) (f₂ : Fin k ↪ Fin m₂) (p₁ : Chart m₁) (p₂ : Chart m₂)
    (r : Chart k), restrict f₁ p₁ = some r → restrict f₂ p₂ = some r →
    ∃ (m : ℕ) (g₁ : Fin m₁ ↪ Fin m) (g₂ : Fin m₂ ↪ Fin m) (p : Chart m),
      f₁.trans g₁ = f₂.trans g₂ ∧ restrict g₁ p = some p₁ ∧ restrict g₂ p = some p₂

/-- **Joint embedding of charts**: any two charts are restrictions of one chart. -/
def ChartJointEmbedding : Prop :=
  ∀ {m₁ m₂ : ℕ} (p₁ : Chart m₁) (p₂ : Chart m₂),
    ∃ (m : ℕ) (g₁ : Fin m₁ ↪ Fin m) (g₂ : Fin m₂ ↪ Fin m) (p : Chart m),
      restrict g₁ p = some p₁ ∧ restrict g₂ p = some p₂

variable {Chart restrict}

/-- Amalgamation over the empty chart gives joint embedding, when every chart restricts to one
empty chart.  The empty root is an instance of amalgamation, not a separate construction. -/
theorem chartJointEmbedding_of_chartAmalgamation (hAP : ChartAmalgamation Chart restrict)
    (e : Chart 0)
    (hempty : ∀ {m : ℕ} (p : Chart m), restrict Function.Embedding.ofIsEmpty p = some e) :
    ChartJointEmbedding Chart restrict := by
  intro m₁ m₂ p₁ p₂
  obtain ⟨m, g₁, g₂, p, -, h₁, h₂⟩ :=
    hAP Function.Embedding.ofIsEmpty Function.Embedding.ofIsEmpty p₁ p₂ e (hempty p₁) (hempty p₂)
  exact ⟨m, g₁, g₂, p, h₁, h₂⟩

end Charts

namespace Orbits

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- **Local automorphisms preserve infinitary formulas.**  A self-map of `M` that agrees with an
automorphism on the tuple `a` preserves every `L_{ω₁,ω}` formula at `a`.  Applied to a
self-embedding agreeing with an automorphism on each finite tuple, it gives preservation of all
infinitary formulas.  No proper self-embedding is constructed here. -/
theorem realize_comp_iff_of_agrees_with_automorphism (f : M → M) {n : ℕ} (a : Fin n → M)
    (hf : ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a) (φ : L.Formulaω (Fin n)) :
    Formulaω.Realize φ (f ∘ a) ↔ Formulaω.Realize φ a := by
  obtain ⟨e, he⟩ := hf
  rw [← he, Formulaω.realize_def, Formulaω.realize_def,
    BoundedFormulaω.realize_equiv e φ a Fin.elim0]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- The first-order formula `φ` defines the automorphism orbit of `a`. -/
def OrbitDefinedBy {n : ℕ} (a : Fin n → M) (φ : L.Formula (Fin n)) : Prop :=
  ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b

variable [Nonempty M]

/-- **A definable orbit isolates the complete type** (target, generic).  If `φ` defines the
automorphism orbit of `a`, then `φ` isolates the complete type of `a` over the complete theory
of `M`: the only complete type containing `φ` is the type of `a`.  Uniqueness of realizations
inside `M` alone is not the statement; the singleton is in the space of complete types, so the
universal implications `∀ x̄, φ → ψ` transfer to every model of the theory. -/
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

/-- **Countable atomic implies prime** (target, generic).  A countable structure all of whose
types are isolated embeds elementarily into every model of its complete theory, in an independent
universe and of arbitrary cardinality.  Intended proof: enumerate only `M`, extend finite partial
maps preserving every first-order formula, and take the union. -/
theorem nonempty_elementaryEmbedding_of_typesIsolated [Countable M]
    (hM : TypesIsolated L M) (N : Type w') [L.Structure N] [N ⊨ L.completeTheory M] :
    Nonempty (M ↪ₑ[L] N) := by
  sorry

omit [Nonempty M] in
/-- **Internal Scott rank at most `ω`** from orbits determined at finite levels.  This is the
library's convention, `⨆ a, orbitRank a + 1`; no equality of ranks is asserted. -/
theorem internalScottRank_le_omega0_of_finite_levels
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ k : ℕ,
      ∀ b : Fin n → M, BFEquiv (L := L) (k : Ordinal.{w}) n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    internalScottRank (L := L) M ≤ Ordinal.omega0 := by
  refine internalScottRank_le_of_orbits_determined fun n a => ?_
  obtain ⟨k, hk⟩ := h n a
  exact ⟨k, Ordinal.natCast_lt_omega0 k, hk⟩

omit [Nonempty M] in
/-- **Internal Scott rank at most `ω`** from first-order orbit formulas (target, generic).  The
orbit formula has finite quantifier rank, and back-and-forth equivalence at that level forces
agreement on it.  `[Countable M]` is the hypothesis of that agreement,
`BFEquiv_implies_agree_formulas_omega`; its levels are in `Ordinal.{0}`, and
`BFEquiv.ofOrdinalLift` and `BFEquiv.toOrdinalLift` pass to `Ordinal.{w}`.  The finite rank of a
first-order formula in `L_{ω₁,ω}` is to be added upstream. -/
theorem internalScottRank_le_omega0_of_orbitDefinedBy [L.IsRelational] [Countable M]
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n), OrbitDefinedBy a φ) :
    internalScottRank (L := L) M ≤ Ordinal.omega0 := by
  sorry

end Orbits

/-! ## C. A geometric obstruction

The generic shape: a binary hull in which, of any three distinct points, one lies in the hull of
the other two (two-generation), and a family of self-maps each fixing pointwise the hull of any
two points it fixes (pointwise hull fixation).  For a realization, the hull is the canonical
finite hull and the maps are its automorphisms; both hypotheses are to be proved from exact
consistency and covering alone. -/

namespace HullObstruction

variable {M : Type u} (hull : M → M → Set M) (Aut : Set (M → M))

/-- The core step: with `p` in the hull of `q` and `r`, the transposition of `p` with a fourth
point `s` fixing `q` and `r` cannot extend to a map in `Aut`. -/
theorem false_of_swap {S : Set M}
    (hfix : ∀ g ∈ Aut, ∀ x y, g x = x → g y = y → ∀ z ∈ hull x y, g z = z)
    (hperm : ∀ σ : Equiv.Perm S, ∃ g ∈ Aut, ∀ s : S, g s = σ s)
    {p q r s : M} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hs : s ∈ S)
    (hqp : q ≠ p) (hqs : q ≠ s) (hrp : r ≠ p) (hrs : r ≠ s) (hps : p ≠ s)
    (hmem : p ∈ hull q r) : False := by
  classical
  obtain ⟨g, hg, hgσ⟩ := hperm (Equiv.swap ⟨p, hp⟩ ⟨s, hs⟩)
  have hgq : g q = q := by
    have := hgσ ⟨q, hq⟩
    rw [Equiv.swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hqp)
      (by simpa [Subtype.ext_iff] using hqs)] at this
    exact this
  have hgr : g r = r := by
    have := hgσ ⟨r, hr⟩
    rw [Equiv.swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hrp)
      (by simpa [Subtype.ext_iff] using hrs)] at this
    exact this
  have hgp : g p = s := by
    have := hgσ ⟨p, hp⟩
    rw [Equiv.swap_apply_left] at this
    exact this
  exact hps ((hfix g hg q r hgq hgr p hmem).symm.trans hgp)

/-- **No four points have all their permutations extended.**  Under two-generation and pointwise
hull fixation, no set containing four distinct points has every permutation extended by a map in
`Aut`. -/
theorem false_of_four_points {S : Set M}
    (htwo : ∀ x y z : M, x ≠ y → y ≠ z → x ≠ z →
      z ∈ hull x y ∨ x ∈ hull y z ∨ y ∈ hull x z)
    (hfix : ∀ g ∈ Aut, ∀ x y, g x = x → g y = y → ∀ z ∈ hull x y, g z = z)
    (hperm : ∀ σ : Equiv.Perm S, ∃ g ∈ Aut, ∀ s : S, g s = σ s)
    {a b c d : M} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    False := by
  rcases htwo a b c hab hbc hac with h | h | h
  · exact false_of_swap hull Aut hfix hperm hc ha hb hd hac had hbc hbd hcd h
  · exact false_of_swap hull Aut hfix hperm ha hb hc hd hab.symm hbd hac.symm hcd had h
  · exact false_of_swap hull Aut hfix hperm hb ha hc hd hab had hbc.symm hcd hbd h

/-- **The obstruction.**  Under two-generation and pointwise hull fixation, no infinite set has
all its permutations extended by maps in `Aut`. -/
theorem not_forall_perm_extends_of_infinite {S : Set M} (hS : S.Infinite)
    (htwo : ∀ x y z : M, x ≠ y → y ≠ z → x ≠ z →
      z ∈ hull x y ∨ x ∈ hull y z ∨ y ∈ hull x z)
    (hfix : ∀ g ∈ Aut, ∀ x y, g x = x → g y = y → ∀ z ∈ hull x y, g z = z) :
    ¬ ∀ σ : Equiv.Perm S, ∃ g ∈ Aut, ∀ s : S, g s = σ s := by
  intro hperm
  let f := hS.natEmbedding
  have hne : ∀ i j : ℕ, i ≠ j → (f i : M) ≠ f j := fun i j hij h =>
    hij (f.injective (Subtype.ext h))
  exact false_of_four_points hull Aut htwo hfix hperm (f 0).2 (f 1).2 (f 2).2 (f 3).2
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide))

/-- **Two-generation for three points**, from the whole-hull two-generation hypothesis of the
library's `TwoGeneratorCardinality` (the hull of every finite set is the hull of at most two of
its points): of three distinct points, one lies in the closure of the other two. -/
theorem mem_closure_pair_of_twoGeneration [DecidableEq M] (c : ClosureOperator (Finset M))
    (hgen : ∀ S : Finset M, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) {x y z : M}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    z ∈ c {x, y} ∨ x ∈ c {y, z} ∨ y ∈ c {x, z} := by
  obtain ⟨T, hTS, hT2, hTc⟩ := hgen {x, y, z}
  have hmem : ∀ w ∈ ({x, y, z} : Finset M), w ∈ c T := fun w hw => by
    rw [hTc]; exact c.le_closure _ hw
  have hcard : ({x, y, z} : Finset M).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_pair hyz]
  by_cases hz : z ∈ T
  · by_cases hx : x ∈ T
    · by_cases hy : y ∈ T
      · have : ({x, y, z} : Finset M) ⊆ T := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card this
        omega
      · right; right
        have hT : T ⊆ {x, z} := by
          intro w hw
          have := hTS hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
          rcases this with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact absurd hw hy
          · exact Or.inr rfl
        exact c.monotone hT (hmem y (by simp))
    · right; left
      have hT : T ⊆ {y, z} := by
        intro w hw
        have := hTS hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact absurd hw hx
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact c.monotone hT (hmem x (by simp))
  · left
    have hT : T ⊆ {x, y} := by
      intro w hw
      have := hTS hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hw hz
    exact c.monotone hT (hmem z (by simp))

/-- The obstruction for a finite-hull closure operator with whole-hull two-generation. -/
theorem not_forall_perm_extends_of_twoGeneration [DecidableEq M] (c : ClosureOperator (Finset M))
    (hgen : ∀ S : Finset M, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S)
    (hfix : ∀ g ∈ Aut, ∀ x y, g x = x → g y = y → ∀ z ∈ c {x, y}, g z = z)
    {S : Set M} (hS : S.Infinite) :
    ¬ ∀ σ : Equiv.Perm S, ∃ g ∈ Aut, ∀ s : S, g s = σ s :=
  not_forall_perm_extends_of_infinite (fun x y => (↑(c {x, y}) : Set M)) Aut hS
    (fun _ _ _ hxy hyz hxz => by
      simpa only [Finset.mem_coe] using mem_closure_pair_of_twoGeneration c hgen hxy hyz hxz)
    (fun g hg x y hx hy z hz => hfix g hg x y hx hy z (Finset.mem_coe.mp hz))

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
#check FirstOrder.Language.BoundedFormulaω.realize_equiv
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.ofExtensionFamily
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.family_bfEquiv
set_option linter.hashCommand false in
#check FirstOrder.Language.exists_automorphism_of_bfEquiv_all
set_option linter.hashCommand false in
#check FirstOrder.Language.BoundedFormula.toLω
set_option linter.hashCommand false in
#check FirstOrder.Language.Formula.realize_toLω
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv_implies_agree_formulas_omega
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv.ofOrdinalLift
set_option linter.hashCommand false in
#check FirstOrder.Language.BFEquiv.toOrdinalLift
set_option linter.hashCommand false in
#check FirstOrder.Language.realize_scottFormula_iff_BFEquiv
set_option linter.hashCommand false in
#check FirstOrder.Language.PotentialIso.countable_toEquiv_graph
set_option linter.hashCommand false in
#check FirstOrder.Language.internalScottRank_le_of_orbits_determined
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

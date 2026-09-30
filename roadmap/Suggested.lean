import InfinitaryLogic.OrdinalCountability
import InfinitaryLogic.Descriptive.StructureIsoSetoid

/-!
# Selected interfaces for the roadmap

`README.md` and `IMPLEMENTATION.md` are authoritative; this file is nonexhaustive and leaves the
formalization free.
This file is a HUMAN-OWNED SKETCH OF THEOREM STATEMENTS, NOT PART OF THE LIBRARY.
The bodies marked `sorry` are theorem statements still to be proved. Definitions have
actual bodies. The file is outside the library build; check it with
`lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true roadmap/Suggested.lean`.
No new verified Lean result is claimed.

Mathlib and the pinned infinitary-logic library are intended dependencies.
The concrete finite construction is specified in README and SEMANTIC_CONTRACT;
proving these general statements alone does not construct it.
-/

set_option autoImplicit false
noncomputable section

namespace Roadmap

universe u v w z

/-! ## 0. Restriction of lawful sections and bounded observations

Here X and Y already denote lawful section spaces. OX and OY are observation
spaces, not necessarily spaces of lawful sections. Apply the statement separately
at every PERMITTED cap; no assertion about unrestricted caps is hidden here.
-/

namespace ObservationLifting

variable {X : Type u} {Y : Type v} {OX : Type w} {OY : Type z}

def ball (obs : Y → OY) (q : Y) : Set Y := {q' | obs q' = obs q}

def Lifts (r : Y → X) (obsX : X → OX) (obsY : Y → OY) : Prop :=
  ∀ q p, obsX p = obsX (r q) → ∃ q', r q' = p ∧ obsY q' = obsY q

/-- Observation compatibility is weaker than demanding a lawful cap map. -/
theorem lifts_iff_ball_image (r : Y → X) (obsX : X → OX) (obsY : Y → OY)
    (hcompat : ∀ q q', obsY q = obsY q' → obsX (r q) = obsX (r q')) :
    Lifts r obsX obsY ↔ ∀ q, r '' ball obsY q = ball obsX (r q) := by
  constructor
  · intro hl q
    apply Set.Subset.antisymm
    · rintro _ ⟨q', hq', rfl⟩
      exact hcompat q' q hq'
    · intro p hp
      obtain ⟨q', hr, ho⟩ := hl q p hp
      exact ⟨q', ho, hr⟩
  · intro himg q p hp
    have hp' : p ∈ ball obsX (r q) := hp
    rw [← himg q] at hp'
    obtain ⟨q', ho, hr⟩ := hp'
    exact ⟨q', hr, ho⟩

end ObservationLifting

/-! ## 0. A countable cover, not a canonical classification invariant -/

namespace Counting

theorem countable_of_subsingleton_cover {I : Type u} {C : Type v} [Countable C]
    (P : C → I → Prop)
    (hsub : ∀ c i j, P c i → P c j → i = j)
    (hcover : ∀ i, ∃ c, P c i) : Countable I := by
  choose c hc using hcover
  apply Function.Injective.countable (f := c)
  intro i j hij
  apply hsub (c i) i j (hc i)
  rw [hij]
  exact hc j

/- The concrete count of terminal classes must prove its cover and the three comparisons.
Its index is (Σ n, StageType α n) ⊕ ℕ ⊕ Unit, not characteristic arity.
The descriptions may overlap. Grade zero must yield the empty rigid core.
-/

end Counting

/-! ## 0. Directed numerical limits

Apply only after proving that actual rooted covers form the required directed
system and that the transported-cell observation is monotone.
-/

namespace DirectedLimits

open Filter

theorem monotone_nat_dichotomy {P : Type u} [Preorder P] [Nonempty P]
    [IsDirected P (· ≤ ·)] (f : P → ℕ) (hf : Monotone f) :
    (∃ n, ∀ᶠ p in atTop, f p = n) ∨
      (∀ n, ∀ᶠ p in atTop, n < f p) := by
  sorry

/- Reuse existing ENat/filter results where available. The interpretation
of a finite limit n is α+n and of infinity is the FORMAL top, not α+ω.
Finite-family synchronization and reindexing should remain general lemmas.
-/

end DirectedLimits

/-! ## 5. Countable losses and observations: no stopping-rank hypothesis -/

namespace Domains

open Cardinal

abbrev firstUncountable : Ordinal.{0} := (aleph 1).ord

/-- This generic upper-level lemma already exists upstream; use it. -/
theorem countable_complement {Q : Type u} (D : Ordinal.{0} → Set Q)
    (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < firstUncountable → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ δ, Order.IsSuccLimit δ → δ < firstUncountable →
      (⋂ ξ < δ, D ξ) ⊆ D δ) :
    ∀ η, η < firstUncountable → (D η)ᶜ.Countable := by
  change ∀ η, η < (aleph 1).ord → (D η)ᶜ.Countable
  change ∀ ξ, ξ < (aleph 1).ord → (D ξ \ D (ξ + 1)).Countable at hsucc
  change ∀ δ, Order.IsSuccLimit δ → δ < (aleph 1).ord →
    (⋂ ξ < δ, D ξ) ⊆ D δ at hlim
  rw [Cardinal.ord_aleph] at hsucc hlim ⊢
  exact InfinitaryLogic.compl_countable_of_loss D h0 hsucc hlim

/-- No topology, measurability, nonempty domain, or rank function is required.
Proved in the library as `VaughtConjecture.Counting.countable_split_of_uniform_domain`
(with `D` implicit); the statement is kept here as part of the target list. -/
theorem countable_split_of_uniform_domain {Q : Type u} (D : Set Q)
    (P : Q → Prop) (hsmall : Dᶜ.Countable)
    (huniform : ∀ q ∈ D, ∀ s ∈ D, P q ↔ P s) :
    ({q | P q} : Set Q).Countable ∨ ({q | ¬ P q} : Set Q).Countable := by
  by_cases hex : ∃ q ∈ D, P q
  · obtain ⟨q, hq, hp⟩ := hex
    right
    exact Set.Countable.mono
      (fun s hs hsd => hs ((huniform q hq s hsd).mp hp)) hsmall
  · left
    exact Set.Countable.mono (fun q hq hqd => hex ⟨q, hqd, hq⟩) hsmall

/-- The lower bound is independent of small losses and logical comparison.
Proved in the library, for any linear successor order and any set of indices with nonempty
successor losses, as `VaughtConjecture.Counting.exists_injective_mem_sdiff_succ`; the statement
is kept here, with its `sorry`, as part of the target list. -/
theorem exists_injective_loss_choice {Q : Type u} (D : Ordinal.{0} → Set Q)
    (hanti : Antitone D)
    (hne : ∀ ξ, ξ < firstUncountable → (D ξ \ D (ξ + 1)).Nonempty) :
    ∃ f : Set.Iio firstUncountable → Q, Function.Injective f ∧
      ∀ ξ, f ξ ∈ D ξ.1 \ D (ξ.1 + 1) := by
  sorry

/- Concrete statements to prove, not replaced by the abstract lemmas:

* define D from literal model expansion existence on isomorphism classes;
* prove coherent countable-limit expansion;
* map each loss into fixed-stage terminal classes;
* prove whole-finite-cover comparison at block η for qrank ≤ η;
* construct a TOP-FREE terminal model at each countable block;
* use expansion uniqueness to put its base class in that block's loss.

The thinness theorem must use actual satisfaction on model codes.
Never put an assumed Borel structure on Q. Use the existing InfinitaryLogic (the pinned
infinitary-logic library) class-presentation, Scott-separation, and small-vocabulary results,
and its thinness theorem for countable sentence splits
(`Sentenceω.isThinOnNatModels_of_countable_sentence_splits`). The upper bound is Scott
separation on the persistent core; Morley's dichotomy is an alternative that is not used.
-/

end Domains

/-! ## Optional: finite-character closure and its naturality

These definitions/theorems can be reused for any finite hull. They add no new
capped-extension requirement and are not needed for the main theorem on the spectrum.
-/

namespace Hull

variable {M : Type u} {N : Type v}

def finitaryExtension (h : Finset M → Finset M) (A : Set M) : Set M :=
  {x | ∃ F : Finset M, (↑F : Set M) ⊆ A ∧ x ∈ h F}

theorem finitaryExtension_unique (h : Finset M → Finset M)
    (c d : Set M → Set M)
    (hc : ∀ A x, x ∈ c A ↔ ∃ F : Finset M, (↑F : Set M) ⊆ A ∧ x ∈ h F)
    (hd : ∀ A x, x ∈ d A ↔ ∃ F : Finset M, (↑F : Set M) ⊆ A ∧ x ∈ h F) :
    c = d := by
  funext A
  apply Set.ext
  intro x
  exact (hc A x).trans (hd A x).symm

theorem image_finitaryExtension [DecidableEq M] [DecidableEq N]
    (e : M ≃ N) (h : Finset M → Finset M) (k : Finset N → Finset N)
    (hpres : ∀ F, (h F).image e = k (F.image e)) (A : Set M) :
    e '' finitaryExtension h A = finitaryExtension k (e '' A) := by
  sorry

/- Concrete optional hull-operation target (see HULL_ALGEBRA.md):

For each ACTUAL finite base type q and indices i₀,i₁ containing its extremes,
use the existing finite formula
  θ(x₀,x₁,y) := ∃ z̄, P_q(z̄) ∧ z_i₀=x₀ ∧ z_i₁=x₁ ∧ z_j=y.
Prove global single-valuedness from chart uniqueness. Totalize with x₀ when
there is no witness; the graph is definable without choosing a base point.
Show that the resulting countable family of binary operations generates exactly
the canonical hull closure. Deduce cl(A) ⊆ dcl(A), not the reverse inclusion.

The concrete operations and both closure inclusions must be CONSTRUCTED;
assuming a record field that they already generate cl does not establish this.
-/

end Hull

/-! ## The main theorem, stated with actual library objects

The concrete language and sentence must come from the independent finite
construction, with the semantic contract (SEMANTIC_CONTRACT.md) unchanged. This predicate may not be
assumed in place of any construction. The final theorem has no hypotheses
asserting this predicate or the capped-extension/classification conclusions.
-/

open FirstOrder Language

/-- The models of `φ` coded on `ℕ` have exactly `ℵ₁` isomorphism classes, and there is no
perfect set of pairwise nonisomorphic such models. -/
def HasThinAlephOneSpectrum {L : Language.{0, 1}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω) : Prop :=
  Cardinal.mk (Quotient (isoSetoid φ)) = Cardinal.aleph 1 ∧
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

/- Required concrete theorem, where `concreteSentence` is the density sentence (the structural
clauses and the one-point capped-extension clause):
  theorem concreteSentence_hasThinAlephOneSpectrum :
    HasThinAlephOneSpectrum concreteSentence := ...
plus the no-finite-model theorem, actual structure/realization correspondence, the
required equivalence of `concreteSentence` with the four-family sentence, and the
all-countable-carrier spectrum and perfect-set variants.

No firstFailure, characteristic-arity, canonical-stop, global-departure, or
Scott-rank-equality target is a premise of this theorem.
-/

end Roadmap

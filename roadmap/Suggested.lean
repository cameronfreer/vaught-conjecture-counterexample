import InfinitaryLogic.OrdinalCountability
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import InfinitaryLogic.Scott.BackAndForth
import Mathlib.ModelTheory.Fraisse

/-!
# Selected interfaces for the roadmap

`README.md` and `IMPLEMENTATION.md` are authoritative; this file is nonexhaustive and leaves the
formalization free.
This file is a SKETCH OF THEOREM STATEMENTS, NOT PART OF THE LIBRARY.
The bodies marked `sorry` are theorem statements still to be proved. Definitions have
actual bodies. The file is outside the library build; check it with
`lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true roadmap/Suggested.lean`.
Section 6's approximate comparison is proved here from the hypotheses stated in that section;
no library result is claimed.

Mathlib and the pinned infinitary-logic library are the current dependencies; section 3 also
names statements of ComputableModelTheory, prospective: neither available upstream nor pinned
(`IMPLEMENTATION.md`, "Dependency pins").
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
at every cap self-visible at the target grade (not at the permitted cutoffs of
receiving); no assertion about other caps is hidden here.
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

/-! ## 3. The top-free witnesses: the finite age and its classical limit

Statement shapes for the hypotheses and the reconstruction of `README.md`, section "The
top-free witnesses: the finite age and its classical limit".  Charts are abstract here: a type
`Chart n` of charts on `n` points with exact partial restriction `restrict`, as in the chart
system of `SuggestedInterfaces.lean`, and a map `rel` sending a chart to a relation symbol of a
language `L` (the stage chart language, or its definitional expansion by the hull operations).
The concrete charts, the hull operations, and the amalgamation proof are not constructed here.

The classical theorems applied in steps 3–6 are prospective (neither available upstream nor pinned)
(`IMPLEMENTATION.md`, "Dependency pins") and are not named in Lean here: from
ComputableModelTheory, `representativeClass`, `isFraisse_representativeClass`, the existence
theorem, and `exists_factor_tuple_of_age_subset`.  The orbit formula of a chart and the
orbit theory are companion material (`SuggestedCompanions.lean`, section B).  Mathlib's
`IsUltrahomogeneous.extend_embedding` is available now.
-/

namespace ClassicalLimit

open FirstOrder Language Structure

variable (Chart : ℕ → Type u)
variable (restrict : {n m : ℕ} → (Fin n ↪ Fin m) → Chart m → Option (Chart n))

/-- **Amalgamation of charts** (step 2), with the literal commuting root equation
`f₁.trans g₁ = f₂.trans g₂`.  Two charts restricting to the same chart along `f₁` and `f₂` are
both restrictions of one chart.  This is not strong amalgamation (the images of `g₁` and `g₂` may
overlap outside the image of the root).  The target is to prove it for the top-free finite
closed charts at a nonzero countable limit stage, from the plain form of the coatom extension
property followed by capping; after the definitional expansion by the hull operations it is
Mathlib's `FirstOrder.Language.Amalgamation` for the age of top-free charts. -/
def ChartAmalgamation : Prop :=
  ∀ {k m₁ m₂ : ℕ} (f₁ : Fin k ↪ Fin m₁) (f₂ : Fin k ↪ Fin m₂) (p₁ : Chart m₁) (p₂ : Chart m₂)
    (r : Chart k), restrict f₁ p₁ = some r → restrict f₂ p₂ = some r →
    ∃ (m : ℕ) (g₁ : Fin m₁ ↪ Fin m) (g₂ : Fin m₂ ↪ Fin m) (p : Chart m),
      f₁.trans g₁ = f₂.trans g₂ ∧ restrict g₁ p = some p₁ ∧ restrict g₂ p = some p₂

/-- **Joint embedding of charts** (step 2): any two charts are restrictions of one chart. -/
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

variable {L : Language.{v, w}} (rel : ∀ {n : ℕ}, Chart n → L.Relations n)
variable {M : Type z} [L.Structure M]

/-- **Literal recovery of chart relations**, with injectivity of labelled tuples: the relation of
the chart `p` holds at a tuple exactly when the tuple is injective and its evaluation is `p`. -/
def RecoversRelations (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M) (p : Chart n),
    RelMap (rel p) a ↔ ∃ t : Fin n ↪ M, ⇑t = a ∧ eval t = some p

variable (restrict) in
/-- **Exact partial restriction**: the evaluation of a face of an evaluated tuple is the literal
restriction of its type; an invisible face (`restrict f p = none`) evaluates to `none`. -/
def ExactRestriction (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)) : Prop :=
  ∀ {n m : ℕ} (t : Fin m ↪ M) (p : Chart m) (f : Fin n ↪ Fin m),
    eval t = some p → eval (f.trans t) = restrict f p

/-- **Covering** of arbitrary tuples, the empty tuple and repeated coordinates included: every
tuple factors literally through the points of an actual occurrence. -/
def CoversTuples (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M), ∃ (m : ℕ) (u : Fin m ↪ M) (b : Fin n → Fin m) (p : Chart m),
    ⇑u ∘ b = a ∧ eval u = some p

variable (restrict) in
/-- **The reconstruction predicate** (`SEMANTIC_CONTRACT.md`, item 11, without receiving):
literal recovery of the chart relations with injectivity of labelled tuples, exact partial
restriction, and covering.  It concerns the relations only: the identification of the function
symbols with the definable hull operations is the reconstruction roundtrip of
`SEMANTIC_CONTRACT.md`, item 11 (a statement still to be proved), which uses local chart
coverage and no homogeneity. -/
def Reconstructs (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)) : Prop :=
  RecoversRelations rel eval ∧ ExactRestriction restrict eval ∧ CoversTuples eval

/-- Uniqueness of labelled tuples: at most one chart relation holds at a tuple. -/
theorem eq_of_relMap_of_relMap {eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)}
    (h : RecoversRelations rel eval) {n : ℕ} {a : Fin n → M} {p q : Chart n}
    (hp : RelMap (rel p) a) (hq : RelMap (rel q) a) : p = q := by
  obtain ⟨t, rfl, htp⟩ := (h a p).mp hp
  obtain ⟨t', ht', htq⟩ := (h t q).mp hq
  have htt : t' = t := DFunLike.coe_injective ht'
  subst htt
  exact Option.some_injective _ (htp.symm.trans htq)

/-- Injectivity of labelled tuples: a tuple at which a chart relation holds is injective. -/
theorem injective_of_relMap {eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n)}
    (h : RecoversRelations rel eval) {n : ℕ} {a : Fin n → M} {p : Chart n}
    (hp : RelMap (rel p) a) : Function.Injective a := by
  obtain ⟨t, rfl, -⟩ := (h a p).mp hp
  exact t.injective

open Classical in
/-- The evaluation read from the relations: the chart whose relation holds at the tuple, and
`none` when no chart relation holds. -/
noncomputable def evalOfRel {n : ℕ} (t : Fin n ↪ M) : Option (Chart n) :=
  if h : ∃ p : Chart n, RelMap (rel p) ⇑t then some h.choose else none

/-- **Reconstruction from the age** (target; steps 4–5).  Let each chart `p` on `m` points be read
as a structure `S p` on `Fin m` whose chart relations are literally its faces (`hS`), and let every
finitely generated substructure of `M` be isomorphic to some `S p` (the age of `M` is contained in
the representative class of the charts).  Then the evaluation read from the relations reconstructs
the realization.  Intended proof: factor each tuple through a representative
(ComputableModelTheory's `exists_factor_tuple_of_age_subset`, prospective) and read the relations
there; `hid` and `hcomp` are the identity and composition laws of exact partial restriction. -/
theorem reconstructs_evalOfRel
    (hid : ∀ {n : ℕ} (p : Chart n), restrict (Function.Embedding.refl _) p = some p)
    (hcomp : ∀ {k n m : ℕ} (f : Fin k ↪ Fin n) (g : Fin n ↪ Fin m) (p : Chart m) (q : Chart n),
      restrict g p = some q → restrict (f.trans g) p = restrict f q)
    (S : ∀ {m : ℕ}, Chart m → L.Structure (Fin m))
    (hS : ∀ {m : ℕ} (p : Chart m) {n : ℕ} (f : Fin n → Fin m) (q : Chart n),
      (S p).RelMap (rel q) f ↔ ∃ g : Fin n ↪ Fin m, ⇑g = f ∧ restrict g p = some q)
    (hage : L.age M ⊆
      {N | ∃ (m : ℕ) (p : Chart m), Nonempty (@Language.Equiv L N (Fin m) N.str (S p))}) :
    Reconstructs restrict rel (evalOfRel rel (M := M)) := by
  sorry

variable (restrict) in
/-- **Receiving with all equations attached to one occurrence** (step 6).  For an evaluated
root `t` of type `p` and a one-point donor `d` over it, there is one occurrence `u` on `n + 1`
points whose restriction to the first `n` is literally `t`, whose evaluation is some `q`, and
whose `q` stands in the relation `agree q d` (agreement below the requested cutoff, one cutoff at
a time: for a donor with top labels, the occurrence depends on the cutoff).  Freshness of the new
point is the injectivity of `u`.  Receiving at a permitted cutoff `δ` is
`ReceivesOn restrict eval (agreeBelow δ)`, asserted for each `δ` separately. -/
def ReceivesOn (eval : {n : ℕ} → (Fin n ↪ M) → Option (Chart n))
    (agree : ∀ {n : ℕ}, Chart n → Chart n → Prop) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : Chart n) (d : Chart (n + 1)),
    eval t = some p → restrict Fin.castSuccEmb d = some p →
    ∃ (u : Fin (n + 1) ↪ M) (q : Chart (n + 1)),
      Fin.castSuccEmb.trans u = t ∧ eval u = some q ∧ agree q d

end ClassicalLimit

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

/-! ## 6. Full presentations: approximate extension and approximate comparison

Statement shapes for `README.md`, "Reduction to full presentations", with a complete proof of
approximate comparison from them. A presentation of a structure `M` is given here only through its
closed tuples (enumerations of finite closed sets) and their level observations at the levels up
to its own; fullness, exact comparison, and the count of full presentations are not stated here. The
level sets `S η n` are separate types with explicit projections `τ`; a single composition law on one
ambient set is not used. `BFEquiv` is the back-and-forth equivalence of InfinitaryLogic (available
at the pin). In the application the base language is relational, as `BFEquiv_implies_agreeQR`
requires for the passage to sentences; the comparison itself does not use relationality.
-/

namespace FullPresentation

open FirstOrder Language

/-- **Level observations**: countable sets `S η n` of observed invariants of `n`-tuples at each
level `η`, with projections `τ` from a higher level to a lower one that compose exactly. -/
structure LevelObservations where
  /-- The observed invariants of `n`-tuples at level `η`. -/
  S : Ordinal.{0} → ℕ → Type
  /-- Each level set is countable. -/
  countable : ∀ η n, Countable (S η n)
  /-- The projection from level `ξ` down to a level `η ≤ ξ`. -/
  τ : ∀ {η ξ : Ordinal.{0}}, η ≤ ξ → ∀ {n : ℕ}, S ξ n → S η n
  /-- The projection to the same level is the identity. -/
  τ_refl : ∀ {η : Ordinal.{0}} {n : ℕ} (s : S η n), τ le_rfl s = s
  /-- Projections compose. -/
  τ_comp : ∀ {η ξ ζ : Ordinal.{0}} (h₁ : η ≤ ξ) (h₂ : ξ ≤ ζ) {n : ℕ} (s : S ζ n),
    τ h₁ (τ h₂ s) = τ (h₁.trans h₂) s

/-- An **observed presentation** of `M` at level `level`: its closed tuples, with a closed
extension of every closed tuple containing any given point, and the level observations of closed
tuples, coherent under the projections up to `level`.  Fullness is not part of this structure. -/
structure ObservedPresentation (O : LevelObservations) (M : Type w) where
  /-- The level of the presentation. -/
  level : Ordinal.{0}
  /-- The closed tuples: enumerations of finite closed sets. -/
  IsClosed : ∀ {n : ℕ}, (Fin n → M) → Prop
  /-- Every point lies in a closed extension of every closed tuple. -/
  exists_closed_extension : ∀ {n : ℕ} (a : Fin n → M), IsClosed a → ∀ x : M,
    ∃ (k : ℕ) (c : Fin k → M) (j : Fin (n + k)),
      IsClosed (Fin.append a c) ∧ Fin.append a c j = x
  /-- The observation of a tuple at a level (read only on closed tuples, up to `level`). -/
  obs : ∀ (η : Ordinal.{0}) {n : ℕ}, (Fin n → M) → O.S η n
  /-- The observations of a closed tuple are coherent under the projections. -/
  obs_τ : ∀ {η ξ : Ordinal.{0}} (h : η ≤ ξ), ξ ≤ level → ∀ {n : ℕ} (a : Fin n → M),
    IsClosed a → O.τ h (obs ξ a) = obs η a

variable {L : Language.{u, v}}
variable {O : LevelObservations} {M : Type w} {N : Type z} [L.Structure M] [L.Structure N]

variable (L) in
/-- **Atomic recovery at level `0`**, across the two structures: closed tuples with equal
observations at level `0` have the same atomic type in the base language. -/
def AtomicAtZero (H : ObservedPresentation O M) (H' : ObservedPresentation O N) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M) (b : Fin n → N), H.IsClosed a → H'.IsClosed b →
    H.obs 0 a = H'.obs 0 b → SameAtomicType (L := L) a b

/-- **The approximate extension property (AE) at level `η`**, from `H` to `H'`: for closed tuples
`a` and `b` with equal observations at `η + 1`, every closed extension `a ++ c` in `H` is matched
by a closed extension `b ++ d` in `H'` of the same length, with equal observations at `η`.  The
target tuple `b` is kept literally; only the enlarged tuples are compared, one level down.  (AE)
in both directions is this property for `(H, H')` and for `(H', H)`. -/
def ApproxExtension (H : ObservedPresentation O M) (H' : ObservedPresentation O N)
    (η : Ordinal.{0}) : Prop :=
  ∀ {n : ℕ} (a : Fin n → M) (b : Fin n → N), H.IsClosed a → H'.IsClosed b →
    H.obs (Order.succ η) a = H'.obs (Order.succ η) b →
    ∀ {k : ℕ} (c : Fin k → M), H.IsClosed (Fin.append a c) →
      ∃ d : Fin k → N, H'.IsClosed (Fin.append b d) ∧
        H.obs η (Fin.append a c) = H'.obs η (Fin.append b d)

/-- **Approximate comparison.**  If two presentations of levels at least `η` satisfy the atomic
condition at `0` and (AE) in both directions at every level below `η`, then closed tuples with
equal observations at `η` are back-and-forth equivalent at `η` in the base structures, and so is
every corresponding selection `s` of their coordinates, repetitions allowed (`m = 0` compares the
structures).  The proof is by induction on `η`: at a successor, a closed extension containing the
requested point, (AE), and the selection of coordinates; at a limit, the projections.  The
library's `SameAtomicType` covers relations and equalities on variables, not terms: for a
language with function symbols the conclusion is weaker than the usual `≡_η`; the base language
of the application is relational. -/
theorem bfEquiv_comp_of_obs_eq (H : ObservedPresentation O M) (H' : ObservedPresentation O N)
    (hzero : AtomicAtZero L H H') {η : Ordinal.{0}}
    (hae : ∀ ζ, ζ < η → ApproxExtension H H' ζ ∧ ApproxExtension H' H ζ)
    (hη : η ≤ H.level) (hη' : η ≤ H'.level)
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) (ha : H.IsClosed a) (hb : H'.IsClosed b)
    (hobs : H.obs η a = H'.obs η b) {m : ℕ} (s : Fin m → Fin n) :
    BFEquiv (L := L) η m (a ∘ s) (b ∘ s) := by
  induction η using Ordinal.limitRecOn generalizing n a b m with
  | zero =>
    rw [BFEquiv.zero]
    have h0 := hzero a b ha hb hobs
    intro idx
    rw [AtomicIdx.holds_comp_eq_holds_pushforward, AtomicIdx.holds_comp_eq_holds_pushforward]
    exact h0 _
  | add_one ζ ih =>
    rw [← Order.succ_eq_add_one] at hη hη' hobs hae ⊢
    have ih := ih (fun ζ' h => hae ζ' (h.trans (Order.lt_succ ζ)))
    have hζ : ζ ≤ H.level := (Order.le_succ ζ).trans hη
    have hζ' : ζ ≤ H'.level := (Order.le_succ ζ).trans hη'
    have hobsζ : H.obs ζ a = H'.obs ζ b := by
      rw [← H.obs_τ (Order.le_succ ζ) hη a ha, ← H'.obs_τ (Order.le_succ ζ) hη' b hb, hobs]
    obtain ⟨hforth, hback⟩ := hae ζ (Order.lt_succ ζ)
    rw [BFEquiv.succ]
    refine ⟨ih hζ hζ' a b ha hb hobsζ s, fun x => ?_, fun y => ?_⟩
    · obtain ⟨k, c, j, hc, hj⟩ := H.exists_closed_extension a ha x
      obtain ⟨d, hd, hcd⟩ := hforth a b ha hb hobs c hc
      refine ⟨Fin.append b d j, ?_⟩
      have := ih hζ hζ' (Fin.append a c) (Fin.append b d) hc hd hcd
        (Fin.snoc (Fin.castAdd k ∘ s) j)
      rw [Fin.comp_snoc, Fin.comp_snoc, ← Function.comp_assoc, ← Function.comp_assoc,
        show Fin.append _ _ ∘ Fin.castAdd k = _ from funext (Fin.append_left _ _),
        show Fin.append _ _ ∘ Fin.castAdd k = _ from funext (Fin.append_left _ _), hj] at this
      exact this
    · obtain ⟨k, d, j, hd, hj⟩ := H'.exists_closed_extension b hb y
      obtain ⟨c, hc, hcd⟩ := hback b a hb ha hobs.symm d hd
      refine ⟨Fin.append a c j, ?_⟩
      have := ih hζ hζ' (Fin.append a c) (Fin.append b d) hc hd hcd.symm
        (Fin.snoc (Fin.castAdd k ∘ s) j)
      rw [Fin.comp_snoc, Fin.comp_snoc, ← Function.comp_assoc, ← Function.comp_assoc,
        show Fin.append _ _ ∘ Fin.castAdd k = _ from funext (Fin.append_left _ _),
        show Fin.append _ _ ∘ Fin.castAdd k = _ from funext (Fin.append_left _ _), hj] at this
      exact this
  | limit l hl ih =>
    rw [BFEquiv.limit l hl]
    intro β hβ
    have hobsβ : H.obs β a = H'.obs β b := by
      rw [← H.obs_τ hβ.le hη a ha, ← H'.obs_τ hβ.le hη' b hb, hobs]
    exact ih β hβ (fun ζ h => hae ζ (h.trans hβ)) (hβ.le.trans hη) (hβ.le.trans hη')
      a b ha hb hobsβ s

end FullPresentation

/-! ## Optional: finite-character closure and its naturality

These definitions/theorems can be reused for any finite hull. They add no new
receiving requirement and are not needed for the main theorem on the spectrum: the global
closure of infinite sets is optional, while the hull operations and their finite-set closure
equality below are core (README.md, Layer 2).
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

/- Concrete hull-operation target (see HULL_ALGEBRA.md).  The definable total hull operations and
the equality of hull closure with generated-substructure closure for finite sets are core
(README.md, Layer 2, facts 1–5); only the equality for infinite sets, the cardinality material,
and the descriptive consequences are optional.

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
asserting this predicate or the receiving/classification conclusions.
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

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.ScottDefinability
import InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.FiniteSupportClosure
import InfinitaryLogic.TwoGeneratorCardinality

/-! # Selected interfaces for the implementation roadmap

`IMPLEMENTATION.md` is the specification; this file is nonexhaustive.  It contains no admitted
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

/-- Unique restriction turns per-cap lifts into simultaneous preservation. Compatibility
and the exact extension equation remain explicit; observations need not themselves be lawful. -/
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

/-- Hypotheses of the observation-filtration argument, applied AFTER countable-loss induction.
An instance of this structure is not a proof of the countable-loss or receiving constructions
in the README. -/
structure ObservationFiltration (Q : Type 1) (O : Type u) (truth : O → Q → Prop) where
  domain : Ordinal.{0} → Set Q
  complement_countable : ∀ η, η < (Cardinal.aleph 1).ord → (domain η)ᶜ.Countable
  homogeneous : ∀ o, ∃ η, η < (Cardinal.aleph 1).ord ∧
    ∀ p ∈ domain η, ∀ q ∈ domain η, (truth o p ↔ truth o q)
  separates : ∀ p q, p ≠ q → ∃ o, ¬ (truth o p ↔ truth o q)

namespace ObservationFiltration

variable {Q : Type 1} {O : Type u} {truth : O → Q → Prop}
variable (F : ObservationFiltration Q O truth)

/-- Scott separation makes the persistent core subsingleton; departure is unnecessary. -/
theorem persistent_subsingleton :
    (⋂ η < (Cardinal.aleph 1).ord, F.domain η).Subsingleton := by
  intro p hp q hq
  by_contra hne
  obtain ⟨o, ho⟩ := F.separates p q hne
  obtain ⟨η, hη, hh⟩ := F.homogeneous o
  exact ho (hh p (Set.mem_iInter₂.mp hp η hη) q (Set.mem_iInter₂.mp hq η hη))

include F in
/-- Each observation has one countable truth side, without measurability on `Q`. -/
theorem countable_truth_side (o : O) :
    ({q | truth o q} : Set Q).Countable ∨ ({q | ¬ truth o q} : Set Q).Countable := by
  obtain ⟨η, hη, hh⟩ := F.homogeneous o
  have hc := F.complement_countable η hη
  by_cases h : ∃ q ∈ F.domain η, truth o q
  · obtain ⟨q, hq, ht⟩ := h
    exact Or.inr (hc.mono fun p hp hpd => hp ((hh p hpd q hq).mpr ht))
  · exact Or.inl (hc.mono fun q hq hqd => h ⟨q, hqd, hq⟩)

end ObservationFiltration

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

/- Proposed substantive targets (not declared as axioms or claimed proved here):

FiniteSemantics: construct the concrete ChartSystem and prove countability of charts,
  legal face restriction, stage reduction, lawful lifting with all retained caps.
Receiving: exact literal root + one actual occurrence + requested capped/LOW equations on it.
ChainConstruction: finite master + root absorption + supported-invisible permanence + union.
StableLift: consistency-only uniqueness; consistency/covering lawfulness; cap modelhood.
Comparison: finite-donor one-sided transfer; rooted BF; singleton terminal conditions.
Domains: expansion uniqueness + limit existence; terminal losses countable and nonempty.
MainTheorem: countable-loss induction + the observation filtration above + Scott/DST library.

Every data definition also needs extensionality, identity/composition, projection and
transport APIs. Use directional simp rules for these; never a transitivity instance for
the nontransitive transformation relation. See README.md for exact semantic boundaries.
-/

end Roadmap

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthLevelRoute

/-!
# Expected failure: altered semantics

A copy of `comparator/SolutionDefinitions.lean` and `comparator/Solution.lean` in which one
definition used by the reference statement is altered: `NoFiniteModels` excludes the finite
models on nonempty carriers only (`Fin (n + 1)` in place of `Fin n`), so it no longer excludes the
empty structure.  The theorem has the text of the reference statement and a valid proof with the
standard axioms only.  Comparator must reject it because a definition used by the statement
differs from the reference (`comparator/check.sh` asserts the diagnostic naming
`PalomarChallenge.NoFiniteModels`).
-/

namespace PalomarChallenge

variable (R : ℕ → Type 1)

/-- A purely relational language, with no functions or constants. -/
def language : FirstOrder.Language := ⟨fun _ => Empty, R⟩

instance : (language R).IsRelational := fun _ => (inferInstance : IsEmpty Empty)

/-- A relation symbol together with a tuple of arguments. -/
abbrev RelQueryOn (M : Type) := Σ r : (Σ n, R n), (Fin r.1 → M)

/-- A Boolean relation truth table. -/
abbrev Code (M : Type) := RelQueryOn R M → Bool

/-- Codes for structures on the natural numbers. -/
abbrev StructureSpace := Code R ℕ

/-- Decode every relation coordinate. -/
@[instance_reducible]
def structureOfCode {M : Type} (c : Code R M) : (language R).Structure M where
  funMap := fun f => isEmptyElim f
  RelMap := fun {n} r xs => c ⟨⟨n, r⟩, xs⟩ = true

/-- Ordinary satisfaction in the decoded structure. -/
def Satisfies {M : Type} (φ : (language R).Sentenceω) (c : Code R M) : Prop :=
  letI := structureOfCode R c
  FirstOrder.Language.BoundedFormulaInf.Realize (M := M) φ Empty.elim Fin.elim0

/-- The set of sentence models in the ordinary coding space. -/
def ModelsOf (φ : (language R).Sentenceω) : Set (StructureSpace R) :=
  {c | Satisfies R φ c}

/-- Isomorphism by a permutation preserving every relation truth value. -/
def Isomorphic (c d : Code R ℕ) : Prop :=
  ∃ e : ℕ ≃ ℕ, ∀ n (r : R n) (xs : Fin n → ℕ), c ⟨⟨n, r⟩, xs⟩ = d ⟨⟨n, r⟩, e ∘ xs⟩

/-- Isomorphism of codes is an equivalence relation. -/
theorem isomorphic_equivalence : Equivalence (Isomorphic R) := ⟨
    fun c => ⟨Equiv.refl ℕ, fun _ _ _ => rfl⟩,
    by
      rintro c d ⟨e, h⟩
      refine ⟨e.symm, fun n r xs => ?_⟩
      simpa [Function.comp_def] using (h n r (e.symm ∘ xs)).symm,
    by
      rintro c d f ⟨e, h⟩ ⟨e', h'⟩
      exact ⟨e.trans e', fun n r xs => (h n r xs).trans (h' n r (e ∘ xs))⟩⟩

/-- The equivalence relation on codes. -/
def isoSetoid : Setoid (Code R ℕ) := ⟨Isomorphic R, isomorphic_equivalence R⟩

/-- Actual models, not arbitrary codes or chosen representatives. -/
abbrev NatModel (φ : (language R).Sentenceω) := {c : Code R ℕ // Satisfies R φ c}

/-- Isomorphism restricted to the models. -/
def modelSetoid (φ : (language R).Sentenceω) : Setoid (NatModel R φ) :=
  Setoid.comap Subtype.val (isoSetoid R)

/-- Isomorphism classes of models. -/
abbrev IsoClasses (φ : (language R).Sentenceω) := Quotient (modelSetoid R φ)

/-- **Altered**: no finite coded model on a nonempty carrier; the empty carrier is not
excluded. -/
def NoFiniteModels (φ : (language R).Sentenceω) : Prop :=
  ∀ n (c : Code R (Fin (n + 1))), ¬ Satisfies R φ c

/-- No nonempty perfect set of pairwise nonisomorphic models, in the product topology. -/
def NoPerfectAntichain (φ : (language R).Sentenceω) : Prop :=
  ¬ ∃ P : Set (StructureSpace R), P.Nonempty ∧ Perfect P ∧
    (∀ c ∈ P, Satisfies R φ c) ∧
      ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ Isomorphic R c d

/-! ### The three clauses for the density sentence -/

open FirstOrder Language VaughtConjecture

/-- Isomorphism of codes by a permutation of `ℕ` is `Language.Equiv` of the decoded structures,
the relation `structureIsoSetoid` of `InfinitaryLogic`. -/
theorem isomorphic_iff_structureIsoSetoid (c d : Code baseLanguage.{0}.Relations ℕ) :
    Isomorphic baseLanguage.{0}.Relations c d ↔ (structureIsoSetoid baseLanguage.{0}).r c d := by
  change _ ↔ Nonempty (@Language.Equiv baseLanguage.{0} ℕ ℕ
    (StructureSpaceOn.toStructure c) (StructureSpaceOn.toStructure d))
  constructor
  · rintro ⟨e, h⟩
    refine ⟨@Language.Equiv.mk baseLanguage.{0} ℕ ℕ (StructureSpaceOn.toStructure c)
      (StructureSpaceOn.toStructure d) e (fun f => isEmptyElim f) (fun {n} r xs => ?_)⟩
    change d ⟨⟨n, r⟩, e ∘ xs⟩ = true ↔ c ⟨⟨n, r⟩, xs⟩ = true
    rw [h n r xs]
  · rintro ⟨e⟩
    let σ := @Language.Equiv.toEquiv baseLanguage.{0} ℕ ℕ (StructureSpaceOn.toStructure c)
      (StructureSpaceOn.toStructure d) e
    refine ⟨σ, fun n r xs => ?_⟩
    have h := @Language.Equiv.map_rel' baseLanguage.{0} ℕ ℕ (StructureSpaceOn.toStructure c)
      (StructureSpaceOn.toStructure d) e n r xs
    change (d ⟨⟨n, r⟩, σ ∘ xs⟩ = true ↔ c ⟨⟨n, r⟩, xs⟩ = true) at h
    cases hc : c ⟨⟨n, r⟩, xs⟩ <;> cases hd : d ⟨⟨n, r⟩, σ ∘ xs⟩ <;> simp_all

/-- The quotient of the reference statement is the quotient `isoSetoid` of `InfinitaryLogic`,
for the density sentence. -/
theorem modelSetoid_baseLanguage_eq :
    modelSetoid baseLanguage.{0}.Relations baseLanguage.densitySentence.{0} =
      FirstOrder.Language.isoSetoid baseLanguage.densitySentence.{0} := by
  ext c d
  exact isomorphic_iff_structureIsoSetoid c.1 d.1

/-- **The count**: the density sentence has exactly `ℵ₁` classes of models coded on `ℕ`. -/
theorem card_isoClasses_densitySentence :
    Cardinal.mk (IsoClasses baseLanguage.{0}.Relations baseLanguage.densitySentence.{0}) =
      Cardinal.aleph 1 := by
  change Cardinal.mk (Quotient (modelSetoid baseLanguage.{0}.Relations _)) = _
  rw [modelSetoid_baseLanguage_eq]
  exact MainTheorem.vaughtCounterexample_allCarriers_densitySentence.{0}.1.1

/-- **No finite models on a nonempty carrier**: a code on `Fin (n + 1)` never satisfies the
density sentence. -/
theorem noFiniteModels_densitySentence :
    NoFiniteModels baseLanguage.{0}.Relations baseLanguage.densitySentence.{0} := by
  intro n c hc
  have hinf := MainTheorem.vaughtCounterexample_allCarriers_densitySentence.{0}.2.2.2.1
  exact not_finite_iff_infinite.mpr
    (@hinf (Fin (n + 1)) (structureOfCode baseLanguage.{0}.Relations c) hc) inferInstance

/-- **No perfect antichain** of models of the density sentence coded on `ℕ`. -/
theorem noPerfectAntichain_densitySentence :
    NoPerfectAntichain baseLanguage.{0}.Relations baseLanguage.densitySentence.{0} := by
  rintro ⟨P, hne, hperfect, hmodels, hanti⟩
  refine MainTheorem.vaughtCounterexample_allCarriers_densitySentence.{0}.1.2
    ⟨P, hperfect, hne, hmodels, fun c hc d hd hcd => ?_⟩
  by_contra hne
  exact hanti c hc d hd hne ((isomorphic_iff_structureIsoSetoid c d).mpr hcd)

/-- The reference statement, with the altered `NoFiniteModels`. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ :=
  ⟨baseLanguage.{0}.Relations, inferInstance, baseLanguage.densitySentence.{0},
    card_isoClasses_densitySentence, noFiniteModels_densitySentence,
    noPerfectAntichain_densitySentence⟩

end PalomarChallenge

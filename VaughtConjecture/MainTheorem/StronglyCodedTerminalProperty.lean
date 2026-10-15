/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.RestrictedHollow
import VaughtConjecture.Correspondence.Density.ClassRealization
import VaughtConjecture.Counting.Domains
import VaughtConjecture.MainTheorem.StronglyCodedSuccessor

/-!
# Terminal properties in the strongly coded receiving class, and the comparison targets

Roadmap, Layer 4 (the terminal classification: rigid finite core, eventual top grade, hollow
unbounded growth; the rigid-core, residual and hollow comparisons) and Correspondence, item 1
(the strongly coded legal stage types).

Throughout, `ξ : Ordinal.{0}`, `λ_ξ = blockStage ξ`, and realizations at `λ_ξ` are on a carrier
`M : Type w`.  The class is `Realization.IsStronglyCodedReceiving` and terminality in it is
`Realization.IsStronglyCodedTerminalAt` (`VaughtConjecture.MainTheorem.StronglyCodedSuccessor`).

**The index is reused.**  `TerminalProperty ξ` is an index type only, and
`Realization.HasTerminalProperty` is defined for every realization: neither bundles modelhood.  So
the same properties are used for the strongly coded class, unchanged: a globally rigid core of type
`p` (`inl ⟨k, p⟩`), a finite residual top grade `K` with no globally rigid core (`inr (inl K)`),
and cover-hollowness with unbounded growth (`inr (inr ())`).  This is a countable family of
properties for `ξ < ω₁` (`countable_terminalProperty`); it is **not yet countability up to
isomorphism**, which needs the comparisons below.

**The split** (`Realization.StronglyCodedTerminalSplitTarget`, proved: native construction).  A
realization terminal in the class at `ξ` has

* top-grade supremum `⊤`, and then it is cover-hollow
  (`Realization.IsStronglyCodedTerminalAt.isCoverHollow`): the hollow property; or
* top-grade supremum `0`, and then the empty tuple is a globally rigid core covering the stage
  type on no points: the rigid-core property on no points (**grade zero**,
  `Realization.IsStronglyCodedReceiving.hasTerminalProperty_zero`); or
* a positive natural number `K` as top-grade supremum, and then either some cover is a globally
  rigid core, or none is and the residual property `K` holds.

Terminality is used once, through the successor in the class, and only in the first case.  The
bounded branch needs no further input for the assignment of a property: whether a globally rigid
core exists is decided classically.  The residual grade is positive
(`Realization.IsStronglyCodedReceiving.ne_zero_of_residual`).  Grade zero needs only exact
consistency, covering (`Realization.exists_covers_zero_of_isCovering`, for the cover on no points)
and legal types (`Realization.isGloballyRigidCore_empty_iff_of_hasLegalTypes`), the model-level
`Realization.IsModel.exists_covers_zero` and `Realization.IsModel.isGloballyRigidCore_empty_iff`
with modelhood replaced by these class fields.  A chosen property is
`Realization.stronglyCodedTerminalProperty`; it is not canonical, as for models
(`VaughtConjecture.Continuation.Classification`).  Every property passes to a restricted one
(`Realization.exists_hasRestrictedTerminalProperty_of_hasTerminalProperty`, with no hypothesis).

**Exact receiving at a rigid root** (`Realization.StronglyCodedRigidRootTarget`, proved: native
construction).  The model-level `Realization.exists_covers_of_isRigidCoreIn` uses exact
consistency, the limit stage and finite-extension receiving of every legal donor.  In the class,
receiving is `Realization.HasFiniteExtensionReceivingIn` for the donors with strongly coded rows
(from the class field by `Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff` at the
block stage), and the donor's strong coding is an explicit premise.  The rigidity argument
(`StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn`) is unchanged.  With the age restricted to
strongly coded donors (`StageType.stronglyCodedRigidCoreAge`), age inclusion at a globally rigid
core holds in the class, since actual types are strongly coded
(`Realization.IsGloballyRigidCore.mem_stronglyCodedRigidCoreAge`), and exact receiving within that
age at any core follows
(`Realization.IsStronglyCodedReceiving.exactReceivingWithinAt_stronglyCodedRigidCoreAge`).

**The isomorphism conclusion.**  The model-level comparisons
(`VaughtConjecture.Continuation.Comparison`) conclude an isomorphism of the base structures
`M ≃[baseLanguage] N`, of expansions `R.IsExpansionOf`.  Here the conclusion is the native, literal
one: an isomorphism of realizations, `Realization.IsIso` (a bijection `e` of carriers with
`R.map e = S`).  The matched tuples of the back-and-forth (`Realization.CoverMatch`) are covers of
one literal stage type, so the comparison can be run in the relational language whose symbols are
the stage types, interpreted by covering; its isomorphisms are isomorphisms of realizations.  The
class language of [AFK26] (`templateLanguage`, with the structure
`ClassRealization.toStructure` of the class reading `Realization.classReading`) sees types only up
to cell renaming (`Realization.classReading_eq_classReading_iff`), so it gives the weaker
isomorphism of class readings; it is the reading of the conclusion on the correspondence side
(`Realization.ClassReadingEquivTarget`).  No base agreement between `R` and `S` is a premise: the
model-level comparisons use none either, `IsExpansionOf` only fixing the structure in which each
is compared.

**The targets** (stated here, not proved unless marked):

* (c) `Realization.ExactAgeIsoTarget`: the exact-age comparison without modelhood, concluding an
  isomorphism of realizations carrying one core to the other; and its class-language parts,
  `Realization.ClassReadingAtomicAgreementTarget` (covers of one type have the same atomic type in
  the class language, from exact consistency only: the replacement of
  `Realization.Covers.sameAtomicType`, which uses `IsExpansionOf`) and
  `Realization.ClassReadingEquivTarget`.  `Realization.ExactAgeIsoTarget` and
  `Realization.ClassReadingEquivTarget` are proved in
  `VaughtConjecture.MainTheorem.StronglyCodedComparison` (`Realization.exactAgeIsoTarget`, in the
  language of stage types, and `Realization.classReadingEquivTarget`);
  `Realization.ClassReadingAtomicAgreementTarget` is not used there and remains stated only.
* (b) `Realization.StronglyCodedRigidCoreIsoTarget`: the rigid-core comparison in the class.  No
  premise beyond the class: (c) with the proved restricted age inclusion and exact receiving.
  Proved in `VaughtConjecture.MainTheorem.StronglyCodedComparison`
  (`Realization.stronglyCodedRigidCoreIsoTarget`).
* the residual and hollow comparisons, through one engine
  `Realization.StronglyCodedExactGrowthIsoTarget` (exact one-point receiving of the strongly coded
  cofaces of top grade at most the top-grade supremum, `Realization.HasExactStronglyCodedReceiving`,
  in both), and
  `Realization.StronglyCodedResidualIsoTarget` (premise: restricted (R2),
  `Realization.StronglyCodedResidualReceiving`) and `Realization.StronglyCodedHollowIsoTarget`
  (premise: restricted (R3), `Realization.StronglyCodedHollowReceiving`, for the restricted hollow
  property: cover-hollowness without a globally rigid core).
  The exact-growth, residual and hollow comparisons are proved in
  `VaughtConjecture.MainTheorem.StronglyCodedComparison`
  (`Realization.stronglyCodedExactGrowthIsoTarget`, `Realization.stronglyCodedResidualIsoTarget`,
  `Realization.stronglyCodedHollowIsoTarget`); the residual and hollow ones keep restricted (R2)
  and (R3) as premises.  Both premises are proved (`Realization.stronglyCodedResidualReceiving`,
  in `VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`, and
  `Realization.stronglyCodedHollowReceiving`, in
  `VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier`).
* `Realization.StronglyCodedTerminalIsoTarget`: two realizations terminal in the class sharing a
  restricted terminal property are isomorphic, under restricted (R2) and (R3) on both carriers.
  It follows from the three comparisons
  (`Realization.stronglyCodedTerminalIsoTarget_of_comparisons`, proved: case analysis).
* `Realization.StronglyCodedTerminalCountTarget`: for `ξ < ω₁`, countably many isomorphism classes
  of realizations on `ℕ` terminal in the class at `ξ`.  It follows from the previous target
  (`Realization.stronglyCodedTerminalCountTarget_of_isoTarget`, proved: the countable union of
  subsingletons, `Counting.countable_of_subsingleton_cover`, over `countable_terminalProperty`).
  With restricted (R2) and (R3) instantiated, the isomorphism theorem and the count are proved
  with no (R2) or (R3) premise in `VaughtConjecture.MainTheorem.StronglyCodedTerminalCount`
  (`Realization.stronglyCodedTerminalIso`, `Realization.stronglyCodedTerminalClasses_countable`;
  the stage bound `ξ < ω₁` remains).

**Modelhood uses of the model-level comparison and their replacements.**

Each entry: model-level use; where it is used; replacement in the class.

* `IsModel.isConsistent`; rigid root, age inclusion, one point to many, forth step; the
  `isConsistent` field.
* `IsModel.isCovering`; forth step (`Realization.IsCovering.exists_castAdd`); the `isCovering`
  field.
* `IsModel.isLegal`; age inclusion, empty core; the `hasLegalTypes` field.
* `IsModel.nonempty_occurrence`; the cover on no points; `IsCovering.nonempty_occurrence`.
* `HasFiniteExtensionReceiving` ((R1), assumed for models); rigid root;
  `HasFiniteExtensionReceivingIn` for strongly coded donors, from the `receiving` field, with the
  donor's strong coding explicit.
* `IsExpansionOf` (the base reduct); atomic agreement of matched tuples; the language of stage
  types (literal), or the class language (`ClassReadingAtomicAgreementTarget`), from exact
  consistency.
* `ResidualReceiving` ((R2), assumed for models); residual comparison; restricted (R2): class
  members, strongly coded cofaces.
* `HollowReceiving` ((R3), assumed for models); hollow comparison; restricted (R3): class members
  without a globally rigid core, strongly coded cofaces.

Strong coding of the actual types (`isStronglyCoded` field) is what lets the ages be restricted to
strongly coded donors.  Unrestricted saturation or unrestricted receiving is not invoked by any
proved statement here.  For (R3), the model-level route realizes a growth carrier through
unrestricted saturation, and strongly coded inputs do not certify the new rows of that carrier.
The original ladder carrier is not strongly coded: its codes `Label.ladderSource` have a diagonal
that is not strongly coded at grade one (`Label.not_isStronglyCoded_ladderSource_diag`).  The
coded replacement `Label.codedLadderSource` is strongly coded
(`Label.isStronglyCoded_codedLadderSource`); the limitation is that of the original ladder only.
Restricted (R2) is proved as `Realization.stronglyCodedResidualReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay` (the bounded strongly coded pinned extension
`StageType.exists_stronglyCoded_pinned_extension_topGrade_le` and a LOW display with the strongly
coded apex); the statements here keep it as an explicit premise.  Restricted (R3) is proved as
`Realization.stronglyCodedHollowReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier` (strongly coded exact growth carriers from
the coded ladder, realized by strongly coded receiving); the statements here keep it as an explicit
premise.  These inputs are the premises, each a named `Prop` here.

Everything here is a native construction of this repository; no correspondence with [AFK26] is
claimed beyond the reading of the conclusion in the class language.  Manuscript maximality, the
relation of this terminality to models, and the spectrum are not addressed.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure

namespace StageType

variable {α : Ordinal.{u}} {k₀ : ℕ}

/-- The **strongly coded pointed age of a rigid core of type `p`**: the members of the pointed age
of a rigid core (`StageType.rigidCoreAge`) with strongly coded rows. -/
def stronglyCodedRigidCoreAge (p : StageType.{u} α k₀) (m : ℕ) (ι : Fin k₀ ↪ Fin m) :
    Set (StageType.{u} α m) :=
  {D | D ∈ rigidCoreAge p m ι ∧ D.rows.IsStronglyCoded}

end StageType

namespace Realization

/-! ### The cover on no points and grade zero, without modelhood -/

section GradeZero

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M}

/-- **The cover on no points** (native construction): in an exactly consistent covering
realization, the empty tuple covers a stage type on no points.  As
`Realization.IsModel.exists_covers_zero`, with the occurrence from covering. -/
theorem exists_covers_zero_of_isCovering (hR : R.IsConsistent) (hc : R.IsCovering) :
    ∃ t : StageType.{u} α 0, R.Covers t ![] := by
  obtain ⟨x⟩ := hc.nonempty_occurrence
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (x.type.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  refine ⟨t, fun i ↦ i.elim0, ?_⟩
  rw [← ht, ← Realization.eval_face hR x]
  congr 1
  ext i
  exact i.elim0

/-- **The empty core without modelhood** (native construction): at a limit stage, for a
realization with legal types, the empty tuple is a globally rigid core exactly when the top-grade
supremum is `0`.  As `Realization.IsModel.isGloballyRigidCore_empty_iff`, which uses only the
legality of the actual types. -/
theorem isGloballyRigidCore_empty_iff_of_hasLegalTypes (hl : R.HasLegalTypes)
    (hα : Order.IsSuccLimit α) : R.IsGloballyRigidCore ![] ↔ R.topGradeSup = 0 := by
  rw [topGradeSup_eq_zero_iff]
  refine ⟨fun h x ↦ ?_, fun h ↦ isGloballyRigidCore_of_forall_isTopFree h _⟩
  refine (StageType.isRigidCoreIn_empty_iff_isTopFree hα (hl _ _ x.eval_tuple)
    Function.Embedding.ofIsEmpty).mp ?_
  exact h x.type x.tuple _ (covers_of_eval _ x.eval_tuple) (funext fun i ↦ i.elim0)

end GradeZero

/-! ### The terminal properties of the strongly coded terminal realizations -/

section Property

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **Grade zero** (native construction): a realization in the strongly coded receiving class at
`λ_ξ` with top-grade supremum `0` has the rigid-core property on no points, for the stage type on
no points (unique, `StageType.eq_of_zero`): the empty tuple covers it and is a globally rigid
core. -/
theorem IsStronglyCodedReceiving.hasTerminalProperty_zero (hR : R.IsStronglyCodedReceiving)
    (h0 : R.topGradeSup = 0) (p : StageType.{0} (blockStage ξ) 0) :
    R.HasTerminalProperty (.inl ⟨0, p⟩) := by
  obtain ⟨q, hq⟩ := exists_covers_zero_of_isCovering hR.isConsistent hR.isCovering
  exact ⟨![], StageType.eq_of_zero q p ▸ hq,
    (isGloballyRigidCore_empty_iff_of_hasLegalTypes hR.hasLegalTypes
      (isSuccLimit_blockStage ξ)).mpr h0⟩

/-- **The residual grade is positive** in the strongly coded receiving class (native
construction): with top-grade supremum `0`, the empty tuple would be a globally rigid core.  As
`Realization.topGradeSup_ne_zero_of_residual`. -/
theorem IsStronglyCodedReceiving.ne_zero_of_residual (hR : R.IsStronglyCodedReceiving) {K : ℕ}
    (h : R.HasTerminalProperty (.inr (.inl K))) : K ≠ 0 := by
  rintro rfl
  obtain ⟨p, hp⟩ := exists_covers_zero_of_isCovering hR.isConsistent hR.isCovering
  exact h.1 ⟨0, p, ![], hp, (isGloballyRigidCore_empty_iff_of_hasLegalTypes hR.hasLegalTypes
    (isSuccLimit_blockStage ξ)).mpr (by exact_mod_cast h.2)⟩

end Property

section SplitTargets

variable (ξ : Ordinal.{0}) (M : Type w)

/-- **Target: the terminal-property split in the strongly coded receiving class**.  A realization
at `λ_ξ` terminal in the class at `ξ` has the hollow property (top-grade supremum `⊤`, and
cover-hollow); or top-grade supremum `0` and the rigid-core property on no points (grade zero); or
a positive natural number `K` as top-grade supremum and a rigid-core property or the residual
property `K`.  The cases are not claimed to be exclusive. -/
def StronglyCodedTerminalSplitTarget : Prop :=
  ∀ R : Realization.{0, w} (blockStage ξ) M, R.IsStronglyCodedTerminalAt ξ →
    R.HasTerminalProperty (.inr (.inr ())) ∨
      (R.topGradeSup = 0 ∧
        ∀ p : StageType.{0} (blockStage ξ) 0, R.HasTerminalProperty (.inl ⟨0, p⟩)) ∨
      ∃ K : ℕ, K ≠ 0 ∧ R.topGradeSup = K ∧
        ((∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k), R.HasTerminalProperty (.inl ⟨k, p⟩)) ∨
          R.HasTerminalProperty (.inr (.inl K)))

/-- **Target: the cover of the strongly coded terminal realizations by the terminal properties**.
Every realization at `λ_ξ` terminal in the strongly coded receiving class at `ξ` has some terminal
property.  For `ξ < ω₁` the properties are countably many (`countable_terminalProperty`); this is
not yet countability up to isomorphism. -/
def StronglyCodedTerminalPropertyTarget : Prop :=
  ∀ R : Realization.{0, w} (blockStage ξ) M, R.IsStronglyCodedTerminalAt ξ →
    ∃ P : TerminalProperty ξ, R.HasTerminalProperty P

end SplitTargets

/-- **Target: the terminal-property split** (native construction).  With top-grade supremum `⊤`,
terminality in the class implies cover-hollowness
(`Realization.IsStronglyCodedTerminalAt.isCoverHollow`); with `0`, grade zero
(`Realization.IsStronglyCodedReceiving.hasTerminalProperty_zero`); otherwise a globally rigid core
exists or not. -/
theorem stronglyCodedTerminalSplitTarget (ξ : Ordinal.{0}) (M : Type w) :
    StronglyCodedTerminalSplitTarget ξ M := by
  intro R ht
  by_cases htop : R.topGradeSup = ⊤
  · exact .inl ⟨ht.isCoverHollow htop, htop⟩
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp htop
  rcases Nat.eq_zero_or_pos K with rfl | hpos
  · have h0 : R.topGradeSup = 0 := by rw [← hK]; rfl
    exact .inr (.inl ⟨h0, ht.1.hasTerminalProperty_zero h0⟩)
  refine .inr (.inr ⟨K, hpos.ne', hK.symm, ?_⟩)
  by_cases hcore : ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
      R.Covers p c ∧ R.IsGloballyRigidCore c
  · obtain ⟨k, p, hp⟩ := hcore
    exact .inl ⟨k, p, hp⟩
  · exact .inr ⟨hcore, hK.symm⟩

/-- **Target: the cover by the terminal properties** (native construction): from the split
(`Realization.stronglyCodedTerminalSplitTarget`). -/
theorem stronglyCodedTerminalPropertyTarget (ξ : Ordinal.{0}) (M : Type w) :
    StronglyCodedTerminalPropertyTarget ξ M := by
  intro R ht
  rcases stronglyCodedTerminalSplitTarget ξ M R ht with h | ⟨-, h⟩ | ⟨K, -, -, ⟨k, p, h⟩ | h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h (exists_covers_zero_of_isCovering ht.1.isConsistent ht.1.isCovering).choose⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

section Assignment

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **A terminal property of a strongly coded terminal realization**, chosen
(`Realization.stronglyCodedTerminalPropertyTarget`).  The choice is not canonical: a realization
may have several properties. -/
noncomputable def stronglyCodedTerminalProperty (ht : R.IsStronglyCodedTerminalAt ξ) :
    TerminalProperty ξ :=
  (stronglyCodedTerminalPropertyTarget ξ M R ht).choose

/-- The chosen property is a terminal property of the realization. -/
theorem hasTerminalProperty_stronglyCodedTerminalProperty (ht : R.IsStronglyCodedTerminalAt ξ) :
    R.HasTerminalProperty (stronglyCodedTerminalProperty ht) :=
  (stronglyCodedTerminalPropertyTarget ξ M R ht).choose_spec

/-- **A strongly coded terminal realization has a restricted terminal property** (native
construction): the cover by the terminal properties and
`Realization.exists_hasRestrictedTerminalProperty_of_hasTerminalProperty`. -/
theorem IsStronglyCodedTerminalAt.exists_hasRestrictedTerminalProperty
    (ht : R.IsStronglyCodedTerminalAt ξ) : ∃ P, R.HasRestrictedTerminalProperty P :=
  exists_hasRestrictedTerminalProperty_of_hasTerminalProperty
    (hasTerminalProperty_stronglyCodedTerminalProperty ht)

end Assignment

/-! ### Exact receiving at a rigid root for strongly coded donors -/

section RigidRoot

variable (α : Ordinal.{u}) (M : Type w)

/-- **Target: exact receiving at a rigid root for strongly coded donors**.  In an exactly
consistent realization at a limit stage with finite-extension receiving for the legal donors with
strongly coded rows, over a cover `c` of `t`, a legal donor `D` with strongly coded rows
restricting to `t` along `g`, in which the root is a rigid core, is the type of a cover extending
`c`.  The premises are those of `Realization.exists_covers_of_isRigidCoreIn`, with receiving
restricted to strongly coded donors and the donor's strong coding added. -/
def StronglyCodedRigidRootTarget : Prop :=
  ∀ R : Realization.{u, w} α M, R.IsConsistent → Order.IsSuccLimit α →
    R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
      ∀ ⦃n m : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ (D : StageType.{u} α m) (g : Fin n ↪ Fin m), D.IsLegal → D.rows.IsStronglyCoded →
          StageType.restrictFace g D = some t → D.IsRigidCoreIn g →
            ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c

end RigidRoot

section RigidRootProofs

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n m k₀ : ℕ}

/-- **Exact receiving at a rigid root for strongly coded donors** (native construction): the
argument of `Realization.exists_covers_of_isRigidCoreIn`, with the donor received through
receiving restricted to strongly coded donors.  The donor is received at a cutoff above all its
labels other than `⊤` (`StageType.exists_lt_forall_label_lt`), and rigidity makes the received type
the donor (`StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn`). -/
theorem exists_covers_of_isRigidCoreIn_of_isStronglyCoded (hR : R.IsConsistent)
    (hα : Order.IsSuccLimit α)
    (hrec : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c) {D : StageType.{u} α m}
    {g : Fin n ↪ Fin m} (hD : D.IsLegal) (hDs : D.rows.IsStronglyCoded)
    (hg : StageType.restrictFace g D = some t) (hrig : D.IsRigidCoreIn g) :
    ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c := by
  obtain ⟨δ, hδα, hδ⟩ := D.exists_lt_forall_label_lt hα
  obtain ⟨u, hu, q, hq, huq⟩ :=
    hrec ⟨c, hc.injective⟩ t hc.eval_eq D g hD hDs hg δ (Label.isPermittedCutoff_coe.mpr hδα)
  have hqg : StageType.restrictFace g q = some t := by
    rw [← hR u q g huq, hu]
    exact hc.eval_eq
  obtain rfl := StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn hD hδ hq hqg hg hrig
  exact ⟨u, covers_of_eval u huq, funext fun i ↦ DFunLike.congr_fun hu i⟩

/-- **Target: exact receiving at a rigid root for strongly coded donors** (native construction):
`Realization.exists_covers_of_isRigidCoreIn_of_isStronglyCoded`. -/
theorem stronglyCodedRigidRootTarget (α : Ordinal.{u}) (M : Type w) :
    StronglyCodedRigidRootTarget α M :=
  fun _ hR hα hrec _ _ _ _ hc _ _ hD hDs hg hrig ↦
    exists_covers_of_isRigidCoreIn_of_isStronglyCoded hR hα hrec hc hD hDs hg hrig

/-- **Exact receiving at a rigid root in the strongly coded receiving class** (native
construction): at the block stage, the class field of receiving gives finite-extension receiving
for strongly coded donors (`Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff`). -/
theorem IsStronglyCodedReceiving.exists_covers_of_isRigidCoreIn {ξ : Ordinal.{u}}
    {R : Realization.{u, w} (blockStage ξ) M} (hR : R.IsStronglyCodedReceiving)
    {t : StageType.{u} (blockStage ξ) n} {c : Fin n → M} (hc : R.Covers t c)
    {D : StageType.{u} (blockStage ξ) m} {g : Fin n ↪ Fin m} (hD : D.IsLegal)
    (hDs : D.rows.IsStronglyCoded) (hg : StageType.restrictFace g D = some t)
    (hrig : D.IsRigidCoreIn g) : ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c :=
  exists_covers_of_isRigidCoreIn_of_isStronglyCoded hR.isConsistent (isSuccLimit_blockStage ξ)
    ((hasFiniteExtensionReceivingIn_isStronglyCoded_iff hR.isConsistent
      (isSuccLimit_blockStage ξ).isSuccPrelimit).mpr hR.receiving) hc hD hDs hg hrig

/-- **Exact receiving within the strongly coded pointed age of a rigid core, at any core**, in the
strongly coded receiving class (native construction): as
`Realization.exactReceivingWithinAt_rigidCoreAge`, a donor in which the core is rigid has the root
rigid too (`StageType.IsRigidCoreIn.mono`). -/
theorem IsStronglyCodedReceiving.exactReceivingWithinAt_stronglyCodedRigidCoreAge
    {ξ : Ordinal.{u}} {R : Realization.{u, w} (blockStage ξ) M} (hR : R.IsStronglyCodedReceiving)
    (x₀ : Fin k₀ → M) (p : StageType.{u} (blockStage ξ) k₀) :
    R.ExactReceivingWithinAt x₀ (StageType.stronglyCodedRigidCoreAge p) :=
  fun _ _ _ _ ι hc _ _ g hD hg ↦
    hR.exists_covers_of_isRigidCoreIn hc hD.1.1 hD.2 hg
      (hD.1.2.2.mono (by rintro _ ⟨i, rfl⟩; exact ⟨ι i, rfl⟩))

/-- **Age inclusion at a globally rigid core in the strongly coded receiving class** (native
construction): as `Realization.IsGloballyRigidCore.mem_rigidCoreAge`, with legality and exact
consistency from the class fields; the actual types are strongly coded by the class field. -/
theorem IsGloballyRigidCore.mem_stronglyCodedRigidCoreAge {p : StageType.{u} α k₀}
    {x₀ : Fin k₀ → M} (hcore : R.IsGloballyRigidCore x₀) (hR : R.IsStronglyCodedReceiving)
    (hc : R.Covers p x₀) {s : Fin m ↪ M} (ι : Fin k₀ ↪ Fin m) {D : StageType.{u} α m}
    (hs : R.eval s = some D) (hsι : ⇑s ∘ ι = x₀) :
    D ∈ StageType.stronglyCodedRigidCoreAge p m ι := by
  refine ⟨StageType.mem_rigidCoreAge.mpr
    ⟨hR.hasLegalTypes s D hs, ?_, hcore D s ι (covers_of_eval s hs) hsι⟩,
    hR.isStronglyCoded s D hs⟩
  rw [← hR.isConsistent s D ι hs, ← hc.eval_eq]
  congr 1
  ext i
  exact congrFun hsι i

end RigidRootProofs

/-! ### Exact one-point receiving, and the restricted (R2) and (R3) -/

section Exact

variable {α : Ordinal.{u}} {M : Type w}

variable (R : Realization.{u, w} α M) in
/-- **Exact one-point receiving of the strongly coded cofaces of top grade at most `K`**: over
every cover `c` of a stage type `t`, the empty cover included, every one-point coface of `t` with
strongly coded rows and top grade at most `K` is the type of `c` extended by one point.  For
`K = ⊤` the bound is no condition. -/
def HasExactStronglyCodedReceiving (K : ℕ∞) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
    ∀ D ∈ t.cofaces, D.rows.IsStronglyCoded → (D.topGrade : ℕ∞) ≤ K →
      ∃ y : M, R.Covers D (Fin.snoc c y)

end Exact

section Premises

variable (ξ : Ordinal.{0}) (M : Type w)

/-- **Restricted (R2), exact residual receiving in the strongly coded receiving class**: a
realization in the class at `λ_ξ` with the residual property `K` has exact one-point receiving of
the strongly coded cofaces of top grade at most `K`.  Proved as
`Realization.stronglyCodedResidualReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`; the statements here keep it as an explicit
premise.  The model-level form is
`Realization.ResidualReceiving`, for models and every coface. -/
def StronglyCodedResidualReceiving : Prop :=
  ∀ (R : Realization.{0, w} (blockStage ξ) M) (K : ℕ), R.IsStronglyCodedReceiving →
    R.HasTerminalProperty (.inr (.inl K)) → R.HasExactStronglyCodedReceiving K

/-- **Restricted (R3), exact hollow-growth receiving in the strongly coded receiving class**: a
realization in the class at `λ_ξ` with the restricted hollow property (cover-hollow without a
globally rigid core, and top-grade supremum `⊤`) has exact one-point receiving of the strongly
coded cofaces.  Proved as `Realization.stronglyCodedHollowReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier`; the statements here keep it as an
explicit premise.  The model-level form is
`Realization.HollowReceiving Realization.IsCoverHollowWithoutRigidCoreAtBlock`, for models and
every coface. -/
def StronglyCodedHollowReceiving : Prop :=
  ∀ R : Realization.{0, w} (blockStage ξ) M, R.IsStronglyCodedReceiving →
    R.HasRestrictedTerminalProperty (.inr (.inr ())) → R.HasExactStronglyCodedReceiving ⊤

end Premises

/-! ### The comparison targets -/

section Comparison

variable (α : Ordinal.{u}) (M N : Type w)

/-- **Target (c): the exact-age comparison without modelhood**.  Let `R` on `M` and `S` on `N` be
exactly consistent covering realizations at a common stage, on countable carriers, with cores `x₀`
and `y₀` covering one stage type `p`.  If every actual type of a cover containing the core at
positions `ι` lies in `A m ι`, in both (age inclusion), and both have exact receiving within `A` at
their cores, then some isomorphism of the realizations carries `x₀` to `y₀`.  The premises are those
of `Realization.exists_equiv_comp_eq_of_exactReceivingWithinAt` with each expansion replaced by
exact consistency and covering; the conclusion is an isomorphism of realizations, not of base
structures.  Proof plan: the matched tuples (`Realization.CoverMatch`) in the relational language
of stage types interpreted by covering, whose atomic agreement follows from exact consistency, and
InfinitaryLogic's countable back-and-forth construction. -/
def ExactAgeIsoTarget : Prop :=
  Countable M → Countable N →
    ∀ (R : Realization.{u, w} α M) (S : Realization.{u, w} α N) (k₀ : ℕ)
      (p : StageType.{u} α k₀) (x₀ : Fin k₀ → M) (y₀ : Fin k₀ → N)
      (A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)),
      R.IsConsistent → R.IsCovering → S.IsConsistent → S.IsCovering →
      (∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
        R.eval s = some D → ⇑s ∘ ι = x₀ → D ∈ A m ι) →
      (∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
        S.eval s = some D → ⇑s ∘ ι = y₀ → D ∈ A m ι) →
      R.ExactReceivingWithinAt x₀ A → S.ExactReceivingWithinAt y₀ A →
      R.Covers p x₀ → S.Covers p y₀ → ∃ i : R.Iso S, ⇑i.1 ∘ x₀ = y₀

/-- **Target (c), the class-language atomic agreement**: in exactly consistent realizations, two
covers of one stage type have the same atomic type in the class language `templateLanguage`, for
the structures of the class readings (`ClassRealization.toStructure` of
`Realization.classReading`).  This replaces `Realization.Covers.sameAtomicType`, which uses
`IsExpansionOf`; with it the back-and-forth of (c) runs in the class language and gives an
isomorphism of class readings only. -/
def ClassReadingAtomicAgreementTarget : Prop :=
  ∀ (R : Realization.{u, w} α M) (S : Realization.{u, w} α N), R.IsConsistent → S.IsConsistent →
    ∀ ⦃k : ℕ⦄ (t : StageType.{u} α k) (x : Fin k → M) (y : Fin k → N), R.Covers t x →
      S.Covers t y →
        letI := R.classReading.toStructure
        letI := S.classReading.toStructure
        SameAtomicType (L := templateLanguage.{u}) x y

/-- **Target (c), the class-language reading of the conclusion**: an isomorphism of realizations
gives an isomorphism, in the class language `templateLanguage`, of the structures of their class
readings. -/
def ClassReadingEquivTarget : Prop :=
  ∀ (R : Realization.{u, w} α M) (S : Realization.{u, w} α N), R.IsIso S →
    letI := R.classReading.toStructure
    letI := S.classReading.toStructure
    Nonempty (M ≃[templateLanguage.{u}] N)

end Comparison

section ClassComparison

variable (ξ : Ordinal.{0}) (M N : Type w)

/-- **Target (b): the rigid-core comparison in the strongly coded receiving class**.  Two
realizations in the class at `λ_ξ` on countable carriers, with globally rigid cores `x₀` and `y₀`
covering one stage type `p`, have an isomorphism of realizations carrying `x₀` to `y₀`.  No premise
beyond the class: the model-level `Realization.exists_equiv_comp_eq_of_isGloballyRigidCore` assumes
(R1), here replaced by the class field of receiving through
`Realization.IsStronglyCodedReceiving.exactReceivingWithinAt_stronglyCodedRigidCoreAge`, with age
inclusion `Realization.IsGloballyRigidCore.mem_stronglyCodedRigidCoreAge`; the remaining input is
(c). -/
def StronglyCodedRigidCoreIsoTarget : Prop :=
  Countable M → Countable N →
    ∀ (R : Realization.{0, w} (blockStage ξ) M) (S : Realization.{0, w} (blockStage ξ) N)
      (k₀ : ℕ) (p : StageType.{0} (blockStage ξ) k₀) (x₀ : Fin k₀ → M) (y₀ : Fin k₀ → N),
      R.IsStronglyCodedReceiving → S.IsStronglyCodedReceiving → R.Covers p x₀ → S.Covers p y₀ →
        R.IsGloballyRigidCore x₀ → S.IsGloballyRigidCore y₀ → ∃ i : R.Iso S, ⇑i.1 ∘ x₀ = y₀

/-- **Target: the exact-growth comparison in the strongly coded receiving class**, the engine of
the residual and hollow comparisons.  Two realizations in the class at `λ_ξ` on countable carriers,
with one top-grade supremum `K` (in `ℕ∞`) and exact one-point receiving of the strongly coded
cofaces of top grade at most `K`, are isomorphic.  Proof plan: the age is that of the legal
strongly coded types of top grade at most `K`, closed under faces; every actual type lies in it
(class fields and `Realization.Occurrence.topGrade_le_topGradeSup`); one point gives many
(`Realization.ExactReceivingWithin.of_one_point`, exact consistency only); the initial match is the
pair of covers on no points (`Realization.exists_covers_zero_of_isCovering`); then (c). -/
def StronglyCodedExactGrowthIsoTarget : Prop :=
  Countable M → Countable N →
    ∀ (R : Realization.{0, w} (blockStage ξ) M) (S : Realization.{0, w} (blockStage ξ) N)
      (K : ℕ∞), R.IsStronglyCodedReceiving → S.IsStronglyCodedReceiving →
      R.topGradeSup = K → S.topGradeSup = K →
      R.HasExactStronglyCodedReceiving K → S.HasExactStronglyCodedReceiving K → R.IsIso S

/-- **Target: the residual comparison in the strongly coded receiving class**, under restricted
(R2) on both carriers (`Realization.StronglyCodedResidualReceiving`): two realizations in the class
at `λ_ξ` on countable carriers with the same residual property `K` are isomorphic.  The model-level
form is `Realization.nonempty_equiv_of_residual`.  Restricted (R2) is proved
(`Realization.stronglyCodedResidualReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`) and kept here as an explicit premise. -/
def StronglyCodedResidualIsoTarget : Prop :=
  StronglyCodedResidualReceiving ξ M → StronglyCodedResidualReceiving ξ N →
    Countable M → Countable N →
    ∀ (R : Realization.{0, w} (blockStage ξ) M) (S : Realization.{0, w} (blockStage ξ) N) (K : ℕ),
      R.IsStronglyCodedReceiving → S.IsStronglyCodedReceiving →
      R.HasTerminalProperty (.inr (.inl K)) → S.HasTerminalProperty (.inr (.inl K)) → R.IsIso S

/-- **Target: the hollow comparison in the strongly coded receiving class**, under restricted (R3)
on both carriers (`Realization.StronglyCodedHollowReceiving`): two realizations in the class at
`λ_ξ` on countable carriers with the restricted hollow property are isomorphic.  The model-level
form is `Realization.nonempty_equiv_of_hollow` for the predicate
`Realization.IsCoverHollowWithoutRigidCoreAtBlock`.  Restricted (R3) is proved
(`Realization.stronglyCodedHollowReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier`) and kept here as an explicit
premise. -/
def StronglyCodedHollowIsoTarget : Prop :=
  StronglyCodedHollowReceiving ξ M → StronglyCodedHollowReceiving ξ N →
    Countable M → Countable N →
    ∀ (R : Realization.{0, w} (blockStage ξ) M) (S : Realization.{0, w} (blockStage ξ) N),
      R.IsStronglyCodedReceiving → S.IsStronglyCodedReceiving →
      R.HasRestrictedTerminalProperty (.inr (.inr ())) →
      S.HasRestrictedTerminalProperty (.inr (.inr ())) → R.IsIso S

/-- **Target: shared restricted terminal properties determine the isomorphism class**, under
restricted (R2) and (R3) on both carriers.  Two realizations at `λ_ξ` on countable carriers,
terminal in the strongly coded receiving class at `ξ`, with a common restricted terminal property,
are isomorphic realizations.  Terminality is not used by the comparisons; it enters through the
cover (`Realization.IsStronglyCodedTerminalAt.exists_hasRestrictedTerminalProperty`).  Restricted
(R2) and (R3) are proved (`Realization.stronglyCodedResidualReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`, and
`Realization.stronglyCodedHollowReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier`) and kept here as explicit premises; the
statement with both instantiated is `Realization.stronglyCodedTerminalIso`, in
`VaughtConjecture.MainTheorem.StronglyCodedTerminalCount`. -/
def StronglyCodedTerminalIsoTarget : Prop :=
  StronglyCodedResidualReceiving ξ M → StronglyCodedResidualReceiving ξ N →
    StronglyCodedHollowReceiving ξ M → StronglyCodedHollowReceiving ξ N →
    Countable M → Countable N →
    ∀ (R : Realization.{0, w} (blockStage ξ) M) (S : Realization.{0, w} (blockStage ξ) N),
      R.IsStronglyCodedTerminalAt ξ → S.IsStronglyCodedTerminalAt ξ →
      ∀ P : TerminalProperty ξ, R.HasRestrictedTerminalProperty P →
        S.HasRestrictedTerminalProperty P → R.IsIso S

end ClassComparison

/-- **Shared restricted terminal properties determine the isomorphism class, from the three
comparisons** (native construction, case analysis on the property): the rigid-core comparison for
`inl ⟨k, p⟩`, the residual comparison for `inr (inl K)` and the hollow comparison for
`inr (inr ())`. -/
theorem stronglyCodedTerminalIsoTarget_of_comparisons {ξ : Ordinal.{0}} {M N : Type w}
    (hrig : StronglyCodedRigidCoreIsoTarget ξ M N) (hres : StronglyCodedResidualIsoTarget ξ M N)
    (hhol : StronglyCodedHollowIsoTarget ξ M N) : StronglyCodedTerminalIsoTarget ξ M N := by
  intro hrM hrN hhM hhN hM hN R S hR hS P hRP hSP
  rcases P with ⟨k, p⟩ | K | ⟨⟩
  · obtain ⟨x₀, hx₀, hcx⟩ := hRP
    obtain ⟨y₀, hy₀, hcy⟩ := hSP
    obtain ⟨i, -⟩ := hrig hM hN R S k p x₀ y₀ hR.1 hS.1 hx₀ hy₀ hcx hcy
    exact ⟨i⟩
  · exact hres hrM hrN hM hN R S K hR.1 hS.1 hRP hSP
  · exact hhol hhM hhN hM hN R S hR.1 hS.1 hRP hSP

/-! ### Countably many isomorphism classes -/

section Count

/-- The **isomorphism classes of realizations on `ℕ` terminal in the strongly coded receiving
class at `ξ`**. -/
def stronglyCodedTerminalClasses (ξ : Ordinal.{0}) :
    Set (Quotient (isoSetoid (blockStage ξ) ℕ)) :=
  {q | ∃ R : Realization.{0, 0} (blockStage ξ) ℕ, Quotient.mk _ R = q ∧
    R.IsStronglyCodedTerminalAt ξ}

/-- **Target: countably many strongly coded terminal isomorphism classes**: for `ξ < ω₁`, under
restricted (R2) and (R3) on `ℕ`, only countably many isomorphism classes of realizations on `ℕ`
are terminal in the strongly coded receiving class at `ξ`.  Restricted (R2) and (R3) are proved
(`Realization.stronglyCodedResidualReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`, and
`Realization.stronglyCodedHollowReceiving`, in
`VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier`) and kept here as explicit premises; the
count with both instantiated is `Realization.stronglyCodedTerminalClasses_countable`, in
`VaughtConjecture.MainTheorem.StronglyCodedTerminalCount`. -/
def StronglyCodedTerminalCountTarget (ξ : Ordinal.{0}) : Prop :=
  ξ < ω₁ → StronglyCodedResidualReceiving ξ ℕ → StronglyCodedHollowReceiving ξ ℕ →
    (stronglyCodedTerminalClasses ξ).Countable

/-- **Countably many strongly coded terminal isomorphism classes, from the comparison** (native
construction): the classes with a given restricted terminal property are a subsingleton by
`Realization.StronglyCodedTerminalIsoTarget`, they cover the terminal classes
(`Realization.IsStronglyCodedTerminalAt.exists_hasRestrictedTerminalProperty`), and the properties
are countably many (`countable_terminalProperty`). -/
theorem stronglyCodedTerminalCountTarget_of_isoTarget {ξ : Ordinal.{0}}
    (h : StronglyCodedTerminalIsoTarget ξ ℕ ℕ) : StronglyCodedTerminalCountTarget ξ := by
  intro hξ hres hhol
  have := countable_terminalProperty hξ
  refine Counting.countable_of_subsingleton_cover
    (fun P ↦ {q | ∃ R : Realization.{0, 0} (blockStage ξ) ℕ, Quotient.mk _ R = q ∧
      R.IsStronglyCodedTerminalAt ξ ∧ R.HasRestrictedTerminalProperty P}) ?_ ?_
  · rintro P _ ⟨R, rfl, hR, hRP⟩ _ ⟨S, rfl, hS, hSP⟩
    exact Quotient.sound (h hres hres hhol hhol inferInstance inferInstance R S hR hS P hRP hSP)
  · rintro _ ⟨R, rfl, hR⟩
    obtain ⟨P, hP⟩ := hR.exists_hasRestrictedTerminalProperty
    exact Set.mem_iUnion.mpr ⟨P, R, rfl, hR, hP⟩

end Count

end Realization

end VaughtConjecture

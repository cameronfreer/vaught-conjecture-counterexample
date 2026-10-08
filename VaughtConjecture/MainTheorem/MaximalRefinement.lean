/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.RefinementCount
import VaughtConjecture.Counting.OrdinalAttainment
import VaughtConjecture.MainTheorem.LowerBound

/-!
# Maximal refinement of a prescribed model, conditionally

Roadmap, the section "Manuscript correspondence (required)", item 5: the Scott route to maximal
presentations and the terminal refinement of a specified higher presentation; Layer 6.

Fix a model `V` at a block stage `λ_β = ω + ω · β` on a countable carrier `X`, and write `B` for
its **base structure**: the structure of the base language on `X` read from the stage reduction
of `V` to `ω`.  An index `η` is **serving** for `B` when `B` has a model expansion to `λ_η`
(`ModelExpansion B (blockStage η)`, in `VaughtConjecture.Realization.Expansion`), and `V` itself
is a model expansion of `B` to `λ_β`.  The **maximal refinement** of `V`
(`exists_maximalRefinement`) is a model `W` at a block stage `λ_ρ`, on the same carrier `X`, with
`β ≤ ρ < ω₁`, such that
* `W` is terminal at `ρ` (`Realization.IsTerminalAt`: no model at `λ_{ρ+1}` reduces to `W`);
* the stage reduction of `W` to `λ_β` is `V`, literally (an equation of realizations on `X`);
* `ρ` is the greatest serving index of `B`: every model on `X` at a block stage `λ_η` whose base
  structure is `B` has `η ≤ ρ`.

Maximality is read literally, for the base structure `B` on `X`; it holds up to isomorphism too,
for model expansions of base structures isomorphic to `B` on any carrier
(`le_of_modelExpansion_of_equiv`, through `ModelExpansion.map`).

**The route.**
1. *An isolating sentence* (`exists_isolates`).  A sentence `σ` **isolates** `B` (`Isolates`)
   when a countable structure of the base language in `Type` satisfies `σ` exactly when it is
   isomorphic to `B`.  The Scott sentence of `B` isolates it (InfinitaryLogic's
   `scottSentence_characterizes`, with the passage from a formula with no free variables to a
   sentence, `Formulaω.realize_as_sentence_iff_toSentenceω`).  Every sentence of `L_{ω₁ω}` has
   countable quantifier rank (`qrank_lt_omega_one`, in `VaughtConjecture.MainTheorem.Spectrum`,
   by induction on the formula; not stated at the pin `e460cb6`).  The bound used below is
   `δ = qrank σ` for the *chosen* isolating sentence `σ`; it is not identified with any Scott
   rank of `B`.
2. *Two classes in every countable domain* (`expansionDomain_nontrivial`).  At a countable `η`,
   the loss `D_η \ D_{η+1}` and the loss `D_{η+1} \ D_{η+2}` are nonempty
   (`nonempty_loss_of_hasApexCoatomExtensions`, in `VaughtConjecture.MainTheorem.LowerBound`), so
   `D_η` contains a class not in `D_{η+1}` and a class in `D_{η+1}`, which are distinct.
3. *A strict bound on serving indices* (`lt_qrank_of_isolates`).  If `B` had a model expansion to
   `λ_η` with `qrank σ ≤ η < ω₁`, every class in `D_η` would agree with `B` on `σ`
   (`Expansion.realize_iff_of_modelExpansions`: two base structures with model expansions to
   `λ_η` agree on the sentences of quantifier rank at most `η`), hence be the class of a structure
   isomorphic to `B`, and `D_η` would be a subsingleton
   (`expansionDomain_subsingleton_of_isolates`), against step 2.  Serving indices are closed
   downward (`ModelExpansion.reduceBlock`), so every serving index of `B` is below `qrank σ`.
4. *An attained greatest serving index* (`exists_isGreatest_servingIndex`).  The serving indices
   contain `β`, are closed downward, are closed at nonzero countable limits
   (`ModelExpansion.nonempty_of_forall_lt`, in `VaughtConjecture.Expansion.Uniqueness`, with the
   coherence of the expansions below the limit derived from next-block uniqueness), and are
   bounded by the countable `qrank σ`; so they have a greatest element `ρ` (bounded-stage
   attainment, `exists_isGreatest_servingIndex_of_le`, for any countable bound, through
   `exists_isGreatest_of_closed`, in `VaughtConjecture.Counting.OrdinalAttainment`).
5. *Terminality and the literal reduct* (`exists_maximalRefinement_of_modelExpansion`).  A model
   expansion `f` of `B` to `λ_ρ` is terminal at `ρ`, since `ρ + 1` is not serving
   (`Realization.IsExpansionOf.isTerminalAt`).  Literal uniqueness of a terminal model expansion
   (`exists_le_reduceBlock_eq_of_isTerminalAt`) then gives that the reduction of `f` to `λ_β` is
   `V`: two model expansions of `B` to `λ_β` are equal, by the injectivity of model reduction in
   its raw form (`ModelExpansion.subsingleton`, from next-block uniqueness).

**Hypotheses.**  The maximal refinement is compiled conditional on the following hypotheses, each
still to be proved except the cap-to-model theorem, forcing donors and the coatom extension property
with apex where listed, which are compiled (`MainTheorem.capToModel`, `forcingDonors_of_blockStage`,
`StageType.hasApexCoatomExtensions_blockStage`):
* `FiniteCutReceiving` ((R1) of the table of Layer 3; `hrec`): the agreement of step 3, through
  finite-extension receiving (`Expansion.FiniteCutReceiving.finiteExtensionReceiving`);
* `NextBlockUniqueness` (next-block uniqueness of models, a consequence of normalization, Layer 4,
  output 2; `hnext`), which gives the injectivity of model reduction in its raw form
  (`ModelExpansion.subsingleton`): the uniqueness of the model expansions of the top-free
  witnesses for the losses of step 2, the closure at limits of step 4, and the literal reduct of
  step 5;
* `HasApexCoatomExtensions` at every countable block stage (Layer 3, 3.1, (R6), compiled as
  `StageType.hasApexCoatomExtensions_blockStage`;
  `hext`): the nonempty losses of step 2, at `qrank σ` and at the next index.
No global termination, no eventual departure for all classes, no countable-slot argument, and no
continuation criterion is used: the bound concerns the one base structure `B`.  The countability
of the carrier is used only for the isolating sentence; `β < ω₁` is not assumed and follows from
`β ≤ ρ` (`Realization.IsModel.lt_omega_one` is not used).  Bounded-stage attainment and literal
uniqueness take next-block uniqueness alone, on any carrier.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization StageType Ordinal

/-! ### An isolating sentence -/

/-- A sentence `σ` of the base language **isolates** the base structure `B` when a countable
structure of the base language in `Type` satisfies `σ` exactly when it is isomorphic to `B`. -/
def Isolates (σ : baseLanguage.{0}.Sentenceω) (B : Type) [baseLanguage.{0}.Structure B] : Prop :=
  ∀ (N : Type) [baseLanguage.{0}.Structure N] [Countable N],
    σ.Realize N ↔ Nonempty (B ≃[baseLanguage.{0}] N)

/-- **A countable base structure has an isolating sentence**: the Scott sentence of `B`, read as a
sentence (InfinitaryLogic's `scottSentence_characterizes`). -/
theorem exists_isolates (B : Type) [baseLanguage.{0}.Structure B] [Countable B] :
    ∃ σ : baseLanguage.{0}.Sentenceω, Isolates σ B :=
  ⟨(scottSentence (L := baseLanguage.{0}) B).toSentenceω, fun N _ _ ↦ by
    rw [← Formulaω.realize_as_sentence_iff_toSentenceω]
    exact scottSentence_characterizes B N⟩

/-! ### Two classes in every countable domain -/

/-- **Every countable expansion domain contains two distinct classes**, under the coatom extension
property with apex at the block stages `λ_η` and `λ_{η+1}` (`hext`, `hext'`; compiled,
`StageType.hasApexCoatomExtensions_blockStage`) and next-block uniqueness of models (`hnext`, still
to be proved): a class in the loss at `η` and a class in
the loss at `η + 1`, which lies in `D_{η+1} ⊆ D_η` (`nonempty_loss_of_hasApexCoatomExtensions`). -/
theorem expansionDomain_nontrivial (hnext : NextBlockUniqueness.{0}) {η : Ordinal.{0}}
    (hη : η < ω₁) (hext : HasApexCoatomExtensions.{0} (blockStage η))
    (hext' : HasApexCoatomExtensions.{0} (blockStage (η + 1))) :
    (expansionDomain η).Nontrivial := by
  have hη' : η + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hη
  obtain ⟨p, hp, hp'⟩ := nonempty_loss_of_hasApexCoatomExtensions hη hext
    fun _ _ _ ↦ ModelExpansion.subsingleton hnext hη
  obtain ⟨p', hp₁, -⟩ := nonempty_loss_of_hasApexCoatomExtensions hη' hext'
    fun _ _ _ ↦ ModelExpansion.subsingleton hnext hη'
  exact ⟨p, hp, p', expansionDomain_antitone (Order.le_succ η) hp₁, fun h ↦ hp' (h ▸ hp₁)⟩

/-! ### A strict bound on serving indices -/

variable {B : Type} [baseLanguage.{0}.Structure B] [Countable B] {σ : baseLanguage.{0}.Sentenceω}

/-- **A domain containing an isolated structure is a subsingleton**, conditional on finite-cut
receiving of models (`hrec`; (R1) of the table of Layer 3, still to be proved): if `σ` isolates
`B`, has quantifier rank at most `η < ω₁`, and `B` has a model expansion to `λ_η`, then every
class in `D_η` agrees with `B` on `σ` (`Expansion.realize_iff_of_modelExpansions`), so its codes
are isomorphic to `B`, and `D_η` has at most one element. -/
theorem expansionDomain_subsingleton_of_isolates (hrec : FiniteCutReceiving.{0})
    (hσ : Isolates σ B) {η : Ordinal.{0}} (hη : η < ω₁) (hqr : σ.qrank ≤ η)
    (hB : Nonempty (ModelExpansion B (blockStage η))) : (expansionDomain η).Subsingleton := by
  have hiso : ∀ c : ModelsOf densitySentence.{0}, Quotient.mk _ c ∈ expansionDomain η →
      Nonempty (@Language.Equiv baseLanguage.{0} B ℕ _ c.1.toStructure) := fun c hc ↦ by
    let := c.1.toStructure
    refine (hσ ℕ).mp ?_
    exact (realize_iff_of_modelExpansions hrec.finiteExtensionReceiving hη hB
      ((mem_expansionDomain_iff c).mp hc) σ hqr).mp ((hσ B).mpr ⟨Language.Equiv.refl _ B⟩)
  intro q hq q' hq'
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  obtain ⟨c', rfl⟩ := Quotient.mk_surjective q'
  obtain ⟨e⟩ := hiso c hq
  obtain ⟨e'⟩ := hiso c' hq'
  exact Quotient.sound (isoSetoid_r_iff.mpr ⟨@Language.Equiv.comp _ ℕ B c.1.toStructure _ ℕ
    c'.1.toStructure e' (@Language.Equiv.symm _ B ℕ _ c.1.toStructure e)⟩)

/-- **No model expansion at or above the rank of an isolating sentence**, conditional on
finite-cut receiving of models (`hrec`), next-block uniqueness of models (`hnext`), and the coatom
extension property with apex at every countable block stage (`hext`; compiled,
`StageType.hasApexCoatomExtensions_blockStage`), the others still to be proved: if
`σ` isolates `B` and `qrank σ ≤ η < ω₁`, then `B` has no model expansion to `λ_η`; otherwise `D_η`
would be a subsingleton (`expansionDomain_subsingleton_of_isolates`) containing two distinct
classes (`expansionDomain_nontrivial`). -/
theorem isEmpty_modelExpansion_of_isolates (hrec : FiniteCutReceiving.{0})
    (hnext : NextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) (hσ : Isolates σ B)
    {η : Ordinal.{0}} (hη : η < ω₁) (hqr : σ.qrank ≤ η) :
    IsEmpty (ModelExpansion B (blockStage η)) := by
  refine not_nonempty_iff.mp fun hB ↦ ?_
  have hη' : η + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hη
  exact (expansionDomain_nontrivial hnext hη (hext η hη) (hext (η + 1) hη')).not_subsingleton
    (expansionDomain_subsingleton_of_isolates hrec hσ hη hqr hB)

/-- **A strict bound on serving indices**: every serving index of `B` is below the quantifier rank
of an isolating sentence `σ`, conditional on finite-cut receiving of models (`hrec`), next-block
uniqueness of models (`hnext`), and the coatom extension property with apex at every countable block
stage (`hext`; compiled, `StageType.hasApexCoatomExtensions_blockStage`), the others still to be
proved.  A model expansion to `λ_η` with `qrank σ ≤ η`
reduces to one at `λ_{qrank σ}` (`ModelExpansion.reduceBlock`), which does not exist
(`isEmpty_modelExpansion_of_isolates`). -/
theorem lt_qrank_of_isolates (hrec : FiniteCutReceiving.{0}) (hnext : NextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) (hσ : Isolates σ B)
    {η : Ordinal.{0}} (h : Nonempty (ModelExpansion B (blockStage η))) : η < σ.qrank := by
  refine lt_of_not_ge fun hle ↦ ?_
  obtain ⟨e⟩ := h
  exact (isEmpty_modelExpansion_of_isolates hrec hnext hext hσ (qrank_lt_omega_one σ)
    le_rfl).false (e.reduceBlock hle)

/-! ### Bounded-stage attainment and literal uniqueness -/

omit [Countable B] in
/-- **Bounded-stage attainment**, conditional on next-block uniqueness of models (`hnext`, still
to be proved): if `B` has a model expansion to `λ_β` and every serving index of `B` is at most a
countable `δ`, the serving indices have a greatest element `ρ`, with `β ≤ ρ ≤ δ`.  The serving
indices are closed downward (`ModelExpansion.reduceBlock`) and closed at nonzero countable limits
(`ModelExpansion.nonempty_of_forall_lt`, by `hnext`), and `exists_isGreatest_of_closed` applies.
The carrier need not be countable. -/
theorem exists_isGreatest_servingIndex_of_le (hnext : NextBlockUniqueness.{0})
    {β δ : Ordinal.{0}} (e : ModelExpansion B (blockStage β))
    (hb : ∀ η, Nonempty (ModelExpansion B (blockStage η)) → η ≤ δ) (hδ : δ < ω₁) :
    ∃ ρ, IsGreatest {η | Nonempty (ModelExpansion B (blockStage η))} ρ ∧ β ≤ ρ ∧ ρ ≤ δ := by
  obtain ⟨ρ, hρ, hβρ, hρδ⟩ := exists_isGreatest_of_closed (P := fun η ↦
      Nonempty (ModelExpansion B (blockStage η))) ⟨e⟩
    (fun _ _ hab ⟨f⟩ ↦ ⟨f.reduceBlock hab⟩)
    (fun _ hl hlω h ↦ ModelExpansion.nonempty_of_forall_lt hnext hl hlω h)
    (fun η h ↦ Order.lt_add_one_iff.mpr (hb η h)) ((Cardinal.isSuccLimit_omega 1).add_one_lt hδ)
  exact ⟨ρ, hρ, hβρ, Order.lt_add_one_iff.mp hρδ⟩

omit [Countable B] in
/-- **Literal uniqueness of a terminal model expansion**, conditional on next-block uniqueness of
models (`hnext`, still to be proved): if `f` is a model expansion of `B` to `λ_ρ`, `ρ < ω₁`,
terminal at `ρ`, then every model expansion `e` of `B` to a block stage `λ_η` has `η ≤ ρ` and is
the stage reduction of `f`.  The inequality is terminal collision: for `ρ < η`, the reduction of
`e` to `λ_{ρ+1}` is a model whose reduction to `λ_ρ` is a model expansion of `B`, hence `f`
(`ModelExpansion.subsingleton` at `ρ`), against terminality; the equality is
`ModelExpansion.subsingleton` at `η`.  The carrier need not be countable. -/
theorem exists_le_reduceBlock_eq_of_isTerminalAt (hnext : NextBlockUniqueness.{0})
    {ρ η : Ordinal.{0}} (hρ : ρ < ω₁) (f : ModelExpansion B (blockStage ρ))
    (hf : f.1.IsTerminalAt ρ) (e : ModelExpansion B (blockStage η)) :
    ∃ h : η ≤ ρ, f.reduceBlock h = e :=
  ModelExpansion.exists_le_reduceBlock_eq_of_isTerminalAt hnext hρ f hf e

/-! ### The greatest serving index and the maximal refinement -/

/-- **An attained greatest serving index**: if `B` has a model expansion to `λ_β`, its serving
indices have a greatest element `ρ`, with `β ≤ ρ < ω₁`, conditional on finite-cut receiving of
models (`hrec`), next-block uniqueness of models (`hnext`), and the coatom extension property with
apex at every countable block stage (`hext`; compiled,
`StageType.hasApexCoatomExtensions_blockStage`), the others still to be proved.  The serving indices
are
bounded by the quantifier rank of an isolating sentence (`lt_qrank_of_isolates`), which is
countable (`qrank_lt_omega_one`), and bounded-stage attainment applies
(`exists_isGreatest_servingIndex_of_le`). -/
theorem exists_isGreatest_servingIndex (hrec : FiniteCutReceiving.{0})
    (hnext : NextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) {β : Ordinal.{0}}
    (e : ModelExpansion B (blockStage β)) :
    ∃ ρ, IsGreatest {η | Nonempty (ModelExpansion B (blockStage η))} ρ ∧ β ≤ ρ ∧ ρ < ω₁ := by
  obtain ⟨σ, hσ⟩ := exists_isolates B
  obtain ⟨ρ, hρ, hβρ, hρσ⟩ := exists_isGreatest_servingIndex_of_le hnext e
    (fun _ h ↦ (lt_qrank_of_isolates hrec hnext hext hσ h).le) (qrank_lt_omega_one σ)
  exact ⟨ρ, hρ, hβρ, hρσ.trans_lt (qrank_lt_omega_one σ)⟩

/-- **Maximal refinement of a model expansion**: a model expansion `e` of `B` to `λ_β` is the
stage reduction of a model expansion `f` of `B` to `λ_ρ`, with `β ≤ ρ < ω₁`, that is terminal at
`ρ`, and `ρ` is the greatest serving index of `B`.  Conditional on finite-cut receiving of models
(`hrec`), next-block uniqueness of models (`hnext`), and the coatom extension property with apex at
every countable block stage (`hext`; compiled, `StageType.hasApexCoatomExtensions_blockStage`), the
others still to be proved.  Terminality: `ρ + 1` is not
serving (`Realization.IsExpansionOf.isTerminalAt`); the literal reduct: literal uniqueness of a
terminal model expansion (`exists_le_reduceBlock_eq_of_isTerminalAt`, by `hnext`). -/
theorem exists_maximalRefinement_of_modelExpansion (hrec : FiniteCutReceiving.{0})
    (hnext : NextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) {β : Ordinal.{0}}
    (e : ModelExpansion B (blockStage β)) :
    ∃ ρ, β ≤ ρ ∧ ρ < ω₁ ∧ ∃ f : ModelExpansion B (blockStage ρ), f.1.IsTerminalAt ρ ∧
      f.1.reduce (isSuccPrelimit_blockStage β) = e.1 ∧
      ∀ η, Nonempty (ModelExpansion B (blockStage η)) → η ≤ ρ := by
  obtain ⟨ρ, ⟨⟨f⟩, hmax⟩, -, hρ⟩ := exists_isGreatest_servingIndex hrec hnext hext e
  have hterm : f.1.IsTerminalAt ρ := f.2.isTerminalAt <| not_nonempty_iff.mp fun h ↦
    (Order.lt_add_one_iff.mpr le_rfl).not_ge (hmax h)
  obtain ⟨h, hfe⟩ := exists_le_reduceBlock_eq_of_isTerminalAt hnext hρ f hterm e
  exact ⟨ρ, h, hρ, f, hterm, congrArg Subtype.val hfe, fun _ h ↦ hmax h⟩

omit [Countable B] in
/-- **Maximality up to isomorphism**: if every serving index of `B` is at most `ρ`, then every
model expansion, to a block stage `λ_η`, of a base structure isomorphic to `B`, on any carrier,
has `η ≤ ρ`: it is carried back to a model expansion of `B` (`ModelExpansion.map`). -/
theorem le_of_modelExpansion_of_equiv {ρ η : Ordinal.{0}}
    (hmax : ∀ η, Nonempty (ModelExpansion B (blockStage η)) → η ≤ ρ) {N : Type*}
    [baseLanguage.{0}.Structure N] (i : B ≃[baseLanguage.{0}] N)
    (g : ModelExpansion N (blockStage η)) : η ≤ ρ :=
  hmax η ⟨g.map i.symm⟩

/-- **Maximal refinement of a prescribed model**: a model `V` at a block stage `λ_β` on a
countable carrier `X` is the stage reduction, literally, of a model `W` at a block stage `λ_ρ` on
the same carrier, with `β ≤ ρ < ω₁`, that is terminal at `ρ` and maximal: every model on `X` at a
block stage `λ_η` with the base structure of `V` has `η ≤ ρ`.

Compiled conditional on the following hypotheses, each still to be proved except the cap-to-model
theorem, forcing donors and the coatom extension property with apex where listed, which are compiled
(`MainTheorem.capToModel`, `forcingDonors_of_blockStage`,
`StageType.hasApexCoatomExtensions_blockStage`):
* finite-cut receiving of models (`hrec`; `FiniteCutReceiving`, (R1) of the table of Layer 3):
  the agreement of the classes of a countable domain on an isolating sentence;
* next-block uniqueness of models (`hnext`; `NextBlockUniqueness`, Layer 4, output 2), which
  gives the injectivity of model reduction (`ModelExpansion.subsingleton`): the losses, the
  closure of the serving indices at limits, and the literal reduct;
* the coatom extension property with apex at every countable block stage (`hext`;
  `HasApexCoatomExtensions`, Layer 3, 3.1): two classes in each countable domain.
The bound on `ρ` is the quantifier rank of a chosen isolating sentence of the base structure of
`V`, its Scott sentence, not a Scott rank; no global termination is used. -/
theorem exists_maximalRefinement (hrec : FiniteCutReceiving.{0}) (hnext : NextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) {X : Type} [Countable X]
    {β : Ordinal.{0}} {V : Realization.{0, 0} (blockStage β) X} (hV : V.IsModel) :
    ∃ ρ, β ≤ ρ ∧ ρ < ω₁ ∧ ∃ W : Realization.{0, 0} (blockStage ρ) X, W.IsModel ∧
      W.IsTerminalAt ρ ∧ W.reduce (isSuccPrelimit_blockStage β) = V ∧
      ∀ (η : Ordinal.{0}) (W' : Realization.{0, 0} (blockStage η) X), W'.IsModel →
        (W'.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure =
          (V.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure → η ≤ ρ := by
  let := (V.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  obtain ⟨ρ, hβρ, hρ, f, hterm, hred, hmax⟩ :=
    exists_maximalRefinement_of_modelExpansion hrec hnext hext (B := X) ⟨V, hV, rfl⟩
  exact ⟨ρ, hβρ, hρ, f.1, f.2.isModel, hterm, hred,
    fun η W' hW' h ↦ hmax η ⟨⟨W', hW', h⟩⟩⟩

end VaughtConjecture.MainTheorem

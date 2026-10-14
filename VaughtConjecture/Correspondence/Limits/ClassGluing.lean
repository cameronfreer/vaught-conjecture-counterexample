/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Reconstruction.Reconstruction
import VaughtConjecture.Realization.ReceivingLimit

/-!
# Coherent limits of class realizations: conditional gluing for Limits

Numbering as in the current draft of [AFK26].  Write `λ_ξ = blockStage ξ = ω + ω · ξ`.

**What this file is, and what it is not.**  It proves a *conditional* gluing ingredient for the
Limits clause of [AFK26, Proposition 4.34]: at a nonzero limit `δ`, a family of class
realizations at the stages `λ_ξ`, `ξ < δ`, that is coherent under stage reduction, well-formed,
and has donor density, has a limit class realization at `λ_δ` reducing to every member, which is
well-formed and has donor density at every permitted cutoff at `λ_δ` (`classGluingTarget`).
Coherence is a **hypothesis** here (`CoherentClassFamily.coherent`).  This is not the Limits
conclusion of [AFK26, Proposition 4.34]: in the final assembly, coherence of the lower lifts must
be derived from lifts that exist on their own (after Reconstruction and the projection target
B.T9), and must not be kept as an extra hypothesis.  No modelhood, no unrestricted receiving, and
no correspondence between models and the printed classes is assumed or used.

**Classes, not positions** (native construction).  The members of the family are class
realizations (`ClassRealization`): each tuple carries a class of stage types up to cell renaming
(`TemplateClass`).  Coherence is an equality of class realizations,
`(S ζ).reduce _ = S ξ` for `ξ < ζ < δ`, so at each tuple the renaming witnessing it is chosen at
that pair of stages; representatives of the classes may vary by renaming from stage to stage, and
no coherent positional presentation across the stages is assumed or constructed.

## The targets and their proofs

Each target is stated as a proposition, every premise visible, and proved below.

* **Coherent families of classes** (`TemplateClass.IsCoherentFamily c`, for
  `c : ∀ ξ < δ, TemplateClass (λ_ξ) n`): `(c ζ).reduce _ = c ξ` for `ξ < ζ < δ`; the class form,
  at one tuple, of the coherence of `CoherentClassFamily`.
* **Stabilization of a coherent family of classes** (`ClassStabilizationTarget δ n`, proved as
  `classStabilizationTarget`): for a limit `δ`, every coherent family of classes below `δ` is
  eventually constant up to the reading of the stage: some `ξ₀ < δ` has `c ξ = (c ξ₀).castLE _`
  for every `ξ₀ ≤ ξ < δ`.  It is the class analogue of `StageType.IsCoherentFamily.eq_castLE`,
  whose proof tracks the cell at a fixed position across the stages, which a class does not have.
  The class proof counts instead the cells labelled by the formal top (`TemplateClass.topCount`):
  the count is invariant under renaming, can only grow under stage reduction (reduction sends a
  label to the formal top or keeps it), and so, along a coherent family, does not grow with the
  index; at an index `ξ₀` where it is least, every member from `ξ₀` on has the count of its
  reduction to `λ_ξ₀`, so it has no label at or above `λ_ξ₀` other than the formal top, and it is
  its reduction to `λ_ξ₀` read back at its own stage (`TemplateClass.castLE_reduce_of_topCount_le`).
* **Descent of a class at `λ_δ`** (`ClassDescentTarget δ n`, proved as `classDescentTarget`): for
  a limit `δ`, every class at `λ_δ` is, from some `ξ₀ < δ` on, its reduction to `λ_ξ` read back at
  `λ_δ`: a representative has finitely many labels, all at some stage `λ_ξ₀`, `ξ₀ < δ`
  (`Label.exists_lt_forall_atStage_blockStage`, from Reconstruction).
* **Gluing of a coherent family of classes** (`ClassFamilyGluingTarget δ n`, proved as
  `classFamilyGluingTarget`): for a limit `δ`, every coherent family of classes below `δ` has a
  class at `λ_δ` reducing to each member: the stabilized class read at `λ_δ`.  The class analogue
  of `StageType.IsCoherentFamily.glue_reduce`.
* **Observation along stage reduction** (`ObservesAtReduceTarget α β n`, proved as
  `observesAtReduceTarget`): for a cutoff `x ≤ β`, the reduction of `q` to `β` observes the
  reduction of `D` at `x` exactly when `q` observes `D` at `x` (`TemplateClass.ObservesAt`); the
  class form of `StageType.reduce_mem_receivingFamily_reduce_iff`, since renaming commutes with
  reduction.
* **The gluing target** (`ClassGluingTarget δ M`, proved as `classGluingTarget`): for a limit
  `δ < ω₁`, every `CoherentClassFamily δ M` has a class realization `T` at `λ_δ` with
  `T.reduce _ = S.family ξ _` for every `ξ < δ`, `T.IsWellFormed`, and donor density of `T` at
  every permitted cutoff at `λ_δ`.  The limit (`CoherentClassFamily.limit`) types a tuple when it
  is typed at every earlier block stage, by the glued class of its classes.  Consistency is by
  separation of classes at `λ_δ` (`TemplateClass.eq_of_forall_reduce_blockStage_eq`, from
  Reconstruction), since reduction commutes with face maps; covering is from the member at `λ_0`;
  legality is invariant under reduction.

**The cutoffs** (native construction).  `ClassRealization.HasDonorDensity` at a stage `α`
quantifies over every permitted cutoff at `α`, that is every label `x` with `⊥ < x < α`
(`Label.IsPermittedCutoff`): the bottom label `⊥` is excluded, while the ordinal `0`, a label
distinct from `⊥`, is included.  At `α = λ_δ` these are the ordinal cutoffs `γ < λ_δ`, including
zero; neither `λ_δ` nor the formal top is permitted.  The target states the cutoff quantifier
explicitly, through `ClassRealization.HasDonorDensityAt` (donor density at one cutoff), and
`hasDonorDensity_iff_forall_hasDonorDensityAt` identifies the conjunction over the permitted
cutoffs with `HasDonorDensity`.  For a permitted cutoff `x < λ_δ` the proof chooses an earlier
block stage `λ_ξ`, `ξ < δ`, strictly above `x` (`Label.exists_lt_blockStage_of_lt`), reduces the
donor `D` and the root class to `λ_ξ` (the face of the reduced donor is the reduced root,
`TemplateClass.restrictFace_reduce`), applies donor density of the member at `ξ` at the cutoff
`x`, which is permitted there, and returns the observation to `λ_δ` through
`observesAtReduceTarget` (`x ≤ λ_ξ`).

**Premises.**  The premise `δ < ω₁` of `ClassGluingTarget` records the countable range of
[AFK26, Proposition 4.34]; the proof does not use it.  No countability or nonemptiness of the
carrier is assumed.

**Shared declarations.**  Separation of classes and of class realizations at `λ_δ`, and the
finitely-many-labels lemma, are those of Reconstruction
(`VaughtConjecture.Correspondence.Reconstruction.Reconstruction`); they are used here, not
proved again.

## Placement

Conditional gluing for Limits (roadmap, Layer 4).
-/


universe u v

namespace VaughtConjecture

open Ordinal

noncomputable section

/-! ### Donor density at one cutoff -/

namespace ClassRealization

variable {α : Ordinal.{u}} {M : Type v} (R : ClassRealization.{u, v} α M)

/-- **Donor density at a cutoff `x`** (native construction): `ClassRealization.HasDonorDensity`
with the cutoff fixed.  For every typed tuple `t` of class `p`, every strongly coded legal class
`D` at the stage `α` on `m` points whose face along `g : Fin n ↪ Fin m` is `p` (`n = 0`
included), some injective tuple `u` extends `t` along `g` literally and has a class `q` with the
observation of `D` at `x` up to renaming.  Native construction. -/
def HasDonorDensityAt (x : Label.{u}) : Prop :=
  ∀ ⦃n m : ℕ⦄ (t : Fin n ↪ M) (p : TemplateClass.{u} α n), R.eval t = some p →
    ∀ (D : TemplateClass.{u} α m) (g : Fin n ↪ Fin m), D.IsStronglyCodedLegal →
      D.restrictFace g = some p →
        ∃ u : Fin m ↪ M, g.trans u = t ∧ ∃ q, R.eval u = some q ∧ q.ObservesAt x D

/-- **Donor density is donor density at every permitted cutoff** (`⊥ < x < α`).
Native construction. -/
theorem hasDonorDensity_iff_forall_hasDonorDensityAt :
    R.HasDonorDensity ↔ ∀ x : Label.{u}, Label.IsPermittedCutoff α x → R.HasDonorDensityAt x :=
  ⟨fun h _ hx _ _ t p hp D g hD hDg ↦ h t p hp D g hD hDg _ hx,
    fun h _ _ t p hp D g hD hDg _ hx ↦ h _ hx t p hp D g hD hDg⟩

end ClassRealization

/-! ### Coherent families -/

namespace TemplateClass

variable {δ : Ordinal.{u}} {n : ℕ}

/-- A family of classes at the block stages below `δ` is a **coherent family** when the class at
`ζ` reduces to the class at every `ξ < ζ`.  An equality of classes: the renaming witnessing it is
chosen for each pair of stages.  Native construction. -/
def IsCoherentFamily (c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n) : Prop :=
  ∀ ξ (hξ : ξ < δ) ζ (hζ : ζ < δ), ξ < ζ →
    (c ζ hζ).reduce (isSuccPrelimit_blockStage ξ) = c ξ hξ

end TemplateClass

/-- **A coherent family of class realizations** below `δ` on `M` (native construction): class
realizations at the block stages `λ_ξ`, `ξ < δ`, with explicit coherence under stage reduction
(an equality of class realizations, so renamings of representatives are absorbed tuple by
tuple), each well-formed and with donor density.  Coherence is a hypothesis of every statement
that uses this structure; nothing here derives it.  Native construction. -/
structure CoherentClassFamily (δ : Ordinal.{u}) (M : Type v) where
  /-- The class realization at the block stage `λ_ξ`. -/
  family : ∀ ξ < δ, ClassRealization.{u, v} (blockStage ξ) M
  /-- Coherence: the member at `ζ` reduces to the member at every `ξ < ζ`. -/
  coherent : ∀ ξ (hξ : ξ < δ) ζ (hζ : ζ < δ), ξ < ζ →
    (family ζ hζ).reduce (isSuccPrelimit_blockStage ξ) = family ξ hξ
  /-- Every member is well-formed. -/
  isWellFormed : ∀ ξ (hξ : ξ < δ), (family ξ hξ).IsWellFormed
  /-- Every member has donor density, at every permitted cutoff at its own stage. -/
  hasDonorDensity : ∀ ξ (hξ : ξ < δ), (family ξ hξ).HasDonorDensity

/-! ### The targets -/

/-- **Target: stabilization of a coherent family of classes** (native construction): for a limit
`δ`, every coherent family of classes on `n` points at the block stages below `δ` is eventually
constant up to the reading of the stage: some `ξ₀ < δ` has `c ξ = (c ξ₀).castLE _` for every
`ξ₀ ≤ ξ < δ`.  The class analogue of `StageType.IsCoherentFamily.eq_castLE`, without a cell
position tracked across the stages. -/
def ClassStabilizationTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n,
    TemplateClass.IsCoherentFamily c → ∃ ξ₀, ∃ h₀ : ξ₀ < δ, ∀ ξ (hξ : ξ < δ) (h : ξ₀ ≤ ξ),
      c ξ hξ = (c ξ₀ h₀).castLE (blockStage_mono h)

/-- **Target: descent of a class at a limit block stage** (native construction): for a limit `δ`,
every class `c` on `n` points at `λ_δ` has some `ξ₀ < δ` such that, for every `ξ₀ ≤ ξ < δ`, the
reduction of `c` to `λ_ξ`, read back at `λ_δ`, is `c`. -/
def ClassDescentTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c : TemplateClass.{u} (blockStage δ) n, ∃ ξ₀ < δ,
    ∀ ξ (hξ : ξ < δ), ξ₀ ≤ ξ →
      (c.reduce (isSuccPrelimit_blockStage ξ)).castLE (blockStage_strictMono hξ).le = c

/-- **Target: gluing a coherent family of classes** (native construction): for a limit `δ`,
every coherent family of classes on `n` points at the block stages below `δ` has a class at
`λ_δ` whose reduction to every `λ_ξ`, `ξ < δ`, is the member at `ξ`.  The class analogue of
`StageType.IsCoherentFamily.glue_reduce`. -/
def ClassFamilyGluingTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n,
    TemplateClass.IsCoherentFamily c → ∃ d : TemplateClass.{u} (blockStage δ) n,
      ∀ ξ (hξ : ξ < δ), d.reduce (isSuccPrelimit_blockStage ξ) = c ξ hξ

/-- **Target: observation along stage reduction** (native construction): for a stage `β` that is
zero or a limit and a cutoff `x ≤ β`, the reduction of `q` to `β` observes the reduction of `D`
at `x` exactly when `q` observes `D` at `x`.  The class form of
`StageType.reduce_mem_receivingFamily_reduce_iff`. -/
def ObservesAtReduceTarget (α β : Ordinal.{u}) (n : ℕ) : Prop :=
  ∀ (hβ : Order.IsSuccPrelimit β) (q D : TemplateClass.{u} α n) (x : Label.{u}), x ≤ β →
    ((q.reduce hβ).ObservesAt x (D.reduce hβ) ↔ q.ObservesAt x D)

/-- **Target: the coherent limit of class realizations** (native construction, conditional on
coherence): for a limit `δ < ω₁`, every coherent family `S` of well-formed class realizations
with donor density at the block stages below `δ` has a class realization `T` at `λ_δ` with

* `T.reduce _ = S.family ξ _` for every `ξ < δ` (equality of class realizations);
* `T.IsWellFormed`;
* donor density of `T` at every permitted cutoff `x` at `λ_δ` (`⊥ < x < λ_δ`, the cutoffs below
  the block stage `λ_δ`), which is `T.HasDonorDensity`
  (`ClassRealization.hasDonorDensity_iff_forall_hasDonorDensityAt`).

Coherence of the family is a premise, not a conclusion; this is not the limit conclusion of
[AFK26, Proposition 4.34], whose assembly must derive the coherence.  The premise `δ < ω₁` is the
countable range of [AFK26, Proposition 4.34]. -/
def ClassGluingTarget (δ : Ordinal.{u}) (M : Type v) : Prop :=
  Order.IsSuccLimit δ → δ < ω₁ → ∀ S : CoherentClassFamily.{u, v} δ M,
    ∃ T : ClassRealization.{u, v} (blockStage δ) M,
      (∀ ξ (hξ : ξ < δ), T.reduce (isSuccPrelimit_blockStage ξ) = S.family ξ hξ) ∧
        T.IsWellFormed ∧
          ∀ x : Label.{u}, Label.IsPermittedCutoff (blockStage δ) x → T.HasDonorDensityAt x

/-! ### Cells labelled by the formal top -/

namespace StageType

variable {α β : Ordinal.{u}} {n : ℕ}

/-- **The number of cells labelled by the formal top.**  Native construction. -/
def topCount (t : StageType.{u} α n) : ℕ :=
  (Finset.univ.filter fun i : Fin t.card ↦ t.label i = ⊤).card

/-- The number of top-labelled cells is invariant under renaming.  Native construction. -/
theorem topCount_renameCells (t : StageType.{u} α n) {k : ℕ} (σ : Fin k ≃ Fin t.card) :
    (t.renameCells σ).topCount = t.topCount :=
  Finset.card_equiv σ fun _ ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl

/-- The top-labelled cells of the reduction, indexed by the cells of `t`.  Native construction. -/
private theorem topCount_reduce (hβ : Order.IsSuccPrelimit β) (t : StageType.{u} α n) :
    (t.reduce hβ).topCount =
      (Finset.univ.filter fun i : Fin t.card ↦ Label.reduce β (t.label i) = ⊤).card :=
  rfl

/-- The top-labelled cells of `t` are top-labelled in its reduction.  Native construction. -/
private theorem filter_top_subset_reduce (t : StageType.{u} α n) :
    (Finset.univ.filter fun i : Fin t.card ↦ t.label i = ⊤) ⊆
      Finset.univ.filter fun i : Fin t.card ↦ Label.reduce β (t.label i) = ⊤ :=
  fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [(Finset.mem_filter.mp hi).2, Label.reduce_top]⟩

/-- Stage reduction does not lower the number of top-labelled cells.  Native construction. -/
theorem topCount_le_topCount_reduce (hβ : Order.IsSuccPrelimit β) (t : StageType.{u} α n) :
    t.topCount ≤ (t.reduce hβ).topCount := by
  rw [topCount_reduce]
  exact Finset.card_le_card (filter_top_subset_reduce t)

/-- **No new top-labelled cell under reduction**: if the reduction of `t` to `β` has no more
top-labelled cells than `t`, every label of `t` is at stage `β`.  Native construction. -/
theorem atStage_of_topCount_reduce_le (hβ : Order.IsSuccPrelimit β) (t : StageType.{u} α n)
    (h : (t.reduce hβ).topCount ≤ t.topCount) (i : Fin t.card) : Label.AtStage β (t.label i) := by
  by_contra hi
  have hne : t.label i ≠ ⊤ := fun h' ↦ hi (.inr h')
  have hle : (β : Label.{u}) ≤ t.label i := not_lt.mp fun h' ↦ hi (.inl h')
  rw [topCount_reduce] at h
  exact absurd h (not_le.mpr (Finset.card_lt_card ((Finset.ssubset_iff_of_subset
    (filter_top_subset_reduce t)).mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Label.reduce_of_le hle⟩, fun hi' ↦ hne (Finset.mem_filter.mp hi').2⟩)))

end StageType

namespace TemplateClass

variable {α β : Ordinal.{u}} {n : ℕ}

/-- **The number of cells labelled by the formal top** of a class (`StageType.topCount` of any
representative).  Native construction. -/
def topCount (c : TemplateClass.{u} α n) : ℕ :=
  Quotient.lift StageType.topCount (fun a _ h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact (a.topCount_renameCells σ).symm) c

@[simp] theorem topCount_toClass (t : StageType.{u} α n) : t.toClass.topCount = t.topCount :=
  rfl

/-- Stage reduction of classes does not lower the number of top-labelled cells.
Native construction. -/
theorem topCount_le_topCount_reduce (hβ : Order.IsSuccPrelimit β) (c : TemplateClass.{u} α n) :
    c.topCount ≤ (c.reduce hβ).topCount :=
  Quotient.inductionOn c fun t ↦ t.topCount_le_topCount_reduce hβ

/-- **A class with no new top-labelled cell under reduction is its reduction read back**: for
`β ≤ α`, if the reduction of `c` to `β` has no more top-labelled cells than `c`, then `c` is its
reduction to `β`, read at `α`.  Native construction. -/
theorem castLE_reduce_of_topCount_le (hβ : Order.IsSuccPrelimit β) (hβα : β ≤ α)
    (c : TemplateClass.{u} α n) (h : (c.reduce hβ).topCount ≤ c.topCount) :
    (c.reduce hβ).castLE hβα = c := by
  induction c using Quotient.inductionOn with
  | h t =>
    exact congrArg StageType.toClass
      (t.castLE_reduce_of_atStage hβ hβα (t.atStage_of_topCount_reduce_le hβ h))

/-- Reduction of classes does not see the stage at which a class is read.  Native construction. -/
theorem reduce_castLE (h : α ≤ β) {γ : Ordinal.{u}} (hγ : Order.IsSuccPrelimit γ)
    (c : TemplateClass.{u} α n) : (c.castLE h).reduce hγ = c.reduce hγ :=
  Quotient.inductionOn c fun _ ↦ rfl

/-- Reduction of a class to a larger stage only reads it at that stage.  Native construction. -/
theorem reduce_eq_castLE (hβ : Order.IsSuccPrelimit β) (h : α ≤ β) (c : TemplateClass.{u} α n) :
    c.reduce hβ = c.castLE h :=
  Quotient.inductionOn c fun t ↦ congrArg StageType.toClass (t.reduce_eq_castLE hβ h)

variable {δ : Ordinal.{u}} {c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n}

/-- In a coherent family of classes, the class at `ζ` reduces to the class at every `ξ ≤ ζ`.
Native construction. -/
theorem IsCoherentFamily.reduce_eq_of_le (hc : IsCoherentFamily c) {ξ ζ : Ordinal.{u}}
    (hξ : ξ < δ) (hζ : ζ < δ) (h : ξ ≤ ζ) :
    (c ζ hζ).reduce (isSuccPrelimit_blockStage ξ) = c ξ hξ := by
  rcases h.lt_or_eq with h | rfl
  · exact hc ξ hξ ζ hζ h
  · exact reduce_self _ _

/-- **Separation of optional classes at a limit block stage**, by the separation of classes of
Reconstruction (`TemplateClass.eq_of_forall_reduce_blockStage_eq`).  Native construction. -/
private theorem option_eq_of_forall_map_reduce_eq (hδ : Order.IsSuccLimit δ)
    {a b : Option (TemplateClass.{u} (blockStage δ) n)}
    (h : ∀ ξ < δ, a.map (reduce (isSuccPrelimit_blockStage ξ)) =
      b.map (reduce (isSuccPrelimit_blockStage ξ))) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some _ => simpa using h 0 hδ.pos
  | some p => cases b with
    | none => simpa using h 0 hδ.pos
    | some q =>
      exact congrArg some (eq_of_forall_reduce_blockStage_eq hδ fun ξ hξ ↦ by
        simpa using h ξ hξ)

end TemplateClass

/-! ### Stabilization, descent, gluing of classes, and observation -/

/-- **Stabilization of a coherent family of classes** (`ClassStabilizationTarget`): the index `ξ₀`
is one at which the number of top-labelled cells is least.  Native construction. -/
theorem classStabilizationTarget (δ : Ordinal.{u}) (n : ℕ) : ClassStabilizationTarget δ n := by
  intro hδ c hc
  classical
  have hP : ∃ m, ∃ ξ, ∃ hξ : ξ < δ, (c ξ hξ).topCount = m := ⟨_, 0, hδ.pos, rfl⟩
  obtain ⟨ξ₀, h₀, hm⟩ := Nat.find_spec hP
  refine ⟨ξ₀, h₀, fun ξ hξ h ↦ ?_⟩
  have hred := hc.reduce_eq_of_le h₀ hξ h
  have hle : ((c ξ hξ).reduce (isSuccPrelimit_blockStage ξ₀)).topCount ≤ (c ξ hξ).topCount := by
    rw [hred, hm]
    exact Nat.find_min' hP ⟨ξ, hξ, rfl⟩
  have key := TemplateClass.castLE_reduce_of_topCount_le _ (blockStage_mono h) _ hle
  rw [hred] at key
  exact key.symm

/-- **Descent of a class at a limit block stage** (`ClassDescentTarget`): the labels of a
representative all lie at one earlier block stage (`Label.exists_lt_forall_atStage_blockStage`).
Native construction. -/
theorem classDescentTarget (δ : Ordinal.{u}) (n : ℕ) : ClassDescentTarget δ n := by
  intro hδ c
  induction c using Quotient.inductionOn with
  | h t =>
    obtain ⟨ξ₀, h₀, ht⟩ := Label.exists_lt_forall_atStage_blockStage hδ t.label t.atStage
    exact ⟨ξ₀, h₀, fun ξ _ h ↦ congrArg StageType.toClass (t.castLE_reduce_of_atStage _ _
      fun i ↦ (ht i).mono (blockStage_mono h))⟩

/-- **Gluing a coherent family of classes** (`ClassFamilyGluingTarget`): the stabilized class read
at `λ_δ`.  Native construction. -/
theorem classFamilyGluingTarget (δ : Ordinal.{u}) (n : ℕ) : ClassFamilyGluingTarget δ n := by
  intro hδ c hc
  obtain ⟨ξ₀, h₀, hs⟩ := classStabilizationTarget δ n hδ c hc
  refine ⟨(c ξ₀ h₀).castLE (blockStage_strictMono h₀).le, fun ξ hξ ↦ ?_⟩
  rw [TemplateClass.reduce_castLE]
  rcases le_total ξ ξ₀ with h | h
  · exact hc.reduce_eq_of_le hξ h₀ h
  · rw [TemplateClass.reduce_eq_castLE _ (blockStage_mono h), hs ξ hξ h]

/-- **Observation along stage reduction** (`ObservesAtReduceTarget`): renaming commutes with
reduction, and reduction to `β` keeps the observation at a cutoff `x ≤ β`
(`StageType.reduce_mem_receivingFamily_reduce_iff`).  Native construction. -/
theorem observesAtReduceTarget (α β : Ordinal.{u}) (n : ℕ) : ObservesAtReduceTarget α β n := by
  intro hβ q D x hx
  induction q using Quotient.inductionOn with
  | h q =>
  induction D using Quotient.inductionOn with
  | h D =>
    change (q.reduce hβ).toClass.ObservesAt x (D.reduce hβ).toClass ↔
      q.toClass.ObservesAt x D.toClass
    rw [TemplateClass.observesAt_toClass_iff, TemplateClass.observesAt_toClass_iff]
    constructor
    · rintro ⟨_, ⟨k, σ, rfl⟩, hq⟩
      exact ⟨_, ⟨k, σ, rfl⟩,
        (StageType.reduce_mem_receivingFamily_reduce_iff (q := q.renameCells σ) hβ hx).mp hq⟩
    · rintro ⟨_, ⟨k, σ, rfl⟩, hq⟩
      exact ⟨_, ⟨k, σ, rfl⟩,
        (StageType.reduce_mem_receivingFamily_reduce_iff (q := q.renameCells σ) hβ hx).mpr hq⟩

/-! ### The limit of a coherent family of class realizations -/

namespace CoherentClassFamily

variable {δ : Ordinal.{u}} {M : Type v} (S : CoherentClassFamily.{u, v} δ M)

/-- The member at `ζ` reduces to the member at every `ξ ≤ ζ`.  Native construction. -/
theorem reduce_eq_of_le {ξ ζ : Ordinal.{u}} (hξ : ξ < δ) (hζ : ζ < δ) (h : ξ ≤ ζ) :
    (S.family ζ hζ).reduce (isSuccPrelimit_blockStage ξ) = S.family ξ hξ := by
  rcases h.lt_or_eq with h | rfl
  · exact S.coherent ξ hξ ζ hζ h
  · refine ClassRealization.ext fun t ↦ ?_
    rw [ClassRealization.reduce_eval]
    cases (S.family ξ hξ).eval t <;> simp

/-- A tuple is typed by one member exactly when it is typed by the member at `λ_0`.
Native construction. -/
theorem isSome_eval {ξ : Ordinal.{u}} (hξ : ξ < δ) (h0 : 0 < δ) {n : ℕ} (t : Fin n ↪ M) :
    ((S.family ξ hξ).eval t).isSome = ((S.family 0 h0).eval t).isSome := by
  rw [← S.reduce_eq_of_le h0 hξ zero_le, ClassRealization.reduce_eval, Option.isSome_map]

/-- The classes of a tuple typed by every member form a coherent family of classes.
Native construction. -/
theorem isCoherentFamily_get {n : ℕ} (t : Fin n ↪ M)
    (h : ∀ ξ (hξ : ξ < δ), ((S.family ξ hξ).eval t).isSome) :
    TemplateClass.IsCoherentFamily fun ξ hξ ↦ ((S.family ξ hξ).eval t).get (h ξ hξ) := by
  intro ξ hξ ζ hζ hlt
  have := congrArg (fun R ↦ R.eval t) (S.coherent ξ hξ ζ hζ hlt)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (h ζ hζ)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (h ξ hξ)
  simp only [ClassRealization.reduce_eval, hp, hq, Option.map_some, Option.some_inj] at this
  simpa only [hp, hq, Option.get_some] using this

open Classical in
/-- **The limit** of a coherent family of class realizations below a limit `δ`: a tuple typed by
every member has the glued class of its classes (`classFamilyGluingTarget`), chosen; any other
tuple is untyped.  Native construction. -/
def limit (hδ : Order.IsSuccLimit δ) : ClassRealization.{u, v} (blockStage δ) M where
  eval t := if h : ∀ ξ (hξ : ξ < δ), ((S.family ξ hξ).eval t).isSome then
    some (classFamilyGluingTarget δ _ hδ _ (S.isCoherentFamily_get t h)).choose else none

variable {hδ : Order.IsSuccLimit δ}

/-- **The limit reduces to the family**: its reduction to every earlier block stage is the member
there.  Native construction. -/
theorem limit_reduce {ξ : Ordinal.{u}} (hξ : ξ < δ) :
    (S.limit hδ).reduce (isSuccPrelimit_blockStage ξ) = S.family ξ hξ := by
  refine ClassRealization.ext fun t ↦ ?_
  rw [ClassRealization.reduce_eval]
  by_cases h : ∀ ζ (hζ : ζ < δ), ((S.family ζ hζ).eval t).isSome
  · simp only [limit, h, implies_true, ↓reduceDIte, Option.map_some]
    rw [(classFamilyGluingTarget δ _ hδ _ (S.isCoherentFamily_get t h)).choose_spec ξ hξ,
      Option.some_get]
  · have hn : (S.family ξ hξ).eval t = none := by
      push Not at h
      obtain ⟨ζ, hζ, hn⟩ := h
      rw [← Option.not_isSome_iff_eq_none, S.isSome_eval hξ hδ.pos, ← S.isSome_eval hζ hδ.pos]
      simpa using hn
    simp only [limit, h, ↓reduceDIte, Option.map_none, hn]

/-- A tuple of class `c` in the limit has the reduction of `c` in every member.
Native construction. -/
theorem eval_family_of_eval_limit {n : ℕ} {t : Fin n ↪ M} {c : TemplateClass.{u} _ n}
    (hc : (S.limit hδ).eval t = some c) {ξ : Ordinal.{u}} (hξ : ξ < δ) :
    (S.family ξ hξ).eval t = some (c.reduce (isSuccPrelimit_blockStage ξ)) := by
  rw [← S.limit_reduce (hδ := hδ) hξ, ClassRealization.reduce_eval, hc, Option.map_some]

/-- A tuple is typed in the limit exactly when it is typed by the member at `λ_0`.
Native construction. -/
theorem isSome_limit_eval {n : ℕ} (t : Fin n ↪ M) :
    ((S.limit hδ).eval t).isSome = ((S.family 0 hδ.pos).eval t).isSome := by
  rw [← S.limit_reduce (hδ := hδ) hδ.pos, ClassRealization.reduce_eval, Option.isSome_map]

/-- **The limit is well-formed**: consistency by separation of optional classes at `λ_δ`, since
reduction commutes with face maps; covering from the member at `λ_0`; legal types, since
legality is invariant under reduction.  Native construction. -/
theorem isWellFormed_limit : (S.limit hδ).IsWellFormed where
  isConsistent := by
    intro m n t c f hc
    refine TemplateClass.option_eq_of_forall_map_reduce_eq hδ fun ξ hξ ↦ ?_
    rw [← ClassRealization.reduce_eval, S.limit_reduce (hδ := hδ) hξ,
      ← TemplateClass.restrictFace_reduce]
    exact (S.isWellFormed ξ hξ).isConsistent t _ f (S.eval_family_of_eval_limit hc hξ)
  isCovering := by
    intro n t
    obtain ⟨m, u, f, hfu, hu⟩ := (S.isWellFormed 0 hδ.pos).isCovering t
    exact ⟨m, u, f, hfu, by rw [S.isSome_limit_eval]; exact hu⟩
  hasLegalTypes := by
    intro n t c hc
    exact (TemplateClass.isStronglyCodedLegal_reduce_iff _ c).mp
      ((S.isWellFormed 0 hδ.pos).hasLegalTypes t _ (S.eval_family_of_eval_limit hc hδ.pos))

/-- **Donor density of the limit at a permitted cutoff `x`** at `λ_δ`: an earlier block stage
`λ_ξ` strictly above `x` is chosen; the donor and the root class are reduced to `λ_ξ`, where
`x` is permitted; donor density of the member at `ξ` gives the extension, and the observation
returns to `λ_δ` along reduction (`observesAtReduceTarget`, `x ≤ λ_ξ`).  Native construction. -/
theorem hasDonorDensityAt_limit {x : Label.{u}} (hx : Label.IsPermittedCutoff (blockStage δ) x) :
    (S.limit hδ).HasDonorDensityAt x := by
  intro n m t p hp D g hD hDg
  obtain ⟨ξ, hξ, hxξ⟩ := Label.exists_lt_blockStage_of_lt hδ hx.2
  have hβ := isSuccPrelimit_blockStage ξ
  obtain ⟨u, hu, q', hq', hobs⟩ := S.hasDonorDensity ξ hξ t (p.reduce hβ)
    (S.eval_family_of_eval_limit hp hξ) (D.reduce hβ) g
    ((TemplateClass.isStronglyCodedLegal_reduce_iff hβ D).mpr hD)
    (by rw [TemplateClass.restrictFace_reduce, hDg, Option.map_some]) x ⟨hx.1, hxξ⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (show ((S.limit hδ).eval u).isSome by rw [S.isSome_limit_eval, ← S.isSome_eval hξ, hq']; rfl)
  have hqq := S.eval_family_of_eval_limit hq hξ
  rw [hq', Option.some_inj] at hqq
  rw [hqq] at hobs
  exact ⟨u, hu, q, hq, (observesAtReduceTarget _ _ _ hβ q D x hxξ.le).mp hobs⟩

/-- **The limit has donor density.**  Native construction. -/
theorem hasDonorDensity_limit : (S.limit hδ).HasDonorDensity :=
  (ClassRealization.hasDonorDensity_iff_forall_hasDonorDensityAt _).mpr fun _ hx ↦
    S.hasDonorDensityAt_limit hx

end CoherentClassFamily

/-- **The coherent limit of class realizations** (`ClassGluingTarget`, native construction,
conditional on coherence): the limit `CoherentClassFamily.limit` reduces to every member, is
well-formed, and has donor density at every permitted cutoff at `λ_δ`.  Coherence of the family is
a premise; the premise `δ < ω₁` is not used.  This is not the Limits conclusion of
[AFK26, Proposition 4.34], whose assembly must derive the coherence. -/
theorem classGluingTarget (δ : Ordinal.{u}) (M : Type v) : ClassGluingTarget δ M :=
  fun hδ _ S ↦ ⟨S.limit hδ, fun _ hξ ↦ S.limit_reduce (hδ := hδ) hξ, S.isWellFormed_limit,
    fun _ hx ↦ S.hasDonorDensityAt_limit hx⟩

end

end VaughtConjecture

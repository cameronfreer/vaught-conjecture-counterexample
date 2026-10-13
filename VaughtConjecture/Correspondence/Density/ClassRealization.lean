/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Density

/-!
# Class realizations, the decoder, and the targets of the decoder and of density

Numbering as in the current draft of [AFK26].

**Class realizations** (native construction).  A `ClassRealization α M` assigns to some injective
tuples of `M` a class of stage types at stage `α` up to cell renaming (`TemplateClass α n`), with
no numbering of cells chosen: no positional presentation is assumed.  Its well-formedness
conditions are explicit and separate (`ClassRealization.IsWellFormed`):

* `IsConsistent`: every face of a typed tuple has the face class of its class, including `none`
  at a face that is not closed (`TemplateClass.restrictFace`);
* `IsCovering`: every injective tuple is a face of a typed tuple;
* `HasLegalTypes`: every class is strongly coded legal, the legal templates of [AFK26,
  Definition 4.29] (`TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate`).

Stage reduction acts on classes (`ClassRealization.reduce`) and keeps the three conditions
(`IsWellFormed.reduce`).  A positional realization has a **class reading**
(`Realization.classReading`): the class of each type.  It keeps consistency and covering, and
legal types when the types are strongly coded; it commutes with stage reduction; and two
realizations have the same class reading exactly when, tuple by tuple, their types are cell
renamings of each other (`Realization.classReading_eq_classReading_iff`).

**Density of a class realization** (`ClassRealization.HasDonorDensity`, native construction,
defined without reference to `SatisfiesDensityAt`): for every typed tuple `t` of class `p`,
every strongly coded legal class `D` **at the stage of the realization** on `m` points restricting
to `p` along **any** embedding `g : Fin n ↪ Fin m` (including `n = 0`), and every permitted cutoff
`x` (`⊥ < x < α`), some tuple `u` extends `t` along `g` literally and has a class with the
observation of `D` at `x` up to renaming (`TemplateClass.ObservesAt`, capped observation
`min · x`).  It is the class form of `Realization.HasFiniteExtensionReceiving` restricted to
strongly coded donors: a realization with finite-extension receiving and strongly coded legal
types has a class reading with donor density
(`Realization.HasFiniteExtensionReceiving.hasDonorDensity_classReading`).  It differs from
`D[α]` in four ways: donors at the stage instead of at `ω₁` (any rank), arbitrary embeddings
instead of the old points first, roots on no points, and capped observation at cutoffs below the
stage instead of raw truncation.  Their comparison is the target B.T6 below.

**Structures and the decoder** (native construction).  `ClassRealization.toStructure` is the
structure of `L_b[L] ∪ L_c[L]` read from a class realization: a symbol holds of an injective
typed tuple when it reads the class at `ω₁` of its type (`TemplateSymbol.Reads`), as in the charts
of [AFK26, Definition 4.31].  `decode β G` reads a structure as a class realization at the block
stage `ω + ω · β`: the empty tuple has the class on no points, and a tuple on `n ≥ 1` points has
the reduction to `ω + ω · β` of a class `c` with `G ⊨ Q_c(t)`, if there is one, chosen.  The
decoder needs no hypothesis to be defined; its coherence is in the targets.

**Proved here** (the directions of B.T5 that need no compatibility): for `β < ω₁`,
`projectStructure β R.toStructure = R.toStructure` for every class realization at the block
stage (`projectStructure_toStructure`), and `decode β R.toStructure = R` for every well-formed
one (`decode_toStructure`).

## The statements B.T5 and B.T6

Stated here as propositions, every premise visible; proved in
`VaughtConjecture.Correspondence.Density.Decoder` (`decoderRoundTrip`) and
`VaughtConjecture.Correspondence.Density.DonorDensity` (`densityDecoderEquivalence`).

* **B.T5, the decoder round trip** (`DecoderRoundTrip β M`, for `β < ω₁`): compatible `β`-fixed
  structures and well-formed class realizations at `ω + ω · β` correspond, all symbols preserved:
  ```
  theorem decoderRoundTrip (hβ : β < ω₁) : DecoderRoundTrip β M
  ```
  where `DecoderRoundTrip β M` is
  ```
  (∀ G : templateLanguage.Structure M, IsTemplateCompatible G → projectStructure β G = G →
      (decode β G).IsWellFormed ∧ (decode β G).toStructure = G) ∧
    ∀ R : ClassRealization (blockStage β) M, R.IsWellFormed →
      IsTemplateCompatible R.toStructure ∧ projectStructure β R.toStructure = R.toStructure ∧
        decode β R.toStructure = R
  ```
  The last two conjuncts of the second half are proved in this file
  (`projectStructure_toStructure`, `decode_toStructure`).
* **B.T6, density** (`DensityDecoderEquivalence β M`, for `β < ω₁`):
  ```
  theorem densityDecoderEquivalence (hβ : β < ω₁) : DensityDecoderEquivalence β M
  ```
  where `DensityDecoderEquivalence β M` is
  ```
  ∀ G : templateLanguage.Structure M, Nonempty M → IsTemplateCompatible G →
    projectStructure β G = G →
      ((∀ α < blockStage β, SatisfiesDensityAt α G) ↔ (decode β G).HasDonorDensity)
  ```
  `Nonempty M` is needed for the roots on no points of `HasDonorDensity`, which `D[α]` does not
  have.

## Targets of the presentation checkpoint

Nothing in this directory presents class data positionally.  The tuplewise statement
`Realization.classReading_eq_classReading_iff` (equal class readings exactly when the types are
cell renamings of each other, tuple by tuple) is not a coherent renaming: it asserts no
compatibility of the bijections of cells with faces, and no statement here uses it as one.  The
statements that need a positional presentation are targets of the presentation checkpoint:

* **B.T7, presentation**: for `β < ω₁`, `[Countable M]`, `Nonempty M`, a well-formed class
  realization `S` at `ω + ω · β` with `S.HasDonorDensity` is the class reading of a positional
  realization with strongly coded legal types and receiving restricted to strongly coded donors:
  ```
  ∃ R : Realization (blockStage β) M, R.IsConsistent ∧ R.IsCovering ∧
    (∀ ⦃n⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsStronglyCodedLegal) ∧
    R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) ∧ R.classReading = S
  ```
  Here the positional consistency of `R` is the coherence that tuplewise renaming lacks.
* **B.T8, coherent renaming**: for `[Countable M]`, two such presentations of one class
  realization are related by a coherent cell renaming (bijections of cells natural along faces).
* **Unification with the receiving core**: the class reading of a realization with receiving
  restricted to strongly coded donors (`HasFiniteExtensionReceivingIn`, not on the main branch
  when this was written) has donor density, as
  `Realization.HasFiniteExtensionReceiving.hasDonorDensity_classReading` does for receiving with
  every legal donor.  This direction reads a given positional realization and needs no
  presentation.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Classes: the empty class, reduction, and the class at `ω₁` -/

namespace TemplateClass

open StageType

variable {α β γ : Ordinal.{u}} {n m : ℕ}

variable (α) in
/-- The class on no points.  Native construction. -/
def empty : TemplateClass.{u} α 0 :=
  ((Correspondence.isLegal_intervalScheme 0).toStageType α).toClass

/-- There is exactly one class on no points.  Native construction. -/
theorem eq_empty (c : TemplateClass.{u} α 0) : c = empty α :=
  Quotient.inductionOn c fun _ ↦ congrArg toClass (eq_of_zero _ _)

/-- The face of a class on no points is defined and is the class on no points.
Native construction. -/
theorem restrictFace_zero (c : TemplateClass.{u} α n) (f : Fin 0 ↪ Fin n) :
    c.restrictFace f = some (empty α) :=
  Quotient.inductionOn c fun t ↦ by
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (t.isSome_restrictFace_of_zero f)
    rw [restrictFace_toClass, hs, Option.map_some, eq_empty s.toClass]

/-- Stage reduction of classes commutes with face maps, including definedness.
Native construction. -/
theorem restrictFace_reduce (hβ : Order.IsSuccPrelimit β) (c : TemplateClass.{u} α n)
    (f : Fin m ↪ Fin n) : (c.reduce hβ).restrictFace f = (c.restrictFace f).map (reduce hβ) :=
  Quotient.inductionOn c fun t ↦ by
    rw [reduce_toClass, restrictFace_toClass, restrictFace_toClass, StageType.restrictFace_reduce,
      Option.map_map, Option.map_map]
    rfl

/-- Reductions of classes compose to the lower one.  Native construction. -/
theorem reduce_reduce (hβ : Order.IsSuccPrelimit β) (hγ : Order.IsSuccPrelimit γ) (hγβ : γ ≤ β)
    (c : TemplateClass.{u} α n) : (c.reduce hβ).reduce hγ = c.reduce hγ :=
  Quotient.inductionOn c fun t ↦ congrArg toClass (StageType.reduce_reduce t hβ hγ hγβ)

/-- Reduction of a class to its own stage is the identity.  Native construction. -/
@[simp] theorem reduce_self (hα : Order.IsSuccPrelimit α) (c : TemplateClass.{u} α n) :
    c.reduce hα = c :=
  Quotient.inductionOn c fun t ↦ congrArg toClass (t.reduce_self hα)

/-- Stage reduction keeps strongly coded legality, in both directions.  Native construction. -/
@[simp] theorem isStronglyCodedLegal_reduce_iff (hβ : Order.IsSuccPrelimit β)
    (c : TemplateClass.{u} α n) : (c.reduce hβ).IsStronglyCodedLegal ↔ c.IsStronglyCodedLegal :=
  Quotient.inductionOn c fun _ ↦ Iff.rfl

/-- **The class at `ω₁`** of a class: its reduction to `ω₁` (`StageType.globalClass` on
representatives).  Native construction. -/
def globalClass (c : TemplateClass.{u} α n) : TemplateClass.{u} ω₁ n :=
  c.reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit

@[simp] theorem globalClass_toClass (t : StageType.{u} α n) :
    t.toClass.globalClass = t.globalClass :=
  rfl

/-- At a stage `λ ≤ ω₁` that is zero or a limit, reducing the class at `ω₁` back to `λ` gives the
class.  Native construction. -/
theorem reduce_globalClass {lam : Ordinal.{u}} (hlam : Order.IsSuccPrelimit lam) (h : lam ≤ ω₁)
    (c : TemplateClass.{u} lam n) : c.globalClass.reduce hlam = c := by
  rw [globalClass, reduce_reduce _ _ h, reduce_self]

/-- At a stage `λ ≤ ω₁`, the class at `ω₁` determines the class.  Native construction. -/
theorem globalClass_injective {lam : Ordinal.{u}} (hlam : Order.IsSuccPrelimit lam)
    (h : lam ≤ ω₁) : Function.Injective (globalClass (α := lam) (n := n)) := fun c d hcd ↦ by
  rw [← reduce_globalClass hlam h c, hcd, reduce_globalClass hlam h d]

/-- **The class at `ω₁` of a class at a stage `λ ≤ ω₁` is fixed by the projection to `λ`.**
Correspondence with the printed definitions. -/
theorem project_globalClass {lam : Ordinal.{u}} (hlam : Order.IsSuccPrelimit lam) (h : lam ≤ ω₁)
    (c : TemplateClass.{u} lam n) : c.globalClass.project hlam = c.globalClass :=
  Quotient.inductionOn c fun t ↦ by
    rw [globalClass_toClass, StageType.globalClass, project_toClass_eq_iff hlam h]
    intro d
    rw [StageType.reduce_label_of_le t _ h d]
    exact t.atStage d

end TemplateClass

/-! ### Class realizations -/

/-- **A class realization** at stage `α` on `M` (native construction): a partial evaluation of
the injective tuples of `M` by classes of stage types at stage `α` up to cell renaming.  No
numbering of cells is part of the data.  Native construction. -/
structure ClassRealization (α : Ordinal.{u}) (M : Type v) where
  /-- The class of an injective tuple, if it has one. -/
  eval {n : ℕ} : (Fin n ↪ M) → Option (TemplateClass.{u} α n)

namespace ClassRealization

variable {α β : Ordinal.{u}} {M : Type v} {n : ℕ} (R : ClassRealization.{u, v} α M)

/-- Extensionality: equal evaluations at every tuple.  Native construction. -/
@[ext] theorem ext {R R' : ClassRealization.{u, v} α M}
    (h : ∀ {n : ℕ} (t : Fin n ↪ M), R.eval t = R'.eval t) : R = R' := by
  obtain ⟨e⟩ := R
  obtain ⟨e'⟩ := R'
  congr
  funext n t
  exact h t

/-- **Consistency**: every face of a typed tuple has the face class of its class, including
`none` at a face that is not closed.  Native construction. -/
def IsConsistent : Prop :=
  ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (c : TemplateClass.{u} α n) (f : Fin m ↪ Fin n),
    R.eval t = some c → R.eval (f.trans t) = c.restrictFace f

/-- **Covering**: every injective tuple is a face of a typed tuple.  Native construction. -/
def IsCovering : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
    ∃ (m : ℕ) (u : Fin m ↪ M) (f : Fin n ↪ Fin m), f.trans u = t ∧ (R.eval u).isSome

/-- **Legal types**: every class is strongly coded legal, the class of a legal template of
[AFK26, Definition 4.29].  Native construction. -/
def HasLegalTypes : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (c : TemplateClass.{u} α n), R.eval t = some c →
    c.IsStronglyCodedLegal

/-- **A well-formed class realization**: consistent, covering, with legal types.
Native construction. -/
structure IsWellFormed : Prop where
  /-- Consistency. -/
  isConsistent : R.IsConsistent
  /-- Covering. -/
  isCovering : R.IsCovering
  /-- Legal types. -/
  hasLegalTypes : R.HasLegalTypes

variable {R}

/-- In a consistent covering class realization, the empty tuple has the class on no points.
Native construction. -/
theorem eval_zero (hR : R.IsConsistent) (hc : R.IsCovering) (t : Fin 0 ↪ M) :
    R.eval t = some (TemplateClass.empty α) := by
  obtain ⟨m, u, f, hfu, hu⟩ := hc t
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hu
  rw [← hfu, hR u c f hc, TemplateClass.restrictFace_zero]

variable (R)

/-- **Stage reduction** of a class realization to a stage that is zero or a limit.
Native construction. -/
def reduce (hβ : Order.IsSuccPrelimit β) : ClassRealization.{u, v} β M where
  eval t := (R.eval t).map (TemplateClass.reduce hβ)

@[simp] theorem reduce_eval (hβ : Order.IsSuccPrelimit β) (t : Fin n ↪ M) :
    (R.reduce hβ).eval t = (R.eval t).map (TemplateClass.reduce hβ) :=
  rfl

variable {R}

/-- **Stage reduction keeps well-formedness.**  Native construction. -/
theorem IsWellFormed.reduce (hR : R.IsWellFormed) (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).IsWellFormed where
  isConsistent := by
    intro m n t c f h
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [reduce_eval, hR.isConsistent t c' f hc', TemplateClass.restrictFace_reduce]
  isCovering := by
    intro n t
    obtain ⟨m, u, f, hfu, hu⟩ := hR.isCovering t
    exact ⟨m, u, f, hfu, by simpa using hu⟩
  hasLegalTypes := by
    intro n t c h
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
    exact (TemplateClass.isStronglyCodedLegal_reduce_iff hβ c').mpr (hR.hasLegalTypes t c' hc')

/-! ### Donor density -/

variable (R)

/-- **Donor density of a class realization** (native construction): for every typed tuple `t` of
class `p`, every strongly coded legal class `D` at the stage `α` of the realization on `m` points
whose face along `g : Fin n ↪ Fin m` is `p`, and every permitted cutoff `x` (`⊥ < x < α`), some
injective tuple `u` extends `t` along `g` literally (`g.trans u = t`) and has a class `q` with the
observation of `D` at `x` up to renaming (`TemplateClass.ObservesAt`).  `n = 0` is included.
Native construction. -/
def HasDonorDensity : Prop :=
  ∀ ⦃n m : ℕ⦄ (t : Fin n ↪ M) (p : TemplateClass.{u} α n), R.eval t = some p →
    ∀ (D : TemplateClass.{u} α m) (g : Fin n ↪ Fin m), D.IsStronglyCodedLegal →
      D.restrictFace g = some p → ∀ x : Label.{u}, Label.IsPermittedCutoff α x →
        ∃ u : Fin m ↪ M, g.trans u = t ∧ ∃ q, R.eval u = some q ∧ q.ObservesAt x D

/-! ### The structure of a class realization -/

/-- **The structure of a class realization** (native construction): a symbol holds of a tuple
when the tuple is injective, typed, and the symbol reads the class at `ω₁` of its type
(`TemplateSymbol.Reads`: `P_k` every class, `Q_c` the class `c`, `R_c` the classes with
`τ₀`-projection `c`).  Native construction. -/
@[instance_reducible] def toStructure : templateLanguage.{u}.Structure M where
  funMap f := Empty.elim f
  RelMap r xs := ∃ h : Function.Injective xs, ∃ c, R.eval ⟨xs, h⟩ = some c ∧ r.Reads c.globalClass

theorem relMap_toStructure {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := R.toStructure) r xs ↔
      ∃ h : Function.Injective xs, ∃ c, R.eval ⟨xs, h⟩ = some c ∧ r.Reads c.globalClass :=
  Iff.rfl

/-- **A class realization at a block stage gives a structure fixed by the projection to that
stage**, for `β < ω₁`: `τ_β(R.toStructure) = R.toStructure`.  No well-formedness is needed.
Correspondence with the printed definitions. -/
theorem projectStructure_toStructure (hβ : β < ω₁) (R : ClassRealization.{u, v} (blockStage β) M) :
    projectStructure β R.toStructure = R.toStructure := by
  have hlam : blockStage β ≤ ω₁ := (blockStage_lt_omega_one hβ).le
  refine templateStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk => exact Iff.rfl
  | base c h0 hk => exact Iff.rfl
  | invariant c hk =>
    rw [relMap_projectStructure_invariant]
    constructor
    · rintro ⟨c', rfl, h, d, hd, hc'⟩
      refine ⟨h, d, hd, ?_⟩
      change d.globalClass = c'.1.project _
      rw [← hc']
      exact (TemplateClass.project_globalClass _ hlam d).symm
    · intro hx
      refine ⟨c, Subtype.ext ?_, hx⟩
      obtain ⟨h, d, hd, hc⟩ := hx
      change c.1.project _ = c.1
      rw [← hc]
      exact TemplateClass.project_globalClass _ hlam d

end ClassRealization

/-! ### The decoder -/

variable {M : Type v}

open Classical in
/-- The evaluation of the decoder: the class on no points for the empty tuple, and for `n ≥ 1`
the reduction to `ω + ω · β` of a legal class `c` with `G ⊨ Q_c(t)`, chosen, if there is one.
Native construction. -/
def decodeEval (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) :
    ∀ {n : ℕ}, (Fin n ↪ M) → Option (TemplateClass.{u} (blockStage β) n)
  | 0, _ => some (TemplateClass.empty _)
  | n + 1, t => if h : ∃ c : LegalClass.{u} (n + 1),
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c n.succ_pos) t
      then some (h.choose.1.reduce (isSuccPrelimit_blockStage β)) else none

/-- **The decoder** (native construction): a structure of `L_b[L] ∪ L_c[L]` read as a class
realization at the block stage `ω + ω · β` (`decodeEval`).  It is defined for every structure;
its coherence for compatible `β`-fixed structures is the target `DecoderRoundTrip`.
Native construction. -/
def decode (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) :
    ClassRealization.{u, v} (blockStage β) M :=
  ⟨decodeEval β G⟩

/-- **Decoding the structure of a well-formed class realization gives it back**, for `β < ω₁`.
Native construction. -/
theorem decode_toStructure {β : Ordinal.{u}} (hβ : β < ω₁)
    {R : ClassRealization.{u, v} (blockStage β) M} (hR : R.IsWellFormed) :
    decode β R.toStructure = R := by
  have hlam : blockStage β ≤ ω₁ := (blockStage_lt_omega_one hβ).le
  refine ClassRealization.ext ?_
  intro n t
  cases n with
  | zero => exact (ClassRealization.eval_zero hR.isConsistent hR.isCovering t).symm
  | succ n =>
    change decodeEval β R.toStructure t = R.eval t
    simp only [decodeEval]
    split_ifs with h
    · obtain ⟨_, d, hd, hc⟩ := h.choose_spec
      change R.eval t = some d at hd
      change d.globalClass = h.choose.1 at hc
      rw [hd, ← hc, TemplateClass.reduce_globalClass _ hlam]
    · cases hd : R.eval t with
      | none => rfl
      | some d =>
        exact absurd ⟨⟨d.globalClass, (TemplateClass.isStronglyCodedLegal_reduce_iff _ d).mpr
          (hR.hasLegalTypes t d hd)⟩, t.injective, d, hd, rfl⟩ h

/-! ### The class reading of a positional realization -/

namespace Realization

variable {α β : Ordinal.{u}} {n : ℕ} (R : Realization.{u, v} α M)

/-- **The class reading** of a positional realization: the class of the type of each tuple.
Native construction. -/
def classReading : ClassRealization.{u, v} α M where
  eval t := (R.eval t).map StageType.toClass

@[simp] theorem classReading_eval (t : Fin n ↪ M) :
    R.classReading.eval t = (R.eval t).map StageType.toClass :=
  rfl

/-- Two realizations **agree up to cell renaming, tuple by tuple**: the same tuples are typed,
by types that are cell renamings of each other.  The bijections of cells are chosen tuple by
tuple, with no compatibility along faces: this is not a coherent renaming of presentations.
Native construction. -/
def IsCellRenamingOf (R' : Realization.{u, v} α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), Option.Rel StageType.IsCellRenaming (R.eval t) (R'.eval t)

/-- **The class reading respects renaming**: two realizations have the same class reading exactly
when their types are cell renamings of each other, tuple by tuple.  Tuplewise only: a coherent
renaming of presentations is a target of the presentation checkpoint.  Native construction. -/
theorem classReading_eq_classReading_iff {R' : Realization.{u, v} α M} :
    R.classReading = R'.classReading ↔ R.IsCellRenamingOf R' := by
  constructor
  · intro h n t
    have ht : (R.eval t).map StageType.toClass = (R'.eval t).map StageType.toClass :=
      congrArg (fun S : ClassRealization.{u, v} α M ↦ S.eval t) h
    revert ht
    cases R.eval t <;> cases R'.eval t <;> intro ht
    · exact Option.Rel.none
    · simp at ht
    · simp at ht
    · exact Option.Rel.some (StageType.toClass_eq_toClass_iff.mp (Option.some.inj ht))
  · intro h
    refine ClassRealization.ext fun t ↦ ?_
    simp only [classReading_eval]
    have ht := h t
    revert ht
    cases R.eval t <;> cases R'.eval t <;> intro ht
    · rfl
    · exact absurd ht (by simp)
    · exact absurd ht (by simp)
    · exact congrArg some (StageType.toClass_eq_toClass_iff.mpr (Option.rel_some_some.mp ht))

/-- **The class reading commutes with stage reduction.**  Native construction. -/
theorem classReading_reduce (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).classReading = R.classReading.reduce hβ :=
  ClassRealization.ext fun t ↦ by
    simp only [classReading_eval, reduce_eval, ClassRealization.reduce_eval, Option.map_map]
    rfl

variable {R}

/-- The class reading of a consistent realization is consistent.  Native construction. -/
theorem IsConsistent.classReading (hR : R.IsConsistent) : R.classReading.IsConsistent := by
  intro m n t c f h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [classReading_eval, hR t p f hp, TemplateClass.restrictFace_toClass]

/-- The class reading of a covering realization is covering.  Native construction. -/
theorem IsCovering.classReading (hc : R.IsCovering) : R.classReading.IsCovering := by
  intro n t
  obtain ⟨m, u, f, hfu, hu⟩ := hc t
  exact ⟨m, u, f, hfu, by simpa using hu⟩

/-- The class reading of a realization with strongly coded legal types has legal types.
Native construction. -/
theorem classReading_hasLegalTypes
    (hl : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal) : R.classReading.HasLegalTypes := by
  intro n t c h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact hl t p hp

/-- **Positional receiving gives class donor density**: a realization with finite-extension
receiving (every legal donor) has a class reading with donor density.  Each class donor has a
representative with the type of the root as its face along `g`
(`TemplateClass.exists_renaming_restrictFace_eq`).  Native construction. -/
theorem HasFiniteExtensionReceiving.hasDonorDensity_classReading
    (h : R.HasFiniteExtensionReceiving) : R.classReading.HasDonorDensity := by
  intro n m t p hp D g hD hDg x hx
  obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
  induction D using Quotient.inductionOn with
  | h D' =>
    obtain ⟨D'', hD'', hface⟩ := TemplateClass.exists_renaming_restrictFace_eq D' g hDg
    have hleg : D''.IsLegal := by
      change D'.toClass.IsStronglyCodedLegal at hD
      rw [← hD''] at hD
      exact hD.1
    obtain ⟨u, hu, q, hq, he⟩ := h t p' hp' D'' g hleg hface x hx
    refine ⟨u, hu, q.toClass, by rw [classReading_eval, he, Option.map_some], ?_⟩
    change q.toClass.ObservesAt x D'.toClass
    rw [← hD'']
    exact ⟨q, D'', rfl, rfl, hq⟩

end Realization

/-! ### The statements B.T5 and B.T6 -/

/-- **Target B.T5, the decoder round trip at `β`** (for `β < ω₁`): a compatible structure fixed by
`τ_β` decodes to a well-formed class realization at `ω + ω · β` whose structure is the given one;
and the structure of a well-formed class realization at `ω + ω · β` is compatible, fixed by
`τ_β`, and decodes back to the realization.  All symbols are preserved: the equalities are
equalities of structures of `L_b[L] ∪ L_c[L]` and of class realizations.  Proved for `β < ω₁`
(`decoderRoundTrip`).  Correspondence with the printed definitions. -/
def DecoderRoundTrip (β : Ordinal.{u}) (M : Type v) : Prop :=
  (∀ G : templateLanguage.{u}.Structure M, IsTemplateCompatible G → projectStructure β G = G →
      (decode β G).IsWellFormed ∧ (decode β G).toStructure = G) ∧
    ∀ R : ClassRealization.{u, v} (blockStage β) M, R.IsWellFormed →
      IsTemplateCompatible R.toStructure ∧ projectStructure β R.toStructure = R.toStructure ∧
        decode β R.toStructure = R

/-- **Target B.T6, density through the decoder at `β`** (for `β < ω₁`): for a compatible
structure on a nonempty carrier fixed by `τ_β`, density `D[α]` at every `α < ω + ω · β` holds
exactly when its decoded class realization has donor density.  Proved for `β < ω₁`
(`densityDecoderEquivalence`).  Correspondence with the printed definitions. -/
def DensityDecoderEquivalence (β : Ordinal.{u}) (M : Type v) : Prop :=
  ∀ G : templateLanguage.{u}.Structure M, Nonempty M → IsTemplateCompatible G →
    projectStructure β G = G →
      ((∀ α < blockStage β, SatisfiesDensityAt α G) ↔ (decode β G).HasDonorDensity)

end

end VaughtConjecture

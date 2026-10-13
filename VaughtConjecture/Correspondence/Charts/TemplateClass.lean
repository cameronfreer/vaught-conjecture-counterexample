/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.RenamingFaces
import VaughtConjecture.Correspondence.InvariantSystem

/-!
# Templates up to cell renaming

[AFK26, Definition 4.6] identifies a template with its cell renamings ("we think of renamings of
templates as being the same"), and the template system `L` of [AFK26, Definition 4.11 and
Proposition 4.30] keeps one template in each class.  `TemplateClass α n` is the type of stage types
at stage `α` on `n` points up to `StageType.IsCellRenaming` (`StageType.renamingSetoid`).

**Operations on classes** (all natively, by the invariance of each operation under renaming):

* `TemplateClass.restrictFace f`, the face map, defined exactly at the closed faces
  (`StageType.restrictFace_renameCells`, `StageType.restrictFace_renameCells_eq_none_iff`);
* `TemplateClass.reduce` (stage reduction), `TemplateClass.castLE` (reading at a larger stage),
  and, at stage `ω₁`, `TemplateClass.project` (the projection `StageType.project` of
  `VaughtConjecture.Correspondence.InvariantSystem`, the truncation of [AFK26, Definitions 4.10 and
  4.16]);
* `TemplateClass.IsStronglyCodedLegal`, the legal templates of [AFK26, Definition 4.29]
  (`TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate`).

**Alignment of representatives along faces** (`TemplateClass.exists_renaming_restrictFace_eq`): if
the class of `t` has, along `f`, the face class of `s`, some renaming of `t` has the face `s` along
`f`, literally.  This is what lets the native amalgamation, which needs equal faces, act on
classes.

**Classes at `ω₁`.**  A stage type at any stage has a class at `ω₁`, the class of its reduction to
`ω₁` (`StageType.globalClass`).  For a stage at most `ω₁` two stage types have the same class at
`ω₁` exactly when they are renamings of each other (`StageType.globalClass_eq_iff`).  The classes
at `ω₁` fixed by the projection to a stage `γ ≤ ω₁` are those whose labels lie at stage `γ`
(`TemplateClass.project_toClass_eq_iff`): a renaming keeps the number of labels `∞`, and the
projection adds one for every label in `[γ, ∞)`.
-/

universe u

namespace VaughtConjecture

open Finset Ordinal

noncomputable section

/-- **Stage types up to cell renaming** [AFK26, Definition 4.6]: the templates on `[n]` with labels
at stage `α`, up to renaming. -/
abbrev TemplateClass (α : Ordinal.{u}) (n : ℕ) : Type (u + 1) :=
  Quotient (StageType.renamingSetoid.{u} α n)

namespace StageType

variable {α β : Ordinal.{u}} {n m : ℕ}

/-- The class of a stage type. -/
abbrev toClass (t : StageType.{u} α n) : TemplateClass.{u} α n :=
  Quotient.mk _ t

/-- Two stage types have the same class exactly when one is a renaming of the other. -/
theorem toClass_eq_toClass_iff {s t : StageType.{u} α n} :
    s.toClass = t.toClass ↔ s.IsCellRenaming t :=
  Quotient.eq (r := renamingSetoid.{u} α n)

/-- A renaming has the class of the type. -/
@[simp] theorem toClass_renameCells (t : StageType.{u} α n) {k : ℕ} (σ : Fin k ≃ Fin t.card) :
    (t.renameCells σ).toClass = t.toClass :=
  (toClass_eq_toClass_iff.mpr ⟨_, σ, rfl⟩).symm

/-- Reading at a larger stage is injective. -/
theorem castLE_injective (h : α ≤ β) :
    Function.Injective (fun t : StageType.{u} α n ↦ t.castLE h) := fun s t hst ↦ by
  refine ext (congrArg (fun r : StageType.{u} β n ↦ r.toScheme) hst) fun i j hij ↦ ?_
  exact label_congr hst hij

/-- Reading at a larger stage reflects cell renaming. -/
theorem isCellRenaming_castLE_iff (h : α ≤ β) {s t : StageType.{u} α n} :
    (s.castLE h).IsCellRenaming (t.castLE h) ↔ s.IsCellRenaming t := by
  refine ⟨fun ⟨k, σ, hσ⟩ ↦ ⟨k, σ, castLE_injective h hσ⟩, fun ⟨k, σ, hσ⟩ ↦ ⟨k, σ, ?_⟩⟩
  subst hσ
  rfl

/-- **The class at `ω₁`** of a stage type: the class of its reduction to `ω₁`. -/
def globalClass (t : StageType.{u} α n) : TemplateClass.{u} ω₁ n :=
  (t.reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit).toClass

/-- A renaming has the class at `ω₁` of the type. -/
@[simp] theorem globalClass_renameCells (t : StageType.{u} α n) {k : ℕ}
    (σ : Fin k ≃ Fin t.card) : (t.renameCells σ).globalClass = t.globalClass :=
  toClass_renameCells (t.reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit) σ

/-- **At a stage at most `ω₁`, the classes at `ω₁` are the classes.** -/
theorem globalClass_eq_iff (hα : α ≤ ω₁) {s t : StageType.{u} α n} :
    s.globalClass = t.globalClass ↔ s.IsCellRenaming t := by
  rw [globalClass, globalClass, toClass_eq_toClass_iff, reduce_eq_castLE _ _ hα,
    reduce_eq_castLE _ _ hα, isCellRenaming_castLE_iff]

end StageType

namespace TemplateClass

variable {α β γ : Ordinal.{u}} {n m : ℕ}

open StageType

/-- A class is **strongly coded legal** when its stage types are: at a stage at most `ω₁`, these
are the classes of the legal templates of [AFK26, Definition 4.29]. -/
def IsStronglyCodedLegal (c : TemplateClass.{u} α n) : Prop :=
  Quotient.lift (fun t : StageType.{u} α n ↦ t.IsStronglyCodedLegal) (fun a b h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact propext (isStronglyCodedLegal_renameCells_iff a σ).symm) c

@[simp] theorem isStronglyCodedLegal_toClass (t : StageType.{u} α n) :
    t.toClass.IsStronglyCodedLegal ↔ t.IsStronglyCodedLegal :=
  Iff.rfl

/-- **The legal classes are the classes of the legal templates** [AFK26, Definition 4.29], at a
stage at most `ω₁`. -/
theorem isStronglyCodedLegal_toClass_iff_isLegalTemplate (hα : α ≤ ω₁) (t : StageType.{u} α n) :
    t.toClass.IsStronglyCodedLegal ↔ t.IsLegalTemplate ω₁ :=
  (isLegalTemplate_omega_one_iff_of_le hα).symm

/-- The face of a class along `f` is the class of a face. -/
private theorem restrictFace_map_toClass_eq {a : StageType.{u} α n} {k : ℕ}
    (σ : Fin k ≃ Fin a.card) (f : Fin m ↪ Fin n) :
    (StageType.restrictFace f a).map toClass =
      (StageType.restrictFace f (a.renameCells σ)).map toClass := by
  cases ha : StageType.restrictFace f a with
  | none =>
    rw [Option.map_none, ((restrictFace_renameCells_eq_none_iff a σ f).mpr ha), Option.map_none]
  | some x =>
    obtain ⟨x', hx', hxx'⟩ := restrictFace_renameCells a σ f ha
    rw [hx', Option.map_some, Option.map_some, toClass_eq_toClass_iff.mpr hxx']

/-- **The face map on classes** [AFK26, Definitions 4.6 and 4.8]: the class of the face of a
representative, defined exactly at the closed faces. -/
def restrictFace (f : Fin m ↪ Fin n) (c : TemplateClass.{u} α n) :
    Option (TemplateClass.{u} α m) :=
  Quotient.lift (fun t : StageType.{u} α n ↦ (StageType.restrictFace f t).map toClass)
    (fun a b h ↦ by
      obtain ⟨_, σ, rfl⟩ := h
      exact restrictFace_map_toClass_eq σ f) c

@[simp] theorem restrictFace_toClass (f : Fin m ↪ Fin n) (t : StageType.{u} α n) :
    t.toClass.restrictFace f = (StageType.restrictFace f t).map toClass :=
  rfl

/-- **Stage reduction on classes**, to a stage that is zero or a limit. -/
def reduce (hβ : Order.IsSuccPrelimit β) (c : TemplateClass.{u} α n) : TemplateClass.{u} β n :=
  Quotient.map (fun t : StageType.{u} α n ↦ t.reduce hβ) (fun a b h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact ⟨_, σ, rfl⟩) c

@[simp] theorem reduce_toClass (hβ : Order.IsSuccPrelimit β) (t : StageType.{u} α n) :
    t.toClass.reduce hβ = (t.reduce hβ).toClass :=
  rfl

/-- **Reading a class at a larger stage.** -/
def castLE (h : α ≤ β) (c : TemplateClass.{u} α n) : TemplateClass.{u} β n :=
  Quotient.map (fun t : StageType.{u} α n ↦ t.castLE h) (fun a b h' ↦ by
    obtain ⟨_, σ, rfl⟩ := h'
    exact ⟨_, σ, rfl⟩) c

@[simp] theorem castLE_toClass (h : α ≤ β) (t : StageType.{u} α n) :
    t.toClass.castLE h = (t.castLE h).toClass :=
  rfl

/-- **The projection of a class at `ω₁`** to a stage that is zero or a limit
([AFK26, Definitions 4.10 and 4.16]): the class of the projection `StageType.project`. -/
def project (hγ : Order.IsSuccPrelimit γ) (c : TemplateClass.{u} ω₁ n) : TemplateClass.{u} ω₁ n :=
  Quotient.map (fun t : StageType.{u} ω₁ n ↦ t.project hγ) (fun a b h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact ⟨_, σ, rfl⟩) c

@[simp] theorem project_toClass (hγ : Order.IsSuccPrelimit γ) (t : StageType.{u} ω₁ n) :
    t.toClass.project hγ = (t.project hγ).toClass :=
  rfl

/-- **Alignment of representatives along faces**: if the face class of `t` along `f` is the class
of `s`, some renaming of `t` has the face `s` along `f`. -/
theorem exists_renaming_restrictFace_eq (t : StageType.{u} α n) (f : Fin m ↪ Fin n)
    {s : StageType.{u} α m} (hs : t.toClass.restrictFace f = some s.toClass) :
    ∃ t' : StageType.{u} α n, t'.toClass = t.toClass ∧ StageType.restrictFace f t' = some s := by
  rw [restrictFace_toClass, Option.map_eq_some_iff] at hs
  obtain ⟨x, hx, hxs⟩ := hs
  obtain ⟨π, hπ⟩ := exists_restrictFace_renameCells t f hx (toClass_eq_toClass_iff.mp hxs)
  exact ⟨_, toClass_renameCells t π, hπ⟩

/-- **The classes fixed by a projection** to a stage `γ ≤ ω₁` that is zero or a limit are those
whose labels lie at stage `γ` ([AFK26, Definition 4.16]: `τ(Q_t) = Q_t` exactly when the
truncation of `t` is a renaming of `t`). -/
theorem project_toClass_eq_iff (hγ : Order.IsSuccPrelimit γ) (hγω : γ ≤ ω₁)
    (t : StageType.{u} ω₁ n) :
    t.toClass.project hγ = t.toClass ↔ ∀ d, Label.AtStage γ (t.label d) := by
  classical
  rw [project_toClass, toClass_eq_toClass_iff]
  constructor
  · intro h
    obtain ⟨c, σ, hσ⟩ := h.symm
    have hc : c = t.card := congrArg (fun s : StageType.{u} ω₁ n ↦ s.card) hσ
    subst hc
    have hl (d : Fin t.card) : t.label (σ d) = Label.reduce γ (t.label d) :=
      (label_congr hσ rfl).trans (t.label_project hγ hγω d)
    set A := univ.filter fun d ↦ t.label d = ⊤
    set B := univ.filter fun d ↦ Label.reduce γ (t.label d) = ⊤
    have hAB : A ⊆ B := fun d hd ↦ by
      rw [mem_filter] at hd ⊢
      rw [hd.2]
      exact ⟨hd.1, Label.reduce_top⟩
    have hcard : #B ≤ #A := by
      refine Finset.card_le_card_of_injOn σ (fun d hd ↦ ?_) σ.injective.injOn
      rw [mem_coe, mem_filter] at hd ⊢
      exact ⟨mem_univ _, (hl d).trans hd.2⟩
    have hBA : B = A := (Finset.eq_of_subset_of_card_le hAB hcard).symm
    intro d
    by_contra hd
    rw [Label.AtStage, not_or, not_lt] at hd
    have hdB : d ∈ B := mem_filter.mpr ⟨mem_univ _, Label.reduce_eq_top_iff.mpr hd.1⟩
    rw [hBA, mem_filter] at hdB
    exact hd.2 hdB.2
  · intro ht
    rw [(t.project_eq_self_iff hγ hγω).mpr ht]
    exact IsCellRenaming.refl t

end TemplateClass

end

end VaughtConjecture

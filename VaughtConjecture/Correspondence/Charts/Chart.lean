/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Substructures
import VaughtConjecture.Correspondence.Charts.RenamingFaces
import VaughtConjecture.Realization.Expansion

/-!
# The charts of [AFK26] as relational structures

Numbering as in the draft of [AFK26] dated 10 October 2026.

**The language.**  [AFK26, Definitions 4.12, 4.15 and 4.17]: `L_a = {P_n}_{n ≥ 1}`,
`L_b[L] = {Q_t}_{t ∈ L}` with `Q_t` of arity `n` for `t` on `[n]`, and
`L_c[L] = L_a ∪ {R_t : t ∈ L, τ₀(Q_t) = Q_t}`.  The template system `L` has exactly one template
in each cell-renaming class of finite legal templates on `[n]` ([AFK26, Proposition 4.30] and
Definition 4.11); by `StageType.isLegalTemplate_omega_one_iff_of_le` and the construction of
`VaughtConjecture.Correspondence.Charts.Template`, these classes are the classes, under
`StageType.IsCellRenaming`, of the strongly coded legal stage types at stage `ω₁` on `n ≥ 1`
points (`TemplateClass n`, `TemplateClass.IsLegal`).  So `templateChartLanguage` has, in each
arity `k ≥ 1`, one symbol `P_k` (`TemplateSymbol.plan`), one symbol `Q_c` for each legal class `c`
(`TemplateSymbol.base`), and one symbol `R_c` for each legal class `c` fixed by the truncation at
`ω`, that is, with labels at stage `ω` (`TemplateSymbol.cap`); there are no function symbols and no
symbols of arity `0`.  The symbols are indexed by the classes themselves, not by chosen
representatives; choosing the representatives is choosing `L`.

**The chart of a stage type.**  [AFK26, Definition 4.18] determines the structure on the points of
a template `t`: `P_k` holds of distinct points spanning a closed set, `Q_{t*}` of a tuple `x` when
`t*` is the class of the restriction of `t` to the points of `x`, transported along `x`, and
`R_{t⁻}` when moreover `t⁻` is the class of its truncation at `ω`.  For a stage type `t` this
restriction is the face map `StageType.restrictFace x t` (defined exactly at the closed faces), so
on the points `Fin n` of `t` the relation of a symbol holds of a tuple `x` exactly when `x` is
injective, its face is defined, and the symbol reads the class of the face
(`TemplateSymbol.Reads`).  This is `StageType.TemplateChart t` (`StageType.relMap_templateChart`).
It depends only on the class of `t` (`StageType.templateChartEquivRename`).

**Charts and the category `C_β[L]`.**  [AFK26, Definition 4.31]: a chart on `t` is a finite
structure `M` with an enumeration `a : [n] → M` such that every relation holds of `a ∘ x` exactly
when the diagram of `t` says so (`IsChartOn t M a`); `C_β[L]` consists of the charts on templates
`t` with `trunc_{ω + ω · β}(t) = t`, that is, `Label.reduce (blockStage β)` fixes every label
(`IsTemplateChart β M`).  Such charts are nonempty: the templates of [AFK26] have nonempty
underlying sets.

**Embeddings** (`StageType.templateChartEmbedding`, `StageType.exists_restrictFace_of_embedding`).
A map of points `f : Fin m ↪ Fin n` is an embedding of the chart of `s` into the chart of `t`
exactly when the face of `t` along `f` is defined and is a cell renaming of `s`.  The point map is
`f` itself; only the cells of the face are identified with those of `s` up to renaming, and this
is the only place where renaming enters.  No global numbering of the cells of charts is chosen.

**HP, JEP, AP** ([AFK26, Proposition 4.32], `IsTemplateChart.hereditary`,
`IsTemplateChart.jointEmbedding`, `IsTemplateChart.amalgamation`), at every `β < ω₁`, with no
hypothesis on coatom extensions: the native constructions are
`StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit` and
`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit` at the block stage `ω + ω · β`, which
is zero or a limit (`isSuccPrelimit_blockStage`); they need no countability of the stage.  The
hypothesis `β < ω₁` places the block stage below the label universe `ω₁` of the language, where
the amalgam is read (`StageType.castLE`).  For AP, the two embeddings of the common chart give two
faces that are cell renamings of each other; one of the two outer types is renamed so that the
faces are equal (`StageType.exists_restrictFace_renameCells`) before the native amalgamation, and
renaming does not change the chart.  The joint embedding passes through the face on no points
internally; no chart on no points is formed.

**Not treated here.**  The Fraïssé limit of `C_β[L]`, the density sentence and the models of
[AFK26, §4], and [AFK26, Propositions 4.34 and 4.35].  The hull language of
`VaughtConjecture.Language.HullOperations` is not used.
-/

universe u v w x

namespace VaughtConjecture

open FirstOrder Language Structure Finset Ordinal

noncomputable section

/-! ### Classes of templates and the language -/

/-- The stage types at stage `ω₁` on `k` points up to cell renaming: the templates of [AFK26] on
`[k]` with labels in `{-∞} ∪ ω₁ ∪ {∞}`, up to renaming. -/
abbrev TemplateClass (k : ℕ) : Type (u + 1) :=
  Quotient (StageType.cellRenamingSetoid.{u} ω₁ k)

/-- The class of a stage type. -/
abbrev StageType.toClass {k : ℕ} (t : StageType.{u} ω₁ k) : TemplateClass.{u} k :=
  Quotient.mk _ t

/-- Renamings have the same class. -/
theorem StageType.toClass_eq_toClass_iff {k : ℕ} {s t : StageType.{u} ω₁ k} :
    s.toClass = t.toClass ↔ s.IsCellRenaming t :=
  Quotient.eq (r := StageType.cellRenamingSetoid.{u} ω₁ k)

namespace TemplateClass

variable {k : ℕ}

/-- A class is **legal** when its stage types are strongly coded legal: these are the classes of
the legal templates of [AFK26, Definition 4.29]
(`StageType.isLegalTemplate_omega_one_iff_of_le`). -/
def IsLegal (c : TemplateClass.{u} k) : Prop :=
  Quotient.lift (fun t : StageType.{u} ω₁ k ↦ t.IsStronglyCodedLegal) (fun a b h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact propext (StageType.isStronglyCodedLegal_renameCells_iff a σ).symm) c

@[simp] theorem isLegal_toClass (t : StageType.{u} ω₁ k) :
    t.toClass.IsLegal ↔ t.IsStronglyCodedLegal :=
  Iff.rfl

/-- A class is **fixed by `τ₀`** when the labels of its stage types are at stage `ω`; this is
`trunc_ω(t) ≅_ren t` of [AFK26, Definition 4.17] (`TemplateClass.isBase_iff_truncOmega_eq`). -/
def IsBase (c : TemplateClass.{u} k) : Prop :=
  Quotient.lift (fun t : StageType.{u} ω₁ k ↦ ∀ d, Label.AtStage ω (t.label d)) (fun a b h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact propext ⟨fun h d ↦ h (σ d), fun h d ↦ by simpa using h (σ.symm d)⟩) c

/-- The truncation at `ω` of a stage type at `ω₁`, read at `ω₁` ([AFK26, Definition 4.10]). -/
noncomputable def _root_.VaughtConjecture.StageType.truncOmega {k : ℕ}
    (t : StageType.{u} ω₁ k) : StageType.{u} ω₁ k :=
  (t.reduce isSuccLimit_omega0.isSuccPrelimit).castLE omega0_lt_omega_one.le

/-- **The truncation at `ω` of a class** ([AFK26, Definition 4.10]): truncation commutes with
renaming. -/
noncomputable def truncOmega (c : TemplateClass.{u} k) : TemplateClass.{u} k :=
  Quotient.map StageType.truncOmega (fun a b h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact ⟨_, σ, rfl⟩) c

@[simp] theorem truncOmega_toClass (t : StageType.{u} ω₁ k) :
    t.toClass.truncOmega = t.truncOmega.toClass :=
  rfl

/-- **The classes fixed by `τ₀` are the classes with labels at stage `ω`**
([AFK26, Definitions 4.16 and 4.17]: `τ₀(Q_t) = Q_t` exactly when `trunc_ω(t) ≅_ren t`).  A
renaming keeps the number of labels `∞`, and the truncation at `ω` adds one for every label in
`[ω, ∞)`. -/
theorem isBase_iff_truncOmega_eq (c : TemplateClass.{u} k) : c.IsBase ↔ c.truncOmega = c := by
  classical
  induction c using Quotient.inductionOn with | h t => ?_
  change (∀ d, Label.AtStage ω (t.label d)) ↔ t.truncOmega.toClass = t.toClass
  rw [StageType.toClass_eq_toClass_iff]
  constructor
  · intro ht
    have : t.truncOmega = t :=
      StageType.castLE_reduce_of_atStage t isSuccLimit_omega0.isSuccPrelimit _ ht
    rw [this]
    exact StageType.IsCellRenaming.refl t
  · intro h
    obtain ⟨c, σ, hσ⟩ := h.symm
    have hc : c = t.card := congrArg (fun s : StageType.{u} ω₁ k ↦ s.card) hσ
    subst hc
    have hl (d : Fin t.card) : t.label (σ d) = Label.reduce ω (t.label d) :=
      StageType.label_congr hσ rfl
    set A := univ.filter fun d ↦ t.label d = ⊤
    set B := univ.filter fun d ↦ Label.reduce ω (t.label d) = ⊤
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

end TemplateClass

/-- **The relation symbols of arity `k`** of `L_b[L] ∪ L_c[L]` ([AFK26, Definitions 4.12, 4.15 and
4.17]), for `k ≥ 1`. -/
inductive TemplateSymbol (k : ℕ) : Type (u + 1)
  /-- `P_k ∈ L_a`. -/
  | plan (hk : 0 < k)
  /-- `Q_t ∈ L_b[L]`, for the legal class `c` of `t`. -/
  | base (c : TemplateClass.{u} k) (hk : 0 < k) (hc : c.IsLegal)
  /-- `R_t ∈ L_c[L]`, for the legal class `c` of `t`, fixed by `τ₀`. -/
  | cap (c : TemplateClass.{u} k) (hk : 0 < k) (hc : c.IsLegal) (hb : c.IsBase)

/-- **The language `L_b[L] ∪ L_c[L]`** of [AFK26, Definitions 4.12, 4.15 and 4.17]: relational,
with the symbols `TemplateSymbol`. -/
def templateChartLanguage : Language.{0, u + 1} where
  Functions _ := Empty
  Relations := TemplateSymbol.{u}

instance : templateChartLanguage.{u}.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

namespace TemplateSymbol

variable {k : ℕ}

/-- **The reading of a symbol on the class of a face** ([AFK26, Definition 4.18]): `P_k` reads
every face, `Q_c` the faces of class `c`, `R_c` the faces whose truncation at `ω` has class `c`. -/
def Reads : TemplateSymbol.{u} k → TemplateClass.{u} k → Prop
  | plan _, _ => True
  | base c _ _, x => x = c
  | cap c _ _ _, x => x.truncOmega = c

end TemplateSymbol

/-! ### The chart of a stage type -/

namespace StageType

variable {n m k : ℕ}

/-- **The chart of a stage type** at stage `ω₁` on `n` points: its points `Fin n`, as a structure
of `templateChartLanguage`.  A type synonym of `Fin n`, so that the structure is not an instance
on `Fin n`. -/
@[nolint unusedArguments]
def TemplateChart (_t : StageType.{u} ω₁ n) : Type :=
  Fin n

variable (t : StageType.{u} ω₁ n)

instance : Fintype t.TemplateChart := inferInstanceAs (Fintype (Fin n))

instance : DecidableEq t.TemplateChart := inferInstanceAs (DecidableEq (Fin n))

/-- The structure of the chart ([AFK26, Definition 4.18]): a symbol holds of a tuple when the
tuple is injective, its face is defined, and the symbol reads the class of the face. -/
instance : templateChartLanguage.{u}.Structure t.TemplateChart where
  funMap f := Empty.elim f
  RelMap r xs := ∃ h : Function.Injective xs, ∃ s,
    restrictFace ⟨xs, h⟩ t = some s ∧ TemplateSymbol.Reads r s.toClass

/-- The relations of the chart of `t`. -/
theorem relMap_templateChart (r : TemplateSymbol.{u} k) (xs : Fin k → t.TemplateChart) :
    RelMap (L := templateChartLanguage.{u}) r xs ↔ ∃ h : Function.Injective xs, ∃ s,
      restrictFace ⟨xs, h⟩ t = some s ∧ TemplateSymbol.Reads r s.toClass :=
  Iff.rfl

/-! ### Faces of renamings and the chart -/

/-- **The faces of renamings have the same classes.** -/
theorem exists_restrictFace_iff_of_isCellRenaming {s s' : StageType.{u} ω₁ m}
    (hss : s.IsCellRenaming s') (g : Fin k ↪ Fin m) (P : TemplateClass.{u} k → Prop) :
    (∃ x, restrictFace g s' = some x ∧ P x.toClass) ↔
      ∃ x, restrictFace g s = some x ∧ P x.toClass := by
  obtain ⟨_, π, rfl⟩ := hss
  constructor
  · rintro ⟨x', hx', hP⟩
    cases hx : restrictFace g s with
    | none =>
      rw [← restrictFace_renameCells_eq_none_iff s π g, hx'] at hx
      exact absurd hx (by simp)
    | some x =>
      obtain ⟨x'', hx'', hxx''⟩ := restrictFace_renameCells s π g hx
      rw [hx', Option.some_inj] at hx''
      subst hx''
      exact ⟨x, rfl, (toClass_eq_toClass_iff.mpr hxx'') ▸ hP⟩
  · rintro ⟨x, hx, hP⟩
    obtain ⟨x', hx', hxx'⟩ := restrictFace_renameCells s π g hx
    exact ⟨x', hx', (toClass_eq_toClass_iff.mpr hxx') ▸ hP⟩

/-- **Relations along a face map**: if the face of `t` along `f` is a renaming of `s`, a symbol
holds of `f ∘ xs` in the chart of `t` exactly when it holds of `xs` in the chart of `s`. -/
theorem relMap_comp_iff {s s' : StageType.{u} ω₁ m} {f : Fin m ↪ Fin n}
    (hf : restrictFace f t = some s') (hss : s.IsCellRenaming s') (r : TemplateSymbol.{u} k)
    (xs : Fin k → Fin m) :
    RelMap (L := templateChartLanguage.{u}) (M := t.TemplateChart) r (f ∘ xs) ↔
      RelMap (L := templateChartLanguage.{u}) (M := s.TemplateChart) r xs := by
  change (∃ h : Function.Injective (f ∘ xs), ∃ s₀, restrictFace ⟨f ∘ xs, h⟩ t = some s₀ ∧
      TemplateSymbol.Reads r s₀.toClass) ↔ ∃ h : Function.Injective xs, ∃ s₀,
      restrictFace ⟨xs, h⟩ s = some s₀ ∧ TemplateSymbol.Reads r s₀.toClass
  constructor
  · rintro ⟨h, hx⟩
    have hxs : Function.Injective xs := h.of_comp
    have heq : restrictFace ⟨f ∘ xs, h⟩ t = restrictFace ⟨xs, hxs⟩ s' :=
      (restrictFace_trans t f ⟨xs, hxs⟩ hf).symm
    rw [heq] at hx
    exact ⟨hxs, (exists_restrictFace_iff_of_isCellRenaming hss _ _).mp hx⟩
  · rintro ⟨h, hx⟩
    have hfx : Function.Injective (f ∘ xs) := f.injective.comp h
    have heq : restrictFace ⟨f ∘ xs, hfx⟩ t = restrictFace ⟨xs, h⟩ s' :=
      (restrictFace_trans t f ⟨xs, h⟩ hf).symm
    exact ⟨hfx, heq ▸ (exists_restrictFace_iff_of_isCellRenaming hss _ _).mpr hx⟩

/-- **The chart embedding of a face map up to renaming**: if the face of `t` along `f` is a cell
renaming of `s`, the map `f` is an embedding of the chart of `s` into the chart of `t`. -/
def templateChartEmbedding {s s' : StageType.{u} ω₁ m} {f : Fin m ↪ Fin n}
    (hf : restrictFace f t = some s') (hss : s.IsCellRenaming s') :
    s.TemplateChart ↪[templateChartLanguage.{u}] t.TemplateChart where
  toEmbedding := f
  map_fun' g := Empty.elim g
  map_rel' r xs := relMap_comp_iff t hf hss r xs

@[simp] theorem templateChartEmbedding_apply {s s' : StageType.{u} ω₁ m} {f : Fin m ↪ Fin n}
    (hf : restrictFace f t = some s') (hss : s.IsCellRenaming s') (y : s.TemplateChart) :
    t.templateChartEmbedding hf hss y = f y :=
  rfl

/-- **The chart depends only on the class**: the chart of a renaming is the chart of the type, by
the identity of the points. -/
def templateChartEquivRename {k' : ℕ} (π : Fin k' ≃ Fin t.card) :
    (t.renameCells π).TemplateChart ≃[templateChartLanguage.{u}] t.TemplateChart where
  toEquiv := Equiv.refl _
  map_fun' g := Empty.elim g
  map_rel' r xs := by
    change (∃ h : Function.Injective xs, ∃ s₀, restrictFace ⟨xs, h⟩ t = some s₀ ∧
      TemplateSymbol.Reads r s₀.toClass) ↔ ∃ h : Function.Injective xs, ∃ s₀,
      restrictFace ⟨xs, h⟩ (t.renameCells π) = some s₀ ∧ TemplateSymbol.Reads r s₀.toClass
    exact exists_congr fun _ ↦
      (exists_restrictFace_iff_of_isCellRenaming ⟨_, π, rfl⟩ _ _).symm

/-- **Embeddings of charts are face maps up to renaming** ([AFK26, Definition 4.31], morphisms of
`C_β[L]`): an embedding of the chart of a strongly coded legal `s` into the chart of `t` has as
its point map a face map of `t` whose face is a cell renaming of `s`. -/
theorem exists_restrictFace_of_embedding {s : StageType.{u} ω₁ m} (hs : s.IsStronglyCodedLegal)
    (φ : s.TemplateChart ↪[templateChartLanguage.{u}] t.TemplateChart) :
    ∃ s', restrictFace φ.toEmbedding t = some s' ∧ s.IsCellRenaming s' := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (t.isSome_restrictFace_of_zero φ.toEmbedding)
    exact ⟨s', hs', eq_of_zero s s' ▸ IsCellRenaming.refl s⟩
  · have hrel := (φ.map_rel (TemplateSymbol.base s.toClass hm hs) id).mpr
      ⟨Function.injective_id, s, restrictFace_refl s, rfl⟩
    obtain ⟨_, s', hs', hc⟩ := hrel
    exact ⟨s', hs', (toClass_eq_toClass_iff.mp hc.symm)⟩

end StageType

/-! ### Charts on templates and the category `C_β[L]` -/

section Charts

open StageType

variable {n m : ℕ} {M : Type v} [templateChartLanguage.{u}.Structure M]
  {N : Type w} [templateChartLanguage.{u}.Structure N]
  {R : Type x} [templateChartLanguage.{u}.Structure R]

/-- **A chart on `t`** [AFK26, Definition 4.31]: the enumeration `a` of `M` by the points of `t`
carries every relation of the chart of `t` to `M` and back. -/
def IsChartOn (t : StageType.{u} ω₁ n) (M : Type v) [templateChartLanguage.{u}.Structure M]
    (a : Fin n ≃ M) : Prop :=
  ∀ {k} (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n),
    RelMap (L := templateChartLanguage.{u}) r (a ∘ xs) ↔
      RelMap (L := templateChartLanguage.{u}) (M := t.TemplateChart) r xs

/-- **The category `C_β[L]`** [AFK26, Definition 4.31], as a class of structures: the charts on
strongly coded legal stage types (the legal templates) at stage `ω₁` on `n ≥ 1` points whose
labels are fixed by the truncation at `ω + ω · β`. -/
def IsTemplateChart (β : Ordinal.{u}) (M : Type v) [templateChartLanguage.{u}.Structure M] :
    Prop :=
  ∃ (n : ℕ) (t : StageType.{u} ω₁ n), 0 < n ∧ t.IsStronglyCodedLegal ∧
    (∀ d, Label.reduce (blockStage β) (t.label d) = t.label d) ∧ ∃ a : Fin n ≃ M, IsChartOn t M a

/-- The chart of a stage type is a chart on it, by the identity. -/
theorem isChartOn_templateChart (t : StageType.{u} ω₁ n) :
    IsChartOn t t.TemplateChart (Equiv.refl _) :=
  fun _ _ ↦ Iff.rfl

/-- A chart on `t` is isomorphic to the chart of `t`, by its enumeration. -/
def IsChartOn.equiv {t : StageType.{u} ω₁ n} {a : Fin n ≃ M} (h : IsChartOn t M a) :
    t.TemplateChart ≃[templateChartLanguage.{u}] M where
  toEquiv := a
  map_fun' g := Empty.elim g
  map_rel' r xs := h r xs

@[simp] theorem IsChartOn.equiv_apply {t : StageType.{u} ω₁ n} {a : Fin n ≃ M}
    (h : IsChartOn t M a) (y : Fin n) : h.equiv y = a y :=
  rfl

/-- The chart of a strongly coded legal stage type on `n ≥ 1` points with labels fixed by the
truncation at `ω + ω · β` is in `C_β[L]`. -/
theorem isTemplateChart_templateChart {β : Ordinal.{u}} {t : StageType.{u} ω₁ n} (hn : 0 < n)
    (ht : t.IsStronglyCodedLegal) (hβ : ∀ d, Label.reduce (blockStage β) (t.label d) = t.label d) :
    IsTemplateChart β t.TemplateChart :=
  ⟨n, t, hn, ht, hβ, _, isChartOn_templateChart t⟩

/-! ### The hereditary property -/

/-- A set of points of `M` is **closed** ([AFK26, Definition 4.12]) when it is enumerated by a
tuple satisfying `P_k`; the empty set is not considered here. -/
def IsClosedNonempty (A : Set M) : Prop :=
  ∃ (k : ℕ) (hk : 0 < k) (xs : Fin k → M),
    RelMap (L := templateChartLanguage.{u}) (TemplateSymbol.plan hk) xs ∧ Set.range xs = A

/-- **The hereditary property** [AFK26, Proposition 4.32]: the restriction of a chart in
`C_β[L]` to a nonempty closed set of its points is in `C_β[L]`.  No hypothesis on `β`. -/
theorem IsTemplateChart.hereditary {β : Ordinal.{u}} (hM : IsTemplateChart β M)
    (S : templateChartLanguage.{u}.Substructure M) (hS : IsClosedNonempty (S : Set M)) :
    IsTemplateChart β S := by
  obtain ⟨n, t, -, ht, hβ, a, hta⟩ := hM
  obtain ⟨k, hk, xs, hxs, hrange⟩ := hS
  -- the tuple, read in the chart of `t`
  have hP := (hta (TemplateSymbol.plan hk) (a.symm ∘ xs)).mp (by
    simpa [Function.comp_def] using hxs)
  obtain ⟨hinj, s, hs, -⟩ := hP
  set g : Fin k ↪ Fin n := ⟨a.symm ∘ xs, hinj⟩
  have hxinj : Function.Injective xs := fun i j hij ↦ hinj (congrArg a.symm hij)
  have hmem (i : Fin k) : xs i ∈ S := by
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨i, rfl⟩
  let b : Fin k ≃ S := Equiv.ofBijective (fun i ↦ ⟨xs i, hmem i⟩)
    ⟨fun i j hij ↦ hxinj (congrArg Subtype.val hij), fun y ↦ by
      obtain ⟨i, hi⟩ : (y : M) ∈ Set.range xs := by rw [hrange]; exact y.2
      exact ⟨i, Subtype.ext hi⟩⟩
  refine ⟨k, s, hk, ⟨ht.1.restrictFace g hs, isStronglyCoded_of_restrictFace hs ht.2⟩,
    fun d ↦ ?_, b, fun r ys ↦ ?_⟩
  · obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t g).mp hs
    exact hβ _
  · have h1 := hta r (g ∘ ys)
    have h2 := t.relMap_comp_iff hs (IsCellRenaming.refl s) r ys
    refine Iff.trans ?_ (h1.trans h2)
    change RelMap (L := templateChartLanguage.{u}) (M := M) r (fun i ↦ ((b (ys i) : S) : M)) ↔
      RelMap (L := templateChartLanguage.{u}) (M := M) r (a ∘ (g ∘ ys))
    have : (fun i ↦ ((b (ys i) : S) : M)) = a ∘ (g ∘ ys) := funext fun i ↦ by
      change xs (ys i) = a (a.symm (xs (ys i)))
      exact (a.apply_symm_apply _).symm
    rw [this]

/-! ### Joint embedding and amalgamation -/

/-- The block stage of a countable index is at most `ω₁`. -/
private theorem blockStage_le_omega_one {β : Ordinal.{u}} (hβ : β < ω₁) : blockStage β ≤ ω₁ :=
  (blockStage_lt_omega_one hβ).le

/-- A stage type at stage `ω₁` with labels fixed by the truncation at `ω + ω · β`, reduced to
that stage. -/
private noncomputable def toBlock {β : Ordinal.{u}} {n : ℕ} (t : StageType.{u} ω₁ n) :
    StageType.{u} (blockStage β) n :=
  t.reduce (isSuccPrelimit_blockStage β)

private theorem castLE_toBlock {β : Ordinal.{u}} (hβ : β < ω₁) {n : ℕ} (t : StageType.{u} ω₁ n)
    (ht : ∀ d, Label.reduce (blockStage β) (t.label d) = t.label d) :
    (toBlock (β := β) t).castLE (blockStage_le_omega_one hβ) = t :=
  StageType.castLE_reduce_of_atStage t _ _ fun d ↦ Label.reduce_eq_self_iff.mp (ht d)

private theorem isStronglyCodedLegal_toBlock {β : Ordinal.{u}} {n : ℕ} {t : StageType.{u} ω₁ n}
    (ht : t.IsStronglyCodedLegal) : (toBlock (β := β) t).IsStronglyCodedLegal :=
  ht

/-- **A chart into the chart of a stage type read at `ω₁`** after an amalgamation at the block
stage: the face of the cast type is the cast face. -/
private theorem restrictFace_castLE_toBlock {β : Ordinal.{u}} (hβ : β < ω₁) {n N : ℕ}
    {Q : StageType.{u} (blockStage β) N} {P : StageType.{u} ω₁ n} {i : Fin n ↪ Fin N}
    (hP : ∀ d, Label.reduce (blockStage β) (P.label d) = P.label d)
    (hi : restrictFace i Q = some (toBlock P)) :
    restrictFace i (Q.castLE (blockStage_le_omega_one hβ)) = some P := by
  rw [StageType.restrictFace_castLE, hi, Option.map_some, castLE_toBlock hβ P hP]

/-- **Joint embedding** [AFK26, Proposition 4.32]: any two charts in `C_β[L]` embed into the
chart of one strongly coded legal stage type, which is in `C_β[L]`.  The native joint embedding
is at the block stage `ω + ω · β`, which is zero or a limit; the hypothesis `β < ω₁` places it
below `ω₁`. -/
theorem IsTemplateChart.jointEmbedding {β : Ordinal.{u}} (hβ : β < ω₁) (hM : IsTemplateChart β M)
    (hN : IsTemplateChart β N) :
    ∃ (K : ℕ) (Q : StageType.{u} ω₁ K), IsTemplateChart β Q.TemplateChart ∧
      Nonempty (M ↪[templateChartLanguage.{u}] Q.TemplateChart) ∧
      Nonempty (N ↪[templateChartLanguage.{u}] Q.TemplateChart) := by
  obtain ⟨n, P, hn, hP, hPβ, a, hPa⟩ := hM
  obtain ⟨m, T, -, hT, hTβ, b, hTb⟩ := hN
  obtain ⟨K, Q, i, j, hQ, hQP, hQT⟩ :=
    StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit (isSuccPrelimit_blockStage β)
      (isStronglyCodedLegal_toBlock (β := β) hP) (isStronglyCodedLegal_toBlock (β := β) hT)
  set Q' := Q.castLE (blockStage_le_omega_one hβ)
  have hQ'P := restrictFace_castLE_toBlock hβ hPβ hQP
  have hQ'T := restrictFace_castLE_toBlock hβ hTβ hQT
  have hK : 0 < K := hn.trans_le (by simpa using Fintype.card_le_of_embedding i)
  refine ⟨K, Q', isTemplateChart_templateChart hK hQ (fun d ↦ ?_),
    ⟨(Q'.templateChartEmbedding hQ'P (IsCellRenaming.refl P)).comp hPa.equiv.symm.toEmbedding⟩,
    ⟨(Q'.templateChartEmbedding hQ'T (IsCellRenaming.refl T)).comp hTb.equiv.symm.toEmbedding⟩⟩
  exact (Q.atStage d).reduce_eq

/-- **Amalgamation** [AFK26, Proposition 4.32]: two embeddings of a chart in `C_β[L]` into charts
in `C_β[L]` are amalgamated, with commuting embeddings, in the chart of one strongly coded legal
stage type, which is in `C_β[L]`.  The point maps are composed literally; the two faces of the
common chart are cell renamings of each other, and one outer type is renamed before the native
amalgamation at the block stage `ω + ω · β`. -/
theorem IsTemplateChart.amalgamation {β : Ordinal.{u}} (hβ : β < ω₁) (hM : IsTemplateChart β M)
    (hN : IsTemplateChart β N) (hR : IsTemplateChart β R)
    (f : M ↪[templateChartLanguage.{u}] N) (g : M ↪[templateChartLanguage.{u}] R) :
    ∃ (K : ℕ) (Q : StageType.{u} ω₁ K), IsTemplateChart β Q.TemplateChart ∧
      ∃ (i : N ↪[templateChartLanguage.{u}] Q.TemplateChart)
        (j : R ↪[templateChartLanguage.{u}] Q.TemplateChart), i.comp f = j.comp g := by
  obtain ⟨k, p, -, hp, -, a, hpa⟩ := hM
  obtain ⟨n, P, hn, hP, hPβ, b, hPb⟩ := hN
  obtain ⟨m, T, -, hT, hTβ, c, hTc⟩ := hR
  -- the two point maps, as embeddings of charts of stage types
  let φ := hPb.equiv.symm.toEmbedding.comp (f.comp hpa.equiv.toEmbedding)
  let ψ := hTc.equiv.symm.toEmbedding.comp (g.comp hpa.equiv.toEmbedding)
  let φ' : Fin k ↪ Fin n := φ.toEmbedding
  let ψ' : Fin k ↪ Fin m := ψ.toEmbedding
  obtain ⟨p₁, hp₁, hpp₁⟩ := P.exists_restrictFace_of_embedding hp φ
  obtain ⟨p₂, hp₂, hpp₂⟩ := T.exists_restrictFace_of_embedding hp ψ
  have hp₁' : restrictFace φ' P = some p₁ := hp₁
  have hp₂' : restrictFace ψ' T = some p₂ := hp₂
  -- rename `T` so that its face is `p₁`
  obtain ⟨π, hπ⟩ := T.exists_restrictFace_renameCells ψ' hp₂' (hpp₂.symm.trans hpp₁)
  set T' := T.renameCells π
  have hT' : T'.IsStronglyCodedLegal := (T.isStronglyCodedLegal_renameCells_iff π).mpr hT
  have hT'β : ∀ d, Label.reduce (blockStage β) (T'.label d) = T'.label d := fun d ↦ hTβ (π d)
  -- the native amalgamation at the block stage
  have hp₁β : restrictFace φ' (toBlock (β := β) P) = some (toBlock p₁) := by
    rw [toBlock, StageType.restrictFace_reduce, hp₁', Option.map_some]
    rfl
  have hp₂β : restrictFace ψ' (toBlock (β := β) T') = some (toBlock p₁) := by
    rw [toBlock, StageType.restrictFace_reduce, hπ, Option.map_some]
    rfl
  obtain ⟨K, Q, i, j, hQ, hQP, hQT, hcomm⟩ :=
    StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit (isSuccPrelimit_blockStage β)
      (isStronglyCodedLegal_toBlock (β := β) hP) (isStronglyCodedLegal_toBlock (β := β) hT')
      hp₁β hp₂β
  set Q' := Q.castLE (blockStage_le_omega_one hβ)
  have hQ'P := restrictFace_castLE_toBlock hβ hPβ hQP
  have hQ'T := restrictFace_castLE_toBlock hβ hT'β hQT
  have hK : 0 < K := hn.trans_le (by simpa using Fintype.card_le_of_embedding i)
  refine ⟨K, Q', isTemplateChart_templateChart hK hQ (fun d ↦ (Q.atStage d).reduce_eq),
    (Q'.templateChartEmbedding hQ'P (IsCellRenaming.refl P)).comp hPb.equiv.symm.toEmbedding,
    ((Q'.templateChartEmbedding hQ'T (IsCellRenaming.refl T')).comp
      (T.templateChartEquivRename π).symm.toEmbedding).comp hTc.equiv.symm.toEmbedding, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hpa.equiv.surjective y
  exact congrArg (fun e : Fin k ↪ Fin K ↦ e z) hcomm

end Charts

end

end VaughtConjecture

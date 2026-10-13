/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Basic
import VaughtConjecture.Correspondence.Charts.TemplateClass
import VaughtConjecture.Realization.Expansion

/-!
# The charts of [AFK26] as relational structures

Numbering as in the current draft of [AFK26]; the clauses were compared with the text of the
draft of 10 October 2026, which has the same numbers.

**The language** (`templateLanguage`, `TemplateSymbol`).  [AFK26, Definitions 4.12, 4.15 and
4.17]: `L_a = {P_n}_{n ≥ 1}`, `L_b[L] = {Q_t}_{t ∈ L}` with `Q_t` of arity `n` for `t` on `[n]`, and
`L_c[L] = L_a ∪ {R_t : t ∈ L, τ₀(Q_t) = Q_t}`.  The template system `L` keeps exactly one template
in each cell-renaming class of finite legal templates on `[n]` ([AFK26, Definition 4.11 and
Proposition 4.30]); by `TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate` and the
construction of `VaughtConjecture.Correspondence.Charts.Template`, these are the strongly coded
legal classes at stage `ω₁` on `n ≥ 1` points (`LegalClass n`).  So `templateLanguage` has, in each
arity `n ≥ 1`, the symbol `P_n` (`TemplateSymbol.closed`), one symbol `Q_c` for each legal class
`c` (`TemplateSymbol.invariant`), and one symbol `R_c` for each legal class with `τ₀(c) = c`, the
projection to `ω + ω · 0 = ω` (`TemplateSymbol.base`); there are no function symbols and no symbols
of arity `0`.  One alphabet serves every rank.  The symbols are indexed by the classes themselves;
choosing a representative in each class is choosing `L`.

**The chart of a stage type** (`StageType.Holds`, `StageType.TemplateChart`).  [AFK26,
Definition 4.18] determines the structure on the points of a template `t`: `P_k` holds of
distinct points spanning a closed set, `Q_{t*}` of a tuple `x` when `t*` is the class of the
restriction of `t` to the points of `x`, transported along `x`, and `R_{t⁻}` when moreover `t⁻` is
the class of its truncation at `ω`.  For a stage type the restriction is the face map
`StageType.restrictFace x t`, defined exactly at the closed faces; its class is read at `ω₁`
(`StageType.globalClass`).  So a symbol holds of a tuple exactly when the tuple is injective, its
face is defined, and the symbol reads the class of the face (`TemplateSymbol.Reads`).  The chart
depends only on the class of `t` (`StageType.templateChartEquivRename`).

**Charts and `C_β[L]`** (`IsTemplateChart β G`).  [AFK26, Definition 4.31]: a chart is a finite
structure `G` on `M` with an enumeration `e : Fin n ≃ M` of its points by a template `t ∈ L` such
that every symbol holds of `e ∘ xs` exactly when it holds of `xs` in the chart of `t`; `C_β[L]`
takes the templates with `trunc_{ω + ω · β}(t) = t`.  Here `t` is a stage type at the block stage
`ω + ω · β` that is a legal template with labels in `{-∞} ∪ ω₁ ∪ {∞}` (`IsLegalTemplate ω₁`), on
`n ≥ 1` points: the templates of [AFK26] have nonempty underlying sets.

**Embeddings** (`StageType.embeddingEquivFace`): at a stage at most `ω₁`, the embeddings of the
chart of a strongly coded legal `s` into the chart of `t` are exactly the maps of points `f` along
which the class of `t` has the face class of `s`, with the same point map.  Only the cells of the
face are identified with those of `s`, up to renaming; no global numbering of cells is chosen.

**HP, JEP, AP** [AFK26, Proposition 4.32] (`IsTemplateChart.hereditary`,
`IsTemplateChart.jointEmbedding`, `IsTemplateChart.amalgamation`), with no hypothesis on coatom
extensions.  They rest on the native theorems `StageType.IsLegal.restrictFace` with
`StageType.isStronglyCoded_of_restrictFace` (HP),
`StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit` (JEP) and
`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit` (AP) at the block stage `ω + ω · β`,
which is zero or a limit (`isSuccPrelimit_blockStage`); those need no countability of the stage.
The dictionary is: the legal templates are the strongly coded legal stage types
(`StageType.isLegalTemplate_omega_one_iff`), the charts are the charts of stage types
(`IsTemplateChart`), and embeddings are face maps up to renaming (`StageType.embeddingEquivFace`).
HP holds at every `β`.  For JEP and AP the hypothesis `β < ω₁` (the printed range `β ∈ ω₁`) puts
the labels of the amalgam, at the block stage, in the label universe `{-∞} ∪ ω₁ ∪ {∞}` of the
legal templates, and identifies classes at `ω₁` with classes at the block stage
(`StageType.globalClass_eq_iff`).  For AP the two embeddings of the common chart give two faces
that are cell renamings of each other; one outer type is renamed so that the faces are equal
(`StageType.exists_restrictFace_renameCells`) before the native amalgamation, and renaming does not
change the chart.  JEP passes through the face on no points internally; no chart on no points is
formed.

**Deferred.**  The sublanguage `L_c[L]` of `templateLanguage` (the symbols `P_n` and `R_t`) and
the reduct of a structure to it, the interface that the later comparison of the sentence `σ[L]`
uses, are not defined here.

**Not treated here.**  The Fraïssé limit of `C_β[L]`, the density sentence and the models of
[AFK26, §4], and [AFK26, Propositions 4.34 and 4.35].  The hull language of
`VaughtConjecture.Language.HullOperations` is not used.
-/

universe u v w x

namespace VaughtConjecture

open FirstOrder Language Structure Finset Ordinal

noncomputable section

/-! ### The language -/

/-- **The legal classes** on `n` points: the classes at stage `ω₁` of the strongly coded legal stage
types, which are the classes of the legal templates of [AFK26, Definition 4.29] with labels in
`{-∞} ∪ ω₁ ∪ {∞}`. -/
abbrev LegalClass (n : ℕ) : Type (u + 1) :=
  {c : TemplateClass.{u} ω₁ n // c.IsStronglyCodedLegal}

/-- **The relation symbols** of `L_b[L] ∪ L_c[L]` ([AFK26, Definitions 4.12, 4.15 and 4.17]). -/
inductive TemplateSymbol : ℕ → Type (u + 1)
  /-- `P_n ∈ L_a`. -/
  | closed {n : ℕ} (hn : 0 < n) : TemplateSymbol n
  /-- `Q_t ∈ L_b[L]`, for the legal class `c` of `t`. -/
  | invariant {n : ℕ} (c : LegalClass.{u} n) (hn : 0 < n) : TemplateSymbol n
  /-- `R_t ∈ L_c[L]`, for the legal class `c` of `t` with `τ₀(Q_t) = Q_t`. -/
  | base {n : ℕ} (c : LegalClass.{u} n) (h0 : c.1.project (isSuccPrelimit_blockStage 0) = c.1)
      (hn : 0 < n) : TemplateSymbol n

/-- **The language `L_b[L] ∪ L_c[L]`** of [AFK26, Definitions 4.12, 4.15 and 4.17]: relational,
with the symbols `TemplateSymbol`. -/
def templateLanguage : Language.{0, u + 1} where
  Functions _ := Empty
  Relations := TemplateSymbol.{u}

instance : templateLanguage.{u}.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- **The reading of a symbol on the class of a face** ([AFK26, Definition 4.18]): `P_k` reads
every face, `Q_c` the faces of class `c`, and `R_c` the faces whose truncation at `ω` has class
`c`. -/
def TemplateSymbol.Reads {k : ℕ} : TemplateSymbol.{u} k → TemplateClass.{u} ω₁ k → Prop
  | closed _, _ => True
  | invariant c _, x => x = c.1
  | base c _ _, x => x.project (isSuccPrelimit_blockStage 0) = c.1

/-! ### The chart of a stage type -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **The relations of the chart of `t`** ([AFK26, Definition 4.18]): a symbol holds of a tuple
when the tuple is injective, its face is defined, and the symbol reads the class at `ω₁` of the
face. -/
def Holds (t : StageType.{u} α n) (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n) : Prop :=
  ∃ h : Function.Injective xs, ∃ s, restrictFace ⟨xs, h⟩ t = some s ∧ r.Reads s.globalClass

/-- **The chart of a stage type**: its points `Fin n`, a structure of `templateLanguage` with the
relations `Holds`.  A type synonym of `Fin n`, so that the structure is not an instance on
`Fin n`. -/
@[nolint unusedArguments]
def TemplateChart (_t : StageType.{u} α n) : Type :=
  Fin n

variable (t : StageType.{u} α n)

instance : Fintype t.TemplateChart := inferInstanceAs (Fintype (Fin n))

instance : DecidableEq t.TemplateChart := inferInstanceAs (DecidableEq (Fin n))

instance : templateLanguage.{u}.Structure t.TemplateChart where
  funMap f := Empty.elim f
  RelMap r xs := t.Holds r xs

/-- The relations of the chart of `t` are `Holds`. -/
theorem relMap_templateChart (r : TemplateSymbol.{u} k) (xs : Fin k → t.TemplateChart) :
    RelMap (L := templateLanguage.{u}) r xs ↔ t.Holds r xs :=
  Iff.rfl

/-- **The faces of renamings have the same classes.** -/
theorem exists_restrictFace_iff_of_isCellRenaming {s s' : StageType.{u} α m}
    (hss : s.IsCellRenaming s') (g : Fin k ↪ Fin m) (P : TemplateClass.{u} ω₁ k → Prop) :
    (∃ x, restrictFace g s' = some x ∧ P x.globalClass) ↔
      ∃ x, restrictFace g s = some x ∧ P x.globalClass := by
  obtain ⟨_, π, rfl⟩ := hss
  constructor
  · rintro ⟨x', hx', hP⟩
    cases hx : restrictFace g s with
    | none =>
      rw [← restrictFace_renameCells_eq_none_iff s π g, hx'] at hx
      exact absurd hx (by simp)
    | some x =>
      obtain ⟨x'', hx'', ⟨_, σ, rfl⟩⟩ := restrictFace_renameCells s π g hx
      rw [hx', Option.some_inj] at hx''
      subst hx''
      exact ⟨x, rfl, (globalClass_renameCells x σ) ▸ hP⟩
  · rintro ⟨x, hx, hP⟩
    obtain ⟨x', hx', ⟨_, σ, rfl⟩⟩ := restrictFace_renameCells s π g hx
    exact ⟨_, hx', (globalClass_renameCells x σ).symm ▸ hP⟩

/-- **Relations along a face map up to renaming**: if the face of `t` along `f` is a renaming of
`s`, a symbol holds of `f ∘ xs` in the chart of `t` exactly when it holds of `xs` in the chart of
`s`. -/
theorem holds_comp_iff {s s' : StageType.{u} α m} {f : Fin m ↪ Fin n}
    (hf : restrictFace f t = some s') (hss : s.IsCellRenaming s') (r : TemplateSymbol.{u} k)
    (xs : Fin k → Fin m) : t.Holds r (f ∘ xs) ↔ s.Holds r xs := by
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

/-- **The embedding of charts of a face map up to renaming**: if the face of `t` along `f` is a
cell renaming of `s`, the map `f` is an embedding of the chart of `s` into the chart of `t`. -/
def templateChartEmbedding {s s' : StageType.{u} α m} {f : Fin m ↪ Fin n}
    (hf : restrictFace f t = some s') (hss : s.IsCellRenaming s') :
    s.TemplateChart ↪[templateLanguage.{u}] t.TemplateChart where
  toEmbedding := f
  map_fun' g := Empty.elim g
  map_rel' r xs := t.holds_comp_iff hf hss r xs

@[simp] theorem templateChartEmbedding_apply {s s' : StageType.{u} α m} {f : Fin m ↪ Fin n}
    (hf : restrictFace f t = some s') (hss : s.IsCellRenaming s') (y : s.TemplateChart) :
    t.templateChartEmbedding hf hss y = f y :=
  rfl

/-- **The chart depends only on the class**: the chart of a renaming is the chart of the type, by
the identity of the points. -/
def templateChartEquivRename {k' : ℕ} (π : Fin k' ≃ Fin t.card) :
    (t.renameCells π).TemplateChart ≃[templateLanguage.{u}] t.TemplateChart where
  toEquiv := Equiv.refl _
  map_fun' g := Empty.elim g
  map_rel' _ _ := exists_congr fun _ ↦
    (exists_restrictFace_iff_of_isCellRenaming ⟨_, π, rfl⟩ _ _).symm

/-- **The point map of an embedding of charts is a face map up to renaming**: an embedding of the
chart of a strongly coded legal `s` into the chart of `t` has a face of `t` with the class of `s`
at `ω₁` along its point map. -/
theorem exists_restrictFace_of_embedding {s : StageType.{u} α m} (hs : s.IsStronglyCodedLegal)
    (φ : s.TemplateChart ↪[templateLanguage.{u}] t.TemplateChart) :
    ∃ s', restrictFace φ.toEmbedding t = some s' ∧ s'.globalClass = s.globalClass := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (t.isSome_restrictFace_of_zero φ.toEmbedding)
    exact ⟨s', hs', by rw [eq_of_zero s s']⟩
  · have hrel := (φ.map_rel (TemplateSymbol.invariant ⟨s.globalClass, hs⟩ hm) id).mpr
      ⟨Function.injective_id, s, restrictFace_refl s, rfl⟩
    obtain ⟨_, s', hs', hc⟩ := hrel
    exact ⟨s', hs', hc⟩

/-- **Embeddings of charts are the face maps up to renaming, with the same point map** ([AFK26,
Definition 4.31], the morphisms of `C_β[L]`): at a stage at most `ω₁`, for a strongly coded legal
`s`, the embeddings of the chart of `s` into the chart of `t` correspond, by their point maps, to
the maps of points along which the class of `t` has the face class of `s`. -/
def embeddingEquivFace (hα : α ≤ ω₁) {s : StageType.{u} α m} (hs : s.IsStronglyCodedLegal) :
    (s.TemplateChart ↪[templateLanguage.{u}] t.TemplateChart) ≃
      {f : Fin m ↪ Fin n // t.toClass.restrictFace f = some s.toClass} where
  toFun φ := ⟨φ.toEmbedding, by
    obtain ⟨s', hs', hc⟩ := t.exists_restrictFace_of_embedding hs φ
    have hs'' : restrictFace (φ.toEmbedding : Fin m ↪ Fin n) t = some s' := hs'
    change (restrictFace (φ.toEmbedding : Fin m ↪ Fin n) t).map toClass = some s.toClass
    rw [hs'', Option.map_some, toClass_eq_toClass_iff.mpr ((globalClass_eq_iff hα).mp hc)]⟩
  invFun f := t.templateChartEmbedding
    (Option.map_eq_some_iff.mp f.2).choose_spec.1
    (toClass_eq_toClass_iff.mp (Option.map_eq_some_iff.mp f.2).choose_spec.2).symm
  left_inv φ := Embedding.ext fun _ ↦ rfl
  right_inv f := rfl

@[simp] theorem embeddingEquivFace_apply_coe (hα : α ≤ ω₁) {s : StageType.{u} α m}
    (hs : s.IsStronglyCodedLegal) (φ : s.TemplateChart ↪[templateLanguage.{u}] t.TemplateChart) :
    ((t.embeddingEquivFace hα hs φ) : Fin m ↪ Fin n) = φ.toEmbedding :=
  rfl

end StageType

/-! ### Charts and the category `C_β[L]` -/

section Charts

open StageType

variable {M : Type v} {N : Type w} {R : Type x}

/-- **The category `C_β[L]`** [AFK26, Definition 4.31], as a class of structures: `G` is a chart on
a legal template `t` with `trunc_{ω + ω · β}(t) = t`.  Here `t` is a stage type at the block stage
`ω + ω · β` on `n ≥ 1` points that is a legal template with labels in `{-∞} ∪ ω₁ ∪ {∞}`, and the
enumeration `e` carries every relation of the chart of `t` (every symbol, every tuple, repetitions
allowed) to `G` and back.  `M` is finite, by the enumeration. -/
def IsTemplateChart (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  ∃ (n : ℕ) (t : StageType.{u} (blockStage β) n) (e : Fin n ≃ M), 0 < n ∧
    t.IsLegalTemplate ω₁ ∧ ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n),
      RelMap (L := templateLanguage.{u}) (self := G) r (e ∘ xs) ↔ t.Holds r xs

/-- The structure induced on a set of points ([AFK26, Proposition 4.32]: `M↾M₀`): the relations of
`G` on tuples of the set. -/
@[instance_reducible] def inducedOn (G : templateLanguage.{u}.Structure M) (s : Set M) :
    templateLanguage.{u}.Structure s where
  funMap f := Empty.elim f
  RelMap r xs := RelMap (L := templateLanguage.{u}) (self := G) r (Subtype.val ∘ xs)

/-- A set of points is **closed** in `G` ([AFK26, Definition 4.12]): it is empty, or enumerated by a
tuple satisfying `P_k`. -/
def IsClosedIn (G : templateLanguage.{u}.Structure M) (s : Set M) : Prop :=
  s = ∅ ∨ ∃ (k : ℕ) (hk : 0 < k) (xs : Fin k → M),
    RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.closed hk) xs ∧
      Set.range xs = s

/-- The chart of a stage type at a block stage is in `C_β[L]` when the stage type is a legal
template with labels in `{-∞} ∪ ω₁ ∪ {∞}` on `n ≥ 1` points. -/
theorem isTemplateChart_templateChart {β : Ordinal.{u}} {n : ℕ}
    {t : StageType.{u} (blockStage β) n} (hn : 0 < n) (ht : t.IsLegalTemplate ω₁) :
    IsTemplateChart β (inferInstance : templateLanguage.{u}.Structure t.TemplateChart) :=
  ⟨n, t, Equiv.refl _, hn, ht, fun _ _ ↦ Iff.rfl⟩

/-- A chart is isomorphic to the chart of its template, by its enumeration. -/
private def chartEquiv {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} {e : Fin n ≃ M}
    (G : templateLanguage.{u}.Structure M)
    (h : ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n),
      RelMap (L := templateLanguage.{u}) (self := G) r (e ∘ xs) ↔ t.Holds r xs) :
    @Language.Equiv templateLanguage.{u} t.TemplateChart M _ G where
  toEquiv := e
  map_fun' g := Empty.elim g
  map_rel' r xs := h r xs

/-- **The hereditary property** [AFK26, Proposition 4.32]: the restriction of a chart in
`C_β[L]` to a nonempty closed set of its points is in `C_β[L]`.  No hypothesis on `β`.  Native
theorem: faces of strongly coded legal stage types are strongly coded legal
(`StageType.IsLegal.restrictFace`, `StageType.isStronglyCoded_of_restrictFace`). -/
theorem IsTemplateChart.hereditary {β : Ordinal.{u}} {G : templateLanguage.{u}.Structure M}
    (hG : IsTemplateChart β G) {s : Set M} (hs : s.Nonempty) (hcl : IsClosedIn G s) :
    IsTemplateChart β (inducedOn G s) := by
  obtain ⟨n, t, e, -, ht, hte⟩ := hG
  obtain ⟨hlt, hθ⟩ := isLegalTemplate_omega_one_iff.mp ht
  obtain hs0 | ⟨k, hk, xs, hxs, hrange⟩ := hcl
  · exact absurd hs0 hs.ne_empty
  -- the tuple, read in the chart of `t`
  have hP := (hte (TemplateSymbol.closed hk) (e.symm ∘ xs)).mp (by
    simpa [Function.comp_def] using hxs)
  obtain ⟨hinj, p, hp, -⟩ := hP
  set g : Fin k ↪ Fin n := ⟨e.symm ∘ xs, hinj⟩
  have hxinj : Function.Injective xs := fun i j hij ↦ hinj (congrArg e.symm hij)
  have hmem (i : Fin k) : xs i ∈ s := by
    rw [← hrange]
    exact ⟨i, rfl⟩
  let b : Fin k ≃ s := Equiv.ofBijective (fun i ↦ ⟨xs i, hmem i⟩)
    ⟨fun i j hij ↦ hxinj (congrArg Subtype.val hij), fun y ↦ by
      obtain ⟨i, hi⟩ : (y : M) ∈ Set.range xs := by rw [hrange]; exact y.2
      exact ⟨i, Subtype.ext hi⟩⟩
  have hpθ : ∀ d, Label.AtStage ω₁ (p.label d) := by
    obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t g).mp hp
    exact fun d ↦ hθ _
  refine ⟨k, p, b, hk, isLegalTemplate_omega_one_iff.mpr
    ⟨⟨hlt.1.restrictFace g hp, isStronglyCoded_of_restrictFace hp hlt.2⟩, hpθ⟩,
    fun r ys ↦ ?_⟩
  have h1 := hte r (g ∘ ys)
  have h2 := t.holds_comp_iff hp (IsCellRenaming.refl p) r ys
  refine Iff.trans ?_ (h1.trans h2)
  change RelMap (L := templateLanguage.{u}) (self := G) r (fun i ↦ ((b (ys i) : s) : M)) ↔
    RelMap (L := templateLanguage.{u}) (self := G) r (e ∘ (g ∘ ys))
  have : (fun i ↦ ((b (ys i) : s) : M)) = e ∘ (g ∘ ys) := funext fun i ↦ by
    change xs (ys i) = e (e.symm (xs (ys i)))
    exact (e.apply_symm_apply _).symm
  rw [this]

/-- **Joint embedding** [AFK26, Proposition 4.32]: any two charts in `C_β[L]` embed into one chart
in `C_β[L]`, for `β < ω₁`.  Native theorem:
`StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit` at the block stage, through the
dictionary of `IsTemplateChart` and `StageType.templateChartEmbedding`. -/
theorem IsTemplateChart.jointEmbedding {β : Ordinal.{u}} (hβ : β < ω₁)
    [G : templateLanguage.{u}.Structure M] [H : templateLanguage.{u}.Structure N]
    (hG : IsTemplateChart β G) (hH : IsTemplateChart β H) :
    ∃ (P : Type) (I : templateLanguage.{u}.Structure P), IsTemplateChart β I ∧
      Nonempty (@Language.Embedding templateLanguage.{u} M P G I) ∧
      Nonempty (@Language.Embedding templateLanguage.{u} N P H I) := by
  obtain ⟨n, P, a, hn, hP, hPa⟩ := hG
  obtain ⟨m, T, b, -, hT, hTb⟩ := hH
  have hβω := (blockStage_lt_omega_one hβ).le
  obtain ⟨K, Q, i, j, hQ, hQP, hQT⟩ :=
    StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit (isSuccPrelimit_blockStage β)
      ((isLegalTemplate_omega_one_iff_of_le hβω).mp hP)
      ((isLegalTemplate_omega_one_iff_of_le hβω).mp hT)
  have hK : 0 < K := hn.trans_le (by simpa using Fintype.card_le_of_embedding i)
  exact ⟨Q.TemplateChart, inferInstance,
    isTemplateChart_templateChart hK ((isLegalTemplate_omega_one_iff_of_le hβω).mpr hQ),
    ⟨(Q.templateChartEmbedding hQP (IsCellRenaming.refl P)).comp
      (chartEquiv G hPa).symm.toEmbedding⟩,
    ⟨(Q.templateChartEmbedding hQT (IsCellRenaming.refl T)).comp
      (chartEquiv H hTb).symm.toEmbedding⟩⟩

/-- **Amalgamation** [AFK26, Proposition 4.32]: two embeddings `e : G ↪ H` and `f : G ↪ I` of
charts in `C_β[L]` are amalgamated by embeddings `i`, `j` into one chart in `C_β[L]` with
`i ∘ e = j ∘ f`, for `β < ω₁`.  Native theorem:
`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit` at the block stage, through the
dictionary of `IsTemplateChart` and `StageType.embeddingEquivFace`; the two faces of the common
chart, renamings of each other, are aligned first (`StageType.exists_restrictFace_renameCells`). -/
theorem IsTemplateChart.amalgamation {β : Ordinal.{u}} (hβ : β < ω₁)
    [G : templateLanguage.{u}.Structure M] [H : templateLanguage.{u}.Structure N]
    [I : templateLanguage.{u}.Structure R]
    (hG : IsTemplateChart β G) (hH : IsTemplateChart β H) (hI : IsTemplateChart β I)
    (e : M ↪[templateLanguage.{u}] N) (f : M ↪[templateLanguage.{u}] R) :
    ∃ (P : Type) (J : templateLanguage.{u}.Structure P), IsTemplateChart β J ∧
      ∃ (i : @Language.Embedding templateLanguage.{u} N P H J)
        (j : @Language.Embedding templateLanguage.{u} R P I J),
        letI := J; i.comp e = j.comp f := by
  obtain ⟨k, p, a, -, hp, hpa⟩ := hG
  obtain ⟨n, P, b, hn, hP, hPb⟩ := hH
  obtain ⟨m, T, c, -, hT, hTc⟩ := hI
  have hβω := (blockStage_lt_omega_one hβ).le
  have hp' := (isLegalTemplate_omega_one_iff_of_le hβω).mp hp
  have hP' := (isLegalTemplate_omega_one_iff_of_le hβω).mp hP
  have hT' := (isLegalTemplate_omega_one_iff_of_le hβω).mp hT
  -- the two point maps, as embeddings of charts of stage types
  let φ := (chartEquiv H hPb).symm.toEmbedding.comp (e.comp (chartEquiv G hpa).toEmbedding)
  let ψ := (chartEquiv I hTc).symm.toEmbedding.comp (f.comp (chartEquiv G hpa).toEmbedding)
  let φ' : Fin k ↪ Fin n := φ.toEmbedding
  let ψ' : Fin k ↪ Fin m := ψ.toEmbedding
  obtain ⟨p₁, hp₁, hpp₁⟩ := P.exists_restrictFace_of_embedding hp' φ
  obtain ⟨p₂, hp₂, hpp₂⟩ := T.exists_restrictFace_of_embedding hp' ψ
  have hp₁' : restrictFace φ' P = some p₁ := hp₁
  have hp₂' : restrictFace ψ' T = some p₂ := hp₂
  have h₁₂ : p₂.IsCellRenaming p₁ := (globalClass_eq_iff hβω).mp (hpp₂.trans hpp₁.symm)
  -- rename `T` so that its face is `p₁`
  obtain ⟨π, hπ⟩ := T.exists_restrictFace_renameCells ψ' hp₂' h₁₂
  have hT'' : (T.renameCells π).IsStronglyCodedLegal :=
    (T.isStronglyCodedLegal_renameCells_iff π).mpr hT'
  -- the native amalgamation at the block stage
  obtain ⟨K, Q, i, j, hQ, hQP, hQT, hcomm⟩ :=
    StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit (isSuccPrelimit_blockStage β)
      hP' hT'' hp₁' hπ
  have hK : 0 < K := hn.trans_le (by simpa using Fintype.card_le_of_embedding i)
  refine ⟨Q.TemplateChart, inferInstance,
    isTemplateChart_templateChart hK ((isLegalTemplate_omega_one_iff_of_le hβω).mpr hQ),
    (Q.templateChartEmbedding hQP (IsCellRenaming.refl P)).comp
      (chartEquiv H hPb).symm.toEmbedding,
    ((Q.templateChartEmbedding hQT (IsCellRenaming.refl _)).comp
      (T.templateChartEquivRename π).symm.toEmbedding).comp
      (chartEquiv I hTc).symm.toEmbedding, Embedding.ext fun y ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (chartEquiv G hpa).surjective y
  exact congrArg (fun g : Fin k ↪ Fin K ↦ g z) hcomm

end Charts

end

end VaughtConjecture

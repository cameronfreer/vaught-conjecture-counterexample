/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.WeakSystem

/-!
# The legal templates form a template system: [AFK26, Definition 4.11 and Proposition 4.30]

Numbering as in the current draft of [AFK26] (Definitions 4.6, 4.7, 4.8, 4.10, 4.11, 4.29 and
Proposition 4.30 read identically in the published version).  This file states
[AFK26, Proposition 4.30] for the positional legal templates, clause by clause, and proves the
clauses (a)–(g) and the four clauses of a template system for the chosen representatives of the
legal classes (`proposition430Target`).  The passage from arbitrary finite carriers is stated here
and proved in `VaughtConjecture.Correspondence.TemplateSystem.LegalCarrier`.

**Positional reading.**  A template on `[n]` is a stage type `t : StageType ω₁ n` (points `Fin n`,
cells `Fin t.card`); a legal template is `t.IsLegalTemplate ω₁` ([AFK26, Definition 4.29],
labels in `{-∞} ∪ ω₁ ∪ {∞}`).  "`A₀ ⊆ A` closed and `t↾A₀`" is a point embedding
`f : Fin m ↪ Fin n` with `StageType.restrictFace f t = some s` (defined exactly at closed faces);
"`u` extends `s`" is `StageType.restrictFace f u = some s`; `trunc_λ` at a block stage
`λ = ω + ω · β` is `StageType.project (isSuccPrelimit_blockStage β)` (`StageType.label_project`);
`trunc_δ(v) ≅_ren trunc_δ(u)` at an arbitrary ordinal `δ` is `StageType.IsTruncRenaming δ v u`
(raw truncated labellings, no truncated stage type is formed); `t₀ ≅_ren t₁` is
`StageType.IsCellRenaming t₀ t₁` ([AFK26, Definition 4.6]).  Printed templates live on nonempty
sets, so the arity is positive throughout (`0 < n`, explicit in `LegalTemplates` and
`chosenLegalTemplates`); natively `LegalClass 0` exists.

**Statements.**

* `LegalTemplates n` — the family `T` of the proof of [AFK26, Proposition 4.30] on `[n]`: the
  legal templates of positive arity.
* `TemplateSystemClauses T` — [AFK26, Definition 4.11] (b)–(g) for a family of positional
  templates, one named Prop per clause: `ReindexClause` (b), `FaceClause` (c), `ProjectClause`
  (d), `ProjectNeClause` (e), `ArityClause` (f), `TruncRepairClause` (g).  Clause (a) (points and
  cells are finite subsets of `ω`) holds by typing: points `Fin n`, cells `Fin t.card`.
* `IsTemplateSystemOver T L` — the four clauses on a template system `T* = L` of
  [AFK26, Definition 4.11] (the second, initial segments, by typing).
* `chosenTemplateRepresentative` — one stage type in every class of `TemplateClass ω₁ n`, by
  `Quotient.out`; `chosenLegalTemplates n` — the representatives of the legal classes, at positive
  arity.
* `TruncRepairTarget` — clause (g) as a literal stage-type statement; `LegalClassTruncRepairTarget`
  — its class-level counterpart with `TemplateClass.TruncEquiv`.
* `Proposition430Target` — `TemplateSystemClauses LegalTemplates` and
  `IsTemplateSystemOver LegalTemplates chosenLegalTemplates`.
* `Proposition430FintypeTarget` — with the second bullet of [AFK26, Proposition 4.30] for legal
  templates on an arbitrary `Fintype` of points with an explicit equivalence to `Fin n`
  (`FintypeCarrierClause`); `Proposition430FinsetNatTarget` — the specialization to underlying sets
  and cells that are finite subsets of `ℕ`, the printed collection `T` (`FinsetNatCarrierClause`).

**Status.**

* Proved: clauses (b), (c), (d), (e), (f) for `LegalTemplates` (`reindexClause_legalTemplates`,
  `faceClause_legalTemplates`, `projectClause_legalTemplates`, `projectNeClause_legalTemplates`,
  `arityClause_legalTemplates`, with nonemptiness at every positive arity
  `legalTemplates_nonempty`); the specification of the representatives
  (`toClass_chosenTemplateRepresentative`, `isLegalTemplate_chosenTemplateRepresentative`,
  `isStronglyCodedLegal_chosenTemplateRepresentative`); the four clauses of a template system for
  `chosenLegalTemplates` (`isTemplateSystemOver_chosenLegalTemplates`); clause (g) as a literal
  stage-type statement (`truncRepairTarget`) and on legal classes (`legalClassTruncRepairTarget`),
  for `LegalTemplates` (`truncRepairClause_legalTemplates`); and `proposition430Target`.  No premise
  beyond those of the printed clause (no countability, no coatom hypothesis).
* Stated here, proved in `VaughtConjecture.Correspondence.TemplateSystem.LegalCarrier`:
  `FintypeCarrierClause`, `FinsetNatCarrierClause`, `Proposition430FintypeTarget` and
  `Proposition430FinsetNatTarget`.

**Proof of clause (g)** (`truncRepairTarget`, as in the proof of [AFK26, Proposition 4.30]).
Fix `β < ω₁`, `λ := blockStage β`, `δ < λ`, and the data of `TruncRepairTarget`.
1. A cap `c` with `δ < c < λ` self-visible at `n`: `Label.exists_lt_lt_isSelfVisible`
   (`λ` is a limit, `isSuccPrelimit_blockStage`).
2. `q' := u'.reduce hλ` is legal with the face `t.reduce hλ` along `f`:
   `StageType.restrictFace_reduce` and `StageType.reduce_reduce` (`t.project hλ` reduces to
   `t.reduce hλ`).
3. `StageType.exists_isLawful_lift` (bountifulness from the face `(range f, m)` to `(univ, n)`)
   gives a labelling `ρ` lawful for the rows of `u'`, with `min (ρ d) c = min (u'.label d) c` and
   `ρ` extending the labels of `t` along `f`: the printed `r ∈ B_γ(p_u)`, `r↾(D_u↓V_t) = p_t`.
4. `v := StageType.ofIsLawful` on the scheme of `u'` with the labels `ρ` (reduced to `ω₁`): legal
   and strongly coded (scheme of `u'`), face `t` along `f` (`StageType.restrictFace_ofIsLawful`),
   so `v' := v` works.
5. Truncation: `δ ≤ c` and `Label.min_eq_min_iff_reduce_eq` give `Label.reduce δ` agreement of `v`
   and `u'` cell by cell, hence `v.IsTruncRenaming δ u` (`u'` is a renaming of `u`).
The class-level form follows by `TemplateClass.exists_renaming_restrictFace_eq` and
`TemplateClass.truncEquiv_toClass_iff`.  The amalgamation, pinned-extension and apex theorems are
not the tools: they change the scheme, while (g) keeps the frame and rows of `u'` and changes only
the labels.

**Ledger.**

* Already proved before this file (inputs, cited here): the identification of the legal templates
  of [AFK26, Definition 4.29] with the strongly coded legal stage types, both directions, at any
  stage `θ ≥ ω ^ 2` that is zero or a limit (`StageType.isLegalTemplate_iff`,
  `CellScheme.Rows.isLegalTemplate_iff`; at `ω₁`, `StageType.isLegalTemplate_omega_one_iff_of_le`
  and `TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate`).  This closes the ledger's
  gap G1; the sentence "its identification with the legal templates of [AFK26] is not proved" in
  the docstring of `StageType.IsStronglyCodedLegal` is out of date (that file is not edited here).
  Also already proved: renaming (`StageType.renameCells`, `StageType.IsCellRenaming`,
  `TemplateClass`), alignment of faces (`TemplateClass.exists_renaming_restrictFace_eq`), and the
  witness of (e) (`exists_legalClass_project_ne`).
* Closed by this file: the remaining part of gap G2, a named representative map
  (`chosenTemplateRepresentative`) and the four clauses of a template system for its legal range
  (`isTemplateSystemOver_chosenLegalTemplates`).  With `chosenLegalTemplates` named, "a chart on
  `t ∈ L`" of [AFK26, Definition 4.31] (item P32.1) can be stated literally; it is not stated here.
* Closed by this file: clause (g) (`truncRepairTarget`, `legalClassTruncRepairTarget`).
* Closed in `VaughtConjecture.Correspondence.TemplateSystem.LegalCarrier`: the passage from
  arbitrary finite carriers (`fintypeCarrierClause_chosenLegalTemplates`,
  `finsetNatCarrierClause_chosenLegalTemplates`).
* Later work, separate from this file: the printed argument for `τ_α(K_β[L]) ⊆ K_α[L]` in
  [AFK26, Theorem 4.23] uses (g); with (g) proved here it could remove the premise `Countable M`
  from `ProjectionTarget`.  Not attempted here.
-/

universe u w

namespace VaughtConjecture

open Finset Ordinal

/-! ### The legal templates -/

/-- **The legal templates on `[n]`** ([AFK26, Definition 4.29 and the proof of
Proposition 4.30], the collection `T`, read positionally): legal templates with labels in
`{-∞} ∪ ω₁ ∪ {∞}` on a nonempty underlying set. -/
def LegalTemplates (n : ℕ) : Set (StageType.{u} ω₁ n) :=
  {t | 0 < n ∧ t.IsLegalTemplate ω₁}

/-! ### The clauses of a template system -/

section Clauses

variable (T : ∀ n, Set (StageType.{u} ω₁ n))

/-- **[AFK26, Definition 4.11 (b)]**, positionally: reindexing the points along a bijection
`e : Fin m ≃ Fin n` (the face map along `e`, `StageType.reindex`) stays in `T`. -/
def ReindexClause : Prop :=
  ∀ ⦃m n : ℕ⦄ (e : Fin m ≃ Fin n) ⦃t : StageType.{u} ω₁ n⦄, t ∈ T n → t.reindex e ∈ T m

/-- **[AFK26, Definition 4.11 (c)]**, positionally: the restriction to a nonempty closed set of
points (a defined face along `f : Fin m ↪ Fin n`, `0 < m`) stays in `T`. -/
def FaceClause : Prop :=
  ∀ ⦃m n : ℕ⦄ (f : Fin m ↪ Fin n) ⦃t : StageType.{u} ω₁ n⦄ ⦃s : StageType.{u} ω₁ m⦄, 0 < m →
    t ∈ T n → StageType.restrictFace f t = some s → s ∈ T m

/-- **[AFK26, Definition 4.11 (d)]**: for `β < ω₁`, the truncation at `ω + ω · β` stays in `T`. -/
def ProjectClause : Prop :=
  ∀ β < ω₁, ∀ ⦃n : ℕ⦄ ⦃t : StageType.{u} ω₁ n⦄, t ∈ T n →
    t.project (isSuccPrelimit_blockStage β) ∈ T n

/-- **[AFK26, Definition 4.11 (e)]**: for every `β < ω₁`, some member of `T` is not fixed by the
truncation at `ω + ω · β`. -/
def ProjectNeClause : Prop :=
  ∀ β < ω₁, ∃ n : ℕ, ∃ t ∈ T n, t.project (isSuccPrelimit_blockStage β) ≠ t

/-- **[AFK26, Definition 4.11 (f)]**: for every `k`, some member of `T` has at least `k`
points. -/
def ArityClause : Prop :=
  ∀ k : ℕ, ∃ n, k ≤ n ∧ (T n).Nonempty

/-- **[AFK26, Definition 4.11 (g)]**, positionally: for `β < ω₁`, `λ = ω + ω · β`, every `δ < λ`
and `t, u ∈ T`, if a renaming `u'` of `u` extends `trunc_λ(t)` along `f`, then some `v ∈ T` on the
points of `u` has a renaming `v'` extending `t` along the same `f`, and
`trunc_δ(v) ≅_ren trunc_δ(u)`. -/
def TruncRepairClause : Prop :=
  ∀ β < ω₁, ∀ δ < blockStage β, ∀ ⦃m n : ℕ⦄ (f : Fin m ↪ Fin n) ⦃t : StageType.{u} ω₁ m⦄
    ⦃u : StageType.{u} ω₁ n⦄, t ∈ T m → u ∈ T n →
    (∃ u', u'.IsCellRenaming u ∧
      StageType.restrictFace f u' = some (t.project (isSuccPrelimit_blockStage β))) →
    ∃ v ∈ T n, (∃ v', v'.IsCellRenaming v ∧ StageType.restrictFace f v' = some t) ∧
      v.IsTruncRenaming δ u

/-- **[AFK26, Definition 4.11 (b)–(g)]** for a family `T` of positional templates.  Clause (a)
holds by typing: the points are `Fin n` and the cells `Fin t.card`, initial segments of `ω`. -/
structure TemplateSystemClauses : Prop where
  /-- (b) closure under reindexing the points. -/
  reindex : ReindexClause T
  /-- (c) closure under restriction to nonempty closed sets. -/
  face : FaceClause T
  /-- (d) closure under truncation at the block stages. -/
  project : ProjectClause T
  /-- (e) a member not fixed by each truncation. -/
  project_ne : ProjectNeClause T
  /-- (f) members with arbitrarily many points. -/
  arity : ArityClause T
  /-- (g) repair of a prescribed root. -/
  truncRepair : TruncRepairClause T

/-- **A template system over `T`** [AFK26, Definition 4.11], positionally: `L ⊆ T`, members of
`L` have a positive number of points, every member of `T` on `[n]` (`n ≥ 1`) is a renaming of a
member of `L`, and members of `L` that are renamings of each other are equal.  The second printed
clause (points and cells are initial segments of `ω`) holds by typing. -/
structure IsTemplateSystemOver (L : ∀ n, Set (StageType.{u} ω₁ n)) : Prop where
  /-- `T* ⊆ T`. -/
  subset : ∀ n, L n ⊆ T n
  /-- Members of `L` live on nonempty sets. -/
  pos : ∀ ⦃n : ℕ⦄ ⦃t : StageType.{u} ω₁ n⦄, t ∈ L n → 0 < n
  /-- Every member of `T` on `[n]` has a renaming in `L`. -/
  exists_renaming : ∀ ⦃n : ℕ⦄, 0 < n → ∀ t ∈ T n, ∃ t' ∈ L n, t.IsCellRenaming t'
  /-- Renamings within `L` are equal. -/
  eq_of_isCellRenaming : ∀ ⦃n : ℕ⦄ ⦃t t' : StageType.{u} ω₁ n⦄, t ∈ L n → t' ∈ L n →
    t.IsCellRenaming t' → t = t'

end Clauses

/-! ### The chosen representatives -/

/-- **The chosen representative of a class** ([AFK26, proof of Proposition 4.30]: "choose one
representative of each cell-renaming class on each underlying set `[n]`"): a stage type of the
class, by `Quotient.out`.  It covers every class; on the legal classes it is a legal template
(`isLegalTemplate_chosenTemplateRepresentative`). -/
noncomputable def chosenTemplateRepresentative {n : ℕ} (c : TemplateClass.{u} ω₁ n) :
    StageType.{u} ω₁ n :=
  Quotient.out c

/-- The chosen representative of a class lies in the class. -/
@[simp] theorem toClass_chosenTemplateRepresentative {n : ℕ} (c : TemplateClass.{u} ω₁ n) :
    (chosenTemplateRepresentative c).toClass = c :=
  Quotient.out_eq c

/-- The chosen representative of a legal class is strongly coded legal. -/
theorem isStronglyCodedLegal_chosenTemplateRepresentative {n : ℕ} {c : TemplateClass.{u} ω₁ n}
    (hc : c.IsStronglyCodedLegal) : (chosenTemplateRepresentative c).IsStronglyCodedLegal := by
  rw [← TemplateClass.isStronglyCodedLegal_toClass, toClass_chosenTemplateRepresentative]
  exact hc

/-- **The chosen representative of a legal class is a legal template** [AFK26,
Definition 4.29]. -/
theorem isLegalTemplate_chosenTemplateRepresentative {n : ℕ} {c : TemplateClass.{u} ω₁ n}
    (hc : c.IsStronglyCodedLegal) : (chosenTemplateRepresentative c).IsLegalTemplate ω₁ :=
  (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mpr
    (isStronglyCodedLegal_chosenTemplateRepresentative hc)

/-- **The chosen legal templates on `[n]`** ([AFK26, Proposition 4.30], the system `L`): the chosen
representatives of the legal classes, on a nonempty underlying set. -/
def chosenLegalTemplates (n : ℕ) : Set (StageType.{u} ω₁ n) :=
  {t | 0 < n ∧ ∃ c : LegalClass.{u} n, chosenTemplateRepresentative c.1 = t}

/-! ### Clause (g) -/

/-- **Target: [AFK26, Definition 4.11 (g)] for the legal templates, as a literal stage-type
statement.**  For `β < ω₁` and `λ = ω + ω · β`, legal templates `t` on `[m]` and `u` on `[n]`
(`m, n ≥ 1`), a renaming `u'` of `u` and a face map `f` with `u'↾f = trunc_λ(t)` (the face at the
ambient stage `ω₁`, `t.project`), and every `δ < λ`: there are a legal template `v` on `[n]` and a
renaming `v'` of `v` with `v'↾f = t` (the same `f`, the literal face `t`) and
`trunc_δ(v) ≅_ren trunc_δ(u)`.  No closedness premise: the face equation states that `range f` is
closed in `u'`.  Proved: `truncRepairTarget`. -/
def TruncRepairTarget : Prop :=
  ∀ β < ω₁, ∀ ⦃m n : ℕ⦄ (t : StageType.{u} ω₁ m) (u : StageType.{u} ω₁ n), 0 < m → 0 < n →
    t.IsLegalTemplate ω₁ → u.IsLegalTemplate ω₁ → ∀ u' : StageType.{u} ω₁ n, u'.IsCellRenaming u →
    ∀ f : Fin m ↪ Fin n,
      StageType.restrictFace f u' = some (t.project (isSuccPrelimit_blockStage β)) →
    ∀ δ < blockStage β, ∃ v : StageType.{u} ω₁ n, v.IsLegalTemplate ω₁ ∧
      ∃ v' : StageType.{u} ω₁ n, v'.IsCellRenaming v ∧ StageType.restrictFace f v' = some t ∧
        v.IsTruncRenaming δ u

/-- **Target: [AFK26, Definition 4.11 (g)] on legal classes.**  For `β < ω₁`, legal classes `t`
on `[m]` and `u` on `[n]` (`m, n ≥ 1`) with `u↾f = τ_β(t)`, and every `δ < ω + ω · β`: some legal
class `v` on `[n]` has `v↾f = t` and `trunc_δ(v) ≅_ren trunc_δ(u)` (`TemplateClass.TruncEquiv`).
Proved: `legalClassTruncRepairTarget`. -/
def LegalClassTruncRepairTarget : Prop :=
  ∀ β < ω₁, ∀ ⦃m n : ℕ⦄ (f : Fin m ↪ Fin n) (t : LegalClass.{u} m) (u : LegalClass.{u} n),
    0 < m → 0 < n → u.1.restrictFace f = some (t.project β).1 →
    ∀ δ < blockStage β, ∃ v : LegalClass.{u} n, v.1.restrictFace f = some t.1 ∧
      v.1.TruncEquiv δ u.1

/-! ### Arbitrary finite carriers -/

/-- **Isomorphic to a renaming, along given bijections** [AFK26, Definitions 4.6 and 4.7]: the
template `(D, R, p)` with cells `ι` and underlying set `A = D.ground ⊆ P` is carried by the point
bijection `j : [n] → A` (the inverse of the printed isomorphism `i : A → [n]`) and the cell
bijection `e` (the printed renaming bijection) onto `t`.  The plan of `t` is carried onto the plan
of `D`; the scope of the cell `e d` of `t` is carried onto the scope of `d`, with the same grade;
the label of `e d` is `p d`; and the row of `e d` at `e x` is the row of `d` at `x`. -/
structure IsIsoRenamingAlong {ι P : Type*} {α : Ordinal.{u}} {n : ℕ} (j : Fin n ↪ P)
    (D : CellScheme ι P) (R : D.Rows.{u}) (p : ι → Label.{u}) (t : StageType.{u} α n)
    (e : ι ≃ Fin t.card) : Prop where
  /-- The underlying set is the image of `[n]`. -/
  ground_eq : D.ground = Finset.univ.map j
  /-- The plan is the image of the plan of `t`. -/
  faces_eq : D.faces = t.toCellScheme.faces.map (mapEmbedding j).toEmbedding
  /-- Scopes correspond. -/
  scope_eq : ∀ d, (t.toCellScheme.scope (e d)).map j = D.scope d
  /-- Grades correspond. -/
  grade_eq : ∀ d, t.toCellScheme.grade (e d) = D.grade d
  /-- Labels correspond. -/
  label_eq : ∀ d, t.label (e d) = p d
  /-- Rows correspond. -/
  row_eq : ∀ d (x : D.below (D.gradedIndex d))
    (y : t.toCellScheme.below (t.toCellScheme.gradedIndex (e d))),
    (y : Fin t.card) = e x → t.rows.row (e d) y = R.row d x

/-- **Isomorphic to a renaming** [AFK26, Definitions 4.6 and 4.7]: `(D, R, p)` is isomorphic,
along the point bijection `j`, to a renaming of `t`. -/
def IsIsoRenaming {ι P : Type*} {α : Ordinal.{u}} {n : ℕ} (j : Fin n ↪ P) (D : CellScheme ι P)
    (R : D.Rows.{u}) (p : ι → Label.{u}) (t : StageType.{u} α n) : Prop :=
  ∃ e : ι ≃ Fin t.card, IsIsoRenamingAlong j D R p t e

/-- **The second bullet of [AFK26, Proposition 4.30] on `Fintype` carriers**: every legal template
([AFK26, Definitions 4.1 and 4.29]) with finitely many cells whose underlying set is all of a
finite type `P`, with an explicit equivalence `i : P ≃ Fin n`, is isomorphic along `i` to a
renaming of a member of `L n`. -/
def FintypeCarrierClause (L : ∀ n, Set (StageType.{u} ω₁ n)) : Prop :=
  ∀ (P : Type w) [Fintype P] [DecidableEq P] (n : ℕ) (i : P ≃ Fin n) {ι : Type w} [Finite ι]
    (D : CellScheme ι P) (R : D.Rows.{u}) (p : ι → Label.{u}), D.ground = Finset.univ →
    Geometry.IsTemplatePlan D.ground D.faces → R.IsLegalTemplate ω₁ p →
    ∃ t ∈ L n, IsIsoRenaming i.symm.toEmbedding D R p t

/-- **The second bullet of [AFK26, Proposition 4.30] for the printed collection `T`**: every legal
template whose underlying set `A` and cells `C` are finite subsets of `ℕ`
([AFK26, Definition 4.11 (a)]), with an explicit equivalence `i : A ≃ Fin n`, is isomorphic along
`i` to a renaming of a member of `L n`. -/
def FinsetNatCarrierClause (L : ∀ n, Set (StageType.{u} ω₁ n)) : Prop :=
  ∀ (A C : Finset ℕ) (n : ℕ) (i : A ≃ Fin n) (D : CellScheme C ℕ) (R : D.Rows.{u})
    (p : C → Label.{u}), D.ground = A → Geometry.IsTemplatePlan D.ground D.faces →
    R.IsLegalTemplate ω₁ p →
    ∃ t ∈ L n, IsIsoRenaming (i.symm.toEmbedding.trans (Function.Embedding.subtype _)) D R p t

/-! ### The targets -/

/-- **Target: [AFK26, Proposition 4.30] for positional legal templates**: the legal templates
satisfy [AFK26, Definition 4.11] (b)–(g), and the chosen representatives of the legal classes form
a template system over them (so all its members are legal templates, the first bullet).  Proved:
`proposition430Target`. -/
def Proposition430Target : Prop :=
  TemplateSystemClauses LegalTemplates.{u} ∧
    IsTemplateSystemOver LegalTemplates.{u} chosenLegalTemplates.{u}

/-- **Target: [AFK26, Proposition 4.30], with legal templates on arbitrary finite carriers**:
`Proposition430Target`, and every legal template on a finite type of points with an explicit
equivalence to `Fin n` is isomorphic to a renaming of a chosen legal template (the second
bullet).  Proved: `proposition430FintypeTarget`. -/
def Proposition430FintypeTarget : Prop :=
  Proposition430Target.{u} ∧ FintypeCarrierClause.{u, w} chosenLegalTemplates.{u}

/-- **Target: [AFK26, Proposition 4.30] for templates on finite subsets of `ℕ`**:
`Proposition430Target`, and every legal template whose underlying set and cells are finite subsets
of `ℕ` is isomorphic to a renaming of a chosen legal template.  It is to follow from the `Fintype`
form `Proposition430FintypeTarget` (point type the subtype of `A`).  Proved:
`proposition430FinsetNatTarget`. -/
def Proposition430FinsetNatTarget : Prop :=
  Proposition430Target.{u} ∧ FinsetNatCarrierClause.{u} chosenLegalTemplates.{u}

/-! ### The clauses that are compositions -/

/-- **Clause (b) for the legal templates** [AFK26, Definition 4.11 (b)]: reindexing along a
bijection keeps legality and strong coding. -/
theorem reindexClause_legalTemplates : ReindexClause LegalTemplates.{u} := by
  intro m n e t ht
  have hmn : m = n := by simpa using Fintype.card_congr e
  have hs := (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mp ht.2
  exact ⟨hmn ▸ ht.1, (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mpr
    ⟨hs.1.reindex e, Scheme.isStronglyCoded_comap hs.2 e.toEmbedding⟩⟩

/-- **Clause (c) for the legal templates** [AFK26, Definition 4.11 (c)]: a defined face of a
legal template on a nonempty set of points is a legal template. -/
theorem faceClause_legalTemplates : FaceClause LegalTemplates.{u} := by
  intro m n f t s hm ht hs
  have ht' := (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mp ht.2
  exact ⟨hm, (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mpr
    ⟨ht'.1.restrictFace f hs, StageType.isStronglyCoded_of_restrictFace hs ht'.2⟩⟩

/-- **Clause (d) for the legal templates** [AFK26, Definition 4.11 (d)]: the truncation keeps the
scheme and the rows (`StageType.isStronglyCodedLegal_project_iff`). -/
theorem projectClause_legalTemplates : ProjectClause LegalTemplates.{u} := by
  intro β _ n t ht
  exact ⟨ht.1, (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mpr
    ((StageType.isStronglyCodedLegal_project_iff t _).mpr
      ((StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mp ht.2))⟩

/-- **Clause (e) for the legal templates** [AFK26, Definition 4.11 (e)]: the chosen representative
of a legal class on one point not fixed by `τ_β` (`exists_legalClass_project_ne`). -/
theorem projectNeClause_legalTemplates : ProjectNeClause LegalTemplates.{u} := by
  intro β hβ
  obtain ⟨c, hc⟩ := exists_legalClass_project_ne hβ
  refine ⟨1, chosenTemplateRepresentative c.1,
    ⟨one_pos, isLegalTemplate_chosenTemplateRepresentative c.2⟩, fun h ↦ hc (Subtype.ext ?_)⟩
  have h' := congrArg StageType.toClass h
  rwa [← TemplateClass.project_toClass, toClass_chosenTemplateRepresentative] at h'

/-- **A legal template on every positive number of points** (the chosen representative of a legal
class, `exists_legalClass`). -/
theorem legalTemplates_nonempty {n : ℕ} (hn : 0 < n) : (LegalTemplates.{u} n).Nonempty := by
  obtain ⟨c⟩ := exists_legalClass.{u} n
  exact ⟨chosenTemplateRepresentative c.1, hn, isLegalTemplate_chosenTemplateRepresentative c.2⟩

/-- **Clause (f) for the legal templates** [AFK26, Definition 4.11 (f)]. -/
theorem arityClause_legalTemplates : ArityClause LegalTemplates.{u} :=
  fun k ↦ ⟨k + 1, Nat.le_succ k, legalTemplates_nonempty k.succ_pos⟩

/-- **The chosen legal templates form a template system over the legal templates**
[AFK26, Definition 4.11 and the proof of Proposition 4.30]. -/
theorem isTemplateSystemOver_chosenLegalTemplates :
    IsTemplateSystemOver LegalTemplates.{u} chosenLegalTemplates.{u} where
  subset := by
    rintro n _ ⟨hn, c, rfl⟩
    exact ⟨hn, isLegalTemplate_chosenTemplateRepresentative c.2⟩
  pos := fun _ _ ht ↦ ht.1
  exists_renaming := by
    intro n hn t ht
    refine ⟨chosenTemplateRepresentative t.toClass,
      ⟨hn, ⟨t.toClass, (TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate le_rfl
        t).mpr ht.2⟩, rfl⟩, ?_⟩
    exact StageType.toClass_eq_toClass_iff.mp (toClass_chosenTemplateRepresentative _).symm
  eq_of_isCellRenaming := by
    rintro n _ _ ⟨-, c, rfl⟩ ⟨-, c', rfl⟩ h
    have h' := StageType.toClass_eq_toClass_iff.mpr h
    rw [toClass_chosenTemplateRepresentative, toClass_chosenTemplateRepresentative] at h'
    rw [h']

/-- **Clause (g) for the legal templates from its stage-type form**: `TruncRepairTarget` gives
[AFK26, Definition 4.11 (g)] for `LegalTemplates`. -/
theorem truncRepairClause_of_truncRepairTarget (h : TruncRepairTarget.{u}) :
    TruncRepairClause LegalTemplates.{u} := by
  rintro β hβ δ hδ m n f t u ⟨hm, ht⟩ ⟨hn, hu⟩ ⟨u', hu', hf⟩
  obtain ⟨v, hv, v', hv', hvf, hvu⟩ := h β hβ t u hm hn ht hu u' hu' f hf δ hδ
  exact ⟨v, ⟨hn, hv⟩, ⟨v', hv', hvf⟩, hvu⟩

/-- **[AFK26, Proposition 4.30] for positional legal templates, from clause (g)**: every other
clause is proved. -/
theorem proposition430Target_of_truncRepairTarget (h : TruncRepairTarget.{u}) :
    Proposition430Target.{u} :=
  ⟨⟨reindexClause_legalTemplates, faceClause_legalTemplates, projectClause_legalTemplates,
    projectNeClause_legalTemplates, arityClause_legalTemplates,
    truncRepairClause_of_truncRepairTarget h⟩, isTemplateSystemOver_chosenLegalTemplates⟩

/-! ### Clause (g) -/

/-- **[AFK26, Definition 4.11 (g)] for the legal templates, as a literal stage-type statement**
(the proof of [AFK26, Proposition 4.30]).  Route: a cap `c` with `δ < c < λ` self-visible at `n`
(`Label.exists_lt_lt_isSelfVisible`); bountifulness of the rows of `u'` from the face along `f`
to all points, at the cap `c`, for the reduction of `u'` to `λ` whose face is `t` reduced to `λ`
(`StageType.exists_isLawful_lift`); the stage type `v` on the scheme of `u'` with the lifted labels
(`StageType.ofIsLawful`), whose face along `f` is `t` (`StageType.restrictFace_ofIsLawful`); and
agreement of `v` with `u'` capped at `c`, hence after `trunc_δ` (`Label.min_eq_min_iff_reduce_eq`).
The witness `v` has the frame and rows of `u'`, and `v' = v`. -/
theorem truncRepairTarget : TruncRepairTarget.{u} := by
  intro β hβ m n t u hm hn ht hu u' hu' f hf δ hδ
  have hL := isSuccPrelimit_blockStage β
  have hω : Order.IsSuccPrelimit ω₁ := (Cardinal.isSuccLimit_omega 1).isSuccPrelimit
  have hLω : blockStage β ≤ ω₁ := (blockStage_lt_omega_one hβ).le
  obtain ⟨c, hδc, hcL, hcn⟩ := Label.exists_lt_lt_isSelfVisible hL hδ n
  obtain ⟨k, σ, rfl⟩ := hu'
  have hsl : u'.IsStronglyCodedLegal :=
    (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mp
      ((StageType.isLegalTemplate_renameCells_iff u' σ
        (Cardinal.isSuccLimit_omega 1).isSuccPrelimit Label.omega0_sq_lt_omega_one.le).mp hu)
  obtain ⟨hfm, heq⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have hp : u'.toScheme.comap f = t.toScheme := congrArg StageType.toScheme heq
  have hface : StageType.restrictFace f (u'.reduce hL) = some (t.reduce hL) := by
    rw [StageType.restrictFace_reduce, hf, Option.map_some, StageType.project,
      StageType.reduce_reduce _ hω hL hLω, StageType.reduce_reduce _ hL hL le_rfl]
  have hcL' : ((c : Ordinal.{u}) : Label.{u}) ≤ ((blockStage β : Ordinal.{u}) : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hcL.le)
  obtain ⟨ρ, hρ, hρc, hext⟩ := StageType.exists_isLawful_lift hL hsl.1 hface hcn hcL'
  let v : StageType.{u} ω₁ n := StageType.ofIsLawful hω u'.toScheme u'.isWellFormed u'.isCoded ρ hρ
  have hv : v.IsLegalTemplate ω₁ :=
    (StageType.isLegalTemplate_omega_one_iff_of_le le_rfl).mpr hsl
  refine ⟨v, hv, v, StageType.IsCellRenaming.refl v,
    StageType.restrictFace_ofIsLawful hω hfm hp hext, v.renameCells σ, ⟨k, σ, rfl⟩, rfl,
    fun i j hij ↦ ?_⟩
  obtain rfl := Fin.ext hij
  change Label.reduce δ (Label.reduce ω₁ (ρ (σ i))) = Label.reduce δ (u'.label (σ i))
  rw [Label.reduce_reduce_of_le (hδ.le.trans hLω)]
  have h1 := hρc (σ i)
  rw [StageType.reduce_label, Label.min_reduce_of_le hcL'] at h1
  have hδc' : ((δ : Ordinal.{u}) : Label.{u}) ≤ ((c : Ordinal.{u}) : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hδc.le)
  refine Label.min_eq_min_iff_reduce_eq.mp ?_
  have h2 := congrArg (min · ((δ : Ordinal.{u}) : Label.{u})) h1
  simpa only [min_assoc, min_eq_right hδc'] using h2

/-- **[AFK26, Definition 4.11 (g)] on legal classes**: from `truncRepairTarget` on the chosen
representatives, after aligning a representative of `u` with the face `τ_β(t)`
(`TemplateClass.exists_renaming_restrictFace_eq`); the truncation is read on classes by
`TemplateClass.truncEquiv_toClass_iff`. -/
theorem legalClassTruncRepairTarget : LegalClassTruncRepairTarget.{u} := by
  intro β hβ m n f t u hm hn htu δ hδ
  set t₀ := chosenTemplateRepresentative t.1
  set u₀ := chosenTemplateRepresentative u.1
  have ht₀ : t₀.toClass = t.1 := toClass_chosenTemplateRepresentative _
  have hu₀ : u₀.toClass = u.1 := toClass_chosenTemplateRepresentative _
  have hface : u₀.toClass.restrictFace f =
      some (t₀.project (isSuccPrelimit_blockStage β)).toClass := by
    rw [hu₀, htu, LegalClass.coe_project, ← ht₀, TemplateClass.project_toClass]
  obtain ⟨u', hu'u, hu'f⟩ := TemplateClass.exists_renaming_restrictFace_eq u₀ f hface
  obtain ⟨v, hv, v', hv'v, hv'f, hvu⟩ := truncRepairTarget β hβ t₀ u₀ hm hn
    (isLegalTemplate_chosenTemplateRepresentative t.2)
    (isLegalTemplate_chosenTemplateRepresentative u.2)
    u' (StageType.toClass_eq_toClass_iff.mp hu'u) f hu'f δ hδ
  refine ⟨⟨v.toClass, (TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate le_rfl
    v).mpr hv⟩, ?_, ?_⟩
  · change v.toClass.restrictFace f = some t.1
    rw [← StageType.toClass_eq_toClass_iff.mpr hv'v, TemplateClass.restrictFace_toClass, hv'f,
      Option.map_some, ht₀]
  · change v.toClass.TruncEquiv δ u.1
    rw [← hu₀]
    exact TemplateClass.truncEquiv_toClass_iff.mpr hvu

/-- **[AFK26, Definition 4.11 (g)] for `LegalTemplates`.** -/
theorem truncRepairClause_legalTemplates : TruncRepairClause LegalTemplates.{u} :=
  truncRepairClause_of_truncRepairTarget truncRepairTarget

/-- **[AFK26, Proposition 4.30] for positional legal templates**: the legal templates satisfy
[AFK26, Definition 4.11] (b)–(g), and the chosen representatives of the legal classes form a
template system over them. -/
theorem proposition430Target : Proposition430Target.{u} :=
  proposition430Target_of_truncRepairTarget truncRepairTarget

end VaughtConjecture

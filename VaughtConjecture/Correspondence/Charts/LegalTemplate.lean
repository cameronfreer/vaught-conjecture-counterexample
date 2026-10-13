/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Current.Bountiful
import VaughtConjecture.Correspondence.Legal
import VaughtConjecture.Extension.BountifulCompression
import VaughtConjecture.Extension.StronglyCodedAmalgamation
import VaughtConjecture.Realization.Expansion

/-!
# The legal templates of [AFK26], clause by clause, and the strongly coded legal stage types

[AFK26, Definition 4.29] calls a template `t = (c, Σ, p)` over a plan `(A, P)`, with
`Σ = (ℓ_d)_{d ∈ D}`, **legal** if

1. `range(c) = GradedFace[P]`, i.e., every graded face has a cell;
2. `p` is lawful with respect to `Σ`;
3. for each `d ∈ D`, `ℓ_d` is lawful;
4. the rows of `(ℓ_d)_{d ∈ D}` are bountiful;
5. for each `d`, `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : n ∈ ω, i ≤ g(d) + 1}`.

The numbering is that of the draft of [AFK26] dated 10 October 2026: Definition 4.2 (graded
faces), 4.4 (labels, row systems), 4.5 (templates), 4.26 (visibility maps, self-visibility), 4.27
(the relation `u ⇒ v`), 4.28 (lawful local labellings, the balls `B_γ(q)`, bountiful rows), 4.29
(legal templates).  This file states these definitions on their own
(`Label.TemplateWitness`, `Label.TemplateTransformsTo`, `CellScheme.Rows.TemplateLawfulLocal`,
`CellScheme.Rows.TemplateLawful`, `CellScheme.Rows.templateBall`,
`CellScheme.Rows.TemplateBountiful`, `StageType.IsLegalTemplate`) and compares them with the
native notions.  It does not use the formalizations of earlier drafts in
`VaughtConjecture.Correspondence.Current` as definitions; their comparison theorems are used in
proofs only.

## The reading

* **Fixed rows.**  The frame `c` is the graded index of the cells of a scheme
  (`CellScheme.gradedIndex`), the plan `P` its faces, and the row system `Σ` the fixed semantic rows
  of the scheme (`ℓ_d = t.rows.row d`), against which a labelling is lawful.  The label `p` is the
  label section of a stage type.  The plan, the typing of the frame into the graded faces, the
  finiteness of the cells, and the range `{-∞} ∪ ω ^ 2` of a row system
  ([AFK26, Definitions 4.1–4.5]) are carried by the stage type itself (`StageType.isWellFormed`,
  `StageType.isCoded`); they are not fields here, and the plan conditions are not compared with
  [AFK26, Definition 4.1] in this file.
* **The label universe.**  [AFK26] takes labels in `{-∞} ∪ ω₁ ∪ {∞}`.  The definitions are stated
  at a stage `θ`, the labels being those at stage `θ` (`Label.AtStage θ`: `⊥`, the ordinals below
  `θ`, and `⊤`); [AFK26] takes `θ = ω₁`.  The stage `θ` is the label universe of the template; it
  is a separate parameter from the stage `α` of the stage type `t : StageType α n`, which bounds
  the labels of `t` (`StageType.atStage`).
* **Visibility.**  [AFK26, Definition 4.26] sends `ω · α + n` to `ω · α + i` if `n < k` and fixes
  it otherwise; this is `Label.visibilityReplace k i` (`Label.visibilityReplace_omega0_mul_add`),
  and self-visibility at `k`, `visible<k>[k](x) = x`, is literally `Label.IsSelfVisible k x`.
* **Graded faces.**  [AFK26, Definition 4.2] takes `1 ≤ j ≤ |B|`, which is
  `CellScheme.gradedFaces`.

| Clause of [AFK26, Definition 4.29] | Field of `StageType.IsLegalTemplate` | Native |
| --- | --- | --- |
| `p : D → {-∞} ∪ θ ∪ {∞}` (Definition 4.4) | `label_atStage` | `StageType.atStage` at `α ≤ θ` |
| 1. `range(c) = GradedFace[P]` | `range_gradedIndex` | `IsWellFormed`, `IsComplete` |
| 2. `p` lawful | `lawful` | `StageType.isLawful` |
| 3. each `ℓ_d` lawful | `row_lawful` | `Rows.IsConsistent` |
| 4. the rows bountiful | `bountiful` | `Rows.IsBountiful` |
| 5. `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : i ≤ g(d) + 1}` | `row_range` | `Rows.IsStronglyCoded` |

## The comparison

At a stage `θ ≥ ω ^ 2` that is zero or a limit, a stage type is a legal template with labels at
stage `θ` exactly when it is strongly coded legal and its labels lie at stage `θ`
(`StageType.isLegalTemplate_iff`); at `ω₁`, `StageType.isLegalTemplate_omega_one_iff`; for a
stage type at a stage `α ≤ ω₁`, in particular at a block stage `ω + ω · β` with `β < ω₁`, it is
a legal template exactly when it is strongly coded legal
(`StageType.isLegalTemplate_omega_one_iff_of_le`, `StageType.isLegalTemplate_blockStage_iff`).

Clauses 1, 2, 3 and 5 match field by field (2 and 3 through the identification of the relation
`⇒` with `Label.TransformsTo` at a stage that is zero or a limit, `Label.templateTransformsTo_iff`).
Clause 4 is bountifulness at the single stage `θ` (caps and labellings with values at stage `θ`),
while `CellScheme.Rows.IsBountiful` quantifies over all labels.  Native → printed is
`CellScheme.Rows.IsBountiful.templateBountiful` (reduce the native lift to stage `θ`).
Printed → native is `CellScheme.Rows.TemplateBountiful.isBountiful`, for finitely many cells and
`θ ≥ ω ^ 2`: by block compression (`CellScheme.Rows.isBountiful_of_forall_atStage`), the capped
lifts of labellings at stage `θ` give those of arbitrary labellings.  The cap `-∞` and the cap `∞`
are among the printed caps (`γ ∈ {-∞} ∪ ω₁ ∪ {∞}`), so no separate extension of lawful labellings
is needed.

For the formalization of the earlier draft (bountifulness with ordinal caps only,
`CellScheme.Rows.PrintedBountifulRows`), the same compression gives bountifulness from the printed
definition at the single stage `θ` together with the extension of lawful labellings (the cap
`-∞`), `CellScheme.Rows.isBountiful_of_printedBountifulRows`.

**Not stated here.**  Cell renaming ([AFK26, Definition 4.6]): two stage types that differ by a
permutation of cells are distinct, while [AFK26] identifies a template with its renamings; the
predicate here is on positional stage types.  The charts of [AFK26, Definition 4.31] and the
comparison of [AFK26, Definition 4.1] with `Geometry.IsPlan` are not treated in this file.
-/

universe u

namespace VaughtConjecture

open Finset Label Ordinal

/-! ### The relation `u ⇒ v` -/

namespace Label

variable {D : Type*} {θ : Ordinal.{u}} {g : D → ℕ} {u v : D → Label.{u}}
  {f : ℕ → Label.{u}} {h : Label.{u} → Label.{u}}

/-- **A witness of `u ⇒ v`** [AFK26, Definition 4.27], on the labels at stage `θ` ([AFK26] takes
`θ = ω₁`): a suppressor `f : ω → {-∞} ∪ θ ∪ {∞}` and a shifter `h` of `{-∞} ∪ θ ∪ {∞}` to itself,
with the printed clauses in their printed order; the visibility map is
`Label.visibilityReplace`. -/
structure TemplateWitness (θ : Ordinal.{u}) (f : ℕ → Label.{u}) (h : Label.{u} → Label.{u}) :
    Prop where
  /-- The typing `f : ω → {-∞} ∪ θ ∪ {∞}`. -/
  suppressor_atStage : ∀ k, AtStage θ (f k)
  /-- The typing `h : {-∞} ∪ θ ∪ {∞} → {-∞} ∪ θ ∪ {∞}`. -/
  shifter_atStage : ∀ x, AtStage θ x → AtStage θ (h x)
  /-- `f` is antitone: for all `a ≤ b`, `f(a) ≥ f(b)`. -/
  antitone : ∀ a b : ℕ, a ≤ b → f b ≤ f a
  /-- For all `k`, the value `f(k)` is self-visible at `k`. -/
  isSelfVisible : ∀ k, IsSelfVisible k (f k)
  /-- `h` is non-decreasing. -/
  monotone : ∀ x y, AtStage θ x → AtStage θ y → x ≤ y → h x ≤ h y
  /-- `h(-∞) = -∞`. -/
  map_bot : h ⊥ = ⊥
  /-- For all `i ≤ k` and `x` with `h(x) ≤ f(k)`,
  `h(visible<k>[i](x)) = visible<k>[i](h(x))`. -/
  comm : ∀ i k : ℕ, i ≤ k → ∀ x, AtStage θ x → h x ≤ f k →
    h (visibilityReplace k i x) = visibilityReplace k i (h x)

/-- **The relation `u ⇒ v`** [AFK26, Definition 4.27] at stage `θ`, for labellings `u`, `v` of
cells with grades `g`: some witness `(f, h)` has `v(d) = min {h(u(d)), f(g(d))}` for every cell
`d`. -/
def TemplateTransformsTo (θ : Ordinal.{u}) (g : D → ℕ) (u v : D → Label.{u}) : Prop :=
  ∃ f h, TemplateWitness θ f h ∧ ∀ d, v d = min (h (u d)) (f (g d))

/-- The witnesses of [AFK26, Definition 4.27] are those of [Kni26, Definition 2.3.9]. -/
theorem templateWitness_iff_printedWitness : TemplateWitness θ f h ↔ PrintedWitness θ f h :=
  ⟨fun hw ↦ ⟨hw.suppressor_atStage, hw.shifter_atStage, fun a b hab ↦ hw.antitone a b hab.le,
      fun k ↦ (hw.isSelfVisible k).symm, hw.map_bot, hw.monotone,
      fun x hx k hk i hik ↦ hw.comm i k hik x hx hk⟩,
    fun hw ↦ ⟨hw.suppressor_atStage, hw.shifter_atStage,
      fun a b hab ↦ (eq_or_lt_of_le hab).elim (fun e ↦ e ▸ le_rfl) (hw.antitone a b),
      fun k ↦ (hw.visibility k).symm, hw.monotone, hw.map_bot,
      fun i k hik x hx hk ↦ hw.comm x hx k hk i hik⟩⟩

/-- The relation of [AFK26, Definition 4.27] is that of [Kni26, Definition 2.3.9]. -/
theorem templateTransformsTo_iff_printedTransformsTo :
    TemplateTransformsTo θ g u v ↔ PrintedTransformsTo θ g u v :=
  exists_congr fun _ ↦ exists_congr fun _ ↦ and_congr_left' templateWitness_iff_printedWitness

/-- **The relation `u ⇒ v` is the transformation relation**: at a stage `θ` that is zero or a
limit, for labellings with values at stage `θ`, `u ⇒ v` in the sense of
[AFK26, Definition 4.27] exactly when `Label.TransformsTo g u v`. -/
theorem templateTransformsTo_iff (hθ : Order.IsSuccPrelimit θ) (hu : ∀ d, AtStage θ (u d))
    (hv : ∀ d, AtStage θ (v d)) : TemplateTransformsTo θ g u v ↔ TransformsTo g u v :=
  templateTransformsTo_iff_printedTransformsTo.trans (printedTransformsTo_iff hθ hu hv)

end Label

/-! ### Lawful labellings and bountiful rows -/

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) {θ : Ordinal.{u}}

/-- **Lawful local labellings** [AFK26, Definition 4.28], at stage `θ`: a local labelling
`r : D↓U → {-∞} ∪ θ ∪ {∞}` satisfying Orderliness, Locality, and Availability with respect to the
rows `R` (`ℓ_d = R.row d`).  The values of `r` at stage `θ` are a separate hypothesis wherever
they are needed. -/
structure TemplateLawfulLocal (θ : Ordinal.{u}) (U : Finset α × ℕ) (r : D.below U → Label.{u}) :
    Prop where
  /-- (Orderliness) For all `d ∈ D↓U`, the value `r(d)` is self-visible at `g(d)`. -/
  orderliness : ∀ d : D.below U, IsSelfVisible (D.grade d) (r d)
  /-- (Locality) For all `d ∈ D↓U`, `ℓ_d ⇒ r_d`, where `r_d : D↓d → {-∞} ∪ θ ∪ {∞}` is
  `r_d(e) = min {r(e), r(d)}`. -/
  locality : ∀ d : D.below U,
    TemplateTransformsTo θ (fun e : D.below (D.gradedIndex d) ↦ D.grade e) (R.row d)
      (fun e ↦ min (r (Set.inclusion (D.below_mono d.2) e)) (r d))
  /-- (Availability) For all `d, e ∈ D↓U`, if `s(d) ⊆ s(e)` and `g(d) = g(e)` then there is an
  `e' ∈ D` with `c(e) = c(e')` and `r(d) ≤ r(e')`; the cell `e'` lies in `D↓U`, where `r` is
  defined. -/
  availability : ∀ d e : D.below U, D.scope d ⊆ D.scope e → D.grade d = D.grade e →
    ∃ e' : ι, D.gradedIndex e' = D.gradedIndex e ∧ ∃ he' : e' ∈ D.below U, r d ≤ r ⟨e', he'⟩

/-- **Lawful labellings** [AFK26, Definition 4.28] ("in the obvious analogous way"), at stage
`θ`: a labelling `p : D → {-∞} ∪ θ ∪ {∞}` of all cells satisfying Orderliness, Locality, and
Availability with respect to the rows `R`. -/
structure TemplateLawful (θ : Ordinal.{u}) (p : ι → Label.{u}) : Prop where
  /-- (Orderliness) For all `d ∈ D`, the value `p(d)` is self-visible at `g(d)`. -/
  orderliness : ∀ d, IsSelfVisible (D.grade d) (p d)
  /-- (Locality) For all `d ∈ D`, `ℓ_d ⇒ p_d`, where `p_d(e) = min {p(e), p(d)}` on `D↓d`. -/
  locality : ∀ d, TemplateTransformsTo θ (fun e : D.below (D.gradedIndex d) ↦ D.grade e)
    (R.row d) (fun e ↦ min (p e) (p d))
  /-- (Availability) For all `d, e ∈ D`, if `s(d) ⊆ s(e)` and `g(d) = g(e)` then there is an
  `e' ∈ D` with `c(e) = c(e')` and `p(d) ≤ p(e')`. -/
  availability : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = D.grade e →
    ∃ e', D.gradedIndex e' = D.gradedIndex e ∧ p d ≤ p e'

/-- **The ball `B_γ(q)`** [AFK26, Definition 4.28], at stage `θ`: the lawful local labellings `r`
at `U` with values at stage `θ` such that `min {r, γ} = min {q, γ}`. -/
def templateBall (θ : Ordinal.{u}) (U : Finset α × ℕ) (γ : Label.{u})
    (q : D.below U → Label.{u}) : Set (D.below U → Label.{u}) :=
  {r | (∀ d, AtStage θ (r d)) ∧ R.TemplateLawfulLocal θ U r ∧ ∀ d, min (r d) γ = min (q d) γ}

/-- **Bountiful rows** [AFK26, Definition 4.28], at stage `θ`: for every graded face `U`, lawful
local map `q` with `dom(q) = D↓U` and values at stage `θ`, `γ ∈ {-∞} ∪ θ ∪ {∞}` self-visible at
`g(U)`, and graded face `V ≤ U`, `{r↾D↓V : r ∈ B_γ(q)} = B_γ(q↾D↓V)`. -/
def TemplateBountiful (θ : Ordinal.{u}) : Prop :=
  ∀ U ∈ D.gradedFaces, ∀ q : D.below U → Label.{u}, (∀ d, AtStage θ (q d)) →
    R.TemplateLawfulLocal θ U q → ∀ γ : Label.{u}, AtStage θ γ → IsSelfVisible U.2 γ →
    ∀ V ∈ D.gradedFaces, ∀ hVU : V ≤ U,
      (fun r ↦ r ∘ Set.inclusion (D.below_mono hVU)) '' R.templateBall θ U γ q =
        R.templateBall θ V γ (q ∘ Set.inclusion (D.below_mono hVU))

variable {R}

/-- The lawful local labellings of [AFK26, Definition 4.28] are those of the formalization of the
earlier draft (`CellScheme.Rows.PrintedLawfulLocal`): the relations `⇒` agree. -/
theorem templateLawfulLocal_iff_printedLawfulLocal {U : Finset α × ℕ}
    {r : D.below U → Label.{u}} : R.TemplateLawfulLocal θ U r ↔ R.PrintedLawfulLocal θ U r :=
  ⟨fun h ↦ ⟨h.orderliness,
      fun d ↦ Label.templateTransformsTo_iff_printedTransformsTo.mp (h.locality d),
      h.availability⟩,
    fun h ↦ ⟨h.orderliness,
      fun d ↦ Label.templateTransformsTo_iff_printedTransformsTo.mpr (h.locality d),
      h.availability⟩⟩

/-- **Lawful local labellings are the labellings lawful below `U`**: at a stage `θ` that is zero
or a limit, for rows and a labelling with values at stage `θ`. -/
theorem templateLawfulLocal_iff (hθ : Order.IsSuccPrelimit θ)
    (hR : ∀ s t, AtStage θ (R.row s t)) {U : Finset α × ℕ} {r : D.below U → Label.{u}}
    (hr : ∀ d, AtStage θ (r d)) : R.TemplateLawfulLocal θ U r ↔ R.IsLawfulBelow U r :=
  templateLawfulLocal_iff_printedLawfulLocal.trans (printedLawfulLocal_iff hθ hR hr)

/-- **Lawful labellings are the lawful sections**: at a stage `θ` that is zero or a limit, for
rows and a labelling with values at stage `θ`. -/
theorem templateLawful_iff (hθ : Order.IsSuccPrelimit θ) (hR : ∀ s t, AtStage θ (R.row s t))
    {p : ι → Label.{u}} (hp : ∀ d, AtStage θ (p d)) : R.TemplateLawful θ p ↔ R.IsLawful p :=
  ⟨fun h ↦ ⟨h.orderliness,
      fun d ↦ (templateTransformsTo_iff hθ (hR d) fun e ↦ (hp e).min (hp d)).mp (h.locality d),
      h.availability⟩,
    fun h ↦ ⟨h.orderly,
      fun d ↦ (templateTransformsTo_iff hθ (hR d) fun e ↦ (hp e).min (hp d)).mpr (h.locality d),
      h.availability⟩⟩

/-- **Bountiful rows are bountiful in the sense of [AFK26, Definition 4.28]**, at every stage `θ`
that is zero or a limit and carries the values of the rows: the native lift, reduced to stage
`θ`, lies in the ball and restricts to the given labelling. -/
theorem IsBountiful.templateBountiful (hθ : Order.IsSuccPrelimit θ)
    (hR : ∀ s t, AtStage θ (R.row s t)) (hb : R.IsBountiful) : R.TemplateBountiful θ := by
  intro U hU q hq hql γ hγ hγv V hV hVU
  ext r'
  constructor
  · rintro ⟨r, ⟨hrθ, hrl, hrc⟩, rfl⟩
    exact ⟨fun d ↦ hrθ _, (templateLawfulLocal_iff hθ hR fun d ↦ hrθ _).mpr
      (((templateLawfulLocal_iff hθ hR hrθ).mp hrl).mono hVU), fun d ↦ hrc _⟩
  · rintro ⟨hθr', hl', hc'⟩
    obtain ⟨q', hl, hc, hr⟩ := (isBountiful_iff_forall_exists R).mp hb hV hU hVU γ hγv r' q
      ((templateLawfulLocal_iff hθ hR hθr').mp hl') ((templateLawfulLocal_iff hθ hR hq).mp hql)
      fun d ↦ (hc' d).symm
    refine ⟨Label.reduce θ ∘ q', ⟨fun d ↦ atStage_reduce θ _,
      (templateLawfulLocal_iff hθ hR fun d ↦ atStage_reduce θ _).mpr (hl.reduce hθ),
      fun d ↦ ?_⟩, funext fun d ↦ ?_⟩
    · rw [Function.comp_apply, ← hγ.reduce_eq, ← (monotone_reduce θ).map_min, hc d,
        (monotone_reduce θ).map_min, hγ.reduce_eq, (hq d).reduce_eq]
    · simp only [Function.comp_apply]
      rw [hr d, (hθr' d).reduce_eq]

/-- **Bountiful rows in the sense of [AFK26, Definition 4.28] are bountiful**: for a scheme with
finitely many cells, at a stage `θ ≥ ω ^ 2` that is zero or a limit and carries the values of the
rows, bountifulness at the single stage `θ` (in particular at `ω₁`) gives
`CellScheme.Rows.IsBountiful`, which quantifies over all labels.  The labellings with values at
stage `θ` are handled by the printed definition, and arbitrary labellings by block compression
(`CellScheme.Rows.isBountiful_of_forall_atStage`). -/
theorem TemplateBountiful.isBountiful [Finite ι] (hθ : Order.IsSuccPrelimit θ)
    (hθ2 : ω ^ 2 ≤ θ) (hR : ∀ s t, AtStage θ (R.row s t)) (hb : R.TemplateBountiful θ) :
    R.IsBountiful := by
  refine isBountiful_of_forall_atStage hθ2 fun X Y hX hY hXY c hcθ hc p q hpθ hqθ hp hq hpq ↦ ?_
  have hpb : p ∈ R.templateBall θ X c (q ∘ Set.inclusion (D.below_mono hXY)) :=
    ⟨hpθ, (templateLawfulLocal_iff hθ hR hpθ).mpr hp, fun d ↦ (hpq d).symm⟩
  rw [← hb Y hY q hqθ ((templateLawfulLocal_iff hθ hR hqθ).mpr hq) c hcθ hc X hX hXY] at hpb
  obtain ⟨r, ⟨hrθ, hrl, hrc⟩, hr⟩ := hpb
  exact ⟨r, (templateLawfulLocal_iff hθ hR hrθ).mp hrl, hrc, fun d ↦ congrFun hr d⟩

/-- **Bountifulness of [AFK26, Definition 4.28] at one stage is bountifulness**: for a scheme
with finitely many cells, at a stage `θ ≥ ω ^ 2` that is zero or a limit and carries the values
of the rows. -/
theorem templateBountiful_iff [Finite ι] (hθ : Order.IsSuccPrelimit θ) (hθ2 : ω ^ 2 ≤ θ)
    (hR : ∀ s t, AtStage θ (R.row s t)) : R.TemplateBountiful θ ↔ R.IsBountiful :=
  ⟨fun h ↦ h.isBountiful hθ hθ2 hR, fun h ↦ h.templateBountiful hθ hR⟩

/-- **The definition of the earlier draft at one stage, with the cap `-∞`**: for a scheme with
finitely many cells, all with graded index in the graded plan, at a stage `θ ≥ ω ^ 2` that is
zero or a limit and carries the values of the rows, the rows are bountiful if they are bountiful
as printed in the earlier draft (`CellScheme.Rows.PrintedBountifulRows`, ordinal caps only) at
the single stage `θ` and every labelling lawful below a graded face extends to one lawful below
every larger graded face. -/
theorem isBountiful_of_printedBountifulRows [Finite ι] (hθ : Order.IsSuccPrelimit θ)
    (hθ2 : ω ^ 2 ≤ θ) (hR : ∀ s t, AtStage θ (R.row s t)) (h : R.PrintedBountifulRows θ)
    (hbot : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ hXY : X ≤ Y,
      Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono hXY)) {q | R.IsLawfulBelow Y q}
        {p | R.IsLawfulBelow X p}) :
    R.IsBountiful := by
  refine isBountiful_of_forall_atStage hθ2 fun X Y hX hY hXY c hcθ hc p q hpθ hqθ hp hq hpq ↦ ?_
  induction c using recBotCoeTop with
  | bot =>
    obtain ⟨q', hq', hr⟩ := hbot hX hY hXY hp
    exact ⟨q', hq', fun d ↦ by simp, fun d ↦ congrFun hr d⟩
  | top =>
    exact ⟨q, hq, fun _ ↦ rfl, fun d ↦ by simpa using hpq d⟩
  | coe o =>
    have heq := h Y X q o ⟨gradedFaces_subset_printedGradedFaces hY, hqθ,
      (printedLawfulLocal_iff hθ hR hqθ).mpr hq, atStage_coe.mp hcθ, hc,
      gradedFaces_subset_printedGradedFaces hX, hXY⟩
    have hpb : p ∈ R.printedBall θ X o (q ∘ Set.inclusion (D.below_mono hXY)) :=
      ⟨hpθ, (printedLawfulLocal_iff hθ hR hpθ).mpr hp, fun d ↦ (hpq d).symm⟩
    rw [← heq] at hpb
    obtain ⟨r, ⟨hrθ, hrl, hrc⟩, hr⟩ := hpb
    exact ⟨r, (printedLawfulLocal_iff hθ hR hrθ).mp hrl, hrc, fun d ↦ congrFun hr d⟩

end CellScheme.Rows

/-! ### Legal templates -/

namespace StageType

open CellScheme.Rows

variable {α θ : Ordinal.{u}} {n : ℕ}

/-- **Legal templates** [AFK26, Definition 4.29], with labels in `{-∞} ∪ θ ∪ {∞}` ([AFK26] takes
`θ = ω₁`), in the fixed-rows reading: the frame `c` is the graded index of the cells of `t`, the
row system `Σ = (ℓ_d)_{d ∈ D}` its rows, and the label `p` its label section.  The template data
(plan, frame, finitely many cells, rows below `ω ^ 2`) are those of the stage type.  A stage type
carries the native lawfulness of its labels (`StageType.isLawful`); clause 2 is stated here as
printed all the same.  This is not `StageType.IsStronglyCodedLegal`; the two are compared in
`StageType.isLegalTemplate_iff`. -/
structure IsLegalTemplate (θ : Ordinal.{u}) (t : StageType.{u} α n) : Prop where
  /-- [AFK26, Definition 4.4]: the label `p` takes values in `{-∞} ∪ θ ∪ {∞}`. -/
  label_atStage : ∀ d, AtStage θ (t.label d)
  /-- Clause 1: `range(c) = GradedFace[P]`, i.e., every graded face has a cell. -/
  range_gradedIndex : Set.range t.toCellScheme.gradedIndex = t.toCellScheme.gradedFaces
  /-- Clause 2: `p` is lawful with respect to `Σ`. -/
  lawful : t.rows.TemplateLawful θ t.label
  /-- Clause 3: for each `d ∈ D`, `ℓ_d` is lawful (a lawful local labelling at `c(d)`). -/
  row_lawful : ∀ d, t.rows.TemplateLawfulLocal θ (t.toCellScheme.gradedIndex d) (t.rows.row d)
  /-- Clause 4: the rows of `(ℓ_d)_{d ∈ D}` are bountiful. -/
  bountiful : t.rows.TemplateBountiful θ
  /-- Clause 5: for each `d`, `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : n ∈ ω, i ≤ g(d) + 1}`. -/
  row_range : ∀ d (e : t.toCellScheme.below (t.toCellScheme.gradedIndex d)),
    t.rows.row d e = ⊥ ∨ ∃ m i : ℕ, i ≤ t.toCellScheme.grade d + 1 ∧
      t.rows.row d e = ((ω * m + i : Ordinal.{u}) : Label.{u})

/-- **Legal templates are the strongly coded legal stage types**: at a stage `θ ≥ ω ^ 2` that is
zero or a limit, a stage type is a legal template of [AFK26, Definition 4.29] with labels at
stage `θ` exactly when it is strongly coded legal and its labels lie at stage `θ`.  Clause 4 at
the single stage `θ` is bountifulness by `CellScheme.Rows.templateBountiful_iff`. -/
theorem isLegalTemplate_iff (hθ : Order.IsSuccPrelimit θ) (hθ2 : ω ^ 2 ≤ θ)
    {t : StageType.{u} α n} :
    t.IsLegalTemplate θ ↔ t.IsStronglyCodedLegal ∧ ∀ d, AtStage θ (t.label d) := by
  have hR : ∀ s e, AtStage θ (t.rows.row s e) := t.isCoded.atStage hθ2
  refine ⟨fun h ↦ ⟨⟨isLegal_iff.mpr ⟨fun d ↦ (templateLawfulLocal_iff hθ hR (hR d)).mp
      (h.row_lawful d), h.bountiful.isBountiful hθ hθ2 hR, fun X hX ↦ by
        rw [← h.range_gradedIndex] at hX
        exact hX⟩, fun s e ↦ h.row_range s e⟩, h.label_atStage⟩, fun ⟨⟨hl, hs⟩, hθl⟩ ↦ ?_⟩
  obtain ⟨hcons, hb, hcomp⟩ := isLegal_iff.mp hl
  exact { label_atStage := hθl
          range_gradedIndex := Set.Subset.antisymm
            (Set.range_subset_iff.mpr t.isWellFormed.isWellFormed.gradedIndex_mem) hcomp
          lawful := (templateLawful_iff hθ hR hθl).mpr t.isLawful
          row_lawful := fun d ↦ (templateLawfulLocal_iff hθ hR (hR d)).mpr (hcons d)
          bountiful := hb.templateBountiful hθ hR
          row_range := hs }

/-- **Legal templates at `ω₁`** [AFK26, Definition 4.29]: a stage type is a legal template with
labels in `{-∞} ∪ ω₁ ∪ {∞}` exactly when it is strongly coded legal with labels at stage `ω₁`. -/
theorem isLegalTemplate_omega_one_iff {t : StageType.{u} α n} :
    t.IsLegalTemplate ω₁ ↔ t.IsStronglyCodedLegal ∧ ∀ d, AtStage ω₁ (t.label d) :=
  isLegalTemplate_iff (Cardinal.isSuccLimit_omega 1).isSuccPrelimit omega0_sq_lt_omega_one.le

/-- **Legal templates at a countable stage**: a stage type at a stage `α ≤ ω₁` is a legal
template of [AFK26, Definition 4.29] exactly when it is strongly coded legal. -/
theorem isLegalTemplate_omega_one_iff_of_le (hα : α ≤ ω₁) {t : StageType.{u} α n} :
    t.IsLegalTemplate ω₁ ↔ t.IsStronglyCodedLegal :=
  isLegalTemplate_omega_one_iff.trans (and_iff_left fun d ↦ (t.atStage d).mono hα)

/-- **Legal templates at a block stage**: for `β < ω₁`, a stage type at the block stage
`ω + ω · β` is a legal template of [AFK26, Definition 4.29] exactly when it is strongly coded
legal. -/
theorem isLegalTemplate_blockStage_iff {β : Ordinal.{u}} (hβ : β < ω₁)
    {t : StageType.{u} (blockStage β) n} : t.IsLegalTemplate ω₁ ↔ t.IsStronglyCodedLegal :=
  isLegalTemplate_omega_one_iff_of_le (blockStage_lt_omega_one hβ).le

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Legal

/-!
# Correspondence: stage types and face maps

Roadmap, "Manuscript concordance", row 8.  The printed definitions of the type spaces
[Kni26, Definition 3.1.1] and of their face maps [Kni26, Definition 3.1.5] are compiled clause by
clause and identified with the legal stage types (`StageType.IsLegal`) and the face maps
`StageType.restrictFace`.

## Types, [Kni26, Definition 3.1.1]

A type on the points `Fin n` is a labelling `p` of the cells of a scheme `S`
(`Scheme.PrintedType S θ α p`):

| Printed clause | Field of `PrintedType` | Here |
| --- | --- | --- |
| for some plan `P` on `A` | `isPlan` | `Scheme.IsWellFormed.isPlan` |
| for some domain `D` on `P` | `domain` | `Scheme.IsLegal` (row 7, corrected) |
| `p : D → {-∞} ∪ α ∪ {∞}` | `atStage` | `StageType.atStage` |
| `p` respects the semantics associated with `D` | `respects` | `StageType.isLawful` (row 4) |

**Identification.**  At a stage `θ` that is zero or a limit with `ω ^ 2 ≤ θ` and `α ≤ θ`, a
labelling is a type as printed exactly when the scheme is legal and the labelling is a lawful
section with labels at stage `α` (`Scheme.printedType_iff`); on the printed labels
`{-∞} ∪ ω₁ ∪ {∞}` the only hypothesis is `α ≤ ω₁` (`Scheme.printedType_omega_one_iff`).  So a
stage type is legal exactly when its scheme and labels are a type as printed
(`StageType.isLegal_iff_printedType`), and the legal stage types at stage `α ≤ ω₁` on `n` points
are in bijection with the types as printed on `Fin n`, by forgetting the laws
(`StageType.legalEquivPrintedType`).

## Face maps, [Kni26, Definition 3.1.5]

For a one-to-one `f : A → B` with `ran f ∈ P`, `(S^α f)(p)` is the labelling of the domain
`D' = (Df)[D⟨ran f, |A|⟩]` with `(S^α f)(p)((Df)(Ξ)) = p(Ξ)`, where `Df` and `D'` are those of
[Kni26, Proposition 2.6.3, clause 5] and its proof.  Here `u` is `(S^α f)(t)` along a map `φ`
from the cells of `u` to those of `t`, the inverse of `Df` (`StageType.PrintedFaceMap f t u φ`):

| Printed clause | Field of `PrintedFaceMap` | Here |
| --- | --- | --- |
| `S^α f` is defined at `p` when `ran f ∈ P` | `range_mem` | `StageType.restrictFace_of_mem` |
| `D'` is on the plan `(Pf)(P) = {C : f[C] ∈ P}` | `mem_faces_iff` | `Scheme.mem_comap_faces` |
| `Df` is a bijection of `D⟨ran f, \|A\|⟩` onto `D'` | `injective`, `mem_range_iff` | `cellMap` |
| `Df(Ξ)` has scope `f⁻¹[C]`, the arity of `Ξ` | `map_scope`, `grade_eq` | `map_comap_scope` |
| `E'(Df(Ξ))(Df(Θ)) = E(Ξ)(Θ)` | `row_eq` | `Scheme.comap_row` |
| `(S^α f)(p)((Df)(Ξ)) = p(Ξ)` | `label_eq` | `StageType.comap_label` |

**Identification.**  `restrictFace f t = some u` exactly when `u` is a printed face map of `t`
along `f` for a strictly monotone `φ` (`StageType.restrictFace_eq_some_iff_exists_printedFaceMap`),
and `restrictFace f t = none` exactly when `ran f ∉ P` (`StageType.restrictFace_eq_none_iff`).
The laws required of the face maps by [Kni26, Definition 3.1.5]: `S^α ι_{A,A}` is the identity
(`StageType.restrictFace_refl`); `S^α (f ∘ g) ⊇ (S^α g) ∘ (S^α f)`
(`StageType.restrictFace_trans_of_bind_eq_some`); and equality along bijections, which are
canonical isomorphisms (`StageType.restrictFace_equiv`, `StageType.reindex_reindex`,
`StageType.reindex_refl`).

**Departures.**
1. *The domain* is the domain as corrected in row 7 (`Scheme.IsLegal`, status C there): with
   coded rows and bountifulness at every stage.
2. *The points.*  The printed `S^α A` is on a finite set `A`; here the points are `Fin n`, as for
   the spaces `S^α n` of [Kni26, Definition 3.2.1], and the plan is on all of them.
3. *The stage.*  The printed `α ≤ ω₁` is a limit; `StageType α n` is defined at every ordinal
   `α`.  Harmless: the identifications above hold for every `α ≤ θ`, limit or not.
4. *The labels of `⇒`.*  Respect [Kni26, Definition 2.5.4] is printed for labellings with values
   in `{-∞} ∪ ω₁ ∪ {∞}`; it is stated at a stage `θ`, and `θ = ω₁` is
   `Scheme.printedType_omega_one_iff`.
5. *The scheme of a type is data.*  A printed type `p` determines its domain `dom p`, and the
   semantics through the coding; here a stage type carries its scheme as a field, as for the
   coding clause of row 7.
6. *The numbering of the cells of a face.*  The printed `Df` keeps the code of each cell.  Here
   the code of a cell is its position, and the face map numbers the cells of `u` in the
   increasing order of the corresponding cells of `t` (`StrictMono φ`); with this numbering the
   printed face map is `restrictFace`.  This is the coding of row 7, not a further clause.

The inclusion case of the face maps, `(S^α ι_{B,A})(p) = p↾D⟨B,|B|⟩`, is the second clause of
[Kni26, Definition 3.1.2]; its first clause, stage reduction, is row 10.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Types -/

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) {θ α : Ordinal.{u}} {p : Fin S.card → Label.{u}}

/-- **Types** [Kni26, Definition 3.1.1], on the points `Fin n` at stage `α`, with the relation `⇒`
at stage `θ`: `p` is a labelling of the cells of a domain on a plan on all the points, with
values in `{-∞} ∪ α ∪ {∞}`, respecting the semantics of the domain.  The domain is the domain as
corrected in row 7 (`Scheme.IsLegal`). -/
structure PrintedType (θ α : Ordinal.{u}) (p : Fin S.card → Label.{u}) : Prop where
  /-- [Kni26, Definition 3.1.1]: for some plan `P` on `A`. -/
  isPlan : Geometry.IsPlan univ S.toCellScheme.faces
  /-- [Kni26, Definition 3.1.1]: for some domain `D` on `P` ([Kni26, Definition 2.6.1], as
  corrected in row 7). -/
  domain : S.IsLegal
  /-- [Kni26, Definition 3.1.1]: `p : D → {-∞} ∪ α ∪ {∞}`. -/
  atStage : ∀ d, AtStage α (p d)
  /-- [Kni26, Definition 3.1.1]: `p` respects the semantics associated with `D`
  ([Kni26, Definition 2.5.4]). -/
  respects : S.rows.PrintedRespects θ p

variable {S}

/-- **Types are the lawful sections of legal schemes** [Kni26, Definition 3.1.1]: at a stage `θ`
that is zero or a limit, at least `ω ^ 2`, and at least `α`, a labelling is a type as printed
exactly when the scheme is legal and the labelling is a lawful section with labels at stage
`α`. -/
theorem printedType_iff (hθ : Order.IsSuccPrelimit θ) (hθ₂ : Ordinal.omega0 ^ 2 ≤ θ)
    (hαθ : α ≤ θ) :
    S.PrintedType θ α p ↔ S.IsLegal ∧ S.rows.IsLawful p ∧ ∀ d, AtStage α (p d) := by
  have key (hS : S.IsLegal) (hp : ∀ d, AtStage α (p d)) :=
    S.rows.printedRespects_iff hθ hS.isWellFormed.isWellFormed.gradedIndex_mem
      (hS.isCoded.atStage hθ₂) fun d ↦ (hp d).mono hαθ
  exact ⟨fun h ↦ ⟨h.domain, (key h.domain h.atStage).mp h.respects, h.atStage⟩,
    fun ⟨hS, hl, hp⟩ ↦ ⟨hS.isWellFormed.isPlan, hS, hp, (key hS hp).mpr hl⟩⟩

/-- **Types are the lawful sections of legal schemes** [Kni26, Definition 3.1.1], on the printed
labels `{-∞} ∪ ω₁ ∪ {∞}`: for `α ≤ ω₁`, a labelling is a type as printed exactly when the scheme
is legal and the labelling is a lawful section with labels at stage `α`. -/
theorem printedType_omega_one_iff (hα : α ≤ Ordinal.omega.{u} 1) :
    S.PrintedType (Ordinal.omega.{u} 1) α p ↔
      S.IsLegal ∧ S.rows.IsLawful p ∧ ∀ d, AtStage α (p d) :=
  printedType_iff (Cardinal.isSuccLimit_omega 1).isSuccPrelimit omega0_sq_lt_omega_one.le hα

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **Legal stage types are the types as printed** [Kni26, Definition 3.1.1]: for `α ≤ ω₁`, a
stage type is legal exactly when its scheme and labels are a type as printed. -/
theorem isLegal_iff_printedType (t : StageType.{u} α n) (hα : α ≤ Ordinal.omega.{u} 1) :
    t.IsLegal ↔ t.toScheme.PrintedType (Ordinal.omega.{u} 1) α t.label := by
  rw [Scheme.printedType_omega_one_iff hα]
  exact ⟨fun h ↦ ⟨h, t.isLawful, t.atStage⟩, fun h ↦ h.1⟩

/-- **The type space as printed** [Kni26, Definition 3.1.1]: for `α ≤ ω₁`, the legal stage types
at stage `α` on `n` points correspond to the types as printed on `Fin n` (a scheme with a
labelling of its cells), by forgetting the laws. -/
def legalEquivPrintedType (hα : α ≤ Ordinal.omega.{u} 1) :
    {t : StageType.{u} α n // t.IsLegal} ≃
      {x : (S : Scheme.{u} n) × (Fin S.card → Label.{u}) //
        x.1.PrintedType (Ordinal.omega.{u} 1) α x.2} where
  toFun t := ⟨⟨t.1.toScheme, t.1.label⟩, (isLegal_iff_printedType t.1 hα).mp t.2⟩
  invFun x :=
    have h := (Scheme.printedType_omega_one_iff hα).mp x.2
    ⟨{ toScheme := x.1.1
       label := x.1.2
       isWellFormed := h.1.isWellFormed
       isCoded := h.1.isCoded
       isLawful := h.2.1
       atStage := h.2.2 }, h.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Face maps -/

/-- The cells below the pair of the range of `f` with grade `m` are those whose scope lies in the
range of `f`. -/
theorem mem_below_map_univ_iff (t : StageType.{u} α n) (f : Fin m ↪ Fin n) (d : Fin t.card) :
    d ∈ t.toCellScheme.below (univ.map f, m) ↔
      (t.toCellScheme.scope d : Set (Fin n)) ⊆ Set.range f := by
  have hsub : t.toCellScheme.scope d ⊆ univ.map f ↔
      (t.toCellScheme.scope d : Set (Fin n)) ⊆ Set.range f := by
    rw [← coe_subset, coe_map, coe_univ, Set.image_univ]
  rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff, hsub]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  calc t.toCellScheme.grade d ≤ #(t.toCellScheme.scope d) :=
        t.isWellFormed.isWellFormed.grade_le_card d
    _ ≤ #(univ.map f) := card_le_card (hsub.mpr h)
    _ = m := by simp

/-- **Face maps** [Kni26, Definition 3.1.5]: `u` is `(S^α f)(t)`, its cells corresponding to the
cells of `t` over the range of `f` along `φ`, the inverse of the map `Df` of
[Kni26, Proposition 2.6.3, clause 5]. -/
structure PrintedFaceMap (f : Fin m ↪ Fin n) (t : StageType.{u} α n) (u : StageType.{u} α m)
    (φ : Fin u.card → Fin t.card) : Prop where
  /-- [Kni26, Definition 3.1.5]: `S^α f` is defined at `t` when `ran f ∈ P`. -/
  range_mem : univ.map f ∈ t.toCellScheme.faces
  /-- [Kni26, Definition 2.1.9 and Proposition 2.6.3, clause 5]: the plan of `u` is
  `(Pf)(P) = {C : f[C] ∈ P}`. -/
  mem_faces_iff : ∀ C : Finset (Fin m), C ∈ u.toCellScheme.faces ↔ C.map f ∈ t.toCellScheme.faces
  /-- [Kni26, Proposition 2.6.3, clause 5]: `Df` is a bijection, here `φ` is one-to-one. -/
  injective : Function.Injective φ
  /-- [Kni26, Proposition 2.6.3, clause 5]: `Df` is defined on `D⟨ran f, |A|⟩`, here the range
  of `φ`. -/
  mem_range_iff : ∀ d, d ∈ Set.range φ ↔ d ∈ t.toCellScheme.below (univ.map f, m)
  /-- The definition of `Df` in [Kni26, Proposition 2.6.3]: `Df(Ξ)` has scope `f⁻¹[C]` for `Ξ` of
  scope `C`. -/
  map_scope : ∀ i, (u.toCellScheme.scope i).map f = t.toCellScheme.scope (φ i)
  /-- The definition of `Df` in [Kni26, Proposition 2.6.3]: `Df(Ξ)` has the arity of `Ξ`. -/
  grade_eq : ∀ i, u.toCellScheme.grade i = t.toCellScheme.grade (φ i)
  /-- [Kni26, Proposition 2.6.3, clause 5]: `E'(Df(Ξ))(Df(Θ)) = E(Ξ)(Θ)`. -/
  row_eq : ∀ s (r : u.toCellScheme.below (u.toCellScheme.gradedIndex s))
    (r' : t.toCellScheme.below (t.toCellScheme.gradedIndex (φ s))), r'.1 = φ r.1 →
      u.rows.row s r = t.rows.row (φ s) r'
  /-- [Kni26, Definition 3.1.5]: `(S^α f)(p)((Df)(Ξ)) = p(Ξ)`. -/
  label_eq : ∀ i, u.label i = t.label (φ i)

/-- **The face maps are the printed face maps** [Kni26, Definition 3.1.5]: the face map of `t`
along `f` is `u` exactly when `u` is a printed face map of `t` along `f`, its cells numbered in
the increasing order of the corresponding cells of `t`. -/
theorem restrictFace_eq_some_iff_exists_printedFaceMap (t : StageType.{u} α n)
    (f : Fin m ↪ Fin n) {u : StageType.{u} α m} :
    restrictFace f t = some u ↔ ∃ φ, StrictMono φ ∧ PrintedFaceMap f t u φ := by
  constructor
  · intro h
    obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp h
    refine ⟨t.cellMap f, (t.cellMap f).strictMono, ⟨hf, fun C ↦ Scheme.mem_comap_faces _ f,
      (t.cellMap f).injective, fun d ↦ ?_, t.map_comap_scope f, fun _ ↦ rfl, fun s r r' hr ↦ ?_,
      fun _ ↦ rfl⟩⟩
    · rw [mem_below_map_univ_iff, ← Scheme.mem_visibleCells, ← mem_coe, ← Scheme.range_cellMap]
      exact Iff.rfl
    · change t.rows.row (t.cellMap f s)
        ⟨t.cellMap f r.1, ((t.isLowerEmbedding_comap f).le_iff _ _).mpr r.2⟩ = _
      exact t.rows.row_congr rfl hr.symm
  · rintro ⟨φ, hφ, h⟩
    have hr (d : Fin t.card) : d ∈ Set.range φ ↔ d ∈ t.visibleCells f := by
      rw [h.mem_range_iff, mem_below_map_univ_iff, Scheme.mem_visibleCells]
    have key {i : Fin u.card} {j : Fin (t.toScheme.comap f).card} (hij : (i : ℕ) = j) :
        φ i = t.cellMap f j :=
      t.cellMap_eq_of_strictMono f hφ hr hij
    have hS : t.toScheme.comap f = u.toScheme := by
      refine Scheme.ext ((t.comap_card f).trans (t.card_visibleCells_eq_of_strictMono f hφ hr))
        ((t.isWellFormed.comap f h.range_mem).ground_eq.trans u.isWellFormed.ground_eq.symm)
        ?_ ?_ ?_ ?_
      · ext C
        rw [Scheme.mem_comap_faces, h.mem_faces_iff]
      · intro i j hij
        rw [Scheme.comap_scope, ← key hij.symm, ← h.map_scope, preimage_map]
      · intro i j hij
        rw [Scheme.comap_grade, ← key hij.symm, h.grade_eq]
      · intro s s' r r' hs hr'
        have hmem : φ r'.1 ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex (φ s')) := by
          rw [key hr'.symm, key hs.symm]
          exact ((t.isLowerEmbedding_comap f).le_iff _ _).mpr r.2
        rw [h.row_eq s' r' ⟨φ r'.1, hmem⟩ rfl, Scheme.comap_row]
        exact t.rows.row_congr (key hs.symm).symm (key hr'.symm).symm
    rw [restrictFace_of_mem t f h.range_mem]
    refine congrArg some (ext hS fun i j hij ↦ ?_)
    rw [comap_label, h.label_eq, key hij.symm]

/-- **The composition law of the face maps** [Kni26, Definition 3.1.5],
`S^α (f ∘ g) ⊇ (S^α g) ∘ (S^α f)`: if the face map along `f` and then the face map along `g` are
defined with value `v`, the face map along the composite is defined with value `v`. -/
theorem restrictFace_trans_of_bind_eq_some (t : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (g : Fin k ↪ Fin m) {v : StageType.{u} α k}
    (h : (restrictFace f t).bind (restrictFace g) = some v) :
    restrictFace (g.trans f) t = some v := by
  rw [bind_restrictFace] at h
  split_ifs at h
  exact h

end StageType

end VaughtConjecture

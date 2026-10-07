/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Basic

/-!
# Templates and the coherent local rows of a labelling

Roadmap, "Manuscript correspondence (required)", item 1, and Layer 2, "The templates of [AFK26]
and the stage types here"; concordance row 9.

**The printed templates.**  A template [AFK26, Definition 4.6] is a frame with a row system: a
frame [AFK26, Definition 4.4] on a plan `P` [AFK26, Definition 4.1] gives each cell `d` of a set
`D` a graded face `(B, j)` of `P`, that is `B ∈ P` and `j ≤ |B|`, its scope and grade
[AFK26, Definition 4.2]; the cells below `d` are those whose scope and grade are at most those of
`d`; and a row system [AFK26, Definition 4.5] is a local label `ℓ_d` at every cell `d`, a label of
each cell below `d`.  This is `Template`, whose fields are the clauses:

* `frame`, a cell scheme on the points `Fin n` with cells `Fin card`: its faces are `P`, and its
  scopes and grades are the map `c : D → GF(P)`;
* `isFrame` (`IsFrame`): the faces form a plan on the ground set (`Geometry.IsPlan`), the scope of
  every cell is a face, and its grade is at most the size of the scope, the grade `0` allowed;
* `rows`, a `RowSystem`.

The plan clause is transcribed as the recursive plan `Geometry.IsPlan`, which is a finite convex
geometry with exactly two extreme points on every closed set of at least two points
(`Geometry.isPlan_iff_isConvexGeometry_and_card_extremes`); its clause-by-clause comparison with
[AFK26, Definition 4.1] is not recorded here.  The `β`-truncation of a template
[AFK26, Definition 4.10] applies the function of [AFK26, Definitions 3.12 and 4.9], which is the
stage reduction `Label.reduce β` (`Label.reduce_coe_eq_ite`), to every entry of every local label
(`Template.reduce`).

**Stage types as templates.**  A stage type is a scheme with fixed coded rows (the semantics) and a
separate lawful labelling `p` of its cells.  Its template (`StageType.toTemplate`) is its frame
with the **coherent local rows** of its labelling, `r_d(e) = min (p e) (p d)` for the cells `e`
below `d` (`coherentRows`).

* **The labels are recovered from the diagonal**: `r_d(d) = p d` (`diagonal_coherentRows`).
* **Coherent row systems**: a row system is coherent (`RowSystem.IsCoherent`) when
  `r_d(e) = min (r_e(e)) (r_d(d))` for every `e` below `d`; it is then the coherent local rows of
  its diagonal (`RowSystem.IsCoherent.coherentRows_diagonal`), and the coherent row systems are
  exactly the coherent local rows of labellings (`isCoherent_iff_exists_eq_coherentRows`).
* **Both round trips**: on a scheme, the lawful labellings and the coherent row systems with a
  lawful diagonal correspond by the mutually inverse maps `coherentRows` and
  `RowSystem.diagonal` (`lawfulRowsEquiv`); a stage type is determined by its scheme and its
  template (`StageType.eq_of_toTemplate_eq`), and a well-formed scheme with coded rows and a
  coherent row system whose diagonal is lawful at stage `α` is the scheme and template of a stage
  type (`StageType.ofCoherentRows`, `StageType.toTemplate_ofCoherentRows`,
  `StageType.ofCoherentRows_toTemplate`).
* **Compatibility with projection**: the template of the stage reduction of a stage type is the
  entrywise reduction of its template (`StageType.toTemplate_reduce`): on coherent local rows,
  stage reduction of the labelling and the printed truncation of every row entry agree, since
  reduction is monotone and so commutes with `min`.
* **Compatibility with restriction**: the local rows of the restriction of a stage type to a closed
  face are the local rows of the corresponding cells (`StageType.coherentRows_comap`), as in the
  restriction of a template to a closed set [AFK26, Definition 4.8], which keeps the local label
  of every cell of the closed set; the restriction is undefined exactly when the face is not
  closed (`StageType.restrictFace_eq_none_iff`), and then the printed restriction is undefined
  too.

**Departures.**  The cells of a template here are `Fin card`, finitely many, while the printed set
of cells is arbitrary.  The frames of the stage types are well formed (`Scheme.IsWellFormed`), and
the well-formed cell schemes are exactly the frames with finitely many cells and positive grades
(`isWellFormed_iff_isFrame`), while a printed graded face allows the grade `0`; the stage types
carry their fixed coded rows, which a printed template does not; the printed restriction keeps
the points of the closed set, while the restriction here renames them along the embedding `f`;
and the row systems of the stage types are the coherent ones.  Whether the legal templates
of [AFK26, Definition 4.27] (with the lawful local labellings and bountiful rows of
[AFK26, Definition 4.26]) are exactly the coherent ones is not settled by these theorems.

## Placement

The concordance row and its note are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".

## References

[AFK26] is the draft *A counterexample to Vaught's Conjecture for `L_{ω₁ω}`* (2026), recorded in
`roadmap/REFERENCES.bib`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Correspondence

variable {ι α : Type*} {D : CellScheme ι α}

/-- A **row system** on a cell scheme [AFK26, Definition 4.5]: a local label at every cell `d`, a
label of each cell below `d`. -/
abbrev RowSystem (D : CellScheme ι α) : Type _ :=
  ∀ d : ι, D.below (D.gradedIndex d) → Label.{u}

/-- The **coherent local rows** of a labelling `p`: `r_d(e) = min (p e) (p d)` for the cells `e`
below `d`. -/
noncomputable def coherentRows (D : CellScheme ι α) (p : ι → Label.{u}) : RowSystem.{u} D :=
  fun d e ↦ min (p e) (p d)

namespace RowSystem

/-- The **diagonal** of a row system: the entry `r_d(d)` of each cell in its own local label. -/
def diagonal (r : RowSystem.{u} D) : ι → Label.{u} :=
  fun d ↦ r d ⟨d, D.mem_below_gradedIndex d⟩

/-- A row system is **coherent** when `r_d(e) = min (r_e(e)) (r_d(d))` for every `e` below `d`. -/
def IsCoherent (r : RowSystem.{u} D) : Prop :=
  ∀ d (e : D.below (D.gradedIndex d)), r d e = min (r.diagonal e) (r.diagonal d)

end RowSystem

/-- **The labels are recovered from the diagonal** of the coherent local rows: `r_d(d) = p d`. -/
@[simp] theorem diagonal_coherentRows (p : ι → Label.{u}) :
    (coherentRows D p).diagonal = p :=
  funext fun _ ↦ min_self _

/-- The coherent local rows of a labelling are coherent. -/
theorem isCoherent_coherentRows (p : ι → Label.{u}) : (coherentRows D p).IsCoherent := by
  intro d e
  simp [coherentRows]

/-- **A coherent row system is the coherent local rows of its diagonal.** -/
theorem RowSystem.IsCoherent.coherentRows_diagonal {r : RowSystem.{u} D} (hr : r.IsCoherent) :
    coherentRows D r.diagonal = r :=
  funext fun d ↦ funext fun e ↦ (hr d e).symm

/-- **The coherent row systems are the coherent local rows of labellings.** -/
theorem isCoherent_iff_exists_eq_coherentRows {r : RowSystem.{u} D} :
    r.IsCoherent ↔ ∃ p, coherentRows D p = r :=
  ⟨fun hr ↦ ⟨_, hr.coherentRows_diagonal⟩, fun ⟨_, hp⟩ ↦ hp ▸ isCoherent_coherentRows _⟩

/-- A labelling is determined by its coherent local rows. -/
theorem coherentRows_injective : Function.Injective (coherentRows.{u} D) := fun p q h ↦ by
  rw [← diagonal_coherentRows (D := D) p, h, diagonal_coherentRows]

/-- **Both round trips between lawful labellings and coherent row systems**: on a scheme, the
lawful labellings correspond to the coherent row systems with a lawful diagonal, by the coherent
local rows and the diagonal. -/
noncomputable def lawfulRowsEquiv {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) :
    {p : ι → Label.{u} // R.IsLawful p} ≃
      {r : RowSystem.{u} D // r.IsCoherent ∧ R.IsLawful r.diagonal} where
  toFun p := ⟨coherentRows D p.1, isCoherent_coherentRows _, by simpa using p.2⟩
  invFun r := ⟨r.1.diagonal, r.2.2⟩
  left_inv p := Subtype.ext (diagonal_coherentRows p.1)
  right_inv r := Subtype.ext r.2.1.coherentRows_diagonal

/-- A cell scheme is a **frame** [AFK26, Definition 4.4] when its faces form a plan on its ground
set (`Geometry.IsPlan`, for the plan of [AFK26, Definition 4.1]) and every cell is mapped to a
graded face of the plan [AFK26, Definition 4.2]: its scope is a face, and its grade is at most the
size of its scope.  The grade `0` is allowed. -/
structure IsFrame [DecidableEq α] (D : CellScheme ι α) : Prop where
  /-- The faces form a plan on the ground set [AFK26, Definition 4.1]. -/
  isPlan : Geometry.IsPlan D.ground D.faces
  /-- The scope of every cell is a face of the plan [AFK26, Definition 4.2]. -/
  scope_mem (d : ι) : D.scope d ∈ D.faces
  /-- The grade of every cell is at most the size of its scope [AFK26, Definition 4.2]. -/
  grade_le_card (d : ι) : D.grade d ≤ #(D.scope d)

/-- A well-formed cell scheme is a frame. -/
theorem isFrame_of_isWellFormed [DecidableEq α] (hD : D.IsWellFormed) : IsFrame D :=
  ⟨hD.isPlan, hD.scope_mem, hD.grade_le_card⟩

/-- **The well-formed cell schemes are the frames with finitely many cells and positive grades**:
the laws of a cell scheme here are the printed frame conditions together with the finiteness of
the cells and the positivity of the grades, where a printed graded face allows the grade `0`. -/
theorem isWellFormed_iff_isFrame [DecidableEq α] :
    D.IsWellFormed ↔ Finite ι ∧ IsFrame D ∧ ∀ d, 0 < D.grade d :=
  ⟨fun hD ↦ ⟨hD.finite, isFrame_of_isWellFormed hD, hD.grade_pos⟩, fun ⟨hf, hD, hpos⟩ ↦
    ⟨hf, hD.isPlan, fun d ↦ ⟨hD.scope_mem d, hpos d, hD.grade_le_card d⟩⟩⟩

/-- A **template** [AFK26, Definition 4.6], one field for each clause: a frame on the points
`Fin n` with cells `Fin card` ([AFK26, Definition 4.4]: the faces of the cell scheme are the plan,
and its scopes and grades map the cells to graded faces) and a row system on it
([AFK26, Definition 4.5]). -/
structure Template (n : ℕ) : Type (u + 1) where
  /-- The number of cells. -/
  card : ℕ
  /-- The frame: the plan, and the scope and grade of each cell. -/
  frame : CellScheme (Fin card) (Fin n)
  /-- The frame conditions: the faces form a plan, and every cell has a graded face. -/
  isFrame : IsFrame frame
  /-- The row system: a local label at every cell. -/
  rows : RowSystem.{u} frame

/-- The **entrywise stage reduction** of a template to `β`, the `β`-truncation of a template of
[AFK26, Definition 4.10]: every entry of every local label is reduced to `β`. -/
noncomputable def Template.reduce {n : ℕ} (β : Ordinal.{u}) (t : Template.{u} n) :
    Template.{u} n :=
  ⟨t.card, t.frame, t.isFrame, fun d e ↦ Label.reduce β (t.rows d e)⟩

end Correspondence

namespace StageType

open Correspondence

variable {α β : Ordinal.{u}} {n m : ℕ} (t : StageType.{u} α n)

/-- The **template of a stage type**: its frame with the coherent local rows of its labelling. -/
noncomputable def toTemplate : Template.{u} n :=
  ⟨t.card, t.toCellScheme, isFrame_of_isWellFormed t.isWellFormed.isWellFormed,
    coherentRows t.toCellScheme t.label⟩

/-- The labels of a stage type are the diagonal of its template. -/
@[simp] theorem diagonal_toTemplate : t.toTemplate.rows.diagonal = t.label :=
  diagonal_coherentRows _

/-- **A stage type is determined by its scheme and its template.** -/
theorem eq_of_toTemplate_eq {t' : StageType.{u} α n} (hS : t.toScheme = t'.toScheme)
    (hT : HEq t.toTemplate.rows t'.toTemplate.rows) : t = t' := by
  obtain ⟨S, p, _, _, _, _⟩ := t
  obtain ⟨S', p', _, _, _, _⟩ := t'
  obtain rfl : S = S' := hS
  obtain rfl : p = p' := coherentRows_injective (eq_of_heq hT)
  rfl

/-- The **stage type of a coherent row system**: a well-formed scheme with coded rows and a
coherent row system on its frame whose diagonal is lawful and occurs at stage `α`. -/
def ofCoherentRows (S : Scheme.{u} n) (hw : S.IsWellFormed) (hc : S.IsCoded)
    (r : RowSystem.{u} S.toCellScheme) (hlaw : S.rows.IsLawful r.diagonal)
    (hα : ∀ d, AtStage α (r.diagonal d)) : StageType.{u} α n where
  toScheme := S
  label := r.diagonal
  isWellFormed := hw
  isCoded := hc
  isLawful := hlaw
  atStage := hα

/-- **Round trip from coherent row systems**: the template of the stage type of a coherent row
system is the frame with that row system. -/
theorem toTemplate_ofCoherentRows (S : Scheme.{u} n) (hw : S.IsWellFormed) (hc : S.IsCoded)
    (r : RowSystem.{u} S.toCellScheme) (hr : r.IsCoherent) (hlaw : S.rows.IsLawful r.diagonal)
    (hα : ∀ d, AtStage α (r.diagonal d)) :
    (ofCoherentRows S hw hc r hlaw hα).toTemplate =
      ⟨S.card, S.toCellScheme, isFrame_of_isWellFormed hw.isWellFormed, r⟩ := by
  simp only [toTemplate, ofCoherentRows, hr.coherentRows_diagonal]

/-- **Round trip from stage types**: the stage type of the template of a stage type, on its
scheme, is the stage type. -/
theorem ofCoherentRows_toTemplate :
    ofCoherentRows t.toScheme t.isWellFormed t.isCoded (coherentRows t.toCellScheme t.label)
      (by rw [diagonal_coherentRows]; exact t.isLawful)
      (by rw [diagonal_coherentRows]; exact t.atStage) = t := by
  obtain ⟨S, p, _, _, _, _⟩ := t
  simp only [ofCoherentRows, diagonal_coherentRows]

/-- **Compatibility with projection**: the template of the stage reduction of a stage type is the
entrywise reduction of its template, the printed truncation [AFK26, Definition 4.10]. -/
theorem toTemplate_reduce (hβ : Order.IsSuccPrelimit β) :
    (t.reduce hβ).toTemplate = t.toTemplate.reduce β := by
  -- both templates have the frame of `t`; their rows, by the definitions of `toTemplate`,
  -- `StageType.reduce` and `Template.reduce`
  change (⟨t.card, t.toCellScheme, isFrame_of_isWellFormed t.isWellFormed.isWellFormed,
      coherentRows t.toCellScheme (Label.reduce β ∘ t.label)⟩ : Template.{u} n) =
    ⟨t.card, t.toCellScheme, isFrame_of_isWellFormed t.isWellFormed.isWellFormed,
      fun d e ↦ Label.reduce β (coherentRows t.toCellScheme t.label d e)⟩
  congr 1
  funext d e
  exact ((monotone_reduce β).map_min).symm

/-- **Compatibility with restriction**: the local rows of the restriction of a stage type to the
closed face spanned by `f` are the local rows of the corresponding cells. -/
theorem coherentRows_comap (f : Fin m ↪ Fin n) (hf : univ.map f ∈ t.toCellScheme.faces)
    (i : Fin (t.comap f hf).card)
    (e : (t.comap f hf).toCellScheme.below ((t.comap f hf).toCellScheme.gradedIndex i)) :
    (t.comap f hf).toTemplate.rows i e = t.toTemplate.rows (t.cellMap f i)
      ⟨t.cellMap f e.1,
        ((t.isLowerEmbedding_comap f).le_iff (e.1 : Fin (t.toScheme.comap f).card) i).mpr e.2⟩ :=
  rfl

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Realization.Model

/-!
# Prescribed rows at the cells of full scope

Roadmap, Layer 3, 3.4 (the receiving rows (R1)–(R4) and their finite hypotheses) and 3.1 (the
completion of the coatom amalgam, (R6)); semantic contract, items 3 and 5.

**The setting.**  Let `t'` be a stage type on `k` points and `d` a stage type on `n + 1` points
whose face along the first `n` points is the face `t` of `t'` along `h : Fin n ↪ Fin k`.  A
one-point extension `D` of `t'` *carries* `d` when its face along `extendByLast h` is `d`.  The
cells of `D` of graded index `(univ, g)` are its **cells of full scope**; the cells of `t'` and of
`d` are its **known cells** (`StageType.KnownCell`).  A **full-row prescription**
(`StageType.FullRowPrescription`) is, for every grade `g`, a condition `Φ g r w` on the readings
`r` of the known cells and the reading `w` of the cell itself by a cell of graded index
`(univ, g)`.  A scheme **extends `t'` and `d` with the rows prescribed by `Φ`**
(`StageType.ExtendsWithPrescribedRows`) when its faces are the schemes of `t'` and `d` and every
cell of full scope meets `Φ`; a **prescribed extension** (`StageType.IsPrescribedExtension`) is a
legal one-point extension of `t'` carrying `d` on such a scheme.  Since the condition concerns the
scheme, a model realizes over every occurrence of type `t'`, by generalized saturation, a coface
whose scheme meets `Φ` (`Realization.IsModel.realizesOver_extendsWithPrescribedRows`).  Prescribed
extensions of particular prescriptions imply the conditions of the receiving routes at the inputs
where those prescriptions are compatible with the faces
(`VaughtConjecture.Extension.PrescribedFullRowsRoutes`).

**Forcing** (`CellScheme.Rows.IsLawful.le_of_forall_row_le`).  If every cell of a graded index
`Y` reads `x` at least as `s`, where `s` has the grade of `Y` and `x` at most that grade, then every
lawful section `p` has `p s ≤ p x`: availability puts `s` below a cell of graded index `Y` labelled
at least `p s`, and locality there is monotone in the row value and antitone in the grade.  With
bountifulness at the cap `⊥`, every lawful labelling of a face of a legal stage type extends to it
(`StageType.exists_isLawful_extend_of_restrictFace`), so a reading prescribed at every cell of full
scope constrains **every** lawful labelling of `t'`, not only its labels.

**Admissibility and its necessity.**  An **admissible row** (`StageType.IsAdmissibleRow`) at the
grade `g` for a labelling `L` of the known cells, with a value `v`, is a pair `(r, w)` meeting
`Φ g`, coded, lawful below `(univ, g)` in the rows of `t'` and of `d`, and transforming (with
`w ↦ v`) to `L` capped at `v` on the known cells of grade at most `g`.  A prescription is
**compatible with the faces** (`StageType.IsFaceCompatible`) when at every lawful labelling `a` of
`t'` some lawful labelling `b` of `d`, agreeing with `a` on `t`, makes `Φ` admissible: at every
grade of a cell of full scope and every known cell of that grade, an admissible row with a value at
least its label (`StageType.IsAdmissibleAt`).  It is **compatible at the labels of `t'`**
(`StageType.IsFaceCompatibleAtLabels`) when this holds at the labels of `t'`, with some lawful
labelling of `d`.  Both are necessary for a prescribed extension
(`StageType.IsPrescribedExtension.isFaceCompatible`,
`StageType.IsPrescribedExtension.isFaceCompatibleAtLabels`): every lawful labelling of `t'`
extends to the prescribed extension, completeness and availability give a cell of full scope above
the known cell, and its row is admissible (`StageType.ExtendsWithPrescribedRows.isAdmissibleAt`).

**The common core.**  `StageType.HasPrescribedFullRows α` (a hypothesis on stage types introduced
here, not on models) asks a prescribed extension for every prescription compatible with the faces,
over every legal `t'` and legal `d`.  The form with compatibility at the labels of `t'`,
`StageType.HasPrescribedFullRowsAtLabels α`, implies it
(`StageType.HasPrescribedFullRowsAtLabels.hasPrescribedFullRows`, vacuous: its hypothesis is
refuted) and is false at every stage
(`PrescribedFullRowsCounterexample.not_hasPrescribedFullRowsAtLabels`, at `P α`): compatibility at
the labels of `t'` does not suffice, because the reading forces an order on every lawful labelling
of the face.  The uniform form is not tested by that input, since its compatibility premise fails
there (`PrescribedFullRowsCounterexample.not_isFaceCompatible`); it is neither proved nor refuted.
Compatibility is far from sufficient in general: it is asked per lawful labelling and per served
cell, while a prescribed extension has finitely many fixed rows serving every lawful labelling, rows
lawful on all of `D` (including the cells that are neither known cells nor the cell itself), and
legality of `D` at every graded face.

**The empty prescription** (`StageType.emptyPrescription`).  Its prescribed extensions over `ta`
carrying `tb` along the first points are the coatom extensions.  The coatom extension property
`StageType.HasCoatomExtensions α` makes the empty prescription compatible at every input
(`StageType.HasCoatomExtensions.hasCompatibleEmptyPrescription`); conversely `HasPrescribedFullRows`
and that compatibility give the coatom extension property
(`StageType.HasPrescribedFullRows.hasCoatomExtensions`).  So under `HasPrescribedFullRows` the
coatom extension property is equivalent to `StageType.HasCompatibleEmptyPrescription α`
(`StageType.HasPrescribedFullRows.hasCoatomExtensions_iff`), a statement about lawful labellings of
two faces alone, which is not proved here (it asks for coded readings of both faces with one
transformation witness).  Conversely the coatom extension property gives a prescribed extension of
the empty prescription at every input
(`StageType.HasCoatomExtensions.isPrescribedExtension_empty`).  So the empty prescription is the
case of the core that the completion addresses: any general proof of `HasPrescribedFullRows`
constructs, there, coatom extensions at every input where the empty prescription is compatible.
The coatom extension property follows from completions below the full grade of every coatom seed
(`StageType.HasCoatomExtensions.of_completionBelowFullGrade`), open at `m ≥ 3`; that construction
is the first clause of a general proof that the existing completion results do not close.

**What is not claimed.**  Nothing here proves or refutes (R1)–(R4) or the completion.  The
refutation concerns the form of the core compatible at the labels of `t'`.  That no clause of
`Realization.IsModel` prescribes the row of a cell of full scope is argued, not compiled.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

Lawful sections, locality and availability are [Kni26, Definition 2.5.4]; bountifulness is
[Kni26, Definition 2.5.14]; generalized saturation is [Kni26, Definition 3.2.1, clause 4(a)i]; the
coatom extension property is [Kni26, Corollary 4.3.22] without the apex.
-/

universe u v

namespace VaughtConjecture

open Finset Label

/-! ### Forcing by a reading at every cell of a graded index -/

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p : ι → Label.{u}}

/-- **A reading at every cell of a graded index forces an order of labels.**  Let `Y` be the
graded index of some cell, let `s` have grade `Y.2` and scope inside `Y.1`, and let `x` have scope
inside `Y.1` and grade at most that of `s`.  If every cell of graded index `Y` reads `x` at least as
it reads `s`, then every lawful section `p` has `p s ≤ p x`.  Availability puts `s` below a cell
`u` of graded index `Y` with `p s ≤ p u`, and locality at `u` is monotone in the row value and
antitone in the grade (`Label.TransformsTo.le_of_le`), so `p s = min (p s) (p u)` is at most
`min (p x) (p u)`. -/
theorem IsLawful.le_of_forall_row_le (hp : R.IsLawful p) {Y : Finset α × ℕ}
    (hY : ∃ u, D.gradedIndex u = Y) {s x : ι} (hsY : D.scope s ⊆ Y.1) (hgs : D.grade s = Y.2)
    (hxY : D.scope x ⊆ Y.1) (hgx : D.grade x ≤ D.grade s)
    (hread : ∀ u, D.gradedIndex u = Y → ∀ a b : D.below (D.gradedIndex u), a.1 = s → b.1 = x →
      R.row u a ≤ R.row u b) : p s ≤ p x := by
  obtain ⟨u₀, hu₀⟩ := hY
  have hsc : D.scope u₀ = Y.1 := congrArg Prod.fst hu₀
  have hgr : D.grade u₀ = Y.2 := congrArg Prod.snd hu₀
  obtain ⟨u, hu, hsu⟩ := hp.availability s u₀ (hsc ▸ hsY) (hgr ▸ hgs)
  have huY : D.gradedIndex u = Y := hu.trans hu₀
  have hs : s ∈ D.below (D.gradedIndex u) := by
    rw [huY]; exact (D.gradedIndex_le_iff).mpr ⟨hsY, hgs.le⟩
  have hx : x ∈ D.below (D.gradedIndex u) := by
    rw [huY]; exact (D.gradedIndex_le_iff).mpr ⟨hxY, hgx.trans hgs.le⟩
  have key := (hp.locality u).le_of_le (d := ⟨s, hs⟩) (d' := ⟨x, hx⟩)
    (hread u huY ⟨s, hs⟩ ⟨x, hx⟩ rfl rfl) hgx
  simp only [min_eq_left hsu] at key
  exact key.trans (min_le_left _ _)

end CellScheme.Rows

/-! ### Rows read at a cell, and the cells of a face -/

namespace Scheme

variable {n m k : ℕ} (S : Scheme.{u} n)

open Classical in
/-- The row of the cell `u` read at the cell `x`: its value there when `x` lies below the graded
index of `u`, and `⊥` otherwise. -/
noncomputable def rowAt (u x : Fin S.card) : Label.{u} :=
  if hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u) then S.rows.row u ⟨x, hx⟩
  else ⊥

variable {S}

/-- At a cell below `u`, `rowAt` is the row of `u`. -/
theorem rowAt_of_mem {u x : Fin S.card}
    (hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u)) :
    S.rowAt u x = S.rows.row u ⟨x, hx⟩ := by
  simp only [rowAt, hx, ↓reduceDIte]

/-- At a cell not below `u`, `rowAt` is `⊥`. -/
theorem rowAt_of_notMem {u x : Fin S.card}
    (hx : x ∉ S.toCellScheme.below (S.toCellScheme.gradedIndex u)) : S.rowAt u x = ⊥ := by
  simp only [rowAt, hx, ↓reduceDIte]

/-- A cell read by `u` at a value other than `⊥` lies below `u`. -/
theorem mem_below_of_rowAt_ne_bot {u x : Fin S.card} (h : S.rowAt u x ≠ ⊥) :
    x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u) := by
  by_contra hx
  exact h (rowAt_of_notMem hx)

/-- A coded scheme reads every cell below `ω ^ 2`. -/
theorem IsCoded.rowAt_lt (hS : S.IsCoded) (u x : Fin S.card) :
    S.rowAt u x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  by_cases hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u)
  · rw [rowAt_of_mem hx]; exact hS u _
  · rw [rowAt_of_notMem hx]; exact WithBot.bot_lt_coe _

/-- **The cells of the composite face**: the cell map along `f` of the cell map along `g` of the
restriction is the cell map along the composite, at equal positions. -/
theorem cellMap_cellMap (f : Fin m ↪ Fin n) (g : Fin k ↪ Fin m)
    {i : Fin ((S.comap f).comap g).card} {j : Fin (S.comap (g.trans f)).card} (h : (i : ℕ) = j) :
    S.cellMap f ((S.comap f).cellMap g i) = S.cellMap (g.trans f) j :=
  S.cellMap_eq_of_strictMono _ ((S.cellMap f).strictMono.comp ((S.comap f).cellMap g).strictMono)
    (S.mem_range_cellMap_comp_iff f g) h

/-- The cell maps along equal embeddings agree at equal positions. -/
theorem cellMap_congr {f f' : Fin m ↪ Fin n} (hf : f = f') {i : Fin (S.comap f).card}
    {j : Fin (S.comap f').card} (h : (i : ℕ) = j) : S.cellMap f i = S.cellMap f' j := by
  subst hf
  rw [Fin.ext h]

/-- The cell of `S` at position `i` of a face along `f` whose restriction is the scheme `T`. -/
noncomputable def faceCell (f : Fin m ↪ Fin n) {T : Scheme.{u} m} (he : S.comap f = T)
    (i : Fin T.card) : Fin S.card :=
  S.cellMap f (Fin.cast (congrArg Scheme.card he).symm i)

variable {f : Fin m ↪ Fin n} {T : Scheme.{u} m}

/-- The grade of a cell of a face is its grade in the face. -/
theorem grade_faceCell (he : S.comap f = T) (i : Fin T.card) :
    S.toCellScheme.grade (S.faceCell f he i) = T.toCellScheme.grade i := by
  subst he; rfl

/-- The scope of a cell of a face is the image of its scope in the face. -/
theorem scope_faceCell (he : S.comap f = T) (i : Fin T.card) :
    S.toCellScheme.scope (S.faceCell f he i) = (T.toCellScheme.scope i).map f := by
  subst he
  exact (S.map_comap_scope f i).symm

/-- The cells of a face are visible through it. -/
theorem faceCell_mem_visibleCells (he : S.comap f = T) (i : Fin T.card) :
    S.faceCell f he i ∈ S.visibleCells f :=
  S.cellMap_mem f _

/-- Every visible cell is a cell of the face. -/
theorem exists_faceCell_eq (he : S.comap f = T) {d : Fin S.card} (hd : d ∈ S.visibleCells f) :
    ∃ i, S.faceCell f he i = d := by
  subst he
  have : d ∈ Set.range (S.cellMap f) := by rw [range_cellMap]; exact hd
  obtain ⟨i, rfl⟩ := this
  exact ⟨i, rfl⟩

/-- The cell map of a face is injective. -/
theorem faceCell_injective (he : S.comap f = T) : Function.Injective (S.faceCell f he) := by
  subst he
  exact (S.cellMap f).injective

/-- **A row read through `rowAt` is lawful below the graded index of its cell**, for consistent
rows. -/
theorem isLawfulBelow_rowAt (hS : S.rows.IsConsistent) {u : Fin S.card}
    {X : Finset (Fin n) × ℕ} (hu : S.toCellScheme.gradedIndex u = X) :
    S.rows.IsLawfulBelow X fun e ↦ S.rowAt u e.1 := by
  subst hu
  have : (fun e : S.toCellScheme.below (S.toCellScheme.gradedIndex u) ↦ S.rowAt u e.1) =
      S.rows.row u := funext fun e ↦ rowAt_of_mem e.2
  rw [this]
  exact hS u

/-- **The row of a cell of graded index `(univ, g)`, read on a face, is lawful there**: with
consistent rows, the readings of the cells of the face along `f` by a cell of graded index
`(univ, g)` are lawful below `(univ, g)` in the rows of the face. -/
theorem isLawfulBelow_rowAt_faceCell (hS : S.rows.IsConsistent) {u : Fin S.card} {g : ℕ}
    (hu : S.toCellScheme.gradedIndex u = (univ, g)) (he : S.comap f = T) :
    T.rows.IsLawfulBelow ((univ : Finset (Fin m)), g) fun z ↦ S.rowAt u (S.faceCell f he z.1) := by
  subst he
  exact (S.isLawfulBelow_comap_cellMap_iff f (univ, g) (S.rowAt u)).mpr
    ((isLawfulBelow_rowAt hS hu).mono (X := Prod.map (Finset.map f) id ((univ : Finset (Fin m)), g))
      ⟨subset_univ _, le_rfl⟩)

end Scheme

/-! ### The cells of a face of a stage type -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ} {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
  {t : StageType.{u} α m}

/-- The scheme of a face is the restriction of the scheme. -/
theorem comap_toScheme_of_restrictFace (h : restrictFace f D = some t) :
    D.toScheme.comap f = t.toScheme := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  rfl

/-- The cell of `D` at a cell of its face `t` along `f`. -/
noncomputable def faceCell (h : restrictFace f D = some t) (i : Fin t.card) : Fin D.card :=
  D.toScheme.faceCell f (comap_toScheme_of_restrictFace h) i

/-- The label of a cell of a face is its label in the face. -/
@[simp] theorem label_faceCell (h : restrictFace f D = some t) (i : Fin t.card) :
    D.label (faceCell h i) = t.label i := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  rfl

/-- The grade of a cell of a face is its grade in the face. -/
@[simp] theorem grade_faceCell (h : restrictFace f D = some t) (i : Fin t.card) :
    D.toCellScheme.grade (faceCell h i) = t.toCellScheme.grade i :=
  D.toScheme.grade_faceCell _ i

/-- The scope of a cell of a face is the image of its scope in the face. -/
theorem scope_faceCell (h : restrictFace f D = some t) (i : Fin t.card) :
    D.toCellScheme.scope (faceCell h i) = (t.toCellScheme.scope i).map f :=
  D.toScheme.scope_faceCell _ i

/-- **Lawful sections restrict to a face.** -/
theorem isLawful_comp_faceCell (h : restrictFace f D = some t) {a : Fin D.card → Label.{u}}
    (ha : D.rows.IsLawful a) : t.rows.IsLawful fun i ↦ a (faceCell h i) := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  exact ha.comap (D.toScheme.isLowerEmbedding_comap f)

/-- **Lawful sections of a face extend**: every lawful section of the rows of a face of a legal
stage type extends to a lawful section of its rows (bountifulness at the cap `⊥`,
`Scheme.IsLegal.exists_isLawful_extend`).  It concerns all lawful sections of the face, not only
its labels. -/
theorem exists_isLawful_extend_of_restrictFace (hD : D.IsLegal) (h : restrictFace f D = some t)
    {a : Fin t.card → Label.{u}} (ha : t.rows.IsLawful a) :
    ∃ a' : Fin D.card → Label.{u}, D.rows.IsLawful a' ∧ ∀ i, a' (faceCell h i) = a i := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  obtain ⟨r, hr, -, hext⟩ := Scheme.IsLegal.exists_isLawful_extend hD hf (isSelfVisible_bot n)
    ha D.isLawful fun _ ↦ by simp
  exact ⟨r, hr, fun i ↦ hext i⟩

/-- **The root of a pinned extension**: in a one-point extension `D` of `t'` whose face along
`extendByLast h` is `d`, the cells of the common face `t` (the face of `t'` along `h` and of `d`
along the initial segment) are the same cells of `D`, reached through `t'` or through `d`. -/
theorem faceCell_faceCell {n' : ℕ} {D : StageType.{u} α (k + 1)} {t' : StageType.{u} α k}
    {h : Fin n' ↪ Fin k} {t : StageType.{u} α n'} {d : StageType.{u} α (n' + 1)}
    (h₁ : restrictFace Fin.castSuccEmb D = some t') (h₂ : restrictFace (extendByLast h) D = some d)
    (ht : restrictFace h t' = some t) (hd : restrictFace Fin.castSuccEmb d = some t)
    (i : Fin t.card) : faceCell h₁ (faceCell ht i) = faceCell h₂ (faceCell hd i) := by
  obtain ⟨hf₁, rfl⟩ := (restrictFace_eq_some_iff D _).mp h₁
  obtain ⟨hf₂, rfl⟩ := (restrictFace_eq_some_iff D _).mp h₂
  -- `faceCell` unfolds to the cell maps of the two composite faces
  change D.toScheme.cellMap _ ((D.toScheme.comap Fin.castSuccEmb).cellMap h _) =
    D.toScheme.cellMap _ ((D.toScheme.comap (extendByLast h)).cellMap Fin.castSuccEmb _)
  refine (Scheme.cellMap_cellMap _ _ (j := Fin.cast (congrArg Scheme.card
    (D.toScheme.comap_comap _ _)) _) rfl).trans ((Scheme.cellMap_congr
      (castSuccEmb_trans_extendByLast h).symm ?_).trans
    (Scheme.cellMap_cellMap _ _ (j := Fin.cast (congrArg Scheme.card
      (D.toScheme.comap_comap _ _)) _) rfl).symm)
  rfl

end StageType

/-! ### Prescriptions, prescribed extensions, and admissibility -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- The **known cells** of a one-point extension of `t'` carrying `d`: the cells of `t'` (on the
first points) and the cells of `d` (on a face through the new point). -/
abbrev KnownCell (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) : Type :=
  Fin t'.card ⊕ Fin d.card

/-- The grade of a known cell. -/
def knownGrade (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) :
    KnownCell t' d → ℕ :=
  Sum.elim (fun z ↦ t'.toCellScheme.grade z) fun j ↦ d.toCellScheme.grade j

/-- A **full-row prescription** for one-point extensions of `t'` carrying `d`: for every grade
`g`, a condition `Φ g r w` on the readings `r` of the known cells and the reading `w` of the cell
itself by a cell of graded index `(univ, g)`. -/
abbrev FullRowPrescription (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) :=
  ℕ → (KnownCell t' d → Label.{u}) → Label.{u} → Prop

/-- The readings of the known cells by the cell `u` of a scheme `S` on `k + 1` points whose face
along the first points is the scheme of `t'` and whose face along `extendByLast h` is the scheme
of `d`. -/
noncomputable def knownReading (t' : StageType.{u} α k) {h : Fin n ↪ Fin k}
    (d : StageType.{u} α (n + 1)) {S : Scheme.{u} (k + 1)}
    (he₁ : S.comap Fin.castSuccEmb = t'.toScheme) (he₂ : S.comap (extendByLast h) = d.toScheme)
    (u : Fin S.card) : KnownCell t' d → Label.{u} :=
  Sum.elim (fun z ↦ S.rowAt u (S.faceCell _ he₁ z)) fun j ↦ S.rowAt u (S.faceCell _ he₂ j)

/-- A scheme `S` on `k + 1` points **extends `t'` and `d` with the rows prescribed by `Φ`**: its
faces along the first points and along `extendByLast h` are the schemes of `t'` and `d`, and every
cell of graded index `(univ, g)` meets `Φ g` with its readings of the known cells and of itself.
The condition concerns the rows of `S` only, so it is a condition on schemes. -/
def ExtendsWithPrescribedRows (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (Φ : FullRowPrescription t' d) (S : Scheme.{u} (k + 1)) : Prop :=
  ∃ (he₁ : S.comap Fin.castSuccEmb = t'.toScheme) (he₂ : S.comap (extendByLast h) = d.toScheme),
    ∀ u g, S.toCellScheme.gradedIndex u = (univ, g) →
      Φ g (knownReading t' d he₁ he₂ u) (S.rowAt u u)

/-- A stage type `D` on `k + 1` points is a **prescribed extension** for `Φ` over `t'` carrying `d`
along `h`: a legal one-point extension of `t'` whose face along `extendByLast h` is `d`, on a scheme
that extends `t'` and `d` with the rows prescribed by `Φ`. -/
def IsPrescribedExtension (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (Φ : FullRowPrescription t' d) (D : StageType.{u} α (k + 1)) :
    Prop :=
  D.IsLegal ∧ restrictFace Fin.castSuccEmb D = some t' ∧ restrictFace (extendByLast h) D = some d ∧
    ExtendsWithPrescribedRows t' h d Φ D.toScheme

/-- An **admissible row** at the grade `g` for a labelling `L` of the known cells, with value `v`:
readings `r` of the known cells and `w` of the cell itself that meet `Φ g`, are coded, are lawful
below `(univ, g)` in the rows of `t'` and of `d`, and transform (with `w ↦ v`) to `L` capped at
`v` on the known cells of grade at most `g` (locality of a cell labelled `v`). -/
def IsAdmissibleRow (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1))
    (Φ : FullRowPrescription t' d) (L : KnownCell t' d → Label.{u}) (g : ℕ)
    (r : KnownCell t' d → Label.{u}) (w v : Label.{u}) : Prop :=
  Φ g r w ∧ (∀ T, r T < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) ∧
    w < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) ∧
    t'.rows.IsLawfulBelow ((univ : Finset (Fin k)), g) (fun z ↦ r (.inl z.1)) ∧
    d.rows.IsLawfulBelow ((univ : Finset (Fin (n + 1))), g) (fun j ↦ r (.inr j.1)) ∧
    ∃ (gs : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness gs σ ∧ v = min (σ w) (gs g) ∧
      ∀ T, knownGrade t' d T ≤ g → min (L T) v = min (σ (r T)) (gs (knownGrade t' d T))

/-- The admissibility of `Φ` at a labelling `a` of `t'` and a labelling `b` of `d` agreeing on
the common face: at every grade `g` of a cell of full scope, and for every known cell of grade
`g` (or none), an admissible row with a value at least the label of that cell. -/
def IsAdmissibleAt (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1))
    (Φ : FullRowPrescription t' d) (a : Fin t'.card → Label.{u}) (b : Fin d.card → Label.{u}) :
    Prop :=
  ∀ g, 0 < g → g ≤ k + 1 → ∀ T : Option (KnownCell t' d), (∀ T' ∈ T, knownGrade t' d T' = g) →
    ∃ r w v, (∀ T' ∈ T, Sum.elim a b T' ≤ v) ∧ IsAdmissibleRow t' d Φ (Sum.elim a b) g r w v

/-- A prescription is **compatible with the faces at the labels of `t'`**: admissible at the
labels of `t'` and some lawful labelling of `d` (not necessarily its labels) agreeing with them on
the common face `t`. -/
def IsFaceCompatibleAtLabels (t' : StageType.{u} α k) {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (Φ : FullRowPrescription t' d) : Prop :=
  ∃ b : Fin d.card → Label.{u}, d.rows.IsLawful b ∧
    (∀ i, t'.label (faceCell ht i) = b (faceCell hd i)) ∧ IsAdmissibleAt t' d Φ t'.label b

/-- A prescription is **compatible with the faces** (uniformly): admissible at every lawful
labelling `a` of the rows of `t'`, with some lawful labelling of `d` agreeing with `a` on the
common face. -/
def IsFaceCompatible (t' : StageType.{u} α k) {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (Φ : FullRowPrescription t' d) : Prop :=
  ∀ a : Fin t'.card → Label.{u}, t'.rows.IsLawful a → ∃ b : Fin d.card → Label.{u},
    d.rows.IsLawful b ∧ (∀ i, a (faceCell ht i) = b (faceCell hd i)) ∧ IsAdmissibleAt t' d Φ a b

/-- Uniform compatibility gives compatibility at the labels of `t'`. -/
theorem IsFaceCompatible.isFaceCompatibleAtLabels {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} {ht : restrictFace h t' = some t}
    {d : StageType.{u} α (n + 1)} {hd : restrictFace Fin.castSuccEmb d = some t}
    {Φ : FullRowPrescription t' d} (hΦ : IsFaceCompatible t' ht d hd Φ) :
    IsFaceCompatibleAtLabels t' ht d hd Φ :=
  hΦ t'.label t'.isLawful

variable (α) in
/-- **Prescribed rows at the cells of full scope** (a named hypothesis on stage types, not on
models): over every legal `t'` on `k` points, every legal `d` on `n + 1` points whose face along
the first points is the face `t` of `t'` along `h`, and every prescription `Φ` compatible with
the faces (`IsFaceCompatible`), some legal one-point extension of `t'` carrying `d` along `h` is a
prescribed extension for `Φ`. -/
def HasPrescribedFullRows : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t), t'.IsLegal → d.IsLegal →
    ∀ Φ : FullRowPrescription t' d, IsFaceCompatible t' ht d hd Φ →
      ∃ D, IsPrescribedExtension t' h d Φ D

variable (α) in
/-- **Prescribed rows at the cells of full scope, compatible at the labels**: the form of
`HasPrescribedFullRows` whose admissibility asks compatibility with the faces only at the labels of
`t'` (`IsFaceCompatibleAtLabels`).  It is false at every stage
(`PrescribedFullRowsCounterexample.not_hasPrescribedFullRowsAtLabels`). -/
def HasPrescribedFullRowsAtLabels : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t), t'.IsLegal → d.IsLegal →
    ∀ Φ : FullRowPrescription t' d, IsFaceCompatibleAtLabels t' ht d hd Φ →
      ∃ D, IsPrescribedExtension t' h d Φ D

/-- The form compatible at the labels implies the uniform form (it asks less of a
prescription).  The implication is vacuous: its hypothesis is false at every stage
(`PrescribedFullRowsCounterexample.not_hasPrescribedFullRowsAtLabels`). -/
theorem HasPrescribedFullRowsAtLabels.hasPrescribedFullRows
    (hc : HasPrescribedFullRowsAtLabels.{u} α) : HasPrescribedFullRows.{u} α :=
  fun _ _ t' h t ht d hd ht' hd' Φ hΦ ↦ hc t' h t ht d hd ht' hd' Φ hΦ.isFaceCompatibleAtLabels

end StageType

/-! ### Necessity: prescribed extensions are compatible with the faces -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- **The rows of a prescribed extension are admissible at every lawful labelling**: if `D` is a
legal one-point extension of `t'` carrying `d` along `h` on a scheme meeting `Φ`, then `Φ` is
admissible at the restrictions to `t'` and to `d` of every lawful labelling `a'` of `D`.  At a
grade `g` and a known cell of grade `g`, completeness and availability give a cell `u` of graded
index `(univ, g)` labelled at least as that cell; its readings meet `Φ g` (the scheme), are
coded, are lawful below `(univ, g)` in the faces (consistency of `D`), and locality at `u` is the
transformation. -/
theorem ExtendsWithPrescribedRows.isAdmissibleAt {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} {Φ : FullRowPrescription t' d} {D : StageType.{u} α (k + 1)}
    (hD : D.IsLegal) (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (h₂ : restrictFace (extendByLast h) D = some d)
    (hS : ExtendsWithPrescribedRows t' h d Φ D.toScheme)
    {a' : Fin D.card → Label.{u}} (ha' : D.rows.IsLawful a') :
    IsAdmissibleAt t' d Φ (fun z ↦ a' (faceCell h₁ z)) (fun j ↦ a' (faceCell h₂ j)) := by
  intro g hg0 hgk T hT
  obtain ⟨he₁, he₂, hreal⟩ := hS
  -- the cells of `D` at the known cells
  set κ : KnownCell t' d → Fin D.card :=
    Sum.elim (fun z ↦ D.toScheme.faceCell _ he₁ z) fun j ↦ D.toScheme.faceCell _ he₂ j with hκ
  have hgrade (T' : KnownCell t' d) : D.toCellScheme.grade (κ T') = knownGrade t' d T' := by
    cases T' with
    | inl z => exact D.toScheme.grade_faceCell he₁ z
    | inr j => exact D.toScheme.grade_faceCell he₂ j
  have hL (T' : KnownCell t' d) : Sum.elim (fun z ↦ a' (faceCell h₁ z))
      (fun j ↦ a' (faceCell h₂ j)) T' = a' (κ T') := by
    cases T' <;> rfl
  have hr (u : Fin D.card) (T' : KnownCell t' d) :
      knownReading t' d he₁ he₂ u T' = D.rowAt u (κ T') := by
    cases T' <;> rfl
  -- a cell of graded index `(univ, g)` above the given known cell
  obtain ⟨u₀, hu₀⟩ := hD.isComplete ((univ : Finset (Fin (k + 1))), g)
    ⟨D.univ_mem_faces, hg0, by simpa using hgk⟩
  obtain ⟨u, hu, hTu⟩ : ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), g) ∧
      ∀ T' ∈ T, a' (κ T') ≤ a' u := by
    cases T with
    | none => exact ⟨u₀, hu₀, by simp⟩
    | some T' =>
      have hs₀ : D.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
      have hg₀ : D.toCellScheme.grade u₀ = g := congrArg Prod.snd hu₀
      obtain ⟨u, hu, hle⟩ := ha'.availability (κ T') u₀ (hs₀ ▸ subset_univ _)
        ((hgrade T').trans ((hT T' rfl).trans hg₀.symm))
      exact ⟨u, hu.trans hu₀, by simpa using hle⟩
  have hgu : D.toCellScheme.grade u = g := congrArg Prod.snd hu
  have hmem (T' : KnownCell t' d) (hT' : knownGrade t' d T' ≤ g) :
      κ T' ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [hu]
    exact (D.toCellScheme.gradedIndex_le_iff).mpr ⟨subset_univ _, (hgrade T').trans_le hT'⟩
  obtain ⟨gs, σ, hw, heq⟩ := ha'.locality u
  refine ⟨knownReading t' d he₁ he₂ u, D.rowAt u u, a' u, fun T' hT' ↦ (hL T').trans_le
    (hTu T' hT'), hreal u g hu, fun T' ↦ (hr u T').symm ▸ D.isCoded.rowAt_lt u _,
    D.isCoded.rowAt_lt u u, D.toScheme.isLawfulBelow_rowAt_faceCell hD.isConsistent hu he₁,
    D.toScheme.isLawfulBelow_rowAt_faceCell hD.isConsistent hu he₂, gs, σ, hw, ?_, ?_⟩
  · have := heq ⟨u, D.toCellScheme.mem_below_gradedIndex u⟩
    simp only [min_self] at this
    rw [Scheme.rowAt_of_mem (D.toCellScheme.mem_below_gradedIndex u), ← hgu]
    exact this
  · intro T' hT'
    have := heq ⟨κ T', hmem T' hT'⟩
    simp only at this
    rw [hL, hr, Scheme.rowAt_of_mem (hmem T' hT'), ← hgrade]
    exact this

/-- **Necessity of uniform compatibility**: a prescription with a prescribed extension is
compatible with the faces (`IsFaceCompatible`).  Every lawful labelling of `t'` extends to a lawful
labelling of the prescribed extension (bountifulness at the cap `⊥`), whose restriction to `d`
agrees with it on the common face; the rows of the prescribed extension are admissible there
(`StageType.ExtendsWithPrescribedRows.isAdmissibleAt`). -/
theorem IsPrescribedExtension.isFaceCompatible {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {Φ : FullRowPrescription t' d}
    {D : StageType.{u} α (k + 1)} (hD : IsPrescribedExtension t' h d Φ D) :
    IsFaceCompatible t' ht d hd Φ := by
  obtain ⟨hDl, h₁, h₂, hS⟩ := hD
  intro a ha
  obtain ⟨a', ha', hext⟩ := exists_isLawful_extend_of_restrictFace hDl h₁ ha
  refine ⟨fun j ↦ a' (faceCell h₂ j), isLawful_comp_faceCell h₂ ha', fun i ↦ ?_, ?_⟩
  · rw [← hext, faceCell_faceCell h₁ h₂ ht hd]
  · have := hS.isAdmissibleAt hDl h₁ h₂ ha'
    simp only [hext] at this
    exact this

/-- **Necessity of compatibility at the labels**: a prescription with a prescribed extension is
compatible with the faces at the labels of `t'`; the labels of the prescribed extension restrict
to those of `t'` and `d`. -/
theorem IsPrescribedExtension.isFaceCompatibleAtLabels {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} (ht : restrictFace h t' = some t)
    {d : StageType.{u} α (n + 1)} (hd : restrictFace Fin.castSuccEmb d = some t)
    {Φ : FullRowPrescription t' d} {D : StageType.{u} α (k + 1)}
    (hD : IsPrescribedExtension t' h d Φ D) : IsFaceCompatibleAtLabels t' ht d hd Φ :=
  (hD.isFaceCompatible ht hd).isFaceCompatibleAtLabels

end StageType

/-! ### The empty prescription: the coatom extension property -/

namespace StageType

variable {α : Ordinal.{u}}

/-- The **empty prescription**: no condition on the rows. -/
def emptyPrescription {k n : ℕ} (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) :
    FullRowPrescription t' d :=
  fun _ _ _ ↦ True

variable (α) in
/-- The **empty prescription is compatible** at every input of the coatom extension property:
two legal stage types on `m + 1` points with a common face along the first points. -/
def HasCompatibleEmptyPrescription : Prop :=
  ∀ (m : ℕ) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
    (hpa : restrictFace Fin.castSuccEmb ta = some p)
    (hpb : restrictFace Fin.castSuccEmb tb = some p), ta.IsLegal → tb.IsLegal →
    IsFaceCompatible ta hpa tb hpb (emptyPrescription ta tb)

/-- **The coatom extension property makes the empty prescription compatible**: a coatom
extension is a prescribed extension for the empty prescription, and prescribed extensions are
compatible with the faces
(`StageType.IsPrescribedExtension.isFaceCompatible`). -/
theorem HasCoatomExtensions.hasCompatibleEmptyPrescription (hext : HasCoatomExtensions.{u} α) :
    HasCompatibleEmptyPrescription.{u} α := by
  intro m ta tb p hpa hpb hta htb
  obtain ⟨t, ht, hta', htb'⟩ := hext m ta tb p hta htb hpa hpb
  exact IsPrescribedExtension.isFaceCompatible (D := t) hpa hpb
    ⟨ht, hta', htb', comap_toScheme_of_restrictFace hta', comap_toScheme_of_restrictFace htb',
      fun _ _ _ ↦ trivial⟩

/-- **A coatom extension is a prescribed extension for the empty prescription**: under the coatom
extension property, every legal `ta` and `tb` with a common face along the first points have a
prescribed extension for the empty prescription over `ta` carrying `tb`. -/
theorem HasCoatomExtensions.isPrescribedExtension_empty (hext : HasCoatomExtensions.{u} α)
    {m : ℕ} {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m} (hta : ta.IsLegal)
    (htb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
    (hpb : restrictFace Fin.castSuccEmb tb = some p) :
    ∃ D, IsPrescribedExtension ta Fin.castSuccEmb tb (emptyPrescription ta tb) D := by
  obtain ⟨t, ht, hta', htb'⟩ := hext m ta tb p hta htb hpa hpb
  exact ⟨t, ht, hta', htb', comap_toScheme_of_restrictFace hta',
    comap_toScheme_of_restrictFace htb', fun _ _ _ ↦ trivial⟩

/-- **Prescribed rows give the coatom extension property where the empty prescription is
compatible**: the coatom extension of `ta` and `tb` over `p` is a prescribed extension for the
empty prescription over `ta` carrying `tb` along the first points. -/
theorem HasPrescribedFullRows.hasCoatomExtensions (hpr : HasPrescribedFullRows.{u} α)
    (hc : HasCompatibleEmptyPrescription.{u} α) : HasCoatomExtensions.{u} α := by
  intro m ta tb p hta htb hpa hpb
  obtain ⟨D, hD, hDa, hDb, -⟩ := hpr ta Fin.castSuccEmb p hpa tb hpb hta htb _
    (hc m ta tb p hpa hpb hta htb)
  exact ⟨D, hD, hDa, hDb⟩

/-- **Under prescribed rows, the coatom extension property is the compatibility of the empty
prescription**, a statement about lawful labellings of the two faces alone. -/
theorem HasPrescribedFullRows.hasCoatomExtensions_iff (hpr : HasPrescribedFullRows.{u} α) :
    HasCoatomExtensions.{u} α ↔ HasCompatibleEmptyPrescription.{u} α :=
  ⟨HasCoatomExtensions.hasCompatibleEmptyPrescription, hpr.hasCoatomExtensions⟩

end StageType

/-! ### Prescribed extensions are reached by generalized saturation -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Generalized saturation reaches a prescribed extension**: at a stage that is zero or a limit,
if a prescribed extension for `Φ` over the type of an occurrence `x` carries `d`, a model realizes
over `x` a coface of its type whose scheme meets `Φ`.  Meeting `Φ` is a condition on the scheme
(`StageType.ExtendsWithPrescribedRows`), and the saturation clause prescribes the scheme. -/
theorem IsModel.realizesOver_extendsWithPrescribedRows (hR : R.IsModel)
    (hα : Order.IsSuccPrelimit α)
    (x : R.Occurrence) {n : ℕ} {h : Fin n ↪ Fin x.arity} {d : StageType.{u} α (n + 1)}
    {Φ : StageType.FullRowPrescription x.type d} {D : StageType.{u} α (x.arity + 1)}
    (hD : StageType.IsPrescribedExtension x.type h d Φ D) :
    R.RealizesOver x.tuple
      (x.type.cofaces ∩ {q | StageType.ExtendsWithPrescribedRows x.type h d Φ q.toScheme}) := by
  obtain ⟨hDl, h₁, -, hS⟩ := hD
  refine (hR.saturation_of_isLegal hα x hDl
    ((StageType.restrictFace_eq_some_iff D _).mp h₁).1
    (StageType.comap_toScheme_of_restrictFace h₁)).mono fun q ⟨hq, hqS⟩ ↦ ⟨hq, ?_⟩
  rw [StageType.mem_saturationFamily] at hqS
  -- the saturation family is stated through `q.toScheme`; unfold membership to its condition
  change StageType.ExtendsWithPrescribedRows x.type h d Φ q.toScheme
  rw [hqS]
  exact hS

end Realization

end VaughtConjecture

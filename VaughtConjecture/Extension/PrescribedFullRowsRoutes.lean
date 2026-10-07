/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.PrescribedFullRows

/-!
# Prescribed rows and the reading conditions of the receiving routes

Roadmap, Layer 3, 3.4 (the finite hypotheses of the receiving rows (R1)–(R4)) and Layer 4, output 3
(stable recovery through a reading cell); semantic contract, items 5 and 8.

The open finite hypotheses of the receiving routes ask for objects whose cells of full scope read
prescribed cells in a prescribed way: (R2) and (R3) for a legal one-point extension of a context
(a reading coface), (R1) and (R4) for a scheme (`IsBlockTight` asks for a scheme on which every
coface of the context reads in its own block; a cap-reading scheme carries a coface of the stage
reduction `T⁺↓β`).  This file states, in full, the reading conditions of three routes, writes each
as a full-row prescription (`VaughtConjecture.Extension.PrescribedFullRows`), and proves that a
prescribed extension for the prescription gives the condition (for (R4), the part of it concerning
the scheme); so `StageType.HasPrescribedFullRows α` implies each condition at every input where its
prescription is compatible with the faces.  Compatibility with the faces is a hypothesis of each
implication, and it is necessary for a prescribed extension
(`StageType.IsPrescribedExtension.isFaceCompatible`); where it fails the implication says nothing.

* **Reading the new tops at least as a private top** ((R2), (R3); `IsReadingContext`,
  `ReadsAtLeast`).  A choice of private tops (`IsTopChoice`) gives the reading prescription
  (`readingPrescription`); a prescribed extension for it is a reading coface
  (`IsPrescribedExtension.isReadingContext`), and under prescribed rows a compatible reading
  prescription gives a reading context (`StageType.HasPrescribedFullRows.isReadingContext`).
  Conversely a reading context determines a choice whose reading prescription is compatible
  (`IsReadingContext.exists_isFaceCompatible`), so under prescribed rows, at a legal input, a
  reading context is equivalent to a choice of private tops with a compatible reading
  prescription.  Unconditionally, a reading context forces, at every lawful labelling `a` of the
  context, a lawful labelling of the donor agreeing with `a` on the common face under which every
  new top is at least `a` at some private top of at least its grade
  (`IsReadingContext.forall_exists_le`): the passage from a graded context with a top to a reading
  context needs that at every lawful labelling, not only at the labels; that passage is open and
  not derived from `StageType.HasPrescribedFullRows`.
* **Reading the labels of one block in the own block** ((R1), the per-block design;
  `ReadsInOwnBlock`, `IsBlockTight`, `HasBlockTightSaturations`).  The block prescription
  (`blockPrescription`) reads the cells of the context in the block of the reading of the cell
  itself; a prescribed extension for it is block-tight (`IsPrescribedExtension.isBlockTight`),
  with the cells of the context as the cells read.  Under prescribed rows, compatibility of every
  block prescription over the empty face with the one-point donor gives block-tight saturations
  (`StageType.HasPrescribedFullRows.hasBlockTightSaturations`), but that hypothesis is not met
  where it matters.  The block prescription is not compatible with the faces wherever `p` has a
  lawful labelling that is `⊥` at a cell `z` of the block, not self-visible at the grade `N`, and
  not `⊥` at a cell of grade `N` (`not_isFaceCompatible_block`): the row serving that cell would
  read `z` in the block of its own reading; the transformation sends the reading of `z` to `⊥`,
  hence, commuting with the visibility replacement, the reading of the cell itself, so the row's
  value is `⊥`.  At the refuting context of the per-block route, the private type
  `CoupledGatedExtensionCounterexample.P α` (in a module not on this base), these hypotheses hold
  at every stage `α > 1`: that module proves it legal, its cell `z₁` is
  labelled `1` and not self-visible at the grade `2`, and it has the lawful labelling
  `⊥, ⊥, ⊥, ω + 1, ω + 2`.  So there the hypothesis of
  `StageType.HasPrescribedFullRows.hasBlockTightSaturations` fails (argued from those compiled
  pieces; the joining lemma is to be compiled once that module is on this base), and the (R1)
  implication is **not a reduction** of block-tight saturations to the common core
  `StageType.HasPrescribedFullRows`.  The cause is the
  domain of the prescription: it names only known cells, while block-tightness accepts any cell
  with the label, new cells included.  The per-input implication
  `IsPrescribedExtension.isBlockTight` stands, and nothing here refutes block-tight saturations,
  (R1) or `StageType.HasPrescribedFullRows`.
* **Reading the new cells through the cap** ((R4); `ReadsThroughCap`, `IsCapReadingScheme`).  The
  cap prescription (`capPrescription`) reads every new cell of the donor as `⊥`, as the cap, or in
  the block of a reference cell; a prescribed extension for it is a cap-reading scheme when the
  cap's grade exceeds `k` (`IsPrescribedExtension.isCapReadingScheme`,
  `StageType.HasPrescribedFullRows.exists_isCapReadingScheme`).  A cap-reading scheme is the part
  concerning the scheme of the sufficient condition for a stable recovery scheme through a reading
  cell; the remaining hypotheses there concern the label of the cap and the calibration, and the
  composition giving a stable recovery scheme is not compiled here.  The prescribed extension fixes
  the labels of the donor, more than a cap-reading scheme asks.

The completion route is the empty prescription (`StageType.emptyPrescription`,
`StageType.HasPrescribedFullRows.hasCoatomExtensions_iff`).  A step of the canonical multi-layer
scheme of a seed (`Seed.HasCanonicalMultiStep`, not on this base) is not an instance (argued, not
compiled): it asks for a completion of one shape (two copies at each graded index of full scope
reading through their originals), while a prescribed extension for the empty prescription is a
coatom extension of any shape.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

The private context is that of [Kni26, Lemma 8.1.1]; generalized saturation is [Kni26,
Definition 3.2.1, clause 4(a)i].
-/

universe u

namespace VaughtConjecture.PrescribedFullRows

open Finset Label StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-! ### Reading the new tops at least as a private top -/

/-- `D` **reads the cell `x` at least as the cell `s`**: `x` has grade at most that of `s`, and
every cell of graded index `(univ, g)`, for `g` the grade of `s`, reads `x` in its row at least as
it reads `s`. -/
def ReadsAtLeast {m : ℕ} (D : StageType.{u} α m) (s x : Fin D.card) : Prop :=
  D.toCellScheme.grade x ≤ D.toCellScheme.grade s ∧
    ∀ u, D.toCellScheme.gradedIndex u = (univ, D.toCellScheme.grade s) →
      ∀ a b : D.toCellScheme.below (D.toCellScheme.gradedIndex u), a.1 = s → b.1 = x →
        D.rows.row u a ≤ D.rows.row u b

/-- `t'` is a **reading context** for `d` along `h`: some legal one-point coface of `t'` has face
`d` along `extendByLast h` and reads each of its new cells visible in that face and labelled `⊤` at
least as some private cell labelled `⊤`. -/
def IsReadingContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) :
    Prop :=
  ∃ D' ∈ t'.cofaces, restrictFace (extendByLast h) D' = some d ∧
    ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
      D'.label x = ⊤ → ∃ s, Fin.last k ∉ D'.toCellScheme.scope s ∧ D'.label s = ⊤ ∧
        ReadsAtLeast D' s x

/-- The type of a **choice of private tops**: a cell of `t'` for every new cell of `d` labelled
`⊤`. -/
abbrev TopChoice (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) : Type :=
  ∀ j : Fin d.card, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → Fin t'.card

/-- A **choice of private tops** for the new tops of `d`: for every new cell of `d` labelled `⊤`,
a cell of `t'` labelled `⊤` of at least its grade. -/
def IsTopChoice (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1))
    (σ : TopChoice t' d) : Prop :=
  ∀ j hj ht, t'.label (σ j hj ht) = ⊤ ∧ d.toCellScheme.grade j ≤ t'.toCellScheme.grade (σ j hj ht)

/-- The **reading prescription** of a choice of private tops: at the grade of the private top
chosen for a new top, the new top is read at least as the private top. -/
def readingPrescription (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1))
    (σ : TopChoice t' d) : FullRowPrescription t' d :=
  fun g r _ ↦ ∀ j hj ht, t'.toCellScheme.grade (σ j hj ht) = g → r (.inl (σ j hj ht)) ≤ r (.inr j)

/-- The last point lies in the scope of a cell of the face along `extendByLast h` exactly when the
last point lies in its scope in the face. -/
theorem last_mem_scope_faceCell_iff {D : StageType.{u} α (k + 1)} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (h₂ : restrictFace (extendByLast h) D = some d)
    (j : Fin d.card) :
    Fin.last k ∈ D.toCellScheme.scope (faceCell h₂ j) ↔ Fin.last n ∈ d.toCellScheme.scope j := by
  rw [scope_faceCell, mem_map, ← extendByLast_last h]
  exact ⟨fun ⟨y, hy, hye⟩ ↦ (extendByLast h).injective hye ▸ hy, fun hy ↦ ⟨_, hy, rfl⟩⟩

/-- A cell of the face along the first points avoids the last point. -/
theorem last_notMem_scope_faceCell {D : StageType.{u} α (k + 1)} {t' : StageType.{u} α k}
    (h₁ : restrictFace Fin.castSuccEmb D = some t') (z : Fin t'.card) :
    Fin.last k ∉ D.toCellScheme.scope (faceCell h₁ z) := by
  rw [scope_faceCell, mem_map]
  rintro ⟨y, -, hy⟩
  exact (Fin.castSucc_lt_last y).ne hy

/-- A cell avoiding the last point is a cell of the face along the first points. -/
theorem exists_faceCell_eq_of_last_notMem {D : StageType.{u} α (k + 1)} {t' : StageType.{u} α k}
    (h₁ : restrictFace Fin.castSuccEmb D = some t') {s : Fin D.card}
    (hs : Fin.last k ∉ D.toCellScheme.scope s) : ∃ z, faceCell h₁ z = s :=
  D.toScheme.exists_faceCell_eq _ (Scheme.mem_visibleCells.mpr fun _ hx ↦
    Fin.exists_castSucc_eq.mpr fun hxl ↦ hs (hxl ▸ hx))

/-- **A prescribed extension for the reading prescription is a reading coface**: the legal one-point
extension of `t'` carrying `d` reads every new top at least as its chosen private top. -/
theorem IsPrescribedExtension.isReadingContext {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} {σ : TopChoice t' d} (hσ : IsTopChoice t' d σ)
    {D : StageType.{u} α (k + 1)}
    (hD : IsPrescribedExtension t' h d (readingPrescription t' d σ) D) :
    IsReadingContext t' h d := by
  obtain ⟨hDl, h₁, h₂, he₁, he₂, hreal⟩ := hD
  refine ⟨D, ⟨hDl, h₁⟩, h₂, fun x hx hxl hxt ↦ ?_⟩
  obtain ⟨j, hj⟩ := D.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace h₂) hx
  replace hj : faceCell h₂ j = x := hj
  subst hj
  have hjl := (last_mem_scope_faceCell_iff h₂ j).mp hxl
  rw [label_faceCell] at hxt
  obtain ⟨hst, hgr⟩ := hσ j hjl hxt
  refine ⟨faceCell h₁ (σ j hjl hxt), last_notMem_scope_faceCell h₁ _, by rw [label_faceCell, hst],
    by rwa [grade_faceCell, grade_faceCell], fun u hu a b ha hb ↦ ?_⟩
  have := hreal u _ (hu.trans (by rw [grade_faceCell])) j hjl hxt rfl
  -- unfold `knownReading` at the two known cells
  change D.rowAt u (faceCell h₁ (σ j hjl hxt)) ≤ D.rowAt u (faceCell h₂ j) at this
  rw [← ha, ← hb, Scheme.rowAt_of_mem a.2, Scheme.rowAt_of_mem b.2] at this
  exact this

/-- **Prescribed rows give reading contexts where the reading prescription is compatible**: under
`StageType.HasPrescribedFullRows α`, over a legal `t'` and a legal `d` with the common face `t`,
a choice of private tops whose reading prescription is compatible with the faces gives a reading
context. -/
theorem _root_.VaughtConjecture.StageType.HasPrescribedFullRows.isReadingContext
    (hpr : HasPrescribedFullRows.{u} α) {t' : StageType.{u} α k} (ht' : t'.IsLegal)
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} (ht : restrictFace h t' = some t)
    {d : StageType.{u} α (n + 1)} (hd' : d.IsLegal) (hd : restrictFace Fin.castSuccEmb d = some t)
    {σ : TopChoice t' d} (hσ : IsTopChoice t' d σ)
    (hc : IsFaceCompatible t' ht d hd (readingPrescription t' d σ)) : IsReadingContext t' h d :=
  let ⟨_, hD⟩ := hpr t' h t ht d hd ht' hd' _ hc
  IsPrescribedExtension.isReadingContext hσ hD

/-- **Reading contexts make a reading prescription compatible**: a reading coface determines a
choice of private tops (each new top's private top is a cell of `t'`), is a prescribed extension
for its reading prescription, and so that prescription is compatible with the faces
(`StageType.IsPrescribedExtension.isFaceCompatible`).  Under prescribed rows, at a legal input, a
reading context is therefore equivalent to a choice of private tops with a compatible reading
prescription. -/
theorem IsReadingContext.exists_isFaceCompatible {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) (hR : IsReadingContext t' h d) :
    ∃ σ, IsTopChoice t' d σ ∧ IsFaceCompatible t' ht d hd (readingPrescription t' d σ) := by
  classical
  obtain ⟨D, ⟨hDl, h₁⟩, h₂, hread⟩ := hR
  -- the private top read below each new top
  have hx (j : Fin d.card) (hj : Fin.last n ∈ d.toCellScheme.scope j) (ht : d.label j = ⊤) :
      ∃ z : Fin t'.card, t'.label z = ⊤ ∧ ReadsAtLeast D (faceCell h₁ z) (faceCell h₂ j) := by
    obtain ⟨s, hsl, hst, hs⟩ := hread (faceCell h₂ j)
      (D.toScheme.faceCell_mem_visibleCells _ j) ((last_mem_scope_faceCell_iff h₂ j).mpr hj)
      (by rw [label_faceCell]; exact ht)
    obtain ⟨z, rfl⟩ := exists_faceCell_eq_of_last_notMem h₁ hsl
    exact ⟨z, by rw [← label_faceCell h₁]; exact hst, hs⟩
  refine ⟨fun j hj ht ↦ (hx j hj ht).choose, fun j hj ht ↦ ⟨(hx j hj ht).choose_spec.1, ?_⟩,
    IsPrescribedExtension.isFaceCompatible ht hd (D := D) ⟨hDl, h₁, h₂,
      comap_toScheme_of_restrictFace h₁, comap_toScheme_of_restrictFace h₂, ?_⟩⟩
  · have := (hx j hj ht).choose_spec.2.1
    rwa [grade_faceCell, grade_faceCell] at this
  · intro u g hu j hj ht hg
    have hr := (hx j hj ht).choose_spec.2
    have hu' : D.toCellScheme.gradedIndex u =
        (univ, D.toCellScheme.grade (faceCell h₁ (hx j hj ht).choose)) := by
      rw [hu, grade_faceCell, hg]
    have hmem (y : Fin D.card) (hy : D.toCellScheme.grade y ≤ g) :
        y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
      rw [hu]; exact ⟨subset_univ _, hy⟩
    have hsm := hmem (faceCell h₁ (hx j hj ht).choose) (by rw [grade_faceCell, hg])
    have hxm := hmem (faceCell h₂ j) (by
      rw [grade_faceCell, ← hg]; have := hr.1; rwa [grade_faceCell, grade_faceCell] at this)
    have := hr.2 u hu' ⟨_, hsm⟩ ⟨_, hxm⟩ rfl rfl
    -- unfold `knownReading` at the two known cells
    change D.rowAt u (faceCell h₁ (hx j hj ht).choose) ≤ D.rowAt u (faceCell h₂ j)
    rw [Scheme.rowAt_of_mem hsm, Scheme.rowAt_of_mem hxm]
    exact this

/-- **What a reading context forces** (by `CellScheme.Rows.IsLawful.le_of_forall_row_le`): if `t'`
is a reading context for `d`, then every lawful labelling `a` of the rows of `t'` has a lawful
labelling `b` of the rows of `d`, agreeing with `a` on the common face, under which every new top
of `d` is at least `a` at some private top of `t'` of at least its grade.  Every lawful labelling
of `t'` extends to the reading coface (bountifulness at the cap `⊥`), and there the reading at every
cell of the graded index of the private top forces the order. -/
theorem IsReadingContext.forall_exists_le {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) (hR : IsReadingContext t' h d)
    {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a) :
    ∃ b : Fin d.card → Label.{u}, d.rows.IsLawful b ∧
      (∀ i, a (faceCell ht i) = b (faceCell hd i)) ∧
      ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ →
        ∃ z, t'.label z = ⊤ ∧ d.toCellScheme.grade j ≤ t'.toCellScheme.grade z ∧ a z ≤ b j := by
  obtain ⟨D, ⟨hDl, h₁⟩, h₂, hread⟩ := hR
  obtain ⟨a', ha', hext⟩ := exists_isLawful_extend_of_restrictFace hDl h₁ ha
  refine ⟨fun j ↦ a' (faceCell h₂ j), isLawful_comp_faceCell h₂ ha', fun i ↦ ?_,
    fun j hj hjt ↦ ?_⟩
  · rw [← hext, faceCell_faceCell h₁ h₂ ht hd]
  obtain ⟨s, hsl, hst, hs⟩ := hread (faceCell h₂ j) (D.toScheme.faceCell_mem_visibleCells _ j)
    ((last_mem_scope_faceCell_iff h₂ j).mpr hj) (by rw [label_faceCell]; exact hjt)
  obtain ⟨z, rfl⟩ := exists_faceCell_eq_of_last_notMem h₁ hsl
  have hle := ha'.le_of_forall_row_le (Y := ((univ : Finset (Fin (k + 1))),
      D.toCellScheme.grade (faceCell h₁ z)))
    (hDl.isComplete _ ⟨D.univ_mem_faces, D.isWellFormed.isWellFormed.grade_pos _,
      by simpa using D.grade_le (faceCell h₁ z)⟩) (subset_univ _) rfl (subset_univ _) hs.1 hs.2
  refine ⟨z, by rw [← label_faceCell h₁]; exact hst, ?_, by rw [← hext]; exact hle⟩
  have := hs.1
  rwa [grade_faceCell, grade_faceCell] at this

/-! ### Reading the labels of one block in the own block -/

/-- The row of a cell `C` of `P` **reads a cell labelled `l` in its own block**: some cell `z`
below `C`, labelled `l`, is read by the row of `C` in the block `[μ, μ + ω)` (`μ` zero or a limit)
of its reading of `C` itself. -/
def ReadsInOwnBlock {m : ℕ} (P : StageType.{u} α m) (C : Fin P.card) (l : Label.{u}) : Prop :=
  ∃ z, ∃ hz : z ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C), P.label z = l ∧
    ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ i i' : ℕ,
      P.rows.row C ⟨z, hz⟩ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
      P.rows.row C ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩ =
        ((μ + i' : Ordinal.{u}) : Label.{u})

/-- The clause of **block-tight saturations** at a legal `p` on `N` points and a block start `μ`:
some scheme on `N + 1` points carries a coface of `p`, and in every coface of `p` on it every cell
of graded index `(univ, N)` reads, in its own block, every label of `p` in the block `[μ, μ + ω)`
that is not self-visible at `N`. -/
def IsBlockTight {N : ℕ} (p : StageType.{u} α N) (μ : Ordinal.{u}) : Prop :=
  ∃ S : Scheme.{u} (N + 1), (p.cofaces ∩ saturationFamily S).Nonempty ∧
    ∀ q ∈ p.cofaces ∩ saturationFamily S, ∀ G : Fin q.card,
      q.toCellScheme.gradedIndex G = (univ, N) →
      ∀ z : Fin p.card, ¬ IsSelfVisible N (p.label z) →
        (∃ i : ℕ, p.label z = ((μ + i : Ordinal.{u}) : Label.{u})) →
        ReadsInOwnBlock q G (p.label z)

variable (α) in
/-- **Block-tight saturations**: the clause `IsBlockTight` at every legal `p` and every block
start. -/
def HasBlockTightSaturations : Prop :=
  ∀ {N : ℕ} (p : StageType.{u} α N), p.IsLegal → ∀ μ : Ordinal.{u}, Order.IsSuccPrelimit μ →
    IsBlockTight p μ

/-- The **block prescription** of `p` and `μ`: at the grade `N`, every cell of `p` labelled in the
block `[μ, μ + ω)` and not self-visible at `N` is read in the block of the reading of the cell
itself.  The cells read are cells of `p` (old witnesses). -/
def blockPrescription {N : ℕ} (p : StageType.{u} α N) (d : StageType.{u} α (n + 1))
    (μ : Ordinal.{u}) : FullRowPrescription p d :=
  fun g r w ↦ g = N → ∀ z, ¬ IsSelfVisible N (p.label z) →
    (∃ i : ℕ, p.label z = ((μ + i : Ordinal.{u}) : Label.{u})) →
    ∃ (c : Ordinal.{u}) (i i' : ℕ), Order.IsSuccPrelimit c ∧
      r (.inl z) = ((c + i : Ordinal.{u}) : Label.{u}) ∧ w = ((c + i' : Ordinal.{u}) : Label.{u})

/-- **A prescribed extension for the block prescription is block-tight**: its scheme carries a
coface of `p`, and since the condition concerns rows and the old cells, every coface on it reads the
labels of the block in the own block, through the cells of `p`. -/
theorem IsPrescribedExtension.isBlockTight {N : ℕ} {p : StageType.{u} α N} {h : Fin n ↪ Fin N}
    {d : StageType.{u} α (n + 1)} {μ : Ordinal.{u}} {D : StageType.{u} α (N + 1)}
    (hD : IsPrescribedExtension p h d (blockPrescription p d μ) D) : IsBlockTight p μ := by
  obtain ⟨hDl, h₁, -, hS⟩ := hD
  refine ⟨D.toScheme, ⟨D, ⟨hDl, h₁⟩, rfl⟩, fun q ⟨hq, hqS⟩ G hG z hz hzμ ↦ ?_⟩
  rw [mem_saturationFamily] at hqS
  obtain ⟨he₁, he₂, hreal⟩ : ExtendsWithPrescribedRows p h d (blockPrescription p d μ) q.toScheme :=
    hqS ▸ hS
  obtain ⟨c, i, i', hc, hr, hw⟩ := hreal G N hG rfl z hz hzμ
  -- unfold `knownReading` at the old cell `z`
  change q.rowAt G (faceCell hq.2 z) = _ at hr
  have hmem := Scheme.mem_below_of_rowAt_ne_bot (hr ▸ WithBot.coe_ne_bot)
  refine ⟨faceCell hq.2 z, hmem, label_faceCell hq.2 z, c, hc, i, i', ?_, ?_⟩
  · rw [← Scheme.rowAt_of_mem hmem]; exact hr
  · rw [← Scheme.rowAt_of_mem]; exact hw

/-- **Prescribed rows give the block-tight clause where the block prescription is compatible**,
with any legal donor on one point over the empty face.  The compatibility hypothesis fails wherever
`p` has a lawful labelling `⊥` at a cell of the block and not `⊥` at a cell of grade `N`
(`not_isFaceCompatible_block`). -/
theorem _root_.VaughtConjecture.StageType.HasPrescribedFullRows.isBlockTight
    (hpr : HasPrescribedFullRows.{u} α) {N : ℕ} {p : StageType.{u} α N} (hp : p.IsLegal)
    (μ : Ordinal.{u}) {t : StageType.{u} α 0}
    (ht : restrictFace (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin N) p = some t)
    {d : StageType.{u} α 1} (hd' : d.IsLegal) (hd : restrictFace Fin.castSuccEmb d = some t)
    (hc : IsFaceCompatible p ht d hd (blockPrescription p d μ)) : IsBlockTight p μ :=
  let ⟨_, hD⟩ := hpr p _ t ht d hd hp hd' _ hc
  IsPrescribedExtension.isBlockTight hD

/-- **Block-tight saturations from prescribed rows**, where every block prescription is
compatible over the empty face with the one-point donor of the one-point scheme.  This is not a
reduction: the compatibility hypothesis `hc` fails at every stage `α > 1`, at the refuting context
`CoupledGatedExtensionCounterexample.P α` of the per-block route (argued from
`not_isFaceCompatible_block` and the lawful labelling of that context that is `⊥` at its cell `z₁`
and `ω + 2` at its cell of grade `2`; see the module docstring). -/
theorem _root_.VaughtConjecture.StageType.HasPrescribedFullRows.hasBlockTightSaturations
    (hpr : HasPrescribedFullRows.{u} α)
    (hc : ∀ {N : ℕ} (p : StageType.{u} α N), p.IsLegal → ∀ μ : Ordinal.{u},
      Order.IsSuccPrelimit μ → ∀ (t : StageType.{u} α 0)
      (ht : restrictFace (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin N) p = some t)
      (hd : restrictFace Fin.castSuccEmb (Scheme.isLegal_onePoint.{u}.toStageType α) = some t),
      IsFaceCompatible p ht _ hd (blockPrescription p _ μ)) :
    HasBlockTightSaturations.{u} α := by
  intro N p hp μ hμ
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (p.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin N))
  obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.mp
    ((Scheme.isLegal_onePoint.{u}.toStageType α).isSome_restrictFace_of_zero Fin.castSuccEmb)
  have hd : restrictFace Fin.castSuccEmb (Scheme.isLegal_onePoint.{u}.toStageType α) = some t :=
    ht₀.trans (by rw [eq_of_zero t₀ t])
  exact hpr.isBlockTight hp μ ht (Scheme.isLegal_onePoint.isLegal_toStageType α) hd
    (hc p hp μ hμ t ht hd)

/-- **No admissible row for the block prescription reads a block cell labelled `⊥` with a value
other than `⊥`**: if the labelling `L` is `⊥` at a cell `z` of `p` in the block `[μ, μ + ω)`, not
self-visible at `N`, then an admissible row at the grade `N` reads `z` at `c + i` and itself at
`c + i'` in one block; the transformation sends `c + i` to `⊥`, so, commuting with the visibility
replacement in that block, it sends `c + i'` to `⊥`, and the value is `⊥`. -/
theorem not_isAdmissibleRow_block {N : ℕ} {p : StageType.{u} α N} {d : StageType.{u} α (n + 1)}
    {μ : Ordinal.{u}} {L r : KnownCell p d → Label.{u}} {w v : Label.{u}} {z : Fin p.card}
    (hz : ¬ IsSelfVisible N (p.label z))
    (hzμ : ∃ i : ℕ, p.label z = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hzg : p.toCellScheme.grade z ≤ N) (hLz : L (.inl z) = ⊥) (hv : v ≠ ⊥)
    (h : IsAdmissibleRow p d (blockPrescription p d μ) L N r w v) : False := by
  obtain ⟨hΦ, -, -, -, -, gs, σ, hw, hvw, htr⟩ := h
  obtain ⟨c, i, i', hc, hr, hwc⟩ := hΦ rfl z hz hzμ
  have ht := htr (.inl z) hzg
  simp only [hLz, bot_le, min_eq_left, knownGrade, Sum.elim_inl, hr] at ht
  have hgN : gs N ≠ ⊥ := fun h0 ↦ hv (by rw [hvw, h0, min_bot_right])
  have hgz : gs (p.toCellScheme.grade z) ≠ ⊥ := fun h0 ↦
    hgN (le_bot_iff.mp (h0 ▸ hw.antitone hzg))
  have hσ : σ ((c + i : Ordinal.{u}) : Label.{u}) = ⊥ :=
    (min_eq_bot.mp ht.symm).resolve_right hgz
  have hvr := visibilityReplace_coe_add_natCast (n := max i i' + 1) hc
    (show i < max i i' + 1 by omega) i'
  have hcomm := hw.visibilityReplace_comm ((c + i : Ordinal.{u}) : Label.{u}) (max i i' + 1)
    (by rw [hσ]; exact bot_le) i' (by omega)
  rw [hvr, hσ, visibilityReplace_bot] at hcomm
  exact hv (by rw [hvw, hwc, hcomm, min_bot_left])

/-- **The block prescription is not compatible with the faces** wherever `p` has a lawful labelling
that is `⊥` at a cell `z` of the block `[μ, μ + ω)`, not self-visible at `N`, and not `⊥` at a cell
`T` of grade `N`: the admissible row serving `T` would have a value at least the label of `T`, and
it reads `z` (`not_isAdmissibleRow_block`).  With the one-point donor, this is the compatibility
hypothesis of `StageType.HasPrescribedFullRows.hasBlockTightSaturations` failing at `p`. -/
theorem not_isFaceCompatible_block {N : ℕ} {p : StageType.{u} α N} {t : StageType.{u} α 0}
    (ht : restrictFace (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin N) p = some t)
    {d : StageType.{u} α 1} (hd : restrictFace Fin.castSuccEmb d = some t) {μ : Ordinal.{u}}
    {z T : Fin p.card} (hz : ¬ IsSelfVisible N (p.label z))
    (hzμ : ∃ i : ℕ, p.label z = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hT : p.toCellScheme.grade T = N) {a : Fin p.card → Label.{u}} (ha : p.rows.IsLawful a)
    (haz : a z = ⊥) (haT : a T ≠ ⊥) :
    ¬ IsFaceCompatible p ht d hd (blockPrescription p d μ) := by
  intro hc
  obtain ⟨b, -, -, hadm⟩ := hc a ha
  have hN : 0 < N := hT ▸ p.isWellFormed.isWellFormed.grade_pos T
  obtain ⟨r, w, v, hv, hrow⟩ := hadm N hN (by omega) (some (.inl T)) (fun T' hT' ↦ by
    cases hT'; exact hT)
  have hvb : v ≠ ⊥ := fun h0 ↦ haT (le_bot_iff.mp (h0 ▸ hv _ rfl))
  exact not_isAdmissibleRow_block hz hzμ (p.grade_le z) haz hvb hrow

/-! ### Reading the new cells through the cap -/

/-- **A cell reads a new cell through the cap**: in a scheme `E` on `m + 1` points carrying `T⁺`
on its first points, the row of `u` reads the cell `e` as a cell labelled `ℓ`, relative to the cap
`b`: as `⊥` if `ℓ = ⊥`; as it reads `b` if `ℓ = ⊤`; and, if `ℓ = μ + n` with `μ` zero or a limit,
with `n` below the grade of `b` and at `ω · c + n`, where it reads at `ω · c + i` a reference cell
of `T⁺` labelled `μ + i`, with `i` below the grade of `b`. -/
def ReadsThroughCap {m : ℕ} (Tp : StageType.{u} α m) (E : Scheme.{u} (m + 1))
    (b : Fin (E.comap Fin.castSuccEmb).card) (u e : Fin E.card) (ℓ : Label.{u}) : Prop :=
  ∀ (he : e ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u))
    (hb : E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u)),
    (ℓ = ⊥ → E.rows.row u ⟨e, he⟩ = ⊥) ∧
    (ℓ = ⊤ → E.rows.row u ⟨e, he⟩ = E.rows.row u ⟨_, hb⟩) ∧
    ∀ (μ : Ordinal.{u}) (n : ℕ), Order.IsSuccPrelimit μ →
      ℓ = ((μ + n : Ordinal.{u}) : Label.{u}) →
        n < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
        ∃ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card) (i : ℕ) (c : Ordinal.{u}),
          (a : ℕ) = a₀ ∧ Tp.label a₀ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
          i < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
          ∃ ha : E.cellMap Fin.castSuccEmb a ∈
              E.toCellScheme.below (E.toCellScheme.gradedIndex u),
            E.rows.row u ⟨_, ha⟩ = ((Ordinal.omega0 * c + i : Ordinal.{u}) : Label.{u}) ∧
            E.rows.row u ⟨e, he⟩ = ((Ordinal.omega0 * c + n : Ordinal.{u}) : Label.{u})

/-- A scheme `E` on `m + 1` points is a **cap-reading scheme** for `T⁺`, `f`, `D` and the cap
`b₀` of `T⁺`: it carries a coface of the stage reduction `T⁺↓β`, its face along `extendByLast f`
is the scheme of `D`, and some cell `s` of the grade of the cap whose graded index lies above the
cap and the new cells of `D` is such that every cell of that graded index reads each new cell of
`D` through the cap as labelled in `D`.  These are the conditions on the scheme in the sufficient
condition for stable recovery through a reading cell; the remaining conditions concern the cap's
label and the calibration. -/
def IsCapReadingScheme {β : Ordinal.{u}} {m : ℕ} (Tp : StageType.{u} α m)
    (hβ : Order.IsSuccPrelimit β) (f : Fin k ↪ Fin m) (D : StageType.{u} α (k + 1))
    (b₀ : Fin Tp.card) (E : Scheme.{u} (m + 1)) : Prop :=
  (∃ q ∈ (Tp.reduce hβ).cofaces, q.toScheme = E) ∧
    (∃ _ : univ.map (extendByLast f) ∈ E.toCellScheme.faces,
      E.comap (extendByLast f) = D.toScheme) ∧
    ∃ b : Fin (E.comap Fin.castSuccEmb).card, (b : ℕ) = b₀ ∧ ∃ s : Fin E.card,
      E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex s) ∧
      E.toCellScheme.grade s = E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
      ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
        Fin.last k ∈ D.toCellScheme.scope j →
          E.cellMap (extendByLast f) i ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex s) ∧
          ∀ u, E.toCellScheme.gradedIndex u = E.toCellScheme.gradedIndex s →
            ReadsThroughCap Tp E b u (E.cellMap (extendByLast f) i) (D.label j)

/-- The **cap prescription** of `T⁺`, `D` and the cap `b₀`: at the grade of the cap, every new
cell of `D` is read as `⊥` if labelled `⊥`, as the cap if labelled `⊤`, and, if labelled `μ + n`
with `n` below the grade of the cap, at `ω · c + n` where a reference cell of `T⁺` labelled `μ + i`,
`i` below the grade of the cap, is read at `ω · c + i`. -/
def capPrescription {m : ℕ} (Tp : StageType.{u} α m) (D : StageType.{u} α (k + 1))
    (b₀ : Fin Tp.card) : FullRowPrescription Tp D :=
  fun g r _ ↦ g = Tp.toCellScheme.grade b₀ → ∀ j, Fin.last k ∈ D.toCellScheme.scope j →
    (D.label j = ⊥ → r (.inr j) = ⊥) ∧ (D.label j = ⊤ → r (.inr j) = r (.inl b₀)) ∧
    ∀ (μ : Ordinal.{u}) (n : ℕ), Order.IsSuccPrelimit μ →
      D.label j = ((μ + n : Ordinal.{u}) : Label.{u}) → n < Tp.toCellScheme.grade b₀ ∧
      ∃ (a₀ : Fin Tp.card) (i : ℕ) (c : Ordinal.{u}),
        Tp.label a₀ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i < Tp.toCellScheme.grade b₀ ∧
        r (.inl a₀) = ((Ordinal.omega0 * c + i : Ordinal.{u}) : Label.{u}) ∧
        r (.inr j) = ((Ordinal.omega0 * c + n : Ordinal.{u}) : Label.{u})

/-- **A prescribed extension for the cap prescription is a cap-reading scheme**, when the grade of
the cap
exceeds `k` (so that the new cells of `D` lie below the cells of full scope of the grade of the
cap). -/
theorem IsPrescribedExtension.isCapReadingScheme {β : Ordinal.{u}} {m : ℕ} {Tp : StageType.{u} α m}
    (hβ : Order.IsSuccPrelimit β) {f : Fin k ↪ Fin m} {D : StageType.{u} α (k + 1)}
    {b₀ : Fin Tp.card} (hkN : k < Tp.toCellScheme.grade b₀) {D' : StageType.{u} α (m + 1)}
    (hD : IsPrescribedExtension Tp f D (capPrescription Tp D b₀) D') :
    IsCapReadingScheme Tp hβ f D b₀ D'.toScheme := by
  obtain ⟨hDl, h₁, h₂, he₁, he₂, hreal⟩ := hD
  have hf₁ := ((restrictFace_eq_some_iff D' _).mp h₁).1
  have hf₂ := ((restrictFace_eq_some_iff D' _).mp h₂).1
  obtain ⟨q, hq, hqS⟩ := nonempty_cofaces_inter_saturationFamily (p := Tp.reduce hβ) hβ hDl hf₁ he₁
  set N := Tp.toCellScheme.grade b₀ with hN
  obtain ⟨s, hs⟩ := hDl.isComplete ((univ : Finset (Fin (m + 1))), N)
    ⟨D'.univ_mem_faces, Tp.isWellFormed.isWellFormed.grade_pos b₀,
      by simpa using (Tp.grade_le b₀).trans (Nat.le_succ m)⟩
  have hb : faceCell h₁ b₀ ∈ D'.toCellScheme.below (D'.toCellScheme.gradedIndex s) := by
    rw [hs]; exact ⟨subset_univ _, (grade_faceCell h₁ b₀).le⟩
  refine ⟨⟨q, hq, hqS⟩, ⟨hf₂, he₂⟩, Fin.cast (congrArg Scheme.card he₁).symm b₀, rfl, s, hb,
    (congrArg Prod.snd hs).trans (grade_faceCell h₁ b₀).symm, fun i j hij hj ↦ ?_⟩
  -- the cell of `D'` at the new cell `j` of `D`
  have hie : D'.cellMap (extendByLast f) i = faceCell h₂ j :=
    Scheme.cellMap_congr rfl hij
  have hjm : faceCell h₂ j ∈ D'.toCellScheme.below (D'.toCellScheme.gradedIndex s) := by
    rw [hs]
    exact ⟨subset_univ _, (grade_faceCell h₂ j).trans_le ((D.grade_le j).trans hkN)⟩
  refine ⟨hie ▸ hjm, fun u hu he hb' ↦ ?_⟩
  obtain ⟨hbot, htop, hord⟩ := hreal u N (hu.trans hs) rfl j hj
  have hre : D'.rowAt u (faceCell h₂ j) = D'.rows.row u ⟨D'.cellMap (extendByLast f) i, he⟩ := by
    rw [← hie]; exact Scheme.rowAt_of_mem he
  have hrb : D'.rowAt u (faceCell h₁ b₀) = D'.rows.row u ⟨_, hb'⟩ := Scheme.rowAt_of_mem hb'
  refine ⟨fun h0 ↦ hre ▸ hbot h0, fun ht ↦ hre ▸ hrb ▸ htop ht, fun μ n hμ hℓ ↦ ?_⟩
  obtain ⟨hn, a₀, i', c, ha₀, hi, hra, hrj⟩ := hord μ n hμ hℓ
  -- unfold `knownReading` at the reference cell `a₀`
  change D'.rowAt u (faceCell h₁ a₀) = _ at hra
  have ham := Scheme.mem_below_of_rowAt_ne_bot (hra ▸ WithBot.coe_ne_bot)
  exact ⟨hn.trans_eq (grade_faceCell h₁ b₀).symm, Fin.cast (congrArg Scheme.card he₁).symm a₀, a₀,
    i', c, rfl, ha₀, hi.trans_eq (grade_faceCell h₁ b₀).symm, ham,
    (Scheme.rowAt_of_mem ham).symm.trans hra, hre.symm.trans hrj⟩

/-- **Prescribed rows give cap-reading schemes where the cap prescription is compatible**: under
`StageType.HasPrescribedFullRows α`, for a legal `T⁺`, a face `P` of `T⁺` along `f`, a coface `D`
of `P`, and a cap `b₀` of grade above `k`, a compatible cap prescription gives a cap-reading
scheme (the part of the sufficient condition for a stable recovery scheme concerning the
scheme). -/
theorem _root_.VaughtConjecture.StageType.HasPrescribedFullRows.exists_isCapReadingScheme
    {β : Ordinal.{u}} {m : ℕ} (hpr : HasPrescribedFullRows.{u} α) {Tp : StageType.{u} α m}
    (hTp : Tp.IsLegal) (hβ : Order.IsSuccPrelimit β) {f : Fin k ↪ Fin m} {P : StageType.{u} α k}
    (hP : restrictFace f Tp = some P) {D : StageType.{u} α (k + 1)} (hD : D ∈ P.cofaces)
    {b₀ : Fin Tp.card} (hkN : k < Tp.toCellScheme.grade b₀)
    (hc : IsFaceCompatible Tp hP D hD.2 (capPrescription Tp D b₀)) :
    ∃ E, IsCapReadingScheme Tp hβ f D b₀ E :=
  let ⟨_, hD'⟩ := hpr Tp f P hP D hD.2 hTp hD.1 _ hc
  ⟨_, IsPrescribedExtension.isCapReadingScheme hβ hkN hD'⟩

end VaughtConjecture.PrescribedFullRows

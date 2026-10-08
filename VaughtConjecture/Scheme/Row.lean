/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.StepWitness
import VaughtConjecture.Scheme.Cell

/-!
# Semantic rows and lawful sections

Roadmap, Layer 1 (semantic rows and lawful sections; the order, availability, and locality laws;
restriction, transport, pullback, and the bottom cases); semantic contract, item 3; the
expositions, §1 (semantic rows constrain which labellings are lawful).

The **semantic rows** of a cell scheme `D` (`CellScheme.Rows D`) are raw data: for every cell `s`
a labelling `R.row s` of the cells below `s`, that is, of `D.below (D.gradedIndex s)`.  They are
separate from the scheme itself; the bundle of a scheme with its rows (and its label section)
belongs to the stage types (`VaughtConjecture.Stage.Basic`).  A labelling
`p : ι → Label` of all cells is a **lawful section** of the rows (`Rows.IsLawful R p`) when it
satisfies three laws:

* **order**: every label `p d` is self-visible at the grade of its cell;
* **locality**: for every cell `s`, the row `R.row s` transforms (`Label.TransformsTo`, over the
  grades of the cells below `s`) to the section below `s` capped at the label of `s`,
  `d ↦ min (p d) (p s)`;
* **availability**: if the scope of `s` lies in the scope of `t` and the grades agree, then some
  cell `u` with the graded index of `t` has `p s ≤ p u`.  Availability quantifies over all cells
  with a given graded index, so it depends on the multiplicities of cells.

Rows pull back along a lower embedding of schemes (`Rows.comap`, functorially: `comap_id`,
`comap_comap`), and lawful sections pull back with them (`IsLawful.comap`); along an equivalence
of cells that is a lower embedding, in both directions (`isLawful_comap_equiv_iff`).  Instances
are the restriction to a face (`Rows.restrict`, `IsLawful.restrict`), the pullback along an
embedding of ground sets, reindexing along an equivalence of cells, and the lower sets: a
labelling `r` of the cells below a pair `X` is *lawful below `X`* (`Rows.IsLawfulBelow R X r`)
when it is a lawful section of the rows restricted to the scheme `D⟨X⟩` of cells below `X`
(`isLawfulBelow_iff`); along a lower embedding mapping the cells below `X` onto the cells below
`Y`, lawfulness below `X` is lawfulness below `Y` (`isLawfulBelow_comap_iff`).  Lawful sections
restrict to every lower set (`IsLawful.isLawfulBelow`) and from a lower set to a smaller one
(`IsLawfulBelow.mono`).  At a stage `β` that is zero or a limit, the stage reduction
`Label.reduce β ∘ p` of a lawful section `p` is lawful (`IsLawful.reduce`), by the reduction rule
`Label.TransformsTo.reduce`; at a successor stage it need not be
(`VaughtConjecture.Stage.Examples`).  Capping a lawful section at a label `c` that is
self-visible at the grade of every cell whose label is at least `c` keeps it lawful
(`IsLawful.min_const`, [Kni26, Lemma 2.5.8]), in particular at a cap self-visible at a bound on all
grades (`IsLawful.min_const_of_isSelfVisible`), and below a pair (`IsLawfulBelow.min_const`,
`IsLawfulBelow.min_const_of_isSelfVisible`); capping at a cutoff that is not self-visible need
not keep lawfulness.  Capping only the cells whose scope contains a point `a` keeps lawfulness when
availability carries no label above the cap into them from a cell avoiding `a`
(`IsLawful.min_const_of_mem_scope`); more generally, capping only the cells of a set closed
upward in the graded order keeps lawfulness when availability carries no label above the cap into
the set (`IsLawful.min_const_of_upper`).  Capping only the cells of the top grade `N` at a cap
self-visible at `N` also keeps a lawful section lawful (`IsLawful.capTopGrade`).

**Reading cells through a row.**  In a lawful section `p`, let the label of a cell `s` be at least
that of a cell `b` (a cap).  If the row of `s` reads a cell `a` and a cell `e` in one block, at
`ω · c + i` and `ω · c + o`, with the grades of `a` and `e` at most that of `b`, `i < grade b`,
`o ≤ grade b`, and `p a = μ + i` (`μ` zero or a limit) with `μ + i`, `μ + o` below `p b`, then
`p e = μ + o` (`IsLawful.label_eq_of_reading`, from `Label.TransformsTo.eq_coe_add_of_reading`); a
cell of grade at most that of `b` read as `b` has label at least `p b`
(`IsLawful.le_label_of_reading`), and a cell read as `⊥` has label `⊥` when `p s ≠ ⊥`
(`IsLawful.label_eq_bot_of_reading`).

**Dropping cells by blocks.**  A lawful section `q` not `⊥` at a cell `C` that is `⊥` at a cell
`x` read by the row of `C` at `μ + i` (`μ` zero or a limit) is `⊥` at every cell that row reads at
most `μ + j`, so at most the end of the block of `x` (`IsLawful.eq_bot_of_row_le_block`); so the
row of `C` reads `C` above that whole block (`IsLawful.lt_row_self_of_eq_bot`), and `q` is not `⊥`
at a cell read in the block of the reading of `C` (`IsLawful.ne_bot_of_row_mem_block`).  These
concern cells read at ordinals; a cell read as `⊥` has no block.

The constant bottom labelling is lawful for all rows (`isLawful_const_bot`), and a cell whose row is
bottom at the cell itself has bottom label in every lawful section
(`IsLawful.eq_bot_of_row_self_eq_bot`).  The rows are **consistent** (`Rows.IsConsistent`) when
each row `R.row s` is lawful below the graded index of `s`; consistent rows are orderly
(`IsConsistent.isOrderly`) and consistency pulls back along lower embeddings
(`IsConsistent.comap`).  Since the bottom labelling is always lawful, the mere existence of lawful
sections carries no information; consistency is the statement about the rows themselves.

The **bottom** rows (`Rows.bot D`) are constantly bottom.  Every cell's row is bottom at the cell
itself, so the only lawful section is the bottom labelling (`isLawful_bot_iff`), below every pair
as well (`isLawfulBelow_bot_iff`); the bottom rows are consistent (`isConsistent_bot`) and pull back
to the bottom rows (`comap_bot`).

## References

Semantic rows are the semantics of [Kni26, Definition 2.5.3], lawful sections the labellings
respecting them ([Kni26, Definition 2.5.4]: locality is its first clause, availability its
second), and consistency is [Kni26, Definition 2.5.12]; the bottom rows are the constantly bottom
semantics of the last clause of [Kni26, Lemma 4.2.2], and stage reduction is
[Kni26, Definition 3.1.2].
-/

universe u

namespace VaughtConjecture.CellScheme

open Label

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

/-- The **semantic rows** of a cell scheme [Kni26, §2.5]: for every cell `s`, a labelling `row s`
of the cells below `s`.  The rows are data separate from the scheme; the bundle of a scheme with
its rows belongs to the stage types. -/
@[ext]
structure Rows (D : CellScheme ι α) where
  /-- The semantic row of a cell: a labelling of the cells below it. -/
  row (s : ι) : D.below (D.gradedIndex s) → Label.{u}

namespace Rows

variable (R : D.Rows) {φ : κ → ι}

/-- Values of a row at equal cells and equal arguments are equal. -/
theorem row_congr {s s' : ι} (hs : s = s') {t : D.below (D.gradedIndex s)}
    {t' : D.below (D.gradedIndex s')} (ht : t.1 = t'.1) : R.row s t = R.row s' t' := by
  subst hs
  rw [Subtype.ext ht]

/-- The rows are *orderly*: every value of the row of `s` at a cell `t` is self-visible at the
grade of `t`. -/
def IsOrderly : Prop :=
  ∀ s (t : D.below (D.gradedIndex s)), IsSelfVisible (D.grade t) (R.row s t)

/-- The pullback of rows along a lower embedding `φ` of `E` into `D`: the row of `s` at `t` is
the row of `φ s` at `φ t`. -/
def comap (hφ : E.IsLowerEmbedding D φ) : E.Rows where
  row s t := R.row (φ s) ⟨φ t, (hφ.le_iff t s).mpr t.2⟩

/-- The row of a pulled-back cell. -/
@[simp] theorem comap_row (hφ : E.IsLowerEmbedding D φ) (s : κ) (t : E.below (E.gradedIndex s)) :
    (R.comap hφ).row s t = R.row (φ s) ⟨φ t, (hφ.le_iff t s).mpr t.2⟩ := rfl

/-- Pulling back along the identity does not change the rows. -/
@[simp] theorem comap_id : R.comap (IsLowerEmbedding.id D) = R := rfl

/-- Pulling back along two lower embeddings is pulling back along their composite. -/
@[simp] theorem comap_comap {μ γ : Type*} {F : CellScheme μ γ} {ψ : μ → κ}
    (hφ : E.IsLowerEmbedding D φ) (hψ : F.IsLowerEmbedding E ψ) :
    (R.comap hφ).comap hψ = R.comap (hφ.comp hψ) := rfl

/-- The rows of the restriction of a scheme to a face: the rows of the visible cells. -/
def restrict [DecidableEq α] (B : Finset α) : (D.restrict B).Rows :=
  R.comap (IsLowerEmbedding.restrict D B)

/-- The row of a cell of the restriction is its original row. -/
@[simp] theorem restrict_row [DecidableEq α] (B : Finset α) (s : D.visible (B : Set α))
    (t : (D.restrict B).below ((D.restrict B).gradedIndex s)) :
    (R.restrict B).row s t = R.row s ⟨t.1, t.2⟩ := rfl

/-! ### Lawful sections -/

/-- A labelling `p` of the cells is a **lawful section** of the rows `R` [Kni26, §2.5]: it
satisfies the order, locality, and availability laws. -/
structure IsLawful (p : ι → Label.{u}) : Prop where
  /-- Order: the label of every cell is self-visible at the grade of the cell. -/
  orderly (d : ι) : IsSelfVisible (D.grade d) (p d)
  /-- Locality: the row of every cell `s` transforms, over the grades of the cells below `s`, to
  the labelling `d ↦ min (p d) (p s)` of the cells below `s`. -/
  locality (s : ι) : TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
    (fun d ↦ min (p d) (p s))
  /-- Availability: if the scope of `s` lies in the scope of `t` and their grades agree, then
  some cell with the graded index of `t` has a label at least that of `s`. -/
  availability (s t : ι) : D.scope s ⊆ D.scope t → D.grade s = D.grade t →
    ∃ u, D.gradedIndex u = D.gradedIndex t ∧ p s ≤ p u

/-- A labelling `r` of the cells below `X` is *lawful below `X`*: it is a lawful section of the
rows restricted to the scheme `D⟨X⟩` of cells below `X`. -/
def IsLawfulBelow (X : Finset α × ℕ) (r : D.below X → Label.{u}) : Prop :=
  (R.comap (IsLowerEmbedding.subtypeVal_below D X)).IsLawful r

/-- The rows are **consistent** [Kni26, §2.5]: the row of every cell `s` is lawful
below the graded index of `s`. -/
def IsConsistent : Prop := ∀ s, R.IsLawfulBelow (D.gradedIndex s) (R.row s)

variable {R}

/-- Lawfulness below `X` is lawfulness for the rows pulled back to the scheme `D⟨X⟩` of cells
below `X`. -/
theorem isLawfulBelow_iff {X : Finset α × ℕ} {r : D.below X → Label.{u}} :
    R.IsLawfulBelow X r ↔ (R.comap (IsLowerEmbedding.subtypeVal_below D X)).IsLawful r :=
  Iff.rfl

/-- The constant bottom labelling is a lawful section of all rows. -/
theorem isLawful_const_bot : R.IsLawful fun _ ↦ ⊥ where
  orderly _ := isSelfVisible_bot _
  locality s := by simpa only [min_self] using TransformsTo.bot _ (R.row s)
  availability _ t _ _ := ⟨t, rfl, le_rfl⟩

/-- The constant bottom labelling is lawful below every pair. -/
theorem isLawfulBelow_const_bot (X : Finset α × ℕ) : R.IsLawfulBelow X fun _ ↦ ⊥ :=
  isLawfulBelow_iff.mpr isLawful_const_bot

/-- Every labelling of a scheme without cells is lawful. -/
theorem isLawful_of_isEmpty [IsEmpty ι] (p : ι → Label.{u}) : R.IsLawful p where
  orderly d := isEmptyElim d
  locality s := isEmptyElim s
  availability s := isEmptyElim s

namespace IsLawful

variable {p : ι → Label.{u}}

/-- A cell whose row is bottom at the cell itself has bottom label in every lawful section. -/
theorem eq_bot_of_row_self_eq_bot (h : R.IsLawful p) (s : ι)
    (hs : R.row s ⟨s, D.mem_below_gradedIndex s⟩ = ⊥) : p s = ⊥ := by
  simpa using (h.locality s).eq_bot (d := ⟨s, D.mem_below_gradedIndex s⟩) hs

/-- **Pullback of lawful sections**: along a lower embedding `φ`, a lawful section `p` of `R`
pulls back to the lawful section `p ∘ φ` of the pulled-back rows. -/
theorem comap (h : R.IsLawful p) (hφ : E.IsLowerEmbedding D φ) :
    (R.comap hφ).IsLawful (p ∘ φ) where
  orderly t := hφ.grade_eq t ▸ h.orderly (φ t)
  locality s := by
    have hg : (fun t : E.below (E.gradedIndex s) ↦ E.grade t) =
        (fun d : D.below (D.gradedIndex (φ s)) ↦ D.grade d) ∘
          fun t : E.below (E.gradedIndex s) ↦
            (⟨φ t, (hφ.le_iff t s).mpr t.2⟩ : D.below (D.gradedIndex (φ s))) :=
      funext fun t ↦ (hφ.grade_eq t).symm
    rw [hg]
    exact (h.locality (φ s)).reindex _
  availability s t hst hg := by
    have hle : D.gradedIndex (φ s) ≤ D.gradedIndex (φ t) :=
      (hφ.le_iff s t).mpr ((gradedIndex_le_iff E).mpr ⟨hst, hg.le⟩)
    obtain ⟨u, hu, hpu⟩ := h.availability (φ s) (φ t) hle.1
      (by rw [hφ.grade_eq, hφ.grade_eq, hg])
    obtain ⟨u', rfl⟩ := hφ.mem_range t u hu.le
    exact ⟨u', (hφ.gradedIndex_eq_iff u' t).mp hu, hpu⟩

/-- **Restriction to a face**: a lawful section restricts to a lawful section of the restricted
rows on the cells visible in the face. -/
theorem restrict [DecidableEq α] (h : R.IsLawful p) (B : Finset α) :
    (R.restrict B).IsLawful fun d ↦ p d :=
  h.comap (IsLowerEmbedding.restrict D B)

/-- A lawful section is lawful below every pair. -/
theorem isLawfulBelow (h : R.IsLawful p) (X : Finset α × ℕ) :
    R.IsLawfulBelow X fun d ↦ p d :=
  isLawfulBelow_iff.mpr (h.comap (IsLowerEmbedding.subtypeVal_below D X))

/-- **Stage reduction of lawful sections.**  At a stage `β` that is zero or a limit, the stage
reduction of a lawful section is lawful.  The hypothesis on `β` is necessary
(`VaughtConjecture.Stage.Examples`). -/
theorem reduce {β : Ordinal.{u}} (h : R.IsLawful p) (hβ : Order.IsSuccPrelimit β) :
    R.IsLawful (Label.reduce β ∘ p) where
  orderly d := (h.orderly d).reduce β
  locality s := by
    simpa [Function.comp_def, (monotone_reduce β).map_min] using (h.locality s).reduce hβ
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := h.availability s t hst hg
    exact ⟨u, hu, monotone_reduce β hle⟩

/-- **Capping a lawful section** [Kni26, Lemma 2.5.8].  If the cap `c` is self-visible at the
grade of every cell whose label is at least `c`, the section capped at `c` is lawful.  At a cell
whose label is below `c` the capped section agrees with `p`; at the others its label is `c`, and
the locality of such an owner is capped at `c` (`Label.TransformsTo.min_const`).  It gives the
same statement below a pair (`CellScheme.Rows.IsLawfulBelow.min_const`). -/
theorem min_const (hp : R.IsLawful p) {c : Label.{u}}
    (hc : ∀ d, c ≤ p d → IsSelfVisible (D.grade d) c) : R.IsLawful fun d ↦ min (p d) c where
  orderly d := by
    rcases le_total (p d) c with h | h
    · rw [min_eq_left h]; exact hp.orderly d
    · rw [min_eq_right h]; exact hc d h
  locality s := by
    rcases le_total c (p s) with h | h
    · have := (hp.locality s).min_const (fun d ↦ d.2.2) (hc s h)
      -- The target `d ↦ min (min (p d) c) (min (p s) c)` is `d ↦ min (min (p d) (p s)) c`.
      convert this using 2 with d
      rw [min_min_min_comm, min_self]
    · -- Here `p s ≤ c`, so the capped target reduces to `d ↦ min (p d) (p s)`, that of `p`.
      convert hp.locality s using 2 with d
      rw [min_min_min_comm, min_self]
      exact min_eq_left ((min_le_right _ _).trans h)
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    exact ⟨u, hu, min_le_min_right c hle⟩

/-- **Capping a lawful section at a cap self-visible at a grade bound**, the special case of
[Kni26, Lemma 2.5.8] in which the grades are at most `K` and `c` is self-visible at `K`. -/
theorem min_const_of_isSelfVisible {K : ℕ} (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K)
    {c : Label.{u}} (hc : IsSelfVisible K c) : R.IsLawful fun d ↦ min (p d) c :=
  hp.min_const fun d _ ↦ hc.mono (hK d)

/-- **Capping an upper set of cells.**  Let `c` be self-visible at a bound `K` on the grades, and
let `Z` be a set of cells closed upward in the graded order.  Capping at `c` only the cells of `Z`
keeps a lawful section lawful, provided availability carries no label above `c` into `Z`: every
cell outside `Z` whose scope lies in the scope of a cell of `Z` of the same grade is labelled at
most `c`.  Locality at a cell of `Z` is capped at `c` (`Label.TransformsTo.min_const`), and
locality at a cell outside `Z` is unchanged, since the cells below it are outside `Z`.  The cells
whose scope contains a point form such a set (`IsLawful.min_const_of_mem_scope`), and so do the
cells whose scope contains a point and whose grade is at least a bound, and the cells of grade at
least a bound. -/
theorem min_const_of_upper (hp : R.IsLawful p) (Z : ι → Prop) [DecidablePred Z]
    (hZ : ∀ d s, Z d → D.gradedIndex d ≤ D.gradedIndex s → Z s) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {c : Label.{u}} (hc : IsSelfVisible K c)
    (havail : ∀ s t, D.scope s ⊆ D.scope t → D.grade s = D.grade t → ¬ Z s → Z t → p s ≤ c) :
    R.IsLawful fun d ↦ if Z d then min (p d) c else p d where
  orderly d := by
    split_ifs
    · exact (hp.orderly d).min (hc.mono (hK d))
    · exact hp.orderly d
  locality s := by
    by_cases hs : Z s
    · convert (hp.locality s).min_const (fun d ↦ d.2.2) (hc.mono (hK s)) using 2 with d
      by_cases hd : Z d
      · simp only [hs, hd, ↓reduceIte]
        rw [min_min_min_comm, min_self]
      · simp only [hs, hd, ↓reduceIte, min_assoc]
    · convert hp.locality s using 2 with d
      -- the cells below `s` are outside `Z`
      have hd : ¬ Z d := fun h ↦ hs (hZ _ _ h d.2)
      simp only [hs, hd, ↓reduceIte]
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    refine ⟨u, hu, ?_⟩
    have hut : Z u ↔ Z t := ⟨fun h ↦ hZ _ _ h hu.le, fun h ↦ hZ _ _ h hu.ge⟩
    by_cases ht : Z t
    · have hu' : Z u := hut.mpr ht
      by_cases hs : Z s
      · simpa only [hs, hu', ↓reduceIte] using min_le_min_right c hle
      · simpa only [hs, hu', ↓reduceIte] using le_min hle (havail s t hst hg hs ht)
    · have hs : ¬ Z s := fun h ↦ ht (hZ _ _ h ⟨hst, hg.le⟩)
      have hu' : ¬ Z u := fun h ↦ ht (hut.mp h)
      simpa only [hs, hu', ↓reduceIte] using hle

/-- **Capping the cells through a point.**  Let `c` be self-visible at a bound `K` on the grades,
and let `a` be a point.  Capping at `c` only the cells whose scope contains `a` keeps a lawful
section lawful, provided availability carries no label above `c` into them: every cell whose
scope avoids `a` and lies in the scope of a cell of the same grade containing `a` is labelled at
most `c`.  The cells through `a` form a set closed upward in the graded order
(`IsLawful.min_const_of_upper`). -/
theorem min_const_of_mem_scope [DecidableEq α] (hp : R.IsLawful p) (a : α) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {c : Label.{u}} (hc : IsSelfVisible K c)
    (havail : ∀ s t, D.scope s ⊆ D.scope t → D.grade s = D.grade t → a ∉ D.scope s →
      a ∈ D.scope t → p s ≤ c) :
    R.IsLawful fun d ↦ if a ∈ D.scope d then min (p d) c else p d :=
  hp.min_const_of_upper (a ∈ D.scope ·) (fun _ _ h hle ↦ hle.1 h) hK hc havail

/-- **Capping the top grade**, the top-grade variant of [Kni26, Lemma 2.5.8].  If every grade is
at most `N` and `c` is self-visible at `N`, then capping a lawful section at `c` at the cells of
grade `N` only, and keeping it at the others, gives a lawful section.  At a cell of grade `N` the
locality is that of `p` capped at `c` (`Label.TransformsTo.min_const`); the cells below a cell of
lower grade have lower grade, so its locality does not change; and availability compares cells of
equal grade. -/
theorem capTopGrade (hp : R.IsLawful p) {N : ℕ} (hN : ∀ d, D.grade d ≤ N)
    {c : Label.{u}} (hc : IsSelfVisible N c) :
    R.IsLawful fun d ↦ if D.grade d = N then min (p d) c else p d where
  orderly d := by
    split_ifs with h
    · exact (hp.orderly d).min (h ▸ hc)
    · exact hp.orderly d
  locality s := by
    by_cases hs : D.grade s = N
    · have := (hp.locality s).min_const (fun d ↦ hN d.1) hc
      convert this using 2 with d
      simp only [hs, ite_true]
      split_ifs with hd
      · rw [min_min_min_comm, min_self]
      · rw [min_assoc]
    · convert hp.locality s using 2 with d
      have hd : D.grade d.1 ≠ N := fun h ↦ hs (le_antisymm (hN s) (h ▸ d.2.2))
      simp only [hs, hd, ite_false]
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    refine ⟨u, hu, ?_⟩
    have hgu : D.grade u = D.grade s := (congrArg Prod.snd hu).trans hg.symm
    by_cases h : D.grade s = N
    · simp only [h, hgu, ite_true]
      exact min_le_min_right c hle
    · simp only [h, hgu, ite_false]
      exact hle

/-! ### Reading cells through a row -/

section Reading

open Ordinal

/-- **Recovery of a proper label at a reading cell**: in a lawful section `p`, let `s` be a cell
whose label is at least that of a cell `b` (the cap), and let the row of `s` read a reference cell
`a` and a cell `e` in one block, at `ω · c + i` and `ω · c + o`, with the grades of `a` and `e` at
most that of `b` and `i < grade b`, `o ≤ grade b`.  If `p a = μ + i` (`μ` zero or a limit) and
`μ + i`, `μ + o` lie strictly below `p b`, then `p e = μ + o`. -/
theorem label_eq_of_reading (h : R.IsLawful p) {s a b e : ι}
    (ha : a ∈ D.below (D.gradedIndex s)) (hb : b ∈ D.below (D.gradedIndex s))
    (he : e ∈ D.below (D.gradedIndex s)) {μ c : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    {i o : ℕ} (hab : D.grade a ≤ D.grade b) (hi : i < D.grade b) (ho : o ≤ D.grade b)
    (heb : D.grade e ≤ D.grade b) (hra : R.row s ⟨a, ha⟩ = ((ω * c + i : Ordinal.{u}) : Label.{u}))
    (hre : R.row s ⟨e, he⟩ = ((ω * c + o : Ordinal.{u}) : Label.{u}))
    (hpa : p a = ((μ + i : Ordinal.{u}) : Label.{u})) (hbs : p b ≤ p s)
    (hib : ((μ + i : Ordinal.{u}) : Label.{u}) < p b)
    (hob : ((μ + o : Ordinal.{u}) : Label.{u}) < p b) :
    p e = ((μ + o : Ordinal.{u}) : Label.{u}) := by
  have hqb : min (p b) (p s) = p b := min_eq_left hbs
  have key := (h.locality s).eq_coe_add_of_reading (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (e := ⟨e, he⟩)
    hμ hab hi ho heb hra hre (by
      -- the labelling of locality at `s` is `d ↦ min (p d) (p s)`
      change min (p a) (p s) = _
      rw [min_eq_left ((hpa ▸ hib).le.trans hbs), hpa]) (by
      -- the same labelling, at the cap
      change _ < min (p b) (p s)
      rwa [hqb]) (by
      -- the same labelling, at the cap
      change _ < min (p b) (p s)
      rwa [hqb])
  -- the same labelling, at the new cell
  change min (p e) (p s) = _ at key
  rcases le_total (p e) (p s) with h1 | h1
  · rwa [min_eq_left h1] at key
  · rw [min_eq_right h1] at key
    exact absurd key (hob.trans_le hbs).ne'

/-- **A cell read like the cap is at least the cap**: in a lawful section `p`, if the row of a cell
`s` with label at least that of `b` reads `e` as it reads `b`, and the grade of `e` is at most that
of `b`, then `p b ≤ p e`. -/
theorem le_label_of_reading (h : R.IsLawful p) {s b e : ι}
    (hb : b ∈ D.below (D.gradedIndex s)) (he : e ∈ D.below (D.gradedIndex s))
    (heb : D.grade e ≤ D.grade b) (hre : R.row s ⟨e, he⟩ = R.row s ⟨b, hb⟩) (hbs : p b ≤ p s) :
    p b ≤ p e := by
  have key := (h.locality s).le_of_le (d := ⟨b, hb⟩) (d' := ⟨e, he⟩) hre.symm.le heb
  -- the labelling of locality at `s` is `d ↦ min (p d) (p s)`
  change min (p b) (p s) ≤ min (p e) (p s) at key
  rw [min_eq_left hbs] at key
  exact key.trans (min_le_left _ _)

/-- **A cell read as bottom is bottom**: in a lawful section `p`, if the row of a cell `s` with a
label other than bottom reads `e` as `⊥`, then `p e = ⊥`. -/
theorem label_eq_bot_of_reading (h : R.IsLawful p) {s e : ι}
    (he : e ∈ D.below (D.gradedIndex s)) (hre : R.row s ⟨e, he⟩ = ⊥) (hs : p s ≠ ⊥) :
    p e = ⊥ := by
  have key := (h.locality s).eq_bot (d := ⟨e, he⟩) hre
  -- the labelling of locality at `s` is `d ↦ min (p d) (p s)`
  change min (p e) (p s) = ⊥ at key
  rcases min_eq_iff.mp key with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 hs

end Reading

end IsLawful

/-! ### Lawful sections along equivalences -/

/-- Rows pulled back along an equivalence of cells that is a lower embedding and then back along
its inverse are the original rows. -/
theorem comap_comap_symm (R : D.Rows.{u}) {e : κ ≃ ι} (h : E.IsLowerEmbedding D e) :
    (R.comap h).comap h.symm = R := by
  ext s t
  exact R.row_congr (e.apply_symm_apply s) (e.apply_symm_apply t)

/-- **Transport along an equivalence of cells** that is a lower embedding: `p ∘ e` is lawful for
the pulled-back rows exactly when `p` is lawful. -/
theorem isLawful_comap_equiv_iff {R : D.Rows.{u}} {e : κ ≃ ι} (h : E.IsLowerEmbedding D e)
    {p : ι → Label.{u}} : (R.comap h).IsLawful (p ∘ e) ↔ R.IsLawful p := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ hp.comap h⟩
  have h' := hp.comap h.symm
  rwa [comap_comap_symm, Function.comp_assoc, e.self_comp_symm, Function.comp_id] at h'

/-- For a lower embedding `φ` mapping the cells below `X` onto the cells below `Y`, a labelling of
the cells below `Y` is lawful below `Y` exactly when its transport along `belowEquiv` is lawful
below `X` for the pulled-back rows. -/
theorem isLawfulBelow_comap_iff {R : D.Rows.{u}} (hφ : E.IsLowerEmbedding D φ)
    {X : Finset β × ℕ} {Y : Finset α × ℕ} (h : φ '' E.below X = D.below Y)
    {r : D.below Y → Label.{u}} :
    (R.comap hφ).IsLawfulBelow X (r ∘ hφ.belowEquiv h) ↔ R.IsLawfulBelow Y r :=
  isLawful_comap_equiv_iff (R := R.comap (IsLowerEmbedding.subtypeVal_below D Y))
    (hφ.isLowerEmbedding_belowEquiv h)

namespace IsLawfulBelow

variable {X Y : Finset α × ℕ}

/-- **Restriction between lower sets**: a labelling lawful below `Y` restricts to one lawful
below every `X ≤ Y`. -/
theorem mono {q : D.below Y → Label.{u}} (h : R.IsLawfulBelow Y q) (hXY : X ≤ Y) :
    R.IsLawfulBelow X (q ∘ Set.inclusion (D.below_mono hXY)) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp h).comap (IsLowerEmbedding.inclusion_below D hXY))

/-- A labelling lawful below a pair lying above every cell is a lawful section. -/
theorem isLawful {r : D.below X → Label.{u}} (h : R.IsLawfulBelow X r)
    (hX : ∀ d, d ∈ D.below X) : R.IsLawful fun d ↦ r ⟨d, hX d⟩ := by
  exact (isLawfulBelow_iff.mp h).comap
    (IsLowerEmbedding.reindex_symm D (Equiv.subtypeUnivEquiv hX))

end IsLawfulBelow

/-! ### Capping -/

/-- **Capping a labelling lawful below a pair** [Kni26, Lemma 2.5.8]: if the cap `c` is
self-visible at the grade of every cell below `X` whose label is at least `c`, the capped
labelling is lawful below `X`. -/
theorem IsLawfulBelow.min_const {X : Finset α × ℕ} {r : D.below X → Label.{u}}
    (hr : R.IsLawfulBelow X r) {c : Label.{u}}
    (hc : ∀ d : D.below X, c ≤ r d → IsSelfVisible (D.grade d) c) :
    R.IsLawfulBelow X fun d ↦ min (r d) c :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).min_const hc)

/-- **Capping a labelling lawful below a pair at a cap self-visible at its grade**, the special
case of [Kni26, Lemma 2.5.8] at the grade of `X`: a labelling lawful below `X` stays lawful when
capped at a label self-visible at the grade of `X`, such as the cap of a lift to `X`. -/
theorem IsLawfulBelow.min_const_of_isSelfVisible {X : Finset α × ℕ} {r : D.below X → Label.{u}}
    (hr : R.IsLawfulBelow X r) {c : Label.{u}} (hc : IsSelfVisible X.2 c) :
    R.IsLawfulBelow X fun d ↦ min (r d) c :=
  hr.min_const fun d _ ↦ hc.mono d.2.2

/-! ### Consistent rows -/

namespace IsConsistent

/-- Consistent rows are orderly. -/
theorem isOrderly (hR : R.IsConsistent) : R.IsOrderly := fun s t ↦ (hR s).orderly t

/-- Consistency pulls back along lower embeddings. -/
theorem comap (hR : R.IsConsistent) (hφ : E.IsLowerEmbedding D φ) : (R.comap hφ).IsConsistent :=
  fun s ↦ isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp (hR (φ s))).comap (hφ.below s))

/-- The restriction of consistent rows to a face is consistent. -/
theorem restrict [DecidableEq α] (hR : R.IsConsistent) (B : Finset α) :
    (R.restrict B).IsConsistent :=
  hR.comap (IsLowerEmbedding.restrict D B)

end IsConsistent

/-! ### Changing a labelling below a pair -/

/-- A labelling equal to another below a pair is lawful there exactly when the other is. -/
theorem isLawfulBelow_congr {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}
    {X : Finset β × ℕ} {w w' : ι → Label.{u}} (h : ∀ d ∈ D.below X, w d = w' d) :
    R.IsLawfulBelow X (fun d : D.below X ↦ w d) ↔
      R.IsLawfulBelow X (fun d : D.below X ↦ w' d) := by
  have : (fun d : D.below X ↦ w d) = fun d : D.below X ↦ w' d := funext fun d ↦ h d d.2
  rw [this]

/-- **Extension by bottom above a grade.**  A labelling lawful below `(B, k)`, replaced by `⊥` at
every cell of grade above `k`, is lawful below `(B, K)` for every `K`: the new cells of the lower
set carry `⊥`, their targets are `⊥`, and they are available to every cell. -/
theorem isLawfulBelow_extendAbove {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}
    {B : Finset β} {k K : ℕ} {w : ι → Label.{u}} (hw : R.IsLawfulBelow (B, k) fun d ↦ w d) :
    R.IsLawfulBelow (B, K) fun d ↦ if D.grade d ≤ k then w d else ⊥ := by
  have hmem {d : ι} (hd : d ∈ D.below (B, K)) (h : D.grade d ≤ k) : d ∈ D.below (B, k) :=
    ⟨hd.1, h⟩
  refine isLawfulBelow_iff.mpr ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- The grade of a cell of the scheme of cells below `(B, K)` is its grade in `D`.
    change IsSelfVisible (D.grade d.1) (if D.grade d.1 ≤ k then w d.1 else ⊥)
    split_ifs with h
    · exact hw.orderly ⟨d.1, hmem d.2 h⟩
    · exact isSelfVisible_bot _
  · by_cases h : D.grade s.1 ≤ k
    · have hs : s.1 ∈ D.below (B, k) := hmem s.2 h
      have hl : TransformsTo (fun d : D.below (D.gradedIndex s.1) ↦ D.grade d) (R.row s.1)
          (fun d ↦ min (if D.grade d.1 ≤ k then w d.1 else ⊥)
            (if D.grade s.1 ≤ k then w s.1 else ⊥)) := by
        have he : (fun d : D.below (D.gradedIndex s.1) ↦
            min (if D.grade d.1 ≤ k then w d.1 else ⊥) (if D.grade s.1 ≤ k then w s.1 else ⊥)) =
            fun d ↦ min (w d.1) (w s.1) := by
          funext d
          have hd : D.grade d.1 ≤ k := d.2.2.trans h
          rw [ite_eq_left hd, ite_eq_left h]
        rw [he]
        exact (hw.locality ⟨s.1, hs⟩).reindex fun d : D.below (D.gradedIndex s.1) ↦
          ⟨⟨d.1, (le_trans d.2 hs : D.gradedIndex d.1 ≤ (B, k))⟩, d.2⟩
      exact hl.reindex (D' := (D.reindex ((↑) : D.below (B, K) → ι)).below
        ((D.reindex ((↑) : D.below (B, K) → ι)).gradedIndex s)) fun t ↦ ⟨t.1.1, t.2⟩
    · simp only [ite_eq_right h, min_bot_right]
      exact TransformsTo.bot _ _
  · by_cases h : D.grade t.1 ≤ k
    · obtain ⟨u, hu, hle⟩ := hw.availability ⟨s.1, hmem s.2 (hg ▸ h)⟩ ⟨t.1, hmem t.2 h⟩ hst hg
      -- Graded indices in the scheme of cells below `(B, k)` are those of `D`.
      change D.gradedIndex u.1 = D.gradedIndex t.1 at hu
      refine ⟨⟨u.1, (hu ▸ t.2 : D.gradedIndex u.1 ≤ (B, K))⟩, hu, ?_⟩
      have hu' : D.grade u.1 ≤ k := (congrArg Prod.snd hu).trans_le h
      -- The labelling at `s` and `u`, unfolded.
      change (if D.grade s.1 ≤ k then w s.1 else ⊥) ≤ (if D.grade u.1 ≤ k then w u.1 else ⊥)
      rw [ite_eq_left (hg ▸ h), ite_eq_left hu']
      exact hle
    · refine ⟨t, rfl, ?_⟩
      rw [ite_eq_right (hg ▸ h)]
      exact bot_le

/-! ### The bottom rows -/

variable (D) in
/-- The **bottom** rows: every row is constantly bottom [Kni26, §4.2]. -/
def bot : D.Rows.{u} := ⟨fun _ _ ↦ ⊥⟩

/-- A value of a bottom row. -/
@[simp] theorem bot_row (s : ι) (t : D.below (D.gradedIndex s)) : (bot D).row s t = ⊥ := rfl

/-- The bottom rows pull back to the bottom rows. -/
@[simp] theorem comap_bot (hφ : E.IsLowerEmbedding D φ) : (bot D).comap hφ = bot E := rfl

/-- The lawful sections of the bottom rows: only the bottom labelling. -/
@[simp] theorem isLawful_bot_iff {p : ι → Label.{u}} : (bot D).IsLawful p ↔ p = fun _ ↦ ⊥ := by
  refine ⟨fun h ↦ funext fun s ↦ h.eq_bot_of_row_self_eq_bot s rfl, ?_⟩
  rintro rfl
  exact isLawful_const_bot

/-- Below every pair, the only labelling lawful for the bottom rows is the bottom labelling. -/
@[simp] theorem isLawfulBelow_bot_iff {X : Finset α × ℕ} {r : D.below X → Label.{u}} :
    (bot D).IsLawfulBelow X r ↔ r = fun _ ↦ ⊥ := by
  rw [isLawfulBelow_iff, comap_bot, isLawful_bot_iff]

/-- The bottom rows are consistent. -/
theorem isConsistent_bot : (bot D : D.Rows.{u}).IsConsistent := fun _ ↦ isLawfulBelow_const_bot _

end Rows

end VaughtConjecture.CellScheme

namespace VaughtConjecture

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

end VaughtConjecture

namespace VaughtConjecture.CellScheme.Rows.IsLawful

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {G C : ι} {P : Set ι}
  {w q : ι → Label.{u}}

/-- **A labelling that keeps a cell drops only whole blocks of its row.**  Let `q` be lawful and
not `⊥` at a cell `C`, and let `x`, `y` be cells below `C` such that the row of `C` reads `x` at
`μ + i` (`μ` zero or a limit) and `y` at most at `μ + j`, so at most the end of the block of `x`.
If `q` is `⊥` at `x`, it is `⊥` at `y`.  The witness `(g, σ)` of locality at `C` has `g ≠ ⊥` at
the grades below `C` (it bounds `q C`), so `σ (μ + i) = ⊥`; by the commutation law, whose guard
holds at `⊥`, `σ` sends the whole block `[μ, μ + ω)`, and so everything below its end, to `⊥`.
With `y = C` this is `ne_bot_of_row_mem_block`. -/
theorem eq_bot_of_row_le_block (hq : R.IsLawful q) {x y : ι}
    (hx : x ∈ D.below (D.gradedIndex C)) (hy : y ∈ D.below (D.gradedIndex C))
    {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {i j : ℕ}
    (hrx : R.row C ⟨x, hx⟩ = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hry : R.row C ⟨y, hy⟩ ≤ ((μ + j : Ordinal.{u}) : Label.{u})) (hC : q C ≠ ⊥)
    (hqx : q x = ⊥) : q y = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := hq.locality C
  have hCC : min (q C) (q C) = min (σ (R.row C ⟨C, D.mem_below_gradedIndex C⟩))
      (g (D.grade C)) := heq ⟨C, D.mem_below_gradedIndex C⟩
  rw [min_self] at hCC
  have hg : g (D.grade x) ≠ ⊥ := by
    have hle : g (D.grade C) ≤ g (D.grade x) := hw.antitone ((D.mem_below).mp hx).2
    intro h0
    exact hC (le_bot_iff.mp (hCC ▸ (min_le_right _ _).trans (hle.trans_eq h0)))
  have hσ : σ ((μ + i : Ordinal.{u}) : Label.{u}) = ⊥ := by
    have hxC : min (q x) (q C) = min (σ ((μ + i : Ordinal.{u}) : Label.{u}))
        (g (D.grade x)) := by
      rw [← hrx]; exact heq ⟨x, hx⟩
    rw [hqx, min_eq_left bot_le] at hxC
    exact (min_eq_bot.mp hxC.symm).resolve_right hg
  have hvr := visibilityReplace_coe_add_natCast (n := max i j + 1) hμ
    (show i < max i j + 1 by omega) j
  have hcomm := hw.visibilityReplace_comm ((μ + i : Ordinal.{u}) : Label.{u}) (max i j + 1)
    (by rw [hσ]; exact bot_le) j (by omega)
  rw [hvr, hσ, visibilityReplace_bot] at hcomm
  have hσy : σ (R.row C ⟨y, hy⟩) = ⊥ := le_bot_iff.mp (hcomm ▸ hw.monotone hry)
  have hyC : min (q y) (q C) = min (σ (R.row C ⟨y, hy⟩)) (g (D.grade y)) := heq ⟨y, hy⟩
  rw [hσy, min_eq_left bot_le] at hyC
  exact (min_eq_bot.mp hyC).resolve_right hC

/-- **A dropped cell is read below the block of the keeping cell.**  If `q` is lawful, not `⊥` at
a cell `C`, and `⊥` at a cell `x` that the row of `C` reads at `μ + i` (`μ` zero or a limit), then
the row of `C` reads `C` itself above the whole block `[μ, μ + ω)` (`eq_bot_of_row_le_block` with
`y = C`).  So, of the cells that the row of `C` reads at ordinals, a lawful labelling that keeps
`C` drops only cells read in a block strictly below the block of its reading of `C`; a cell read
as `⊥` has no block. -/
theorem lt_row_self_of_eq_bot (hq : R.IsLawful q) {x : ι} (hx : x ∈ D.below (D.gradedIndex C))
    {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {i : ℕ}
    (hrx : R.row C ⟨x, hx⟩ = ((μ + i : Ordinal.{u}) : Label.{u})) (hC : q C ≠ ⊥)
    (hqx : q x = ⊥) (j : ℕ) :
    ((μ + j : Ordinal.{u}) : Label.{u}) < R.row C ⟨C, D.mem_below_gradedIndex C⟩ :=
  lt_of_not_ge fun h ↦
    hC (hq.eq_bot_of_row_le_block hx (D.mem_below_gradedIndex C) hμ hrx h hC hqx)

/-- **A cap that reads an anchor in its own block keeps it.**  If the row of `C` reads a cell `z`
below it and `C` itself in one block `[μ, μ + ω)` (`μ` zero or a limit), then a lawful labelling
that is not `⊥` at `C` is not `⊥` at `z`: a shifter sending the reading `μ + i` of `z` to `⊥`
sends `vr_k(μ + i, i') = μ + i'` (for `k > i`) to `vr_k(⊥, i') = ⊥`, the guard of the commutation
law holding at `⊥`, and `μ + i'` is the reading of `C` (`eq_bot_of_row_le_block` with `y = C`). -/
theorem ne_bot_of_row_mem_block (hq : R.IsLawful q) {z : ι} (hz : z ∈ D.below (D.gradedIndex C))
    {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {i i' : ℕ}
    (hrz : R.row C ⟨z, hz⟩ = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hrC : R.row C ⟨C, D.mem_below_gradedIndex C⟩ = ((μ + i' : Ordinal.{u}) : Label.{u}))
    (hC : q C ≠ ⊥) : q z ≠ ⊥ :=
  fun hqz ↦ hC (hq.eq_bot_of_row_le_block hz (D.mem_below_gradedIndex C) hμ hrz hrC.le hC hqz)

end VaughtConjecture.CellScheme.Rows.IsLawful

/-! ### Lawfulness below a pair, pointwise -/

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- A cell below a cell below `X` is below `X`. -/
theorem mem_below_of_le {X : Finset α × ℕ} {d s : ι}
    (hd : D.gradedIndex d ≤ D.gradedIndex s) (hs : s ∈ D.below X) : d ∈ D.below X :=
  (le_trans hd hs : D.gradedIndex d ≤ X)

/-- A cell whose scope lies in that of a cell below `X`, at the same grade, is below `X`. -/
theorem mem_below_of_scope_subset {X : Finset α × ℕ} {s t : ι}
    (hst : D.scope s ⊆ D.scope t) (hg : D.grade s = D.grade t) (ht : t ∈ D.below X) :
    s ∈ D.below X :=
  mem_below_of_le ((D.gradedIndex_le_iff).mpr ⟨hst, hg.le⟩) ht

/-- **Lawfulness below a pair, pointwise.**  A labelling `w` of all cells is lawful below `X`
exactly when every cell below `X` has a label self-visible at its grade, the row of every cell
`s` below `X` transforms to `d ↦ min (w d) (w s)` on the cells below `s`, and availability holds
for every target cell below `X`. -/
theorem isLawfulBelow_iff_forall {X : Finset α × ℕ} {w : ι → Label.{u}} :
    R.IsLawfulBelow X (fun d ↦ w d) ↔
      (∀ d ∈ D.below X, IsSelfVisible (D.grade d) (w d)) ∧
      (∀ s ∈ D.below X, TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (w d) (w s))) ∧
      (∀ s t, t ∈ D.below X → D.scope s ⊆ D.scope t → D.grade s = D.grade t →
        ∃ u, D.gradedIndex u = D.gradedIndex t ∧ w s ≤ w u) := by
  constructor
  · intro h
    refine ⟨fun d hd ↦ h.orderly ⟨d, hd⟩, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · exact (h.locality ⟨s, hs⟩).reindex fun d : D.below (D.gradedIndex s) ↦
        ⟨⟨d.1, mem_below_of_le d.2 hs⟩, d.2⟩
    · obtain ⟨u, hu, hle⟩ :=
        h.availability ⟨s, mem_below_of_scope_subset hst hg ht⟩ ⟨t, ht⟩ hst hg
      exact ⟨u, hu, hle⟩
  · rintro ⟨ho, hl, ha⟩
    refine ⟨fun d ↦ ho d d.2, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
    · exact (hl s s.2).reindex (D' := (D.reindex ((↑) : D.below X → ι)).below
        ((D.reindex ((↑) : D.below X → ι)).gradedIndex s)) fun t ↦ ⟨t.1.1, t.2⟩
    · obtain ⟨u, hu, hle⟩ := ha s t t.2 hst hg
      exact ⟨⟨u, mem_below_of_le hu.le t.2⟩, hu, hle⟩

end VaughtConjecture.CellScheme.Rows

/-! ### Reading at a top, separating lifts, and ties of rows -/

namespace VaughtConjecture.CellScheme.Rows.IsLawful

open Finset Label

variable {ι κ : Type*} {D : CellScheme ι κ} {R : D.Rows.{u}} {p q : ι → Label.{u}}

/-- **A cell read at least as a top by a top is a top**: in a lawful section `p`, if a cell `u`
and a cell `s` below it are labelled `⊤`, and the row of `u` reads a cell `x` below `u` at least
as `s`, then `x` is labelled `⊤`.  Locality at `u` has a suppressor that is `⊤` at the grade of
`u` (since `p u = ⊤`), hence at the grade of `x`, and a shifter sending the entry at `s` to `⊤`
(since `p s = ⊤`), hence also the entry at `x`.  No condition on the grade of `s` is needed. -/
theorem eq_top_of_row_le (h : R.IsLawful p) {u s x : ι} (hs : s ∈ D.below (D.gradedIndex u))
    (hx : x ∈ D.below (D.gradedIndex u)) (hpu : p u = ⊤) (hps : p s = ⊤)
    (hrow : R.row u ⟨s, hs⟩ ≤ R.row u ⟨x, hx⟩) : p x = ⊤ := by
  obtain ⟨g, σ, hw, heq⟩ := h.locality u
  have hu := heq ⟨u, D.mem_below_gradedIndex u⟩
  have hs' := heq ⟨s, hs⟩
  have hx' := heq ⟨x, hx⟩
  -- the labelling of locality at `u` is `d ↦ min (p d) (p u)`
  change min (p u) (p u) = min (σ (R.row u ⟨u, _⟩)) (g (D.grade u)) at hu
  change min (p s) (p u) = min (σ (R.row u ⟨s, hs⟩)) (g (D.grade s)) at hs'
  change min (p x) (p u) = min (σ (R.row u ⟨x, hx⟩)) (g (D.grade x)) at hx'
  rw [hpu, min_self] at hu
  rw [hps, hpu, min_self] at hs'
  rw [hpu, min_top_right] at hx'
  have hgu : g (D.grade u) = ⊤ := (min_eq_top.mp hu.symm).2
  have hσs : σ (R.row u ⟨s, hs⟩) = ⊤ := (min_eq_top.mp hs'.symm).1
  have hgx : g (D.grade x) = ⊤ := top_le_iff.mp (hgu ▸ hw.antitone hx.2)
  have hσx : σ (R.row u ⟨x, hx⟩) = ⊤ := top_le_iff.mp (hσs ▸ hw.monotone hrow)
  rw [hx', hσx, hgx, min_self]

/-- **A separating lift forces a top reading the marker above `x`.**  Let `q` be lawful, `u` a cell
labelled `⊤` whose row reads `r` at most as `x`, with `r` of the grade of `u`, `x` of grade at most
that of `r`, and `r` labelled `⊤`.  If a labelling `w` lawful below the graded index of `u` agrees
with the row of `u` capped at its value at `r` and has `w x < w r`, then some cell `v` of the
graded index of `u` is labelled `⊤` in `q` and its row reads `x` strictly below `r`. -/
theorem exists_top_row_lt (hq : R.IsLawful q) {u x r : ι}
    (hx : x ∈ D.below (D.gradedIndex u)) (hr : r ∈ D.below (D.gradedIndex u))
    (hgr : D.grade r = D.grade u) (hgx : D.grade x ≤ D.grade r) (hqu : q u = ⊤) (hqr : q r = ⊤)
    (hread : R.row u ⟨r, hr⟩ ≤ R.row u ⟨x, hx⟩) {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow (D.gradedIndex u) fun d ↦ w d)
    (hcap : ∀ y (hy : y ∈ D.below (D.gradedIndex u)),
      min (w y) (R.row u ⟨r, hr⟩) = min (R.row u ⟨y, hy⟩) (R.row u ⟨r, hr⟩))
    (hlt : w x < w r) :
    ∃ v, ∃ hxv : x ∈ D.below (D.gradedIndex v), ∃ hrv : r ∈ D.below (D.gradedIndex v),
      D.gradedIndex v = D.gradedIndex u ∧ q v = ⊤ ∧ R.row v ⟨x, hxv⟩ < R.row v ⟨r, hrv⟩ := by
  obtain ⟨-, hloc, havail⟩ := isLawfulBelow_iff_forall.mp hw
  obtain ⟨v, hv, hwv⟩ := havail r u (D.mem_below_gradedIndex u) hr.1 hgr
  set τ := R.row u ⟨r, hr⟩
  have hvu : v ∈ D.below (D.gradedIndex u) := by rw [CellScheme.mem_below, hv]
  -- the separating labelling is at least `τ` at `x`, hence above `τ` at `v`
  have hxτ : τ ≤ w x := by
    have h := hcap x hx
    rw [min_eq_right hread] at h
    exact min_eq_right_iff.mp h
  have hvτ : τ ≤ R.row u ⟨v, hvu⟩ := by
    have h := hcap v hvu
    rw [min_eq_right (hxτ.trans (hlt.le.trans hwv))] at h
    exact min_eq_right_iff.mp h.symm
  have hqv : q v = ⊤ := hq.eq_top_of_row_le hr hvu hqu hqr hvτ
  have hxv : x ∈ D.below (D.gradedIndex v) := by rw [hv]; exact hx
  have hrv : r ∈ D.below (D.gradedIndex v) := by rw [hv]; exact hr
  refine ⟨v, hxv, hrv, hv, hqv, lt_of_not_ge fun hle ↦ ?_⟩
  -- locality of `w` at `v` is monotone in the row and antitone in the grade
  have h := (hloc v hvu).le_of_le (d := ⟨r, hrv⟩) (d' := ⟨x, hxv⟩) hle hgx
  change min (w r) (w v) ≤ min (w x) (w v) at h
  rw [min_eq_left hwv, min_eq_left (hlt.le.trans hwv)] at h
  exact absurd hlt (not_lt.mpr h)

/-- **A cell read by its own row at most as a cell of no larger grade is labelled at most as it.**
If the row of `r` reads `r` at most as a cell `y` below `r` of grade at most that of `r`, then every
labelling lawful below a pair above `r` labels `r` at most as `y`: locality at `r` is monotone in
the row and antitone in the grade.  So such a `y` ties `r` from above in every lawful labelling.
It extends `CellScheme.Rows.IsLawful.le_of_row_self_le` (a cell of the same graded index) to cells
of lower grade and to lawfulness below a pair. -/
theorem le_of_row_self_le_below {X : Finset κ × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {r y : ι} (hrX : r ∈ D.below X)
    (hy : y ∈ D.below (D.gradedIndex r)) (hgy : D.grade y ≤ D.grade r)
    (hrow : R.row r ⟨r, D.mem_below_gradedIndex r⟩ ≤ R.row r ⟨y, hy⟩) : w r ≤ w y := by
  have h := ((isLawfulBelow_iff_forall.mp hw).2.1 r hrX).le_of_le
    (d := ⟨r, D.mem_below_gradedIndex r⟩) (d' := ⟨y, hy⟩) hrow hgy
  -- locality at `r` reads `min (w d) (w r)`
  change min (w r) (w r) ≤ min (w y) (w r) at h
  rw [min_self] at h
  exact h.trans (min_le_left _ _)

end VaughtConjecture.CellScheme.Rows.IsLawful

namespace VaughtConjecture.CellScheme.Rows.IsLawfulBelow

open Finset Label

variable {ι κ : Type*} {D : CellScheme ι κ} {R : D.Rows.{u}}

/-- **Raising an isolated cell to `⊤`.**  Let `w` be lawful below `X` and `r` a cell below `X` that
is the only cell below `X` at or above its graded index, whose row reads every other cell below it
as `⊥` and itself not as `⊥`.  If `w r ≠ ⊥`, the labelling `w` with `r` sent to `⊤` is lawful below
`X`. -/
theorem update_top [DecidableEq ι] {X : Finset κ × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {r : ι} (hrX : r ∈ D.below X)
    (huniq : ∀ y ∈ D.below X, D.gradedIndex r ≤ D.gradedIndex y → y = r)
    (hrow : ∀ y (hy : y ∈ D.below (D.gradedIndex r)), y ≠ r → R.row r ⟨y, hy⟩ = ⊥)
    (hrr : R.row r ⟨r, D.mem_below_gradedIndex r⟩ ≠ ⊥) (hwr : w r ≠ ⊥) :
    R.IsLawfulBelow X fun d ↦ Function.update w r ⊤ d := by
  obtain ⟨hvis, hloc, havail⟩ := isLawfulBelow_iff_forall.mp hw
  have hle (d : ι) : w d ≤ Function.update w r ⊤ d := by
    by_cases hd : d = r
    · subst hd; rw [Function.update_self]; exact le_top
    · rw [Function.update_of_ne hd]
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hdr : d = r
    · subst hdr; rw [Function.update_self]; exact isSelfVisible_top _
    · rw [Function.update_of_ne hdr]; exact hvis d hd
  · by_cases hsr : s = r
    · subst hsr
      refine transformsTo_of_eq_bot_iff _ (K := D.grade s) (fun d ↦ d.2.2) (isSelfVisible_top _)
        _ _ fun d ↦ ?_
      rw [Function.update_self, min_top_right]
      by_cases hds : (d : ι) = s
      · have hd : d = ⟨s, D.mem_below_gradedIndex s⟩ := Subtype.ext hds
        subst hd
        rw [Function.update_self, ite_eq_right hrr]
      · rw [Function.update_of_ne hds, ite_eq_left (hrow d d.2 hds)]
        -- the given labelling is `⊥` at `d`: locality at `s` reads `d` as `⊥`
        have h := (hloc s hs).eq_bot (d := d) (hrow d d.2 hds)
        change min (w d) (w s) = ⊥ at h
        exact (min_eq_bot.mp h).resolve_right hwr
    · -- no cell below `s` is `r`, so the labelling below `s` is unchanged
      have hrs (d : D.below (D.gradedIndex s)) : (d : ι) ≠ r := fun hdr ↦
        hsr (huniq s hs (hdr ▸ d.2))
      have heq : (fun d : D.below (D.gradedIndex s) ↦
          min (Function.update w r ⊤ d) (Function.update w r ⊤ s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s) := funext fun d ↦ by
        rw [Function.update_of_ne (hrs d), Function.update_of_ne hsr]
      rw [heq]
      exact hloc s hs
  · by_cases hsr : s = r
    · subst hsr
      have hts : t = s := huniq t ht ⟨hst, hg.le⟩
      exact ⟨s, hts ▸ rfl, by rw [Function.update_self]⟩
    · obtain ⟨u, hu, hsu⟩ := havail s t ht hst hg
      exact ⟨u, hu, by rw [Function.update_of_ne hsr]; exact hsu.trans (hle u)⟩

/-- **Reading rows tie every lawful labelling.**  Let every cell `v` of graded index `Y` read `r`
at most as `x`, where `r` lies below `Y` with the grade of `Y` and `x` lies below `Y` with grade at
most that of `r`.  Given a cell `t` of graded index `Y`, every labelling lawful below `Y` labels `r`
at most as `x`. -/
theorem le_of_forall_reads {Y : Finset κ × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow Y fun d ↦ w d) {r x t : ι} (hr : r ∈ D.below Y) (hx : x ∈ D.below Y)
    (ht : D.gradedIndex t = Y) (hgr : D.grade r = D.grade t) (hgx : D.grade x ≤ D.grade r)
    (hreads : ∀ v (hv : D.gradedIndex v = Y), R.row v ⟨r, hv ▸ hr⟩ ≤ R.row v ⟨x, hv ▸ hx⟩) :
    w r ≤ w x := by
  obtain ⟨-, hloc, havail⟩ := isLawfulBelow_iff_forall.mp hw
  have htY : t ∈ D.below Y := by rw [CellScheme.mem_below, ht]
  have hst : D.scope t = Y.1 := congrArg Prod.fst ht
  obtain ⟨v, hv, hle⟩ := havail r t htY (by rw [hst]; exact hr.1) hgr
  have hvY : D.gradedIndex v = Y := hv.trans ht
  have hvb : v ∈ D.below Y := by rw [CellScheme.mem_below, hvY]
  have h := (hloc v hvb).le_of_le (d := ⟨r, hvY ▸ hr⟩) (d' := ⟨x, hvY ▸ hx⟩) (hreads v hvY) hgx
  -- locality at `v` reads `min (w d) (w v)`
  change min (w r) (w v) ≤ min (w x) (w v) at h
  rw [min_eq_left hle] at h
  exact h.trans (min_le_left _ _)

end VaughtConjecture.CellScheme.Rows.IsLawfulBelow

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Extension.Apex

/-!
# Source-gap contexts: residual acquisition, and separated top supports

Roadmap, Layer 3 ((R2) of the table of 3.4: exact residual receiving, reduced in
`VaughtConjecture.Continuation.ExactReceiving` to residual acquisition and cutoff determination
for a predicate on acquired contexts) and Layer 4 (the residual comparison); semantic contract,
item 8.

**Source-gap contexts.**  Let `t'` be a stage type on `k` points and `h : Fin n ↪ Fin k` the
embedding of a root.  `t'` is a **source-gap context of grade `K` along `h`**
(`StageType.IsSourceGapContext`) when there are a point `l` outside the range of `h` (the **lost
point**), a cell `o` (the **owner**) and a cell `r` (the **lost top**) with:

* the top grade of `t'` (`StageType.topGrade`, the largest grade of a cell labelled `⊤`) is `K`;
* the owner has full scope, grade `K`, and label `⊤`;
* the lost top has label `⊤`, and its scope contains `l`;
* (**strict source gaps**) the row of the owner at the lost top, replaced at `K`
  (`Label.visibilityReplace K K`), lies strictly below the row of the owner at the owner, and at
  every cell labelled `⊤` whose scope avoids `l` (the **retained** top cells).

Rows are read through `Scheme.rowAt` (the row of a cell at a cell below it, `⊥` elsewhere); every
top cell lies below the owner, since its grade is at most the top grade.  The cells visible through
`h` avoid `l`, so the top cells of the root are retained.  This predicate is defined in this
repository.  The owner and the lost top form a private gap in the sense of the LOW construction
of 3.3 (`roadmap/README.md`: a cell `c` of grade `K` and a cell `r` below it with
`visibilityReplace K K (E_c r) < E_c c`, the row above the replaced value at the root tops), with
the lost point, the full scope of the owner, and the gap at every retained top cell made
explicit.

**Residual acquisition** (compiled in this repository,
`Realization.residualAcquisition_isSourceGapContext`), with no hypothesis beyond those of
`Realization.ResidualAcquisition` (a model at a limit stage, no cover that is a globally rigid
core, top-grade supremum `K`); the acquired context is on `k + 1` points with the lost point last
and the root along the initial segment (`Realization.exists_covers_isSourceGapContextAt`):

* `K > 0`, since at top-grade supremum `0` the empty tuple is a globally rigid core
  (`Realization.IsModel.isGloballyRigidCore_empty_iff`);
* the **tail** is an occurrence `x₀` above which (in the inclusion order of supports) every
  occurrence has top grade `K` (`Realization.exists_forall_le_topGrade_eq`); covering gives an
  occurrence `z` above it containing the cover, hence a top cell of grade `K` in its type
  (`StageType.exists_grade_eq_topGrade`);
* `z` is not a globally rigid core: some cover `x` of a stage type `Q` along `e₀` has an admissible
  top support `H` (`StageType.IsAdmissibleTopSupport`) containing the top cells visible through
  `e₀` and missing a top cell; `Q` has top grade `K` (the tail again);
* **first loss** (`StageType.exists_firstLoss`, stage types only): a closed face `B` above the
  range of `e₀` of largest size on which `H` contains every top cell, and a point `p` with
  `insert p B` closed (accessibility of plans, `Geometry.IsPlan.exists_insert_mem`); some top cell
  `r ∉ H` has scope in `insert p B` containing `p`;
* **the owner** (`StageType.exists_owner`): the top cell of grade `K` visible through `e₀` is in
  `H`, and completeness of `Q` with availability of the lawful section witnessing `H` gives a cell
  of `H` with graded index `(insert p B, K)`;
* **the gaps**: in the lawful section `τ` witnessing `H` (`τ = ⊤` exactly on `H`,
  `StageType.IsAdmissibleTopSupport.exists_isLawful`), the witness of locality at the owner has
  suppressor `⊤` up to grade `K` and shifter sending the row at a cell of `H` to `⊤` and the row
  at `r` to `τ r ≠ ⊤`; monotonicity and the commutation of the shifter with visibility replacement
  give `visibilityReplace K K (row o r) < row o a`
  (`CellScheme.Rows.IsLawful.visibilityReplace_row_lt`); restricted to the face on
  `insert p B`, enumerated with `p` last, these are the gaps.

The last four steps concern stage types only and use no model
(`StageType.exists_isSourceGapContextAt_comap`).

**The coatom off the lost point is closed.**  In the acquired context the lost point is the last
point `p` and the first coatom (the complement of `p`) is the face `B` of first loss, which is
closed.  A **source-gap context with the coatom off the lost point closed**
(`StageType.IsSourceGapContextOff`) is a source-gap context at a lost point `l` whose complement
`univ.erase l` is a closed face; its residual acquisition is compiled
(`Realization.residualAcquisition_isSourceGapContextOff`).  A **source-gap context with the lost
point last** (`StageType.IsSourceGapContextLast`) is a source-gap context whose lost point is the
last point; it is the form at which the coatom form of determination is asked in
`VaughtConjecture.MainTheorem.SourceGapLastRoute`.  Both imply `StageType.IsSourceGapContext`
(`StageType.IsSourceGapContextOff.isSourceGapContext`,
`StageType.IsSourceGapContextLast.isSourceGapContext`).  A source-gap context of grade `K` has top
grade `K` (`StageType.IsSourceGapContext.topGrade_eq`), so every face of one, the first coatom in
particular, has top grade at most `K`
(`StageType.IsSourceGapContext.topGrade_le_of_restrictFace`).

**Determination is open.**  Cutoff determination for source-gap contexts
(`Realization.CutoffDetermination`) is not attempted here.  With it and (R1) for every model at
every limit stage, (R2) follows
(`Realization.residualReceiving_of_cutoffDetermination_isSourceGapContext`, compiled in this
repository, with determination a hypothesis).  Nothing here proves (R2).

**Non-vacuity: legal source-gap types exist.**  If no legal stage type were a source-gap context,
(R2) would hold outright: the compiled acquisition leaves no model at a limit stage with no cover
that is a globally rigid core and with natural top-grade supremum
(`Realization.residualReceiving_of_forall_not_isSourceGapContext`, a valid conditional theorem).
Its hypothesis is false: a legal source-gap stage type exists at every stage
(`GatedExtensionCounterexample.isSourceGapContext_P`,
`Realization.not_forall_not_isSourceGapContext`, in
`VaughtConjecture.Continuation.SourceGapContextInstance`), so the vacuity argument for (R2) is
ruled out.  That is existence of a finite stage type; that such a type occurs as the type of a
cover in a residual model is not proved here, and (R2) and determination stay open.  No stage type
built with `StageType.addApex` is a source-gap context
(`StageType.not_isSourceGapContext_addApex`): the owner must be the apex, whose row is the coded
copy of the labels and reads every top cell at the code of `⊤`, so the gap at the owner fails
(`Label.le_visibilityReplace`).

**Separated top supports.**  An admissible top support is defined through a lawful section (a
legal relabelling that is `⊤` exactly on the support).  A **separated top support**
(`StageType.IsSeparatedTopSupport`) is stated through the rows instead: it consists of top cells,
is available within itself (a cell of the support has a cell of the support at every graded index
with larger scope and the same grade), and is source-separated (below every cell `o` of the
support, the row at a top cell outside it, replaced at the grade of `o`, lies strictly below the
row at every cell of the support).  Every admissible top support is separated
(`StageType.IsAdmissibleTopSupport.isSeparatedTopSupport`, compiled in this repository).  So
rigidity of a core for separated supports gives rigidity
(`StageType.IsSeparatedRigidCoreIn.isRigidCoreIn`),
a globally rigid core for separated supports is a globally rigid core
(`Realization.IsGloballySeparatedRigidCore.isGloballyRigidCore`), and the residual hypothesis
stated with admissible supports gives it stated with separated ones
(`Realization.not_exists_isGloballySeparatedRigidCore`).  This is the direction a first-loss
argument on separated supports uses.  The converse, that a separated support is admissible (the
uniform lowering off the support is lawful), is not formalized here.

**The compiled determination counterexamples are excluded.**  Determination fails for the
predicate that is always true over a top-free root along the identity
(`StageType.not_isDeterminedWithin_receivingFamily_of_isTopFree`,
`StageType.not_isDeterminedWithin_saturationFamily_of_isTopFree`), at the empty root of the apex
point `ExactReceivingExamples.apexPoint`.  A source-gap context is not top-free (its owner is
labelled `⊤`, `StageType.not_isSourceGapContext_of_isTopFree`) and its root map is not surjective
(`StageType.not_isSourceGapContext_of_surjective`), so neither the general obstruction nor the apex
instance is a source-gap context (`VaughtConjecture.Continuation.SourceGapContextExamples`).  This
says nothing about determination for source-gap contexts.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### A lost top read below a surviving owner -/

namespace CellScheme.Rows.IsLawful

variable {ι β : Type*} {D : CellScheme ι β} {R : D.Rows} {τ : ι → Label.{u}}

/-- **A lost top is read strictly below a surviving top**: in a lawful section `τ` with `τ o = ⊤`,
if a cell `r` below `o` has `τ r ≠ ⊤` and a cell `a` below `o` has `τ a = ⊤`, then the row of `o`
at `r`, replaced at the grade of `o`, lies strictly below the row of `o` at `a`.  The witness of
locality at `o` has suppressor `⊤` up to the grade of `o`, sends the row at `a` to `⊤` and the row
at `r` to `τ r`; its shifter is monotone and commutes with visibility replacement there. -/
theorem visibilityReplace_row_lt (hτ : R.IsLawful τ) {o : ι} (ho : τ o = ⊤)
    {r a : D.below (D.gradedIndex o)} (hr : τ r ≠ ⊤) (ha : τ a = ⊤) :
    visibilityReplace (D.grade o) (D.grade o) (R.row o r) < R.row o a := by
  obtain ⟨g, σ, hw, heq⟩ := hτ.locality o
  -- below `o`, the target of locality is `τ` itself, since `τ o = ⊤`
  have hq (d : D.below (D.gradedIndex o)) : τ d = min (σ (R.row o d)) (g (D.grade d)) := by
    have := heq d
    simp only [ho, min_top_right] at this
    exact this
  have hgo : g (D.grade o) = ⊤ :=
    (min_eq_top.mp ((hq ⟨o, D.mem_below_gradedIndex o⟩).symm.trans ho)).2
  have hσa : σ (R.row o a) = ⊤ := (min_eq_top.mp ((hq a).symm.trans ha)).1
  have hgr : g (D.grade r) = ⊤ := top_le_iff.mp (hgo.symm.le.trans (hw.antitone r.2.2))
  have hσr : σ (R.row o r) = τ r := by rw [hq r, hgr, min_top_right]
  have hcomm := hw.visibilityReplace_comm (R.row o r) (D.grade o) (by rw [hgo]; exact le_top)
    (D.grade o) le_rfl
  refine lt_of_not_ge fun hle ↦ hr ?_
  have h := hw.monotone hle
  rwa [hσa, hcomm, hσr, top_le_iff, visibilityReplace_eq_top_iff] at h

end CellScheme.Rows.IsLawful

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {τ : Fin S.card → Label.{u}}

/-- **A lost top is read strictly below a surviving top**, through `rowAt`: the form of
`CellScheme.Rows.IsLawful.visibilityReplace_row_lt` for cells of a scheme on `n` points. -/
theorem visibilityReplace_rowAt_lt (hτ : S.rows.IsLawful τ) {o r a : Fin S.card} (ho : τ o = ⊤)
    (hr : τ r ≠ ⊤) (ha : τ a = ⊤)
    (hrb : r ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex o))
    (hab : a ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex o)) :
    visibilityReplace (S.toCellScheme.grade o) (S.toCellScheme.grade o) (S.rowAt o r) <
      S.rowAt o a := by
  rw [rowAt_of_mem hrb, rowAt_of_mem hab]
  exact hτ.visibilityReplace_row_lt (r := ⟨r, hrb⟩) (a := ⟨a, hab⟩) ho hr ha

end Scheme

/-! ### Separated top supports -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ} {t : StageType.{u} α n}

/-- An admissible top support is the top set of a lawful section of the rows of `t`. -/
theorem IsAdmissibleTopSupport.exists_isLawful {H : Set (Fin t.card)}
    (h : t.IsAdmissibleTopSupport H) :
    ∃ τ : Fin t.card → Label.{u}, t.rows.IsLawful τ ∧ ∀ d, τ d = ⊤ ↔ d ∈ H := by
  obtain ⟨t', _, hs, h'⟩ := h
  obtain ⟨S, p, _, _, hp, _⟩ := t'
  -- the scheme of the witness is the scheme of `t`
  change S = t.toScheme at hs
  subst hs
  exact ⟨p, hp, fun d ↦ (h' d d rfl).2.1⟩

variable (t) in
/-- A set `H` of cells of `t` is a **separated top support** when it consists of top cells and:

* (availability) a cell of `H` has a cell of `H` at every graded index with a larger scope and the
  same grade;
* (source separation) below every cell `o` of `H`, the row of `o` at every top cell `r` not in
  `H`, replaced at the grade of `o` (`Label.visibilityReplace`), lies strictly below the row of
  `o` at every cell `a` of `H` (the cell `o` itself included).

It is a necessary condition for admissibility (`IsAdmissibleTopSupport.isSeparatedTopSupport`),
stated through the rows, with no lawful section quantified.  The acquisition below works with
admissible supports directly; this form and its rigid cores are kept to record the direction of
the comparison between the two forms of top support. -/
structure IsSeparatedTopSupport (H : Set (Fin t.card)) : Prop where
  /-- The support consists of top cells. -/
  subset : H ⊆ {d | t.label d = ⊤}
  /-- Availability within the support. -/
  available (d : Fin t.card) : d ∈ H → ∀ w : Fin t.card,
    t.toCellScheme.scope d ⊆ t.toCellScheme.scope w →
      t.toCellScheme.grade d = t.toCellScheme.grade w →
        ∃ u, t.toCellScheme.gradedIndex u = t.toCellScheme.gradedIndex w ∧ u ∈ H
  /-- Source separation below every cell of the support. -/
  separated (o : Fin t.card) : o ∈ H →
    ∀ a r : t.toCellScheme.below (t.toCellScheme.gradedIndex o), a.1 ∈ H → t.label r = ⊤ →
      r.1 ∉ H → visibilityReplace (t.toCellScheme.grade o) (t.toCellScheme.grade o)
        (t.rows.row o r) < t.rows.row o a

/-- **An admissible top support is separated**: availability is that of the witnessing lawful
section, and source separation is `CellScheme.Rows.IsLawful.visibilityReplace_row_lt` at its
locality. -/
theorem IsAdmissibleTopSupport.isSeparatedTopSupport {H : Set (Fin t.card)}
    (h : t.IsAdmissibleTopSupport H) : t.IsSeparatedTopSupport H := by
  obtain ⟨τ, hτ, hτH⟩ := h.exists_isLawful
  refine ⟨h.subset, fun d hd w hsc hg ↦ ?_, fun o ho a r ha _ hr ↦ ?_⟩
  · obtain ⟨u, hu, hle⟩ := hτ.availability d w hsc hg
    exact ⟨u, hu, (hτH u).mp (top_le_iff.mp (((hτH d).mpr hd).symm.le.trans hle))⟩
  · exact hτ.visibilityReplace_row_lt ((hτH o).mpr ho) (mt (hτH r).mp hr) ((hτH a).mpr ha)

variable (t) in
/-- The core along `e` is **rigid for separated supports** in `t` when every separated top support
containing the top cells visible through `e` contains every top cell. -/
def IsSeparatedRigidCoreIn (e : Fin k ↪ Fin n) : Prop :=
  ∀ H : Set (Fin t.card), t.IsSeparatedTopSupport H →
    (∀ d ∈ t.visibleCells e, t.label d = ⊤ → d ∈ H) → ∀ d, t.label d = ⊤ → d ∈ H

/-- **Rigidity for separated supports gives rigidity**: every admissible top support is separated
(`IsAdmissibleTopSupport.isSeparatedTopSupport`). -/
theorem IsSeparatedRigidCoreIn.isRigidCoreIn {e : Fin k ↪ Fin n} (h : t.IsSeparatedRigidCoreIn e) :
    t.IsRigidCoreIn e :=
  fun H hH hcore ↦ h H hH.isSeparatedTopSupport hcore

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {k : ℕ}

variable (R) in
/-- A tuple `c` is a **globally rigid core for separated supports** of `R` when, for every cover
`x` of a stage type `t` in `R` and every face embedding `e` with `x ∘ e = c`, the core along `e`
is rigid for separated supports in `t`. -/
def IsGloballySeparatedRigidCore (c : Fin k → M) : Prop :=
  ∀ ⦃m : ℕ⦄ (t : StageType.{u} α m) (x : Fin m → M) (e : Fin k ↪ Fin m), R.Covers t x →
    x ∘ e = c → t.IsSeparatedRigidCoreIn e

/-- A globally rigid core for separated supports is a globally rigid core. -/
theorem IsGloballySeparatedRigidCore.isGloballyRigidCore {c : Fin k → M}
    (h : R.IsGloballySeparatedRigidCore c) : R.IsGloballyRigidCore c :=
  fun _ t x e hx hxe ↦ (h t x e hx hxe).isRigidCoreIn

/-- **No globally rigid core, hence none for separated supports**: the residual hypothesis of
(R2), stated with admissible top supports, gives the same hypothesis stated with separated
ones. -/
theorem not_exists_isGloballySeparatedRigidCore
    (h : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c) :
    ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballySeparatedRigidCore c :=
  fun ⟨k, p, c, hc, hcore⟩ ↦ h ⟨k, p, c, hc, hcore.isGloballyRigidCore⟩

end Realization

/-! ### Source-gap contexts -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- The source-gap clauses of `t'` along `h` at the lost point `l`, the owner `o`, and the lost
top `r` (see `IsSourceGapContext`). -/
structure IsSourceGapContextAt (K : ℕ) (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (l : Fin k)
    (o r : Fin t'.card) : Prop where
  /-- The lost point is not a point of the root. -/
  notMem_range : l ∉ Set.range h
  /-- The top grade of the context is `K`. -/
  topGrade_eq : t'.topGrade = K
  /-- The owner has full scope. -/
  scope_owner : t'.toCellScheme.scope o = univ
  /-- The owner has grade `K`. -/
  grade_owner : t'.toCellScheme.grade o = K
  /-- The owner is labelled `⊤`. -/
  label_owner : t'.label o = ⊤
  /-- The lost top is labelled `⊤`. -/
  label_lost : t'.label r = ⊤
  /-- The lost top contains the lost point. -/
  mem_scope_lost : l ∈ t'.toCellScheme.scope r
  /-- The strict source gap at the owner. -/
  gap_owner : visibilityReplace K K (t'.rowAt o r) < t'.rowAt o o
  /-- The strict source gap at every top cell avoiding the lost point. -/
  gap_retained (a : Fin t'.card) : t'.label a = ⊤ → l ∉ t'.toCellScheme.scope a →
    visibilityReplace K K (t'.rowAt o r) < t'.rowAt o a

/-- A **source-gap context** of grade `K`: a stage type `t'` on `k` points with an embedding `h` of
a root, a **lost point** `l` outside the root, an **owner** `o`, and a **lost top** `r`, such that
the top grade of `t'` is `K`; the owner has full scope and grade `K` and is labelled `⊤`; the lost
top is labelled `⊤` and its scope contains `l`; and the row of the owner at the lost top, replaced
at `K` (`Label.visibilityReplace K K`), lies strictly below the row of the owner at the owner and
at every top cell whose scope avoids `l` (the **strict source gaps**).  The rows are read through
`Scheme.rowAt`.  The cells of `t'` visible through `h` avoid `l`, so the gaps hold at the top
cells of the root.  Defined in this repository; residual acquisition is compiled
(`Realization.residualAcquisition_isSourceGapContext`), with the lost point the last of `k + 1`
points; determination is open. -/
def IsSourceGapContext (K : ℕ) (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ (l : Fin k) (o r : Fin t'.card), t'.IsSourceGapContextAt K h l o r

namespace IsSourceGapContextAt

variable {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {l : Fin k} {o r : Fin t'.card}

/-- A source-gap context is not top-free: its owner is labelled `⊤`. -/
theorem not_isTopFree (hs : t'.IsSourceGapContextAt K h l o r) : ¬ t'.IsTopFree :=
  fun ht ↦ ht o hs.label_owner

/-- The root of a source-gap context misses a point: the lost point. -/
theorem not_surjective (hs : t'.IsSourceGapContextAt K h l o r) : ¬ Function.Surjective h :=
  fun hh ↦ hs.notMem_range (hh l)

end IsSourceGapContextAt

/-- **A top-free type is not a source-gap context.** -/
theorem not_isSourceGapContext_of_isTopFree {K : ℕ} {t' : StageType.{u} α k}
    (ht : t'.IsTopFree) (h : Fin n ↪ Fin k) : ¬ t'.IsSourceGapContext K h :=
  fun ⟨_, _, _, hs⟩ ↦ hs.not_isTopFree ht

/-- **No source-gap context along a surjective root**, the identity in particular. -/
theorem not_isSourceGapContext_of_surjective {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (hh : Function.Surjective h) : ¬ t'.IsSourceGapContext K h :=
  fun ⟨_, _, _, hs⟩ ↦ hs.not_surjective hh

/-- A **source-gap context with the coatom off the lost point closed**: a source-gap context of
grade `K` along `h` at a lost point `l` (`IsSourceGapContextAt`) such that the complement
`univ.erase l` of the lost point is a closed face of `t'`; equivalently, the lost point is an
extreme point of the plan of `t'` (`StageType.erase_mem_faces_iff_mem_extremes`, by
`Geometry.mem_extremes`).  Residual acquisition is compiled
(`Realization.residualAcquisition_isSourceGapContextOff`); cutoff determination follows from the
compiled bounded coatom form with the lost point last
(`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff` applied
to `Realization.boundedCoatomCutoffDetermination_sourceGapLast`, in
`VaughtConjecture.MainTheorem.LowPaddedRoute`). -/
def IsSourceGapContextOff (K : ℕ) (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ (l : Fin k) (o r : Fin t'.card), t'.IsSourceGapContextAt K h l o r ∧
    univ.erase l ∈ t'.toCellScheme.faces

/-- **The coatom off a point is closed exactly when the point is extreme**: `univ.erase l` is a
closed face of `t'` if and only if `l` is an extreme point of the plan of `t'` (`Geometry.extremes`,
`StageType.isPlan`). -/
theorem erase_mem_faces_iff_mem_extremes {t' : StageType.{u} α k} {l : Fin k} :
    univ.erase l ∈ t'.toCellScheme.faces ↔ l ∈ Geometry.extremes t'.toCellScheme.faces univ := by
  simp [Geometry.mem_extremes]

/-- A **source-gap context with the lost point last**: a source-gap context of grade `K` along `h`
at a lost point `l` (`IsSourceGapContextAt`) that is the last of the `k` points. -/
def IsSourceGapContextLast (K : ℕ) (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ (l : Fin k) (o r : Fin t'.card), (l : ℕ) + 1 = k ∧ t'.IsSourceGapContextAt K h l o r

/-- A source-gap context with the coatom off the lost point closed is a source-gap context. -/
theorem IsSourceGapContextOff.isSourceGapContext {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (hs : t'.IsSourceGapContextOff K h) : t'.IsSourceGapContext K h :=
  let ⟨l, o, r, hs, _⟩ := hs
  ⟨l, o, r, hs⟩

/-- A source-gap context with the lost point last is a source-gap context. -/
theorem IsSourceGapContextLast.isSourceGapContext {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (hs : t'.IsSourceGapContextLast K h) : t'.IsSourceGapContext K h :=
  let ⟨l, o, r, _, hs⟩ := hs
  ⟨l, o, r, hs⟩

/-- A source-gap context of grade `K` has top grade `K`. -/
theorem IsSourceGapContext.topGrade_eq {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (hs : t'.IsSourceGapContext K h) : t'.topGrade = K :=
  let ⟨_, _, _, hs⟩ := hs
  hs.topGrade_eq

/-- A source-gap context of grade `K` with the lost point last has top grade `K`. -/
theorem IsSourceGapContextLast.topGrade_eq {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (hs : t'.IsSourceGapContextLast K h) : t'.topGrade = K :=
  hs.isSourceGapContext.topGrade_eq

/-- **The faces of a source-gap context of grade `K` have top grade at most `K`**, the first
coatom in particular. -/
theorem IsSourceGapContext.topGrade_le_of_restrictFace {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (hs : t'.IsSourceGapContext K h) {f : Fin m ↪ Fin k}
    {p : StageType.{u} α m} (hp : restrictFace f t' = some p) : p.topGrade ≤ K :=
  (StageType.topGrade_le_of_restrictFace hp).trans hs.topGrade_eq.le

/-! ### First loss -/

/-- A top grade that is positive is the grade of a top cell. -/
theorem exists_grade_eq_topGrade {t : StageType.{u} α n} (h : 0 < t.topGrade) :
    ∃ d, t.label d = ⊤ ∧ t.toCellScheme.grade d = t.topGrade := by
  unfold topGrade at h ⊢
  set s := ({d | t.label d = ⊤} : Finset (Fin t.card)) with hs
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, sup_empty] at h
    exact absurd h (lt_irrefl 0)
  · obtain ⟨d, hd, hd'⟩ := exists_mem_eq_sup s hne t.toCellScheme.grade
    exact ⟨d, by simpa [hs] using hd, hd'.symm⟩

/-- **First loss.**  Let `H` contain every top cell of `Q` whose scope lies in a closed face `G`,
and miss some top cell.  Then there are a closed face `B ⊇ G` on which `H` contains every top cell
and a point `p ∉ B` with `insert p B` closed, such that some top cell `r` not in `H` has scope in
`insert p B` and containing `p`.  `B` is a closed face of largest size above `G` on which `H` is
full, and `p` extends it by accessibility of plans (`Geometry.IsPlan.exists_insert_mem`). -/
theorem exists_firstLoss {Q : StageType.{u} α m} {H : Set (Fin Q.card)} {G : Finset (Fin m)}
    (hG : G ∈ Q.toCellScheme.faces)
    (hfull : ∀ d, Q.toCellScheme.scope d ⊆ G → Q.label d = ⊤ → d ∈ H)
    (hloss : ∃ d, Q.label d = ⊤ ∧ d ∉ H) :
    ∃ (B : Finset (Fin m)) (p : Fin m), B ∈ Q.toCellScheme.faces ∧ G ⊆ B ∧ p ∉ B ∧
      insert p B ∈ Q.toCellScheme.faces ∧
      (∀ d, Q.toCellScheme.scope d ⊆ B → Q.label d = ⊤ → d ∈ H) ∧
      ∃ r, Q.label r = ⊤ ∧ r ∉ H ∧ Q.toCellScheme.scope r ⊆ insert p B ∧
        p ∈ Q.toCellScheme.scope r := by
  classical
  obtain ⟨B, hB, hmax⟩ := exists_max_image
    {B ∈ Q.toCellScheme.faces | G ⊆ B ∧
      ∀ d, Q.toCellScheme.scope d ⊆ B → Q.label d = ⊤ → d ∈ H} card
    ⟨G, mem_filter.mpr ⟨hG, Subset.rfl, hfull⟩⟩
  obtain ⟨hBf, hGB, hBfull⟩ := mem_filter.mp hB
  have hne : B ≠ univ := by
    rintro rfl
    obtain ⟨d, hd, hdH⟩ := hloss
    exact hdH (hBfull d (subset_univ _) hd)
  obtain ⟨p, hp, hpB⟩ := Q.isPlan.exists_insert_mem hBf hne
  have hnot : ¬ ∀ d, Q.toCellScheme.scope d ⊆ insert p B → Q.label d = ⊤ → d ∈ H := by
    intro hfull'
    have := hmax _ (mem_filter.mpr ⟨hpB, hGB.trans (subset_insert _ _), hfull'⟩)
    rw [card_insert_of_notMem hp] at this
    omega
  push Not at hnot
  obtain ⟨r, hrs, hr, hrH⟩ := hnot
  refine ⟨B, p, hBf, hGB, hp, hpB, hBfull, r, hr, hrH, hrs, ?_⟩
  by_contra hpr
  exact hrH (hBfull r ((subset_insert_iff_of_notMem hpr).mp hrs) hr)

/-- **An owner by availability**: in a legal `Q` with a lawful section `τ`, a cell `s` with
`τ s = ⊤` and scope inside a closed face `F` gives a cell `o` of graded index `(F, grade s)` with
`τ o = ⊤` (completeness, then availability of `τ`). -/
theorem exists_owner {Q : StageType.{u} α m} (hQ : Q.IsLegal) {τ : Fin Q.card → Label.{u}}
    (hτ : Q.rows.IsLawful τ) {F : Finset (Fin m)} (hF : F ∈ Q.toCellScheme.faces)
    {s : Fin Q.card} (hs : τ s = ⊤) (hsF : Q.toCellScheme.scope s ⊆ F) :
    ∃ o, Q.toCellScheme.gradedIndex o = (F, Q.toCellScheme.grade s) ∧ τ o = ⊤ := by
  have hwf := Q.isWellFormed.isWellFormed
  obtain ⟨w, hw⟩ := hQ.isComplete (F, Q.toCellScheme.grade s)
    ⟨hF, hwf.grade_pos s, (hwf.grade_le_card s).trans (card_le_card hsF)⟩
  have hwF : Q.toCellScheme.scope w = F := congrArg Prod.fst hw
  obtain ⟨u, hu, hle⟩ := hτ.availability s w (hwF ▸ hsF) (congrArg Prod.snd hw).symm
  exact ⟨u, hu.trans hw, top_le_iff.mp (hs.symm.le.trans hle)⟩

/-- A tuple whose values are among the values of `φ` factors through `φ` along an embedding. -/
private theorem exists_embedding_comp_eq {β : Type*} {c : Fin n → β} (hc : Function.Injective c)
    {φ : Fin k → β} (h : ∀ i, ∃ j, φ j = c i) : ∃ e : Fin n ↪ Fin k, φ ∘ e = c := by
  choose j hj using h
  exact ⟨⟨j, fun a b hab ↦ hc (by rw [← hj a, ← hj b, hab])⟩, funext hj⟩

/-- **A source-gap context from a proper admissible top support** (stage types only, no model):
let `Q` be legal of top grade `K`, let `H` be an admissible top support of `Q` containing every top
cell with scope in a closed face `G` and missing some top cell, and let a top cell `s₀` of grade
`K` have scope in `G`.  Then every injective `g` with values in `G` factors as
`ι ∘ Fin.castSucc ∘ e` through an enumeration `ι` of a closed face, and the face of `Q` along `ι`
is a source-gap context of grade `K` along `e` followed by the initial segment, with the last
point lost; the image under `ι` of its first coatom, `univ.map (Fin.castSuccEmb.trans ι)`, is a
closed face of `Q`.

First loss (`exists_firstLoss`) gives a closed `B ⊇ G` and `p`; `ι` enumerates `insert p B` with
`p` last, so the first coatom is `B`; the owner is the cell of `H` of graded index
`(insert p B, K)` (`exists_owner`, from `s₀`); the gaps are
`CellScheme.Rows.IsLawful.visibilityReplace_row_lt` for the lawful section witnessing `H`,
restricted to the face. -/
theorem exists_isSourceGapContextAt_comap {Q : StageType.{u} α m} (hQ : Q.IsLegal) {K : ℕ}
    (hQK : Q.topGrade = K) {H : Set (Fin Q.card)} (hH : Q.IsAdmissibleTopSupport H)
    {G : Finset (Fin m)} (hG : G ∈ Q.toCellScheme.faces)
    (hfull : ∀ d, Q.toCellScheme.scope d ⊆ G → Q.label d = ⊤ → d ∈ H)
    (hloss : ∃ d, Q.label d = ⊤ ∧ d ∉ H) {s₀ : Fin Q.card} (hs₀ : Q.label s₀ = ⊤)
    (hs₀K : Q.toCellScheme.grade s₀ = K) (hs₀G : Q.toCellScheme.scope s₀ ⊆ G) {g : Fin n → Fin m}
    (hg : Function.Injective g) (hgG : ∀ i, g i ∈ G) :
    ∃ (k : ℕ) (ι : Fin (k + 1) ↪ Fin m) (hι : univ.map ι ∈ Q.toCellScheme.faces)
      (e : Fin n ↪ Fin k), (∀ i, ι (e i).castSucc = g i) ∧
        univ.map (Fin.castSuccEmb.trans ι) ∈ Q.toCellScheme.faces ∧
        ∃ o r,
          (Q.comap ι hι).IsSourceGapContextAt K (e.trans Fin.castSuccEmb) (Fin.last k) o r := by
  classical
  -- the lawful section witnessing `H`
  obtain ⟨τ, hτ, hτH⟩ := hH.exists_isLawful
  -- first loss and the owner
  obtain ⟨B, p, hBf, hGB, hpB, hF, hBfull, r, hr, hrH, hrF, hpr⟩ :=
    exists_firstLoss hG hfull hloss
  obtain ⟨o, ho, hoτ⟩ := exists_owner hQ hτ hF ((hτH s₀).mpr (hfull s₀ hs₀G hs₀))
    (hs₀G.trans (hGB.trans (subset_insert _ _)))
  rw [hs₀K] at ho
  -- the enumeration `ι` of `insert p B` with `p` last
  set k := #B
  let φ : Fin k → Fin m := fun i ↦ B.orderEmbOfFin rfl i
  have hφ : Function.Injective φ := (B.orderEmbOfFin rfl).injective
  have hφr : Set.range φ = B := by simp [φ]
  let ι : Fin (k + 1) ↪ Fin m :=
    ⟨Fin.snoc φ p, Fin.snoc_injective_of_injective hφ (by rw [hφr]; exact hpB)⟩
  have hιc (i : Fin k) : ι i.castSucc = φ i := Fin.snoc_castSucc (α := fun _ ↦ Fin m) _ _ _
  have hιl : ι (Fin.last k) = p := Fin.snoc_last (α := fun _ ↦ Fin m) _ _
  have hιF : univ.map ι = insert p B := by
    ext y
    simp only [mem_map, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last => exact Or.inl hιl
      | cast i =>
        refine Or.inr ?_
        rw [hιc, ← mem_coe, ← hφr]
        exact Set.mem_range_self i
    · rintro (rfl | hy)
      · exact ⟨Fin.last k, hιl⟩
      · obtain ⟨i, rfl⟩ : y ∈ Set.range φ := hφr ▸ hy
        exact ⟨i.castSucc, hιc i⟩
  have hF' : univ.map ι ∈ Q.toCellScheme.faces := hιF ▸ hF
  set t' := Q.comap ι hF'
  have hι : restrictFace ι Q = some t' := restrictFace_of_mem _ _ hF'
  -- the root embedding `e`
  obtain ⟨e, he⟩ := exists_embedding_comp_eq hg (φ := φ) fun i ↦ by
    obtain ⟨j, hj⟩ : g i ∈ Set.range φ := hφr ▸ hGB (hgG i)
    exact ⟨j, hj⟩
  -- the first coatom of the face is `B`, closed
  have hBι : univ.map (Fin.castSuccEmb.trans ι) = B := by
    ext y
    simp only [mem_map, mem_univ, true_and, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hιc, ← mem_coe, ← hφr]
      exact Set.mem_range_self i
    · intro hy
      obtain ⟨i, rfl⟩ : y ∈ Set.range φ := hφr ▸ hy
      exact ⟨i, hιc i⟩
  refine ⟨k, ι, hF', e, fun i ↦ (hιc (e i)).trans (congrFun he i), hBι ▸ hBf, ?_⟩
  -- the cells of `t'`
  have hvis {d : Fin Q.card} (hd : Q.toCellScheme.scope d ⊆ insert p B) :
      ∃ d', faceCell hι d' = d :=
    Q.toScheme.exists_faceCell_eq _ (Scheme.mem_visibleCells.mpr fun y hy ↦ by
      obtain ⟨i, -, hi⟩ := mem_map.mp (hιF ▸ hd hy)
      exact ⟨i, hi⟩)
  have hoF : Q.toCellScheme.scope o = insert p B := congrArg Prod.fst ho
  have hoK : Q.toCellScheme.grade o = K := congrArg Prod.snd ho
  obtain ⟨o', rfl⟩ := hvis hoF.le
  obtain ⟨r', rfl⟩ := hvis hrF
  have hscope_o : t'.toCellScheme.scope o' = univ := by
    refine map_injective ι ?_
    rw [← scope_faceCell hι, hoF, hιF]
  have hgrade_o : t'.toCellScheme.grade o' = K := (grade_faceCell hι o').symm.trans hoK
  have hlabel_o : t'.label o' = ⊤ :=
    (label_faceCell hι o').symm.trans (hH.subset ((hτH _).mp hoτ))
  have htopK : t'.topGrade = K := le_antisymm (hQK ▸ topGrade_le_of_restrictFace hι)
    (hgrade_o ▸ grade_le_topGrade hlabel_o)
  -- every top cell of `t'` lies below the owner
  have hbelow {a : Fin t'.card} (ha : t'.label a = ⊤) :
      a ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o') :=
    (CellScheme.gradedIndex_le_iff _).mpr
      ⟨(CellScheme.gradedIndex_fst _ ▸ hscope_o ▸ subset_univ _ :),
        (CellScheme.gradedIndex_snd _ ▸ hgrade_o ▸ htopK ▸ grade_le_topGrade ha :)⟩
  have hlabel_r : t'.label r' = ⊤ := (label_faceCell hι r').symm.trans hr
  -- the lawful section witnessing `H`, on the face
  have hτ' := isLawful_comp_faceCell hι hτ
  have hgap {a : Fin t'.card} (ha : t'.label a = ⊤) (haτ : τ (faceCell hι a) = ⊤) :
      visibilityReplace K K (t'.rowAt o' r') < t'.rowAt o' a := by
    have := Scheme.visibilityReplace_rowAt_lt hτ' hoτ (mt (hτH _).mp hrH) haτ (hbelow hlabel_r)
      (hbelow ha)
    rwa [hgrade_o] at this
  refine ⟨o', r', ⟨fun ⟨i, hi⟩ ↦ ?_, htopK, hscope_o, hgrade_o, hlabel_o, hlabel_r, ?_,
    hgap hlabel_o hoτ, fun a ha hla ↦ hgap ha ?_⟩⟩
  · -- the root avoids the last point
    exact (Fin.castSucc_lt_last (e i)).ne hi
  · -- the lost top contains the last point
    rw [scope_faceCell hι, mem_map] at hpr
    obtain ⟨y, hy, hyp⟩ := hpr
    obtain rfl : y = Fin.last k := ι.injective (hyp.trans hιl.symm)
    exact hy
  · -- a top cell avoiding the last point is visible in `B`, so in `H`
    refine (hτH _).mpr (hBfull _ ?_ ((label_faceCell hι a).trans ha))
    rw [scope_faceCell hι]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr fun h ↦ hla (h ▸ hy')
    rw [hιc, ← mem_coe, ← hφr]
    exact Set.mem_range_self i

/-! ### Types with an apex are not source-gap contexts -/

/-- **No type with an apex added is a source-gap context** (`addApex`), at any grade and along any
root.  The owner has grade at least the grade `n` of the apex (the top grade), so it is the apex
(`eq_of_grade_addApex`); the row of the apex is the coded copy of the labels (`apexRow`), which
reads every top cell, the apex included, at the code of `⊤`; so the gap at the owner would make a
label strictly larger than its own replacement at `K ≤ n`, against `le_visibilityReplace`. -/
theorem not_isSourceGapContext_addApex {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
    (hn : 0 < n) (K : ℕ) (h : Fin k ↪ Fin n) : ¬ (t.addApex ht hn).IsSourceGapContext K h := by
  rintro ⟨l, o, r, hs⟩
  have hgi : (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _) = (univ, n) :=
    Scheme.appendFullCellScheme_gradedIndex_last _ _
  have hlast : (t.addApex ht hn).toCellScheme.grade (Fin.last _) = n := congrArg Prod.snd hgi
  have hgo : (t.addApex ht hn).toCellScheme.grade o = n := by
    refine le_antisymm ((t.addApex ht hn).grade_le o) ?_
    have := grade_le_topGrade (addApex_label_last ht hn)
    rw [hlast, hs.topGrade_eq] at this
    rw [hs.grade_owner]
    exact this
  obtain rfl := eq_of_grade_addApex ht hn hgo
  have key (x : Fin (t.addApex ht hn).card) (hx : (t.addApex ht hn).label x = ⊤) :
      (t.addApex ht hn).rowAt (Fin.last _) x = apexRow ht (Fin.last _) := by
    have hb : x ∈ (t.addApex ht hn).toCellScheme.below
        ((t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _)) := by
      rw [CellScheme.mem_below, hgi, CellScheme.gradedIndex_le_iff]
      exact ⟨subset_univ _, (t.addApex ht hn).grade_le x⟩
    rw [Scheme.rowAt_of_mem hb]
    -- the rows of `t.addApex` are those of `appendFullCell`
    change (t.toScheme.appendFullCell n (apexRow ht) ht.not_le).rows.row (Fin.last _) ⟨x, hb⟩ = _
    rw [Scheme.appendFullCell_row_last]
    -- the cells of `t.addApex` are the cells of `t` and the apex
    change Fin (t.card + 1) at x
    induction x using Fin.lastCases with
    | last => rfl
    | cast d =>
      rw [addApex_label_castSucc] at hx
      rw [apexRow_castSucc, hx, apexRow_last]
  have hgap := hs.gap_owner
  rw [key r hs.label_lost, key _ hs.label_owner] at hgap
  exact (le_visibilityReplace (by omega) _).not_gt hgap

end StageType

/-! ### Residual acquisition -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n : ℕ}

/-- **Residual acquisition of a source-gap context**, in the form with the lost point last: in a
model at a limit stage with no cover that is a globally rigid core and with top-grade supremum
`K`, every cover `c` of a stage type `t` extends to a cover `c'` of a stage type `t'` on `k + 1`
points along `e` followed by the initial segment, and `t'` is a source-gap context of grade `K`
along it with the last point lost, and the first coatom of `t'` (the complement of the lost point)
is a closed face.

The **tail** is an occurrence `x₀` above which (in the inclusion order of supports) every
occurrence has top grade `K` (`exists_forall_le_topGrade_eq`).  Covering gives an occurrence `z`
above `x₀` containing `c`, of top grade `K`, with a top cell of grade `K` (`K > 0`, since otherwise
the empty tuple is a globally rigid core).  As `z` is not a globally rigid core, a cover `x` of a
stage type `Q` along `e₀` has an admissible top support `H` containing the top cells visible
through `e₀` and missing a top cell, and `Q` has top grade `K` (it lies above the tail).  The rest
is `StageType.exists_isSourceGapContextAt_comap` with `G` the range of `e₀`. -/
theorem exists_covers_isSourceGapContextAt (hα : Order.IsSuccLimit α) (hR : R.IsModel)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) :
    ∃ (k : ℕ) (t' : StageType.{u} α (k + 1)) (c' : Fin (k + 1) → M) (e : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ (e.trans Fin.castSuccEmb) = c ∧
        univ.map Fin.castSuccEmb ∈ t'.toCellScheme.faces ∧
        ∃ o r, t'.IsSourceGapContextAt K (e.trans Fin.castSuccEmb) (Fin.last k) o r := by
  classical
  -- the eventual top grade is positive: otherwise the empty tuple is a globally rigid core
  have hKpos : 0 < K := by
    refine Nat.pos_of_ne_zero fun hK0 ↦ hcore ?_
    obtain ⟨p, hp⟩ := hR.exists_covers_zero
    exact ⟨0, p, ![], hp, (hR.isGloballyRigidCore_empty_iff hα).mpr (by rw [hK, hK0]; rfl)⟩
  -- the tail, and an occurrence `z` above it containing the points of `c`
  obtain ⟨x₀, hx₀⟩ := exists_forall_le_topGrade_eq hR.isConsistent hR.isCovering hK
  obtain ⟨z, hz⟩ := hR.isCovering.exists_subset_support (univ.image c ∪ x₀.support)
  have hzK : z.type.topGrade = K := hx₀ z (subset_union_right.trans hz)
  -- `z` is not a globally rigid core
  have hnr : ¬ R.IsGloballyRigidCore z.tuple :=
    fun h ↦ hcore ⟨_, _, _, covers_of_eval _ z.eval_tuple, h⟩
  simp only [IsGloballyRigidCore, StageType.IsRigidCoreIn] at hnr
  push Not at hnr
  obtain ⟨m, Q, x, e₀, hx, hxe, H, hH, hcoreH, d₀, hd₀, hd₀H⟩ := hnr
  -- the occurrence of `x` lies above `z`, so `Q` has top grade `K`
  let y : R.Occurrence := ⟨m, ⟨x, hx.injective⟩, Q, hx.eval_eq⟩
  have hzy : z ≤ y := by
    intro a ha
    obtain ⟨j, rfl⟩ := (Occurrence.mem_support _).mp ha
    exact (Occurrence.mem_support _).mpr ⟨e₀ j, congrFun hxe j⟩
  have hQK : Q.topGrade = K := hx₀ y ((subset_union_right.trans hz).trans hzy)
  -- the face of `Q` along `e₀` is the type of `z`
  have hface : StageType.restrictFace e₀ Q = some z.type := by
    have he : e₀.trans ⟨x, hx.injective⟩ = z.tuple := Function.Embedding.ext fun j ↦ congrFun hxe j
    rw [← hR.isConsistent _ Q e₀ hx.eval_eq, he, z.eval_tuple]
  have hG : univ.map e₀ ∈ Q.toCellScheme.faces := ((StageType.restrictFace_eq_some_iff _ _).mp
    hface).1
  have hfull (d : Fin Q.card) (hd : Q.toCellScheme.scope d ⊆ univ.map e₀) (hdt : Q.label d = ⊤) :
      d ∈ H :=
    hcoreH d (mem_filter.mpr ⟨mem_univ _, hd⟩) hdt
  -- a top cell `s` of grade `K` of the type of `z`, visible through `e₀` in `Q`
  obtain ⟨s, hs, hsK⟩ := StageType.exists_grade_eq_topGrade (t := z.type) (hzK ▸ hKpos)
  have hsG : Q.toCellScheme.scope (StageType.faceCell hface s) ⊆ univ.map e₀ := by
    rw [StageType.scope_faceCell]
    exact map_subset_map.mpr (subset_univ _)
  -- the positions `g` of `c` in `x`, inside the range of `e₀`
  have hpos (i : Fin n) : ∃ j₀, x (e₀ j₀) = c i := by
    obtain ⟨j₀, hj₀⟩ := (Occurrence.mem_support _).mp
      (hz (mem_union_left _ (mem_image_of_mem c (mem_univ i))))
    exact ⟨j₀, (congrFun hxe j₀).trans hj₀⟩
  obtain ⟨g, hg⟩ := StageType.exists_embedding_comp_eq hc.injective (φ := x) fun i ↦
    let ⟨j₀, hj₀⟩ := hpos i
    ⟨e₀ j₀, hj₀⟩
  have hgG (i : Fin n) : g i ∈ univ.map e₀ := by
    obtain ⟨j₀, hj₀⟩ := hpos i
    exact mem_map.mpr ⟨j₀, mem_univ _, hx.injective (hj₀.trans (congrFun hg i).symm)⟩
  obtain ⟨k, ι, hι, e, he, hcf, o, r, hsg⟩ := StageType.exists_isSourceGapContextAt_comap
    (hR.isLegal _ _ hx.eval_eq) hQK hH hG hfull ⟨d₀, hd₀, hd₀H⟩
    ((StageType.label_faceCell hface s).trans hs)
    ((StageType.grade_faceCell hface s).trans (hsK.trans hzK)) hsG g.injective hgG
  refine ⟨k, Q.comap ι hι, x ∘ ι, e, ⟨hx.injective.comp ι.injective, ?_⟩, ?_,
    (StageType.map_univ_mem_comap_faces_iff Q ι Fin.castSuccEmb hι).mpr hcf, o, r, hsg⟩
  · have hxι : (⟨x ∘ ι, hx.injective.comp ι.injective⟩ : Fin (k + 1) ↪ M) =
        ι.trans ⟨x, hx.injective⟩ := Function.Embedding.ext fun _ ↦ rfl
    rw [hxι, hR.isConsistent _ Q ι hx.eval_eq, StageType.restrictFace_of_mem _ _ hι]
  · funext i
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Fin.coe_castSuccEmb, he]
    exact congrFun hg i

/-- **Residual acquisition for source-gap contexts** (`ResidualAcquisition`), with no hypothesis:
the acquired context of `exists_covers_isSourceGapContextAt`. -/
theorem residualAcquisition_isSourceGapContext :
    ResidualAcquisition.{u, w} fun K t' h ↦ t'.IsSourceGapContext K h where
  exists_context _ _ _ _ hα hR hcore hK _ _ _ hc := by
    obtain ⟨k, t', c', e, hc', hcc', -, o, r, hs⟩ :=
      exists_covers_isSourceGapContextAt hα hR hcore hK hc
    exact ⟨k + 1, t', c', _, hc', hcc', Fin.last k, o, r, hs⟩

/-- **Residual acquisition for source-gap contexts with the coatom off the lost point closed**
(`ResidualAcquisition`), with no hypothesis: the acquired context of
`exists_covers_isSourceGapContextAt`, whose first coatom, the complement of the last point, is
closed. -/
theorem residualAcquisition_isSourceGapContextOff :
    ResidualAcquisition.{u, w} fun K t' h ↦ t'.IsSourceGapContextOff K h where
  exists_context _ _ _ _ hα hR hcore hK _ _ _ hc := by
    obtain ⟨k, t', c', e, hc', hcc', hcf, o, r, hs⟩ :=
      exists_covers_isSourceGapContextAt hα hR hcore hK hc
    refine ⟨k + 1, t', c', _, hc', hcc', Fin.last k, o, r, hs, ?_⟩
    rwa [Fin.univ_castSuccEmb, erase_cons]

/-- **(R2) from (R1) and cutoff determination for source-gap contexts**: the reduction
`residualReceiving_of_cutoffDetermination` with the compiled acquisition
`residualAcquisition_isSourceGapContext`.  Cutoff determination for source-gap contexts is open:
it is a hypothesis here, not proved.  (R1) is assumed for every model at every limit stage, as in
the reduction. -/
theorem residualReceiving_of_cutoffDetermination_isSourceGapContext
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hdet : CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h) :
    ResidualReceiving.{u, w} :=
  residualReceiving_of_cutoffDetermination hrec residualAcquisition_isSourceGapContext hdet

/-- **If no legal stage type is a source-gap context, (R2) holds**: the compiled acquisition
leaves no model at a limit stage with no cover that is a globally rigid core and with natural
top-grade supremum, so (R2) holds vacuously.  The hypothesis is false: legal source-gap stage
types exist at every stage (`Realization.not_forall_not_isSourceGapContext`), so this does not
prove (R2); occurrence of such a type in a residual model is not proved. -/
theorem residualReceiving_of_forall_not_isSourceGapContext
    (hvac : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k K : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      t'.IsLegal → ¬ t'.IsSourceGapContext K h) :
    ResidualReceiving.{u, w} where
  exists_covers _ _ R _ hα hR hcore hK _ t c hc _ _ _ := by
    obtain ⟨k, t', c', h, hc', -, hP⟩ :=
      residualAcquisition_isSourceGapContext.exists_context hα hR hcore hK t c hc
    exact absurd hP (hvac t' h (hR.isLegal _ _ hc'.eval_eq))

end Realization

end VaughtConjecture

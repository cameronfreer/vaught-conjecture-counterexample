/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceivingExamples

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
`h` avoid `l`, so the top cells of the root are retained
(`StageType.IsSourceGapContextAt.gap_visible`).  This predicate is defined in this repository; it
transcribes the private-gap context of the residual construction of 3.3, with the lost point and
the owner explicit.

**Residual acquisition** (compiled in this repository,
`Realization.residualAcquisition_isSourceGapContext`), with no hypothesis beyond those of
`Realization.ResidualAcquisition` (a model at a limit stage, no cover that is a globally rigid
core, top-grade supremum `K`); the acquired context is on `k + 1` points with the lost point last
and the root along the initial segment (`Realization.exists_covers_isSourceGapContextAt`):

* `K > 0`, since at top-grade supremum `0` the empty tuple is a globally rigid core
  (`Realization.IsModel.isGloballyRigidCore_empty_iff`);
* the tail (`Realization.exists_forall_le_topGrade_eq`) and covering give an occurrence `z` of top
  grade `K` containing the cover, hence a top cell of grade `K` in its type
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

**Determination is open.**  Cutoff determination for source-gap contexts
(`Realization.CutoffDetermination`) is not attempted here; with it and (R1) for every model at
every limit stage, `Realization.residualReceiving_of_cutoffDetermination` would give (R2).  Nothing
here proves (R2) or any part of it.

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
instance (the example at the end of this file) is a source-gap context.  This says nothing about
determination for source-gap contexts.

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

This is the form of a top support stated through the rows, with no lawful section quantified. -/
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

/-- The grade of a source-gap context is positive. -/
theorem pos (hs : t'.IsSourceGapContextAt K h l o r) : 0 < K :=
  hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o

/-- A source-gap context is not top-free: its owner is labelled `⊤`. -/
theorem not_isTopFree (hs : t'.IsSourceGapContextAt K h l o r) : ¬ t'.IsTopFree :=
  fun ht ↦ ht o hs.label_owner

/-- The root of a source-gap context misses a point: the lost point. -/
theorem not_surjective (hs : t'.IsSourceGapContextAt K h l o r) : ¬ Function.Surjective h :=
  fun hh ↦ hs.notMem_range (hh l)

/-- **The gaps hold at the top cells of the root**: a cell visible through `h` avoids the lost
point. -/
theorem gap_visible (hs : t'.IsSourceGapContextAt K h l o r) {a : Fin t'.card}
    (ha : a ∈ t'.visibleCells h) (hat : t'.label a = ⊤) :
    visibilityReplace K K (t'.rowAt o r) < t'.rowAt o a :=
  hs.gap_retained a hat fun hl ↦ hs.notMem_range (Scheme.mem_visibleCells.mp ha hl)

end IsSourceGapContextAt

/-- A one-point type within the top grade of (R2) lies within the top grade of the context. -/
theorem IsSourceGapContext.topGrade_le {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (hs : t'.IsSourceGapContext K h) {d : StageType.{u} α m} (hd : d.topGrade ≤ K) :
    d.topGrade ≤ t'.topGrade := by
  obtain ⟨l, o, r, hs⟩ := hs
  rw [hs.topGrade_eq]
  exact hd

/-- **A top-free type is not a source-gap context.** -/
theorem not_isSourceGapContext_of_isTopFree {K : ℕ} {t' : StageType.{u} α k}
    (ht : t'.IsTopFree) (h : Fin n ↪ Fin k) : ¬ t'.IsSourceGapContext K h :=
  fun ⟨_, _, _, hs⟩ ↦ hs.not_isTopFree ht

/-- **No source-gap context along a surjective root**, the identity in particular. -/
theorem not_isSourceGapContext_of_surjective {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} (hh : Function.Surjective h) : ¬ t'.IsSourceGapContext K h :=
  fun ⟨_, _, _, hs⟩ ↦ hs.not_surjective hh

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
    ∃ (B : Finset (Fin m)) (p : Fin m), G ⊆ B ∧ p ∉ B ∧ insert p B ∈ Q.toCellScheme.faces ∧
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
  refine ⟨B, p, hGB, hp, hpB, hBfull, r, hr, hrH, hrs, ?_⟩
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

end StageType

/-! ### Residual acquisition -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n : ℕ}

/-- A tuple whose points are among the values of `φ` factors through `φ` along an embedding. -/
private theorem exists_embedding_comp_eq {k : ℕ} {c : Fin n → M} (hc : Function.Injective c)
    {φ : Fin k → M} (h : ∀ i, ∃ j, φ j = c i) : ∃ e : Fin n ↪ Fin k, φ ∘ e = c := by
  choose j hj using h
  exact ⟨⟨j, fun a b hab ↦ hc (by rw [← hj a, ← hj b, hab])⟩, funext hj⟩

/-- **Residual acquisition of a source-gap context**, in the form with the lost point last: in a
model at a limit stage with no cover that is a globally rigid core and with top-grade supremum
`K`, every cover `c` of a stage type `t` extends to a cover `c'` of a stage type `t'` on `k + 1`
points along `e` followed by the initial segment, and `t'` is a source-gap context of grade `K`
along it with the last point lost.

The tail above an occurrence of top grade `K` (`exists_forall_le_topGrade_eq`) and covering give
an occurrence `z` of top grade `K` containing `c`, with a top cell of grade `K` (`K > 0`, since
otherwise the empty tuple is a globally rigid core).  As `z` is not a globally rigid core, a cover
`x` of a stage type `Q` along `e₀` has an admissible top support `H` containing the top cells
visible through `e₀` and missing a top cell.  First loss (`StageType.exists_firstLoss`) gives a
closed face `B` on which `H` is full and a point `p` with `insert p B` closed and a lost top `r`;
the top cell of grade `K` gives an owner in `H` of graded index `(insert p B, K)`
(`StageType.exists_owner`); `t'` is the face of `Q` on `insert p B`, enumerated with `p` last.  The
gaps are `CellScheme.Rows.IsLawful.visibilityReplace_row_lt` for the lawful section witnessing
`H`, restricted to that face. -/
theorem exists_covers_isSourceGapContextAt (hα : Order.IsSuccLimit α) (hR : R.IsModel)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) :
    ∃ (k : ℕ) (t' : StageType.{u} α (k + 1)) (c' : Fin (k + 1) → M) (e : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ (e.trans Fin.castSuccEmb) = c ∧
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
  have hQ : Q.IsLegal := hR.isLegal _ _ hx.eval_eq
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
  -- a top cell `s₀` of grade `K` visible through `e₀`, so in `H`
  obtain ⟨s, hs, hsK⟩ := StageType.exists_grade_eq_topGrade (t := z.type) (hzK ▸ hKpos)
  set s₀ := StageType.faceCell hface s
  have hs₀ : Q.label s₀ = ⊤ := (StageType.label_faceCell hface s).trans hs
  have hs₀K : Q.toCellScheme.grade s₀ = K := (StageType.grade_faceCell hface s).trans
    (hsK.trans hzK)
  have hs₀G : Q.toCellScheme.scope s₀ ⊆ univ.map e₀ := by
    rw [StageType.scope_faceCell]
    exact map_subset_map.mpr (subset_univ _)
  -- the lawful section witnessing `H`
  obtain ⟨τ, hτ, hτH⟩ := hH.exists_isLawful
  -- first loss and the owner
  obtain ⟨B, p, hGB, hpB, hF, hBfull, r, hr, hrH, hrF, hpr⟩ :=
    StageType.exists_firstLoss hG hfull ⟨d₀, hd₀, hd₀H⟩
  obtain ⟨o, ho, hoτ⟩ := StageType.exists_owner hQ hτ hF ((hτH s₀).mpr (hfull s₀ hs₀G hs₀))
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
  have hι : StageType.restrictFace ι Q = some t' := StageType.restrictFace_of_mem _ _ hF'
  -- the root embedding `e`
  obtain ⟨e, he⟩ := exists_embedding_comp_eq (φ := x ∘ φ) hc.injective fun i ↦ by
    obtain ⟨j₀, hj₀⟩ := (Occurrence.mem_support _).mp
      (hz (mem_union_left _ (mem_image_of_mem c (mem_univ i))))
    have hB : e₀ j₀ ∈ B := hGB (mem_map_of_mem _ (mem_univ j₀))
    obtain ⟨j, hj⟩ : e₀ j₀ ∈ Set.range φ := hφr ▸ hB
    exact ⟨j, by rw [Function.comp_apply, hj, ← hj₀]; exact congrFun hxe j₀⟩
  refine ⟨k, t', x ∘ ι, e, ⟨hx.injective.comp ι.injective, ?_⟩, ?_, ?_⟩
  · have hxι : (⟨x ∘ ι, hx.injective.comp ι.injective⟩ : Fin (k + 1) ↪ M) =
        ι.trans ⟨x, hx.injective⟩ := Function.Embedding.ext fun _ ↦ rfl
    rw [hxι, hR.isConsistent _ Q ι hx.eval_eq, hι]
  · funext i
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Fin.coe_castSuccEmb, hιc]
    exact congrFun he i
  -- the cells of `t'`
  have hvis {d : Fin Q.card} (hd : Q.toCellScheme.scope d ⊆ insert p B) :
      ∃ d', StageType.faceCell hι d' = d :=
    Q.toScheme.exists_faceCell_eq _ (Scheme.mem_visibleCells.mpr fun y hy ↦ by
      obtain ⟨i, -, hi⟩ := mem_map.mp (hιF ▸ hd hy)
      exact ⟨i, hi⟩)
  have hoF : Q.toCellScheme.scope o = insert p B := congrArg Prod.fst ho
  have hoK : Q.toCellScheme.grade o = K := congrArg Prod.snd ho
  obtain ⟨o', rfl⟩ := hvis hoF.le
  obtain ⟨r', rfl⟩ := hvis hrF
  have hscope_o : t'.toCellScheme.scope o' = univ := by
    refine map_injective ι ?_
    rw [← StageType.scope_faceCell hι, hoF, hιF]
  have hgrade_o : t'.toCellScheme.grade o' = K := (StageType.grade_faceCell hι o').symm.trans hoK
  have hlabel_o : t'.label o' = ⊤ :=
    (StageType.label_faceCell hι o').symm.trans (hH.subset ((hτH _).mp hoτ))
  have htopK : t'.topGrade = K := le_antisymm (hQK ▸ StageType.topGrade_le_of_restrictFace hι)
    (hgrade_o ▸ StageType.grade_le_topGrade hlabel_o)
  -- every top cell of `t'` lies below the owner
  have hbelow {a : Fin t'.card} (ha : t'.label a = ⊤) :
      a ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o') :=
    (CellScheme.gradedIndex_le_iff _).mpr
      ⟨(CellScheme.gradedIndex_fst _ ▸ hscope_o ▸ subset_univ _ :),
        (CellScheme.gradedIndex_snd _ ▸ hgrade_o ▸ htopK ▸ StageType.grade_le_topGrade ha :)⟩
  have hlabel_r : t'.label r' = ⊤ := (StageType.label_faceCell hι r').symm.trans hr
  -- the lawful section witnessing `H`, on the face
  have hτ' := StageType.isLawful_comp_faceCell hι hτ
  have hgap {a : Fin t'.card} (ha : t'.label a = ⊤) (haτ : τ (StageType.faceCell hι a) = ⊤) :
      visibilityReplace K K (t'.rowAt o' r') < t'.rowAt o' a := by
    have := Scheme.visibilityReplace_rowAt_lt hτ' hoτ (mt (hτH _).mp hrH) haτ (hbelow hlabel_r)
      (hbelow ha)
    rwa [hgrade_o] at this
  refine ⟨o', r', ⟨fun ⟨i, hi⟩ ↦ ?_, htopK, hscope_o, hgrade_o, hlabel_o, hlabel_r, ?_,
    hgap hlabel_o hoτ, fun a ha hla ↦ hgap ha ?_⟩⟩
  · -- the root avoids the last point
    exact (Fin.castSucc_lt_last (e i)).ne hi
  · -- the lost top contains the last point
    rw [StageType.scope_faceCell hι, mem_map] at hpr
    obtain ⟨y, hy, hyp⟩ := hpr
    obtain rfl : y = Fin.last k := ι.injective (hyp.trans hιl.symm)
    exact hy
  · -- a top cell avoiding the last point is visible in `B`, so in `H`
    refine (hτH _).mpr (hBfull _ ?_ ((StageType.label_faceCell hι a).trans ha))
    rw [StageType.scope_faceCell hι]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr fun h ↦ hla (h ▸ hy')
    rw [hιc, ← mem_coe, ← hφr]
    exact Set.mem_range_self i

/-- **Residual acquisition for source-gap contexts** (`ResidualAcquisition`), with no hypothesis:
the acquired context of `exists_covers_isSourceGapContextAt`. -/
theorem residualAcquisition_isSourceGapContext :
    ResidualAcquisition.{u, w} fun K t' h ↦ t'.IsSourceGapContext K h where
  exists_context _ _ _ _ hα hR hcore hK _ _ _ hc := by
    obtain ⟨k, t', c', e, hc', hcc', o, r, hs⟩ :=
      exists_covers_isSourceGapContextAt hα hR hcore hK hc
    exact ⟨k + 1, t', c', _, hc', hcc', Fin.last k, o, r, hs⟩

end Realization

/-! ### The compiled determination counterexamples are excluded -/

namespace ExactReceivingExamples

open StageType

/-- **The context of the determination counterexample for `P ≡ True` is not a source-gap
context**: the root of `apexPoint` (the stage type on no points) along the identity, at every
grade. -/
example (t : StageType.{0} Ordinal.omega0 0)
    (_ : restrictFace Fin.castSuccEmb apexPoint = some t) (K : ℕ) :
    ¬ t.IsSourceGapContext K (Function.Embedding.refl _) :=
  not_isSourceGapContext_of_surjective fun i ↦ ⟨i, rfl⟩

end ExactReceivingExamples

end VaughtConjecture

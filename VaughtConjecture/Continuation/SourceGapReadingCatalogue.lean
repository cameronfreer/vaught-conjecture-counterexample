/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.MarkedCatalogueCompletion

/-!
# Reading marks in the leaf-and-marked layer

Roadmap, Layer 3 ((R2) of the table of 3.4, the reading of the new tops through private tops);
the leaf-and-marked layer of `VaughtConjecture.Extension.MarkedCatalogue`.

This file records what the leaf-and-marked layer gives, and does not give, for a reading of new
tops through private tops.  A **reading** is a finite set `ps` of pairs `(s, x)` of old cells; a
labelling `e` of the old cells **reads `ps`** (`Scheme.ReadsPairs`) when `e s ≤ e x` for every pair.
The statements here are about the layer and its lifts; no existence of a carrier is claimed.

**Compatibility of the reading marks** (compiled in this repository).  Let the marks be the
catalogue entries that read `ps` (`Scheme.readingMarks`) and the cap the ceiling of the field grid,
constant (`Scheme.ceilingCap`).
* The cap lies in the field grid and respects capped agreement (`Scheme.ceilingCap_mem`,
  `Scheme.capRespects_ceilingCap`).
* **Every set of marks is closed** for this cap (`Scheme.markedClosed_ceilingCap`): above the
  ceiling, capped agreement of two catalogue entries is equality, since entries take values in the
  code grid below the ceiling.  So marked closure does not constrain the choice of marks.
* **Every marked cell reads `ps`** (`Scheme.markedLayer_mark_readsPairs`).
* **Every catalogue entry is the entry of a leaf** (`Scheme.exists_leaf_eq`), and a leaf reads the
  old cells by its entry (`Scheme.markedLayer_row_leaf_castAdd`).  So an entry not reading `ps`
  (the mixed labelling of the input `SeparationObstruction.T α`, context all `⊤`, donor
  `o′ = r′ = 2`, is of this kind) is the entry of a leaf and of no mark
  (`Scheme.not_mem_readingMarks`), and that leaf does not read `ps`
  (`Scheme.markedLayer_leaf_not_readsPairs`).  A reading asked at **every** cell of full scope and
  grade `k` therefore fails in every leaf-and-marked layer whose catalogue has such an entry; only
  a reading asked at the cells labelled `⊤` can come from it.

**The lifts, and which labellings escape** (compiled in this repository).  A capped lift of the
layer serves a labelling `g` of the old cells, lawful below `(univ, k)`, by a template whose entry
is the orbit code of the splice of `g` (`Scheme.exists_template_markedLayer`).  The orbit code is
monotone in the label (`Label.monotone_orbitMap`), so **if `g` reads `ps` (at cells of grade at
most `k`), so does its code, and the code is a reading mark** (`Scheme.orbitCode_splice_mem_
readingMarks`): every such labelling is served by a marked cell whenever it is served above the
cap, and by a leaf reading `ps` otherwise.  The labellings that **escape** are those whose code
does not read `ps`: they are served by a leaf not reading `ps`, along every lift (both coatoms, the
cap `⊥` and every short positive cap).  A carrier whose labelling makes `⊤` only cells reading `ps`
must keep those leaves below `⊤`; the forced-top constraint
(`Scheme.eq_top_natAdd_of_le_agreementHeight`) is what can prevent it, and is not decided here.

**At the arity three** (`TowerProfile.readingSpec`): the marked specification of the marked top with
the reading marks and the ceiling cap exists for every reading of the profile layer at the grade
`4`, so the marked completion (`TowerProfile.markedCompletion`) exists for it, legal below the full
grade.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {k : ℕ}

/-- A labelling of the old cells **reads** the pairs `ps`: `e s ≤ e x` for every `(s, x) ∈ ps`. -/
def ReadsPairs (ps : Finset (Fin S.card × Fin S.card)) (e : Fin S.card → Label.{u}) : Prop :=
  ∀ p ∈ ps, e p.1 ≤ e p.2

variable (S k) in
/-- The **reading marks**: the catalogue entries reading `ps`. -/
noncomputable def readingMarks (ps : Finset (Fin S.card × Fin S.card)) :
    Finset (Fin S.card → Label.{u}) := by
  classical
  exact (S.catalogue k).filter (ReadsPairs ps)

theorem mem_readingMarks {ps : Finset (Fin S.card × Fin S.card)} {e : Fin S.card → Label.{u}} :
    e ∈ S.readingMarks k ps ↔ e ∈ S.catalogue k ∧ ReadsPairs ps e := by
  classical
  simp [readingMarks]

theorem readingMarks_subset (ps : Finset (Fin S.card × Fin S.card)) :
    S.readingMarks k ps ⊆ S.catalogue k :=
  fun _ he ↦ (mem_readingMarks.mp he).1

/-- An entry not reading `ps` is not a reading mark. -/
theorem not_mem_readingMarks {ps : Finset (Fin S.card × Fin S.card)} {e : Fin S.card → Label.{u}}
    (he : ¬ ReadsPairs ps e) : e ∉ S.readingMarks k ps :=
  fun h ↦ he (mem_readingMarks.mp h).2

variable (S k) in
/-- The **ceiling cap**: the largest point of the field grid, at every entry. -/
noncomputable def ceilingCap : (Fin S.card → Label.{u}) → Label.{u} :=
  fun _ ↦ gridPoint k (2 * S.card + 2)

theorem ceilingCap_mem (e : Fin S.card → Label.{u}) : S.ceilingCap k e ∈ S.fieldGrid k :=
  gridPoint_mem_grid le_rfl

theorem capRespects_ceilingCap : CapRespects S k (S.ceilingCap k) :=
  capRespects_const _

/-- A catalogue entry lies below the ceiling of the field grid. -/
theorem lt_ceiling_of_mem_catalogue {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (d : Fin S.card) : a d < gridPoint k (2 * S.card + 2) := by
  rcases mem_codeGrid.mp (mem_codeGrid_of_mem_catalogue ha d) with h | ⟨b, hb, f, hf, h⟩
  · rw [h]; exact WithBot.bot_lt_coe _
  · rw [h]
    refine lt_of_le_of_lt ?_ (gridPoint_lt_gridPoint.mpr (by omega : b < 2 * S.card + 2))
    rw [gridPoint]
    refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
    exact add_le_add_right (Nat.cast_le.mpr hf) _

/-- **Every set of marks is closed for the ceiling cap**: above the ceiling, two catalogue entries
agreeing capped at the cap are equal. -/
theorem markedClosed_ceilingCap {Mk : Finset (Fin S.card → Label.{u})} :
    MarkedClosed S k Mk (S.ceilingCap k) := by
  intro e he b hb h _ _ _ hhe hag
  have hlt : gridPoint k (2 * S.card + 2) < h := not_le.mp hhe
  have : b = e := funext fun d ↦ by
    have h1 := hag d
    rw [min_eq_left ((lt_ceiling_of_mem_catalogue hb d).trans hlt).le] at h1
    rcases le_total (e d) h with h2 | h2
    · rwa [min_eq_left h2] at h1
    · rw [min_eq_right h2] at h1
      exact absurd (h1 ▸ (lt_ceiling_of_mem_catalogue hb d).trans hlt) (lt_irrefl _)
  exact this ▸ he

/-- **Every marked cell of the reading marks reads `ps`.** -/
theorem markedLayer_mark_readsPairs {ps : Finset (Fin S.card × Fin S.card)}
    {κ : (Fin S.card → Label.{u}) → Label.{u}} (m : Fin (S.readingMarks k ps).card) :
    ReadsPairs ps fun d ↦ S.sheetRow k (S.markedEntry k (S.readingMarks k ps))
      (markedSheet _ _) κ (Fin.natAdd _ m) (Fin.castAdd _ d) :=
  markedLayer_mark_reads (P := ReadsPairs ps) (fun _ he ↦ (mem_readingMarks.mp he).2) m

/-- **A leaf reads the old cells by its catalogue entry.** -/
theorem markedLayer_row_leaf_castAdd {Mk : Finset (Fin S.card → Label.{u})}
    {κ : (Fin S.card → Label.{u}) → Label.{u}} (i : Fin (S.catalogue k).card) (d : Fin S.card) :
    S.sheetRow k (S.markedEntry k Mk) (markedSheet _ _) κ (Fin.castAdd _ i) (Fin.castAdd _ d) =
      S.catalogueEntry k i d := by
  rw [sheetRow_castAdd, markedEntry_castAdd]

/-- **A catalogue entry not reading `ps` is the entry of a leaf not reading `ps`**, in every
leaf-and-marked layer. -/
theorem markedLayer_leaf_not_readsPairs {Mk : Finset (Fin S.card → Label.{u})}
    {κ : (Fin S.card → Label.{u}) → Label.{u}} {ps : Finset (Fin S.card × Fin S.card)}
    {b : Fin S.card → Label.{u}} (hb : b ∈ S.catalogue k) (hbr : ¬ ReadsPairs ps b) :
    ∃ j, S.markedEntry k Mk j = b ∧ markedSheet _ Mk.card j = false ∧
      ¬ ReadsPairs ps fun d ↦ S.sheetRow k (S.markedEntry k Mk) (markedSheet _ _) κ j
        (Fin.castAdd _ d) := by
  obtain ⟨j, hj, hjs⟩ := exists_leaf_eq (Mk := Mk) hb
  refine ⟨j, hj, hjs, ?_⟩
  simp only [sheetRow_castAdd, hj]
  exact hbr

/-- **A labelling reading `ps` has a reading mark as code**: if `g` is lawful below `(univ, k)` and
reads `ps` at cells of grade at most `k`, the orbit code of its splice is a reading mark.  The
orbit code is monotone in the label. -/
theorem orbitCode_splice_mem_readingMarks {ps : Finset (Fin S.card × Fin S.card)}
    {g : Fin S.card → Label.{u}} (hg : S.rows.IsLawfulBelow (univ, k) fun d ↦ g d)
    (hps : ∀ p ∈ ps, S.toCellScheme.grade p.1 ≤ k ∧ S.toCellScheme.grade p.2 ≤ k)
    (hr : ReadsPairs ps g) :
    orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) g) ∈ S.readingMarks k ps := by
  refine mem_readingMarks.mpr ⟨orbitCode_splice_bot_mem_catalogue hg, fun p hp ↦ ?_⟩
  rw [orbitCode_apply, orbitCode_apply]
  refine monotone_orbitMap k _ ?_
  rw [CellScheme.splice_of_le (hps p hp).1, CellScheme.splice_of_le (hps p hp).2]
  exact hr p hp

end Scheme

namespace TowerProfile

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- **The reading specification at the arity three**: the reading marks of `ps` and the ceiling
cap. -/
noncomputable def readingSpec (ps : Finset (Fin (scheme I).card × Fin (scheme I).card)) :
    MarkedSpec I where
  marks := (scheme I).readingMarks 4 ps
  cap := (scheme I).ceilingCap 4
  marks_subset := Scheme.readingMarks_subset ps
  cap_mem := Scheme.ceilingCap_mem
  capRespects := Scheme.capRespects_ceilingCap
  closed := Scheme.markedClosed_ceilingCap

end TowerProfile

end VaughtConjecture

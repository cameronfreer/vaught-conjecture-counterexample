/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryAdmittedBountiful
import VaughtConjecture.Extension.CoupledGatedExtensionCounterexample

/-!
# The admitted completion for self-seeds at the arity one

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade with a restricted catalogue at the
reading grades) and 3.3 (the (R4) cap); the generalization from the private type `P` of
`VaughtConjecture.Continuation.StableRecoveryAdmittedBountiful`.

Let `I` be a seed on three points whose two coatom types are equal to a legal stage type `T` on two
points, and `b` a cell of `T` of grade `2` (the cap; it has full scope).  The **admission with the
marker at the cap** (`Seed.admS I hLR b`) on the labellings of the doubled lower layer reads a
labelling `e` on the private copy (`Seed.privS`) and the donor copy (`Seed.donS`) of the cells of
`T`: if the private copy is in the **bottom class** (`Seed.InClassS`: `⊥` exactly at the cells of
grade `1`), the donor copy reads every cell of grade `2` at least as the private copy reads the cap
(the capped reading, which is capped correctness with the marker at the cap when the cells of
grade `1` are dead).

**The two hypotheses on `T`** (explicit; neither is a consequence of legality):

* `StageType.HasDeadLowCells T`: every cell of grade `1` reads itself at `⊥` (so every lawful
  labelling is `⊥` there);
* `StageType.HasTopFullCells T`: every cell of grade `2` is labelled `⊤`.

Under these (`Seed.isLegalBelowFullGrade_admittedLayerS`), the admitted layer at the grade `2` over
the doubled lower layer of the seed of `T` with itself is legal below the full grade: **one
completion per input**.  The lift provisions, for every prescription and every cap, from both
coatoms (`Seed.botProvisionS_left`, `Seed.capProvisionS_left`, `Seed.botProvisionS_right`,
`Seed.capProvisionS_right`), use:

* the raise `min (label of T) v` (lawful by the min-closure of lawful labellings, and `v` at every
  cell of grade `2` by `HasTopFullCells`);
* the lowering `min (private copy of the entry) m`, `m` the least donor value of the prescription
  at the cells of grade `2` (min-closure);
* capped correctness of the entry (the admission);
* the dead cells, for the agreement of the two copies at the common face (its cells have grade
  `1`), the bottom pattern of the class, and the lifts at the grade `1`.

The private type `P` is an instance (`GatedExtensionCounterexample.hasDeadLowCells_P`,
`GatedExtensionCounterexample.hasTopFullCells_P`).  **The gap** is exact at the type of
`VaughtConjecture.Extension.CoupledGatedExtensionCounterexample`: a legal type on two points with a
cell of grade `1` labelled `1` (`CoupledGatedExtensionCounterexample.not_hasDeadLowCells_P`); for
such types the fills above are not available (the two copies of a live cell need not agree, and the
donor's live cells are not requested), and neither the provision nor its failure is proved here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- Every cell of grade `1` of `T` **reads itself at `⊥`**: it is dead. -/
def HasDeadLowCells (T : StageType.{u} α n) : Prop :=
  ∀ z, T.toCellScheme.grade z = 1 →
    T.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥

/-- Every cell of grade `2` of `T` is **labelled `⊤`**. -/
def HasTopFullCells (T : StageType.{u} α n) : Prop :=
  ∀ z, T.toCellScheme.grade z = 2 → T.label z = ⊤

/-- A lawful labelling is `⊥` at a dead cell. -/
theorem HasDeadLowCells.eq_bot {T : StageType.{u} α n} (hT : T.HasDeadLowCells)
    {s : Fin T.card → Label.{u}} (hs : T.rows.IsLawful s) {z : Fin T.card}
    (hz : T.toCellScheme.grade z = 1) : s z = ⊥ := by
  have h := (hs.locality z).eq_bot (d := ⟨z, CellScheme.mem_below_gradedIndex _ z⟩) (hT z hz)
  simpa using h

end StageType

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)

/-! ### Copies, class, admission -/

/-- The private copy of a labelling of the doubled lower layer. -/
noncomputable def privS (e : Fin (I.doubledLower hLR).card → Label.{u}) (z : Fin I.left.card) :
    Label.{u} :=
  e (Fin.castAdd _ (StageType.faceCell I.restrictFace_left z))

/-- The donor copy of a labelling of the doubled lower layer. -/
noncomputable def donS (e : Fin (I.doubledLower hLR).card → Label.{u}) (z : Fin I.left.card) :
    Label.{u} :=
  e (Fin.castAdd _ (StageType.faceCell (I.restrictFace_right_left hLR) z))

/-- The **bottom class**: `⊥` exactly at the cells of grade `1`. -/
def InClassS (s : Fin I.left.card → Label.{u}) : Prop :=
  ∀ z, s z = ⊥ ↔ I.left.toCellScheme.grade z = 1

/-- **The admission with the marker at the cap `b`**: in the bottom class of the private copy, the
donor copy reads every cell of grade `2` at least as the private copy reads the cap. -/
def admS (b : Fin I.left.card) (e : Fin (I.doubledLower hLR).card → Label.{u}) : Prop :=
  I.InClassS (I.privS hLR e) →
    ∀ y, I.left.toCellScheme.grade y = 2 → I.privS hLR e b ≤ I.donS hLR e y

/-- **The admitted layer** at the grade `2` over the doubled lower layer. -/
noncomputable abbrev admittedLayerS (b : Fin I.left.card) : Scheme.{u} 3 :=
  (I.doubledLower hLR).admittedFieldLayer 2 (I.admS hLR b) (I.not_univ_two_le_doubledLower hLR)

variable {I hLR}

/-- The cells of `T` have grade `1` or `2`. -/
theorem grade_one_or_two (z : Fin I.left.card) :
    I.left.toCellScheme.grade z = 1 ∨ I.left.toCellScheme.grade z = 2 := by
  have h0 : 0 < I.left.toCellScheme.grade z :=
    (I.left.isWellFormed.isWellFormed.gradedIndex_mem z).2.1
  have h2 := I.left.grade_le z
  omega

/-- A cell of `T` avoiding the last point has grade `1`. -/
theorem grade_eq_one_of_last_notMem {z : Fin I.left.card}
    (hz : Fin.last 1 ∉ I.left.toCellScheme.scope z) : I.left.toCellScheme.grade z = 1 := by
  have h0 : 0 < I.left.toCellScheme.grade z :=
    (I.left.isWellFormed.isWellFormed.gradedIndex_mem z).2.1
  have hc : I.left.toCellScheme.grade z ≤ #(I.left.toCellScheme.scope z) :=
    I.left.isWellFormed.isWellFormed.grade_le_card z
  have hs : I.left.toCellScheme.scope z ⊆ univ.erase (Fin.last 1) :=
    fun x hx ↦ mem_erase.mpr ⟨fun he ↦ hz (he ▸ hx), mem_univ x⟩
  have := card_le_card hs
  rw [card_erase_of_mem (mem_univ _)] at this
  simp at this
  omega

/-- The constant `⊥` is admitted: it is not in the bottom class at the cap. -/
theorem admS_bot {b : Fin I.left.card} (hb : I.left.toCellScheme.grade b = 2) :
    I.admS hLR b (fun _ ↦ ⊥) :=
  fun hcl ↦ absurd ((hcl b).mp rfl) (by omega)

/-- The private copy of the orbit code is the orbit map of the private copy. -/
theorem privS_orbitCode (g : Fin (I.doubledLower hLR).card → Label.{u}) :
    I.privS hLR (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) =
      fun z ↦ orbitMap 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)
        (I.privS hLR g z) := by
  funext z
  simp only [privS, orbitCode_apply]
  rw [CellScheme.splice_of_le]
  exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans_le
    (Nat.lt_succ_iff.mp (I.grade_lt _))

/-- The donor copy of the orbit code is the orbit map of the donor copy. -/
theorem donS_orbitCode (g : Fin (I.doubledLower hLR).card → Label.{u}) :
    I.donS hLR (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) =
      fun z ↦ orbitMap 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)
        (I.donS hLR g z) := by
  funext z
  simp only [donS, orbitCode_apply]
  rw [CellScheme.splice_of_le]
  exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans_le
    (Nat.lt_succ_iff.mp (I.grade_lt _))

/-- **The orbit code of a labelling with the capped reading is admitted.** -/
theorem admS_orbitCode {b : Fin I.left.card} {g : Fin (I.doubledLower hLR).card → Label.{u}}
    (hT : ∀ y, I.left.toCellScheme.grade y = 2 → I.privS hLR g b ≤ I.donS hLR g y) :
    I.admS hLR b (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  intro _ y hy
  rw [privS_orbitCode, donS_orbitCode]
  exact monotone_orbitMap 2 _ (hT y hy)

/-- A labelling whose private copy is not in the bottom class has its orbit code admitted. -/
theorem admS_orbitCode_of_not {b : Fin I.left.card} {g : Fin (I.doubledLower hLR).card → Label.{u}}
    (hg : ¬ I.InClassS (I.privS hLR g)) :
    I.admS hLR b (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  intro hcl
  refine absurd (fun z ↦ ?_) hg
  rw [privS_orbitCode] at hcl
  have := hcl z
  simpa only [orbitMap_eq_bot_iff] using this

/-- The bottom class passes along an agreement capped at a positive cap. -/
theorem inClassS_of_min_eq {s t : Fin I.left.card → Label.{u}} {h : Label.{u}} (hh : ⊥ < h)
    (hst : ∀ z, min (s z) h = min (t z) h) (hs : I.InClassS s) : I.InClassS t := by
  intro z
  rw [← hs z]
  have e := hst z
  constructor
  · intro ht
    rw [ht, min_bot_left] at e
    rcases min_eq_bot.mp e with h' | h'
    · exact h'
    · exact absurd h' hh.ne'
  · intro hs'
    rw [hs', min_bot_left] at e
    rcases min_eq_bot.mp e.symm with h' | h'
    · exact h'
    · exact absurd h' hh.ne'

/-! ### Gluing, the coatom pairs, and the cells of grade `1` -/

variable (hd : I.left.HasDeadLowCells)
include hd

/-- **Gluing lawful labellings of `T` on the doubled lower layer**, `⊥` at the new cells. -/
theorem exists_glueS (hI : I.left.IsLegal) {sL sR : Fin I.left.card → Label.{u}}
    (hL : I.left.rows.IsLawful sL) (hR : I.left.rows.IsLawful sR) :
    ∃ g : Fin (I.doubledLower hLR).card → Label.{u}, (I.doubledLower hLR).rows.IsLawful g ∧
      I.privS hLR g = sL ∧ I.donS hLR g = sR ∧ ∀ i, g (Fin.natAdd _ i) = ⊥ := by
  obtain ⟨w, hw, hwL, hwR⟩ := I.exists_isLawful_glue hLR hL hR fun z hz ↦ by
    rw [hd.eq_bot hL (grade_eq_one_of_last_notMem hz),
      hd.eq_bot hR (grade_eq_one_of_last_notMem hz)]
  have hw1 (d : Fin I.amalgam.card) (hd1 : I.amalgam.toCellScheme.grade d = 1) : w d = ⊥ := by
    rcases I.eq_faceCell_or hLR d with h | h
    · rw [← h, hwL]
      rw [← h, StageType.grade_faceCell] at hd1
      exact hd.eq_bot hL hd1
    · rw [← h, hwR]
      rw [← h, StageType.grade_faceCell] at hd1
      exact hd.eq_bot hR hd1
  obtain ⟨c, hc⟩ := hI.isComplete ((univ : Finset (Fin 2)), 1)
    ⟨I.left.univ_mem_faces, one_pos, by simp⟩
  obtain ⟨i₀, -⟩ := Scheme.exists_fullCell_eq hc
  refine ⟨Fin.append w fun _ ↦ ⊥, Scheme.isLawful_appendFullCells (h := I.not_univ_le 1)
    ?_ (fun _ ↦ ?_) (fun i ↦ ?_) fun s hs ↦ ⟨i₀, ?_⟩, ?_, ?_, fun i ↦ Fin.append_right _ _ i⟩
  · convert hw using 1
    funext d
    exact Fin.append_left _ _ d
  · rw [Fin.append_right]
    exact isSelfVisible_bot _
  · convert TransformsTo.bot _ _ using 1
    funext t
    rw [Fin.append_right, min_bot_right]
  · rw [Fin.append_right]
    induction s using Fin.addCases with
    | left d =>
      rw [Fin.append_left, hw1 d (by
        rw [← Scheme.appendFullCellsScheme_grade_castAdd]; exact hs)]
    | right j => rw [Fin.append_right]
  · funext z
    exact (Fin.append_left _ _ _).trans (hwL z)
  · funext z
    exact (Fin.append_left _ _ _).trans (hwR z)

omit hd in
private theorem not_univ_one_le_erase {x : Fin 3} {g : ℕ} :
    ¬ ((univ : Finset (Fin 3)), 1) ≤ (univ.erase x, g) :=
  fun h ↦ Finset.notMem_erase x univ (h.1 (mem_univ x))

omit hd in
/-- The private copy of a labelling lawful below the private coatom pair is lawful on `T`. -/
theorem isLawful_privS {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    I.left.rows.IsLawful (I.privS hLR f) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := I.amalgam.toScheme) (k := 1)
    (M := I.nFull 1) (r := I.lowerRow hLR) (h := I.not_univ_le 1) not_univ_one_le_erase).mp hf
  have hpair : ((univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.left 1)) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, Coatom.univ_map_left]
  have h2 := (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) (univ, 2)
      (fun d ↦ f (Fin.castAdd _ d))).mpr (by rw [← hpair]; exact h1)
  exact h2.isLawful fun d ↦ ⟨subset_univ _, I.left.grade_le d⟩

omit hd in
/-- The donor copy of a labelling lawful below the donor coatom pair is lawful on `T`. -/
theorem isLawful_donS {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    I.left.rows.IsLawful (I.donS hLR f) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := I.amalgam.toScheme) (k := 1)
    (M := I.nFull 1) (r := I.lowerRow hLR) (h := I.not_univ_le 1) not_univ_one_le_erase).mp hf
  have hpair : ((univ.erase (Fin.castSucc (Fin.last 1)), 2) : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.right 1)) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, Coatom.univ_map_right]
  have h2 := (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace (I.restrictFace_right_left hLR)) (univ, 2)
      (fun d ↦ f (Fin.castAdd _ d))).mpr (by rw [← hpair]; exact h1)
  exact h2.isLawful fun d ↦ ⟨subset_univ _, I.left.grade_le d⟩

omit hd in
/-- A cell below the private coatom pair is a private copy. -/
theorem exists_left_of_mem_belowS {d : Fin (I.doubledLower hLR).card}
    (hdm : d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2)) :
    ∃ z, d = Fin.castAdd _ (StageType.faceCell I.restrictFace_left z) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hdm.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ (Fin.last 2)))
  | left e =>
    have h : I.amalgam.toCellScheme.scope e ⊆ univ.map (Coatom.left 1) := by
      have h' := hdm.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [Coatom.univ_map_left]
      exact h'
    exact ⟨I.doublingCell hLR e, by rw [I.faceCell_left_of_subset hLR h]⟩

omit hd in
/-- A cell below the donor coatom pair is a donor copy. -/
theorem exists_right_of_mem_belowS {d : Fin (I.doubledLower hLR).card}
    (hdm : d ∈ (I.doubledLower hLR).toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 1)), 2)) :
    ∃ z, d = Fin.castAdd _ (StageType.faceCell (I.restrictFace_right_left hLR) z) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hdm.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ _))
  | left e =>
    have h : I.amalgam.toCellScheme.scope e ⊆ univ.map (Coatom.right 1) := by
      have h' := hdm.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [Coatom.univ_map_right]
      exact h'
    exact ⟨I.doublingCell hLR e, by rw [I.faceCell_right_of_subset hLR h]⟩

omit hd in
/-- The private copies lie below the private coatom pair. -/
theorem left_mem_belowS (z : Fin I.left.card) :
    Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left z) ∈
      (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2) := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨(StageType.scope_faceCell I.restrictFace_left z).trans_subset
    ((map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_left (m := 1)).subset),
    (StageType.grade_faceCell I.restrictFace_left z).trans_le (I.left.grade_le z)⟩

omit hd in
/-- The donor copies lie below the donor coatom pair. -/
theorem right_mem_belowS (z : Fin I.left.card) :
    Fin.castAdd (I.nFull 1) (StageType.faceCell (I.restrictFace_right_left hLR) z) ∈
      (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨(StageType.scope_faceCell (I.restrictFace_right_left hLR) z).trans_subset
    ((map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_right (m := 1)).subset),
    (StageType.grade_faceCell (I.restrictFace_right_left hLR) z).trans_le (I.left.grade_le z)⟩

/-- The cells of grade `1` of the doubled lower layer read themselves at `⊥`. -/
theorem row_self_eq_bot_lowerS {s : Fin (I.doubledLower hLR).card}
    (hs : (I.doubledLower hLR).toCellScheme.grade s = 1) :
    (I.doubledLower hLR).rows.row s ⟨s, CellScheme.mem_below_gradedIndex _ s⟩ = ⊥ := by
  have hD := I.isDoubling_doubledLower hLR
  rw [← Scheme.rowAt_of_mem, hD.rowAt_eq s s (CellScheme.mem_below_gradedIndex _ s)]
  have hz : I.left.toCellScheme.grade (I.lowerCell hLR s) = 1 := (hD.grade_eq s).trans hs
  rw [Scheme.rowAt_of_mem (CellScheme.mem_below_gradedIndex _ _)]
  exact hd _ hz

/-- A labelling lawful below a pair is `⊥` at the cells of grade `1` below it. -/
theorem eq_bot_lowerS {X : Finset (Fin 3) × ℕ} {w : Fin (I.doubledLower hLR).card → Label.{u}}
    (hw : (I.doubledLower hLR).rows.IsLawfulBelow X (fun d ↦ w d))
    {s : Fin (I.doubledLower hLR).card} (hsX : s ∈ (I.doubledLower hLR).toCellScheme.below X)
    (hs : (I.doubledLower hLR).toCellScheme.grade s = 1) : w s = ⊥ := by
  have h := ((CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 s hsX).eq_bot
    (d := ⟨s, CellScheme.mem_below_gradedIndex _ s⟩) (row_self_eq_bot_lowerS hd hs)
  simpa using h

/-- **The lifts of the doubled lower layer at the grade `1`**: the cells there are dead. -/
theorem cappedLift_lowerS_one (U : Finset (Fin 3)) :
    (I.doubledLower hLR).rows.CappedLift (X := (U, 1)) (Y := ((univ : Finset (Fin 3)), 1))
      ⟨subset_univ _, le_rfl⟩ := by
  rw [CellScheme.Rows.cappedLift_iff_forall_exists]
  intro c _ p q hp hq _
  have hpos (d : Fin (I.doubledLower hLR).card) : 0 < (I.doubledLower hLR).toCellScheme.grade d :=
    ((I.isWellFormed_doubledLower hLR).isWellFormed.gradedIndex_mem d).2.1
  have hbot {X : Finset (Fin 3) × ℕ} (hX : X.2 = 1)
      {r : (I.doubledLower hLR).toCellScheme.below X → Label.{u}}
      (hr : (I.doubledLower hLR).rows.IsLawfulBelow X r) (d) : r d = ⊥ := by
    have h := eq_bot_lowerS hd (CellScheme.Rows.isLawfulBelow_extendBot.mpr hr) d.2
      (le_antisymm (d.2.2.trans hX.le) (hpos d.1))
    rwa [CellScheme.Rows.extendBot_of_mem r d.2] at h
  refine ⟨fun _ ↦ ⊥, CellScheme.Rows.isLawfulBelow_const_bot _, fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hbot rfl hq d]
  · exact (hbot rfl hp d).symm

/-! ### The lift provisions -/

variable {b : Fin I.left.card}

/-- The cells of grade at most `2` of the doubled lower layer: copies, and the dead new cells. -/
theorem min_eq_of_copiesS {W a : Fin (I.doubledLower hLR).card → Label.{u}} {h : Label.{u}}
    (ha : (I.doubledLower hLR).rows.IsLawful a) (hWN : ∀ i, W (Fin.natAdd _ i) = ⊥)
    (hL : ∀ z, min (I.privS hLR W z) h = min (I.privS hLR a z) h)
    (hR : ∀ z, min (I.donS hLR W z) h = min (I.donS hLR a z) h)
    (d : Fin (I.doubledLower hLR).card) : min (W d) h = min (a d) h := by
  induction d using Fin.addCases with
  | right i =>
    rw [hWN, eq_bot_lowerS hd (ha.isLawfulBelow ((univ : Finset (Fin 3)), 2))
      (s := Fin.natAdd _ i) ⟨subset_univ _,
        (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le.trans (by omega)⟩
      (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)]
  | left e =>
    rcases I.eq_faceCell_or hLR e with he | he
    · rw [← he]; exact hL _
    · rw [← he]; exact hR _

/-- **The lift provision at the cap `⊥` from the private coatom**: the raise of `T`'s labelling to
the private cap value on the donor copy. -/
theorem botProvisionS_left (hI : I.left.IsLegal) (ht : I.left.HasTopFullCells)
    (hb : I.left.toCellScheme.grade b = 2) {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      I.admS hLR b (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsL := isLawful_privS hf
  have hvs : IsSelfVisible 2 (I.privS hLR f b) := hb ▸ hsL.orderly b
  have hD : I.left.rows.IsLawful fun z ↦ min (I.left.label z) (I.privS hLR f b) :=
    I.left.isLawful.min_const_of_isSelfVisible (K := 2) (fun d ↦ I.left.grade_le d) hvs
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glueS hd hI hsL hD
  refine ⟨g, hg.isLawfulBelow _, fun d hdm ↦ ?_, admS_orbitCode fun y hy ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_belowS hdm
    exact congrFun hgL z
  · rw [hgL, hgR]
    simp only [ht y hy, min_top_left, le_refl]

/-- **The lift provision at a positive cap from the private coatom**: the donor copy of the entry,
or the raise when the prescription is in the bottom class and the entry reads a cell of grade `2`
of the donor below the private cap of the prescription (then all values involved lie at least at
`h`, by capped correctness of the entry). -/
theorem capProvisionS_left (hI : I.left.IsLegal) (ht : I.left.HasTopFullCells)
    (hb : I.left.toCellScheme.grade b = 2) {h : Label.{u}} (hbh : ⊥ < h)
    {a : Fin (I.doubledLower hLR).card → Label.{u}} (ha : (I.doubledLower hLR).rows.IsLawful a)
    (hA : I.admS hLR b a) {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      (∀ d, (I.doubledLower hLR).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admS hLR b (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsL := isLawful_privS hf
  have heL := isLawful_privS (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have heR := isLawful_donS (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  have hagL (z : Fin I.left.card) : min (I.privS hLR f z) h = min (I.privS hLR a z) h :=
    hfa _ (left_mem_belowS z)
  obtain ⟨D, hD, hDa, hDT⟩ : ∃ D : Fin I.left.card → Label.{u}, I.left.rows.IsLawful D ∧
      (∀ z, min (D z) h = min (I.donS hLR a z) h) ∧
      (I.InClassS (I.privS hLR f) → ∀ y, I.left.toCellScheme.grade y = 2 →
        I.privS hLR f b ≤ D y) := by
    by_cases hraise : I.InClassS (I.privS hLR f) ∧
        ¬ ∀ y, I.left.toCellScheme.grade y = 2 → I.privS hLR f b ≤ I.donS hLR a y
    · obtain ⟨hcl, hnot⟩ := hraise
      have hcorr := hA (inClassS_of_min_eq hbh hagL hcl)
      push Not at hnot
      obtain ⟨y₀, hy₀, hlt⟩ := hnot
      have hhe : h ≤ I.privS hLR a b :=
        GatedExtensionCounterexample.le_of_min_eq_of_lt ((hcorr y₀ hy₀).trans_lt hlt) (hagL b)
      have hsh : h ≤ I.privS hLR f b := hhe.trans ((hcorr y₀ hy₀).trans hlt.le)
      have hvs : IsSelfVisible 2 (I.privS hLR f b) := hb ▸ hsL.orderly b
      refine ⟨fun z ↦ min (I.left.label z) (I.privS hLR f b),
        I.left.isLawful.min_const_of_isSelfVisible (K := 2) (fun d ↦ I.left.grade_le d) hvs,
        fun z ↦ ?_, fun _ y hy ↦ by simp only [ht y hy, min_top_left, le_refl]⟩
      rcases grade_one_or_two z with hz | hz
      · simp only
        rw [hd.eq_bot I.left.isLawful hz, min_bot_left, hd.eq_bot heR hz]
      · simp only
        rw [ht z hz, min_top_left, min_eq_right hsh, min_eq_right (hhe.trans (hcorr z hz))]
    · exact ⟨I.donS hLR a, heR, fun _ ↦ rfl, fun hcl ↦ not_not.mp fun hc ↦ hraise ⟨hcl, hc⟩⟩
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glueS hd hI hsL hD
  refine ⟨g, hg.isLawfulBelow _, fun d hdm ↦ ?_,
    fun d _ ↦ min_eq_of_copiesS hd ha hgN (fun z ↦ by rw [hgL]; exact hagL z)
      (fun z ↦ by rw [hgR]; exact hDa z) d, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_belowS hdm
    exact congrFun hgL z
  · by_cases hcl : I.InClassS (I.privS hLR f)
    · exact admS_orbitCode fun y hy ↦ by rw [hgL, hgR]; exact hDT hcl y hy
    · exact admS_orbitCode_of_not (by rw [hgL]; exact hcl)

/-- **The lift provision at the cap `⊥` from the donor coatom**: `⊥` on the private copy. -/
theorem botProvisionS_right (hI : I.left.IsLegal) (hb : I.left.toCellScheme.grade b = 2)
    {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2), W d = f d) ∧
      I.admS hLR b (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glueS hd hI
    (CellScheme.Rows.isLawful_const_bot (R := I.left.rows)) (isLawful_donS hf)
  refine ⟨g, hg.isLawfulBelow _, fun d hdm ↦ ?_, admS_orbitCode_of_not ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_belowS hdm
    exact congrFun hgR z
  · rw [hgL]
    exact fun hcl ↦ absurd ((hcl b).mp rfl) (by omega)

/-- **The lift provision at a positive cap from the donor coatom**: the private copy of the entry,
or its lowering to the least donor value of the prescription at the cells of grade `2` when the
entry is in the bottom class and reads its private cap above a donor value of the prescription
(then that least value lies at least at `h`). -/
theorem capProvisionS_right (hI : I.left.IsLegal) (hb : I.left.toCellScheme.grade b = 2)
    {h : Label.{u}} {a : Fin (I.doubledLower hLR).card → Label.{u}}
    (ha : (I.doubledLower hLR).rows.IsLawful a) (hA : I.admS hLR b a)
    {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ (I.doubledLower hLR).toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 1)), 2), min (f d) h = min (a d) h) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2), W d = f d) ∧
      (∀ d, (I.doubledLower hLR).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admS hLR b (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsR := isLawful_donS hf
  have heL := isLawful_privS (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hagR (z : Fin I.left.card) : min (I.donS hLR f z) h = min (I.donS hLR a z) h :=
    hfa _ (right_mem_belowS z)
  set F : Finset (Fin I.left.card) := univ.filter fun y ↦ I.left.toCellScheme.grade y = 2
  have hbF : b ∈ F := mem_filter.mpr ⟨mem_univ _, hb⟩
  obtain ⟨L, hL, hLa, hLT⟩ : ∃ L : Fin I.left.card → Label.{u}, I.left.rows.IsLawful L ∧
      (∀ z, min (L z) h = min (I.privS hLR a z) h) ∧
      (I.InClassS L → ∀ y, I.left.toCellScheme.grade y = 2 → L b ≤ I.donS hLR f y) := by
    by_cases hlow : I.InClassS (I.privS hLR a) ∧
        ¬ ∀ y, I.left.toCellScheme.grade y = 2 → I.privS hLR a b ≤ I.donS hLR f y
    · obtain ⟨hcl, hnot⟩ := hlow
      have hcorr := hA hcl
      push Not at hnot
      obtain ⟨y₀, hy₀, hlt⟩ := hnot
      have hhy : h ≤ I.donS hLR f y₀ := GatedExtensionCounterexample.le_of_min_eq_of_lt
        (hlt.trans_le (hcorr y₀ hy₀)) (hagR y₀).symm
      have hhe : h ≤ I.privS hLR a b := hhy.trans hlt.le
      have hge (y : Fin I.left.card) (hy : I.left.toCellScheme.grade y = 2) :
          h ≤ I.donS hLR f y := by
        have e := hagR y
        rw [min_eq_right (hhe.trans (hcorr y hy))] at e
        exact min_eq_right_iff.mp e
      set m := F.inf' ⟨b, hbF⟩ (I.donS hLR f)
      have hm : h ≤ m := le_inf' _ _ fun y hy ↦ hge y (mem_filter.mp hy).2
      have hmv : IsSelfVisible 2 m := by
        obtain ⟨y, hy, hym⟩ := exists_mem_eq_inf' ⟨b, hbF⟩ (I.donS hLR f)
        have hm' : m = I.donS hLR f y := hym
        rw [hm']
        exact (mem_filter.mp hy).2 ▸ hsR.orderly y
      refine ⟨fun z ↦ min (I.privS hLR a z) m,
        heL.min_const_of_isSelfVisible (K := 2) (fun d ↦ I.left.grade_le d) hmv,
        fun z ↦ ?_, fun _ y hy ↦
          (min_le_right _ _).trans
            (inf'_le (I.donS hLR f) (show y ∈ F from mem_filter.mpr ⟨mem_univ _, hy⟩))⟩
      simp only
      rw [min_assoc, min_eq_right hm]
    · exact ⟨I.privS hLR a, heL, fun _ ↦ rfl, fun hcl ↦ not_not.mp fun hc ↦ hlow ⟨hcl, hc⟩⟩
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glueS hd hI hL hsR
  refine ⟨g, hg.isLawfulBelow _, fun d hdm ↦ ?_,
    fun d _ ↦ min_eq_of_copiesS hd ha hgN (fun z ↦ by rw [hgL]; exact hLa z)
      (fun z ↦ by rw [hgR]; exact hagR z) d, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_belowS hdm
    exact congrFun hgR z
  · by_cases hcl : I.InClassS L
    · exact admS_orbitCode fun y hy ↦ by rw [hgL, hgR]; exact hLT hcl y hy
    · exact admS_orbitCode_of_not (by rw [hgL]; exact hcl)

/-! ### The admitted completion -/

omit hd in
private theorem erase_ne_univS (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

omit hd in
/-- The private copy of the cap lies at the private coatom pair. -/
theorem gradedIndex_left_cap (hb : I.left.toCellScheme.grade b = 2) :
    (I.doubledLower hLR).toCellScheme.gradedIndex
      (Fin.castAdd (I.nFull 1) (StageType.faceCell I.restrictFace_left b)) =
        (univ.erase (Fin.last 2), 2) := by
  have hs : I.left.toCellScheme.scope b = univ :=
    congrArg Prod.fst (I.left.gradedIndex_eq_univ_of_grade_eq hb)
  refine (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (Prod.ext ?_ ?_)
  · exact (StageType.scope_faceCell I.restrictFace_left b).trans
      (by rw [hs]; exact Coatom.univ_map_left (m := 1))
  · exact (StageType.grade_faceCell I.restrictFace_left b).trans hb

omit hd in
/-- The donor copy of the cap lies at the donor coatom pair. -/
theorem gradedIndex_right_cap (hb : I.left.toCellScheme.grade b = 2) :
    (I.doubledLower hLR).toCellScheme.gradedIndex
      (Fin.castAdd (I.nFull 1) (StageType.faceCell (I.restrictFace_right_left hLR) b)) =
        (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  have hs : I.left.toCellScheme.scope b = univ :=
    congrArg Prod.fst (I.left.gradedIndex_eq_univ_of_grade_eq hb)
  refine (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (Prod.ext ?_ ?_)
  · exact (StageType.scope_faceCell (I.restrictFace_right_left hLR) b).trans
      (by rw [hs]; exact Coatom.univ_map_right (m := 1))
  · exact (StageType.grade_faceCell (I.restrictFace_right_left hLR) b).trans hb

/-- **The lift from the private coatom into the admitted layer.** -/
theorem cappedLift_admittedLayerS_left (hI : I.left.IsLegal) (ht : I.left.HasTopFullCells)
    (hb : I.left.toCellScheme.grade b = 2) :
    (I.admittedLayerS hLR b).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_doubledLower hLR)
    (I.isConsistent_doubledLower hLR hI) (admS_bot hb) (erase_ne_univS _)
    ⟨_, gradedIndex_left_cap hb⟩ (cappedLift_lowerS_one hd _)
    (fun _ hf ↦ botProvisionS_left hd hI ht hb hf)
    (fun _ _ _ hbh _ ha hA _ hf hfa ↦ capProvisionS_left hd hI ht hb hbh ha hA hf hfa)

/-- **The lift from the donor coatom into the admitted layer.** -/
theorem cappedLift_admittedLayerS_right (hI : I.left.IsLegal)
    (hb : I.left.toCellScheme.grade b = 2) :
    (I.admittedLayerS hLR b).rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_doubledLower hLR)
    (I.isConsistent_doubledLower hLR hI) (admS_bot hb) (erase_ne_univS _)
    ⟨_, gradedIndex_right_cap hb⟩ (cappedLift_lowerS_one hd _)
    (fun _ hf ↦ botProvisionS_right hd hI hb hf)
    (fun _ _ _ _ _ ha hA _ hf hfa ↦ capProvisionS_right hd hI hb ha hA hf hfa)

/-- **The admitted completion at the arity one for a self-seed.**  For a seed whose two coatom
types equal a legal type `T` on two points whose cells of grade `1` are dead and whose cells of
grade `2` are labelled `⊤`, and a cap `b` of grade `2`, the admitted layer at the grade `2` over the
doubled lower layer (admission: capped reading with the marker at the cap) is legal below the full
grade. -/
theorem isLegalBelowFullGrade_admittedLayerS (hI : I.left.IsLegal) (ht : I.left.HasTopFullCells)
    (hb : I.left.toCellScheme.grade b = 2) :
    (I.admittedLayerS hLR b).IsLegalBelowFullGrade :=
  I.isLegalBelowFullGrade_admittedDoubledLower hLR hI (admS_bot hb)
    (I.isBountiful_admittedDoubledLower hLR (cappedLift_lowerS_one hd)
      (cappedLift_admittedLayerS_left hd hI ht hb) (cappedLift_admittedLayerS_right hd hI hb))

end Seed

/-! ### The private type `P` is an instance; the gap -/

namespace GatedExtensionCounterexample

/-- The cells of grade `1` of `P` are dead. -/
theorem hasDeadLowCells_P (α : Ordinal.{u}) : (P α).HasDeadLowCells := fun _ hz ↦
  row_self_eq_bot_P hz

/-- The cells of grade `2` of `P` are labelled `⊤`. -/
theorem hasTopFullCells_P (α : Ordinal.{u}) : (P α).HasTopFullCells := by
  have key : ∀ z : Fin 5, cellGrade z = 2 → labelling (⊤ : Label.{u}) ⊤ z = ⊤ := by
    intro z
    fin_cases z <;> first | (intro _; rfl) | (intro h; exact absurd h (by decide))
  exact fun z hz ↦ key z hz

/-- **The admitted completion for the seed of `P` with itself, at either cap**, from the general
theorem. -/
theorem isLegalBelowFullGrade_admittedLayerS_P (β : Ordinal.{u}) {b : Fin 5}
    (hb : cellGrade b = 2) :
    ((seedP β).admittedLayerS rfl b).IsLegalBelowFullGrade :=
  Seed.isLegalBelowFullGrade_admittedLayerS (hasDeadLowCells_P β) (isLegal_P β)
    (hasTopFullCells_P β) hb

end GatedExtensionCounterexample

namespace CoupledGatedExtensionCounterexample

/-- **The gap**: the legal type `P α` of the coupled gate counterexample (a cell of graded index
`(univ, 1)` labelled `1`) does not have dead cells of grade `1`. -/
theorem not_hasDeadLowCells_P (α : Ordinal.{u}) (hα : 1 < α) : ¬ (P α hα).HasDeadLowCells := by
  intro h
  have := h.eq_bot (P α hα).isLawful (z := (2 : Fin 5)) rfl
  exact absurd this (by
    change (1 : Label.{u}) ≠ ⊥
    exact WithBot.coe_ne_bot)

end CoupledGatedExtensionCounterexample

end VaughtConjecture

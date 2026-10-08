/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryMarkedApex
import VaughtConjecture.Extension.SmallArityOne

/-!
# Marked caps with a donor other than the input, at the arity one

Roadmap, Layer 3, 3.1, (R6) and 3.3 (the (R4) cap); the marked layers of
`VaughtConjecture.Continuation.StableRecoverySeparateMarker` with a donor `D` that need not be the
input `T`.

Let `I` be a seed on three points with coatom types `T` (along the first coatom) and `D` (along the
second), over the common face `{0}`.  The lower layer is the canonical field layer at grade `1` of
the amalgam (`Seed.lowerFieldLayer`), with its lifts at grade `1`
(`Seed.cappedLift_lowerFieldLayer`).

**Data** (`Seed.DonorCap`): a cap and a marker on `T`, an offset `R < 2`, references on `T` for the
cells of `D`, and a bottom class on `T`.  **The requests** (`Seed.requestsD`), on the lower layer:
the cap and the marker are the copies of the cap and marker of `T`; `Z` the copies of the cells of
`D` labelled `⊥`, `F` the copies of the cells of `D` labelled in a block (neither `⊥` nor `⊤`), read
through the copies of their references at the offset `1`, and `T` the copies of the cells of `D`
labelled `⊤`.  The admission (`Seed.admD`) is capped correctness in the bottom class of the copies
of the cells of `T`, and `Seed.donorLayer` the admitted field layer at grade `2`.

**The raise from `T` into `D`** (`StageType.HasFullRaiseFrom T D b ref`): every lawful labelling
`sT` of `T` has a lawful labelling of `D` that is `⊥` at the cells of `D` labelled `⊥`, at least
`sT b` at the cells labelled `⊤`, and reads every cell labelled in a block as its reference under
`sT` (capped at `sT b`).  It holds when no cell of `D` is labelled in a block
(`StageType.hasFullRaiseFrom_of_bot_top`: the labels of `D` capped at `sT b`).

## Results

* `Seed.isLegalBelowFullGrade_donorLayer`: for `T` and `D` legal, the cap of grade `2`, `D` with
  dead cells of grade `1` (`StageType.HasDeadLowCells`), no cell of `D` labelled in a block, and
  `HasFullRaiseFrom T D b ref`, **the admitted layer with a donor is legal below the full grade**.
  The marker is any cell of `T`.  The fills: from the coatom of `T`, the lift at grade `1`
  (`Seed.exists_gradeOne`) and on `D` the raise (prescription in the bottom class with its marker
  value above the cap) or the lift of `D` from its cells of grade `1`; from the coatom of `D`, the
  lift at grade `1` and on `T` the lift of `T` from its cells of grade `1`, capped at the cap at the
  cells of grade `2`; the pieces glued by `Seed.exists_assemble`.  The agreement at grade `1`
  between the copy on `D` and the lift at grade `1` is the deadness of the cells of grade `1` of
  `D` (the common face included).
* `Seed.isLegalBelowFullGrade_donorLayer_of_bot_top`: the raise is not needed as a hypothesis
  without block labels.
* Instance: `GatedExtensionCounterexample.isLegalBelowFullGrade_donorLayer_P` (`D = T = P`, over
  the canonical lower layer).
* `CoupledGatedExtensionCounterexample.not_botTop_P`: the coupled-gate type, as a donor, has a cell
  of grade `1` labelled `1`: it is neither dead nor labelled `⊥` or `⊤`, so both hypotheses on
  `D` fail there.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- A cell reading itself at `⊥` is `⊥` in every labelling lawful below a pair above it. -/
theorem IsLawfulBelow.eq_bot_of_row_self {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {z : ι} (hz : z ∈ D.below X)
    (hrow : R.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥) : w z = ⊥ := by
  obtain ⟨-, hl, -⟩ := isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, hwit, hd⟩ := hl z hz
  have h := hd ⟨z, CellScheme.mem_below_gradedIndex _ z⟩
  simp only [min_self] at h
  rw [h, hrow, hwit.map_bot, min_bot_left]

end CellScheme.Rows

namespace StageType

variable {α : Ordinal.{u}}

/-- **The capped lift of a legal type on two points from `(univ, 1)`**: a labelling lawful below
`(univ, 1)` agreeing capped at `h` with a lawful `q` extends to a lawful labelling agreeing with `q`
capped at `h` everywhere. -/
theorem exists_lift_from_one {T : StageType.{u} α 2} (hT : T.IsLegal)
    {p : T.toCellScheme.below ((univ : Finset (Fin 2)), 1) → Label.{u}}
    (hp : T.rows.IsLawfulBelow _ p) {q : Fin T.card → Label.{u}} (hq : T.rows.IsLawful q)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hag : ∀ d, min (q d.1) h = min (p d) h) :
    ∃ r : Fin T.card → Label.{u}, T.rows.IsLawful r ∧ (∀ d, r d.1 = p d) ∧
      ∀ z, min (r z) h = min (q z) h := by
  have hX : ((univ : Finset (Fin 2)), 1) ∈ T.toCellScheme.gradedFaces :=
    ⟨T.univ_mem_faces, one_pos, by simp⟩
  have hY : ((univ : Finset (Fin 2)), 2) ∈ T.toCellScheme.gradedFaces :=
    ⟨T.univ_mem_faces, two_pos, by simp⟩
  have hl := hT.isBountiful hX hY ⟨subset_univ _, by omega⟩
  have hmem (z : Fin T.card) : z ∈ T.toCellScheme.below ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_univ _, T.grade_le z⟩
  obtain ⟨r', hr', hrq, hrp⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp hl h hh
    p (fun d ↦ q d.1) hp (hq.isLawfulBelow _) hag
  refine ⟨fun z ↦ r' ⟨z, hmem z⟩, CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall
    (X := ((univ : Finset (Fin 2)), 2)) (by convert hr' using 1) hmem, fun d ↦ hrp d,
    fun z ↦ hrq ⟨z, hmem z⟩⟩

variable (T D : StageType.{u} α 2) in
/-- **The raise from `T` into `D` at a cap `b`**, for references `ref` of the cells of `D` on `T`:
every lawful `sT` on `T` has a lawful `sD` on `D` that is `⊥` at the cells labelled `⊥`, at least
`sT b` at the cells labelled `⊤`, and reads each cell labelled in a block as its reference at the
offset `1` under the cap `sT b`. -/
def HasFullRaiseFrom (b : Fin T.card) (ref : Fin D.card → Fin T.card) : Prop :=
  ∀ sT : Fin T.card → Label.{u}, T.rows.IsLawful sT → ∃ sD : Fin D.card → Label.{u},
    D.rows.IsLawful sD ∧ (∀ z, D.label z = ⊥ → sD z = ⊥) ∧
      (∀ y, D.label y = ⊤ → sT b ≤ sD y) ∧
        ∀ f, D.label f ≠ ⊥ → D.label f ≠ ⊤ →
          min (sD f) (sT b) = min (visibilityReplace 2 1 (sT (ref f))) (sT b)

/-- **The raise when `D` has no cell labelled in a block**: the labels of `D` capped at `sT b`. -/
theorem hasFullRaiseFrom_of_bot_top {T D : StageType.{u} α 2} {b : Fin T.card}
    (hb : T.toCellScheme.grade b = 2) (hbt : ∀ z, D.label z = ⊥ ∨ D.label z = ⊤)
    (ref : Fin D.card → Fin T.card) : HasFullRaiseFrom T D b ref := by
  intro sT hsT
  have hvs : IsSelfVisible 2 (sT b) := hb ▸ hsT.orderly b
  refine ⟨fun z ↦ min (D.label z) (sT b),
    D.isLawful.min_const_of_isSelfVisible (K := 2) (fun d ↦ D.grade_le d) hvs,
    fun z hz ↦ by simp only [hz, min_bot_left], fun y hy ↦ by simp only [hy, min_top_left, le_refl],
    fun f h1 h2 ↦ ((hbt f).elim h1 h2).elim⟩

end StageType

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1}

/-! ### The coatoms of `Fin 3` -/

private theorem coatom_cases' {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x = Fin.last 2 ∧ y = Fin.castSucc (Fin.last 1)) ∨
      (x = Fin.castSucc (Fin.last 1) ∧ y = Fin.last 2) := by
  revert x y
  decide

private theorem erase_inter_erase' {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    univ.erase x ∩ univ.erase y = {0} := by
  revert x y
  decide

private theorem scope_subset_or' {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    (d : Fin I.amalgam.card) :
    I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y := by
  have h := I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d)
  rcases coatom_cases' hxy hx hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

private theorem not_univ_le_erase (x : Fin 3) (j g : ℕ) :
    ¬ ((univ : Finset (Fin 3)), j) ≤ (univ.erase x, g) :=
  fun h ↦ Finset.notMem_erase x univ (h.1 (mem_univ x))

/-- Every cell of the lower layer lies below `(univ.erase x, 2)`, `(univ, 1)` or
`(univ.erase y, 2)`. -/
theorem mem_below_three {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    (e : Fin I.lowerFieldLayer.card) :
    e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
      e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2) := by
  induction e using Fin.addCases with
  | right i =>
    exact .inr (.inl (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).le)
  | left d =>
    have hsc : I.lowerFieldLayer.toCellScheme.scope (Fin.castAdd _ d) =
        I.amalgam.toCellScheme.scope d :=
      Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d
    have hg := I.lowerFieldLayer_grade_le (Fin.castAdd _ d)
    rcases scope_subset_or' hxy hx hy d with hd | hd
    · exact .inl ⟨(hsc ▸ hd : I.lowerFieldLayer.toCellScheme.scope (Fin.castAdd _ d) ⊆ _), hg⟩
    · exact .inr (.inr ⟨(hsc ▸ hd :
        I.lowerFieldLayer.toCellScheme.scope (Fin.castAdd _ d) ⊆ _), hg⟩)

/-- A cell below the other coatom and on the boundary has grade at most `1`. -/
theorem grade_le_one_of_boundary {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    {e : Fin I.lowerFieldLayer.card}
    (he : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2))
    (hb : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
      e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)) :
    I.lowerFieldLayer.toCellScheme.grade e ≤ 1 := by
  rcases hb with hb | hb
  · have hsub : I.lowerFieldLayer.toCellScheme.scope e ⊆ {0} :=
      (subset_inter hb.1 he.1).trans (erase_inter_erase' hxy hx hy).le
    exact (I.isWellFormed_lowerFieldLayer.isWellFormed.grade_le_card e).trans
      ((card_le_card hsub).trans (by simp))
  · exact hb.2

/-! ### Copies of the cells of a coatom type -/

/-- **Lawfulness through a coatom**: a labelling of the lower layer is lawful below
`(univ.erase y, k)` exactly when its copy on the coatom type along `f` is lawful below
`(univ, k)`. -/
theorem isLawfulBelow_coatom_iff {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) {y : Fin 3} (hy : univ.map f = univ.erase y) (k : ℕ)
    {v : Fin I.lowerFieldLayer.card → Label.{u}} :
    I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase y, k) (fun d ↦ v d) ↔
      E.rows.IsLawfulBelow ((univ : Finset (Fin 2)), k)
        (fun i ↦ v (Fin.castAdd _ (StageType.faceCell hE i))) := by
  have h1 := Scheme.isLawfulBelow_appendFullCells_iff (S := I.amalgam.toScheme) (k := 1)
    (M := (I.amalgam.toScheme.catalogue 1).card)
    (r := fun i ↦ I.amalgam.toScheme.fieldRow 1 (I.amalgam.toScheme.catalogueEntry 1 i))
    (h := I.not_univ_le 1) (not_univ_le_erase y 1 k) (v := v)
  have hpair : ((univ.erase y, k) : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map f) id ((univ : Finset (Fin 2)), k) := by
    simp only [Prod.map, id, hy]
  rw [h1, hpair]
  exact (Scheme.isLawfulBelow_faceCell_iff (StageType.comap_toScheme_of_restrictFace hE)
    (univ, k) (fun d ↦ v (Fin.castAdd _ d))).symm

/-- A copy of a cell of a coatom type lies below that coatom at grade `2`. -/
theorem faceCell_mem_below {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) {y : Fin 3} (hy : univ.map f = univ.erase y)
    (i : Fin E.card) :
    Fin.castAdd _ (StageType.faceCell hE i) ∈
      I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2) := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨(StageType.scope_faceCell hE i).trans_subset
    ((map_subset_map.mpr (subset_univ _)).trans hy.subset),
    (StageType.grade_faceCell hE i).trans_le (E.grade_le i)⟩

/-- A cell below a coatom at grade `2` is a copy of a cell of the coatom type. -/
theorem exists_faceCell_of_mem_below {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) {y : Fin 3} (hy : univ.map f = univ.erase y)
    {d : Fin I.lowerFieldLayer.card}
    (hd : d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2)) :
    ∃ i, d = Fin.castAdd _ (StageType.faceCell hE i) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hd.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ y))
  | left e =>
    have h : I.amalgam.toCellScheme.scope e ⊆ univ.map f := by
      have h' := hd.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [hy]
      exact h'
    obtain ⟨i, hi⟩ := I.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace hE) (d := e)
      (by simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]; exact h)
    exact ⟨i, by rw [← hi]; rfl⟩

/-- The copies of the cells of a coatom type are distinct. -/
theorem faceCell_castAdd_injective {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2}
    (hE : restrictFace f I.amalgam = some E) :
    Function.Injective fun i ↦
      (Fin.castAdd _ (StageType.faceCell hE i) : Fin I.lowerFieldLayer.card) :=
  fun _ _ h ↦ I.amalgam.toScheme.faceCell_injective
    (StageType.comap_toScheme_of_restrictFace hE) (Fin.castAdd_injective _ _ h)

/-! ### The fill: the lift at grade `1` and the assembly -/

/-- **The lift at grade `1` of a prescription on a coatom**: a labelling lawful below
`(univ.erase x, 2)` agreeing capped at `h` with a lawful `a` there extends to a labelling lawful
below `(univ.erase x, 2)` and below `(univ, 1)`, equal to it below `(univ.erase x, 2)` and agreeing
with `a` capped at `h` below `(univ, 1)`. -/
theorem exists_gradeOne {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase x, 2) fun d ↦ f d)
    {a : Fin I.lowerFieldLayer.card → Label.{u}} (ha : I.lowerFieldLayer.rows.IsLawful a)
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2),
      min (f d) h = min (a d) h) :
    ∃ w : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase x, 2) (fun d ↦ w d) ∧
      I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) (fun d ↦ w d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2), w d = f d) ∧
      ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1), min (w d) h = min (a d) h := by
  classical
  have hx1 : ((univ.erase x, 1) : Finset (Fin 3) × ℕ) ≤ (univ.erase x, 2) :=
    ⟨subset_rfl, one_le_two⟩
  obtain ⟨q₁, hq₁, hq₁a, hq₁f⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp
    (I.cappedLift_lowerFieldLayer hxy hx hy) h (hh.mono one_le_two)
    (fun d ↦ f d.1) (fun d ↦ a d.1) (hf.mono hx1) (ha.isLawfulBelow _)
    fun d ↦ (hfa d.1 ⟨d.2.1, d.2.2.trans one_le_two⟩).symm
  have hlow (d) (hd : d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2))
      (hd1 : d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)) :
      d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 1) := ⟨hd.1, hd1.2⟩
  have hw (d) (hd : d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2)) :
      (if h1 : d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) then q₁ ⟨d, h1⟩ else f d) =
        f d := by
    split_ifs with h1
    · exact hq₁f ⟨d, hlow d hd h1⟩
    · rfl
  refine ⟨fun d ↦ if h1 : d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) then q₁ ⟨d, h1⟩
    else f d, ?_, ?_, hw, fun d hd ↦ ?_⟩
  · convert hf using 1
    exact funext fun d ↦ hw d.1 d.2
  · convert hq₁ using 1
    exact funext fun d ↦ dite_eq_left d.2
  · exact (congrArg (min · h) (dite_eq_left hd)).trans (hq₁a ⟨d, hd⟩)

/-- **Assembly**: a labelling lawful below `(univ.erase x, 2)` and below `(univ, 1)`, and a lawful
labelling `s` of the other coatom type agreeing with it at the cells of grade `1`, give a lawful
labelling of the lower layer equal to the first on the boundary and to `s` on the copies. -/
theorem exists_assemble {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    {f : Fin 2 ↪ Fin 3} {E : StageType.{u} α 2} (hE : restrictFace f I.amalgam = some E)
    (hfy : univ.map f = univ.erase y) {w : Fin I.lowerFieldLayer.card → Label.{u}}
    (hwU : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase x, 2) (fun d ↦ w d))
    (hwV : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) (fun d ↦ w d))
    {s : Fin E.card → Label.{u}} (hs : E.rows.IsLawful s)
    (hsw : ∀ i, E.toCellScheme.grade i = 1 → s i = w (Fin.castAdd _ (StageType.faceCell hE i))) :
    ∃ g : Fin I.lowerFieldLayer.card → Label.{u}, I.lowerFieldLayer.rows.IsLawful g ∧
      (∀ e, e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) → g e = w e) ∧
      ∀ i, g (Fin.castAdd _ (StageType.faceCell hE i)) = s i := by
  classical
  set S : Fin I.lowerFieldLayer.card → Label.{u} := fun e ↦
    if he : ∃ i, e = Fin.castAdd _ (StageType.faceCell hE i) then s he.choose else ⊥ with hSdef
  have hS (i : Fin E.card) : S (Fin.castAdd _ (StageType.faceCell hE i)) = s i := by
    have he : ∃ j, (Fin.castAdd _ (StageType.faceCell hE i) : Fin I.lowerFieldLayer.card) =
        Fin.castAdd _ (StageType.faceCell hE j) := ⟨i, rfl⟩
    rw [hSdef]
    exact (dite_eq_left he).trans
      (congrArg s (faceCell_castAdd_injective hE he.choose_spec).symm)
  set g : Fin I.lowerFieldLayer.card → Label.{u} := fun e ↦
    if e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
      e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) then w e else S e with hgdef
  have hgb (e) (hb : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
      e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)) : g e = w e := by
    rw [hgdef]
    exact ite_eq_left hb
  have hgs (i : Fin E.card) : g (Fin.castAdd _ (StageType.faceCell hE i)) = s i := by
    by_cases hb : Fin.castAdd _ (StageType.faceCell hE i) ∈
        I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
      Fin.castAdd _ (StageType.faceCell hE i) ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgb _ hb]
      have hg1 := grade_le_one_of_boundary hxy hx hy (faceCell_mem_below hE hfy i) hb
      have hgE : E.toCellScheme.grade i = 1 := by
        have hge : I.lowerFieldLayer.toCellScheme.grade
            (Fin.castAdd _ (StageType.faceCell hE i)) = E.toCellScheme.grade i :=
          (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
            (StageType.grade_faceCell hE i)
        have h0 : 0 < E.toCellScheme.grade i :=
          (E.isWellFormed.isWellFormed.gradedIndex_mem i).2.1
        omega
      exact (hsw i hgE).symm
    · rw [hgdef]
      exact (ite_eq_right hb).trans (hS i)
  have hW : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase y, 2) (fun d ↦ g d) := by
    refine (isLawfulBelow_coatom_iff hE hfy 2).mpr ?_
    convert hs.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
    exact funext fun i ↦ hgs i.1
  have hlaw : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 2) (fun d ↦ g d) :=
    CellScheme.Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, 2)) (V := (univ, 1))
      (W := (univ.erase y, 2)) (by convert hwU using 1; exact funext fun e ↦ hgb e.1 (.inl e.2))
      (by convert hwV using 1; exact funext fun e ↦ hgb e.1 (.inr e.2)) hW
      fun e _ ↦ mem_below_three hxy hx hy e
  exact ⟨g, CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall hlaw
    (fun d ↦ ⟨subset_univ _, I.lowerFieldLayer_grade_le d⟩), hgb, hgs⟩

/-! ### The data and the requests -/

variable (I) in
/-- **Marked-cap data with a donor**: a cap and a marker on `T = I.left`, an offset `R < 2`,
references on `T` for the cells of `D = I.right`, and a bottom class on `T`. -/
structure DonorCap where
  /-- The cap, a cell of `T`. -/
  cap : Fin I.left.card
  /-- The marker, a cell of `T`. -/
  marker : Fin I.left.card
  /-- The marker offset. -/
  R : ℕ
  /-- The marker offset is below `2`. -/
  R_lt_two : R < 2
  /-- The references of the cells of `D`, on `T`. -/
  ref : Fin I.right.card → Fin I.left.card
  /-- The bottom class on `T`. -/
  botCells : Set (Fin I.left.card)

variable (I) in
/-- The copy of a cell of `T` in the lower layer. -/
noncomputable abbrev privCell (z : Fin I.left.card) : Fin I.lowerFieldLayer.card :=
  Fin.castAdd _ (StageType.faceCell I.restrictFace_left z)

variable (I) in
/-- The copy of a cell of `D` in the lower layer. -/
noncomputable abbrev donCell (z : Fin I.right.card) : Fin I.lowerFieldLayer.card :=
  Fin.castAdd _ (StageType.faceCell I.restrictFace_right z)

namespace DonorCap

variable (c : I.DonorCap)

/-- The **marker value** of a labelling of `T`. -/
noncomputable def value (s : Fin I.left.card → Label.{u}) : Label.{u} :=
  min (visibilityReplace 2 c.R (s c.marker)) (s c.cap)

/-- A labelling of `T` is **in the bottom class** when it is `⊥` exactly at the bottom cells. -/
def InClass (s : Fin I.left.card → Label.{u}) : Prop := ∀ z, s z = ⊥ ↔ z ∈ c.botCells

variable {c}

theorem value_le_cap (s : Fin I.left.card → Label.{u}) : c.value s ≤ s c.cap := min_le_right _ _

theorem min_value_eq {h : Label.{u}} (hh : IsSelfVisible 2 h) {s t : Fin I.left.card → Label.{u}}
    (hst : ∀ z, min (s z) h = min (t z) h) : min (c.value s) h = min (c.value t) h := by
  unfold value
  rw [inf_inf_distrib_right, inf_inf_distrib_right (visibilityReplace 2 c.R (t c.marker)),
    Label.min_visibilityReplace_two_eq hh (by have := c.R_lt_two; omega) (hst c.marker),
    hst c.cap]

theorem InClass.of_min_eq {s t : Fin I.left.card → Label.{u}} {h : Label.{u}} (hh : ⊥ < h)
    (hst : ∀ z, min (s z) h = min (t z) h) (hs : c.InClass s) : c.InClass t := by
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

end DonorCap

variable (I) in
/-- **The (R4) cap requests with a donor** on the lower layer. -/
noncomputable def requestsD (c : I.DonorCap) : CapRequests (Fin I.lowerFieldLayer.card) where
  cap := I.privCell c.cap
  N := 2
  R := c.R
  R_lt_N := c.R_lt_two
  Z := I.donCell '' {z | I.right.label z = ⊥}
  F := I.donCell '' {f | I.right.label f ≠ ⊥ ∧ I.right.label f ≠ ⊤}
  T := I.donCell '' {y | I.right.label y = ⊤}
  ref d := by
    classical
    exact if h : ∃ i, I.donCell i = d then I.privCell (c.ref h.choose) else d
  off _ := 1
  marker := I.privCell c.marker

variable (I) in
/-- **The admission with a donor**: capped correctness in the bottom class of the copies of the
cells of `T`. -/
def admD (c : I.DonorCap) (e : Fin I.lowerFieldLayer.card → Label.{u}) : Prop :=
  (I.requestsD c).Admits (Set.range I.privCell) (I.privCell '' c.botCells) e

variable (I) in
/-- **The admitted layer with a donor** at the grade `2` over the lower layer. -/
noncomputable abbrev donorLayer (c : I.DonorCap) : Scheme.{u} 3 :=
  I.lowerFieldLayer.admittedFieldLayer 2 (I.admD c) I.not_univ_two_le_lowerFieldLayer

variable {c : I.DonorCap}

theorem privCell_injective : Function.Injective I.privCell :=
  faceCell_castAdd_injective I.restrictFace_left

theorem inBottomClass_iffD {e : Fin I.lowerFieldLayer.card → Label.{u}} :
    InBottomClass (Set.range I.privCell) (I.privCell '' c.botCells) e ↔
      c.InClass fun z ↦ e (I.privCell z) := by
  have key (z : Fin I.left.card) : I.privCell z ∈ I.privCell '' c.botCells ↔ z ∈ c.botCells :=
    ⟨fun ⟨z', hz', he⟩ ↦ privCell_injective he ▸ hz', fun hz ↦ ⟨z, hz, rfl⟩⟩
  constructor
  · intro hcl z
    exact (hcl _ ⟨z, rfl⟩).trans (key z)
  · rintro hcl _ ⟨z, rfl⟩
    exact (hcl z).trans (key z).symm

/-- **Correctness with a donor without block labels**: `⊥` at the copies of the cells of `D`
labelled `⊥` under the cap, and at least the marker value at those labelled `⊤`. -/
theorem isCorrect_requestsD (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (hZ : ∀ z, I.right.label z = ⊥ → min (g (I.donCell z)) (g (I.privCell c.cap)) = ⊥)
    (hT : ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ g (I.privCell z)) ≤ g (I.donCell y)) :
    (I.requestsD c).IsCorrect g where
  eq_bot := by
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  eq_refValue := by
    rintro _ ⟨f, ⟨h1, h2⟩, rfl⟩
    exact ((hbt f).elim h1 h2).elim
  markerValue_le := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_min (hT y hy) (DonorCap.value_le_cap (c := c) fun z ↦ g (I.privCell z))

theorem eq_bot_of_isCorrectD {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (hc : (I.requestsD c).IsCorrect g) {z : Fin I.right.card} (hz : I.right.label z = ⊥) :
    min (g (I.donCell z)) (g (I.privCell c.cap)) = ⊥ :=
  hc.eq_bot _ ⟨z, hz, rfl⟩

theorem le_of_isCorrectD {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (hc : (I.requestsD c).IsCorrect g) {y : Fin I.right.card} (hy : I.right.label y = ⊤) :
    c.value (fun z ↦ g (I.privCell z)) ≤ g (I.donCell y) :=
  (hc.markerValue_le _ ⟨y, hy, rfl⟩).trans (min_le_left _ _)

/-- **The orbit code of an admitted state is admitted.** -/
theorem admD_orbitCode {W : Fin I.lowerFieldLayer.card → Label.{u}} (hadm : I.admD c W) :
    I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsp : I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W = W :=
    funext fun d ↦ CellScheme.splice_of_le (I.lowerFieldLayer_grade_le d)
  rw [hsp]
  have hcode : orbitCode 2 W = orbitMap 2 W ∘ W := funext fun d ↦ orbitCode_apply d
  intro hcl
  have hcl' : InBottomClass (Set.range I.privCell) (I.privCell '' c.botCells) W := by
    intro d hd
    rw [← hcl d hd, hcode, Function.comp_apply, orbitMap_eq_bot_iff]
  rw [hcode]
  exact (hadm hcl').comp (isWitness_orbitMap 2 W) le_rfl fun _ _ ↦ by
    change 1 ≤ 2
    omega

theorem admD_of_not {W : Fin I.lowerFieldLayer.card → Label.{u}}
    (hn : ¬ c.InClass fun z ↦ W (I.privCell z)) : I.admD c W :=
  fun hcl ↦ absurd (inBottomClass_iffD.mp hcl) hn

/-- The admission of a lawful state whose copies satisfy the requests in the bottom class. -/
theorem admD_orbitCode_of (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    {g : Fin I.lowerFieldLayer.card → Label.{u}}
    (h4 : c.InClass (fun z ↦ g (I.privCell z)) →
      (∀ z, I.right.label z = ⊥ → min (g (I.donCell z)) (g (I.privCell c.cap)) = ⊥) ∧
        ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ g (I.privCell z)) ≤ g (I.donCell y)) :
    I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  by_cases hcl : c.InClass fun z ↦ g (I.privCell z)
  · exact admD_orbitCode (isCorrect_requestsD hbt (h4 hcl).1 (h4 hcl).2).admits
  · exact admD_orbitCode (admD_of_not hcl)

/-! ### The copies of a lawful labelling -/

theorem isLawful_privOf {v : Fin I.lowerFieldLayer.card → Label.{u}}
    (hv : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) fun d ↦ v d) :
    I.left.rows.IsLawful fun z ↦ v (I.privCell z) :=
  ((isLawfulBelow_coatom_iff I.restrictFace_left (Coatom.univ_map_left (m := 1)) 2).mp hv).isLawful
    fun d ↦ ⟨subset_univ _, I.left.grade_le d⟩

theorem isLawful_donOf {v : Fin I.lowerFieldLayer.card → Label.{u}}
    (hv : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      fun d ↦ v d) :
    I.right.rows.IsLawful fun z ↦ v (I.donCell z) :=
  ((isLawfulBelow_coatom_iff I.restrictFace_right (Coatom.univ_map_right (m := 1)) 2).mp
    hv).isLawful fun d ↦ ⟨subset_univ _, I.right.grade_le d⟩

theorem privCell_mem_below (z : Fin I.left.card) :
    I.privCell z ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2) :=
  faceCell_mem_below I.restrictFace_left (Coatom.univ_map_left (m := 1)) z

theorem donCell_mem_below (z : Fin I.right.card) :
    I.donCell z ∈
      I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2) :=
  faceCell_mem_below I.restrictFace_right (Coatom.univ_map_right (m := 1)) z

/-- A labelling lawful below `(univ, 1)` is `⊥` at the copies of the dead cells of `D`. -/
theorem eq_bot_donCell_of_dead (hd : I.right.HasDeadLowCells)
    {v : Fin I.lowerFieldLayer.card → Label.{u}}
    (hv : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) fun d ↦ v d) {z : Fin I.right.card}
    (hz : I.right.toCellScheme.grade z = 1) : v (I.donCell z) = ⊥ := by
  have h1 := (isLawfulBelow_coatom_iff I.restrictFace_right (Coatom.univ_map_right (m := 1)) 1).mp
    (hv.mono (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1)) ⟨subset_univ _, le_rfl⟩)
  exact h1.eq_bot_of_row_self (w := fun i ↦ v (I.donCell i)) ⟨subset_univ _, hz.le⟩ (hd z hz)

/-- A labelling lawful below `(univ, 1)` extends at the copies of the cells of grade `1` of `T`. -/
theorem isLawfulBelow_privOf_one {v : Fin I.lowerFieldLayer.card → Label.{u}}
    (hv : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) fun d ↦ v d) :
    I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) fun i ↦ v (I.privCell i.1) :=
  (isLawfulBelow_coatom_iff I.restrictFace_left (Coatom.univ_map_left (m := 1)) 1).mp
    (hv.mono (X := (univ.erase (Fin.last 2), 1)) ⟨subset_univ _, le_rfl⟩)

theorem privCell_mem_below_one {z : Fin I.left.card} (hz : I.left.toCellScheme.grade z ≤ 1) :
    I.privCell z ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  exact ⟨subset_univ _, (StageType.grade_faceCell I.restrictFace_left z).trans_le hz⟩

/-! ### The provisions -/

private theorem hxyL : (Fin.last 2 : Fin 3) ≠ Fin.castSucc (Fin.last 1) := by decide
private theorem hxL : (Fin.last 2 : Fin 3) ≠ 0 := by decide
private theorem hyL : (Fin.castSucc (Fin.last 1) : Fin 3) ≠ 0 := by decide

/-- **The lift provision at a positive cap from the coatom of `T`.**  The copy on `D` is the raise
from `T` when the prescription is in the bottom class with its marker value above `h`, and
otherwise the lift of `D` from its cells of grade `1` (all `⊥`) along the entry. -/
theorem capProvisionD_left (hD : I.right.IsLegal) (hd : I.right.HasDeadLowCells)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hraise : I.left.HasFullRaiseFrom I.right c.cap c.ref)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin I.lowerFieldLayer.card → Label.{u}} (ha : I.lowerFieldLayer.rows.IsLawful a)
    (hA : I.admD c a) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      (∀ d, I.lowerFieldLayer.toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have hsT := isLawful_privOf hf
  have heD := isLawful_donOf (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  have hagT (z : Fin I.left.card) : min (f (I.privCell z)) h = min (a (I.privCell z)) h :=
    hfa _ (privCell_mem_below z)
  have hm := DonorCap.min_value_eq (c := c) hh hagT
  obtain ⟨w, hwU, hwV, hwf, hwa⟩ := exists_gradeOne hxyL hxL hyL hh hf ha hfa
  have heD1 (i : Fin I.right.card) (hi : I.right.toCellScheme.grade i = 1) :
      a (I.donCell i) = ⊥ := hd.eq_bot heD hi
  obtain ⟨sD, hsD, hsDa, hsDT⟩ : ∃ sD : Fin I.right.card → Label.{u}, I.right.rows.IsLawful sD ∧
      (∀ i, min (sD i) h = min (a (I.donCell i)) h) ∧
      (c.InClass (fun z ↦ f (I.privCell z)) →
        (∀ z, I.right.label z = ⊥ → min (sD z) (f (I.privCell c.cap)) = ⊥) ∧
          ∀ y, I.right.label y = ⊤ → c.value (fun z ↦ f (I.privCell z)) ≤ sD y) := by
    by_cases hc : c.InClass (fun z ↦ f (I.privCell z)) ∧ h < c.value (fun z ↦ f (I.privCell z))
    · have hclE := hc.1.of_min_eq hbh hagT
      have hcorr := hA (inBottomClass_iffD.mpr hclE)
      have hma : h ≤ c.value (fun z ↦ a (I.privCell z)) := by
        have e1 := hm
        rw [min_eq_right hc.2.le] at e1
        exact min_eq_right_iff.mp e1.symm
      have hcap : h ≤ a (I.privCell c.cap) := hma.trans (DonorCap.value_le_cap _)
      obtain ⟨sD, hsD, hZ, hTT, -⟩ := hraise _ hsT
      refine ⟨sD, hsD, fun i ↦ ?_, fun _ ↦ ⟨fun z hz ↦ by rw [hZ z hz, min_bot_left],
        fun y hy ↦ (DonorCap.value_le_cap _).trans (hTT y hy)⟩⟩
      rcases hbt i with hi | hi
      · have h0 := eq_bot_of_isCorrectD hcorr hi
        have hai : a (I.donCell i) = ⊥ := by
          rcases min_eq_bot.mp h0 with h' | h'
          · exact h'
          · exact absurd h' (ne_bot_of_gt (hbh.trans_le hcap))
        rw [hZ i hi, hai]
      · have h1 : h ≤ sD i := hc.2.le.trans ((DonorCap.value_le_cap _).trans (hTT i hi))
        have h2 : h ≤ a (I.donCell i) := hma.trans (le_of_isCorrectD hcorr hi)
        rw [min_eq_right h1, min_eq_right h2]
    · obtain ⟨r, hr, -, hra⟩ := StageType.exists_lift_one_two hD (p := fun _ ↦ ⊥)
        (q := fun i ↦ a (I.donCell i)) (CellScheme.Rows.isLawful_const_bot (R := I.right.rows))
        heD hh
        fun z hz ↦ by
          show min ⊥ h = min (a (I.donCell z)) h
          rw [heD1 z hz]
      refine ⟨r, hr, hra, fun hcl ↦ ⟨fun z hz ↦ ?_, fun y hy ↦ ?_⟩⟩
      · have hclE := hcl.of_min_eq hbh hagT
        have h0 := eq_bot_of_isCorrectD (hA (inBottomClass_iffD.mpr hclE)) hz
        rcases min_eq_bot.mp h0 with h' | h'
        · have e := hra z
          rw [h', min_bot_left] at e
          rw [(min_eq_bot.mp e).resolve_right hbh.ne', min_bot_left]
        · have e := hagT c.cap
          rw [h', min_bot_left] at e
          rw [(min_eq_bot.mp e).resolve_right hbh.ne', min_bot_right]
      · have hle : c.value (fun z ↦ f (I.privCell z)) ≤ h := not_lt.mp fun hlt ↦ hc ⟨hcl, hlt⟩
        have hclE := hcl.of_min_eq hbh hagT
        calc c.value (fun z ↦ f (I.privCell z))
            = min (c.value (fun z ↦ f (I.privCell z))) h := (min_eq_left hle).symm
          _ = min (c.value fun z ↦ a (I.privCell z)) h := hm
          _ ≤ min (a (I.donCell y)) h :=
            min_le_min_right _ (le_of_isCorrectD (hA (inBottomClass_iffD.mpr hclE)) hy)
          _ = min (r y) h := (hra y).symm
          _ ≤ r y := min_le_left _ _
  have hsw (i : Fin I.right.card) (hi : I.right.toCellScheme.grade i = 1) :
      sD i = w (I.donCell i) :=
    (hd.eq_bot hsD hi).trans (eq_bot_donCell_of_dead hd hwV hi).symm
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyL hxL hyL I.restrictFace_right
    (Coatom.univ_map_right (m := 1)) hwU hwV hsD hsw
  have hpriv (z : Fin I.left.card) : g (I.privCell z) = f (I.privCell z) :=
    (hgw _ (.inl (privCell_mem_below z))).trans (hwf _ (privCell_mem_below z))
  refine ⟨g, hg.isLawfulBelow _, fun d hd' ↦ (hgw d (.inl hd')).trans (hwf d hd'),
    fun d _ ↦ ?_, admD_orbitCode_of hbt fun hcl ↦ ?_⟩
  · by_cases hb : d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2) ∨
        d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgw d hb]
      rcases hb with hb | hb
      · rw [hwf d hb]
        exact hfa d hb
      · exact hwa d hb
    · obtain ⟨i, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_right
        (Coatom.univ_map_right (m := 1))
        (((mem_below_three hxyL hxL hyL d).resolve_left fun h' ↦ hb (.inl h')).resolve_left
          fun h' ↦ hb (.inr h'))
      rw [hgs]
      exact hsDa i
  · have e : (fun z ↦ g (I.privCell z)) = fun z ↦ f (I.privCell z) := funext hpriv
    rw [e] at hcl ⊢
    obtain ⟨hZ, hTT⟩ := hsDT hcl
    refine ⟨fun z hz ↦ ?_, fun y hy ↦ ?_⟩
    · rw [hgs, hpriv]
      exact hZ z hz
    · rw [hgs]
      exact hTT y hy

/-- **The lift provision at the cap `⊥` from the coatom of `T`**: the raise from `T`. -/
theorem botProvisionD_left (hd : I.right.HasDeadLowCells)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hraise : I.left.HasFullRaiseFrom I.right c.cap c.ref)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_privOf hf
  obtain ⟨w, hwU, hwV, hwf, -⟩ := exists_gradeOne hxyL hxL hyL (isSelfVisible_bot 2) hf
    (CellScheme.Rows.isLawful_const_bot (R := I.lowerFieldLayer.rows))
    fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  obtain ⟨sD, hsD, hZ, hTT, -⟩ := hraise _ hsT
  have hsw (i : Fin I.right.card) (hi : I.right.toCellScheme.grade i = 1) :
      sD i = w (I.donCell i) :=
    (hd.eq_bot hsD hi).trans (eq_bot_donCell_of_dead hd hwV hi).symm
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyL hxL hyL I.restrictFace_right
    (Coatom.univ_map_right (m := 1)) hwU hwV hsD hsw
  have hpriv (z : Fin I.left.card) : g (I.privCell z) = f (I.privCell z) :=
    (hgw _ (.inl (privCell_mem_below z))).trans (hwf _ (privCell_mem_below z))
  refine ⟨g, hg.isLawfulBelow _, fun d hd' ↦ (hgw d (.inl hd')).trans (hwf d hd'),
    admD_orbitCode_of hbt fun _ ↦ ⟨fun z hz ↦ ?_, fun y hy ↦ ?_⟩⟩
  · rw [hgs, hZ z hz, min_bot_left]
  · have e : (fun z ↦ g (I.privCell z)) = fun z ↦ f (I.privCell z) := funext hpriv
    rw [e, hgs]
    exact (DonorCap.value_le_cap _).trans (hTT y hy)

/-- **The lift provision at a positive cap from the coatom of `D`**: the copy on `T` is the lift
of `T` from its cells of grade `1` along the entry, capped at `h` at the cells of grade `2`. -/
theorem capProvisionD_right (hT : I.left.IsLegal)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hb : I.left.toCellScheme.grade c.cap = 2)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin I.lowerFieldLayer.card → Label.{u}} (ha : I.lowerFieldLayer.rows.IsLawful a)
    (hA : I.admD c a) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      (∀ d, I.lowerFieldLayer.toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  classical
  have heT := isLawful_privOf (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hagD (i : Fin I.right.card) : min (f (I.donCell i)) h = min (a (I.donCell i)) h :=
    hfa _ (donCell_mem_below i)
  obtain ⟨w, hwU, hwV, hwf, hwa⟩ := exists_gradeOne hxyL.symm hyL hxL hh hf ha hfa
  obtain ⟨r, hr, hrp, hra⟩ := StageType.exists_lift_from_one hT (isLawfulBelow_privOf_one hwV)
    heT hh fun d ↦ (hwa _ (privCell_mem_below_one d.2.2)).symm
  have hsT := StageType.isLawful_capTwo hr hh
  have hsw (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i = 1) :
      (if I.left.toCellScheme.grade i = 2 then min (r i) h else r i) = w (I.privCell i) := by
    simp only [show I.left.toCellScheme.grade i ≠ 2 by omega, ↓reduceIte]
    exact hrp ⟨i, ⟨subset_univ _, hi.le⟩⟩
  have hsTa (i : Fin I.left.card) :
      min (if I.left.toCellScheme.grade i = 2 then min (r i) h else r i) h =
        min (a (I.privCell i)) h := by
    split_ifs
    · rw [min_assoc, min_self, hra]
    · exact hra i
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyL.symm hyL hxL I.restrictFace_left
    (Coatom.univ_map_left (m := 1)) hwU hwV hsT hsw
  have hdon (z : Fin I.right.card) : g (I.donCell z) = f (I.donCell z) :=
    (hgw _ (.inl (donCell_mem_below z))).trans (hwf _ (donCell_mem_below z))
  refine ⟨g, hg.isLawfulBelow _, fun d hd' ↦ (hgw d (.inl hd')).trans (hwf d hd'),
    fun d _ ↦ ?_, admD_orbitCode_of hbt fun hcl ↦ ?_⟩
  · by_cases hb' : d ∈ I.lowerFieldLayer.toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2) ∨
        d ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgw d hb']
      rcases hb' with hb' | hb'
      · rw [hwf d hb']
        exact hfa d hb'
      · exact hwa d hb'
    · obtain ⟨i, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
        (Coatom.univ_map_left (m := 1))
        (((mem_below_three hxyL.symm hyL hxL d).resolve_left fun h' ↦ hb' (.inl h')).resolve_left
          fun h' ↦ hb' (.inr h'))
      rw [hgs]
      exact hsTa i
  · have e : (fun z ↦ g (I.privCell z)) =
        fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) h else r z := funext hgs
    rw [e] at hcl ⊢
    have hclE := hcl.of_min_eq hbh hsTa
    have hcorr := hA (inBottomClass_iffD.mpr hclE)
    have hcapL : (if I.left.toCellScheme.grade c.cap = 2 then min (r c.cap) h else r c.cap) ≤ h :=
      by simp only [hb, ↓reduceIte]; exact min_le_right _ _
    have hcapE : (if I.left.toCellScheme.grade c.cap = 2 then min (r c.cap) h else r c.cap) ≤
        a (I.privCell c.cap) := by
      have e1 := hsTa c.cap
      rw [min_eq_left hcapL] at e1
      exact e1.symm ▸ min_le_left _ _
    refine ⟨fun z hz ↦ ?_, fun y hy ↦ ?_⟩
    · rw [hdon, hgs]
      refine le_bot_iff.mp ?_
      calc _ = min (min (f (I.donCell z)) h)
            (if I.left.toCellScheme.grade c.cap = 2 then min (r c.cap) h else r c.cap) := by
            rw [min_assoc, min_eq_right hcapL]
        _ = min (min (a (I.donCell z)) h)
            (if I.left.toCellScheme.grade c.cap = 2 then min (r c.cap) h else r c.cap) := by
            rw [hagD z]
        _ = min (a (I.donCell z))
            (if I.left.toCellScheme.grade c.cap = 2 then min (r c.cap) h else r c.cap) := by
            rw [min_assoc, min_eq_right hcapL]
        _ ≤ min (a (I.donCell z)) (a (I.privCell c.cap)) := min_le_min_left _ hcapE
        _ = ⊥ := eq_bot_of_isCorrectD hcorr hz
        _ ≤ ⊥ := le_rfl
    · rw [hdon]
      have hle := (DonorCap.value_le_cap (c := c)
        (fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) h else r z)).trans hcapL
      calc _ = min (c.value fun z ↦
              if I.left.toCellScheme.grade z = 2 then min (r z) h else r z) h :=
            (min_eq_left hle).symm
        _ = min (c.value fun z ↦ a (I.privCell z)) h := DonorCap.min_value_eq hh hsTa
        _ ≤ min (a (I.donCell y)) h := min_le_min_right _ (le_of_isCorrectD hcorr hy)
        _ = min (f (I.donCell y)) h := (hagD y).symm
        _ ≤ f (I.donCell y) := min_le_left _ _

/-- **The lift provision at the cap `⊥` from the coatom of `D`**: the copy on `T` is a lawful
extension with its cells of grade `2` capped at `⊥`. -/
theorem botProvisionD_right (hT : I.left.IsLegal)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hb : I.left.toCellScheme.grade c.cap = 2) {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      I.admD c (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  obtain ⟨w, hwU, hwV, hwf, -⟩ := exists_gradeOne hxyL.symm hyL hxL (isSelfVisible_bot 2) hf
    (CellScheme.Rows.isLawful_const_bot (R := I.lowerFieldLayer.rows))
    fun _ _ ↦ by rw [min_bot_right, min_bot_right]
  obtain ⟨r, hr, hrp, -⟩ := StageType.exists_lift_from_one hT (isLawfulBelow_privOf_one hwV)
    (CellScheme.Rows.isLawful_const_bot (R := I.left.rows)) (isSelfVisible_bot 2)
    fun _ ↦ by rw [min_bot_right, min_bot_right]
  have hsT := StageType.isLawful_capTwo hr (isSelfVisible_bot 2)
  have hsw (i : Fin I.left.card) (hi : I.left.toCellScheme.grade i = 1) :
      (if I.left.toCellScheme.grade i = 2 then min (r i) ⊥ else r i) = w (I.privCell i) := by
    simp only [show I.left.toCellScheme.grade i ≠ 2 by omega, ↓reduceIte]
    exact hrp ⟨i, ⟨subset_univ _, hi.le⟩⟩
  obtain ⟨g, hg, hgw, hgs⟩ := exists_assemble hxyL.symm hyL hxL I.restrictFace_left
    (Coatom.univ_map_left (m := 1)) hwU hwV hsT hsw
  have hcap : g (I.privCell c.cap) = ⊥ := by
    rw [hgs]
    simp only [hb, ↓reduceIte, min_bot_right]
  refine ⟨g, hg.isLawfulBelow _, fun d hd' ↦ (hgw d (.inl hd')).trans (hwf d hd'),
    admD_orbitCode_of hbt fun _ ↦ ⟨fun z _ ↦ by rw [hcap, min_bot_right], fun y _ ↦ ?_⟩⟩
  exact ((DonorCap.value_le_cap (c := c) _).trans hcap.le).trans bot_le

/-! ### Legality -/

private theorem erase_ne_univD (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

private theorem exists_gradedIndex_left_two :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c = (univ.erase (Fin.last 2), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.last 2), 2)
    ⟨I.erase_last_mem_faces, two_pos, by decide⟩ (erase_ne_univD _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

private theorem exists_gradedIndex_right_two :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c =
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    ⟨I.erase_castSucc_mem_faces, two_pos, by decide⟩ (erase_ne_univD _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

/-- **The lift from the coatom of `T` into the admitted layer with a donor.** -/
theorem cappedLift_donorLayer_left (hD : I.right.IsLegal) (hd : I.right.HasDeadLowCells)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hraise : I.left.HasFullRaiseFrom I.right c.cap c.ref) :
    (I.donorLayer c).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_lowerFieldLayer)
    I.isConsistent_lowerFieldLayer (CapRequests.admits_bot _ _ _) (erase_ne_univD _)
    exists_gradedIndex_left_two (I.cappedLift_lowerFieldLayer hxyL hxL hyL)
    (fun _ hf ↦ botProvisionD_left hd hbt hraise hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionD_left hD hd hbt hraise hh hbh ha hA hf hfa)

/-- **The lift from the coatom of `D` into the admitted layer with a donor.** -/
theorem cappedLift_donorLayer_right (hT : I.left.IsLegal)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hb : I.left.toCellScheme.grade c.cap = 2) :
    (I.donorLayer c).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_lowerFieldLayer)
    I.isConsistent_lowerFieldLayer (CapRequests.admits_bot _ _ _) (erase_ne_univD _)
    exists_gradedIndex_right_two (I.cappedLift_lowerFieldLayer hxyL.symm hyL hxL)
    (fun _ hf ↦ botProvisionD_right hT hbt hb hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionD_right hT hbt hb hh hbh ha hA hf hfa)

/-- **Bountifulness of the admitted layer with a donor**, from the two lifts at grade `2`. -/
theorem isBountiful_donorLayer
    (hL : (I.donorLayer c).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩)
    (hR : (I.donorLayer c).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) :
    (I.donorLayer c).rows.IsBountiful := by
  have hemb := Scheme.isLowerEmbedding_castAdd (S := I.lowerFieldLayer) 2
    (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)).card
    (fun i ↦ I.lowerFieldLayer.fieldRowOn 2 (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c))
      (Scheme.entryOn _ i)) I.not_univ_two_le_lowerFieldLayer
  have hlow := Scheme.isLowerEmbedding_fieldLayer I.amalgam.toScheme 1 (I.not_univ_le 1)
  have e1 : (I.donorLayer c).rows.comap hemb = I.lowerFieldLayer.rows :=
    Scheme.comap_rows_castAdd (S := I.lowerFieldLayer) (k := 2)
      (M := (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)).card)
      (r := fun i ↦ I.lowerFieldLayer.fieldRowOn 2
        (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)) (Scheme.entryOn _ i))
      (h := I.not_univ_two_le_lowerFieldLayer)
  have e2 : I.lowerFieldLayer.rows.comap hlow = I.amalgam.rows := Scheme.comap_rows_fieldLayer
  have hsp1 : I.lowerFieldLayer.toCellScheme.IsSourcePrefix (I.donorLayer c).toCellScheme
      (Fin.castAdd _) ((univ : Finset (Fin 3)), 1) :=
    ⟨hemb, Scheme.appendFullCellsScheme_scope_castAdd _ _ _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below (fun h ↦ absurd h.2 (by omega)) hd⟩, rfl⟩⟩
  have hone (U : Finset (Fin 3)) (hU : I.lowerFieldLayer.rows.CappedLift (X := (U, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩) :
      (I.donorLayer c).rows.CappedLift (X := (U, 1)) (Y := ((univ : Finset (Fin 3)), 1))
        ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp1.cappedLift_iff _ le_rfl).mp ?_
    change ((I.donorLayer c).rows.comap hemb).CappedLift _
    rw [e1]
    exact hU
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hwf : (I.donorLayer c).IsWellFormed :=
    Scheme.isWellFormed_fieldLayerOn (hS := I.not_univ_two_le_lowerFieldLayer)
      I.isWellFormed_lowerFieldLayer two_pos (by omega)
  have hfull (z : Fin 3) (hlift1 : I.lowerFieldLayer.rows.CappedLift (X := (univ.erase z, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩)
      (hlift2 : (I.donorLayer c).rows.CappedLift (X := (univ.erase z, 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) (j : ℕ) (hj : j ≤ 2) :
      (I.donorLayer c).rows.CappedLift (X := (univ.erase z, j)) (Y := ((univ : Finset (Fin 3)), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact hwf.isWellFormed.cappedLift _ (Or.inl rfl) _
    · exact hone _ hlift1
    · exact hlift2
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces (fun X Y hX hY hXY hYne ↦ ?_)
    (fun j hj ↦ hfull _ (I.cappedLift_lowerFieldLayer hxyL hxL hyL) hL j (hle _ j hj))
    (fun j hj ↦ hfull _ (I.cappedLift_lowerFieldLayer hxyL.symm hyL hxL) hR j (hle _ j hj))
  have h : I.amalgam.toCellScheme.IsSourcePrefix (I.donorLayer c).toCellScheme
      (fun d ↦ Fin.castAdd _ (Fin.castAdd _ d)) Y := by
    refine ⟨hemb.comp hlow, fun t ↦
        (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _), fun d hd ↦ ?_⟩
    have hsc : (I.donorLayer c).toCellScheme.scope d ≠ univ := fun he ↦
      hYne (subset_antisymm (subset_univ _) (he ▸ hd.1))
    induction d using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hsc
    | left d =>
      induction d using Fin.addCases with
      | right i =>
        exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hsc
      | left a => exact ⟨a, rfl⟩
  refine h.cappedLift_of_isBountiful ?_ hX hY hXY le_rfl
  have hc : (I.donorLayer c).rows.comap h.isLowerEmbedding = I.amalgam.rows := by
    change (((I.donorLayer c).rows.comap hemb).comap hlow) = _
    rw [e1, e2]
  rw [hc]
  exact I.isBountiful

/-- **The admitted completion with a donor at the arity one.**  For a seed with coatom types `T`
and `D` (both legal), marked-cap data with the cap of grade `2` in `T`, `D` with dead cells of grade
`1` and no cell labelled in a block, and the raise from `T` into `D` at the cap, the admitted layer
at the grade `2` over the canonical lower layer is legal below the full grade. -/
theorem isLegalBelowFullGrade_donorLayer (hT : I.left.IsLegal) (hD : I.right.IsLegal)
    (hb : I.left.toCellScheme.grade c.cap = 2) (hd : I.right.HasDeadLowCells)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤)
    (hraise : I.left.HasFullRaiseFrom I.right c.cap c.ref) :
    (I.donorLayer c).IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_fieldLayerOn (hS := I.not_univ_two_le_lowerFieldLayer)
    I.isWellFormed_lowerFieldLayer two_pos (by omega)
  isCoded := Scheme.isCoded_admittedFieldLayer (Scheme.isCoded_fieldLayer I.amalgam.isCoded)
  isConsistent := Scheme.isConsistent_admittedFieldLayer I.isConsistent_lowerFieldLayer
  isBountiful := isBountiful_donorLayer (cappedLift_donorLayer_left hD hd hbt hraise)
    (cappedLift_donorLayer_right hT hbt hb)
  grade_lt d := by
    induction d using Fin.addCases with
    | left e =>
      exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_lt
        ((I.lowerFieldLayer_grade_le e).trans_lt (by omega))
    | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    have hj0 : 0 < j := hX.2.1
    by_cases hC : C = univ
    · subst hC
      rcases (show j = 1 ∨ j = 2 by simp only at hX2; omega) with rfl | rfl
      · obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
          (S := I.amalgam.toScheme) (k := 1) (p := fun _ ↦ ⊥)
          (CellScheme.Rows.isLawfulBelow_const_bot _))
        exact ⟨Fin.castAdd _ (Fin.natAdd _ i),
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
            (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)⟩
      · exact Scheme.exists_gradedIndex_eq_admittedFieldLayer (CapRequests.admits_bot _ _ _)
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
          ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd)⟩

/-- **The admitted completion with a donor labelled `⊥` and `⊤`**: the raise is the labels of `D`
capped at `sT b` (`StageType.hasFullRaiseFrom_of_bot_top`). -/
theorem isLegalBelowFullGrade_donorLayer_of_bot_top (hT : I.left.IsLegal) (hD : I.right.IsLegal)
    (hb : I.left.toCellScheme.grade c.cap = 2) (hd : I.right.HasDeadLowCells)
    (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤) :
    (I.donorLayer c).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_donorLayer hT hD hb hd hbt
    (StageType.hasFullRaiseFrom_of_bot_top hb hbt c.ref)

end Seed

/-! ### Instances -/

namespace GatedExtensionCounterexample

variable (α : Ordinal.{u})

/-- **Donor data at `P`** over the canonical lower layer: cap and marker the full cell `4`, bottom
class the dead cells `{0, 1, 2}`. -/
def capDonorP (R : ℕ) (hR : R < 2) : (seedP α).DonorCap where
  cap := ((4 : Fin 5) : Fin (P α).card)
  marker := ((4 : Fin 5) : Fin (P α).card)
  R := R
  R_lt_two := hR
  ref := id
  botCells := ({0, 1, 2} : Set (Fin 5))

/-- **The admitted layer with a donor at `P` is legal below the full grade** (the canonical lower
layer; `D = P` has dead cells of grade `1` and labels `⊥` and `⊤` only). -/
theorem isLegalBelowFullGrade_donorLayer_P (R : ℕ) (hR : R < 2) :
    ((seedP α).donorLayer (capDonorP α R hR)).IsLegalBelowFullGrade :=
  Seed.isLegalBelowFullGrade_donorLayer_of_bot_top (isLegal_P α) (isLegal_P α) rfl
    (hasDeadLowCells_P α) (by
      change ∀ z : Fin 5, labelling ⊤ ⊤ z = ⊥ ∨ labelling ⊤ ⊤ z = ⊤
      intro z
      fin_cases z <;> simp [labelling])

end GatedExtensionCounterexample

namespace CoupledGatedExtensionCounterexample

/-- **The coupled-gate type as a donor breaks two hypotheses**: its cell `z₁ = 2` of grade `1` is
labelled `1`, so it is neither dead nor labelled `⊥` or `⊤`. -/
theorem not_botTop_P (α : Ordinal.{u}) (hα : 1 < α) :
    ¬ (∀ z, (P α hα).label z = ⊥ ∨ (P α hα).label z = ⊤) ∧ ¬ (P α hα).HasDeadLowCells := by
  refine ⟨fun h ↦ ?_, not_hasDeadLowCells_P α hα⟩
  rcases h ((2 : Fin 5) : Fin (P α hα).card) with h2 | h2
  · exact absurd h2 (by change (1 : Label.{u}) ≠ ⊥; exact WithBot.coe_ne_bot)
  · exact absurd h2 (by
      change (1 : Label.{u}) ≠ ⊤
      exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h))

end CoupledGatedExtensionCounterexample

end VaughtConjecture

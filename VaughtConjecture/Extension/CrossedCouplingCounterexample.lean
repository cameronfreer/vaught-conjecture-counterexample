/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CrossedCouplingTypes
import VaughtConjecture.Extension.OrderedLayerObstruction

/-!
# A legal seed on five points without an ordered-layer step

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
a legal seed with two opposite forcings, for which the ordered-layer step fails for all layer
rows); semantic contract, items 2–4.

**The seed** (`seedHG`).  The types `TH` and `TG` of
`VaughtConjecture.Extension.CrossedCouplingTypes` have the same face on `{0, 1, 2}`
(`comap_TH_eq`): their rows differ only at the cells `15` and `18`, of full scope.  That face
carries two parameters, `H` at `({0, 1, 2}, 2)` and `G` at `({0, 1, 2}, 3)`, with no relation
between them.  The seed `seedHG` has the coatom type `TH` on `C = {0, 1, 2, 3}` and `TG` on
`D = {0, 1, 2, 4}`; it is legal, by `Seed.ofCoatoms`.  `TH` couples the parameter `A_C` of the
cells through the point `3` to `H` (`H ≤ A_C`) and leaves it free of `G`; `TG` couples `A_D` to `G`
(`G ≤ A_D`) and leaves it free of `H`.

**Two opposite forcings** (`forcesTop_left`, `forcesTop_right`).  Let `d₁` be the cell at
`({3}, 1)` and `d₂` the cell at `({4}, 1)`.

* The labelling `P` of `TH` on `C` with `A_C = H = 2` and `G = ⊤` is lawful below `(C, 3)`, is
  `2 ≠ ⊤` at `d₁`, and forces `⊤` at `d₂` below `(D, 3)`: a labelling lawful below `(D, 3)` equal
  to `P` on the common face is `⊤` at `({0, 1, 2}, 3)`, hence at `d₂` by the coupling `G ≤ A_D`.
* The labelling `P'` of `TG` on `D` with `A_D = 2`, `H = ⊤` and `G = ⊥` is lawful below `(D, 3)`,
  is `2 ≠ ⊤` at `d₂`, and forces `⊤` at `d₁` below `(C, 3)`, through the coupling `H ≤ A_C`.

**The theorems.**  Every completion below the full grade of `seedHG` has two different cells at
`(univ, 1)`, one reading `d₁` strictly below `d₂` and one reading `d₂` strictly below `d₁`
(`exists_ne_seedHG`, from `CompletionBelowFullGrade.exists_ne_of_forcesTop`), so `seedHG` has no
ordered-layer step, for any layer rows (`not_hasOrderedLayerStep_seedHG`, from
`Seed.not_hasOrderedLayerStep_of_forcesTop`).  So the ordered-layer step is not a property of
every legal seed on five points.  Whether `seedHG` has a completion below the full grade, with
several new cells at `(univ, 1)`, is open.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.CrossedCouplingCounterexample

open Finset Label CellScheme OrderedLayer
open TwoFaceLiftCounterexample (cellScope cellGrade cells gradedIndex_cells)

variable {α : Ordinal.{u}} {b : Bool}

/-! ### The types with the apex -/

/-- The old cells of the type keep their graded indices. -/
theorem gradedIndex_crossType_castSucc (d : Fin 19) :
    (crossType b α).toCellScheme.gradedIndex (Fin.castSucc d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc (S b) 4 d

/-- The apex of the type has graded index `(univ, 4)`. -/
theorem gradedIndex_crossType_last :
    (crossType b α).toCellScheme.gradedIndex (Fin.last 19) = ((univ : Finset (Fin 4)), 4) :=
  Scheme.appendFullCellScheme_gradedIndex_last (S b) 4

/-- The cells of the types: the nineteen cells and the apex. -/
theorem cases_crossType (i : Fin (crossType b α).card) :
    i = Fin.last 19 ∨ ∃ d : Fin 19, i = Fin.castSucc d := by
  -- The type has the nineteen cells and the apex, so `Fin.lastCases` applies.
  change Fin (19 + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- Below a pair not above the apex, lawfulness in the type is lawfulness in `S b`. -/
theorem isLawfulBelow_crossType_iff {X : Finset (Fin 4) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 4)), 4) ≤ X) {w : Fin (crossType b α).card → Label.{u}} :
    (crossType b α).rows.IsLawfulBelow X (fun d ↦ w d) ↔
      (rows b).IsLawfulBelow X (fun d ↦ w (Fin.castSucc d.1)) :=
  Scheme.isLawfulBelow_appendFullCell_iff (h := isLegalBelowFullGrade_S.not_le) hX

/-- The face `{0, 1, 2}` is a face of the types. -/
theorem face_mem_crossType : univ.map (Coatom.face 3) ∈ (crossType b α).toCellScheme.faces := by
  -- The faces of the type are those of the interval plan on four points.
  change univ.map (Coatom.face 3) ∈ Geometry.intervalPlan univ
  decide +kernel

/-! ### The common face -/

/-- The rows of the two types agree away from the cells `15` and `18`. -/
private theorem rowVal_eq_of_ne {s : Fin 19} (h15 : s ≠ 15) (h18 : s ≠ 18) (t : Fin 19) :
    rowVal.{u} true s t = rowVal false s t := by
  simp [rowVal, h15, h18]

/-- The cells visible on the face `{0, 1, 2}` are old and are neither `15` nor `18`. -/
private theorem visible_cases (s : Fin ((S.{u} b).card + 1))
    (hs : (Scheme.appendFullCellScheme (S.{u} b) 4).scope s ⊆ univ.map (Coatom.face 3)) :
    ∃ hl : s ≠ Fin.last _, ((s.castPred hl : Fin (S.{u} b).card) : ℕ) ≠ 15 ∧
      ((s.castPred hl : Fin (S.{u} b).card) : ℕ) ≠ 18 := by
  induction s using Fin.lastCases with
  | last =>
    rw [Scheme.appendFullCellScheme_scope_last] at hs
    exact absurd hs (by decide)
  | cast d =>
    refine ⟨Fin.castSucc_ne_last d, ?_⟩
    rw [Fin.castPred_castSucc]
    rw [Scheme.appendFullCellScheme_scope_castSucc] at hs
    have key : ∀ e : Fin 19, cellScope e ⊆ univ.map (Coatom.face 3) →
        (e : ℕ) ≠ 15 ∧ (e : ℕ) ≠ 18 := by decide
    exact key d hs

/-- **The face of `TH` on `{0, 1, 2}` is the face of `TG`.** -/
theorem comap_TH_eq :
    (TH α).comap (Coatom.face 3) face_mem_crossType =
      (TG α).comap (Coatom.face 3) face_mem_crossType := by
  refine StageType.ext ?_ (fun i j h ↦ ?_)
  · -- Both sides are comaps of the scheme with the apex appended, with the rows of `TH`, `TG`.
    change (Scheme.mk ((S true).card + 1) (Scheme.appendFullCellScheme (S true) 4) _).comap
        (Coatom.face 3) =
      (Scheme.mk ((S false).card + 1) (Scheme.appendFullCellScheme (S false) 4) _).comap
        (Coatom.face 3)
    refine Scheme.comap_mk_congr _ fun s hs ↦ ?_
    rw [Scheme.mem_visibleCells] at hs
    obtain ⟨hl, h15, h18⟩ := visible_cases (b := true) s (by simpa [← coe_subset] using hs)
    funext t
    have hl' : s ≠ Fin.last (crossType₀ true α).card := hl
    have hl'' : s ≠ Fin.last (crossType₀ false α).card := hl
    dsimp only
    split_ifs with h1 h2 h2
    · exact absurd h1 hl'
    · exact absurd h1 hl'
    · exact absurd h2 hl''
    exact rowVal_eq_of_ne (s := s.castPred hl) (fun h ↦ h15 (congrArg Fin.val h))
      (fun h ↦ h18 (congrArg Fin.val h)) _
  · obtain rfl : i = j := Fin.ext h
    rfl

/-- The common face of the two types, on `{0, 1, 2}`. -/
noncomputable def faceHG (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (TG α).comap (Coatom.face 3) face_mem_crossType

/-- The face of `TH` on `{0, 1, 2}` is the common face. -/
theorem restrictFace_TH (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (TH α) = some (faceHG α) := by
  rw [StageType.restrictFace_of_mem _ _ face_mem_crossType, comap_TH_eq]; rfl

/-- The face of `TG` on `{0, 1, 2}` is the common face. -/
theorem restrictFace_TG (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (TG α) = some (faceHG α) :=
  StageType.restrictFace_of_mem _ _ face_mem_crossType

/-- **The seed of the crossed couplings**: the coatom type `TH` on `{0, 1, 2, 3}` and `TG` on
`{0, 1, 2, 4}`, over their common face `{0, 1, 2}`. -/
noncomputable def seedHG (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_TH α) (isLegal_TG α) (restrictFace_TH α) (restrictFace_TG α)

/-! ### Labellings of the amalgam along a coatom -/

/-- Lawful labellings of an amalgam below a coatom whose type is `crossType b`, read on the type:
`lab A H G` with the coupling. -/
theorem exists_lab_of_comap {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (crossType b α)) {k : ℕ} (hk : k ≤ 3)
    (p : Fin Am.card → Label.{u}) (hp : Am.rows.IsLawfulBelow (univ.map f, k) fun d ↦ p d) :
    ∃ A H G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 H ∧ IsSelfVisible 3 G ∧
      Coupled b A H G ∧ ∀ d ∈ Am.toCellScheme.below (univ.map f, k), ∃ c : Fin 19,
        Am.toCellScheme.gradedIndex d = Prod.map (Finset.map f) id (cells.gradedIndex c) ∧
        p d = lab A H G c := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (crossType b α).toScheme := congrArg StageType.toScheme he
  have hgen : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), k) (fun i ↦ x i) →
      ∃ A H G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 H ∧ IsSelfVisible 3 G ∧
        Coupled b A H G ∧
        ∀ i ∈ (Am.toScheme.comap f).toCellScheme.below ((univ : Finset (Fin 4)), k),
          ∃ c : Fin 19, (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex c ∧
            x i = lab A H G c := by
    rw [heq]
    intro x hx
    have hx' := (isLawfulBelow_crossType_iff (α := α) (b := b) (w := x) (fun h ↦ by
      have := h.2; simp only at this; omega)).mp hx
    obtain ⟨A, H, G, hA, hH, hG, hc, hAH⟩ :=
      (isLawfulBelow_iff (x := fun e ↦ x (Fin.castSucc e))).mp hx'
    refine ⟨A, H, G, hA, hH, hG, hc, fun i hi ↦ ?_⟩
    rcases cases_crossType (α := α) (b := b) i with rfl | ⟨c, rfl⟩
    · exfalso
      have h2 := hi.2
      rw [gradedIndex_crossType_last] at h2
      simp only at h2
      omega
    · refine ⟨c, gradedIndex_crossType_castSucc c, hAH c ?_⟩
      rw [CellScheme.mem_below, ← gradedIndex_crossType_castSucc (α := α) (b := b) c]
      exact hi
  obtain ⟨A, H, G, hA, hH, hG, hc, hall⟩ := hgen (fun i ↦ p (Am.toScheme.cellMap f i))
    ((Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f _ p).mpr hp)
  refine ⟨A, H, G, hA, hH, hG, hc, fun d hd ↦ ?_⟩
  have hd' : d ∈ Am.toScheme.cellMap f '' (Am.toScheme.comap f).toCellScheme.below
      ((univ : Finset (Fin 4)), k) := by
    rw [Am.toScheme.image_cellMap_below f]; exact hd
  obtain ⟨i, hi, rfl⟩ := hd'
  obtain ⟨c, hgi, hpc⟩ := hall i hi
  exact ⟨c, by rw [← Am.toScheme.map_comap_gradedIndex f i, hgi], hpc⟩

/-- A labelling of graded indices whose reading along `f` is `lab A H G` is lawful below the
coatom `univ.map f` at the grade `3`, for a stage type whose face along `f` is `crossType b`. -/
theorem isLawfulBelow_coatom {A H G : Label.{u}} (hA : IsSelfVisible 1 A)
    (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G) (hc : Coupled b A H G)
    {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (crossType b α))
    {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = lab A H G d) :
    Am.rows.IsLawfulBelow (univ.map f, 3) (fun d ↦ Lf (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (crossType b α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = Lf (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun i ↦ x i) := by
    rw [heq]
    intro x hx
    refine (isLawfulBelow_crossType_iff (fun h ↦ absurd h.2 (by decide))).mpr ?_
    convert (isLawful_lab hA hH hG hc).isLawfulBelow ((univ : Finset (Fin 4)), 3) using 1
    funext d
    refine (hx _).trans ?_
    rw [gradedIndex_crossType_castSucc]
    exact hL d.1
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 3)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

/-- A cell of the type carried into a stage type along an embedding whose face is the type. -/
theorem exists_cell {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (crossType b α)) (d : Fin 19) :
    ∃ e : Fin Am.card, Am.toCellScheme.gradedIndex e =
      Prod.map (Finset.map f) id (cells.gradedIndex d) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (crossType b α).toScheme := congrArg StageType.toScheme he
  obtain ⟨i, hi⟩ : ∃ i : Fin (Am.toScheme.comap f).card,
      (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex d := by
    rw [heq]; exact ⟨Fin.castSucc d, gradedIndex_crossType_castSucc d⟩
  exact ⟨Am.toScheme.cellMap f i, by rw [← Am.toScheme.map_comap_gradedIndex f i, hi]⟩

/-! ### Labellings of graded indices on five points -/

/-- The kind of a graded index on five points read along the first coatom. -/
def kindC (X : Finset (Fin 5) × ℕ) : Fin 4 :=
  if X ∈ ({({3}, 1), ({2, 3}, 1), ({1, 2, 3}, 1), ({0, 1, 2, 3}, 1)} :
      Finset (Finset (Fin 5) × ℕ)) then 1
  else if X ∈ ({({0, 1, 2}, 2), ({0, 1, 2, 3}, 2)} : Finset (Finset (Fin 5) × ℕ)) then 2
  else if X ∈ ({({0, 1, 2}, 3), ({0, 1, 2, 3}, 3)} : Finset (Finset (Fin 5) × ℕ)) then 3
  else 0

/-- The kind of a graded index on five points read along the second coatom. -/
def kindD (X : Finset (Fin 5) × ℕ) : Fin 4 :=
  if X ∈ ({({4}, 1), ({2, 4}, 1), ({1, 2, 4}, 1), ({0, 1, 2, 4}, 1)} :
      Finset (Finset (Fin 5) × ℕ)) then 1
  else if X ∈ ({({0, 1, 2}, 2), ({0, 1, 2, 4}, 2)} : Finset (Finset (Fin 5) × ℕ)) then 2
  else if X ∈ ({({0, 1, 2}, 3), ({0, 1, 2, 4}, 3)} : Finset (Finset (Fin 5) × ℕ)) then 3
  else 0

/-- The kind of a graded index of the first coatom is the kind of its cell. -/
private theorem kindC_left : ∀ c : Fin 19,
    kindC (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex c)) = kind c := by
  decide +kernel

/-- The kind of a graded index of the second coatom is the kind of its cell. -/
private theorem kindD_right : ∀ c : Fin 19,
    kindD (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c)) = kind c := by
  decide +kernel

/-- The labelling of graded indices of the first coatom with the parameters `A`, `H`, `G`. -/
noncomputable def labC (A H G : Label.{u}) (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  ![⊥, A, H, G] (kindC X)

/-- The labelling of graded indices of the second coatom with the parameters `A`, `H`, `G`. -/
noncomputable def labD (A H G : Label.{u}) (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  ![⊥, A, H, G] (kindD X)

/-- Read along the first coatom, `labC A H G` is `lab A H G`. -/
theorem labC_left (A H G : Label.{u}) (c : Fin 19) :
    labC A H G (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex c)) = lab A H G c := by
  rw [labC, kindC_left]; rfl

/-- Read along the second coatom, `labD A H G` is `lab A H G`. -/
theorem labD_right (A H G : Label.{u}) (c : Fin 19) :
    labD A H G (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c)) =
      lab A H G c := by
  rw [labD, kindD_right]; rfl

/-! ### The two forcings -/

/-- The cell of the type carried to `({3}, 1)` along the first coatom is `3`. -/
private theorem left_eq_three : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex c) =
      (({3} : Finset (Fin 5)), 1) → c = 3 := by decide +kernel

/-- The cell carried to `({0, 1, 2}, 2)` along the first coatom is `13`. -/
private theorem left_eq_thirteen : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex c) =
      (({0, 1, 2} : Finset (Fin 5)), 2) → c = 13 := by decide +kernel

/-- The cell of the type carried to `({4}, 1)` along the second coatom is `3`. -/
private theorem right_eq_three : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c) =
      (({4} : Finset (Fin 5)), 1) → c = 3 := by decide +kernel

/-- The cell carried to `({0, 1, 2}, 3)` along the second coatom is `16`. -/
private theorem right_eq_sixteen : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c) =
      (({0, 1, 2} : Finset (Fin 5)), 3) → c = 16 := by decide +kernel

variable {I : Seed.{u} α 3}

/-- **The first forcing.**  On a seed whose coatom types are `TH` and `TG`, the labelling of `TH`
with `A_C = H = 2` and `G = ⊤` forces `⊤` at the cell `({4}, 1)` below `(D, 3)`: a labelling lawful
below `(D, 3)` equal to it on the common face is `⊤` at `({0, 1, 2}, 3)`, and `TG` couples
`G ≤ A_D`. -/
theorem forcesTop_left (hIR : I.right = TG α) {d₂ : Fin I.amalgam.card}
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1)) :
    I.ForcesTop (coatomC, 3) (coatomD, 3)
      (fun d ↦ labC w2 w2 ⊤ (I.amalgam.toCellScheme.gradedIndex d)) d₂ := by
  intro w hw hwP
  rw [coatomD_eq] at hw
  obtain ⟨A, H, G, -, -, -, hGA, hall⟩ := exists_lab_of_comap (hIR ▸ I.restrictFace_right)
    le_rfl w hw
  have hGA' : G ≤ A := by simpa [Coupled] using hGA
  obtain ⟨g, hg⟩ := exists_cell (hIR ▸ I.restrictFace_right) 16
  have hg' : I.amalgam.toCellScheme.gradedIndex g = (({0, 1, 2} : Finset (Fin 5)), 3) :=
    hg.trans (by decide +kernel)
  have hmem (d : Fin I.amalgam.card) {B : Finset (Fin 5)} (hB : B = coatomC ∨ B = coatomD)
      {X : Finset (Fin 5) × ℕ} (hX : I.amalgam.toCellScheme.gradedIndex d = X)
      (hXB : X ≤ (B, 3)) : d ∈ I.amalgam.toCellScheme.below (B, 3) := by
    rw [CellScheme.mem_below, hX]; exact hXB
  have hgC := hmem g (.inl rfl) hg' (by decide)
  have hgD := hmem g (.inr rfl) hg' (by decide)
  have hd₂D := hmem d₂ (.inr rfl) hd₂ (by decide)
  rw [coatomD_eq] at hgD hd₂D
  obtain ⟨c₂, hc₂, hw₂⟩ := hall d₂ hd₂D
  obtain ⟨cg, hcg, hwg⟩ := hall g hgD
  obtain rfl := right_eq_three c₂ (hc₂.symm.trans hd₂)
  obtain rfl := right_eq_sixteen cg (hcg.symm.trans hg')
  have hPg : w g = ⊤ := by
    rw [hwP g hgC (by rw [coatomD_eq]; exact hgD)]
    -- The prescription read at the cell `({0, 1, 2}, 3)`.
    change labC w2 w2 ⊤ (I.amalgam.toCellScheme.gradedIndex g) = ⊤
    rw [hg']; rfl
  rw [hw₂, lab_of_kind_one (by decide)]
  rw [hwg, lab_of_kind_three (by decide)] at hPg
  exact top_le_iff.mp (hPg ▸ hGA')

/-- **The second forcing.**  On a seed whose coatom types are `TH` and `TG`, the labelling of `TG`
with `A_D = 2`, `H = ⊤` and `G = ⊥` forces `⊤` at the cell `({3}, 1)` below `(C, 3)`: a labelling
lawful below `(C, 3)` equal to it on the common face is `⊤` at `({0, 1, 2}, 2)`, and `TH` couples
`H ≤ A_C`. -/
theorem forcesTop_right (hIL : I.left = TH α) {d₁ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1)) :
    I.ForcesTop (coatomD, 3) (coatomC, 3)
      (fun d ↦ labD w2 ⊤ ⊥ (I.amalgam.toCellScheme.gradedIndex d)) d₁ := by
  intro w hw hwP
  rw [coatomC_eq] at hw
  obtain ⟨A, H, G, -, -, -, hc, hall⟩ := exists_lab_of_comap (hIL ▸ I.restrictFace_left)
    le_rfl w hw
  have hHA : H ≤ A := (by simpa [Coupled] using hc : H ≤ A ∧ min A G ≤ H).1
  obtain ⟨h, hh⟩ := exists_cell (hIL ▸ I.restrictFace_left) 13
  have hh' : I.amalgam.toCellScheme.gradedIndex h = (({0, 1, 2} : Finset (Fin 5)), 2) :=
    hh.trans (by decide +kernel)
  have hmem (d : Fin I.amalgam.card) {B : Finset (Fin 5)}
      {X : Finset (Fin 5) × ℕ} (hX : I.amalgam.toCellScheme.gradedIndex d = X)
      (hXB : X ≤ (B, 3)) : d ∈ I.amalgam.toCellScheme.below (B, 3) := by
    rw [CellScheme.mem_below, hX]; exact hXB
  have hhD := hmem h (B := coatomD) hh' (by decide)
  have hhC := hmem h (B := coatomC) hh' (by decide)
  have hd₁C := hmem d₁ (B := coatomC) hd₁ (by decide)
  rw [coatomC_eq] at hhC hd₁C
  obtain ⟨c₁, hc₁, hw₁⟩ := hall d₁ hd₁C
  obtain ⟨ch, hch, hwh⟩ := hall h hhC
  obtain rfl := left_eq_three c₁ (hc₁.symm.trans hd₁)
  obtain rfl := left_eq_thirteen ch (hch.symm.trans hh')
  have hPh : w h = ⊤ := by
    rw [hwP h hhD (by rw [coatomC_eq]; exact hhC)]
    -- The prescription read at the cell `({0, 1, 2}, 2)`.
    change labD w2 ⊤ ⊥ (I.amalgam.toCellScheme.gradedIndex h) = ⊤
    rw [hh']; rfl
  rw [hw₁, lab_of_kind_one (by decide)]
  rw [hwh, lab_of_kind_two (by decide)] at hPh
  exact top_le_iff.mp (hPh ▸ hHA)

/-- The labelling of `TH` with `A_C = H = 2` and `G = ⊤` is lawful below `(C, 3)`. -/
theorem isLawfulBelow_labC (hIL : I.left = TH α) :
    I.amalgam.rows.IsLawfulBelow (coatomC, 3)
      (fun d ↦ labC w2 w2 ⊤ (I.amalgam.toCellScheme.gradedIndex d)) := by
  rw [coatomC_eq]
  exact isLawfulBelow_coatom (isSelfVisible_w2.mono (by omega)) isSelfVisible_w2
    (isSelfVisible_top 3) (by simp [Coupled]) (hIL ▸ I.restrictFace_left) (labC_left _ _ _)

/-- The labelling of `TG` with `A_D = 2`, `H = ⊤` and `G = ⊥` is lawful below `(D, 3)`. -/
theorem isLawfulBelow_labD (hIR : I.right = TG α) :
    I.amalgam.rows.IsLawfulBelow (coatomD, 3)
      (fun d ↦ labD w2 ⊤ ⊥ (I.amalgam.toCellScheme.gradedIndex d)) := by
  rw [coatomD_eq]
  exact isLawfulBelow_coatom (isSelfVisible_w2.mono (by omega)) (isSelfVisible_top 2)
    (isSelfVisible_bot 3) (by simp [Coupled]) (hIR ▸ I.restrictFace_right) (labD_right _ _ _)

/-! ### The theorems -/

section Theorems

variable (hIL : I.left = TH α) (hIR : I.right = TG α)
include hIL hIR

/-- The two cells `({3}, 1)` and `({4}, 1)` of the amalgam. -/
theorem exists_cells : ∃ d₁ d₂ : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨d₁, h₁⟩ := exists_cell (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₂, h₂⟩ := exists_cell (hIR ▸ I.restrictFace_right) 3
  exact ⟨d₁, d₂, h₁.trans (by decide +kernel), h₂.trans (by decide +kernel)⟩

/-- **Every completion has two different cells at `(univ, 1)`**, for a seed whose coatom types are
`TH` and `TG`: one reads `({3}, 1)` strictly below `({4}, 1)`, the other the reverse. -/
theorem exists_ne_of (F : CompletionBelowFullGrade I) :
    ∃ u u' : Fin F.scheme.card, u ≠ u' ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, 1) ∧
      F.scheme.toCellScheme.gradedIndex u' = (univ, 1) := by
  obtain ⟨d₁, d₂, hd₁, hd₂⟩ := exists_cells hIL hIR
  have hmem (d : Fin I.amalgam.card) {B : Finset (Fin 5)}
      {X : Finset (Fin 5) × ℕ} (hX : I.amalgam.toCellScheme.gradedIndex d = X)
      (hXB : X ≤ (B, 3)) : d ∈ I.amalgam.toCellScheme.below (B, 3) := by
    rw [CellScheme.mem_below, hX]; exact hXB
  have hg₂ : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
  obtain ⟨u, u', hne, hu, hu'⟩ := F.exists_ne_of_forcesTop (B₁ := coatomC) (B₂ := coatomD)
    (k := 3) (k' := 3) (by decide) (by decide)
    ⟨coatomC_mem_faces I, by decide, by decide⟩ ⟨coatomD_mem_faces I, by decide, by decide⟩
    (isLawfulBelow_labC hIL) (isLawfulBelow_labD hIR)
    (hmem d₁ hd₁ (by decide)) (hmem d₂ hd₂ (by decide))
    (hmem d₁ hd₁ (by decide)) (hmem d₂ hd₂ (by decide))
    ((congrArg Prod.snd hd₁).trans hg₂.symm)
    (by simp only [hd₁]; exact gridPoint_ne_top 2 0)
    (by simp only [hd₂]; exact gridPoint_ne_top 2 0)
    (forcesTop_left hIR hd₂) (forcesTop_right hIL hd₁)
  rw [hg₂] at hu hu'
  exact ⟨u, u', hne, hu, hu'⟩

/-- **A seed whose coatom types are `TH` and `TG` has no ordered-layer step**, for any layer
rows. -/
theorem not_hasOrderedLayerStep_of : ¬ I.HasOrderedLayerStep := by
  rintro ⟨ρ, h⟩
  obtain ⟨u, u', hne, hu, hu'⟩ := exists_ne_of hIL hIR h.completion
  exact hne ((eq_newCell (ρ := ρ) le_rfl (by omega) hu).trans
    (eq_newCell le_rfl (by omega) hu').symm)

end Theorems

/-- **Every completion of `seedHG` has two different cells at `(univ, 1)`.** -/
theorem exists_ne_seedHG (F : CompletionBelowFullGrade (seedHG α)) :
    ∃ u u' : Fin F.scheme.card, u ≠ u' ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, 1) ∧
      F.scheme.toCellScheme.gradedIndex u' = (univ, 1) :=
  exists_ne_of rfl rfl F

/-- **`seedHG` has no ordered-layer step**, for any layer rows: the ordered-layer step is not a
property of every legal seed on five points. -/
theorem not_hasOrderedLayerStep_seedHG : ¬ (seedHG α).HasOrderedLayerStep :=
  not_hasOrderedLayerStep_of rfl rfl

/-- **Not every legal seed on five points has an ordered-layer step.** -/
theorem not_forall_hasOrderedLayerStep (α : Ordinal.{u}) :
    ¬ ∀ I : Seed.{u} α 3, I.HasOrderedLayerStep :=
  fun h ↦ not_hasOrderedLayerStep_seedHG (h (seedHG α))

end VaughtConjecture.CrossedCouplingCounterexample

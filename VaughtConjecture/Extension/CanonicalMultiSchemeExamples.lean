/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalMultiScheme
import VaughtConjecture.Extension.CrossedCouplingCompletion

/-!
# The canonical multi-layer scheme completes the crossed-coupling seed

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the special case of the canonical multi-layer scheme whose product clause holds below the top
grade); semantic contract, items 2–4.

Let `I` be a seed on five points whose coatom types are `TH` and `TG`
(`VaughtConjecture.Extension.CrossedCouplingTypes`), such as `seedHG`.  Its lawful labellings below
a coatom at a grade `k ≤ 3` are labellings by kinds (`CrossedCouplingCounterexample.kindOld`) of
parameters `A`, `H`, `G` coupled as in the type of that coatom.

**The copy rows** (`CanonicalHG.rowsHG`): at `(univ, 1)` the copy of `(C, 1)` reads `A_C` at
`ω + 2` and `A_D` at `1`, the copy of `(D, 1)` the reverse; at `(univ, 2)` both copies read `A_C`
and `H` at `ω + 2` and `A_D` at `1`; at `(univ, 3)` both read `A_C` and `H` at `2` and `A_D` and `G`
at `ω + 3`; at `(univ, 4)` both have the top row.  They are the rows of
`CrossedCouplingCounterexample.schemeHG`, each cell there of graded index `(univ, k)`, `k ≥ 2`,
being here two copies with one row.

**The product clause below the top grade holds** (`CanonicalHG.canonicalProduct`): every
labelling of the amalgam lawful below both coatoms at a grade `j ≤ 3` is a labelling by kinds of
`A_C`, `A_D`, `H`, `G` with the couplings of both types (`H`, `G` agreeing on the common face),
and that labelling read through the bases is lawful (`CanonicalHG.isLawful_kindVal`): at each copy
the witness of the corresponding new cell of `schemeHG` (the strip shifter of the other coatom's
parameter at the grade `1`, of `A_D` at the grade `2`, `strip3 A_C` at the grade `3`).  So the
classification of the lawful labellings below `(univ, j)`, `j ≤ 3`, as pairs agreeing on the common
face holds here, and the lifts into the full scope are the lifts from the common face.

**The completion** (`Seed.canonicalMultiStep_of_TH_TG`,
`Seed.nonempty_completionBelowFullGrade_canonical_seedHG`): with
`Seed.canonicalMultiStep_of_productBelowTop`, the canonical multi-layer scheme of these rows is a
completion below the full grade of every seed of `TH` and `TG`.  At the grade `4` the product
clause fails (`Seed.not_canonicalProduct_seedHG`), and the top row restricts the lawful labellings
to the labellings of `Ω` alone.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.OrderedLayer.CanonicalHG

open Finset Label CellScheme
open CrossedCouplingCounterexample (TH TG kindOld kindOld_spec CellKind Coupled crossType
  leftKind rightKind kindOld_left kindOld_right val_leftKind val_rightKind exists_lab_of_comap
  isLawful_amalgam_kindOld hasBottomApexes_HG exists_paramCells w2 w3 isSelfVisible_v1
  isSelfVisible_v2
  isSelfVisible_w2 isSelfVisible_w3 strip3_w2 strip3_w3 min_visibilityReplace_A
  min_visibilityReplace_H)
open TwoFaceLiftCounterexample (v1 v2 stripShifter isWitness_stripShifter stripShifter_v1
  stripShifter_v2)
open TwoFaceLiftExistsCounterexample (strip3 isWitness_strip3)

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- The **labelling by kinds** of the amalgam: each cell carries the value of the kind of its
graded index. -/
def kindVal (AC AD H G Q : Label.{u}) (d : Fin I.amalgam.card) : Label.{u} :=
  (kindOld (I.amalgam.toCellScheme.gradedIndex d)).val AC AD H G Q

/-- **The copy rows of the crossed-coupling seed.** -/
noncomputable def rowsHG : CopyRows I
  | ⟨0, _⟩, ⟨0, _⟩ => kindVal I v2 v1 ⊥ ⊥ ⊥
  | ⟨0, _⟩, _ => kindVal I v1 v2 ⊥ ⊥ ⊥
  | ⟨1, _⟩, _ => kindVal I v2 v1 v2 ⊥ ⊥
  | ⟨2, _⟩, _ => kindVal I w2 w3 w2 w3 ⊥
  | ⟨3, _⟩, _ => amalgamTopRow I

/-- The kind of the original of a copy: `A_C`, `A_D` at the grade `1`, `H`, `G` at the grades `2`,
`3`, and the top kind at the grade `4`. -/
def copyKind : Fin 4 → Fin 2 → CellKind
  | ⟨0, _⟩, ⟨0, _⟩ => .ac
  | ⟨0, _⟩, _ => .ad
  | ⟨1, _⟩, _ => .h
  | ⟨2, _⟩, _ => .g
  | ⟨3, _⟩, _ => .top

/-- The kind of the original of a copy. -/
theorem kindOld_copyOrig (k : Fin 4) (i : Fin 2) :
    kindOld (I.amalgam.toCellScheme.gradedIndex (copyOrig I k i)) = copyKind k i := by
  rw [gradedIndex_copyOrig]
  fin_cases k <;> fin_cases i <;> decide

variable {I}

/-- The grade of a cell determines the grade of its kind. -/
theorem grade_of_kindOld (d : Fin I.amalgam.card) :
    (kindOld (I.amalgam.toCellScheme.gradedIndex d) = .ac → I.amalgam.toCellScheme.grade d = 1) ∧
      (kindOld (I.amalgam.toCellScheme.gradedIndex d) = .ad →
        I.amalgam.toCellScheme.grade d = 1) ∧
      (kindOld (I.amalgam.toCellScheme.gradedIndex d) = .h →
        I.amalgam.toCellScheme.grade d = 2) ∧
      (kindOld (I.amalgam.toCellScheme.gradedIndex d) = .g →
        I.amalgam.toCellScheme.grade d = 3) ∧
      (kindOld (I.amalgam.toCellScheme.gradedIndex d) = .top ↔
        I.amalgam.toCellScheme.grade d = 4) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := kindOld_spec (I.amalgam.toCellScheme.gradedIndex d)
  exact ⟨fun h ↦ (h1 h).1, fun h ↦ (h2 h).1, h3, h4, h5⟩

/-- **A row by kinds transforms to a labelling by kinds capped at `x`** at a copy of grade
`k + 1`, when the witness does so kind by kind, at the grade of each kind below the copy. -/
theorem transformsTo_kindVal {R : CopyRows I} (k : Fin 4) (i : Fin 2)
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    {RAC RAD RH RG RQ AC AD H G Q x : Label.{u}}
    (hac : min AC x = min (σ RAC) (g 1)) (had : min AD x = min (σ RAD) (g 1))
    (hh : 2 ≤ (k : ℕ) + 1 → min H x = min (σ RH) (g 2))
    (hg : 3 ≤ (k : ℕ) + 1 → min G x = min (σ RG) (g 3))
    (htop : 4 ≤ (k : ℕ) + 1 → min Q x = min (σ RQ) (g 4)) :
    TransformsTo (fun t : (canonicalMultiScheme I R).toCellScheme.below
        ((canonicalMultiScheme I R).toCellScheme.gradedIndex (multiNewCell I canonicalMult k i)) ↦
        (canonicalMultiScheme I R).toCellScheme.grade t)
      (fun t ↦ kindVal I RAC RAD RH RG RQ (copyBase I t.1))
      (fun t ↦ min (kindVal I AC AD H G Q (copyBase I t.1)) x) := by
  refine ⟨g, σ, hw, fun t ↦ ?_⟩
  have ht : (canonicalMultiScheme I R).toCellScheme.grade t.1 ≤ (k : ℕ) + 1 :=
    (le_of_le_of_eq (t.2 : (canonicalMultiScheme I R).toCellScheme.gradedIndex t.1 ≤ _)
      (gradedIndex_multiNewCell (r := canonicalRows I R) k i)).2
  have hg' := grade_copyBase R t.1
  obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_kindOld (copyBase I t.1)
  dsimp only
  rw [← hg']
  rw [← hg'] at ht
  unfold kindVal
  cases hk : kindOld (I.amalgam.toCellScheme.gradedIndex (copyBase I t.1)) with
  | dead => simp only [CellKind.val, hw.map_bot, bot_le, min_eq_left]
  | ac => simp only [CellKind.val]; rw [g1 hk]; exact hac
  | ad => simp only [CellKind.val]; rw [g2 hk]; exact had
  | h => simp only [CellKind.val]; rw [g3 hk]; exact hh (by have := g3 hk; omega)
  | g => simp only [CellKind.val]; rw [g4 hk]; exact hg (by have := g4 hk; omega)
  | top => simp only [CellKind.val]; rw [g5.mp hk]; exact htop (by have := g5.mp hk; omega)

/-- The strip shifter is a witness for a suppressor up to the grade `1`. -/
theorem isWitness_stripShifter_one {A F : Label.{u}} (hF : IsSelfVisible 1 F) :
    IsWitness (constStepSuppressor 1 F) (stripShifter A) :=
  (isWitness_stripShifter (A := A) (isSelfVisible_top 2)).of_le
    (fun n ↦ by
      unfold constStepSuppressor
      split_ifs
      · exact le_top
      · omega
      · exact bot_le
      · exact le_rfl)
    (antitone_constStepSuppressor 1 F) (isSelfVisible_constStepSuppressor hF)

variable {H G : Label.{u}}

/-- The value of the kind of the original of a copy is self-visible at its grade. -/
theorem isSelfVisible_copyKind {AC AD : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G) :
    ∀ (k : Fin 4) (i : Fin 2),
      IsSelfVisible ((k : ℕ) + 1) ((copyKind k i).val AC AD H G ⊥)
  | ⟨0, _⟩, ⟨0, _⟩ => hAC
  | ⟨0, _⟩, ⟨1, _⟩ => hAD
  | ⟨1, _⟩, _ => hH
  | ⟨2, _⟩, _ => hG
  | ⟨3, _⟩, _ => isSelfVisible_bot _

/-- **Locality at the copies**: the row of each copy transforms to the labelling by kinds capped
at the value of its kind, by the witness of the corresponding new cell of `schemeHG`. -/
theorem transformsTo_copy {AC AD : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G)
    (h1 : H ≤ AC) (h2 : min AC G ≤ H) (hGA : G ≤ AD) :
    ∀ (k : Fin 4) (i : Fin 2),
      TransformsTo (fun t : (canonicalMultiScheme I (rowsHG I)).toCellScheme.below
          ((canonicalMultiScheme I (rowsHG I)).toCellScheme.gradedIndex
            (multiNewCell I canonicalMult k i)) ↦
          (canonicalMultiScheme I (rowsHG I)).toCellScheme.grade t)
        (fun t ↦ rowsHG I k i (copyBase I t.1))
        (fun t ↦ min (kindVal I AC AD H G ⊥ (copyBase I t.1)) ((copyKind k i).val AC AD H G ⊥))
  | ⟨0, _⟩, ⟨0, _⟩ => by
    -- The copy of `(C, 1)`, labelled `A_C`: the strip shifter of `A_D`, up to `A_C`.
    refine transformsTo_kindVal _ _ (isWitness_stripShifter_one (A := AD) hAC) ?_ ?_
      (fun h ↦ absurd h (by simp)) (fun h ↦ absurd h (by simp)) (fun h ↦ absurd h (by simp))
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v2, constStepSuppressor_of_le _ le_rfl, min_top_left, min_self]
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v1 hAD, constStepSuppressor_of_le _ le_rfl]
  | ⟨0, _⟩, ⟨1, _⟩ => by
    -- The copy of `(D, 1)`, labelled `A_D`: the strip shifter of `A_C`, up to `A_D`.
    refine transformsTo_kindVal _ _ (isWitness_stripShifter_one (A := AC) hAD) ?_ ?_
      (fun h ↦ absurd h (by simp)) (fun h ↦ absurd h (by simp)) (fun h ↦ absurd h (by simp))
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v1 hAC, constStepSuppressor_of_le _ le_rfl]
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v2, constStepSuppressor_of_le _ le_rfl, min_top_left, min_self]
  | ⟨1, _⟩, _ => by
    -- The copies of `(C, 2)` and `(D, 2)`, labelled `H`: the strip shifter of `A_D`, up to `H`.
    refine transformsTo_kindVal _ _ (isWitness_stripShifter (A := AD) hH) ?_ ?_ (fun _ ↦ ?_)
      (fun h ↦ absurd h (by simp)) (fun h ↦ absurd h (by simp))
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v2, constStepSuppressor_of_le _ (by omega), min_top_left, min_eq_right h1]
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v1 hAD, constStepSuppressor_of_le _ (by omega)]
    · simp only [copyKind, CellKind.val]
      rw [stripShifter_v2, constStepSuppressor_of_le _ le_rfl, min_top_left, min_self]
  | ⟨2, _⟩, _ => by
    -- The copies of `(C, 3)` and `(D, 3)`, labelled `G`: `strip3 A_C`, up to `G`.
    refine transformsTo_kindVal _ _ (isWitness_strip3 (A := AC) hG) ?_ ?_ (fun _ ↦ ?_)
      (fun _ ↦ ?_) (fun h ↦ absurd h (by simp))
    · simp only [copyKind, CellKind.val]
      rw [strip3_w2, constStepSuppressor_of_le _ (by omega)]
      exact min_visibilityReplace_A hH h1 h2
    · simp only [copyKind, CellKind.val]
      rw [strip3_w3, constStepSuppressor_of_le _ (by omega), min_top_left, min_eq_right hGA]
    · simp only [copyKind, CellKind.val]
      rw [strip3_w2, constStepSuppressor_of_le _ (by omega)]
      exact min_visibilityReplace_H hH h1 h2
    · simp only [copyKind, CellKind.val]
      rw [strip3_w3, constStepSuppressor_of_le _ le_rfl, min_top_left, min_self]
  | ⟨3, _⟩, _ => by
    -- The copies of `(C, 4)` and `(D, 4)`: their label is `⊥`.
    simp only [copyKind, CellKind.val, min_bot_right]
    exact TransformsTo.bot _ _

variable (hIL : I.left = TH α) (hIR : I.right = TG α)
include hIL hIR

/-- **The labelling by kinds, read through the bases, is lawful** on the canonical multi-layer
scheme of the copy rows `rowsHG`, for parameters self-visible at `1`, `1`, `2`, `3` and coupled as
in `TH` and `TG`, with `⊥` at the cells of grade `4`. -/
theorem isLawful_kindVal {AC AD : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G)
    (hTH : Coupled true AC H G) (hTG : Coupled false AD H G) :
    (canonicalMultiScheme I (rowsHG I)).rows.IsLawful
      fun z ↦ kindVal I AC AD H G ⊥ (copyBase I z) := by
  obtain ⟨h1, h2⟩ : H ≤ AC ∧ min AC G ≤ H := by simpa [Coupled] using hTH
  have hGA : G ≤ AD := by simpa [Coupled] using hTG
  have hcopy (k : Fin 4) (i : Fin 2) :
      kindVal I AC AD H G ⊥ (copyBase I (multiNewCell I canonicalMult k i)) =
        (copyKind k i).val AC AD H G ⊥ := by
    rw [copyBase_multiNewCell, kindVal, kindOld_copyOrig]
  refine isLawful_multiLayerScheme_of ?_ (fun k i ↦ ?_) (fun k i ↦ ?_) (fun s k hs ↦ ?_)
  · simp only [copyBase_multiOldCell]
    exact isLawful_amalgam_kindOld hIL hIR hAC hAD hH hG hTH hTG
  · rw [hcopy]
    exact isSelfVisible_copyKind hAC hAD hH hG k i
  · -- Locality at a copy: the witness of the corresponding new cell of `schemeHG`.
    simp only [canonicalRows_apply]
    rw [hcopy]
    exact transformsTo_copy hAC hAD hH hG h1 h2 hGA k i
  · -- Availability: every cell of grade `k + 1` is at most the copy of its kind.
    have hgs := (grade_copyBase (rowsHG I) s).trans hs
    obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_kindOld (copyBase I s)
    change ∃ i, kindVal I AC AD H G ⊥ (copyBase I s) ≤
      kindVal I AC AD H G ⊥ (copyBase I (multiNewCell I canonicalMult k i))
    simp only [hcopy]
    unfold kindVal
    cases hk : kindOld (I.amalgam.toCellScheme.gradedIndex (copyBase I s)) with
    | dead => exact ⟨0, bot_le⟩
    | top => exact ⟨0, bot_le⟩
    | ac =>
      obtain rfl : k = 0 := Fin.ext (by have := (g1 hk).symm.trans hgs; omega)
      exact ⟨0, le_rfl⟩
    | ad =>
      obtain rfl : k = 0 := Fin.ext (by have := (g2 hk).symm.trans hgs; omega)
      exact ⟨1, le_rfl⟩
    | h =>
      obtain rfl : k = 1 := Fin.ext (by have := (g3 hk).symm.trans hgs; omega)
      exact ⟨0, le_rfl⟩
    | g =>
      obtain rfl : k = 2 := Fin.ext (by have := (g4 hk).symm.trans hgs; omega)
      exact ⟨0, le_rfl⟩

omit hIL hIR in
/-- Two labellings by kinds agree at a cell when their parameters agree at its kind. -/
theorem kindVal_congr {d : Fin I.amalgam.card} {AC AD Q AC' AD' H' G' Q' : Label.{u}}
    (hac : kindOld (I.amalgam.toCellScheme.gradedIndex d) = .ac → AC = AC')
    (had : kindOld (I.amalgam.toCellScheme.gradedIndex d) = .ad → AD = AD')
    (hh : kindOld (I.amalgam.toCellScheme.gradedIndex d) = .h → H = H')
    (hg : kindOld (I.amalgam.toCellScheme.gradedIndex d) = .g → G = G')
    (htop : kindOld (I.amalgam.toCellScheme.gradedIndex d) = .top → Q = Q') :
    kindVal I AC AD H G Q d = kindVal I AC' AD' H' G' Q' d := by
  unfold kindVal
  cases hk : kindOld (I.amalgam.toCellScheme.gradedIndex d) with
  | dead => rfl
  | ac => exact hac hk
  | ad => exact had hk
  | h => exact hh hk
  | g => exact hg hk
  | top => exact htop hk

/-- **The product clause below the top grade**: at every grade `j ≤ 3`, every labelling of the
amalgam lawful below both coatoms, read through the bases, is lawful below `(univ, j)`.  It is a
labelling by kinds on each coatom; the parameters `H` and `G` of the common face agree when their
cells are below the grade `j`, and the labelling by kinds of the four parameters (with `⊥` for the
parameters above `j`) is lawful (`isLawful_kindVal`). -/
theorem canonicalProduct {j : ℕ} (hj : j ≤ 3) : I.CanonicalProduct (rowsHG I) j := by
  intro v hC hD
  have hC' := hC
  have hD' := hD
  rw [coatomC_eq] at hC'
  rw [coatomD_eq] at hD'
  obtain ⟨A, H, G, hA, hH, hG, hcC, hallC⟩ :=
    exists_lab_of_comap (hIL ▸ I.restrictFace_left) hj (fun d ↦ v d) hC'
  obtain ⟨A', H', G', hA', hH', hG', hcD, hallD⟩ :=
    exists_lab_of_comap (hIR ▸ I.restrictFace_right) hj (fun d ↦ v d) hD'
  have valC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatomC, j)) :
      v d = kindVal I A ⊥ H G ⊥ d := by
    obtain ⟨c, hgc, hpc⟩ := hallC d (by rwa [← coatomC_eq])
    rw [hpc, kindVal, hgc, kindOld_left, val_leftKind]
  have valD (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatomD, j)) :
      v d = kindVal I ⊥ A' H' G' ⊥ d := by
    obtain ⟨c, hgc, hpc⟩ := hallD d (by rwa [← coatomD_eq])
    rw [hpc, kindVal, hgc, kindOld_right, val_rightKind]
  -- The parameters of the common face agree below the grade `j`.
  obtain ⟨-, -, e₂, e₃, -, -, he₂, he₃⟩ := exists_paramCells hIL hIR
  have face (e : Fin I.amalgam.card) {X : Finset (Fin 5) × ℕ}
      (he : I.amalgam.toCellScheme.gradedIndex e = X) (hX : X.1 = {0, 1, 2}) (hXj : X.2 ≤ j) :
      kindVal I A ⊥ H G ⊥ e = kindVal I ⊥ A' H' G' ⊥ e := by
    rw [← valC e ⟨by rw [he, hX]; exact (by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomC),
        by rw [he]; exact hXj⟩,
      ← valD e ⟨by rw [he, hX]; exact (by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomD),
        by rw [he]; exact hXj⟩]
  have hHH (h2 : 2 ≤ j) : H = H' := by
    have := face e₂ he₂ rfl h2
    simpa [kindVal, he₂, show kindOld (({0, 1, 2} : Finset (Fin 5)), 2) = .h by decide,
      CellKind.val] using this
  have hGG (h3 : 3 ≤ j) : G = G' := by
    have := face e₃ he₃ rfl h3
    simpa [kindVal, he₃, show kindOld (({0, 1, 2} : Finset (Fin 5)), 3) = .g by decide,
      CellKind.val] using this
  obtain ⟨hHA, hAGH⟩ : H ≤ A ∧ min A G ≤ H := by simpa [Coupled] using hcC
  have hGA' : G' ≤ A' := by simpa [Coupled] using hcD
  -- The four parameters, with `⊥` above the grade `j`.
  set H₀ : Label.{u} := if 2 ≤ j then H else ⊥ with hH₀
  set G₀ : Label.{u} := if 3 ≤ j then G else ⊥ with hG₀
  have sH₀ : IsSelfVisible 2 H₀ := by rw [hH₀]; split_ifs; exacts [hH, isSelfVisible_bot 2]
  have sG₀ : IsSelfVisible 3 G₀ := by rw [hG₀]; split_ifs; exacts [hG, isSelfVisible_bot 3]
  have cTH : Coupled true A H₀ G₀ := by
    simp only [Coupled, ite_true]
    by_cases h3 : 3 ≤ j
    · rw [hH₀, hG₀, ite_eq_left (by omega : 2 ≤ j), ite_eq_left h3]; exact ⟨hHA, hAGH⟩
    · rw [hG₀, ite_eq_right h3, min_bot_right]
      refine ⟨?_, bot_le⟩
      rw [hH₀]; split_ifs
      exacts [hHA, bot_le]
  have cTG : Coupled false A' H₀ G₀ := by
    simp only [Coupled, Bool.false_eq_true, ite_false]
    rw [hG₀]; split_ifs with h3
    exacts [(hGG h3).trans_le hGA', bot_le]
  have hK := (isLawful_kindVal hIL hIR hA hA' sH₀ sG₀ cTH cTG).isLawfulBelow
    ((univ : Finset (Fin 5)), j)
  refine (Rows.isLawfulBelow_congr (w := fun z ↦ kindVal I A A' H₀ G₀ ⊥ (copyBase I z))
    (w' := fun z ↦ v (copyBase I z)) fun z hz ↦ ?_).mp hK
  -- At each cell below `(univ, j)`, the labelling by kinds is `v` at the base.
  have hgz : I.amalgam.toCellScheme.grade (copyBase I z) ≤ j :=
    (grade_copyBase (rowsHG I) z).trans_le hz.2
  obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_kindOld (copyBase I z)
  obtain ⟨-, s2, -, -, -⟩ := kindOld_spec (I.amalgam.toCellScheme.gradedIndex (copyBase I z))
  obtain ⟨s1, -, -, -, -⟩ := kindOld_spec (I.amalgam.toCellScheme.gradedIndex (copyBase I z))
  have top (h : kindOld (I.amalgam.toCellScheme.gradedIndex (copyBase I z)) = .top) : False := by
    have := g5.mp h; omega
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem (copyBase I z))
    (I.scope_ne_univ (copyBase I z)) with hs | hs
  · rw [valC _ ⟨hs, hgz⟩]
    refine kindVal_congr (fun _ ↦ rfl) (fun h ↦ absurd (hs (s2 h).2) (by decide)) (fun h ↦ ?_)
      (fun h ↦ ?_) (fun h ↦ (top h).elim)
    · rw [hH₀, ite_eq_left (by have := g3 h; omega)]
    · rw [hG₀, ite_eq_left (by have := g4 h; omega)]
  · rw [valD _ ⟨hs, hgz⟩]
    refine kindVal_congr (fun h ↦ absurd (hs (s1 h).2) (by decide)) (fun _ ↦ rfl) (fun h ↦ ?_)
      (fun h ↦ ?_) (fun h ↦ (top h).elim)
    · have h2 : 2 ≤ j := by have := g3 h; omega
      rw [hH₀, ite_eq_left h2, hHH h2]
    · have h3 : 3 ≤ j := by have := g4 h; omega
      rw [hG₀, ite_eq_left h3, hGG h3]

omit hIL hIR in
/-- A labelling by kinds with values below `o` (and `⊥ < o`) is below `o`. -/
theorem kindVal_lt {AC AD H G Q o : Label.{u}} (hb : (⊥ : Label.{u}) < o) (hAC : AC < o)
    (hAD : AD < o) (hH : H < o) (hG : G < o) (hQ : Q < o) (d : Fin I.amalgam.card) :
    kindVal I AC AD H G Q d < o := by
  unfold kindVal
  cases kindOld (I.amalgam.toCellScheme.gradedIndex d) <;> assumption

omit hIL hIR in
/-- The copy rows at the grades `1`, `2`, `3` are coded. -/
theorem rowsHG_lt (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card) (hk : (k : ℕ) ≤ 2) :
    rowsHG I k i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have hb : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  have l (a b : ℕ) := gridPoint_lt_omega0_sq.{u} a b
  match k, i with
  | ⟨0, _⟩, ⟨0, _⟩ => exact kindVal_lt hb (l 2 1) (l 1 0) hb hb hb d
  | ⟨0, _⟩, ⟨1, _⟩ => exact kindVal_lt hb (l 1 0) (l 2 1) hb hb hb d
  | ⟨1, _⟩, _ => exact kindVal_lt hb (l 2 1) (l 1 0) (l 2 1) hb hb d
  | ⟨2, _⟩, _ => exact kindVal_lt hb (l 2 0) (l 3 1) (l 2 0) (l 3 1) hb d
  | ⟨3, _⟩, _ => exact absurd hk (by simp)

/-- The copy rows at the grades `1`, `2`, `3` are lawful below both coatoms: each is a labelling
by kinds of parameters coupled as in `TH` and `TG`. -/
theorem isLawfulBelow_rowsHG (k : Fin 4) (i : Fin 2) (hk : (k : ℕ) ≤ 2) :
    I.amalgam.rows.IsLawfulBelow (coatomC, (k : ℕ) + 1) (fun d ↦ rowsHG I k i d) ∧
      I.amalgam.rows.IsLawfulBelow (coatomD, (k : ℕ) + 1) (fun d ↦ rowsHG I k i d) := by
  have both {AC AD H G : Label.{u}} (h : I.amalgam.rows.IsLawful (kindVal I AC AD H G ⊥))
      (X Y : Finset (Fin 5) × ℕ) :
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ kindVal I AC AD H G ⊥ d) ∧
        I.amalgam.rows.IsLawfulBelow Y (fun d ↦ kindVal I AC AD H G ⊥ d) :=
    ⟨h.isLawfulBelow X, h.isLawfulBelow Y⟩
  match k, i with
  | ⟨0, _⟩, ⟨0, _⟩ => exact both (isLawful_amalgam_kindOld hIL hIR
      (isSelfVisible_v2.mono (by omega)) isSelfVisible_v1 (isSelfVisible_bot 2)
      (isSelfVisible_bot 3) (by simp [Coupled]) (by simp [Coupled])) _ _
  | ⟨0, _⟩, ⟨1, _⟩ => exact both (isLawful_amalgam_kindOld hIL hIR isSelfVisible_v1
      (isSelfVisible_v2.mono (by omega)) (isSelfVisible_bot 2) (isSelfVisible_bot 3)
      (by simp [Coupled]) (by simp [Coupled])) _ _
  | ⟨1, _⟩, _ => exact both (isLawful_amalgam_kindOld hIL hIR
      (isSelfVisible_v2.mono (by omega)) isSelfVisible_v1 isSelfVisible_v2 (isSelfVisible_bot 3)
      (by simp [Coupled]) (by simp [Coupled])) _ _
  | ⟨2, _⟩, _ => exact both (isLawful_amalgam_kindOld hIL hIR
      (isSelfVisible_w2.mono (by omega)) (isSelfVisible_w3.mono (by omega)) isSelfVisible_w2
      isSelfVisible_w3 (by simp [Coupled, min_le_iff]) (by simp [Coupled])) _ _
  | ⟨3, _⟩, _ => exact absurd hk (by simp)

end VaughtConjecture.OrderedLayer.CanonicalHG

namespace VaughtConjecture.Seed

open OrderedLayer OrderedLayer.CanonicalHG
open CrossedCouplingCounterexample (TH TG seedHG hasBottomApexes_HG)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The canonical multi-layer step of a seed of `TH` and `TG`**, with the copy rows
`OrderedLayer.CanonicalHG.rowsHG`: the product clause holds below the top grade, and the seed has
bottom apexes (`Seed.canonicalMultiStep_of_productBelowTop`). -/
theorem canonicalMultiStep_of_TH_TG (hIL : I.left = TH α) (hIR : I.right = TG α) :
    I.MultiLayerStep canonicalMult (canonicalRows I (rowsHG I)) :=
  canonicalMultiStep_of_productBelowTop (hasBottomApexes_HG hIL hIR) (fun _ ↦ rfl)
    (fun _ _ hj ↦ canonicalProduct hIL hIR hj) (fun k i d hk _ ↦ rowsHG_lt k i d hk)
    (fun k i hk ↦ isLawfulBelow_rowsHG hIL hIR k i hk)

/-- **`seedHG` has a completion below the full grade by the canonical multi-layer scheme**: two
copies of `(C, k)` and `(D, k)` at each `(univ, k)`. -/
theorem nonempty_completionBelowFullGrade_canonical_seedHG :
    Nonempty (CompletionBelowFullGrade (seedHG α)) :=
  (canonicalMultiStep_of_TH_TG (I := seedHG α) rfl rfl).nonempty_completionBelowFullGrade

end VaughtConjecture.Seed

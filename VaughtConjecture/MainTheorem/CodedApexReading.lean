/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ApexCompletionReading
import VaughtConjecture.MainTheorem.CodedLevelControl
import VaughtConjecture.MainTheorem.CodedLevelFaces
import VaughtConjecture.Extension.StronglyCodedCompletion

/-!
# Reading a coded level after adding the strongly coded apex

Roadmap, Layer 3 ((R3) and (R4), recognition on the completion of the levels) and Correspondence,
item 1 (the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.ApexCompletionReading` for the completion by the
strongly coded apex (`StageType.addStrongApex`) in place of `StageType.addApex`, and for the coded
levels (`Seed.codedLvLevel`). The proofs are those of
`VaughtConjecture.MainTheorem.ApexCompletionReading`: they use of the apex only that it is one cell
of full scope and full grade appended last, with the old rows and labels kept
(`StageType.addStrongApex_label_castSucc`); the row of the apex is never read, the apex being above
every cell at the threshold. So the transport of the controller clauses through the completion
(`Seed.addStrongApex_ladderController_of_levelShape`) needs no fact about the old apex row.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

/-! ### Adding the apex keeps the old cells -/

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ} {t : StageType.{u} α k} (ht : t.IsLegalBelowFullGrade)
  (hn : 0 < k)

/-- After adding the strongly coded apex, an old cell keeps its label. -/
@[simp] theorem addStrongApex_label_castSucc (d : Fin t.card) :
    (t.addStrongApex ht hn).label d.castSucc = t.label d :=
  apexLabel_castSucc d

/-- **After adding the apex, an old cell reads an old cell as before.** -/
theorem rowAt_addStrongApex_castSucc (z x : Fin t.card) :
    (t.addStrongApex ht hn).toScheme.rowAt z.castSucc x.castSucc = t.toScheme.rowAt z x :=
  Scheme.rowAt_appendFullCell_castSucc (h := ht.not_le) z x

/-- After adding the apex, an old cell keeps its graded index. -/
theorem gradedIndex_addStrongApex_castSucc (z : Fin t.card) :
    (t.addStrongApex ht hn).toCellScheme.gradedIndex z.castSucc = t.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z

/-- The apex has full scope and the full grade. -/
theorem gradedIndex_addStrongApex_last :
    (t.addStrongApex ht hn).toCellScheme.gradedIndex (Fin.last _) = ((univ : Finset (Fin k)), k) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- **A cell of the completion below the full grade is old**, with its graded index. -/
theorem exists_castSucc_of_gradedIndex_addStrongApex {X : Finset (Fin k)} {i : ℕ} (hi : i < k)
    (z : Fin (t.addStrongApex ht hn).card)
    (hz : (t.addStrongApex ht hn).toCellScheme.gradedIndex z = (X, i)) :
    ∃ z' : Fin t.card, z = z'.castSucc ∧ t.toCellScheme.gradedIndex z' = (X, i) := by
  -- a cell of the completion is an old cell or the apex
  change Fin (t.card + 1) at z
  induction z using Fin.lastCases with
  | last =>
    exfalso
    have h := congrArg Prod.snd (hz.symm.trans (gradedIndex_addStrongApex_last ht hn))
    simp only at h
    omega
  | cast z => exact ⟨z, rfl, (gradedIndex_addStrongApex_castSucc ht hn z).symm.trans hz⟩

/-- **The apex is never at the activation grade**: for requests on a context on `J` points, the
apex of a completion on `J + 1` points has the full grade `J + 1`, above the threshold. -/
theorem gradedIndex_addStrongApex_last_ne_threshold {J n' : ℕ} {t' : StageType.{u} α J}
    {D : Scheme.{u} (n' + 1)} (Q : GrowthRequests t' D) {t : StageType.{u} α (J + 1)}
    (ht : t.IsLegalBelowFullGrade) (hn : 0 < J + 1) :
    (t.addStrongApex ht hn).toCellScheme.gradedIndex (Fin.last _) ≠
      ((univ : Finset (Fin (J + 1))), Q.threshold) := fun h ↦ by
  have h1 := congrArg Prod.snd ((gradedIndex_addStrongApex_last ht hn).symm.trans h)
  have h2 := Q.threshold_le
  simp only at h1
  omega

/-- **Every cell of the completion at the activation grade is old**: for requests on a context on
`J` points, a cell of a completion on `J + 1` points at `(univ, threshold)` is an old cell at
`(univ, threshold)`. -/
theorem exists_castSucc_of_gradedIndex_threshold_coded {J n' : ℕ} {t' : StageType.{u} α J}
    {D : Scheme.{u} (n' + 1)} (Q : GrowthRequests t' D) {t : StageType.{u} α (J + 1)}
    (ht : t.IsLegalBelowFullGrade) (hn : 0 < J + 1) (z : Fin (t.addStrongApex ht hn).card)
    (hz : (t.addStrongApex ht hn).toCellScheme.gradedIndex z =
      ((univ : Finset (Fin (J + 1))), Q.threshold)) :
    ∃ z' : Fin t.card, z = z'.castSucc ∧
      t.toCellScheme.gradedIndex z' = ((univ : Finset (Fin (J + 1))), Q.threshold) :=
  exists_castSucc_of_gradedIndex_addStrongApex ht hn (by have := Q.threshold_le; omega) z hz

/-- **The completion keeps the labels of a labelling reduced to the stage** where they already lie
at the stage: if the label of an old cell is the reduction of a label at the stage, the completion
carries that label there. -/
theorem label_addStrongApex_castSucc_of_reduce {z : Fin t.card} {y : Label.{u}}
    (hz : t.label z = Label.reduce α y) (hy : Label.AtStage α y) :
    (t.addStrongApex ht hn).label z.castSucc = y :=
  (addStrongApex_label_castSucc ht hn z).trans (hz.trans hy.reduce_eq)

end StageType

/-! ### The shape of a level -/

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

/-! ### Reading a level through the completion -/

variable {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

section Shape

variable {j : ℕ} {N : I.ALvl g H j} {t : StageType.{u} α (m + 2)}
  (ht : t.IsLegalBelowFullGrade) (hn : 0 < m + 2) {κ : Fin N.S.card → Fin t.card}

/-- **Through the completion, a cell of the level reads the cells of the level as the level
does** (the shape of the level: `κ` keeps rows). -/
theorem rowAt_addStrongApex_of_levelShape
    (hrow : ∀ u x, t.toScheme.rowAt (κ u) (κ x) = N.S.rowAt u x) (u x : Fin N.S.card) :
    (t.addStrongApex ht hn).toScheme.rowAt (κ u).castSucc (κ x).castSucc = N.S.rowAt u x :=
  (StageType.rowAt_addStrongApex_castSucc ht hn _ _).trans (hrow u x)

/-- **Every cell of the completion of full scope below the full grade is a cell of the level**,
with its graded index (the shape of a level: `κ` keeps graded indices and reaches every cell of
full scope). -/
theorem exists_level_of_gradedIndex_addStrongApex
    (hgi : ∀ u, t.toCellScheme.gradedIndex (κ u) = N.S.toCellScheme.gradedIndex u)
    (hfull : ∀ z, t.toCellScheme.scope z = univ → z ∈ Set.range κ) {i : ℕ} (hi : i < m + 2)
    (z : Fin (t.addStrongApex ht hn).card)
    (hz : (t.addStrongApex ht hn).toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), i)) :
    ∃ u' : Fin N.S.card, z = (κ u').castSucc ∧
      N.S.toCellScheme.gradedIndex u' = ((univ : Finset (Fin (m + 2))), i) := by
  obtain ⟨z', rfl, hz'⟩ := StageType.exists_castSucc_of_gradedIndex_addStrongApex ht hn hi z hz
  obtain ⟨u', rfl⟩ := hfull z' (congrArg Prod.fst hz')
  exact ⟨u', rfl, (hgi u').symm.trans hz'⟩

/-- **The labels of the attachment survive the completion**: for a stage type labelled by the
reduction to the stage of a labelling `q` extending the labels of the attachment through the
shape map, the completion carries at the cell of a cell `c` of the attachment its actual label,
`⊤` included. -/
theorem label_addStrongApex_attEmb_of_levelShape {q : Fin t.card → Label.{u}}
    (hlab : ∀ z, t.label z = Label.reduce α (q z))
    (hqe : ∀ c, q (κ (N.attEmb c)) = (I.attachmentType g).label c)
    (c : Fin (I.attachment g).card) :
    (t.addStrongApex ht hn).label (κ (N.attEmb c)).castSucc = (I.attachmentType g).label c :=
  StageType.label_addStrongApex_castSucc_of_reduce ht hn ((hlab _).trans (by rw [hqe]))
    ((I.attachmentType g).atStage c)

/-- **At a cell of the context**, the completion carries the label of the context. -/
theorem label_addStrongApex_attachCtxCell_of_levelShape {q : Fin t.card → Label.{u}}
    (hlab : ∀ z, t.label z = Label.reduce α (q z))
    (hqe : ∀ c, q (κ (N.attEmb c)) = (I.attachmentType g).label c) (x : Fin I.left.card) :
    (t.addStrongApex ht hn).label (κ (N.attEmb
        (I.attachCtxCell g x))).castSucc = I.left.label x := by
  rw [label_addStrongApex_attEmb_of_levelShape ht hn hlab hqe, attachCtxCell_eq,
    StageType.label_faceCell]

end Shape

/-- **The controller clauses survive every completion by the apex** of a stage type carrying the
level at the grade `j + 1` (any `j`): every cell of the completion at `(univ, threshold)`, for
requests calibrated on the class with threshold `≥ 2`, is the cell of a cell `u'` of the level,
and for some member `a` and table `F` it stores on the context and donor cells (the cells of the
attachment) an admitted state, reads the top rung at least as high as the cap, the rungs as `F`,
and every positive stored value below the cap as a rung.  The apex is not among these cells
(`StageType.gradedIndex_addStrongApex_last_ne_threshold`); the bottom state stores `⊥`. -/
theorem addStrongApex_ladderController_of_levelShape (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {p₀ : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold) {j : ℕ}
    {t : StageType.{u} α (m + 2)} (ht : t.IsLegalBelowFullGrade) (hn : 0 < m + 2)
    {κ : Fin (I.codedLvLevel g H B hd Q j).S.card → Fin t.card}
    (hrow : ∀ u x, t.toScheme.rowAt (κ u) (κ x) = (I.codedLvLevel g H B hd Q j).S.rowAt u x)
    (hgi : ∀ u, t.toCellScheme.gradedIndex (κ u) =
      (I.codedLvLevel g H B hd Q j).S.toCellScheme.gradedIndex u)
    (hfull : ∀ z, t.toCellScheme.scope z = univ → z ∈ Set.range κ)
    (u : Fin (t.addStrongApex ht hn).card)
    (hu : (t.addStrongApex ht hn).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), Q.threshold)) :
    ∃ u' : Fin (I.codedLvLevel g H B hd Q j).S.card, u = (κ u').castSucc ∧
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}),
        Q.AdmitsOnClass
          (fun x ↦ (t.addStrongApex ht hn).toScheme.rowAt u
            (κ ((I.codedLvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))).castSucc)
          (fun y ↦ (t.addStrongApex ht hn).toScheme.rowAt u
            (κ ((I.codedLvLevel g H B hd Q j).attEmb (I.attachDonCell g hd y))).castSucc) ∧
        (t.addStrongApex ht hn).toScheme.rowAt u
            (κ ((I.codedLvLevel g H B hd Q j).attEmb (I.attachCtxCell g Q.cap))).castSucc ≤
          (t.addStrongApex ht hn).toScheme.rowAt u
            (κ ((I.codedLvLevel g H B hd Q j).embed (lvRung hH a (H - 1)))).castSucc ∧
        (∀ i < H, (t.addStrongApex ht hn).toScheme.rowAt u
            (κ ((I.codedLvLevel g H B hd Q j).embed (lvRung hH a i))).castSucc = F (i + 1)) ∧
        ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
          (t.addStrongApex ht hn).toScheme.rowAt u
              (κ ((I.codedLvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))).castSucc ≠ ⊥ →
            ∃ i < H, (t.addStrongApex ht hn).toScheme.rowAt u
              (κ ((I.codedLvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))).castSucc =
                F (i + 1) := by
  have hNm : Q.threshold < m + 2 := by have := Q.threshold_le; omega
  obtain ⟨u', rfl, hu'⟩ := exists_level_of_gradedIndex_addStrongApex ht hn hgi hfull hNm u hu
  obtain ⟨a, F, hadm, htop, hrung, hval⟩ := codedLvLevel_ladderController hH hcard hQ hB hN2 u' hu'
  refine ⟨u', rfl, a, F, ?_, ?_, fun i hi ↦ ?_, fun x hx hx0 ↦ ?_⟩
  · simp only [rowAt_addStrongApex_of_levelShape ht hn hrow]
    exact hadm
  · rw [rowAt_addStrongApex_of_levelShape ht hn hrow, rowAt_addStrongApex_of_levelShape ht hn hrow]
    exact htop
  · rw [rowAt_addStrongApex_of_levelShape ht hn hrow]
    exact hrung i hi
  · rw [rowAt_addStrongApex_of_levelShape ht hn hrow] at hx0 ⊢
    exact hval x hx hx0

end Seed

end VaughtConjecture

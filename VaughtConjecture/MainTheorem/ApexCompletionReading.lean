/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrier

/-!
# Reading a level after adding the apex

Roadmap, Layer 3 ((R3) and (R4), recognition on the completion of the levels re-rendered per
grade).

Recognition on a level (`Seed.lvLevel_ladderController`) is a statement about rows of the level;
the carrier is a completion of a scheme carrying the level, with the apex added
(`StageType.addApex`).  This file checks that the completion step is a verbatim transport of
that recognition data, for **every** completion by the apex of **every** stage type carrying a
level in the following sense (the shape of a level): a map `κ` from the cells of the level into
the cells of the stage type keeping rows and graded indices, whose range contains every cell of
full scope.  The replicated level (`Seed.ALvl.Good.rep`, copies at the mixed faces) has this shape
along `Fin.castAdd`, at every grade and for every admission predicate
(`Seed.ALvl.Good.rep_rowAt_castAdd`, `Seed.ALvl.Good.rep_gradedIndex_castAdd`,
`Seed.ALvl.Good.rep_mem_range_castAdd_of_scope_univ`).

* **Old rows survive** (`StageType.rowAt_addApex_castSucc`, `Seed.rowAt_addApex_of_levelShape`):
  after adding the apex, an old cell reads an old cell as before; through `κ`, a cell of the level
  reads every cell of the level (rungs `Seed.lvRung` and cells of the attachment included) as in
  the level.
* **The apex is never at the activation grade** (`StageType.GrowthRequests.threshold_le`,
  `StageType.gradedIndex_addApex_last_ne_threshold`): the threshold of requests on a context on
  `J` points is at most `J` (the cap is a cell of the context, its grade at most the size of its
  scope), while the apex of a completion on `J + 1` points has the full grade `J + 1`.
* **Every cell at the activation grade is old** (`StageType.exists_castSucc_of_gradedIndex_addApex`,
  `Seed.exists_level_of_gradedIndex_addApex`): a cell of the completion at `(univ, threshold)` is
  `κ u'` for a cell `u'` of full scope of the level at the threshold.  So no new controller
  appears, and the copies are never controllers.
* **The controller clauses survive** (`Seed.addApex_ladderController_of_levelShape`): every cell
  of the completion at the threshold `≥ 2` satisfies the four clauses of
  `Seed.lvLevel_ladderController`, read through `κ`, at every level `j`.  The bottom state is
  covered as in the level: it stores `⊥`.
* **The labels survive** (`StageType.label_addApex_castSucc_of_reduce`,
  `Seed.label_addApex_attEmb_of_levelShape`): for a labelling reduced to the stage from a lawful
  labelling extending the labels of the attachment, the completion carries at the cell of a cell
  of the attachment its actual label, `⊤` included; at a cell of the context, the label of the
  context.

The completion of the replicated top level used by the carrier (`Seed.lvRepCompletion`) is an
instance (`Seed.lvRepCompletion_ladderController_of_levelShape`,
`Seed.lvRepCompletion_label_attachCtxCell`), and so are the three test inputs
(`TieInstance.lvRepCompletion_reading_tie`, `ApexInstance.lvRepCompletion_reading_apex`,
`QuadInstance.lvRepCompletion_reading_quad`): at each of them the apex is not at the threshold
(`2`, `3`, `4`), every cell at the threshold is old with the four clauses, and the completion
carries `⊤` at the cell of a context cell labelled `⊤`.

## References

The completion of [Kni26, Definition 4.3.14]; the controllers of the growth step are those of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

/-! ### Adding the apex keeps the old cells -/

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ} {t : StageType.{u} α k} (ht : t.IsLegalBelowFullGrade)
  (hn : 0 < k)

/-- **After adding the apex, an old cell reads an old cell as before.** -/
theorem rowAt_addApex_castSucc (z x : Fin t.card) :
    (t.addApex ht hn).toScheme.rowAt z.castSucc x.castSucc = t.toScheme.rowAt z x :=
  Scheme.rowAt_appendFullCell_castSucc (h := ht.not_le) z x

/-- After adding the apex, an old cell keeps its graded index. -/
theorem gradedIndex_addApex_castSucc (z : Fin t.card) :
    (t.addApex ht hn).toCellScheme.gradedIndex z.castSucc = t.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z

/-- The apex has full scope and the full grade. -/
theorem gradedIndex_addApex_last :
    (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _) = ((univ : Finset (Fin k)), k) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- **A cell of the completion below the full grade is old**, with its graded index. -/
theorem exists_castSucc_of_gradedIndex_addApex {X : Finset (Fin k)} {i : ℕ} (hi : i < k)
    (z : Fin (t.addApex ht hn).card)
    (hz : (t.addApex ht hn).toCellScheme.gradedIndex z = (X, i)) :
    ∃ z' : Fin t.card, z = z'.castSucc ∧ t.toCellScheme.gradedIndex z' = (X, i) := by
  change Fin (t.card + 1) at z
  induction z using Fin.lastCases with
  | last =>
    exfalso
    have h := congrArg Prod.snd (hz.symm.trans (gradedIndex_addApex_last ht hn))
    simp only at h
    omega
  | cast z => exact ⟨z, rfl, (gradedIndex_addApex_castSucc ht hn z).symm.trans hz⟩

/-- **The threshold of requests on a context on `J` points is at most `J`**: the cap is a cell of
the context, and the grade of a cell is at most the size of its scope. -/
theorem GrowthRequests.threshold_le {J n' : ℕ} {t' : StageType.{u} α J}
    {D : Scheme.{u} (n' + 1)} (Q : GrowthRequests t' D) : Q.threshold ≤ J :=
  (t'.isWellFormed.isWellFormed.grade_le_card Q.cap).trans
    ((card_le_univ _).trans (by simp))

/-- **The apex is never at the activation grade**: for requests on a context on `J` points, the
apex of a completion on `J + 1` points has the full grade `J + 1`, above the threshold. -/
theorem gradedIndex_addApex_last_ne_threshold {J n' : ℕ} {t' : StageType.{u} α J}
    {D : Scheme.{u} (n' + 1)} (Q : GrowthRequests t' D) {t : StageType.{u} α (J + 1)}
    (ht : t.IsLegalBelowFullGrade) (hn : 0 < J + 1) :
    (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _) ≠
      ((univ : Finset (Fin (J + 1))), Q.threshold) := fun h ↦ by
  have h1 := congrArg Prod.snd ((gradedIndex_addApex_last ht hn).symm.trans h)
  have h2 := Q.threshold_le
  simp only at h1
  omega

/-- **Every cell of the completion at the activation grade is old**: for requests on a context on
`J` points, a cell of a completion on `J + 1` points at `(univ, threshold)` is an old cell at
`(univ, threshold)`. -/
theorem exists_castSucc_of_gradedIndex_threshold {J n' : ℕ} {t' : StageType.{u} α J}
    {D : Scheme.{u} (n' + 1)} (Q : GrowthRequests t' D) {t : StageType.{u} α (J + 1)}
    (ht : t.IsLegalBelowFullGrade) (hn : 0 < J + 1) (z : Fin (t.addApex ht hn).card)
    (hz : (t.addApex ht hn).toCellScheme.gradedIndex z =
      ((univ : Finset (Fin (J + 1))), Q.threshold)) :
    ∃ z' : Fin t.card, z = z'.castSucc ∧
      t.toCellScheme.gradedIndex z' = ((univ : Finset (Fin (J + 1))), Q.threshold) :=
  exists_castSucc_of_gradedIndex_addApex ht hn (by have := Q.threshold_le; omega) z hz

/-- **The completion keeps the labels of a labelling reduced to the stage** where they already lie
at the stage: if the label of an old cell is the reduction of a label at the stage, the completion
carries that label there. -/
theorem label_addApex_castSucc_of_reduce {z : Fin t.card} {y : Label.{u}}
    (hz : t.label z = Label.reduce α y) (hy : Label.AtStage α y) :
    (t.addApex ht hn).label z.castSucc = y :=
  (addApex_label_castSucc ht hn z).trans (hz.trans hy.reduce_eq)

end StageType

/-! ### The shape of a level -/

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

namespace ALvl.Good

variable {j : ℕ} {N : I.ALvl g H j} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}
  (hN : N.Good B A)

/-- The replicated level reads the cells of the level as the level does. -/
theorem rep_rowAt_castAdd (u x : Fin N.S.card) :
    hN.rep.rowAt (Fin.castAdd _ u) (Fin.castAdd _ x) = N.S.rowAt u x :=
  Scheme.rowAt_mirror_castAdd _ _

/-- The cells of the level keep their graded indices in the replicated level. -/
theorem rep_gradedIndex_castAdd (u : Fin N.S.card) :
    hN.rep.toCellScheme.gradedIndex (Fin.castAdd _ u) = N.S.toCellScheme.gradedIndex u :=
  Scheme.gradedIndex_mirror_castAdd (hmix := hN.not_subset_scope) u

/-- **A cell of full scope of the replicated level is a cell of the level**, at every grade and for
every admission predicate: the copies have mixed scope. -/
theorem rep_mem_range_castAdd_of_scope_univ (z : Fin hN.rep.card)
    (hz : hN.rep.toCellScheme.scope z = univ) :
    z ∈ Set.range (Fin.castAdd (N.S.copyCount (I.mixedFaces g)) : Fin N.S.card → _) := by
  change Fin (N.S.card + N.S.copyCount (I.mixedFaces g)) at z
  induction z using Fin.addCases with
  | right i =>
    exfalso
    have hU := (I.mem_mixedFaces g).mp
      (show hN.rep.toCellScheme.scope (Fin.natAdd _ i) ∈ I.mixedFaces g by
        rw [Scheme.scope_mirror_natAdd]; exact ((N.S.copyEquiv _).symm i).2.1)
    exact hU.2.1 hz
  | left u => exact ⟨u, rfl⟩

end ALvl.Good

/-! ### Reading a level through the completion -/

variable {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

section Shape

variable {j : ℕ} {N : I.ALvl g H j} {t : StageType.{u} α (m + 2)}
  (ht : t.IsLegalBelowFullGrade) (hn : 0 < m + 2) {κ : Fin N.S.card → Fin t.card}

/-- **Through the completion, a cell of the level reads the cells of the level as the level
does** (the shape of the level: `κ` keeps rows). -/
theorem rowAt_addApex_of_levelShape
    (hrow : ∀ u x, t.toScheme.rowAt (κ u) (κ x) = N.S.rowAt u x) (u x : Fin N.S.card) :
    (t.addApex ht hn).toScheme.rowAt (κ u).castSucc (κ x).castSucc = N.S.rowAt u x :=
  (StageType.rowAt_addApex_castSucc ht hn _ _).trans (hrow u x)

/-- **Every cell of the completion of full scope below the full grade is a cell of the level**,
with its graded index (the shape of a level: `κ` keeps graded indices and reaches every cell of
full scope). -/
theorem exists_level_of_gradedIndex_addApex
    (hgi : ∀ u, t.toCellScheme.gradedIndex (κ u) = N.S.toCellScheme.gradedIndex u)
    (hfull : ∀ z, t.toCellScheme.scope z = univ → z ∈ Set.range κ) {i : ℕ} (hi : i < m + 2)
    (z : Fin (t.addApex ht hn).card)
    (hz : (t.addApex ht hn).toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), i)) :
    ∃ u' : Fin N.S.card, z = (κ u').castSucc ∧
      N.S.toCellScheme.gradedIndex u' = ((univ : Finset (Fin (m + 2))), i) := by
  obtain ⟨z', rfl, hz'⟩ := StageType.exists_castSucc_of_gradedIndex_addApex ht hn hi z hz
  obtain ⟨u', rfl⟩ := hfull z' (congrArg Prod.fst hz')
  exact ⟨u', rfl, (hgi u').symm.trans hz'⟩

/-- **The labels of the attachment survive the completion**: for a stage type labelled by the
reduction to the stage of a labelling `q` extending the labels of the attachment through the
shape map, the completion carries at the cell of a cell `c` of the attachment its actual label,
`⊤` included. -/
theorem label_addApex_attEmb_of_levelShape {q : Fin t.card → Label.{u}}
    (hlab : ∀ z, t.label z = Label.reduce α (q z))
    (hqe : ∀ c, q (κ (N.attEmb c)) = (I.attachmentType g).label c)
    (c : Fin (I.attachment g).card) :
    (t.addApex ht hn).label (κ (N.attEmb c)).castSucc = (I.attachmentType g).label c :=
  StageType.label_addApex_castSucc_of_reduce ht hn ((hlab _).trans (by rw [hqe]))
    ((I.attachmentType g).atStage c)

/-- **At a cell of the context**, the completion carries the label of the context. -/
theorem label_addApex_attachCtxCell_of_levelShape {q : Fin t.card → Label.{u}}
    (hlab : ∀ z, t.label z = Label.reduce α (q z))
    (hqe : ∀ c, q (κ (N.attEmb c)) = (I.attachmentType g).label c) (x : Fin I.left.card) :
    (t.addApex ht hn).label (κ (N.attEmb (I.attachCtxCell g x))).castSucc = I.left.label x := by
  rw [label_addApex_attEmb_of_levelShape ht hn hlab hqe, attachCtxCell_eq,
    StageType.label_faceCell]

end Shape

/-- **The controller clauses survive every completion by the apex** of a stage type carrying the
level at the grade `j + 1` (any `j`): every cell of the completion at `(univ, threshold)`, for
requests calibrated on the class with threshold `≥ 2`, is the cell of a cell `u'` of the level,
and for some member `a` and table `F` it stores on the context and donor cells (the cells of the
attachment) an admitted state, reads the top rung at least as high as the cap, the rungs as `F`,
and every positive stored value below the cap as a rung.  The apex is not among these cells
(`StageType.gradedIndex_addApex_last_ne_threshold`); the bottom state stores `⊥`. -/
theorem addApex_ladderController_of_levelShape (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {p₀ : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold) {j : ℕ}
    {t : StageType.{u} α (m + 2)} (ht : t.IsLegalBelowFullGrade) (hn : 0 < m + 2)
    {κ : Fin (I.lvLevel g H B hd Q j).S.card → Fin t.card}
    (hrow : ∀ u x, t.toScheme.rowAt (κ u) (κ x) = (I.lvLevel g H B hd Q j).S.rowAt u x)
    (hgi : ∀ u, t.toCellScheme.gradedIndex (κ u) =
      (I.lvLevel g H B hd Q j).S.toCellScheme.gradedIndex u)
    (hfull : ∀ z, t.toCellScheme.scope z = univ → z ∈ Set.range κ)
    (u : Fin (t.addApex ht hn).card)
    (hu : (t.addApex ht hn).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), Q.threshold)) :
    ∃ u' : Fin (I.lvLevel g H B hd Q j).S.card, u = (κ u').castSucc ∧
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}),
        Q.AdmitsOnClass
          (fun x ↦ (t.addApex ht hn).toScheme.rowAt u
            (κ ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))).castSucc)
          (fun y ↦ (t.addApex ht hn).toScheme.rowAt u
            (κ ((I.lvLevel g H B hd Q j).attEmb (I.attachDonCell g hd y))).castSucc) ∧
        (t.addApex ht hn).toScheme.rowAt u
            (κ ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g Q.cap))).castSucc ≤
          (t.addApex ht hn).toScheme.rowAt u
            (κ ((I.lvLevel g H B hd Q j).embed (lvRung hH a (H - 1)))).castSucc ∧
        (∀ i < H, (t.addApex ht hn).toScheme.rowAt u
            (κ ((I.lvLevel g H B hd Q j).embed (lvRung hH a i))).castSucc = F (i + 1)) ∧
        ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
          (t.addApex ht hn).toScheme.rowAt u
              (κ ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))).castSucc ≠ ⊥ →
            ∃ i < H, (t.addApex ht hn).toScheme.rowAt u
              (κ ((I.lvLevel g H B hd Q j).attEmb (I.attachCtxCell g x))).castSucc =
                F (i + 1) := by
  have hNm : Q.threshold < m + 2 := by have := Q.threshold_le; omega
  obtain ⟨u', rfl, hu'⟩ := exists_level_of_gradedIndex_addApex ht hn hgi hfull hNm u hu
  obtain ⟨a, F, hadm, htop, hrung, hval⟩ := lvLevel_ladderController hH hcard hQ hB hN2 u' hu'
  refine ⟨u', rfl, a, F, ?_, ?_, fun i hi ↦ ?_, fun x hx hx0 ↦ ?_⟩
  · simp only [rowAt_addApex_of_levelShape ht hn hrow]
    exact hadm
  · rw [rowAt_addApex_of_levelShape ht hn hrow, rowAt_addApex_of_levelShape ht hn hrow]
    exact htop
  · rw [rowAt_addApex_of_levelShape ht hn hrow]
    exact hrung i hi
  · rw [rowAt_addApex_of_levelShape ht hn hrow] at hx0 ⊢
    exact hval x hx hx0

/-! ### The completion of the replicated top level is an instance -/

section Instance

variable (hα : Order.IsSuccPrelimit α)

/-- **The controller clauses on the completion of the replicated top level**, as an instance of
`Seed.addApex_ladderController_of_levelShape` (the shape map `Fin.castAdd`). -/
theorem lvRepCompletion_ladderController_of_levelShape (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {p₀ : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (u : Fin (lvRepCompletion hα hNm hL hq).card)
    (hu : (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), Q.threshold)) :
    ∃ u' : Fin (I.lvLevel g H B hd Q m).S.card, u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc ∧
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}),
        Q.AdmitsOnClass
          (fun x ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
              Fin hNm.rep.card).castSucc)
          (fun y ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachDonCell g hd y)) :
              Fin hNm.rep.card).castSucc) ∧
        (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g Q.cap)) :
              Fin hNm.rep.card).castSucc ≤
          (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.lvLevel g H B hd Q m).embed (lvRung hH a (H - 1))) :
              Fin hNm.rep.card).castSucc ∧
        (∀ i < H, (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.lvLevel g H B hd Q m).embed (lvRung hH a i)) :
              Fin hNm.rep.card).castSucc = F (i + 1)) ∧
        ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
          (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
              (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
                Fin hNm.rep.card).castSucc ≠ ⊥ →
            ∃ i < H, (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
              (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
                Fin hNm.rep.card).castSucc = F (i + 1) :=
  addApex_ladderController_of_levelShape (t := lvRepType hα hNm hL hq) hH hcard hQ hB hN2 hL
    (Nat.succ_pos _) (κ := Fin.castAdd _) (hNm.rep_rowAt_castAdd) (hNm.rep_gradedIndex_castAdd)
    (hNm.rep_mem_range_castAdd_of_scope_univ) u hu

/-- **The completion of the replicated top level carries the label of the context** at the cell of
a context cell, for a lawful labelling extending the labels of the attachment. -/
theorem lvRepCompletion_label_attachCtxCell (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q))
    (hL : hNm.rep.IsLegalBelowFullGrade) {q : Fin hNm.rep.card → Label.{u}}
    (hq : hNm.rep.rows.IsLawful q)
    (hqe : ∀ c, q (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb c)) =
      (I.attachmentType g).label c) (x : Fin I.left.card) :
    (lvRepCompletion hα hNm hL hq).label
        (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
          Fin hNm.rep.card).castSucc = I.left.label x :=
  label_addApex_attachCtxCell_of_levelShape (t := lvRepType hα hNm hL hq) hL (Nat.succ_pos _)
    (κ := Fin.castAdd _) (q := q) (fun _ ↦ rfl) hqe x

/-- **The completion of the replicated top level, read with the extending labelling**
(`Seed.hasExtendingLabelLevel_rep`): for every legality below the full grade of the replicated top
level, some lawful labelling gives a completion in which the apex is not at the threshold, every
cell at the threshold is old and stores an admitted state, and the cell of every context cell
carries the label of the context. -/
theorem exists_lvRepCompletion_reading (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin (m + 2))), Q.threshold) ∧
        (∀ u, (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin (m + 2))), Q.threshold) →
          ∃ u' : Fin (I.lvLevel g H B hd Q m).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc ∧
            Q.AdmitsOnClass
              (fun x ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
                  Fin hNm.rep.card).castSucc)
              (fun y ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachDonCell g hd y)) :
                  Fin hNm.rep.card).castSucc)) ∧
        ∀ x, (lvRepCompletion hα hNm hL hq).label
          (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
            Fin hNm.rep.card).castSucc = I.left.label x := by
  obtain ⟨q, hq, hqe⟩ := hasExtendingLabelLevel_rep (hd := hd) hH hcard hQ hpair hB m (by omega)
  refine ⟨q, hq, StageType.gradedIndex_addApex_last_ne_threshold Q hL _, fun u hu ↦ ?_,
    lvRepCompletion_label_attachCtxCell hα hNm hL hq hqe⟩
  obtain ⟨u', hu', a, F, hadm, -⟩ :=
    lvRepCompletion_ladderController_of_levelShape hα hH hcard hQ hB hN2 hNm hL hq u hu
  exact ⟨u', hu', hadm⟩

/-- `Seed.exists_lvRepCompletion_reading` for the first coatom type given up to equality. -/
theorem exists_lvRepCompletion_reading_of_eq {t' : StageType.{u} α (m + 1)} (hI : I.left = t')
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p₀}
    {d : StageType.{u} α (n + 1)}
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ y, Q.CorrectAt t'.label y (d.label y))
    (hQ : Q.ClassCalibrated hte) (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.lvLevel g H B hdA (hI ▸ Q) m).Good B (lvAdm hdA (hI ▸ Q)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin (m + 2))), Q.threshold) ∧
        (∀ u, (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin (m + 2))), Q.threshold) →
          ∃ u' : Fin (I.lvLevel g H B hdA (hI ▸ Q) m).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc ∧
            (hI ▸ Q).AdmitsOnClass
              (fun x ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _ ((I.lvLevel g H B hdA (hI ▸ Q) m).attEmb (I.attachCtxCell g x)) :
                  Fin hNm.rep.card).castSucc)
              (fun y ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _
                  ((I.lvLevel g H B hdA (hI ▸ Q) m).attEmb (I.attachDonCell g hdA y)) :
                  Fin hNm.rep.card).castSucc)) ∧
        ∀ x, (lvRepCompletion hα hNm hL hq).label
          (Fin.castAdd _ ((I.lvLevel g H B hdA (hI ▸ Q) m).attEmb (I.attachCtxCell g x)) :
            Fin hNm.rep.card).castSucc = I.left.label x := by
  subst hI
  exact exists_lvRepCompletion_reading hα hH hcard hQ hpair hB hN2 hNm hL

end Instance

end Seed


/-! ### The test inputs -/

open Seed AvailableTopDeterminationCounterexample
open scoped Ordinal

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- **The completion at the tie input** (requests `req ω`, threshold `2`): for every legality
below the full grade of the replicated top level, with the extending labelling, the apex is not at
`(univ, 2)`, every cell at `(univ, 2)` is a cell of the level storing an admitted state, and the
cell of a context cell labelled `⊤` carries `⊤`. -/
theorem lvRepCompletion_reading_tie (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B)
    (hNm : (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) 1).Good B (lvAdm hdA (hI ▸ req ω)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion Ordinal.isSuccLimit_omega0.isSuccPrelimit hNm hL hq).toCellScheme.gradedIndex
          (Fin.last _) ≠ ((univ : Finset (Fin 3)), 2) ∧
        (∀ u, (lvRepCompletion Ordinal.isSuccLimit_omega0.isSuccPrelimit hNm hL
          hq).toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2) →
          ∃ u' : Fin (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) 1).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc) ∧
        ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
          (lvRepCompletion Ordinal.isSuccLimit_omega0.isSuccPrelimit hNm hL hq).label
            (Fin.castAdd _ ((I.lvLevel 𝕣 H B hdA (hI ▸ req ω) 1).attEmb (I.attachCtxCell 𝕣 x)) :
              Fin hNm.rep.card).castSucc = ⊤ := by
  obtain ⟨q, hq, hapex, hold, hlab⟩ := Seed.exists_lvRepCompletion_reading_of_eq
    Ordinal.isSuccLimit_omega0.isSuccPrelimit hI (hte := restrictFace_ctx_root ω) hdA
    (correctAt_req ω) (classCalibrated_req ω) hH hcard hB
    (by have := threshold_req.{u} ω; omega) hNm hL
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨cellR.{u} ω, label_cellR ω⟩
  have e := congrArg (Prod.mk (univ : Finset (Fin 3))) (threshold_req.{u} ω).symm
  refine ⟨q, hq, fun h ↦ hapex (h.trans e), fun u hu ↦ ?_, x, hx, (hlab x).trans hx⟩
  obtain ⟨u', hu', -⟩ := hold u (hu.trans e)
  exact ⟨u', hu'⟩

end TieInstance

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- **The completion at the apex input** (requests `reqTop α`, threshold `3`, the top grade of the
context): at a stage that is zero or a limit, for every legality below the full grade of the
replicated top level, with the extending labelling, the apex of the completion (grade `4`) is not at
`(univ, 3)`, every cell at `(univ, 3)` is a cell of the level, and the cell of the context apex
(labelled `⊤`) carries `⊤`. -/
theorem lvRepCompletion_reading_apex {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α)
    (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B)
    (hNm : (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) 2).Good B (lvAdm hdA (hI ▸ reqTop α)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin 4)), 3) ∧
        (∀ u, (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin 4)), 3) →
          ∃ u' : Fin (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) 2).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc) ∧
        ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
          (lvRepCompletion hα hNm hL hq).label
            (Fin.castAdd _
              ((I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) 2).attEmb (I.attachCtxCell 𝕘 x)) :
              Fin hNm.rep.card).castSucc = ⊤ := by
  obtain ⟨q, hq, hapex, hold, hlab⟩ := Seed.exists_lvRepCompletion_reading_of_eq hα hI
    (hte := restrictFace_root) hdA (correctAt_reqTop α) (classCalibrated_reqTop α) hH hcard hB
    (by have := threshold_reqTop.{u} α; omega) hNm hL
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨apex α, label_apex α⟩
  have e := congrArg (Prod.mk (univ : Finset (Fin 4))) (threshold_reqTop.{u} α).symm
  refine ⟨q, hq, fun h ↦ hapex (h.trans e), fun u hu ↦ ?_, x, hx, (hlab x).trans hx⟩
  obtain ⟨u', hu', -⟩ := hold u (hu.trans e)
  exact ⟨u', hu'⟩

end ApexInstance

namespace QuadInstance

/-- The root of the input. -/
local notation "𝕘" => root

/-- **The completion at the input on four points** (requests `req hα`, threshold `4`, the top
grade of the context): for every legality below the full grade of the replicated top level, with
the extending labelling, the apex of the completion (grade `5`) is not at `(univ, 4)`, every cell
at `(univ, 4)` is a cell of the level, and the cell of the context apex (labelled `⊤`) carries
`⊤`. -/
theorem lvRepCompletion_reading_quad {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B)
    (hNm : (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 3).Good B (lvAdm hdA (hI ▸ req hα)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα.isSuccPrelimit hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin 5)), 4) ∧
        (∀ u, (lvRepCompletion hα.isSuccPrelimit hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin 5)), 4) →
          ∃ u' : Fin (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 3).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc) ∧
        ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
          (lvRepCompletion hα.isSuccPrelimit hNm hL hq).label
            (Fin.castAdd _
              ((I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 3).attEmb (I.attachCtxCell 𝕘 x)) :
              Fin hNm.rep.card).castSucc = ⊤ := by
  obtain ⟨q, hq, hapex, hold, hlab⟩ := Seed.exists_lvRepCompletion_reading_of_eq
    hα.isSuccPrelimit hI (hte := restrictFace_root_quad hα) hdA (correctAt_req hα)
    (classCalibrated_req hα) hH hcard hB (by have := threshold_req hα; omega) hNm hL
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ :=
    hI ▸ ⟨apex hα, label_apex hα⟩
  have e := congrArg (Prod.mk (univ : Finset (Fin 5))) (threshold_req hα).symm
  refine ⟨q, hq, fun h ↦ hapex (h.trans e), fun u hu ↦ ?_, x, hx, (hlab x).trans hx⟩
  obtain ⟨u', hu', -⟩ := hold u (hu.trans e)
  exact ⟨u', hu'⟩

end QuadInstance

end VaughtConjecture

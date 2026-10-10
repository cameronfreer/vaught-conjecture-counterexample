/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelBountifulTop
import VaughtConjecture.MainTheorem.ReplicatedLevelControl

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

The completion of the replicated top level used by the carrier (`Seed.lvRepCompletion`, in
`VaughtConjecture.MainTheorem.LevelCarrier`) is an instance
(`Seed.lvRepCompletion_ladderController`), and so are the three test inputs of
`VaughtConjecture.MainTheorem.LevelCompletionInstances`.

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
  -- a cell of the completion is an old cell or the apex
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
  -- a cell of the replicated level is a cell of the level or a copy
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

end Seed

end VaughtConjecture

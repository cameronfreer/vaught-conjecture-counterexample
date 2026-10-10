/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelBountifulTop
import VaughtConjecture.MainTheorem.LevelExtendingLabel
import VaughtConjecture.MainTheorem.ReplicatedLevelControl
import VaughtConjecture.MainTheorem.ReplicatedCompletion

/-!
# The completion of a replicated level, and its controllers

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels re-rendered per grade).

**The completion.**  A good level `N` at the grade `m + 1` with its copies at the mixed faces
(`Seed.ALvl.Good.rep`) that is legal below the full grade (`Scheme.IsLegalBelowFullGrade`), with a
lawful labelling `q` extending the labels of the attachment (`Seed.ALvl.Good.HasExtendingLabelRep`,
`Seed.hasExtendingLabelLevel_rep`), is completed as the replicated scheme over the height-set tower
is (`Seed.replicatedCompletion`): the labelling reduced to the stage, and the apex added
(`Seed.lvRepType`, `Seed.lvRepCompletion`, `StageType.addApex`).

* `Seed.isLegal_lvRepCompletion`: it is legal.
* `Seed.restrictFace_left_lvRepCompletion`, `Seed.restrictFace_donor_lvRepCompletion`: its context
  face is the first coatom type `I.left` and its donor face the donor `d`, literally, labels
  included (along a proper face whose visible cells are cells of the attachment, the completion is
  the attachment, `Seed.restrictFace_lvRepCompletion`).
* `Seed.cellMap_lvRepCompletion`: along such a face, its cells are those of the attachment.
* `Seed.lvRepCompletion_label_attEmb`: at the cells of the attachment it keeps their actual labels.

**Recognition through the completion.**  The completion reads the cells of the level as the level
does (`Seed.lvRepCompletion_rowAt_level`).  So the rung readings of the field ladder
(`Seed.lvRepCompletion_rung_rows`) and the four controller clauses of the cells of full scope at
the threshold (`Seed.lvLevel_ladderController`: an admitted state on the context and donor cells,
the top rung at least the cap, the rungs read as a table `F`, every positive stored value below
the cap a rung) hold in the completion (`Seed.lvRepCompletion_ladderController`); the apex has
grade `m + 2` and is never at the threshold.

**The carrier** (`Seed.exists_lvRepCarrier`).  Premises, exactly: a stage `α` that is zero or a
limit (`hα`); `0 < H` and `#(I.attachmentBase g) ≤ H` (only the attachment is bounded, never the
amalgam); requests `Q` calibrated on the class (`hQ`) with `2 ≤ Q.threshold`; `2 · #cells ≤ B`;
the level at the grade `m + 1` good (`hNm`) and its replicated scheme legal below the full grade
(`hL`); a lawful labelling `q` extending the labels of the attachment (`hq`, `hqe`).  Conclusion:
the completion is a growth carrier with `I.left` and `d` as literal faces, a cell of full scope at
the threshold, a field ladder of height `H`, and every cell of full scope at the threshold a ladder
controller.

**The bottom state.**  The cell of the bottom state stores `⊥` on the context and donor cells; its
clauses hold trivially (the levels above the first read its ladder base as gap values,
`Seed.lvLevel_σ_embed_bot`, which no clause reads).

**Scope.**  The statements concern the replicated level at the top grade `m + 1`, not the levels at
lower grades.  At the seed position the parameters are the seed-fixed choice
`Seed.seedHeightLevel`, `Seed.seedBlockBound'`
(`VaughtConjecture.MainTheorem.LevelCarrierContract`).

Not yet reviewed.

## References

The completion of [Kni26, Definition 4.3.14]; the amalgam is [Kni26, Definition 4.3.1].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **Every level has the ground set of the amalgam.** -/
theorem ground_lvLevel : ∀ j,
    (I.lvLevel g H B hd Q j).S.toCellScheme.ground = I.amalgam.toCellScheme.ground
  | 0 => rfl
  | j + 1 => ground_lvLevel j

/-- **The cells of the ladder base sit increasingly in every level.** -/
theorem lvLevel_embed_strictMono : ∀ j, StrictMono (I.lvLevel g H B hd Q j).embed
  | 0 => strictMono_id
  | j + 1 => (Fin.castAddOrderEmb _).strictMono.comp (lvLevel_embed_strictMono j)

namespace ALvl.Good

variable {j : ℕ} {N : I.ALvl g H j} (hN : N.Good B (lvAdm hd Q))

include hN in
/-- The cells of the attachment sit increasingly in the replicated level. -/
theorem strictMono_repEmb (hemb : StrictMono N.embed) : StrictMono hN.repEmb :=
  (Fin.castAddOrderEmb _).strictMono.comp (hemb.comp (Fin.castAddOrderEmb _).strictMono)

end ALvl.Good

variable (hα : Order.IsSuccPrelimit α) {N : I.ALvl g H (m + 1)} {hN : N.Good B (lvAdm hd Q)}

variable (hN) in
/-- The replicated level with a lawful labelling, reduced to the stage, as a stage type. -/
noncomputable def lvRepType (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) : StageType.{u} α (m + 2) where
  toScheme := hN.rep
  label z := Label.reduce α (q z)
  isWellFormed := hL.isWellFormed
  isCoded := hL.isCoded
  isLawful := hq.reduce hα
  atStage _ := atStage_reduce α _

variable (hN) in
/-- **The completion of the replicated level**: the replicated level with a lawful labelling
reduced to the stage, and the apex added. -/
noncomputable def lvRepCompletion (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) : StageType.{u} α (m + 2) :=
  (lvRepType hα hN hL hq).addApex hL (Nat.succ_pos _)

/-- **The completion of the replicated level is legal.** -/
theorem isLegal_lvRepCompletion (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) :
    (lvRepCompletion hα hN hL hq).IsLegal :=
  StageType.isLegal_addApex _ _

/-- The faces of the completion along a proper face whose visible cells are cells of the
attachment are those of the attachment, labels included. -/
theorem restrictFace_lvRepCompletion (hemb : StrictMono N.embed)
    (hground : N.S.toCellScheme.ground = I.amalgam.toCellScheme.ground)
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    (hvis : ∀ z : Fin hN.rep.card, (hN.rep.toCellScheme.scope z : Set (Fin (m + 2))) ⊆
      Set.range f → z ∈ Set.range hN.repEmb) :
    restrictFace f (lvRepCompletion hα hN hL hq) = restrictFace f (I.attachmentType g) :=
  (StageType.restrictFace_addApex _ _ _ hf).trans
    (StageType.restrictFace_eq_of_strictMono (t := lvRepType hα hN hL hq)
      (s := I.attachmentType g) f (hN.strictMono_repEmb hemb) hN.isLowerEmbedding_repEmb
      (fun c ↦ congrArg Prod.fst (hN.gradedIndex_repEmb c)) hN.comap_rows_repEmb hground hfaces
      (fun c ↦ by
        change Label.reduce α (q _) = _
        rw [hqe c]
        exact ((I.attachmentType g).atStage c).reduce_eq) hvis)

/-- **The context face of the completion is the first coatom type**, literally. -/
theorem restrictFace_left_lvRepCompletion (hemb : StrictMono N.embed)
    (hground : N.S.toCellScheme.ground = I.amalgam.toCellScheme.ground)
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) :
    restrictFace Fin.castSuccEmb (lvRepCompletion hα hN hL hq) = some I.left :=
  (restrictFace_lvRepCompletion hα hemb hground hfaces hL hq hqe _ Coatom.univ_map_left_ne
    fun z hz ↦ hN.mem_range_repEmb z (.inl fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
      exact mem_map_of_mem _ (mem_univ y))).trans (I.restrictFace_left_attachmentType g)

/-- **The donor face of the completion is the donor**, literally. -/
theorem restrictFace_donor_lvRepCompletion (hemb : StrictMono N.embed)
    (hground : N.S.toCellScheme.ground = I.amalgam.toCellScheme.ground)
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (lvRepCompletion hα hN hL hq) =
      some d :=
  (restrictFace_lvRepCompletion hα hemb hground hfaces hL hq hqe _ (map_extendByLast_ne_univ g)
    fun z hz ↦ hN.mem_range_repEmb z (.inr fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
      exact mem_map_of_mem _ (mem_univ y))).trans (I.restrictFace_donor_attachmentType g hd)


/-- **Along a proper face whose visible cells are cells of the attachment, the cells of the
completion are those of the attachment**, in their order. -/
theorem cellMap_lvRepCompletion (hemb : StrictMono N.embed) (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    (hvis : ∀ z : Fin hN.rep.card, (hN.rep.toCellScheme.scope z : Set (Fin (m + 2))) ⊆
      Set.range f → z ∈ Set.range hN.repEmb)
    {i : Fin ((I.attachment g).comap f).card}
    {j : Fin ((lvRepCompletion hα hN hL hq).toScheme.comap f).card} (hij : (i : ℕ) = j) :
    (lvRepCompletion hα hN hL hq).toScheme.cellMap f j =
      (hN.repEmb ((I.attachment g).cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range f (S := I.attachment g)
    (T := (lvRepCompletion hα hN hL hq).toScheme)
    (φ := fun c ↦ (hN.repEmb c).castSucc)
    (fun a b hab ↦ Fin.castSucc_lt_castSucc_iff.mpr (hN.strictMono_repEmb hemb hab)) (fun c ↦ ?_)
    (fun z hz ↦ ?_) hij
  · change (hN.rep.appendFullCellScheme (m + 2)).scope (hN.repEmb c).castSucc = _
    rw [Scheme.appendFullCellScheme_scope_castSucc]
    exact congrArg Prod.fst (hN.gradedIndex_repEmb c)
  · change Fin (hN.rep.card + 1) at z
    induction z using Fin.lastCases with
    | last =>
      exfalso
      change ((hN.rep.appendFullCellScheme (m + 2)).scope (Fin.last _) :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_last, coe_univ] at hz
      exact hf (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ := hz (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
    | cast z =>
      change ((hN.rep.appendFullCellScheme (m + 2)).scope z.castSucc :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_castSucc] at hz
      obtain ⟨c, rfl⟩ := hvis z hz
      exact ⟨c, rfl⟩

/-- The completion reads the cells of the replicated level as the replicated level does. -/
theorem rowAt_lvRepCompletion_castSucc (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) (z x : Fin hN.rep.card) :
    (lvRepCompletion hα hN hL hq).toScheme.rowAt z.castSucc x.castSucc = hN.rep.rowAt z x :=
  Scheme.rowAt_appendFullCell_castSucc (h := hL.not_le) z x

/-- The cells of the replicated level keep their graded indices in the completion. -/
theorem gradedIndex_lvRepCompletion_castSucc (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) (z : Fin hN.rep.card) :
    (lvRepCompletion hα hN hL hq).toCellScheme.gradedIndex z.castSucc =
      hN.rep.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ z

/-- The apex has the full grade. -/
theorem gradedIndex_lvRepCompletion_last (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) :
    (lvRepCompletion hα hN hL hq).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin (m + 2))), m + 2) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _


/-- **The completion keeps the actual labels of the attachment**: at the cell of a cell `c` of the
attachment, the completed stage type carries the label of `c` in the attachment, `⊤` included
(the labelling extends the labels, and the reduction to the stage fixes a label at the stage). -/
theorem lvRepCompletion_label_attEmb (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) (c : Fin (I.attachment g).card) :
    (lvRepCompletion hα hN hL hq).label (hN.repEmb c).castSucc = (I.attachmentType g).label c := by
  refine (StageType.apexLabel_castSucc (t := lvRepType hα hN hL hq) (hN.repEmb c)).trans ?_
  change Label.reduce α (q _) = _
  rw [hqe c]
  exact ((I.attachmentType g).atStage c).reduce_eq

/-- **The completion reads the cells of the level as the level does.** -/
theorem lvRepCompletion_rowAt_level (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) (z x : Fin N.S.card) :
    (lvRepCompletion hα hN hL hq).toScheme.rowAt (Fin.castAdd _ z : Fin hN.rep.card).castSucc
      (Fin.castAdd _ x : Fin hN.rep.card).castSucc = N.S.rowAt z x :=
  (rowAt_lvRepCompletion_castSucc hα hL hq _ _).trans (Scheme.rowAt_mirror_castAdd _ _)

/-- **The rung readings in the completion** of the replicated top level: the rungs of a member
read themselves at the diagonal code and the preceding rung at the code of the preceding rank. -/
theorem lvRepCompletion_rung_rows (hH : 0 < H)
    (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) (hi : i < H) :
    (lvRepCompletion hα hNm hL hq).toScheme.rowAt
        (Fin.castAdd _ ((I.lvLevel g H B hd Q m).embed (lvRung hH a i)) :
          Fin hNm.rep.card).castSucc
        (Fin.castAdd _ ((I.lvLevel g H B hd Q m).embed (lvRung hH a i)) :
          Fin hNm.rep.card).castSucc = Label.ladderSource (i + 1) (i + 1) ∧
      (0 < i → (lvRepCompletion hα hNm hL hq).toScheme.rowAt
        (Fin.castAdd _ ((I.lvLevel g H B hd Q m).embed (lvRung hH a i)) :
          Fin hNm.rep.card).castSucc
        (Fin.castAdd _ ((I.lvLevel g H B hd Q m).embed (lvRung hH a (i - 1))) :
          Fin hNm.rep.card).castSucc = Label.ladderSource (i + 1) i) := by
  have hceil (i' : ℕ) (hi' : i' < H) : ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H)
      Prod.fst (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a
      ((a, Sum.inl ⟨min i' (H - 1), by omega⟩) : Scheme.LadderPt (I.attachmentBase g).S
        (Scheme.RankMember (I.attachmentBase g).S H) H) = i' + 1 := by
    have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
      (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
      ((a, Sum.inl ⟨min i' (H - 1), by omega⟩) : Scheme.LadderPt (I.attachmentBase g).S
        (Scheme.RankMember (I.attachmentBase g).S H) H)
    exact h.trans (by simp only [Scheme.ladderCeil, Sum.elim_inl]; omega)
  refine ⟨?_, fun hi0 ↦ ?_⟩
  · rw [lvRepCompletion_rowAt_level]
    change (I.lvLevel g H B hd Q m).S.rowAt (I.lvLad g H B hd Q m _) (I.lvLad g H B hd Q m _) = _
    rw [lvLevel_rowAt_lad_lad, hceil i hi]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    congr 1
    omega
  · rw [lvRepCompletion_rowAt_level]
    change (I.lvLevel g H B hd Q m).S.rowAt (I.lvLad g H B hd Q m _) (I.lvLad g H B hd Q m _) = _
    rw [lvLevel_rowAt_lad_lad, hceil (i - 1) (by omega)]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    congr 1 <;> omega

/-- **The controller clauses in the completion** of the replicated top level: a cell of full scope
at the threshold `≥ 2` is the cell of a cell `u'` of the level, and for some member `a` and table
`F` it stores on the context and donor cells (the cells of the attachment) an admitted state, reads
the top rung at least as high as the cap, the rungs as `F`, and every positive stored value below
the cap as a rung (the four clauses of `Seed.lvLevel_ladderController`, read through the
completion).  The bottom state is covered: it stores `⊥`. -/
theorem lvRepCompletion_ladderController (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
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
                Fin hNm.rep.card).castSucc = F (i + 1) := by
  classical
  have hNm1 : Q.threshold ≤ m + 1 := by
    have h1 := I.left.isWellFormed.isWellFormed.grade_le_card Q.cap
    have h2 : #(I.left.toCellScheme.scope Q.cap) ≤ m + 1 :=
      (card_le_univ _).trans (by simp)
    exact h1.trans h2
  obtain ⟨z, rfl⟩ : ∃ z : Fin hNm.rep.card, u = Fin.castSucc z := by
    revert hu
    refine Fin.lastCases (n := hNm.rep.card) (motive := fun u ↦
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 2))), Q.threshold) →
        ∃ z : Fin hNm.rep.card, u = Fin.castSucc z) ?_ (fun z _ ↦ ⟨z, rfl⟩) u
    intro hu
    exfalso
    have h1 := congrArg Prod.snd (hu.symm.trans (gradedIndex_lvRepCompletion_last hα hL hq))
    simp only at h1
    omega
  have hz : hNm.rep.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), Q.threshold) :=
    (gradedIndex_lvRepCompletion_castSucc hα hL hq z).symm.trans hu
  obtain ⟨u', rfl, hu'g⟩ := hNm.exists_castAdd_of_scope_univ z (congrArg Prod.fst hz)
  obtain ⟨a, F, hadm, htop, hrung, hval⟩ :=
    lvLevel_ladderController hH hcard hQ hB hN2 u' (hu'g.symm.trans hz)
  refine ⟨u', rfl, a, F, ?_, ?_, fun i hi ↦ ?_, fun x hx hx0 ↦ ?_⟩
  · simp only [lvRepCompletion_rowAt_level]
    exact hadm
  · rw [lvRepCompletion_rowAt_level, lvRepCompletion_rowAt_level]
    exact htop
  · rw [lvRepCompletion_rowAt_level]
    exact hrung i hi
  · rw [lvRepCompletion_rowAt_level] at hx0 ⊢
    exact hval x hx hx0

include hα in
/-- **The ladder growth carrier of the replicated top level**: at a stage that is zero or a limit,
for requests calibrated on the class with threshold at least `2`, a height `H > 0` bounding the
cells of the attachment and `2 · #cells ≤ B`, if the replicated level at the grade `m + 1` is legal
below the full grade and carries a lawful labelling `q` extending the labels of the attachment,
its completion is a growth carrier with the context `I.left` and the donor `d` as literal faces, a
cell of full scope at the threshold, a field ladder of height `H`, and every cell of full scope at
the threshold a ladder controller (`Seed.lvLevel_ladderController`, the bottom state included: it
stores `⊥`). -/
theorem exists_lvRepCarrier (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hNm.repEmb c) = (I.attachmentType g).label c) :
    ∃ G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb),
      (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
      ∃ (Mb : Type) (H' : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H' ∧
        (∀ a, ∀ i < H', G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
        (∀ a, ∀ i < H', G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
        (∀ a, ∀ i < H', 0 < i →
          G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
        ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
          ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H') r u a F := by
  classical
  have hemb := lvLevel_embed_strictMono (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hground := ground_lvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hfaces := faces_lvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hleftF : restrictFace Fin.castSuccEmb (lvRepCompletion hα hNm hL hq) = some I.left :=
    restrictFace_left_lvRepCompletion hα hemb hground hfaces hL hq hqe
  have hdonF : restrictFace (extendByLast (g.trans Fin.castSuccEmb))
      (lvRepCompletion hα hNm hL hq) = some d :=
    restrictFace_donor_lvRepCompletion hα hemb hground hfaces hL hq hqe
  let G := GrowthCarrier.ofExtension (isLegal_lvRepCompletion hα hL hq) hleftF hdonF
  set N := Q.threshold with hNdef
  have hNm1 : N ≤ m + 1 := by
    have h1 := I.left.isWellFormed.isWellFormed.grade_le_card Q.cap
    have h2 : #(I.left.toCellScheme.scope Q.cap) ≤ m + 1 :=
      (card_le_univ _).trans (by simp)
    exact h1.trans h2
  -- the cells of the level in the completion
  let emb : Fin (I.lvLevel g H B hd Q m).S.card → Fin G.scheme.card :=
    fun z ↦ (Fin.castAdd _ z : Fin hNm.rep.card).castSucc
  have hgi (z : Fin (I.lvLevel g H B hd Q m).S.card) : G.scheme.toCellScheme.gradedIndex (emb z) =
      (I.lvLevel g H B hd Q m).S.toCellScheme.gradedIndex z :=
    (gradedIndex_lvRepCompletion_castSucc hα hL hq _).trans
      (Scheme.gradedIndex_mirror_castAdd (hmix := hNm.not_subset_scope) z)
  have hrow (z x : Fin (I.lvLevel g H B hd Q m).S.card) :
      G.scheme.rowAt (emb z) (emb x) = (I.lvLevel g H B hd Q m).S.rowAt z x :=
    (rowAt_lvRepCompletion_castSucc hα hL hq _ _).trans (Scheme.rowAt_mirror_castAdd _ _)
  -- the context and donor cells are cells of the attachment
  have hctx (x : Fin I.left.card) :
      G.contextCell x = emb ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :=
    cellMap_lvRepCompletion hα hemb hL hq Fin.castSuccEmb Coatom.univ_map_left_ne
      (fun z hz ↦ hNm.mem_range_repEmb z (.inl fun y hy ↦ by
        obtain ⟨w, rfl⟩ := hz (mem_coe.mpr hy)
        exact mem_map_of_mem _ (mem_univ w)))
      (i := Fin.cast (congrArg Scheme.card (I.comap_left_attachment_scheme g)).symm x)
      (j := Fin.cast (congrArg Scheme.card G.comap_context).symm x) rfl
  have hdon (j : Fin d.card) :
      G.donorCell j = emb ((I.lvLevel g H B hd Q m).attEmb (I.attachDonCell g hd j)) :=
    cellMap_lvRepCompletion hα hemb hL hq _ (map_extendByLast_ne_univ g)
      (fun z hz ↦ hNm.mem_range_repEmb z (.inr fun y hy ↦ by
        obtain ⟨w, rfl⟩ := hz (mem_coe.mpr hy)
        exact mem_map_of_mem _ (mem_univ w)))
      (i := Fin.cast (congrArg Scheme.card (I.comap_donor_attachment_scheme g hd)).symm j)
      (j := Fin.cast (congrArg Scheme.card G.comap_donor).symm j) rfl
  -- the ladder
  let r : Scheme.RankMember (I.attachmentBase g).S H → ℕ → Fin G.scheme.card :=
    fun a i ↦ emb ((I.lvLevel g H B hd Q m).embed (lvRung hH a i))
  have hlad (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) :
      (I.lvLevel g H B hd Q m).embed (lvRung hH a i) =
        I.lvLad g H B hd Q m (a, Sum.inl ⟨min i (H - 1), by omega⟩) := rfl
  have hceil (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) (hi : i < H) :
      ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
        (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a
        ((a, Sum.inl ⟨min i (H - 1), by omega⟩) : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H) = i + 1 := by
    have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
      (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
      ((a, Sum.inl ⟨min i (H - 1), by omega⟩) : Scheme.LadderPt (I.attachmentBase g).S
        (Scheme.RankMember (I.attachmentBase g).S H) H)
    exact h.trans (by simp only [Scheme.ladderCeil, Sum.elim_inl]; omega)
  -- a cell of full scope at the threshold
  obtain ⟨w, hw⟩ := lvLevel_hexist (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m N
    hN2 hNm1
  refine ⟨G, ⟨emb w, (hgi w).trans hw⟩, Scheme.RankMember (I.attachmentBase g).S H, H, r, hH,
    fun a i hi ↦ ?_, fun a i hi ↦ ?_, fun a i hi hi0 ↦ ?_, fun u hu ↦ ?_⟩
  · exact (hgi _).trans (lvLevel_gradedIndex_lad m _)
  · refine (hrow _ _).trans ?_
    rw [hlad, lvLevel_rowAt_lad_lad, hceil a i hi]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    congr 1
    omega
  · refine (hrow _ _).trans ?_
    rw [hlad, hlad, lvLevel_rowAt_lad_lad, hceil a (i - 1) (by omega)]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    congr 1 <;> omega
  · -- the controllers: the cells of full scope below the apex are cells of the level
    obtain ⟨z, rfl⟩ : ∃ z : Fin hNm.rep.card, u = Fin.castSucc z := by
      revert hu
      refine Fin.lastCases (n := hNm.rep.card) (motive := fun u ↦
        G.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), N) →
          ∃ z : Fin hNm.rep.card, u = Fin.castSucc z) ?_ (fun z _ ↦ ⟨z, rfl⟩) u
      intro hu
      exfalso
      have h1 := congrArg Prod.snd (hu.symm.trans (gradedIndex_lvRepCompletion_last hα hL hq))
      simp only at h1
      omega
    have hz : hNm.rep.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), N) :=
      (gradedIndex_lvRepCompletion_castSucc hα hL hq z).symm.trans hu
    obtain ⟨u', rfl, hu'g⟩ := hNm.exists_castAdd_of_scope_univ z (congrArg Prod.fst hz)
    have hu' : (I.lvLevel g H B hd Q m).S.toCellScheme.gradedIndex u' =
        ((univ : Finset (Fin (m + 2))), N) :=
      hu'g.symm.trans hz
    obtain ⟨a, F, hadm, htop, hrung, hval⟩ :=
      lvLevel_ladderController hH hcard hQ hB hN2 u' hu'
    have e1 : (fun x ↦ G.scheme.rowAt (emb u') (G.contextCell x)) =
        fun x ↦ (I.lvLevel g H B hd Q m).S.rowAt u'
          ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :=
      funext fun x ↦ by rw [hctx]; exact hrow _ _
    have e2 : (fun j ↦ G.scheme.rowAt (emb u') (G.donorCell j)) =
        fun j ↦ (I.lvLevel g H B hd Q m).S.rowAt u'
          ((I.lvLevel g H B hd Q m).attEmb (I.attachDonCell g hd j)) :=
      funext fun j ↦ by rw [hdon]; exact hrow _ _
    refine ⟨a, F, ?_, ?_, fun i hi ↦ ?_, fun x hx hx0 ↦ ?_⟩
    · change Q.AdmitsOnClass (fun x ↦ G.scheme.rowAt (emb u') (G.contextCell x))
        (fun j ↦ G.scheme.rowAt (emb u') (G.donorCell j))
      rw [e1, e2]
      exact hadm
    · change G.scheme.rowAt (emb u') (G.contextCell Q.cap) ≤ G.scheme.rowAt (emb u') (r a (H - 1))
      rw [hctx, hrow, hrow]
      exact htop
    · change G.scheme.rowAt (emb u') (r a i) = F (i + 1)
      rw [hrow]
      exact hrung i hi
    · change G.scheme.rowAt (emb u') (G.contextCell x) ≠ ⊥ at hx0
      change ∃ i < H, G.scheme.rowAt (emb u') (G.contextCell x) = F (i + 1)
      rw [hctx, hrow] at hx0 ⊢
      exact hval x hx hx0

end Seed

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrier
import VaughtConjecture.MainTheorem.CodedApexReading
import VaughtConjecture.MainTheorem.CodedLevelBountiful
import VaughtConjecture.MainTheorem.CodedLevelMixedLift
import VaughtConjecture.MainTheorem.CodedLevelMirror

/-!
# The strongly coded completion of the replicated coded level

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels) and Correspondence, item 1 (the
strongly coded legal stage types). All results here are native constructions of this repository.

The statements of `VaughtConjecture.MainTheorem.LevelCarrier` for the completion of the replicated
coded level by the strongly coded apex (`Seed.codedLvRepCompletion`, through
`StageType.addStrongApex`): legality, the literal context and donor faces
(`Seed.restrictFace_left_codedLvRepCompletion`, `Seed.restrictFace_donor_codedLvRepCompletion`,
`Seed.contextCell_codedLvRepCompletion`, `Seed.donorCell_codedLvRepCompletion`), the coded rungs
(`Seed.codedLvRepCompletion_rung_rows`, reading `Label.codedLadderSource`), the controllers
(`Seed.codedLvRepCompletion_ladderController`), and the carrier (`Seed.exists_codedLvRepCarrier`).
The proofs are those of `VaughtConjecture.MainTheorem.LevelCarrier`, with the facts of the coded
levels and of the strongly coded apex.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
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
theorem ground_codedLvLevel : ∀ j,
    (I.codedLvLevel g H B hd Q j).S.toCellScheme.ground = I.amalgam.toCellScheme.ground
  | 0 => rfl
  | j + 1 => ground_codedLvLevel j

/-- **The cells of the ladder base sit increasingly in every level.** -/
theorem codedLvLevel_embed_strictMono : ∀ j, StrictMono (I.codedLvLevel g H B hd Q j).embed
  | 0 => strictMono_id
  | j + 1 => (Fin.castAddOrderEmb _).strictMono.comp (codedLvLevel_embed_strictMono j)

variable (hα : Order.IsSuccPrelimit α) {N : I.ALvl g H (m + 1)} {hN : N.Good B (lvAdm hd Q)}

variable (hN) in
/-- **The completion of the replicated level**: the replicated level with a lawful labelling
reduced to the stage, and the apex added. -/
noncomputable def codedLvRepCompletion (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) : StageType.{u} α (m + 2) :=
  (lvRepType hα hN hL hq).addStrongApex hL (Nat.succ_pos _)

/-- **The completion of the replicated level is legal.** -/
theorem isLegal_codedLvRepCompletion (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) :
    (codedLvRepCompletion hα hN hL hq).IsLegal :=
  StageType.isLegal_addStrongApex _ _

/-- The faces of the completion along a proper face whose visible cells are cells of the
attachment are those of the attachment, labels included. -/
theorem restrictFace_codedLvRepCompletion (hemb : StrictMono N.embed)
    (hground : N.S.toCellScheme.ground = I.amalgam.toCellScheme.ground)
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    (hvis : ∀ z : Fin hN.rep.card, (hN.rep.toCellScheme.scope z : Set (Fin (m + 2))) ⊆
      Set.range f → z ∈ Set.range hN.repEmb) :
    restrictFace f (codedLvRepCompletion hα hN hL hq) = restrictFace f (I.attachmentType g) :=
  (StageType.restrictFace_addStrongApex _ _ _ hf).trans
    (StageType.restrictFace_eq_of_strictMono (t := lvRepType hα hN hL hq)
      (s := I.attachmentType g) f (hN.strictMono_repEmb hemb) hN.isLowerEmbedding_repEmb
      (fun c ↦ congrArg Prod.fst (hN.gradedIndex_repEmb c)) hN.comap_rows_repEmb hground hfaces
      (fun c ↦ by
        -- the label of the stage type is the reduction of `q`
        change Label.reduce α (q _) = _
        rw [hqe c]
        exact ((I.attachmentType g).atStage c).reduce_eq) hvis)

/-- **The context face of the completion is the first coatom type**, literally. -/
theorem restrictFace_left_codedLvRepCompletion (hemb : StrictMono N.embed)
    (hground : N.S.toCellScheme.ground = I.amalgam.toCellScheme.ground)
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) :
    restrictFace Fin.castSuccEmb (codedLvRepCompletion hα hN hL hq) = some I.left :=
  (restrictFace_codedLvRepCompletion hα hemb hground hfaces hL hq hqe _ Coatom.univ_map_left_ne
    fun z hz ↦ hN.mem_range_repEmb z (.inl fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
      exact mem_map_of_mem _ (mem_univ y))).trans (I.restrictFace_left_attachmentType g)

/-- **The donor face of the completion is the donor**, literally. -/
theorem restrictFace_donor_codedLvRepCompletion (hemb : StrictMono N.embed)
    (hground : N.S.toCellScheme.ground = I.amalgam.toCellScheme.ground)
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (codedLvRepCompletion hα hN hL hq) =
      some d :=
  (restrictFace_codedLvRepCompletion hα hemb hground hfaces hL hq hqe _ (map_extendByLast_ne_univ g)
    fun z hz ↦ hN.mem_range_repEmb z (.inr fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
      exact mem_map_of_mem _ (mem_univ y))).trans (I.restrictFace_donor_attachmentType g hd)

/-- **Along a proper face whose visible cells are cells of the attachment, the cells of the
completion are those of the attachment**, in their order. -/
theorem cellMap_codedLvRepCompletion (hemb : StrictMono N.embed) (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    (hvis : ∀ z : Fin hN.rep.card, (hN.rep.toCellScheme.scope z : Set (Fin (m + 2))) ⊆
      Set.range f → z ∈ Set.range hN.repEmb)
    {i : Fin ((I.attachment g).comap f).card}
    {j : Fin ((codedLvRepCompletion hα hN hL hq).toScheme.comap f).card} (hij : (i : ℕ) = j) :
    (codedLvRepCompletion hα hN hL hq).toScheme.cellMap f j =
      (hN.repEmb ((I.attachment g).cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range f (S := I.attachment g)
    (T := (codedLvRepCompletion hα hN hL hq).toScheme)
    (φ := fun c ↦ (hN.repEmb c).castSucc)
    (fun a b hab ↦ Fin.castSucc_lt_castSucc_iff.mpr (hN.strictMono_repEmb hemb hab)) (fun c ↦ ?_)
    (fun z hz ↦ ?_) hij
  · -- an old cell of the completion keeps its scope
    change (hN.rep.appendFullCellScheme (m + 2)).scope (hN.repEmb c).castSucc = _
    rw [Scheme.appendFullCellScheme_scope_castSucc]
    exact congrArg Prod.fst (hN.gradedIndex_repEmb c)
  · -- a cell of the completion is an old cell or the apex
    change Fin (hN.rep.card + 1) at z
    induction z using Fin.lastCases with
    | last =>
      exfalso
      -- the apex has full scope
      change ((hN.rep.appendFullCellScheme (m + 2)).scope (Fin.last _) :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_last, coe_univ] at hz
      exact hf (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ := hz (Set.mem_univ x)
        exact mem_map_of_mem _ (mem_univ y))
    | cast z =>
      -- an old cell of the completion keeps its scope
      change ((hN.rep.appendFullCellScheme (m + 2)).scope z.castSucc :
        Set (Fin (m + 2))) ⊆ Set.range f at hz
      rw [Scheme.appendFullCellScheme_scope_castSucc] at hz
      obtain ⟨c, rfl⟩ := hvis z hz
      exact ⟨c, rfl⟩

/-- The completion reads the cells of the replicated level as the replicated level does. -/
theorem rowAt_codedLvRepCompletion_castSucc (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) (z x : Fin hN.rep.card) :
    (codedLvRepCompletion hα hN hL hq).toScheme.rowAt z.castSucc x.castSucc = hN.rep.rowAt z x :=
  StageType.rowAt_addStrongApex_castSucc (t := lvRepType hα hN hL hq) hL _ z x

/-- The cells of the replicated level keep their graded indices in the completion. -/
theorem gradedIndex_codedLvRepCompletion_castSucc (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) (z : Fin hN.rep.card) :
    (codedLvRepCompletion hα hN hL hq).toCellScheme.gradedIndex z.castSucc =
      hN.rep.toCellScheme.gradedIndex z :=
  StageType.gradedIndex_addStrongApex_castSucc (t := lvRepType hα hN hL hq) hL _ z

/-- The apex has the full grade. -/
theorem gradedIndex_codedLvRepCompletion_last (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) :
    (codedLvRepCompletion hα hN hL hq).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin (m + 2))), m + 2) :=
  StageType.gradedIndex_addStrongApex_last (t := lvRepType hα hN hL hq) hL _

/-- **The completion keeps the actual labels of the attachment**: at the cell of a cell `c` of the
attachment, the completed stage type carries the label of `c` in the attachment, `⊤` included
(the labelling extends the labels, and the reduction to the stage fixes a label at the stage). -/
theorem codedLvRepCompletion_label_attEmb (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hN.repEmb c) = (I.attachmentType g).label c) (c : Fin (I.attachment g).card) :
    (codedLvRepCompletion hα hN hL hq).label (hN.repEmb c).castSucc =
        (I.attachmentType g).label c := by
  refine (StageType.apexLabel_castSucc (t := lvRepType hα hN hL hq) (hN.repEmb c)).trans ?_
  -- the label of the stage type is the reduction of `q`
  change Label.reduce α (q _) = _
  rw [hqe c]
  exact ((I.attachmentType g).atStage c).reduce_eq

/-- **The completion reads the cells of the level as the level does.** -/
theorem codedLvRepCompletion_rowAt_level (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q) (z x : Fin N.S.card) :
    (codedLvRepCompletion hα hN hL hq).toScheme.rowAt (Fin.castAdd _ z : Fin hN.rep.card).castSucc
      (Fin.castAdd _ x : Fin hN.rep.card).castSucc = N.S.rowAt z x :=
  rowAt_addStrongApex_of_levelShape (t := lvRepType hα hN hL hq) hL _ hN.rep_rowAt_castAdd z x

/-- **The rung readings in the completion** of the replicated top level: the rungs of a member
read themselves at the diagonal code and the preceding rung at the code of the preceding rank. -/
theorem codedLvRepCompletion_rung_rows (hH : 0 < H)
    (hNm : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (a : Scheme.RankMember (I.attachmentBase g).S H) (i : ℕ) (hi : i < H) :
    (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt
        (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a i)) :
          Fin hNm.rep.card).castSucc
        (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a i)) :
          Fin hNm.rep.card).castSucc = Label.codedLadderSource (i + 1) (i + 1) ∧
      (0 < i → (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt
        (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a i)) :
          Fin hNm.rep.card).castSucc
        (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a (i - 1))) :
          Fin hNm.rep.card).castSucc = Label.codedLadderSource (i + 1) i) := by
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
  · rw [codedLvRepCompletion_rowAt_level]
    -- the rungs are ladder points of the level
    change (I.codedLvLevel g H B hd Q m).S.rowAt (I.codedLvLad g H B hd Q m _)
        (I.codedLvLad g H B hd Q m _) = _
    rw [codedLvLevel_rowAt_lad_lad, hceil i hi]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    congr 1
    omega
  · rw [codedLvRepCompletion_rowAt_level]
    -- the rungs are ladder points of the level
    change (I.codedLvLevel g H B hd Q m).S.rowAt (I.codedLvLad g H B hd Q m _)
        (I.codedLvLad g H B hd Q m _) = _
    rw [codedLvLevel_rowAt_lad_lad, hceil (i - 1) (by omega)]
    simp only [Scheme.ladderCeil, Sum.elim_inl]
    congr 1 <;> omega

/-- **The controller clauses in the completion** of the replicated top level: a cell of full scope
at the threshold `≥ 2` is the cell of a cell `u'` of the level, and for some member `a` and table
`F` it stores on the context and donor cells (the cells of the attachment) an admitted state, reads
the top rung at least as high as the cap, the rungs as `F`, and every positive stored value below
the cap as a rung (the four clauses of `Seed.codedLvLevel_ladderController`, read through the
completion).  The bottom state is covered: it stores `⊥`. -/
theorem codedLvRepCompletion_ladderController (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (u : Fin (codedLvRepCompletion hα hNm hL hq).card)
    (hu : (codedLvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), Q.threshold)) :
    ∃ u' : Fin (I.codedLvLevel g H B hd Q m).S.card, u =
      (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc ∧
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}),
        Q.AdmitsOnClass
          (fun x ↦ (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
              Fin hNm.rep.card).castSucc)
          (fun y ↦ (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).attEmb (I.attachDonCell g hd y)) :
              Fin hNm.rep.card).castSucc) ∧
        (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).attEmb (I.attachCtxCell g Q.cap)) :
              Fin hNm.rep.card).castSucc ≤
          (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a (H - 1))) :
              Fin hNm.rep.card).castSucc ∧
        (∀ i < H, (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
            (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a i)) :
              Fin hNm.rep.card).castSucc = F (i + 1)) ∧
        ∀ x ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex Q.cap),
          (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
              (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
                Fin hNm.rep.card).castSucc ≠ ⊥ →
            ∃ i < H, (codedLvRepCompletion hα hNm hL hq).toScheme.rowAt u
              (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
                Fin hNm.rep.card).castSucc = F (i + 1) :=
  addStrongApex_ladderController_of_levelShape (t := lvRepType hα hNm hL hq) hH hcard hQ hB hN2 hL
    (Nat.succ_pos _) (κ := Fin.castAdd _) hNm.rep_rowAt_castAdd hNm.rep_gradedIndex_castAdd
    hNm.rep_mem_range_castAdd_of_scope_univ u hu

/-- **The context cells of the carrier are the cells of the attachment**: the cell of the
completion at a context cell `x` is the cell of `x` in the attachment, through the replicated
level (the cells of the attachment sit increasingly in the level,
`Seed.codedLvLevel_embed_strictMono`,
and the visible cells of the context face are cells of the attachment,
`Seed.cellMap_codedLvRepCompletion`). -/
theorem contextCell_codedLvRepCompletion (hemb : StrictMono N.embed)
    (hL : hN.rep.IsLegalBelowFullGrade) {q : Fin hN.rep.card → Label.{u}}
    (hq : hN.rep.rows.IsLawful q)
    (hleftF : restrictFace Fin.castSuccEmb (codedLvRepCompletion hα hN hL hq) = some I.left)
    (hdonF : restrictFace (extendByLast (g.trans Fin.castSuccEmb))
      (codedLvRepCompletion hα hN hL hq) = some d) (x : Fin I.left.card) :
    (GrowthCarrier.ofExtension (isLegal_codedLvRepCompletion hα hL hq) hleftF hdonF).contextCell x =
      (Fin.castAdd _ (N.attEmb (I.attachCtxCell g x)) : Fin hN.rep.card).castSucc :=
  cellMap_codedLvRepCompletion hα hemb hL hq Fin.castSuccEmb Coatom.univ_map_left_ne
    (fun z hz ↦ hN.mem_range_repEmb z (.inl fun y hy ↦ by
      obtain ⟨w, rfl⟩ := hz (mem_coe.mpr hy)
      exact mem_map_of_mem _ (mem_univ w)))
    (i := Fin.cast (congrArg Scheme.card (I.comap_left_attachment_scheme g)).symm x)
    (j := Fin.cast (congrArg Scheme.card (GrowthCarrier.ofExtension
      (isLegal_codedLvRepCompletion hα hL hq) hleftF hdonF).comap_context).symm x) rfl

/-- **The donor cells of the carrier are the cells of the attachment**, as for the context cells
(`Seed.contextCell_codedLvRepCompletion`). -/
theorem donorCell_codedLvRepCompletion (hemb : StrictMono N.embed)
    (hL : hN.rep.IsLegalBelowFullGrade) {q : Fin hN.rep.card → Label.{u}}
    (hq : hN.rep.rows.IsLawful q)
    (hleftF : restrictFace Fin.castSuccEmb (codedLvRepCompletion hα hN hL hq) = some I.left)
    (hdonF : restrictFace (extendByLast (g.trans Fin.castSuccEmb))
      (codedLvRepCompletion hα hN hL hq) = some d) (j : Fin d.card) :
    (GrowthCarrier.ofExtension (isLegal_codedLvRepCompletion hα hL hq) hleftF hdonF).donorCell j =
      (Fin.castAdd _ (N.attEmb (I.attachDonCell g hd j)) : Fin hN.rep.card).castSucc :=
  cellMap_codedLvRepCompletion hα hemb hL hq _ (map_extendByLast_ne_univ g)
    (fun z hz ↦ hN.mem_range_repEmb z (.inr fun y hy ↦ by
      obtain ⟨w, rfl⟩ := hz (mem_coe.mpr hy)
      exact mem_map_of_mem _ (mem_univ w)))
    (i := Fin.cast (congrArg Scheme.card (I.comap_donor_attachment_scheme g hd)).symm j)
    (j := Fin.cast (congrArg Scheme.card (GrowthCarrier.ofExtension
      (isLegal_codedLvRepCompletion hα hL hq) hleftF hdonF).comap_donor).symm j) rfl

include hα in
/-- **The ladder growth carrier of the replicated top level**: at a stage that is zero or a limit,
for requests calibrated on the class with threshold at least `2`, a height `H > 0` bounding the
cells of the attachment and `2 · #cells ≤ B`, if the replicated level at the grade `m + 1` is legal
below the full grade and carries a lawful labelling `q` extending the labels of the attachment,
its completion is a growth carrier with the context `I.left` and the donor `d` as literal faces, a
cell of full scope at the threshold, a field ladder of height `H`, and every cell of full scope at
the threshold a ladder controller (`Seed.codedLvLevel_ladderController`, the bottom state included:
it
stores `⊥`). -/
theorem exists_codedLvRepCarrier (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hNm.repEmb c) = (I.attachmentType g).label c) :
    ∃ G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb),
      (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
      ∃ (Mb : Type) (H' : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H' ∧
        (∀ a, ∀ i < H', G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
        (∀ a, ∀ i < H', G.scheme.rowAt (r a i) (r a i) = Label.codedLadderSource (i + 1) (i + 1)) ∧
        (∀ a, ∀ i < H', 0 < i →
          G.scheme.rowAt (r a i) (r a (i - 1)) = Label.codedLadderSource (i + 1) i) ∧
        ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
          ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H') r u a F := by
  classical
  have hemb := codedLvLevel_embed_strictMono (I := I) (g := g) (H := H) (B := B) (hd := hd)
      (Q := Q) m
  have hground := ground_codedLvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hfaces := faces_codedLvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hleftF : restrictFace Fin.castSuccEmb (codedLvRepCompletion hα hNm hL hq) = some I.left :=
    restrictFace_left_codedLvRepCompletion hα hemb hground hfaces hL hq hqe
  have hdonF : restrictFace (extendByLast (g.trans Fin.castSuccEmb))
      (codedLvRepCompletion hα hNm hL hq) = some d :=
    restrictFace_donor_codedLvRepCompletion hα hemb hground hfaces hL hq hqe
  have hctx := contextCell_codedLvRepCompletion hα hemb hL hq hleftF hdonF
  have hdon := donorCell_codedLvRepCompletion hα hemb hL hq hleftF hdonF
  -- a cell of full scope at the threshold: the threshold is at most `m + 1`, the grade of the cap
  obtain ⟨w, hw⟩ := codedLvLevel_hexist (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
    Q.threshold hN2 Q.threshold_le
  refine ⟨GrowthCarrier.ofExtension (isLegal_codedLvRepCompletion hα hL hq) hleftF hdonF,
    ⟨(Fin.castAdd _ w : Fin hNm.rep.card).castSucc,
      (gradedIndex_codedLvRepCompletion_castSucc hα hL hq _).trans
        ((hNm.rep_gradedIndex_castAdd w).trans hw)⟩,
    Scheme.RankMember (I.attachmentBase g).S H, H,
    fun a i ↦ (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a i)) :
      Fin hNm.rep.card).castSucc, hH, fun a i _ ↦ ?_,
    fun a i hi ↦ (codedLvRepCompletion_rung_rows hα hH hNm hL hq a i hi).1,
    fun a i hi hi0 ↦ (codedLvRepCompletion_rung_rows hα hH hNm hL hq a i hi).2 hi0, fun u hu ↦ ?_⟩
  · exact (gradedIndex_codedLvRepCompletion_castSucc hα hL hq _).trans
      ((hNm.rep_gradedIndex_castAdd _).trans (codedLvLevel_gradedIndex_lad m _))
  · -- the controllers, through the context and donor cells of the attachment
    obtain ⟨u', rfl, a, F, hadm, htop, hrung, hval⟩ :=
      codedLvRepCompletion_ladderController hα hH hcard hQ hB hN2 hNm hL hq u hu
    refine ⟨a, F, ?_, ?_, hrung, fun x hx hx0 ↦ ?_⟩
    · simp only [hctx, hdon]
      exact hadm
    · rw [hctx]
      exact htop
    · rw [hctx] at hx0 ⊢
      exact hval x hx hx0

end Seed

end VaughtConjecture

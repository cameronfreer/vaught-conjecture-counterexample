/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryDonorMarked

/-!
# The donor coface with the apex, and stable recovery of the donor

Roadmap, Layer 3, 3.3 (the (R4) cap) and Layer 4 (stable recovery schemes); the admitted layer with
a donor of `VaughtConjecture.Continuation.StableRecoveryDonorMarked`.

Let `I` be a seed on three points with coatom types `T` and `D`, and donor data `c` satisfying the
hypotheses of `Seed.isLegalBelowFullGrade_donorLayer` (bundled as `Seed.DonorHyp`).

* `Seed.donorCompletion`: the admitted layer with a donor is a completion below the full grade, with
  the glued labelling (the labels of `T` and `D`) extended through both layers; the glued labelling
  is admitted (correct: `D` is `⊥` at its cells labelled `⊥` and `⊤` at those labelled `⊤`).
* `Seed.isCorrect_of_isLawful_donorLayer` (**the reading back with a donor**): a lawful labelling
  of the admitted layer labelling the copy of the cap `⊤`, with its copy of `T` in the bottom class
  (bottom cells of `T` dead), is correct on the lower layer.
* `Seed.isStableRecoveryScheme_donorApex`: **stable recovery of `D`**.  At a block stage
  `λ_{ξ+1}`, with the cap labelled `⊤` in `T`, the labels of `T` in the bottom class with dead
  bottom cells, and `γ` below the replaced marker label, the donor coface (the completion: the
  truncation and the apex) is a stable recovery scheme for `T`, `Fin.castSuccEmb`, the donor `D`,
  and `γ`: every stage type on its scheme with face `T` along the first coatom has face along the
  second coatom on the scheme of `D`, `⊥` at the cells of `D` labelled `⊥` (the requests read as
  `⊥` under the cap `⊤`) and above `γ` at those labelled `⊤` (the requests from below).
* Instance: `GatedExtensionCounterexample.isStableRecoveryScheme_donorApex_P` (`D = T = P`, every
  `γ`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {c : I.DonorCap}

variable (I c) in
/-- **The hypotheses of the donor completion.** -/
structure DonorHyp : Prop where
  /-- `T` is legal. -/
  legalT : I.left.IsLegal
  /-- `D` is legal. -/
  legalD : I.right.IsLegal
  /-- The cap has grade `2`. -/
  cap_grade : I.left.toCellScheme.grade c.cap = 2
  /-- The cells of grade `1` of `D` are dead. -/
  dead : I.right.HasDeadLowCells
  /-- `D` has no cell labelled in a block. -/
  botTop : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤

/-! ### The labelling -/

/-- The glued labelling, extended through the lower layer, is correct. -/
theorem exists_isLawful_lower_glued (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤) :
    ∃ r : Fin I.lowerFieldLayer.card → Label.{u}, I.lowerFieldLayer.rows.IsLawful r ∧
      (∀ d, r (Fin.castAdd _ d) = I.amalgam.label d) ∧ (I.requestsD c).IsCorrect r := by
  obtain ⟨r, hr, hrp⟩ := Scheme.exists_isLawful_fieldLayer (S := I.amalgam.toScheme) (k := 1)
    (hS := I.not_univ_le 1) I.amalgam.isLawful
  have hd (z : Fin I.right.card) : r (I.donCell z) = I.right.label z :=
    (hrp _).trans (StageType.label_faceCell _ z)
  refine ⟨r, hr, hrp, isCorrect_requestsD hbt (fun z hz ↦ ?_) fun y hy ↦ ?_⟩
  · rw [hd, hz, min_bot_left]
  · rw [hd, hy]
    exact le_top

/-- Every cell of the admitted layer with a donor lies below `(univ, 2)`. -/
theorem mem_below_donorLayer (d : Fin (I.donorLayer c).card) :
    d ∈ (I.donorLayer c).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
  refine ⟨subset_univ _, ?_⟩
  induction d using Fin.addCases with
  | left e =>
    refine (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_le ?_
    exact I.lowerFieldLayer_grade_le e
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

/-- **A lawful labelling of the admitted layer with a donor** extending the glued labelling. -/
theorem exists_isLawful_donorLayer (hbt : ∀ z, I.right.label z = ⊥ ∨ I.right.label z = ⊤) :
    ∃ q : Fin (I.donorLayer c).card → Label.{u}, (I.donorLayer c).rows.IsLawful q ∧
      ∀ d, q (Fin.castAdd _ (Fin.castAdd _ d)) = I.amalgam.label d := by
  obtain ⟨r, hr, hrp, hrc⟩ := exists_isLawful_lower_glued (c := c) hbt
  have hb : orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) r) ∈
      I.lowerFieldLayer.admittedCatalogue 2 (I.admD c) :=
    Scheme.mem_admittedCatalogue.mpr ⟨Scheme.orbitCode_splice_bot_mem_catalogue
      (hr.isLawfulBelow _), admD_orbitCode hrc.admits⟩
  obtain ⟨q, hq, hqp⟩ := Scheme.exists_isLawfulBelow_fieldLayerOn
    (hS := I.not_univ_two_le_lowerFieldLayer) Scheme.admittedCatalogue_subset hb
  refine ⟨fun d ↦ q ⟨d, mem_below_donorLayer d⟩,
    CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall (X := ((univ : Finset (Fin 3)), 2))
      hq mem_below_donorLayer, fun d ↦ ?_⟩
  exact (hqp _ (I.lowerFieldLayer_grade_le _)).trans (hrp d)

theorem exists_donorOld_eq {d : Fin (I.donorLayer c).card}
    (hd : (I.donorLayer c).toCellScheme.scope d ≠ univ) :
    ∃ a, Fin.castAdd _ (Fin.castAdd _ a) = d := by
  induction d using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hd
  | left d =>
    induction d using Fin.addCases with
    | right i =>
      exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hd
    | left a => exact ⟨a, rfl⟩

variable (I c) in
/-- **The donor completion below the full grade.** -/
noncomputable def donorCompletion (hc : I.DonorHyp c) : CompletionBelowFullGrade I where
  scheme := I.donorLayer c
  embed := (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)
  isLowerEmbedding := (Scheme.isLowerEmbedding_castAdd (S := I.lowerFieldLayer) 2 _
      (fun i ↦ I.lowerFieldLayer.fieldRowOn 2 _ (Scheme.entryOn _ i))
      I.not_univ_two_le_lowerFieldLayer).comp
    (Scheme.isLowerEmbedding_fieldLayer I.amalgam.toScheme 1 (I.not_univ_le 1))
  scope_embed d := (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)
  comap_rows := by
    have hle2 := Scheme.isLowerEmbedding_castAdd (S := I.lowerFieldLayer) 2 _
      (fun i ↦ I.lowerFieldLayer.fieldRowOn 2
        (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)) (Scheme.entryOn _ i))
      I.not_univ_two_le_lowerFieldLayer
    have hle1 := Scheme.isLowerEmbedding_fieldLayer I.amalgam.toScheme 1 (I.not_univ_le 1)
    have e1 : (I.donorLayer c).rows.comap hle2 = I.lowerFieldLayer.rows :=
      Scheme.comap_rows_castAdd (S := I.lowerFieldLayer) (k := 2)
        (M := (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)).card)
        (r := fun i ↦ I.lowerFieldLayer.fieldRowOn 2
          (I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)) (Scheme.entryOn _ i))
        (h := I.not_univ_two_le_lowerFieldLayer)
    have e2 : I.lowerFieldLayer.rows.comap hle1 = I.amalgam.rows := Scheme.comap_rows_fieldLayer
    change ((I.donorLayer c).rows.comap hle2).comap hle1 = _
    rw [e1, e2]
  mem_range_embed z hz := by
    obtain ⟨a, rfl⟩ := exists_donorOld_eq hz
    exact ⟨a, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := isLegalBelowFullGrade_donorLayer_of_bot_top hc.legalT hc.legalD
    hc.cap_grade hc.dead hc.botTop
  label := Classical.choose (exists_isLawful_donorLayer (c := c) hc.botTop)
  isLawful := (Classical.choose_spec (exists_isLawful_donorLayer (c := c) hc.botTop)).1
  label_embed d := (Classical.choose_spec (exists_isLawful_donorLayer (c := c) hc.botTop)).2 d

/-! ### Reading back -/

/-- **Reading back the requests with a donor.** -/
theorem isCorrect_of_isLawful_donorLayer (hb : I.left.toCellScheme.grade c.cap = 2)
    (hdead : ∀ z ∈ c.botCells, I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    {q : Fin (I.donorLayer c).card → Label.{u}} (hq : (I.donorLayer c).rows.IsLawful q)
    (htop : q (Fin.castAdd _ (I.privCell c.cap)) = ⊤)
    (hcl : c.InClass fun z ↦ q (Fin.castAdd _ (I.privCell z))) :
    (I.requestsD c).IsCorrect fun d ↦ q (Fin.castAdd _ d) := by
  obtain ⟨i₀, -⟩ := Scheme.exists_entryOn_eq
    (Scheme.bot_mem_admittedCatalogue (k := 2) (S := I.lowerFieldLayer) (A := I.admD c)
      (CapRequests.admits_bot _ _ _))
  have hgcap : I.lowerFieldLayer.toCellScheme.grade (I.privCell c.cap) = 2 :=
    (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
      ((StageType.grade_faceCell _ _).trans hb)
  obtain ⟨u, hu, hle⟩ := hq.availability (Fin.castAdd _ (I.privCell c.cap)) (Fin.natAdd _ i₀)
    (by rw [Scheme.appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
      (hgcap.trans (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i₀).symm))
  obtain ⟨i, rfl⟩ :=
    Scheme.exists_natAdd_eq_fieldLayerOn (hS := I.not_univ_two_le_lowerFieldLayer)
      (hu.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀))
  have hqu : q (Fin.natAdd _ i) = ⊤ := top_le_iff.mp (htop ▸ hle)
  obtain ⟨g, σ, hw, hgs⟩ := hq.locality (Fin.natAdd _ i)
  have heC := Scheme.mem_admittedCatalogue.mp (Scheme.entryOn_mem (C :=
    I.lowerFieldLayer.admittedCatalogue 2 (I.admD c)) i)
  have he := (Scheme.mem_catalogue.mp heC.1).1
  have hcm (d : Fin I.lowerFieldLayer.card) : Fin.castAdd _ d ∈
      (I.donorLayer c).toCellScheme.below
        ((I.donorLayer c).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact mem_below_donorLayer _
  have hstate (d : Fin I.lowerFieldLayer.card) : q (Fin.castAdd _ d) =
      min (σ (Scheme.entryOn _ i d)) (g (I.lowerFieldLayer.toCellScheme.grade d)) := by
    have h : min (q (Fin.castAdd _ d)) (q (Fin.natAdd _ i)) =
        min (σ ((I.donorLayer c).rows.row (Fin.natAdd _ i) ⟨_, hcm d⟩))
          (g ((I.donorLayer c).toCellScheme.grade (Fin.castAdd _ d))) := hgs ⟨_, hcm d⟩
    rw [hqu, min_top_right] at h
    rw [h, Scheme.fieldLayerOn_row_castAdd (hS := I.not_univ_two_le_lowerFieldLayer) i d (hcm d),
      Scheme.appendFullCellsScheme_grade_castAdd]
  have heT := isLawful_privOf (he.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hcle : c.InClass fun z ↦ Scheme.entryOn _ i (I.privCell z) := fun z ↦ by
    by_cases hz : z ∈ c.botCells
    · exact ⟨fun _ ↦ hz, fun _ ↦ (heT.isLawfulBelow ((univ : Finset (Fin 2)), 2)).eq_bot_of_row_self
        (w := fun z ↦ Scheme.entryOn _ i (I.privCell z)) ⟨subset_univ _, I.left.grade_le z⟩
          (hdead z hz)⟩
    · refine ⟨fun h ↦ absurd ((hcl z).mp ?_) hz, fun h ↦ absurd h hz⟩
      change q (Fin.castAdd _ (I.privCell z)) = ⊥
      rw [hstate, show Scheme.entryOn _ i (I.privCell z) = ⊥ from h, hw.map_bot, min_bot_left]
  have hcorr := heC.2 (inBottomClass_iffD.mpr hcle)
  have hgr : (I.requestsD c).IsGraded I.lowerFieldLayer.toCellScheme.grade := by
    have h2 (d : Fin I.lowerFieldLayer.card) : I.lowerFieldLayer.toCellScheme.grade d ≤
        I.lowerFieldLayer.toCellScheme.grade (I.requestsD c).cap := by
      change _ ≤ I.lowerFieldLayer.toCellScheme.grade (I.privCell c.cap)
      rw [hgcap]
      exact I.lowerFieldLayer_grade_le d
    exact ⟨hgcap.ge, fun _ _ ↦ by change 1 ≤ 2; omega, fun z _ ↦ h2 z, fun f _ ↦ h2 f,
      fun y _ ↦ h2 y, fun f _ ↦ h2 _, h2 _⟩
  have e : (fun d ↦ q (Fin.castAdd _ d)) = fun d ↦
      min (σ (Scheme.entryOn _ i d)) (g (I.lowerFieldLayer.toCellScheme.grade d)) :=
    funext hstate
  rw [e]
  exact hcorr.map hgr hw

end Seed

/-! ### The donor coface at a block stage -/

namespace CompletionBelowFullGrade

variable {ξ : Ordinal.{u}} {J : Seed.{u} (blockStage (ξ + 1)) 1}
  (F : CompletionBelowFullGrade J)

theorem gradedIndex_completion_last :
    (F.completion (isSuccPrelimit_blockStage (ξ + 1))).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin 3)), 3) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

theorem gradedIndex_completion_castSucc (z : Fin F.scheme.card) :
    (F.completion (isSuccPrelimit_blockStage (ξ + 1))).toCellScheme.gradedIndex z.castSucc =
      F.scheme.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ _

private theorem mem_range_old_completion {f : Fin 2 ↪ Fin 3} (hf : univ.map f ≠ univ)
    (z : Fin (F.completion (isSuccPrelimit_blockStage (ξ + 1))).card)
    (hz : ((F.completion (isSuccPrelimit_blockStage (ξ + 1))).toCellScheme.scope z :
      Set (Fin 3)) ⊆ Set.range f) :
    z ∈ Set.range fun d ↦ (F.embed d).castSucc := by
  have huniv {C : Finset (Fin 3)} (hC : C = univ) (hCf : (C : Set (Fin 3)) ⊆ Set.range f) :
      False := by
    subst hC
    refine hf (eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨y, hy⟩ := hCf (mem_coe.mpr (mem_univ x))
    exact mem_map.mpr ⟨y, mem_univ _, hy⟩
  induction z using Fin.lastCases with
  | last => exact (huniv (congrArg Prod.fst F.gradedIndex_completion_last) hz).elim
  | cast z =>
    have hs := congrArg Prod.fst (F.gradedIndex_completion_castSucc z)
    obtain ⟨a, rfl⟩ := F.mem_range_embed z fun he ↦ huniv (hs.trans he) hz
    exact ⟨a, rfl⟩

private theorem cellMap_completion_eq {f : Fin 2 ↪ Fin 3} (hf : univ.map f ≠ univ)
    {k : Fin ((F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme.comap f).card}
    {i : Fin (J.amalgam.toScheme.comap f).card} (hik : (i : ℕ) = k) :
    (F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme.cellMap f k =
      (F.embed (J.amalgam.toScheme.cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range (S := J.amalgam.toScheme)
    (T := (F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme)
    (φ := fun d ↦ (F.embed d).castSucc) f ?_ ?_ (F.mem_range_old_completion hf) hik
  · exact Fin.strictMono_castSucc.comp F.embed.strictMono
  · intro d
    exact (congrArg Prod.fst (F.gradedIndex_completion_castSucc _)).trans (F.scope_embed d)

theorem cellMap_completion_left
    {k : Fin ((F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme.comap
      Fin.castSuccEmb).card} {z : Fin J.left.card} (hkz : (k : ℕ) = z) :
    (F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme.cellMap Fin.castSuccEmb k =
      (F.embed (StageType.faceCell J.restrictFace_left z)).castSucc :=
  F.cellMap_completion_eq Coatom.univ_map_left_ne (i := Fin.cast
    (congrArg Scheme.card (StageType.comap_toScheme_of_restrictFace J.restrictFace_left)).symm z)
    hkz.symm

theorem cellMap_completion_right
    {k : Fin ((F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme.comap
      (extendByLast Fin.castSuccEmb)).card} {z : Fin J.right.card} (hkz : (k : ℕ) = z) :
    (F.completion (isSuccPrelimit_blockStage (ξ + 1))).toScheme.cellMap
        (extendByLast Fin.castSuccEmb) k =
      (F.embed (StageType.faceCell J.restrictFace_right z)).castSucc :=
  F.cellMap_completion_eq Coatom.univ_map_right_ne (i := Fin.cast
    (congrArg Scheme.card (StageType.comap_toScheme_of_restrictFace J.restrictFace_right)).symm z)
    hkz.symm

end CompletionBelowFullGrade

namespace Seed

variable {ξ : Ordinal.{u}} {J : Seed.{u} (blockStage (ξ + 1)) 1} {c : J.DonorCap}

variable (J c) in
/-- **The donor coface**: the completion of the donor completion at `λ_{ξ+1}`. -/
noncomputable abbrev donorApex (hc : J.DonorHyp c) : StageType.{u} (blockStage (ξ + 1)) (1 + 2) :=
  (J.donorCompletion c hc).completion (isSuccPrelimit_blockStage (ξ + 1))

/-- **Stable recovery of the donor.**  For a seed with coatom types `T` and `D` at `λ_{ξ+1}`
satisfying `Seed.DonorHyp`, the cap labelled `⊤` in `T`, the labels of `T` in the bottom class with
dead bottom cells, and `γ` below the replaced marker label, the donor coface is a stable recovery
scheme for `T`, `Fin.castSuccEmb`, the donor `D`, and `γ`. -/
theorem isStableRecoveryScheme_donorApex (hc : J.DonorHyp c)
    (htop : J.left.label c.cap = ⊤) (hcl : c.InClass J.left.label)
    (hdead : ∀ z ∈ c.botCells, J.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    {γ : Ordinal.{u}} (hγ : (γ : Label.{u}) < visibilityReplace 2 c.R (J.left.label c.marker)) :
    J.left.IsStableRecoveryScheme Fin.castSuccEmb J.right γ (J.donorApex c hc).toScheme := by
  have hα := isSuccPrelimit_blockStage (ξ + 1)
  have hfL : restrictFace Fin.castSuccEmb (J.donorApex c hc) = some J.left :=
    (J.donorCompletion c hc).restrictFace_left_completion hα
  have hfR : restrictFace (extendByLast Fin.castSuccEmb) (J.donorApex c hc) = some J.right :=
    (J.donorCompletion c hc).restrictFace_right_completion hα
  refine ⟨⟨(J.donorApex c hc).reduce (isSuccPrelimit_blockStage ξ),
    reduce_mem_cofaces _ ⟨(J.donorCompletion c hc).isLegal_completion hα, hfL⟩, rfl⟩,
    fun Q' hQ' hQ'f ↦ ?_⟩
  obtain ⟨Qs, Ql, Qwf, Qc, Qlaw, Qat⟩ := Q'
  change Qs = _ at hQ'
  subst hQ'
  have hmem : univ.map (extendByLast Fin.castSuccEmb) ∈
      (J.donorApex c hc).toCellScheme.faces := ((restrictFace_eq_some_iff _ _).mp hfR).1
  refine ⟨StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem,
    restrictFace_of_mem (t := ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩) _ hmem,
    (comap_toScheme_of_restrictFace hfR : (J.donorApex c hc).toScheme.comap _ = _),
    fun i j hij ↦ ?_⟩
  have hq : (J.donorLayer c).rows.IsLawful fun e ↦ Ql e.castSucc := by
    have hlow := Scheme.isLowerEmbedding_castSucc (S := J.donorLayer c) 3
      (apexRow (t := (J.donorCompletion c hc).truncate hα)
        (J.donorCompletion c hc).isLegalBelowFullGrade)
      (J.donorCompletion c hc).isLegalBelowFullGrade.not_le
    have hcr : CellScheme.Rows.comap (J.donorApex c hc).rows hlow = (J.donorLayer c).rows :=
      Scheme.comap_rows_castSucc (h := (J.donorCompletion c hc).isLegalBelowFullGrade.not_le)
    have h := Qlaw.comap hlow
    rw [hcr] at h
    exact h
  have hpriv (z : Fin J.left.card) : Ql (Fin.castAdd _ (J.privCell z)).castSucc =
      J.left.label z := by
    obtain ⟨k, hkz, hlab, -⟩ := exists_cellMap_of_restrictFace_eq hQ'f z
    rw [← hlab]
    change _ = Ql (((J.donorCompletion c hc).completion
      (isSuccPrelimit_blockStage (ξ + 1))).toScheme.cellMap Fin.castSuccEmb k)
    rw [(J.donorCompletion c hc).cellMap_completion_left hkz]
    rfl
  have hlab : (StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem).label i =
      Ql (Fin.castAdd _ (J.donCell j)).castSucc := by
    change Ql (((J.donorCompletion c hc).completion
      (isSuccPrelimit_blockStage (ξ + 1))).toScheme.cellMap (extendByLast Fin.castSuccEmb) i) = _
    rw [(J.donorCompletion c hc).cellMap_completion_right hij]
    rfl
  rw [hlab]
  have hcorr := isCorrect_of_isLawful_donorLayer hc.cap_grade hdead hq
    ((hpriv c.cap).trans htop)
    fun z ↦ (iff_of_eq (congrArg (· = ⊥) (hpriv z))).trans (hcl z)
  rcases hc.botTop j with hj | hj
  · have h0 := eq_bot_of_isCorrectD hcorr hj
    change min (Ql (Fin.castAdd _ (J.donCell j)).castSucc)
      (Ql (Fin.castAdd _ (J.privCell c.cap)).castSucc) = ⊥ at h0
    rw [hpriv, htop, min_top_right] at h0
    refine ⟨fun _ ↦ h0.trans hj.symm, fun htj ↦ ?_⟩
    rw [hj] at htj
    exact absurd htj bot_ne_top
  · refine ⟨fun hne ↦ absurd hj hne, fun _ ↦ ?_⟩
    have hle := le_of_isCorrectD hcorr hj
    unfold DonorCap.value at hle
    change min (visibilityReplace 2 c.R (Ql (Fin.castAdd _ (J.privCell c.marker)).castSucc))
      (Ql (Fin.castAdd _ (J.privCell c.cap)).castSucc) ≤
        Ql (Fin.castAdd _ (J.donCell j)).castSucc at hle
    rw [hpriv, hpriv, htop, min_top_right] at hle
    exact hγ.trans_le hle

end Seed

/-! ### Instance -/

namespace GatedExtensionCounterexample

variable (ξ : Ordinal.{u})

theorem donorHyp_P (R : ℕ) (hR : R < 2) :
    (seedP (blockStage (ξ + 1))).DonorHyp (capDonorP (blockStage (ξ + 1)) R hR) where
  legalT := isLegal_P _
  legalD := isLegal_P _
  cap_grade := rfl
  dead := hasDeadLowCells_P _
  botTop := by
    change ∀ z : Fin 5, labelling ⊤ ⊤ z = ⊥ ∨ labelling ⊤ ⊤ z = ⊤
    intro z
    fin_cases z <;> simp [labelling]

/-- **Stable recovery of the donor at `P`** (`D = T = P`, over the canonical lower layer), at every
`γ`. -/
theorem isStableRecoveryScheme_donorApex_P (R : ℕ) (hR : R < 2) (γ : Ordinal.{u}) :
    (seedP (blockStage (ξ + 1))).left.IsStableRecoveryScheme Fin.castSuccEmb
      (seedP (blockStage (ξ + 1))).right γ
      (Seed.donorApex (seedP (blockStage (ξ + 1))) (capDonorP (blockStage (ξ + 1)) R hR)
        (donorHyp_P ξ R hR)).toScheme :=
  Seed.isStableRecoveryScheme_donorApex _ rfl
    (by
      change ∀ z : Fin 5, labelling ⊤ ⊤ z = ⊥ ↔ z = 0 ∨ z = 1 ∨ z = 2
      intro z
      fin_cases z <;> simp [labelling])
    (by rintro z (rfl | rfl | rfl) <;> exact hasDeadLowCells_P _ _ rfl)
    (by
      change (γ : Label.{u}) < visibilityReplace 2 R ⊤
      rw [visibilityReplace_top]
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))

end GatedExtensionCounterexample

end VaughtConjecture

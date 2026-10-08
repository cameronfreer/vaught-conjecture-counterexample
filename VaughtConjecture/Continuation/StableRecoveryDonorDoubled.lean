/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryDonorLive

/-!
# A donor other than the input on one scheme: recovery of a block label

Roadmap, Layer 3, 3.3 (the (R4) cap) and Layer 4 (stable recovery schemes).

The doubled lower layer and the marked layer of a self-seed `J` (coatom type `D`) depend on the
scheme of `D`, not on its labels.  Relabelling the first coatom by lawful labels `sT` of the scheme
of `D` gives a seed of `T` (`D` relabelled) and `D` on the same amalgamated scheme
(`Seed.relabelSeed`; faces of a relabelled type: `StageType.restrictFace_relabel`), and the marked
layer of `J` with the glued labels is a completion of it below the full grade
(`Seed.relabelCompletion`).  Lawful labellings of the doubled lower layer are symmetric at the grade
`1`, which **ties every donor cell of grade `1` to its private copy**; with `sT` agreeing with the
labels of `D` at grade `1`, the donor's labels of grade `1` are read back exactly, block labels
included.

* `Seed.exists_isCorrect_min_of_isLawful_markedLayer`: reading back at a cap of any positive
  value (the state capped at the label of a serving cell is correct).
* `Seed.isStableRecoveryScheme_relabel`: **stable recovery of `D` from the relabelled input** for
  every `γ` below the marker value of `sT`, under `Seed.MarkedHyp` (cells of grade `2` of `D`
  labelled `⊤`), the tying at grade `1`, the bottom class with dead bottom cells, a positive cap,
  and the marker value of `sT` at most the labels of `D` at grade `2`.
* Instance (`DonorScheme`): `D` the coupled-gate type, `T` its scheme with labels
  `⊥, ⊥, 1, ⊤, λ_ξ + 2` (`DonorScheme.isLawful_labLift`), `T ≠ D` (`DonorScheme.left_ne_right`),
  the separate marker; `DonorScheme.isStableRecoveryScheme_LD` (every `γ < λ_ξ + 2`) and
  `DonorScheme.recovers_z₁_LD`: **the block label `1` of `z₁` is recovered with a donor other than
  the input**.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {hLR : I.left = I.right} {c : I.left.MarkedCap}

/-- **Reading back the requests at a cap of any positive value**: a lawful labelling of the marked
layer with private copy in the bottom class (dead bottom cells) and private cap other than `⊥` is,
capped at the label `κ ≥` its private cap of a serving cell of full scope, correct on the doubled
lower layer. -/
theorem exists_isCorrect_min_of_isLawful_markedLayer (hb : I.left.toCellScheme.grade c.cap = 2)
    (hdead : ∀ z ∈ c.botCells, I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    {q : Fin (I.markedLayer hLR c).card → Label.{u}} (hq : (I.markedLayer hLR c).rows.IsLawful q)
    (hcap : q (Fin.castAdd _ (I.leftCell hLR c.cap)) ≠ ⊥)
    (hcl : c.InClass fun z ↦ q (Fin.castAdd _ (I.leftCell hLR z))) :
    ∃ κ, q (Fin.castAdd _ (I.leftCell hLR c.cap)) ≤ κ ∧ IsSelfVisible 2 κ ∧
      (I.requestsOf hLR c).IsCorrect fun d ↦ min (q (Fin.castAdd _ d)) κ := by
  obtain ⟨i₀, -⟩ := Scheme.exists_entryOn_eq
    (Scheme.bot_mem_admittedCatalogue (k := 2) (S := I.doubledLower hLR) (A := I.admOf hLR c)
      (CapRequests.admits_bot _ _ _))
  obtain ⟨u, hu, hle⟩ := hq.availability (Fin.castAdd _ (I.leftCell hLR c.cap)) (Fin.natAdd _ i₀)
    (by rw [Scheme.appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
      (((grade_leftCell c.cap).trans hb).trans
        (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i₀).symm))
  obtain ⟨i, rfl⟩ :=
    Scheme.exists_natAdd_eq_fieldLayerOn (hS := I.not_univ_two_le_doubledLower hLR)
    (hu.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀))
  have hvis : IsSelfVisible 2 (q (Fin.natAdd _ i)) := by
    have h := hq.orderly (Fin.natAdd _ i)
    rwa [Scheme.appendFullCellsScheme_grade_natAdd] at h
  have hu0 : q (Fin.natAdd _ i) ≠ ⊥ := fun h ↦ hcap (le_bot_iff.mp (h ▸ hle))
  obtain ⟨g, σ, hw, hgs⟩ := hq.locality (Fin.natAdd _ i)
  have heC := Scheme.mem_admittedCatalogue.mp (Scheme.entryOn_mem (C :=
    (I.doubledLower hLR).admittedCatalogue 2 (I.admOf hLR c)) i)
  have he := (Scheme.mem_catalogue.mp heC.1).1
  have hcm (d : Fin (I.doubledLower hLR).card) : Fin.castAdd _ d ∈
      (I.markedLayer hLR c).toCellScheme.below
        ((I.markedLayer hLR c).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact mem_below_markedLayer _
  have hstate (d : Fin (I.doubledLower hLR).card) : min (q (Fin.castAdd _ d)) (q (Fin.natAdd _ i)) =
      min (σ (Scheme.entryOn _ i d)) (g ((I.doubledLower hLR).toCellScheme.grade d)) := by
    have h : min (q (Fin.castAdd _ d)) (q (Fin.natAdd _ i)) =
        min (σ ((I.markedLayer hLR c).rows.row (Fin.natAdd _ i) ⟨_, hcm d⟩))
          (g ((I.markedLayer hLR c).toCellScheme.grade (Fin.castAdd _ d))) := hgs ⟨_, hcm d⟩
    rw [h, Scheme.fieldLayerOn_row_castAdd (hS := I.not_univ_two_le_doubledLower hLR) i d (hcm d),
      Scheme.appendFullCellsScheme_grade_castAdd]
  have hcle : c.InClass (I.privS hLR (Scheme.entryOn _ i)) := fun z ↦ by
    by_cases hz : z ∈ c.botCells
    · exact ⟨fun _ ↦ hz, fun _ ↦ I.eq_bot_privS_of_row_self hLR (hdead z hz) he⟩
    · refine ⟨fun h ↦ absurd ((hcl z).mp ?_) hz, fun h ↦ absurd h hz⟩
      have h' := hstate (I.leftCell hLR z)
      change _ = min (σ (I.privS hLR (Scheme.entryOn _ i) z)) _ at h'
      rw [h, hw.map_bot, min_bot_left] at h'
      rcases min_eq_bot.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hu0
  have hcorr := heC.2 (inBottomClass_iff.mpr hcle)
  have hgr : (I.requestsOf hLR c).IsGraded (I.doubledLower hLR).toCellScheme.grade := by
    have hcap' : (I.doubledLower hLR).toCellScheme.grade (I.requestsOf hLR c).cap = 2 :=
      (grade_leftCell c.cap).trans hb
    have h2 (d : Fin (I.doubledLower hLR).card) :
        (I.doubledLower hLR).toCellScheme.grade d ≤
          (I.doubledLower hLR).toCellScheme.grade (I.requestsOf hLR c).cap := by
      rw [hcap']
      exact grade_doubledLower_le_two d
    exact ⟨hcap'.ge, fun _ _ ↦ by change 1 ≤ 2; omega, fun z _ ↦ h2 z, fun f _ ↦ h2 f,
      fun y _ ↦ h2 y, fun f _ ↦ h2 _, h2 _⟩
  refine ⟨q (Fin.natAdd _ i), hle, hvis, ?_⟩
  have e : (fun d ↦ min (q (Fin.castAdd _ d)) (q (Fin.natAdd _ i))) = fun d ↦
      min (σ (Scheme.entryOn _ i d)) (g ((I.doubledLower hLR).toCellScheme.grade d)) :=
    funext hstate
  rw [e]
  exact hcorr.map hgr hw

end Seed

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **A stage type on the scheme of `t` with the labels `s`.** -/
def relabel (t : StageType.{u} α n) (s : Fin t.card → Label.{u}) (hs : t.rows.IsLawful s)
    (hsα : ∀ d, AtStage α (s d)) : StageType.{u} α n where
  toScheme := t.toScheme
  label := s
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := hs
  atStage := hsα

/-- **Faces of a relabelled stage type**: the face along `f` is any stage type on the scheme of the
face of `t` labelled by `s` at the copies. -/
theorem restrictFace_relabel {t : StageType.{u} α n} {f : Fin k ↪ Fin n} {p : StageType.{u} α k}
    (h : restrictFace f t = some p) {s : Fin t.card → Label.{u}} (hs : t.rows.IsLawful s)
    (hsα : ∀ d, AtStage α (s d)) {p' : StageType.{u} α k} (hp : p'.toScheme = p.toScheme)
    (hl : ∀ i : Fin p.card, p'.label (Fin.cast (congrArg Scheme.card hp).symm i) =
      s (faceCell h i)) :
    restrictFace f (t.relabel s hs hsα) = some p' := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp h
  rw [restrictFace_of_mem (t.relabel s hs hsα) f hf]
  refine congrArg some (StageType.ext hp.symm fun i j hij ↦ ?_)
  have e := hl (Fin.cast (congrArg Scheme.card hp) j)
  rw [Fin.cast_cast, Fin.cast_eq_self] at e
  rw [e]
  change s (t.toScheme.cellMap f i) = s (t.toScheme.cellMap f (Fin.cast _ _))
  congr 2
  exact Fin.ext (hij.trans rfl)

end StageType

namespace Seed

variable {α : Ordinal.{u}} (J : Seed.{u} α 1) (hLR : J.left = J.right)

/-- **The glue of `sT` with the labels of the coatom type**, at the stage. -/
theorem exists_glue_atStage {sT : Fin J.left.card → Label.{u}} (hsT : J.left.rows.IsLawful sT)
    (hsTα : ∀ d, AtStage α (sT d))
    (hroot : ∀ z, Fin.last 1 ∉ J.left.toCellScheme.scope z → sT z = J.left.label z) :
    ∃ w : Fin J.amalgam.card → Label.{u}, J.amalgam.rows.IsLawful w ∧ (∀ d, AtStage α (w d)) ∧
      (∀ z, w (StageType.faceCell J.restrictFace_left z) = sT z) ∧
      ∀ z, w (StageType.faceCell (J.restrictFace_right_left hLR) z) = J.left.label z := by
  obtain ⟨w, hw, hwL, hwR⟩ := J.exists_isLawful_glue hLR hsT J.left.isLawful hroot
  refine ⟨w, hw, fun d ↦ ?_, hwL, hwR⟩
  rcases J.mem_visibleCells_or d with hd | hd
  · obtain ⟨z, rfl⟩ := J.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace J.restrictFace_left) hd
    change AtStage α (w (StageType.faceCell J.restrictFace_left z))
    rw [hwL]
    exact hsTα z
  · obtain ⟨z, rfl⟩ := J.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace (J.restrictFace_right_left hLR)) hd
    change AtStage α (w (StageType.faceCell (J.restrictFace_right_left hLR) z))
    rw [hwR]
    exact J.left.atStage z

variable {J hLR} {sT : Fin J.left.card → Label.{u}} {hsT : J.left.rows.IsLawful sT}
  {hsTα : ∀ d, AtStage α (sT d)}
  {hroot : ∀ z, Fin.last 1 ∉ J.left.toCellScheme.scope z → sT z = J.left.label z}

variable (J hLR sT hsT hsTα hroot) in
/-- The glued labels of the amalgam. -/
noncomputable def glueLabel : Fin J.amalgam.card → Label.{u} :=
  Classical.choose (J.exists_glue_atStage hLR hsT hsTα hroot)

theorem glueLabel_spec : J.amalgam.rows.IsLawful (J.glueLabel hLR sT hsT hsTα hroot) ∧
    (∀ d, AtStage α (J.glueLabel hLR sT hsT hsTα hroot d)) ∧
    (∀ z, J.glueLabel hLR sT hsT hsTα hroot (StageType.faceCell J.restrictFace_left z) = sT z) ∧
    ∀ z, J.glueLabel hLR sT hsT hsTα hroot (StageType.faceCell (J.restrictFace_right_left hLR) z) =
      J.left.label z :=
  Classical.choose_spec (J.exists_glue_atStage hLR hsT hsTα hroot)

variable (J hLR sT hsT hsTα hroot) in
/-- **The seed of `T` (the coatom type of `J` relabelled by `sT`) and `D` (the coatom type of
`J`)**: the amalgamated scheme of `J`, with the glued labels. -/
noncomputable def relabelSeed : Seed.{u} α 1 where
  amalgam := J.amalgam.relabel (J.glueLabel hLR sT hsT hsTα hroot) glueLabel_spec.1
    glueLabel_spec.2.1
  left := J.left.relabel sT hsT hsTα
  right := J.left
  face := J.face
  isLegal_left := J.isLegal_left
  isLegal_right := J.isLegal_left
  restrictFace_face_left := StageType.restrictFace_relabel J.restrictFace_face_left hsT hsTα rfl
    fun i ↦ by
      change J.face.label i = sT _
      rw [hroot _ (StageType.last_notMem_scope_faceCell J.restrictFace_face_left i),
        StageType.label_faceCell]
  restrictFace_face_right := J.restrictFace_face_left
  restrictFace_left := StageType.restrictFace_relabel J.restrictFace_left _ _ rfl fun i ↦
    (glueLabel_spec.2.2.1 i).symm
  restrictFace_right := StageType.restrictFace_relabel (J.restrictFace_right_left hLR) _ _ rfl
    fun i ↦ (glueLabel_spec.2.2.2 i).symm
  isConsistent := J.isConsistent
  isBountiful := J.isBountiful
  subset_or_subset := J.subset_or_subset
  scope_ne_univ := J.scope_ne_univ
  exists_gradedIndex_eq := J.exists_gradedIndex_eq

end Seed

namespace Seed

/-! ### The completion of the relabelled seed on the marked layer -/

variable {α : Ordinal.{u}} {J : Seed.{u} α 1} {hLR : J.left = J.right} {c : J.left.MarkedCap}
  {sT : Fin J.left.card → Label.{u}} {hsT : J.left.rows.IsLawful sT}
  {hsTα : ∀ d, AtStage α (sT d)}
  {hroot : ∀ z, Fin.last 1 ∉ J.left.toCellScheme.scope z → sT z = J.left.label z}

/-- **The glued labels on the marked layer**: lawful, extending the glued labels of the amalgam,
when `sT` agrees with the labels of the coatom type at the cells of grade `1` and the donor copy
reads every cell of grade `2` at least as the marker value of `sT`. -/
theorem exists_isLawful_relabel (hc : J.MarkedHyp c)
    (htie : ∀ z, J.left.toCellScheme.grade z = 1 → J.left.label z = sT z)
    (h4 : ∀ y, J.left.toCellScheme.grade y = 2 → c.value sT ≤ J.left.label y) :
    ∃ q : Fin (J.markedCompletion hLR c hc).scheme.card → Label.{u},
      (J.markedCompletion hLR c hc).scheme.rows.IsLawful q ∧
        ∀ d, q ((J.markedCompletion hLR c hc).embed d) = J.glueLabel hLR sT hsT hsTα hroot d := by
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glueSym (hLR := hLR) hc.legal hsT J.left.isLawful htie
  have hadm : J.admOf hLR c g :=
    (isCorrect_requestsOf hc.legal hc.zero hc.exact hc.low hg fun y hy ↦ by
      rw [hgL, hgR]
      exact h4 y hy).admits
  have hb : orbitCode 2 ((J.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g) ∈
      (J.doubledLower hLR).admittedCatalogue 2 (J.admOf hLR c) :=
    Scheme.mem_admittedCatalogue.mpr ⟨Scheme.orbitCode_splice_bot_mem_catalogue
      (hg.isLawfulBelow _), admOf_orbitCode hadm⟩
  obtain ⟨r, hr, hrp⟩ := Scheme.exists_isLawfulBelow_fieldLayerOn
    (hS := J.not_univ_two_le_doubledLower hLR) Scheme.admittedCatalogue_subset hb
  refine ⟨fun d ↦ r ⟨d, mem_below_markedLayer d⟩,
    CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall (X := ((univ : Finset (Fin 3)), 2))
      hr mem_below_markedLayer, fun d ↦ ?_⟩
  change r ⟨Fin.castAdd _ (Fin.castAdd _ d), _⟩ = _
  rw [hrp _ (grade_doubledLower_le_two _)]
  obtain ⟨-, -, hwL, hwR⟩ := glueLabel_spec (J := J) (hLR := hLR) (sT := sT) (hsT := hsT)
    (hsTα := hsTα) (hroot := hroot)
  rcases J.mem_visibleCells_or d with hd | hd
  · obtain ⟨z, rfl⟩ := J.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace J.restrictFace_left) hd
    exact (congrFun hgL z).trans (hwL z).symm
  · obtain ⟨z, rfl⟩ := J.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace (J.restrictFace_right_left hLR)) hd
    exact (congrFun hgR z).trans (hwR z).symm

variable (J hLR c sT hsT hsTα hroot) in
/-- **The completion of the relabelled seed**: the marked layer, with the glued labels. -/
noncomputable def relabelCompletion (hc : J.MarkedHyp c)
    (htie : ∀ z, J.left.toCellScheme.grade z = 1 → J.left.label z = sT z)
    (h4 : ∀ y, J.left.toCellScheme.grade y = 2 → c.value sT ≤ J.left.label y) :
    CompletionBelowFullGrade (J.relabelSeed hLR sT hsT hsTα hroot) where
  scheme := (J.markedCompletion hLR c hc).scheme
  embed := (J.markedCompletion hLR c hc).embed
  isLowerEmbedding := (J.markedCompletion hLR c hc).isLowerEmbedding
  scope_embed := (J.markedCompletion hLR c hc).scope_embed
  comap_rows := (J.markedCompletion hLR c hc).comap_rows
  mem_range_embed := (J.markedCompletion hLR c hc).mem_range_embed
  faces_eq := (J.markedCompletion hLR c hc).faces_eq
  isLegalBelowFullGrade := (J.markedCompletion hLR c hc).isLegalBelowFullGrade
  label := Classical.choose
    (exists_isLawful_relabel (hsT := hsT) (hsTα := hsTα) (hroot := hroot) hc htie h4)
  isLawful := (Classical.choose_spec
    (exists_isLawful_relabel (hsT := hsT) (hsTα := hsTα) (hroot := hroot) hc htie h4)).1
  label_embed := (Classical.choose_spec
    (exists_isLawful_relabel (hsT := hsT) (hsTα := hsTα) (hroot := hroot) hc htie h4)).2

/-- The marker value of `sT` is at most that of `sT` capped at `κ ≥ sT b` self-visible at `2`. -/
theorem value_le_value_min {κ : Label.{u}} (hκ : sT c.cap ≤ κ) (hvis : IsSelfVisible 2 κ) :
    c.value sT ≤ c.value fun z ↦ min (sT z) κ := by
  unfold MarkedCap.value
  change _ ≤ min (visibilityReplace 2 c.R (min (sT c.marker) κ)) (min (sT c.cap) κ)
  rw [min_eq_left hκ]
  by_cases hm : sT c.marker ≤ κ
  · rw [min_eq_left hm]
  · rw [min_eq_right (not_le.mp hm).le, hvis.visibilityReplace_eq]
    exact le_min ((min_le_right _ _).trans hκ) (min_le_right _ _)

end Seed

/-! ### Stable recovery at the relabelled seed -/

namespace Seed

variable {ξ : Ordinal.{u}} {J : Seed.{u} (blockStage (ξ + 1)) 1} {hLR : J.left = J.right}
  {c : J.left.MarkedCap} {sT : Fin J.left.card → Label.{u}} {hsT : J.left.rows.IsLawful sT}
  {hsTα : ∀ d, AtStage (blockStage (ξ + 1)) (sT d)}
  {hroot : ∀ z, Fin.last 1 ∉ J.left.toCellScheme.scope z → sT z = J.left.label z}

variable (J hLR c sT hsT hsTα hroot) in
/-- **The coface of the relabelled seed** at `λ_{ξ+1}`. -/
noncomputable abbrev relabelApex (hc : J.MarkedHyp c)
    (htie : ∀ z, J.left.toCellScheme.grade z = 1 → J.left.label z = sT z)
    (h4 : ∀ y, J.left.toCellScheme.grade y = 2 → c.value sT ≤ J.left.label y) :
    StageType.{u} (blockStage (ξ + 1)) (1 + 2) :=
  (J.relabelCompletion hLR c sT hsT hsTα hroot hc htie h4).completion
    (isSuccPrelimit_blockStage (ξ + 1))

/-- **Stable recovery of the coatom type of `J` from the relabelled input.**  For a self-seed `J`
of a type `D` at `λ_{ξ+1}` with marked-cap data satisfying `Seed.MarkedHyp` (the cells of grade `2`
of `D` labelled `⊤`), and labels `sT` of the scheme of `D` that agree with those of `D` at the cells
of grade `1` (the tying), are in the bottom class with dead bottom cells, are not `⊥` at the cap,
and whose marker value is at most the labels of `D` at its cells of grade `2`, the coface of the
relabelled seed is a stable recovery scheme for `T` (the scheme of `D` labelled `sT`),
`Fin.castSuccEmb`, the donor `D` and every `γ` below the marker value of `sT`: the face along the
second coatom labels every cell of grade `1` as `D` does (block labels included). -/
theorem isStableRecoveryScheme_relabel (hc : J.MarkedHyp c)
    (htie : ∀ z, J.left.toCellScheme.grade z = 1 → J.left.label z = sT z)
    (h4 : ∀ y, J.left.toCellScheme.grade y = 2 → c.value sT ≤ J.left.label y)
    (hcl : c.InClass sT)
    (hdead : ∀ z ∈ c.botCells, J.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hcap : sT c.cap ≠ ⊥) {γ : Ordinal.{u}} (hγ : (γ : Label.{u}) < c.value sT) :
    (J.relabelSeed hLR sT hsT hsTα hroot).left.IsStableRecoveryScheme Fin.castSuccEmb
      (J.relabelSeed hLR sT hsT hsTα hroot).right γ
      (J.relabelApex hLR c sT hsT hsTα hroot hc htie h4).toScheme := by
  have hα := isSuccPrelimit_blockStage (ξ + 1)
  set F := J.relabelCompletion hLR c sT hsT hsTα hroot hc htie h4 with hF
  have hfL : restrictFace Fin.castSuccEmb (J.relabelApex hLR c sT hsT hsTα hroot hc htie h4) =
      some (J.relabelSeed hLR sT hsT hsTα hroot).left := F.restrictFace_left_completion hα
  have hfR : restrictFace (extendByLast Fin.castSuccEmb)
      (J.relabelApex hLR c sT hsT hsTα hroot hc htie h4) =
        some (J.relabelSeed hLR sT hsT hsTα hroot).right := F.restrictFace_right_completion hα
  refine ⟨⟨(J.relabelApex hLR c sT hsT hsTα hroot hc htie h4).reduce
    (isSuccPrelimit_blockStage ξ), reduce_mem_cofaces _ ⟨F.isLegal_completion hα, hfL⟩, rfl⟩,
    fun Q' hQ' hQ'f ↦ ?_⟩
  obtain ⟨Qs, Ql, Qwf, Qc, Qlaw, Qat⟩ := Q'
  change Qs = _ at hQ'
  subst hQ'
  have hmem : univ.map (extendByLast Fin.castSuccEmb) ∈
      (J.relabelApex hLR c sT hsT hsTα hroot hc htie h4).toCellScheme.faces :=
    ((restrictFace_eq_some_iff _ _).mp hfR).1
  refine ⟨StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem,
    restrictFace_of_mem (t := ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩) _ hmem,
    (comap_toScheme_of_restrictFace hfR :
      (J.relabelApex hLR c sT hsT hsTα hroot hc htie h4).toScheme.comap _ = _),
    fun i j hij ↦ ?_⟩
  have hq : (J.markedLayer hLR c).rows.IsLawful fun e ↦ Ql e.castSucc := by
    have hlow := Scheme.isLowerEmbedding_castSucc (S := J.markedLayer hLR c) 3
      (apexRow (t := F.truncate hα) F.isLegalBelowFullGrade) F.isLegalBelowFullGrade.not_le
    have hcr : CellScheme.Rows.comap
        (J.relabelApex hLR c sT hsT hsTα hroot hc htie h4).rows hlow = (J.markedLayer hLR c).rows :=
      Scheme.comap_rows_castSucc (h := F.isLegalBelowFullGrade.not_le)
    have h := Qlaw.comap hlow
    rw [hcr] at h
    exact h
  have hq0 : (J.doubledLower hLR).rows.IsLawful fun d ↦ Ql (Fin.castAdd _ d).castSucc := by
    have hle2 := Scheme.isLowerEmbedding_castAdd (S := J.doubledLower hLR) 2 _
      (fun i ↦ (J.doubledLower hLR).fieldRowOn 2
        ((J.doubledLower hLR).admittedCatalogue 2 (J.admOf hLR c)) (Scheme.entryOn _ i))
      (J.not_univ_two_le_doubledLower hLR)
    have e1 : (J.markedLayer hLR c).rows.comap hle2 = (J.doubledLower hLR).rows :=
      Scheme.comap_rows_castAdd (S := J.doubledLower hLR) (k := 2)
        (M := ((J.doubledLower hLR).admittedCatalogue 2 (J.admOf hLR c)).card)
        (r := fun i ↦ (J.doubledLower hLR).fieldRowOn 2
          ((J.doubledLower hLR).admittedCatalogue 2 (J.admOf hLR c)) (Scheme.entryOn _ i))
        (h := J.not_univ_two_le_doubledLower hLR)
    have h := hq.comap hle2
    rw [e1] at h
    exact h
  have hpriv (z : Fin J.left.card) : Ql (Fin.castAdd _ (J.leftCell hLR z)).castSucc = sT z := by
    obtain ⟨k, hkz, hlab, -⟩ := exists_cellMap_of_restrictFace_eq hQ'f z
    exact Eq.trans (congrArg Ql (F.cellMap_completion_left hkz).symm) hlab
  have hlab : (StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem).label i =
      Ql (Fin.castAdd _ (J.rightCell hLR j)).castSucc := by
    change Ql ((F.completion hα).toScheme.cellMap (extendByLast Fin.castSuccEmb) i) = _
    rw [F.cellMap_completion_right hij]
    rfl
  rw [hlab]
  rcases grade_one_or_two' j with h1 | h2
  · have heq : Ql (Fin.castAdd _ (J.rightCell hLR j)).castSucc = J.left.label j :=
      ((eq_of_grade_one hc.legal hq0 h1).trans (hpriv j)).trans (htie j h1).symm
    rw [heq]
    refine ⟨fun _ ↦ rfl, fun htop ↦ ?_⟩
    change J.left.label j = ⊤ at htop
    rw [htop]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  · refine ⟨fun hne ↦ absurd (hc.top j h2) hne, fun _ ↦ ?_⟩
    obtain ⟨κ, hκ, hvis, hcorr⟩ := exists_isCorrect_min_of_isLawful_markedLayer hc.cap_grade
      hdead hq (by rw [hpriv]; exact hcap)
      fun z ↦ (iff_of_eq (congrArg (· = ⊥) (hpriv z))).trans (hcl z)
    have hle := le_of_isCorrect_requestsOf hcorr (hc.full j h2)
    have e : J.privS hLR (fun d ↦ min (Ql (Fin.castAdd _ d).castSucc) κ) =
        fun z ↦ min (sT z) κ := funext fun z ↦ by
      change min (Ql (Fin.castAdd _ (J.leftCell hLR z)).castSucc) κ = _
      rw [hpriv]
    rw [e] at hle
    rw [hpriv] at hκ
    exact hγ.trans_le ((value_le_value_min hκ hvis).trans (hle.trans (min_le_left _ _)))

end Seed

namespace DonorScheme

/-! ### The shifter fixing the finite labels -/

private theorem lt_omega_vR {x : Label.{u}} (hx : x < ((ω : Ordinal.{u}) : Label.{u})) (k i : ℕ) :
    visibilityReplace k i x < ((ω : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o =>
    have ho : o < ω := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hx)
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ho
    have h : visibilityReplace k i ((n : Ordinal.{u}) : Label.{u}) =
        visibilityReplace k i (n : Label.{u}) := rfl
    rw [h, Label.visibilityReplace_natCast]
    split_ifs
    · exact natCast_label_lt_omega i
    · exact natCast_label_lt_omega n
  | top => exact absurd hx (not_lt.mpr le_top)

private theorem coe_ne_top' (o : Ordinal.{u}) : ((o : Ordinal.{u}) : Label.{u}) ≠ ⊤ :=
  fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)

private theorem vR_ne_top {x : Label.{u}} (hx : x ≠ ⊤) (k i : ℕ) : visibilityReplace k i x ≠ ⊤ := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o => rw [visibilityReplace_coe]; exact coe_ne_top' _
  | top => exact absurd rfl hx

/-- The shifter fixing the finite labels and sending the infinite labels other than `⊤` to `w`. -/
private noncomputable def finTo (w : Label.{u}) (x : Label.{u}) : Label.{u} := by
  classical
  exact if x = ⊥ then ⊥ else if x < ((ω : Ordinal.{u}) : Label.{u}) then x
    else if x = ⊤ then ⊤ else w

private theorem finTo_bot (w : Label.{u}) : finTo w ⊥ = ⊥ := by simp [finTo]

private theorem finTo_fin {w x : Label.{u}} (hx : x < ((ω : Ordinal.{u}) : Label.{u})) :
    finTo w x = x := by
  by_cases h0 : x = ⊥
  · rw [h0, finTo_bot]
  · simp [finTo, h0, hx]

private theorem finTo_inf {w x : Label.{u}} (h0 : x ≠ ⊥)
    (hx : ¬ x < ((ω : Ordinal.{u}) : Label.{u})) (ht : x ≠ ⊤) : finTo w x = w := by
  simp [finTo, h0, hx, ht]

private theorem finTo_top (w : Label.{u}) : finTo w ⊤ = ⊤ := by
  simp [finTo]

private theorem finTo_omegaAdd (w : Label.{u}) (j : ℕ) :
    finTo w (CoupledGatedExtensionCounterexample.omegaAdd.{u} j) = w := by
  refine finTo_inf
    (by unfold CoupledGatedExtensionCounterexample.omegaAdd; exact WithBot.coe_ne_bot)
    (fun h ↦ ?_) (by unfold CoupledGatedExtensionCounterexample.omegaAdd; exact coe_ne_top' _)
  unfold CoupledGatedExtensionCounterexample.omegaAdd at h
  exact absurd (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)) (not_lt.mpr le_self_add)

private theorem isWitness_finTo {w : Label.{u}} (hw : IsSelfVisible 2 w)
    (hwω : ((ω : Ordinal.{u}) : Label.{u}) ≤ w) :
    IsWitness (stepSuppressor 2) (finTo w) where
  antitone := (IsWitness.id_step 2).antitone
  isSelfVisible := (IsWitness.id_step 2).isSelfVisible
  map_bot := finTo_bot w
  monotone := by
    intro x y hxy
    by_cases hx0 : x = ⊥
    · rw [hx0, finTo_bot]
      exact bot_le
    by_cases hxω : x < ((ω : Ordinal.{u}) : Label.{u})
    · rw [finTo_fin hxω]
      by_cases hyω : y < ((ω : Ordinal.{u}) : Label.{u})
      · rw [finTo_fin hyω]
        exact hxy
      · have hy0 : y ≠ ⊥ := fun h ↦ hx0 (le_bot_iff.mp (h ▸ hxy))
        by_cases hyt : y = ⊤
        · rw [hyt, finTo_top]
          exact le_top
        · rw [finTo_inf hy0 hyω hyt]
          exact hxω.le.trans hwω
    · have hy0 : y ≠ ⊥ := fun h ↦ hx0 (le_bot_iff.mp (h ▸ hxy))
      have hyω : ¬ y < ((ω : Ordinal.{u}) : Label.{u}) := fun h ↦ hxω (hxy.trans_lt h)
      by_cases hyt : y = ⊤
      · rw [hyt, finTo_top]
        exact le_top
      · have hxt : x ≠ ⊤ := fun h ↦ hyt (top_le_iff.mp (h ▸ hxy))
        rw [finTo_inf hx0 hxω hxt, finTo_inf hy0 hyω hyt]
  visibilityReplace_comm x k hk i hi := by
    by_cases hx0 : x = ⊥
    · rw [hx0, visibilityReplace_bot, finTo_bot, visibilityReplace_bot]
    have hv0 : visibilityReplace k i x ≠ ⊥ := fun h ↦ hx0 (visibilityReplace_eq_bot_iff.mp h)
    by_cases hxω : x < ((ω : Ordinal.{u}) : Label.{u})
    · rw [finTo_fin hxω, finTo_fin (lt_omega_vR hxω k i)]
    by_cases hxt : x = ⊤
    · rw [hxt, visibilityReplace_top, finTo_top, visibilityReplace_top]
    rw [finTo_inf hx0 hxω hxt, finTo_inf hv0 (not_lt_omega_visibilityReplace hx0 hxω k i)
      (vR_ne_top hxt k i)]
    -- the threshold `k ≤ 2`
    have hk2 : k ≤ 2 := by
      by_contra hk'
      rw [finTo_inf hx0 hxω hxt, stepSuppressor_of_lt (by omega)] at hk
      have : ((ω : Ordinal.{u}) : Label.{u}) ≤ ⊥ := hwω.trans hk
      exact absurd this (not_le.mpr (WithBot.bot_lt_coe _))
    exact ((hw.mono hk2).visibilityReplace_eq i).symm

/-! ### The labelling `⊥, ⊥, 1, ⊤, w` -/

variable (α : Ordinal.{u}) (hα : 1 < α)

private theorem availability_casesCP' : ∀ s t : Fin 5,
    CoupledGatedExtensionCounterexample.cellScope s ⊆
      CoupledGatedExtensionCounterexample.cellScope t →
    CoupledGatedExtensionCounterexample.cellGrade s =
      CoupledGatedExtensionCounterexample.cellGrade t →
    (s = 0 ∨ s = 1) ∨ (CoupledGatedExtensionCounterexample.cellScope t =
      CoupledGatedExtensionCounterexample.cellScope s ∧
        CoupledGatedExtensionCounterexample.cellGrade t =
          CoupledGatedExtensionCounterexample.cellGrade s) := by
  decide

/-- **The labelling `⊥, ⊥, 1, ⊤, w` of the coupled-gate scheme is lawful** for `w ≥ ω`
self-visible at `2`. -/
theorem isLawful_labLift {w : Label.{u}} (hw : IsSelfVisible 2 w)
    (hwω : ((ω : Ordinal.{u}) : Label.{u}) ≤ w) :
    (CoupledGatedExtensionCounterexample.P α hα).rows.IsLawful
      (CoupledGatedExtensionCounterexample.lab 1 ⊤ w) where
  orderly d := by
    fin_cases d
    exacts [isSelfVisible_bot _, isSelfVisible_bot _,
      by change IsSelfVisible 1 (1 : Label.{u}); simp,
      isSelfVisible_top _, hw]
  locality s := by
    fin_cases s
    · exact ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ by
        change min _ ⊥ = min ⊥ ⊤
        rw [min_bot_right, min_bot_left]⟩
    · exact ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ by
        change min _ ⊥ = min ⊥ ⊤
        rw [min_bot_right, min_bot_left]⟩
    · -- the cell `z₁`, labelled `1`: the identity
      refine ⟨stepSuppressor 2, id, IsWitness.id_step 2, fun d ↦ ?_⟩
      obtain ⟨d, hd⟩ := d
      fin_cases d
      all_goals first
        | exact absurd hd.2 (by change ¬ ((2 : ℕ) ≤ 1); omega)
        | (change min ⊥ _ = min ⊥ _; rw [min_bot_left, min_bot_left])
        | (change min (1 : Label.{u}) 1 = min ((1 : ℕ) : Label.{u}) ⊤
           rw [min_self, min_top_right]; simp)
        | (change min (⊤ : Label.{u}) 1 = min ((1 : ℕ) : Label.{u}) ⊤
           rw [min_top_left, min_top_right]; simp)
    · -- the cell `z₂`, labelled `⊤`: the shifter to `⊤`
      refine ⟨stepSuppressor 2, finTo ⊤, isWitness_finTo (isSelfVisible_top 2) le_top,
        fun d ↦ ?_⟩
      obtain ⟨d, hd⟩ := d
      fin_cases d
      all_goals first
        | exact absurd hd.2 (by change ¬ ((2 : ℕ) ≤ 1); omega)
        | (change min ⊥ _ = min (finTo ⊤ ⊥) _; rw [finTo_bot, min_bot_left, min_bot_left])
        | (change min (1 : Label.{u}) ⊤ = min (finTo ⊤ ((1 : ℕ) : Label.{u})) ⊤
           rw [finTo_fin (natCast_label_lt_omega 1)]; simp)
        | (change min (⊤ : Label.{u}) ⊤ =
             min (finTo ⊤ (CoupledGatedExtensionCounterexample.omegaAdd 1)) ⊤
           rw [finTo_omegaAdd])
    · -- the full cell, labelled `w`: the shifter to `w`
      refine ⟨stepSuppressor 2, finTo w, isWitness_finTo hw hwω, fun d ↦ ?_⟩
      obtain ⟨d, hd⟩ := d
      have h1w : ((1 : ℕ) : Label.{u}) ≤ w := (natCast_label_lt_omega 1).le.trans hwω
      fin_cases d
      all_goals first
        | (change min ⊥ _ = min (finTo w ⊥) _; rw [finTo_bot, min_bot_left, min_bot_left])
        | (change min (1 : Label.{u}) w = min (finTo w ((1 : ℕ) : Label.{u})) ⊤
           rw [finTo_fin (natCast_label_lt_omega 1), min_top_right,
             min_eq_left (by simpa using h1w)]
           simp)
        | (change min (⊤ : Label.{u}) w =
             min (finTo w (CoupledGatedExtensionCounterexample.omegaAdd 1)) ⊤
           rw [finTo_omegaAdd, min_top_left, min_top_right])
        | (change min w w = min (finTo w (CoupledGatedExtensionCounterexample.omegaAdd 2)) ⊤
           rw [finTo_omegaAdd, min_self, min_top_right])
  availability s t hst hg := by
    rcases availability_casesCP' s t hst hg with hs | ⟨h1, h2⟩
    · refine ⟨t, rfl, ?_⟩
      rcases hs with rfl | rfl <;> exact bot_le
    · exact ⟨s, Prod.ext h1.symm h2.symm, le_rfl⟩

/-! ### The input `T` and the seed of `T` and `D` -/

variable (ξ : Ordinal.{u})

theorem one_lt_blockStage_succ : 1 < blockStage (ξ + 1) :=
  Ordinal.one_lt_omega0.trans_le (omega0_le_blockStage _)

/-- The label `λ_ξ + 2` of the full cell of `T`. -/
noncomputable abbrev lamTwo : Label.{u} := ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
  Label.{u})

theorem isSelfVisible_lamTwo : IsSelfVisible 2 (lamTwo ξ) :=
  isSelfVisible_coe_add (isSuccPrelimit_blockStage ξ) le_rfl

theorem omega_le_lamTwo : ((ω : Ordinal.{u}) : Label.{u}) ≤ lamTwo ξ :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((omega0_le_blockStage ξ).trans le_self_add))

theorem lamTwo_lt : lamTwo ξ < ((blockStage (ξ + 1) : Ordinal.{u}) : Label.{u}) := by
  refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
  have h : blockStage (ξ + 1) = blockStage ξ + ω := by
    simp only [blockStage, mul_add_one, add_assoc]
  rw [h]
  exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 2)

/-! ### The instance: `T` with labels `⊥, ⊥, 1, ⊤, λ_ξ + 2`, `D` the coupled-gate type -/

/-- The self-seed of the coupled-gate type at `λ_{ξ+1}`. -/
noncomputable abbrev seedDD : Seed.{u} (blockStage (ξ + 1)) 1 :=
  CoupledGatedExtensionCounterexample.seedCP _ (one_lt_blockStage_succ ξ)

/-- The labels of `T`. -/
noncomputable abbrev labT : Fin (seedDD ξ).left.card → Label.{u} :=
  CoupledGatedExtensionCounterexample.lab 1 ⊤ (lamTwo ξ)

theorem isLawful_labT : (seedDD ξ).left.rows.IsLawful (labT ξ) :=
  isLawful_labLift _ (one_lt_blockStage_succ ξ) (isSelfVisible_lamTwo ξ) (omega_le_lamTwo ξ)

theorem atStage_labT (d : Fin (seedDD ξ).left.card) : AtStage (blockStage (ξ + 1)) (labT ξ d) := by
  revert d
  change ∀ d : Fin 5, AtStage _ (CoupledGatedExtensionCounterexample.lab 1 ⊤ (lamTwo ξ) d)
  intro d
  fin_cases d
  exacts [atStage_bot, atStage_bot, Label.atStage_one.mpr (one_lt_blockStage_succ ξ), atStage_top,
    .inl (lamTwo_lt ξ)]

theorem root_labT : ∀ z, Fin.last 1 ∉ (seedDD ξ).left.toCellScheme.scope z →
    labT ξ z = (seedDD ξ).left.label z := by
  change ∀ z : Fin 5, (1 : Fin 2) ∉ CoupledGatedExtensionCounterexample.cellScope z →
    CoupledGatedExtensionCounterexample.lab 1 ⊤ (lamTwo ξ) z =
      CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ z
  intro z hz
  fin_cases z
  all_goals first | rfl | exact absurd (by decide) hz

theorem tie_labT : ∀ z, (seedDD ξ).left.toCellScheme.grade z = 1 →
    (seedDD ξ).left.label z = labT ξ z := by
  change ∀ z : Fin 5, CoupledGatedExtensionCounterexample.cellGrade z = 1 →
    CoupledGatedExtensionCounterexample.lab 1 ⊤ ⊤ z =
      CoupledGatedExtensionCounterexample.lab 1 ⊤ (lamTwo ξ) z
  intro z hz
  fin_cases z
  all_goals first | rfl | exact absurd hz (by decide)

/-- **The seed of `T` and `D`**: the self-seed of the coupled-gate type relabelled on its first
coatom by `⊥, ⊥, 1, ⊤, λ_ξ + 2`. -/
noncomputable abbrev seedLD : Seed.{u} (blockStage (ξ + 1)) 1 :=
  (seedDD ξ).relabelSeed rfl (labT ξ) (isLawful_labT ξ) (atStage_labT ξ) (root_labT ξ)

/-- **`T ≠ D`**: the full cell is labelled `λ_ξ + 2` in `T` and `⊤` in `D`. -/
theorem left_ne_right : (seedLD ξ).left ≠ (seedLD ξ).right := by
  intro h
  have h4 := StageType.label_congr h (i := ((4 : Fin 5) : Fin (seedDD ξ).left.card))
    (j := ((4 : Fin 5) : Fin (seedDD ξ).left.card)) rfl
  change lamTwo ξ = ⊤ at h4
  exact coe_ne_top' _ h4

variable (R : ℕ) (hR : R < 2)

/-- The separate-marker data of the coupled-gate type with itself. -/
noncomputable abbrev capLD : (seedDD ξ).left.MarkedCap :=
  CoupledGatedExtensionCounterexample.capSepCP _ (one_lt_blockStage_succ ξ) R hR

theorem markedHyp_LD : (seedDD ξ).MarkedHyp (capLD ξ R hR) :=
  CoupledGatedExtensionCounterexample.markedHyp_capSepCP ξ R hR

theorem value_labT : (capLD ξ R hR).value (labT ξ) = lamTwo ξ := by
  unfold MarkedCap.value
  change min (visibilityReplace 2 R ⊤) (lamTwo ξ) = lamTwo ξ
  rw [visibilityReplace_top, min_top_left]

theorem h4_LD : ∀ y, (seedDD ξ).left.toCellScheme.grade y = 2 →
    (capLD ξ R hR).value (labT ξ) ≤ (seedDD ξ).left.label y := by
  intro y hy
  rw [(markedHyp_LD ξ R hR).top y hy]
  exact le_top

theorem class_labT : (capLD ξ R hR).InClass (labT ξ) := by
  change ∀ z : Fin 5, CoupledGatedExtensionCounterexample.lab 1 ⊤ (lamTwo ξ) z = ⊥ ↔
    z = 0 ∨ z = 1
  intro z
  fin_cases z <;> simp [CoupledGatedExtensionCounterexample.lab, lamTwo]

/-- **The coface of `T` and `D`** at `λ_{ξ+1}`. -/
noncomputable abbrev apexLD : StageType.{u} (blockStage (ξ + 1)) (1 + 2) :=
  (seedDD ξ).relabelApex rfl (capLD ξ R hR) (labT ξ) (isLawful_labT ξ) (atStage_labT ξ)
    (root_labT ξ) (markedHyp_LD ξ R hR) (tie_labT ξ) (h4_LD ξ R hR)

/-- **Stable recovery with a donor other than the input, recovering a block label.**  For every
`γ < λ_ξ + 2`, the coface of `T` (labels `⊥, ⊥, 1, ⊤, λ_ξ + 2`) and `D` (the coupled-gate type) is
a stable recovery scheme for `T`, `Fin.castSuccEmb`, the donor `D` and `γ`. -/
theorem isStableRecoveryScheme_LD {γ : Ordinal.{u}} (hγ : (γ : Label.{u}) < lamTwo ξ) :
    (seedLD ξ).left.IsStableRecoveryScheme Fin.castSuccEmb (seedLD ξ).right γ
      (apexLD ξ R hR).toScheme :=
  Seed.isStableRecoveryScheme_relabel (markedHyp_LD ξ R hR) (tie_labT ξ) (h4_LD ξ R hR)
    (class_labT ξ R hR) (by rintro z (rfl | rfl) <;> rfl) WithBot.coe_ne_bot
    (by rw [value_labT]; exact hγ)

/-- **The block label `1` of `z₁` is recovered**: every stage type on the coface with face `T`
along the first coatom has, along the second, a face labelling `z₁` with `1`. -/
theorem recovers_z₁_LD {Q' : StageType.{u} (blockStage (ξ + 1)) (2 + 1)}
    (hQ' : Q'.toScheme = (apexLD ξ R hR).toScheme)
    (hf : restrictFace Fin.castSuccEmb Q' = some (seedLD ξ).left) :
    ∃ Q, restrictFace (extendByLast Fin.castSuccEmb) Q' = some Q ∧
      ∀ i : Fin Q.card, (i : ℕ) = 2 → Q.label i = (1 : Label.{u}) := by
  have h0 : ((0 : Ordinal.{u}) : Label.{u}) < lamTwo ξ :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (Ordinal.omega0_pos.trans_le
      ((omega0_le_blockStage ξ).trans le_self_add)))
  obtain ⟨Q, hQ, -, hl⟩ := (isStableRecoveryScheme_LD ξ R hR h0).2 Q' hQ' hf
  refine ⟨Q, hQ, fun i hi ↦ ?_⟩
  have h1 : (seedLD ξ).right.label ((2 : Fin 5) : Fin (seedDD ξ).left.card) = (1 : Label.{u}) :=
    rfl
  refine ((hl i _ hi).1 ?_).trans h1
  rw [h1]
  exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)

end DonorScheme

end VaughtConjecture

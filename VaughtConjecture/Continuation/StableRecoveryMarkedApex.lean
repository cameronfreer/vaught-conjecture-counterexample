/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoverySeparateMarker
import VaughtConjecture.Continuation.StableRecoveryDoubledGate

/-!
# The marked completion with the apex, and stable recovery

Roadmap, Layer 3, 3.3 (the (R4) cap) and Layer 4 (stable recovery schemes); the admitted layer of
marked-cap data of `VaughtConjecture.Continuation.StableRecoverySeparateMarker`.

Let `I` be a seed on three points whose two coatom types are equal to a legal stage type `T` on two
points, with marked-cap data `c` satisfying the hypotheses of
`Seed.isLegalBelowFullGrade_markedLayer` (bundled as `Seed.MarkedHyp`), and with the cells of
grade `2` of `T` labelled `⊤` (`StageType.HasTopFullCells`).

* `Seed.markedCompletion`: the admitted layer is a completion below the full grade
  (`CompletionBelowFullGrade`), with a lawful labelling extending the glued one: the labels of `T`
  through the cell map on the doubled lower layer (admitted: its donor copy is `⊤` at the cells of
  grade `2`), extended through the admitted field layer.
* `Seed.markedApex`: at a block stage `λ_{ξ+1}`, its completion (truncation and apex): a legal
  coface of `T` with face `T` along both coatoms.
* `Seed.isCorrect_of_isLawful_markedLayer` (**the reading back**): every lawful labelling `q` of
  the admitted layer that labels the private copy of the cap `⊤` and whose private copy is in the
  bottom class (the bottom cells dead) is correct on the doubled lower layer: availability from the
  private cap reaches a cell of full scope labelled `⊤`, its row is an admitted entry in the bottom
  class, and locality there makes `q` a transformation of that entry, so correctness passes to `q`
  (`CapRequests.IsCorrect.map`).
* `Seed.isStableRecoveryScheme_markedApex`: **stable recovery** for `T`, `f = Fin.castSuccEmb`, the
  self-donor `D = T` and every `γ` below the replaced marker label: every stage type on the scheme
  of the marked coface with face `T` along the first coatom has face along the second coatom equal
  to `T` at the cells of grade `1` (symmetry of the doubled lower layer) and above `γ` at the cells
  of grade `2` (the reading back of the requests from below).
* Instances: the coupled-gate type with the separate marker
  (`CoupledGatedExtensionCounterexample.isStableRecoveryScheme_markedApex_capSepCP`) and the private
  type `P` with the marker at the cap
  (`GatedExtensionCounterexample.isStableRecoveryScheme_markedApex_capP`), at every `γ`.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- A labelling lawful below a pair lying above every cell is lawful. -/
theorem isLawful_of_isLawfulBelow_of_forall {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) (hall : ∀ d, d ∈ D.below X) : R.IsLawful w := by
  obtain ⟨ho, hl, ha⟩ := isLawfulBelow_iff_forall.mp hw
  exact ⟨fun d ↦ ho d (hall d), fun s ↦ hl s (hall s), fun s t hst hg ↦ ha s t (hall t) hst hg⟩

end CellScheme.Rows

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {hLR : I.left = I.right} {c : I.left.MarkedCap}

variable (I c) in
/-- **The hypotheses of the marked completion**: those of `Seed.isLegalBelowFullGrade_markedLayer`
and the cells of grade `2` of `T` labelled `⊤`. -/
structure MarkedHyp : Prop where
  /-- `T` is legal. -/
  legal : I.left.IsLegal
  /-- The cap has grade `2`. -/
  cap_grade : I.left.toCellScheme.grade c.cap = 2
  /-- The cells read as `⊥` are dead of grade `1`. -/
  zero : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
    I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥
  /-- The cells read exactly have grade `1`. -/
  exact : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1
  /-- Every cell of grade `2` is read from below. -/
  full : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells
  /-- The marker is the only cell of grade `1` read from below. -/
  low : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker
  /-- The raise at the cap. -/
  raise : I.left.HasFullRaise c.cap
  /-- The cells of grade `2` are labelled `⊤`. -/
  top : I.left.HasTopFullCells

/-! ### The old cells of the admitted layer -/

/-- Every cell of the doubled lower layer has grade at most `2`. -/
theorem grade_doubledLower_le_two (d : Fin (I.doubledLower hLR).card) :
    (I.doubledLower hLR).toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left a =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    exact Nat.lt_succ_iff.mp (I.grade_lt a)
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega

/-- Every cell of the admitted layer lies below `(univ, 2)`. -/
theorem mem_below_markedLayer (d : Fin (I.markedLayer hLR c).card) :
    d ∈ (I.markedLayer hLR c).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
  refine ⟨subset_univ _, ?_⟩
  induction d using Fin.addCases with
  | left e =>
    refine (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_le ?_
    induction e using Fin.addCases with
    | left a =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      exact Nat.lt_succ_iff.mp (I.grade_lt a)
    | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

theorem gradedIndex_markedOld (d : Fin I.amalgam.card) :
    (I.markedLayer hLR c).toCellScheme.gradedIndex (Fin.castAdd _ (Fin.castAdd _ d)) =
      I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _)

/-- A cell of the admitted layer of scope other than the ground set is old. -/
theorem exists_markedOld_eq {d : Fin (I.markedLayer hLR c).card}
    (hd : (I.markedLayer hLR c).toCellScheme.scope d ≠ univ) :
    ∃ a, Fin.castAdd _ (Fin.castAdd _ a) = d := by
  induction d using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hd
  | left d =>
    induction d using Fin.addCases with
    | right i =>
      exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hd
    | left a => exact ⟨a, rfl⟩

/-! ### The labelling -/

/-- The labels of `T` through the cell map of the doubled lower layer are admitted. -/
theorem admOf_pullback (hc : I.MarkedHyp c) :
    I.admOf hLR c (I.left.label ∘ I.lowerCell hLR) :=
  (isCorrect_requestsOf hc.legal hc.zero hc.exact hc.low
    ((I.isDoubling_doubledLower hLR).isLawful_comp I.left.isLawful) fun y hy ↦ by
      change _ ≤ I.left.label (I.lowerCell hLR (I.rightCell hLR y))
      rw [lowerCell_right, hc.top y hy]
      exact le_top).admits

/-- **A lawful labelling of the admitted layer** extending the labels of `T` through the cell map
of the doubled lower layer. -/
theorem exists_isLawful_markedLayer (hc : I.MarkedHyp c) :
    ∃ q : Fin (I.markedLayer hLR c).card → Label.{u}, (I.markedLayer hLR c).rows.IsLawful q ∧
      ∀ d, q (Fin.castAdd _ d) = I.left.label (I.lowerCell hLR d) := by
  have hw := (I.isDoubling_doubledLower hLR).isLawful_comp I.left.isLawful
  have hb : orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥)
      (I.left.label ∘ I.lowerCell hLR)) ∈
        (I.doubledLower hLR).admittedCatalogue 2 (I.admOf hLR c) :=
    Scheme.mem_admittedCatalogue.mpr ⟨Scheme.orbitCode_splice_bot_mem_catalogue
      (hw.isLawfulBelow _), admOf_orbitCode (admOf_pullback hc)⟩
  obtain ⟨r, hr, hrp⟩ := Scheme.exists_isLawfulBelow_fieldLayerOn
    (hS := I.not_univ_two_le_doubledLower hLR) Scheme.admittedCatalogue_subset hb
  refine ⟨fun d ↦ r ⟨d, mem_below_markedLayer d⟩,
    CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall (X := ((univ : Finset (Fin 3)), 2))
      hr mem_below_markedLayer, fun d ↦ ?_⟩
  exact hrp d (grade_doubledLower_le_two d)

variable (I hLR c) in
/-- **The marked completion below the full grade**: the admitted layer, with a lawful labelling
extending the glued one. -/
noncomputable def markedCompletion (hc : I.MarkedHyp c) : CompletionBelowFullGrade I where
  scheme := I.markedLayer hLR c
  embed := (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)
  isLowerEmbedding := (Scheme.isLowerEmbedding_castAdd (S := I.doubledLower hLR) 2 _
      (fun i ↦ (I.doubledLower hLR).fieldRowOn 2 _ (Scheme.entryOn _ i))
      (I.not_univ_two_le_doubledLower hLR)).comp
    (Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 (I.nFull 1) (I.lowerRow hLR)
      (I.not_univ_le 1))
  scope_embed d := congrArg Prod.fst (gradedIndex_markedOld d)
  comap_rows := by
    have hle2 := Scheme.isLowerEmbedding_castAdd (S := I.doubledLower hLR) 2 _
      (fun i ↦ (I.doubledLower hLR).fieldRowOn 2
        ((I.doubledLower hLR).admittedCatalogue 2 (I.admOf hLR c)) (Scheme.entryOn _ i))
      (I.not_univ_two_le_doubledLower hLR)
    have hle1 := Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 (I.nFull 1)
      (I.lowerRow hLR) (I.not_univ_le 1)
    have e1 : (I.markedLayer hLR c).rows.comap hle2 = (I.doubledLower hLR).rows :=
      Scheme.comap_rows_castAdd (S := I.doubledLower hLR) (k := 2)
        (M := ((I.doubledLower hLR).admittedCatalogue 2 (I.admOf hLR c)).card)
        (r := fun i ↦ (I.doubledLower hLR).fieldRowOn 2
          ((I.doubledLower hLR).admittedCatalogue 2 (I.admOf hLR c)) (Scheme.entryOn _ i))
        (h := I.not_univ_two_le_doubledLower hLR)
    have e2 : (I.doubledLower hLR).rows.comap hle1 = I.amalgam.rows :=
      Scheme.comap_rows_castAdd (S := I.amalgam.toScheme) (k := 1) (M := I.nFull 1)
        (r := I.lowerRow hLR) (h := I.not_univ_le 1)
    change ((I.markedLayer hLR c).rows.comap hle2).comap hle1 = _
    rw [e1, e2]
  mem_range_embed z hz := by
    obtain ⟨a, rfl⟩ := exists_markedOld_eq hz
    exact ⟨a, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := isLegalBelowFullGrade_markedLayer hc.legal hc.cap_grade hc.zero
    hc.exact hc.full hc.low hc.raise
  label := Classical.choose (exists_isLawful_markedLayer (hLR := hLR) hc)
  isLawful := (Classical.choose_spec (exists_isLawful_markedLayer (hLR := hLR) hc)).1
  label_embed d := by
    change Classical.choose (exists_isLawful_markedLayer (hLR := hLR) hc)
      (Fin.castAdd _ (Fin.castAdd _ d)) = _
    rw [(Classical.choose_spec (exists_isLawful_markedLayer (hLR := hLR) hc)).2, lowerCell,
      Fin.append_left, I.label_amalgam hLR]

/-! ### Reading back -/

/-- **Reading back the requests**: a lawful labelling of the admitted layer labelling the private
copy of the cap `⊤`, whose private copy is in the bottom class with dead bottom cells, is correct on
the doubled lower layer. -/
theorem isCorrect_of_isLawful_markedLayer (hb : I.left.toCellScheme.grade c.cap = 2)
    (hdead : ∀ z ∈ c.botCells, I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    {q : Fin (I.markedLayer hLR c).card → Label.{u}} (hq : (I.markedLayer hLR c).rows.IsLawful q)
    (htop : q (Fin.castAdd _ (I.leftCell hLR c.cap)) = ⊤)
    (hcl : c.InClass fun z ↦ q (Fin.castAdd _ (I.leftCell hLR z))) :
    (I.requestsOf hLR c).IsCorrect fun d ↦ q (Fin.castAdd _ d) := by
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
  have hqu : q (Fin.natAdd _ i) = ⊤ := top_le_iff.mp (htop ▸ hle)
  obtain ⟨g, σ, hw, hgs⟩ := hq.locality (Fin.natAdd _ i)
  have heC := Scheme.mem_admittedCatalogue.mp (Scheme.entryOn_mem (C :=
    (I.doubledLower hLR).admittedCatalogue 2 (I.admOf hLR c)) i)
  have he := (Scheme.mem_catalogue.mp heC.1).1
  have hcm (d : Fin (I.doubledLower hLR).card) : Fin.castAdd _ d ∈
      (I.markedLayer hLR c).toCellScheme.below
        ((I.markedLayer hLR c).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact mem_below_markedLayer _
  have hstate (d : Fin (I.doubledLower hLR).card) : q (Fin.castAdd _ d) =
      min (σ (Scheme.entryOn _ i d)) (g ((I.doubledLower hLR).toCellScheme.grade d)) := by
    have h : min (q (Fin.castAdd _ d)) (q (Fin.natAdd _ i)) =
        min (σ ((I.markedLayer hLR c).rows.row (Fin.natAdd _ i) ⟨_, hcm d⟩))
          (g ((I.markedLayer hLR c).toCellScheme.grade (Fin.castAdd _ d))) := hgs ⟨_, hcm d⟩
    rw [hqu, min_top_right] at h
    rw [h, Scheme.fieldLayerOn_row_castAdd (hS := I.not_univ_two_le_doubledLower hLR) i d (hcm d),
      Scheme.appendFullCellsScheme_grade_castAdd]
  have hcle : c.InClass (I.privS hLR (Scheme.entryOn _ i)) := fun z ↦ by
    by_cases hz : z ∈ c.botCells
    · exact ⟨fun _ ↦ hz, fun _ ↦ I.eq_bot_privS_of_row_self hLR (hdead z hz) he⟩
    · refine ⟨fun h ↦ absurd ((hcl z).mp ?_) hz, fun h ↦ absurd h hz⟩
      change q (Fin.castAdd _ (I.leftCell hLR z)) = ⊥
      rw [hstate]
      change min (σ (I.privS hLR (Scheme.entryOn _ i) z)) _ = ⊥
      rw [h, hw.map_bot, min_bot_left]
  have hcorr := heC.2 (inBottomClass_iff.mpr hcle)
  have hgr : (I.requestsOf hLR c).IsGraded (I.doubledLower hLR).toCellScheme.grade := by
    have hcap : (I.doubledLower hLR).toCellScheme.grade (I.requestsOf hLR c).cap = 2 :=
      (grade_leftCell c.cap).trans hb
    have h2 (d : Fin (I.doubledLower hLR).card) :
        (I.doubledLower hLR).toCellScheme.grade d ≤
          (I.doubledLower hLR).toCellScheme.grade (I.requestsOf hLR c).cap := by
      rw [hcap]
      exact grade_doubledLower_le_two d
    exact ⟨hcap.ge, fun _ _ ↦ by change 1 ≤ 2; omega, fun z _ ↦ h2 z, fun f _ ↦ h2 f,
      fun y _ ↦ h2 y, fun f _ ↦ h2 _, h2 _⟩
  have e : (fun d ↦ q (Fin.castAdd _ d)) = fun d ↦
      min (σ (Scheme.entryOn _ i d)) (g ((I.doubledLower hLR).toCellScheme.grade d)) :=
    funext hstate
  rw [e]
  exact hcorr.map hgr hw

end Seed

/-! ### The marked coface at a block stage -/

namespace Seed

variable {ξ : Ordinal.{u}} {J : Seed.{u} (blockStage (ξ + 1)) 1} {hJ : J.left = J.right}
  {c : J.left.MarkedCap}

variable (J hJ c) in
/-- **The marked coface**: the completion (truncation and apex) of the marked completion at the
block stage `λ_{ξ+1}`. -/
noncomputable def markedApex (hc : J.MarkedHyp c) : StageType.{u} (blockStage (ξ + 1)) (1 + 2) :=
  (J.markedCompletion hJ c hc).completion (isSuccPrelimit_blockStage (ξ + 1))

theorem gradedIndex_markedApex_last (hc : J.MarkedHyp c) :
    (J.markedApex hJ c hc).toCellScheme.gradedIndex (Fin.last _) =
      ((univ : Finset (Fin 3)), 3) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

theorem gradedIndex_markedApex_castSucc (hc : J.MarkedHyp c)
    (z : Fin (J.markedCompletion hJ c hc).scheme.card) :
    (J.markedApex hJ c hc).toCellScheme.gradedIndex z.castSucc =
      (J.markedCompletion hJ c hc).scheme.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ _

/-- The cells of the marked coface visible through a coatom are old cells. -/
private theorem mem_range_old_markedApex (hc : J.MarkedHyp c) {f : Fin 2 ↪ Fin 3}
    (hf : univ.map f ≠ univ) (z : Fin (J.markedApex hJ c hc).card)
    (hz : ((J.markedApex hJ c hc).toCellScheme.scope z : Set (Fin 3)) ⊆ Set.range f) :
    z ∈ Set.range fun d ↦ ((J.markedCompletion hJ c hc).embed d).castSucc := by
  have huniv {C : Finset (Fin 3)} (hC : C = univ) (hCf : (C : Set (Fin 3)) ⊆ Set.range f) :
      False := by
    subst hC
    refine hf (eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨y, hy⟩ := hCf (mem_coe.mpr (mem_univ x))
    exact mem_map.mpr ⟨y, mem_univ _, hy⟩
  induction z using Fin.lastCases with
  | last =>
    exact (huniv (congrArg Prod.fst (gradedIndex_markedApex_last hc)) hz).elim
  | cast z =>
    have hs : (J.markedApex hJ c hc).toCellScheme.scope z.castSucc =
        (J.markedCompletion hJ c hc).scheme.toCellScheme.scope z :=
      congrArg Prod.fst (gradedIndex_markedApex_castSucc hc z)
    obtain ⟨a, rfl⟩ :=
      (J.markedCompletion hJ c hc).mem_range_embed z fun he ↦ huniv (hs.trans he) hz
    exact ⟨a, rfl⟩

/-- The enumeration of the cells visible through a coatom, through the old cells. -/
private theorem cellMap_markedApex_eq (hc : J.MarkedHyp c) {f : Fin 2 ↪ Fin 3}
    (hf : univ.map f ≠ univ) {k : Fin ((J.markedApex hJ c hc).toScheme.comap f).card}
    {i : Fin (J.amalgam.toScheme.comap f).card} (hik : (i : ℕ) = k) :
    (J.markedApex hJ c hc).toScheme.cellMap f k =
      ((J.markedCompletion hJ c hc).embed (J.amalgam.toScheme.cellMap f i)).castSucc := by
  refine Scheme.cellMap_eq_of_strictMono_of_mem_range (S := J.amalgam.toScheme)
    (T := (J.markedApex hJ c hc).toScheme)
    (φ := fun d ↦ ((J.markedCompletion hJ c hc).embed d).castSucc) f ?_ ?_
    (mem_range_old_markedApex hc hf) hik
  · exact Fin.strictMono_castSucc.comp (J.markedCompletion hJ c hc).embed.strictMono
  · intro d
    exact (congrArg Prod.fst (gradedIndex_markedApex_castSucc hc _)).trans
      ((J.markedCompletion hJ c hc).scope_embed d)

/-- **The copies along the first coatom.** -/
theorem cellMap_markedApex_left (hc : J.MarkedHyp c)
    {k : Fin ((J.markedApex hJ c hc).toScheme.comap Fin.castSuccEmb).card} {z : Fin J.left.card}
    (hkz : (k : ℕ) = z) :
    (J.markedApex hJ c hc).toScheme.cellMap Fin.castSuccEmb k =
      (Fin.castAdd _ (J.leftCell hJ z)).castSucc :=
  cellMap_markedApex_eq hc Coatom.univ_map_left_ne (i := Fin.cast
    (congrArg Scheme.card (StageType.comap_toScheme_of_restrictFace J.restrictFace_left)).symm z)
    hkz.symm

/-- **The copies along the second coatom.** -/
theorem cellMap_markedApex_right (hc : J.MarkedHyp c)
    {k : Fin ((J.markedApex hJ c hc).toScheme.comap (extendByLast Fin.castSuccEmb)).card}
    {z : Fin J.left.card} (hkz : (k : ℕ) = z) :
    (J.markedApex hJ c hc).toScheme.cellMap (extendByLast Fin.castSuccEmb) k =
      (Fin.castAdd _ (J.rightCell hJ z)).castSucc :=
  cellMap_markedApex_eq hc Coatom.univ_map_right_ne (i := Fin.cast
    (congrArg Scheme.card
      (StageType.comap_toScheme_of_restrictFace (J.restrictFace_right_left hJ))).symm z)
    hkz.symm

/-- **Stable recovery at the marked coface.**  For a seed whose two coatom types equal a legal stage
type `T` at `λ_{ξ+1}` on two points, marked-cap data with the cap of grade `2`, the cells read as
`⊥` dead of grade `1`, the cells read exactly of grade `1`, every cell of grade `2` read from
below, the marker the only cell of grade `1` read from below, the raise at the cap, the cells of
grade `2` labelled `⊤`, the labels of `T` in the bottom class with dead bottom cells, and `γ` below
the replaced marker label, the marked coface is a stable recovery scheme for `T`,
`Fin.castSuccEmb`, the self-donor `T`, and `γ`. -/
theorem isStableRecoveryScheme_markedApex (hc : J.MarkedHyp c)
    (hcl : c.InClass J.left.label)
    (hdead : ∀ z ∈ c.botCells, J.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    {γ : Ordinal.{u}} (hγ : (γ : Label.{u}) < visibilityReplace 2 c.R (J.left.label c.marker)) :
    J.left.IsStableRecoveryScheme Fin.castSuccEmb J.left γ (J.markedApex hJ c hc).toScheme := by
  have hα := isSuccPrelimit_blockStage (ξ + 1)
  have hfL : restrictFace Fin.castSuccEmb (J.markedApex hJ c hc) = some J.left :=
    (J.markedCompletion hJ c hc).restrictFace_left_completion hα
  have hfR : restrictFace (extendByLast Fin.castSuccEmb) (J.markedApex hJ c hc) = some J.left :=
    ((J.markedCompletion hJ c hc).restrictFace_right_completion hα).trans (by rw [hJ])
  refine ⟨⟨(J.markedApex hJ c hc).reduce (isSuccPrelimit_blockStage ξ),
    reduce_mem_cofaces _ ⟨(J.markedCompletion hJ c hc).isLegal_completion hα, hfL⟩, rfl⟩,
    fun Q' hQ' hQ'f ↦ ?_⟩
  obtain ⟨Qs, Ql, Qwf, Qc, Qlaw, Qat⟩ := Q'
  change Qs = _ at hQ'
  subst hQ'
  have hmem : univ.map (extendByLast Fin.castSuccEmb) ∈
      (J.markedApex hJ c hc).toCellScheme.faces := ((restrictFace_eq_some_iff _ _).mp hfR).1
  refine ⟨StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem,
    restrictFace_of_mem (t := ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩) _ hmem,
    (comap_toScheme_of_restrictFace hfR : (J.markedApex hJ c hc).toScheme.comap _ = _),
    fun i j hij ↦ ?_⟩
  -- the labels on the admitted layer are lawful
  have hq : (J.markedLayer hJ c).rows.IsLawful fun e ↦ Ql e.castSucc := by
    have hlow := Scheme.isLowerEmbedding_castSucc (S := J.markedLayer hJ c) 3
      (apexRow (t := (J.markedCompletion hJ c hc).truncate hα)
        (J.markedCompletion hJ c hc).isLegalBelowFullGrade)
      (J.markedCompletion hJ c hc).isLegalBelowFullGrade.not_le
    have hcr : CellScheme.Rows.comap (J.markedApex hJ c hc).rows hlow = (J.markedLayer hJ c).rows :=
      Scheme.comap_rows_castSucc (h := (J.markedCompletion hJ c hc).isLegalBelowFullGrade.not_le)
    have h := Qlaw.comap hlow
    rw [hcr] at h
    exact h
  have hq0 : (J.doubledLower hJ).rows.IsLawful fun d ↦ Ql (Fin.castAdd _ d).castSucc := by
    have hle2 := Scheme.isLowerEmbedding_castAdd (S := J.doubledLower hJ) 2 _
      (fun i ↦ (J.doubledLower hJ).fieldRowOn 2
        ((J.doubledLower hJ).admittedCatalogue 2 (J.admOf hJ c)) (Scheme.entryOn _ i))
      (J.not_univ_two_le_doubledLower hJ)
    have e1 : (J.markedLayer hJ c).rows.comap hle2 = (J.doubledLower hJ).rows :=
      Scheme.comap_rows_castAdd (S := J.doubledLower hJ) (k := 2)
        (M := ((J.doubledLower hJ).admittedCatalogue 2 (J.admOf hJ c)).card)
        (r := fun i ↦ (J.doubledLower hJ).fieldRowOn 2
          ((J.doubledLower hJ).admittedCatalogue 2 (J.admOf hJ c)) (Scheme.entryOn _ i))
        (h := J.not_univ_two_le_doubledLower hJ)
    have h := hq.comap hle2
    rw [e1] at h
    exact h
  -- the private copies are labelled as in `T`
  have hpriv (z : Fin J.left.card) : Ql (Fin.castAdd _ (J.leftCell hJ z)).castSucc =
      J.left.label z := by
    obtain ⟨k, hkz, hlab, -⟩ := exists_cellMap_of_restrictFace_eq hQ'f z
    rw [← hlab]
    change _ = Ql ((J.markedApex hJ c hc).toScheme.cellMap Fin.castSuccEmb k)
    rw [cellMap_markedApex_left hc hkz]
  -- the donor face reads the donor copies
  have hlab : (StageType.comap ⟨_, Ql, Qwf, Qc, Qlaw, Qat⟩ _ hmem).label i =
      Ql (Fin.castAdd _ (J.rightCell hJ j)).castSucc := by
    change Ql ((J.markedApex hJ c hc).toScheme.cellMap (extendByLast Fin.castSuccEmb) i) = _
    rw [cellMap_markedApex_right hc hij]
  rw [hlab]
  rcases grade_one_or_two' j with h1 | h2
  · have heq : Ql (Fin.castAdd _ (J.rightCell hJ j)).castSucc = J.left.label j :=
      (eq_of_grade_one hc.legal hq0 h1).trans (hpriv j)
    rw [heq]
    refine ⟨fun _ ↦ rfl, fun htop ↦ ?_⟩
    rw [htop]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  · refine ⟨fun hne ↦ absurd (hc.top j h2) hne, fun _ ↦ ?_⟩
    have hcorr := isCorrect_of_isLawful_markedLayer hc.cap_grade hdead hq
      ((hpriv c.cap).trans (hc.top _ hc.cap_grade))
      fun z ↦ (iff_of_eq (congrArg (· = ⊥) (hpriv z))).trans (hcl z)
    have hle := le_of_isCorrect_requestsOf hcorr (hc.full j h2)
    unfold MarkedCap.value at hle
    change min (visibilityReplace 2 c.R (Ql (Fin.castAdd _ (J.leftCell hJ c.marker)).castSucc))
      (Ql (Fin.castAdd _ (J.leftCell hJ c.cap)).castSucc) ≤
        Ql (Fin.castAdd _ (J.rightCell hJ j)).castSucc at hle
    rw [hpriv, hpriv, hc.top _ hc.cap_grade, min_top_right] at hle
    exact hγ.trans_le hle

end Seed

/-! ### Instances -/

private theorem one_lt_blockStage (ξ : Ordinal.{u}) : 1 < blockStage ξ :=
  Ordinal.one_lt_omega0.trans_le (omega0_le_blockStage ξ)

private theorem coe_lt_top' (γ : Ordinal.{u}) : (γ : Label.{u}) < ⊤ :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

namespace CoupledGatedExtensionCounterexample

variable (ξ : Ordinal.{u})

/-- The separate marker at the coupled-gate type satisfies the hypotheses of the marked
completion. -/
theorem markedHyp_capSepCP (R : ℕ) (hR : R < 2) :
    (seedCP (blockStage (ξ + 1)) (one_lt_blockStage _)).MarkedHyp
      (capSepCP (blockStage (ξ + 1)) (one_lt_blockStage _) R hR) where
  legal := isLegal_P _ (one_lt_blockStage _)
  cap_grade := rfl
  zero := by rintro z rfl; exact ⟨rfl, rfl⟩
  exact := by rintro z rfl; rfl
  full := by
    change ∀ z : Fin 5, cellGrade z = 2 → z = 3 ∨ z = 4
    decide
  low := by
    change ∀ y : Fin 5, y = 3 ∨ y = 4 → cellGrade y = 1 → y = 3
    decide
  raise := StageType.hasFullRaise_of_unique (by
    change ∀ z : Fin 5, cellGrade z = 2 → z = 4
    decide)
  top := by
    change ∀ z : Fin 5, cellGrade z = 2 → lab 1 ⊤ ⊤ z = ⊤
    intro z hz
    fin_cases z
    all_goals first | rfl | exact absurd hz (by decide)

/-- **Stable recovery at the coupled-gate type with the separate marker**, at every `γ`. -/
theorem isStableRecoveryScheme_markedApex_capSepCP (R : ℕ) (hR : R < 2) (γ : Ordinal.{u}) :
    (seedCP (blockStage (ξ + 1)) (one_lt_blockStage _)).left.IsStableRecoveryScheme
      Fin.castSuccEmb (seedCP (blockStage (ξ + 1)) (one_lt_blockStage _)).left γ
      (Seed.markedApex (seedCP (blockStage (ξ + 1)) (one_lt_blockStage _)) rfl
        (capSepCP (blockStage (ξ + 1)) (one_lt_blockStage _) R hR)
        (markedHyp_capSepCP ξ R hR)).toScheme :=
  Seed.isStableRecoveryScheme_markedApex _
    (by
      change ∀ z : Fin 5, lab 1 ⊤ ⊤ z = ⊥ ↔ z = 0 ∨ z = 1
      intro z
      fin_cases z <;> simp [lab])
    (by rintro z (rfl | rfl) <;> rfl)
    (by
      change (γ : Label.{u}) < visibilityReplace 2 R ⊤
      rw [visibilityReplace_top]
      exact coe_lt_top' γ)

end CoupledGatedExtensionCounterexample

namespace GatedExtensionCounterexample

variable (ξ : Ordinal.{u})

/-- The marker at the cap at `P` satisfies the hypotheses of the marked completion. -/
theorem markedHyp_capP (R : ℕ) (hR : R < 2) :
    (seedP (blockStage (ξ + 1))).MarkedHyp (capP (blockStage (ξ + 1)) R hR) where
  legal := isLegal_P _
  cap_grade := rfl
  zero := fun _ h ↦ h.elim
  exact := fun _ h ↦ h.elim
  full := by
    change ∀ z : Fin 5, cellGrade z = 2 → z = 3 ∨ z = 4
    decide
  low := by
    change ∀ y : Fin 5, y = 3 ∨ y = 4 → cellGrade y = 1 → y = 4
    decide
  raise := StageType.hasFullRaise_of_dead_top (hasDeadLowCells_P _) (hasTopFullCells_P _) rfl
  top := hasTopFullCells_P _

/-- **Stable recovery at `P` with the marker at the cap**, at every `γ`. -/
theorem isStableRecoveryScheme_markedApex_capP (R : ℕ) (hR : R < 2) (γ : Ordinal.{u}) :
    (seedP (blockStage (ξ + 1))).left.IsStableRecoveryScheme Fin.castSuccEmb
      (seedP (blockStage (ξ + 1))).left γ
      (Seed.markedApex (seedP (blockStage (ξ + 1))) rfl (capP (blockStage (ξ + 1)) R hR)
        (markedHyp_capP ξ R hR)).toScheme :=
  Seed.isStableRecoveryScheme_markedApex _
    (by
      change ∀ z : Fin 5, labelling ⊤ ⊤ z = ⊥ ↔ z = 0 ∨ z = 1 ∨ z = 2
      intro z
      fin_cases z <;> simp [labelling])
    (by rintro z (rfl | rfl | rfl) <;> exact hasDeadLowCells_P _ _ rfl)
    (by
      change (γ : Label.{u}) < visibilityReplace 2 R ⊤
      rw [visibilityReplace_top]
      exact coe_lt_top' γ)

end GatedExtensionCounterexample

end VaughtConjecture

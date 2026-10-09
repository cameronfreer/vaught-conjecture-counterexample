/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayLayer

/-!
# The separator labels of the completed display

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the reading of the
display); semantic contract, items 3, 4 and 8.

`StageType.HasLowLayers` asks, besides a LOW layer (`StageType.IsLowLayer`, compiled for the
completed display in `VaughtConjecture.Continuation.LowDisplayLayer`), for the separator to be
labelled by a proper label (`lo`) and by `⊤` (`hi`) in the labelling of the display.  The labels
of the completed display are a lawful labelling `q` of the completed scheme at the stage
extending the glued labels.  This file shows that in the completed display over the catalogue
layer with the canonical levels above it, `⊤` at a controller forces `⊥` above its grade.

**The canonical levels read a controller of positive cutoff as `⊥`** (compiled in this
repository).  The section operator of the catalogue layer reads the controllers through the code of
the profile with the cutoff `⊥` (`ProfileTower.Lvl.catσ`): the agreement height of a profile with
the cutoff `⊥` and a profile with a positive cutoff is `⊥`, so the section reads every controller
of positive cutoff as `⊥` (`ProfileTower.Lvl.catσ_natAdd_eq_bot`).  The canonical levels above
read the cells below through the section of the level below (`ProfileTower.Lvl.next`), so every
section of every canonical level, and every row of a cell of full scope above the grade of the
controller, reads it as `⊥` (`ProfileTower.Lvl.iter_read_eq_bot`).

**A positive label at a controller forces `⊥` above it** (`ProfileTower.lowDisplay_label_eq_bot`,
compiled in this repository).  Let `q` be a lawful labelling of the completed display at the stage,
not `⊥` (for instance `⊤`) at a controller `hi` of positive cutoff, of grade `K = g + 1`.  Every
cell `u` of full scope and grade `j` with `K < j ≤ m` reads `hi` as `⊥`; locality at `u` at the cell
`hi` below it gives `min (q hi) (q u) = σ ⊥ = ⊥`, so `q u = ⊥`; availability then puts every cell of
grade `j` below a cell of graded index `(univ, j)`, so every cell of grade in `(K, m]` is labelled
`⊥`.  The separator `hi` of a LOW layer has positive cutoff (its cutoff cut lies below its cutoff).

**The decisive consequence** (`ProfileTower.face_label_eq_bot_of_lowDisplay`,
`ProfileTower.lowDisplay_ctrl_eq_bot`, compiled in this repository).  If the completed display over
the catalogue layer has a lawful labelling extending the glued labels with a label other than `⊥` at
a controller of positive cutoff, then every cell of the private context and of the donor of grade in
`(K, m]` is labelled `⊥`.  So for a LOW family with `K < k` and a cell of grade in `(K, k]` not
labelled `⊥` in the context or the donor, the completed display carries no separator labelled as
`StageType.HasLowLayers` asks, whatever the LOW layer: the canonical levels above the controllers
must be replaced, at their sections at the controllers, for the LOW construction to label its
separator `⊤`.  Conversely, when the two faces are `⊥` above `K`, the reading holds
(`ProfileTower.lowReading_of_bot`, in `VaughtConjecture.Continuation.LowDisplayActual`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The canonical levels read a controller of positive cutoff as `⊥` -/

section Read

variable {g : ℕ} {L : Lvl I g} {A : CProf I → Prop}

local notation "𝒞" => predCat I (g + 1) A

/-- **The section of the catalogue layer reads a controller of positive cutoff as `⊥`**: the
agreement height of a profile with the cutoff `⊥` and one with a positive cutoff is `⊥`. -/
theorem Lvl.catσ_natAdd_eq_bot (P : Prof I) {i : Fin (𝒞).card}
    (hi : ((𝒞).equivFin.symm i).1 (Sum.inr ()) ≠ ⊥) :
    L.catσ A P (Fin.natAdd L.S.card i) = ⊥ := by
  rw [Lvl.catσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_natAdd]), Lvl.Φcat_natAdd]
  have hG : (⊥ : Label.{u}) ∈ grid (g + 1) (bound I) := bot_mem_grid _ _
  have h := (agreementHeight_spec hG (withCut (code (g + 1) P) ⊥)
    ((𝒞).equivFin.symm i).1).2 (Sum.inr ())
  have h' : min (((𝒞).equivFin.symm i).1 (Sum.inr ())) (agreementHeight (grid (g + 1) (bound I))
      (withCut (code (g + 1) P) ⊥) ((𝒞).equivFin.symm i).1) = ⊥ := by
    rw [← h]
    exact min_eq_left bot_le
  rw [(min_eq_bot.mp h').resolve_left hi, upperDecoderAt_bot]

end Read

/-- **The canonical levels above a level read a cell of grade at most the grade of the level as
`⊥`, when every section of the level does**: every section of every canonical level above, and
every row of a cell of full scope of grade above that of the level, reads it as `⊥`. -/
theorem Lvl.iter_read_eq_bot {g' : ℕ} (N : Lvl I g') {x : Fin N.S.card}
    (hxg : N.S.toCellScheme.grade x ≤ g') (hσ : ∀ P, N.σ P x = ⊥) :
    ∀ J, (∀ P, (N.iter J).σ P (N.iterEmb J x) = ⊥) ∧
      ∀ u, (N.iter J).S.toCellScheme.scope u = univ → g' < (N.iter J).S.toCellScheme.grade u →
        (N.iter J).S.rowAt u (N.iterEmb J x) = ⊥
  | 0 => ⟨hσ, fun u hu hg ↦ by
      change g' < N.S.toCellScheme.grade u at hg
      exact (N.inv u).elim (fun h ↦ absurd hg (by omega)) fun h ↦ absurd hu h⟩
  | J + 1 => by
    obtain ⟨ihσ, ihrow⟩ := N.iter_read_eq_bot hxg hσ J
    have hyg : (N.iter J).S.toCellScheme.grade (N.iterEmb J x) ≤ g' + J + 1 := by
      rw [(N.isGradePrefix_iter J).lowerEmb.grade_eq]; omega
    refine ⟨fun P ↦ ?_, fun u hu hg ↦ ?_⟩
    · change (N.iter J).nextσ P (Fin.castAdd _ (N.iterEmb J x)) = ⊥
      rw [Lvl.nextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_castAdd]; exact hyg),
        Lvl.Φ_castAdd, ihσ, upperDecoderAt_bot]
    · change (N.iter J).nextS.rowAt u (Fin.castAdd _ (N.iterEmb J x)) = ⊥
      induction u using Fin.addCases with
      | left v =>
        rw [Scheme.rowAt_appendFullCells_castAdd]
        refine ihrow v ?_ ?_
        · rwa [← Scheme.appendFullCellsScheme_scope_castAdd (N.iter J).S (g' + J + 1)
            (cat I (g' + J + 1)).card v]
        · have := hg
          change g' < (Lvl.nextS (N.iter J)).toCellScheme.grade (Fin.castAdd _ v) at this
          rwa [Scheme.appendFullCellsScheme_grade_castAdd] at this
      | right i =>
        by_cases hmem : Fin.castAdd (cat I (g' + J + 1)).card (N.iterEmb J x) ∈
            (N.iter J).nextS.toCellScheme.below
              ((N.iter J).nextS.toCellScheme.gradedIndex (Fin.natAdd _ i))
        · rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, Lvl.Φ_castAdd, ihσ]
        · exact Scheme.rowAt_of_notMem hmem

/-! ### `⊤` at a controller forces `⊥` above it -/

/-- **A cell reading a cell labelled other than `⊥` as `⊥` is labelled `⊥`**: locality at the
cell, at the cell below it, gives `min (label x) (label u) = σ ⊥ = ⊥`. -/
theorem _root_.VaughtConjecture.StageType.label_eq_bot_of_rowAt_eq_bot {n : ℕ}
    (D : StageType.{u} α n) {u x : Fin D.card}
    (hx : x ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u))
    (hrow : D.toScheme.rowAt u x = ⊥) (hpos : D.label x ≠ ⊥) : D.label u = ⊥ := by
  obtain ⟨gg, σ, hσ, heq⟩ := D.isLawful.locality u
  have h := heq ⟨x, hx⟩
  rw [Scheme.rowAt_of_mem hx] at hrow
  dsimp only at h
  rw [hrow, hσ.map_bot, min_eq_left bot_le] at h
  exact (min_eq_bot.mp h).resolve_left hpos

section Display

variable {g j : ℕ} {I : Seed.{u} α (g + 1 + j)} {L : Lvl I g} {A : CProf I → Prop}
  (hL : L.Good) (hN : (L.catNext A).Good) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
  {q : Fin (lowCompletion hL hN hA0).scheme.card → Label.{u}}
  (hq : (lowCompletion hL hN hA0).scheme.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d))

/-- **The level at the grade `m` is a grade prefix of the display** at `m`. -/
theorem isGradePrefix_top_display :
    Scheme.IsGradePrefix ((L.catNext A).iter j).S ((lowCompletion hL hN hA0).display hq
      hqα).toScheme (Fin.castSucc ∘ Fin.castAdd _) (g + 1 + j) :=
  ((lowCompletion hL hN hA0).isGradePrefix_display hq hqα (by omega)).comp
    (Scheme.IsGradePrefix.castAdd (S := ((L.catNext A).iter j).S) (k := g + 1 + j + 1)
      (M := (((L.catNext A).iter j).S.catalogue (g + 1 + j + 1)).card)
      (r := fun i ↦ ((L.catNext A).iter j).S.fieldRow (g + 1 + j + 1)
        (((L.catNext A).iter j).S.catalogueEntry (g + 1 + j + 1) i))
      (h := ((L.catNext A).iter j).not_le) (by omega))

local notation "𝒞" => predCat I (g + 1) A

/-- **A label other than `⊥` at a controller of positive cutoff forces `⊥` at every cell of full
scope above it**, up to the grade `m`: such a cell reads the controller as `⊥`
(`ProfileTower.Lvl.iter_read_eq_bot`), and locality at it at the controller gives its label. -/
theorem lowDisplay_label_full_eq_bot {i : Fin (𝒞).card}
    (hi : ((𝒞).equivFin.symm i).1 (Sum.inr ()) ≠ ⊥)
    (htop : ((lowCompletion hL hN hA0).display hq hqα).label
      (Fin.castSucc (lowCellMap j A L (Fin.natAdd L.S.card i))) ≠ ⊥)
    {u : Fin ((lowCompletion hL hN hA0).display hq hqα).card}
    (hu : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.scope u = univ)
    (hug : g + 1 < ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade u)
    (hum : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade u ≤ g + 1 + j) :
    ((lowCompletion hL hN hA0).display hq hqα).label u = ⊥ := by
  have hP := isGradePrefix_top_display hL hN hA0 hq hqα
  obtain ⟨u', rfl⟩ := hP.mem_range u hum
  have hx : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade (Fin.natAdd L.S.card i) =
      g + 1 := Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i
  have hread := ((L.catNext A).iter_read_eq_bot (x := Fin.natAdd L.S.card i) hx.le
    (fun P ↦ Lvl.catσ_natAdd_eq_bot P hi) j).2 u'
    (by rw [← hP.scope_eq]; exact hu) (by rw [← hP.lowerEmb.grade_eq]; exact hug)
  have hle : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.gradedIndex
      ((Fin.castSucc ∘ Fin.castAdd _) ((L.catNext A).iterEmb j (Fin.natAdd L.S.card i))) ≤
      ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.gradedIndex
        ((Fin.castSucc ∘ Fin.castAdd _) u') := by
    refine (hP.gradedIndex_eq _).trans_le (LE.le.trans_eq ?_ (hP.gradedIndex_eq u').symm)
    refine (((L.catNext A).isGradePrefix_iter j).gradedIndex_eq
      (Fin.natAdd L.S.card i)).trans_le ⟨?_, ?_⟩
    · have hu' : ((L.catNext A).iter j).S.toCellScheme.scope u' = univ :=
        (hP.scope_eq u').symm.trans hu
      change _ ⊆ ((L.catNext A).iter j).S.toCellScheme.scope u'
      rw [hu']
      exact subset_univ _
    · change (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade _ ≤
        ((L.catNext A).iter j).S.toCellScheme.grade u'
      rw [hx, ← hP.lowerEmb.grade_eq u']
      exact hug.le
  exact StageType.label_eq_bot_of_rowAt_eq_bot _ hle ((hP.rowAt_eq _ _).trans hread) htop

/-- **A label other than `⊥` at a controller of positive cutoff forces `⊥` at every cell above
it**, up to the grade `m`: availability puts each such cell below a cell of full scope of its grade.
-/
theorem lowDisplay_label_eq_bot {i : Fin (𝒞).card}
    (hi : ((𝒞).equivFin.symm i).1 (Sum.inr ()) ≠ ⊥)
    (htop : ((lowCompletion hL hN hA0).display hq hqα).label
      (Fin.castSucc (lowCellMap j A L (Fin.natAdd L.S.card i))) ≠ ⊥)
    {z : Fin ((lowCompletion hL hN hA0).display hq hqα).card}
    (hzg : g + 1 < ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade z)
    (hzm : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade z ≤ g + 1 + j) :
    ((lowCompletion hL hN hA0).display hq hqα).label z = ⊥ := by
  have hP := isGradePrefix_top_display hL hN hA0 hq hqα
  obtain ⟨e, he⟩ := (hN.iter j le_rfl).complete
    (((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade z) (by omega) hzm
  have hge := (hP.gradedIndex_eq e).trans he
  have hs : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.scope
      ((Fin.castSucc ∘ Fin.castAdd _) e) = univ := congrArg Prod.fst hge
  have hg : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade
      ((Fin.castSucc ∘ Fin.castAdd _) e) = _ := congrArg Prod.snd hge
  obtain ⟨u, hu, hzu⟩ := ((lowCompletion hL hN hA0).display hq hqα).isLawful.availability z
    ((Fin.castSucc ∘ Fin.castAdd _) e) (by rw [hs]; exact subset_univ _) hg.symm
  have hu' := hu.trans hge
  have hug : ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade u =
      ((lowCompletion hL hN hA0).display hq hqα).toCellScheme.grade z := congrArg Prod.snd hu'
  rw [lowDisplay_label_full_eq_bot hL hN hA0 hq hqα hi htop (congrArg Prod.fst hu')
    (by rw [hug]; exact hzg) (by rw [hug]; exact hzm)] at hzu
  exact le_bot_iff.mp hzu

include hq hqα in
/-- **A label other than `⊥` at a controller of positive cutoff forces `⊥` on the two faces above
it**: every cell of
the private context and of the donor of grade in `(g + 1, m]` is labelled `⊥`, when `q` extends the
glued labels. -/
theorem face_label_eq_bot_of_lowDisplay
    (hqe : ∀ d, q ((lowCompletion hL hN hA0).embed d) = I.amalgam.label d) {i : Fin (𝒞).card}
    (hi : ((𝒞).equivFin.symm i).1 (Sum.inr ()) ≠ ⊥)
    (htop : q (lowCellMap j A L (Fin.natAdd L.S.card i)) ≠ ⊥) :
    (∀ x : Fin I.left.card, g + 1 < I.left.toCellScheme.grade x →
      I.left.toCellScheme.grade x ≤ g + 1 + j → I.left.label x = ⊥) ∧
    ∀ x : Fin I.right.card, g + 1 < I.right.toCellScheme.grade x →
      I.right.toCellScheme.grade x ≤ g + 1 + j → I.right.label x = ⊥ := by
  have htop' : ((lowCompletion hL hN hA0).display hq hqα).label
      (Fin.castSucc (lowCellMap j A L (Fin.natAdd L.S.card i))) ≠ ⊥ := fun h ↦
    htop ((CompletionBelowFullGrade.display_label_castSucc _ hq hqα _).symm.trans h)
  have h₁ := (lowCompletion hL hN hA0).restrictFace_left_display (hq := hq) (hqα := hqα) hqe
  have h₂ := (lowCompletion hL hN hA0).restrictFace_right_display (hq := hq) (hqα := hqα) hqe
  refine ⟨fun x hxg hxm ↦ ?_, fun x hxg hxm ↦ ?_⟩
  · rw [← StageType.label_faceCell h₁ x]
    exact lowDisplay_label_eq_bot hL hN hA0 hq hqα hi htop' (by rw [grade_faceCell]; exact hxg)
      (by rw [grade_faceCell]; exact hxm)
  · rw [← StageType.label_faceCell h₂ x]
    exact lowDisplay_label_eq_bot hL hN hA0 hq hqα hi htop' (by rw [grade_faceCell]; exact hxg)
      (by rw [grade_faceCell]; exact hxm)

include hq hqα in
/-- **No separation with ordinal labels above the controllers**: if the private context or the
donor has a cell of grade in `(g + 1, m]` not labelled `⊥`, every lawful labelling of the
completed display extending the glued labels labels every controller of positive cutoff by `⊥`.
So no controller of positive cutoff (the upper cell of a separator, whose cutoff is above its
cutoff cut) is labelled above any cell; this holds for every labelling keeping the actual faces. -/
theorem lowDisplay_ctrl_eq_bot
    (hqe : ∀ d, q ((lowCompletion hL hN hA0).embed d) = I.amalgam.label d)
    (hne : (∃ x : Fin I.left.card, g + 1 < I.left.toCellScheme.grade x ∧
      I.left.toCellScheme.grade x ≤ g + 1 + j ∧ I.left.label x ≠ ⊥) ∨
      ∃ x : Fin I.right.card, g + 1 < I.right.toCellScheme.grade x ∧
        I.right.toCellScheme.grade x ≤ g + 1 + j ∧ I.right.label x ≠ ⊥)
    {i : Fin (𝒞).card} (hi : ((𝒞).equivFin.symm i).1 (Sum.inr ()) ≠ ⊥) :
    q (lowCellMap j A L (Fin.natAdd L.S.card i)) = ⊥ := by
  by_contra hpos
  obtain ⟨h₁, h₂⟩ := face_label_eq_bot_of_lowDisplay hL hN hA0 hq hqα hqe hi hpos
  rcases hne with ⟨x, hxK, hxm, hx⟩ | ⟨x, hxK, hxm, hx⟩
  · exact hx (h₁ x hxK hxm)
  · exact hx (h₂ x hxK hxm)

end Display

/-! ### The reading of the completed display -/

section Reading

variable {g j : ℕ} {I : Seed.{u} α (g + 1 + j)} {o r : Fin I.left.card}

local notation "𝒜" => lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒞" => lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

variable (o r) in
/-- **The reading of the completed display** (at a stage that is zero or a limit it holds exactly
when the two faces are `⊥` above `K`: `ProfileTower.LowReading.face_label_eq_bot`, and
`ProfileTower.lowReading_of_bot` in `VaughtConjecture.Continuation.LowDisplayActual`) over a good
level `L` at the grade `g` whose
LOW layer is a good level: a lawful labelling `q` at the stage of the completed scheme extending the
glued labels, and two controllers whose profiles are a profile of the LOW catalogue and its partner
over all proper donor cells, with the cutoff cut in the grid and below the cutoff, labelled by `q`
by a proper label and by `⊤`. -/
def LowReading (L : Lvl I g) (hL : L.Good) (hN : (L.catNext 𝒜).Good) : Prop :=
  ∃ (q : Fin (lowCompletion hL hN lowPred_withCut_bot).scheme.card → Label.{u})
    (_ : (lowCompletion hL hN lowPred_withCut_bot).scheme.rows.IsLawful q)
    (_ : ∀ d, AtStage α (q d))
    (_ : ∀ d, q ((lowCompletion hL hN lowPred_withCut_bot).embed d) = I.amalgam.label d)
    (ilo ihi : Fin (𝒞).card),
    ((𝒞).equivFin.symm ilo).1 = Function.update ((𝒞).equivFin.symm ihi).1 (Sum.inr ())
      (cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1) ∧
    cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 ∈ grid (g + 1) (bound I) ∧
    cutoffCut (g + 1) (lowNAll I) ((𝒞).equivFin.symm ihi).1 <
      ((𝒞).equivFin.symm ihi).1 (Sum.inr ()) ∧
    q (lowCellMap j 𝒜 L (Fin.natAdd L.S.card ilo)) ≠ ⊤ ∧
    q (lowCellMap j 𝒜 L (Fin.natAdd L.S.card ihi)) = ⊤

/-- **The reading gives a legal display with a LOW layer and its separator labelled by a proper
label and `⊤`**, with faces the private context and the donor (`ProfileTower.isLowLayer_lowDisplay`,
`CompletionBelowFullGrade.isLegal_display`). -/
theorem LowReading.exists_isLowLayer {L : Lvl I g} {hL : L.Good} {hN : (L.catNext 𝒜).Good}
    (h : LowReading o r L hL hN) :
    ∃ (D : StageType.{u} α (g + 1 + j + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧
        D.label hi = ⊤ ∧ IsLowLayer (g + 1) h₁ h₂ o r G entry s lo hi := by
  obtain ⟨q, hq, hqα, hqe, ilo, ihi, hsep, hmem, hlt, hlo, hhi⟩ := h
  refine ⟨_, _, _, _, _, _, _, _, (lowCompletion hL hN lowPred_withCut_bot).isLegal_display hq hqα,
    ?_, ?_, isLowLayer_lowDisplay hL hN hqe hsep hmem hlt⟩
  · exact fun h' ↦ hlo ((CompletionBelowFullGrade.display_label_castSucc
      (lowCompletion hL hN lowPred_withCut_bot) hq hqα _).symm.trans h')
  · exact (CompletionBelowFullGrade.display_label_castSucc
      (lowCompletion hL hN lowPred_withCut_bot) hq hqα _).trans hhi

/-- **The reading forces `⊥` on the two faces above the grade of the controllers**
(`ProfileTower.face_label_eq_bot_of_lowDisplay`): the controller labelled `⊤` has positive
cutoff, its cutoff cut lying below it. -/
theorem LowReading.face_label_eq_bot {L : Lvl I g} {hL : L.Good} {hN : (L.catNext 𝒜).Good}
    (h : LowReading o r L hL hN) :
    (∀ x : Fin I.left.card, g + 1 < I.left.toCellScheme.grade x →
      I.left.toCellScheme.grade x ≤ g + 1 + j → I.left.label x = ⊥) ∧
    ∀ x : Fin I.right.card, g + 1 < I.right.toCellScheme.grade x →
      I.right.toCellScheme.grade x ≤ g + 1 + j → I.right.label x = ⊥ := by
  obtain ⟨q, hq, hqα, hqe, -, ihi, -, -, hlt, -, hhi⟩ := h
  exact face_label_eq_bot_of_lowDisplay hL hN _ hq hqα hqe (ne_bot_of_gt hlt)
    (by rw [hhi]; exact top_ne_bot)

end Reading

end VaughtConjecture.ProfileTower

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedWriting

/-!
# The copies at a mixed face, and the copied ladder

Roadmap, Layer 3 ((R3) and (R4), the recognition on the copies).

At a mixed face `U` the replicated scheme has one copy (`Seed.copyAt`) of every cell of full scope
of the ladder tower over the attachment of grade at most `|U|`, of scope `U` and the grade of its
original (`Seed.gradedIndex_copyAt`).  The copies at `U` read one another as their originals do
(`Seed.rowAt_copyAt_copyAt`), and read the cells of the attachment inside `U` as their originals
do (`Seed.rowAt_copyAt_attachEmb`).  In particular the copies at `U` of the ladder points
(`Seed.copyLadder`) form a **copied field ladder** with the rows of the ladder
(`Seed.rowAt_copyLadder`), and a copy of a controller reads the copied ladder as the controller
reads the ladder (`Seed.rowAt_copyAt_copyLadder`): the data of `GrowthCarrier.recognizes_of_ladder`
is present inside every mixed face.

**Recognition at a copy** (`Seed.copy_recognition`).  A section `w` lawful below a pair containing
the copy `k` at a mixed face `U` of a controller storing the state `R` reads, at the cells of the
attachment inside `U`, a witness image `σ ∘ R` (locality at `k`); if `w` is positive at `k` and at
the copied top rung, every copied rung is positive (`Scheme.rungs_ne_bot_of_top`, the ladder
predecessor steps), so `σ` sends no positive value of `R` to `⊥`.  What remains of the lift from a
mixed face (not compiled here) is to extend the recognized state to the context cells outside `U`,
render it on the cells of full scope, and keep the observation of the ambient at the cap.

## References

The controllers and the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

variable (H Γ A B') in
/-- **The copy at the mixed face `U`** of a cell `f` of full scope of the tower of grade at most
`|U|`. -/
noncomputable def copyAt (hU : U ∈ I.mixedFaces g) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U) :
    Fin (I.replicated g H Γ A B').card :=
  Fin.natAdd _ ((I.attachTower g H Γ A B').copyEquiv (I.mixedFaces g) ⟨(U, f), hU, hf, hfg⟩)

/-- The original of the copy at `U` of `f` is `f`. -/
theorem mirrorOrig_copyAt (hU : U ∈ I.mixedFaces g) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U) :
    (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (copyAt H Γ A B' hU f hf hfg) = f := by
  rw [copyAt, Scheme.mirrorOrig_natAdd, Equiv.symm_apply_apply]

/-- The copy at `U` of `f` has the scope `U` and the grade of `f`. -/
theorem gradedIndex_copyAt (hU : U ∈ I.mixedFaces g) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U) :
    (I.replicated g H Γ A B').toCellScheme.gradedIndex (copyAt H Γ A B' hU f hf hfg) =
      (U, (I.attachTower g H Γ A B').toCellScheme.grade f) := by
  change ((I.attachTower g H Γ A B').mirrorScope (I.mixedFaces g) _,
    (I.attachTower g H Γ A B').toCellScheme.grade
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) _)) = _
  rw [copyAt, Scheme.mirrorScope_natAdd, Scheme.mirrorOrig_natAdd, Equiv.symm_apply_apply]

/-- **The copies at `U` read one another as their originals do.** -/
theorem rowAt_copyAt_copyAt (hU : U ∈ I.mixedFaces g)
    {f f' : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    (hf' : (I.attachTower g H Γ A B').toCellScheme.scope f' = univ)
    (hfg' : (I.attachTower g H Γ A B').toCellScheme.grade f' ≤ #U)
    (hle : (I.attachTower g H Γ A B').toCellScheme.grade f' ≤
      (I.attachTower g H Γ A B').toCellScheme.grade f) :
    (I.replicated g H Γ A B').rowAt (copyAt H Γ A B' hU f hf hfg)
        (copyAt H Γ A B' hU f' hf' hfg') =
      (I.attachTower g H Γ A B').rowAt f f' := by
  have hmem : copyAt H Γ A B' hU f' hf' hfg' ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex (copyAt H Γ A B' hU f hf hfg)) := by
    rw [CellScheme.mem_below, gradedIndex_copyAt, gradedIndex_copyAt]
    exact ⟨subset_rfl, hle⟩
  rw [Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_copyAt, mirrorOrig_copyAt]

/-- **A copy at `U` reads the cells of the attachment inside `U` as its original does.** -/
theorem rowAt_copyAt_attachEmb (hU : U ∈ I.mixedFaces g)
    {f : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    {c : Fin (I.attachment g).card} (hcs : (I.attachment g).toCellScheme.scope c ⊆ U)
    (hcg : (I.attachment g).toCellScheme.grade c ≤
      (I.attachTower g H Γ A B').toCellScheme.grade f) :
    (I.replicated g H Γ A B').rowAt (copyAt H Γ A B' hU f hf hfg) (I.attachEmb g H Γ A B' c) =
      (I.attachTower g H Γ A B').rowAt f ((I.attachmentBase g).baseCellEmb m c) := by
  have hmem : I.attachEmb g H Γ A B' c ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex (copyAt H Γ A B' hU f hf hfg)) := by
    rw [CellScheme.mem_below, gradedIndex_copyAt, gradedIndex_attachEmb]
    exact ⟨hcs, hcg⟩
  rw [Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_copyAt]
  change (I.attachTower g H Γ A B').rowAt f
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ _)) = _
  rw [Scheme.mirrorOrig_castAdd]

/-! ### The copied ladder -/

variable (H Γ A B') in
/-- The ladder point `p` of the tower over the attachment. -/
noncomputable abbrev ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (I.attachTower g H Γ A B').card :=
  (I.attachmentBase g).towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m
    (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))

theorem gradedIndex_ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').toCellScheme.gradedIndex (ladCell H Γ A B' p) =
      ((univ : Finset (Fin (m + 2))), 1) := by
  refine (Scheme.gradedIndex_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ m).trans ?_
  change ((I.attachmentBase g).S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
  exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _

theorem grade_ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').toCellScheme.grade (ladCell H Γ A B' p) = 1 :=
  congrArg Prod.snd (gradedIndex_ladCell p)

/-- A mixed face is not empty. -/
theorem one_le_card_of_mem_mixedFaces (hU : U ∈ I.mixedFaces g) : 1 ≤ #U := by
  obtain ⟨-, -, hc, -⟩ := (I.mem_mixedFaces g).mp hU
  rcases U.eq_empty_or_nonempty with he | hne
  · exact absurd (he ▸ empty_subset _) hc
  · exact hne.card_pos

variable (H Γ A B') in
/-- **The copied ladder** at the mixed face `U`: the copies at `U` of the ladder points. -/
noncomputable def copyLadder (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (I.replicated g H Γ A B').card :=
  copyAt H Γ A B' hU (ladCell H Γ A B' p) (congrArg Prod.fst (gradedIndex_ladCell p))
    ((grade_ladCell p).trans_le (one_le_card_of_mem_mixedFaces hU))

/-- The copied ladder points have the scope `U` and the grade `1`. -/
theorem gradedIndex_copyLadder (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').toCellScheme.gradedIndex (copyLadder H Γ A B' hU p) = (U, 1) :=
  (gradedIndex_copyAt _ _ _ _).trans (Prod.ext rfl (grade_ladCell p))

/-- **The copied ladder has the rows of the ladder.** -/
theorem rowAt_copyLadder (hU : U ∈ I.mixedFaces g)
    (p q : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').rowAt (copyLadder H Γ A B' hU p) (copyLadder H Γ A B' hU q) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (Scheme.baseIndex H (Scheme.rankProf (I.attachmentBase g).S H) p.1
          (Fin.natAdd _ (Scheme.ladderEquiv _ _ H q))) := by
  refine (rowAt_copyAt_copyAt hU _ _ _ _ ?_).trans ?_
  · rw [grade_ladCell, grade_ladCell]
  · exact (Scheme.rowAt_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
      (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ _ m).trans
      (Scheme.rowAt_ladderBase_ladder (hS := (I.attachmentBase g).noFull)
        (I.attachmentBase g).wf p q)

/-- **A copy of a cell of full scope reads the copied ladder as its original reads the ladder.** -/
theorem rowAt_copyAt_copyLadder (hU : U ∈ I.mixedFaces g)
    {f : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    (hf1 : 1 ≤ (I.attachTower g H Γ A B').toCellScheme.grade f)
    (q : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').rowAt (copyAt H Γ A B' hU f hf hfg) (copyLadder H Γ A B' hU q) =
      (I.attachTower g H Γ A B').rowAt f (ladCell H Γ A B' q) :=
  rowAt_copyAt_copyAt hU _ _ _ _
    ((grade_ladCell q).trans_le hf1)

/-! ### Positivity along a ladder -/

/-- **Positivity along a field ladder**: in a lawful section below a pair containing rungs of
graded index `(V, 1)` whose rows read the diagonal code and the code of the preceding rank, a
positive top rung makes every rung positive (`Label.eq_bot_of_ladder_predecessor`). -/
theorem _root_.VaughtConjecture.Scheme.rungs_ne_bot_of_top {k : ℕ} {S : Scheme.{u} k}
    (hpos : ∀ d, 0 < S.toCellScheme.grade d) {Y : Finset (Fin k) × ℕ}
    {w : Fin S.card → Label.{u}} (hw : S.rows.IsLawfulBelow Y fun d ↦ w d) {H : ℕ}
    {V : Finset (Fin k)} (r : ℕ → Fin S.card)
    (hr : ∀ i < H, S.toCellScheme.gradedIndex (r i) = (V, 1))
    (hrY : ∀ i < H, r i ∈ S.toCellScheme.below Y)
    (hrd : ∀ i < H, S.rowAt (r i) (r i) = ladderSource (i + 1) (i + 1))
    (hrp : ∀ i < H, 0 < i → S.rowAt (r i) (r (i - 1)) = ladderSource (i + 1) i)
    (htop : w (r (H - 1)) ≠ ⊥) : ∀ i < H, w (r i) ≠ ⊥ := by
  have hall1 (z : Fin S.card) (i : ℕ) (hi : i < H)
      (hz : z ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex (r i))) :
      S.toCellScheme.grade z = 1 := by
    have h1 : S.toCellScheme.grade z ≤ 1 := by
      have := hz.2
      rw [hr i hi] at this
      exact this
    have h2 := hpos z
    omega
  intro i hi h0
  have key : ∀ j, i + j < H → w (r (i + j)) = ⊥ := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      set c' := r (i + (j + 1))
      have hloc := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 c' (hrY _ hj)
      have hloc' : TransformsTo (fun _ : S.toCellScheme.below (S.toCellScheme.gradedIndex c') ↦ 1)
          (S.rows.row c') (fun z ↦ min (w z) (w c')) := by
        convert hloc using 2 with z
        exact (hall1 z.1 _ hj z.2).symm
      have hcm : c' ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c') :=
        CellScheme.mem_below_gradedIndex _ _
      have hdm : r (i + j) ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c') :=
        le_of_eq ((hr _ (by omega)).trans (hr _ hj).symm)
      exact eq_bot_of_ladder_predecessor
        (D := S.toCellScheme.below (S.toCellScheme.gradedIndex c'))
        (t := i + (j + 1) + 1) (by omega) hloc' (c := ⟨c', hcm⟩) (d := ⟨r (i + j), hdm⟩)
        (by rw [← Scheme.rowAt_of_mem hcm]; exact hrd _ hj)
        (by
          rw [← Scheme.rowAt_of_mem hdm]
          have h2 := hrp _ hj (by omega)
          rw [show i + (j + 1) - 1 = i + j by omega] at h2
          rw [h2]
          congr 1)
        hprev
  apply htop
  have := key (H - 1 - i) (by omega)
  rwa [show i + (H - 1 - i) = H - 1 by omega] at this

/-! ### Recognition at a copy -/

/-- **Recognition at a copy of a controller.**  Let `w` be lawful below a pair `Y` of the
replicated scheme, and `k` the copy at a mixed face `U` of a controller `u` of the tower at a grade
`N + 2 ≤ |U|`, below `Y`.  The controller stores a state `R` of the catalogue; the locality of `w`
at `k` reads, on the cells of the attachment inside `U`, a witness image `σ ∘ R` of it; and if `w`
is positive at `k` and at the copied top rung of the member of `R`, then `σ` sends no positive
value of `R` to `⊥`: the copied ladder makes every copied rung positive, and every positive value
of `R` is a value of its positive table. -/
theorem copy_recognition (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {Y : Finset (Fin (m + 2)) × ℕ} {w : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hw : (I.replicated g H Γ A B').rows.IsLawfulBelow Y fun d ↦ w d)
    (hU : U ∈ I.mixedFaces g) {N : ℕ} (hN : N + 1 ≤ m)
    {u : Fin (I.attachTower g H Γ A B').card}
    (hu : (I.attachTower g H Γ A B').toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), N + 2))
    (hNU : N + 2 ≤ #U)
    (hkY : copyAt H Γ A B' hU u (congrArg Prod.fst hu) ((congrArg Prod.snd hu).trans_le hNU) ∈
      (I.replicated g H Γ A B').toCellScheme.below Y) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A (N + 2), ∃ hR : (I.attachment g).rows.IsLawful R,
      ∃ (gg : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        (∀ c : Fin (I.attachment g).card, (I.attachment g).toCellScheme.scope c ⊆ U →
          (I.attachment g).toCellScheme.grade c ≤ N + 2 →
          min (w (I.attachEmb g H Γ A B' c))
              (w (copyAt H Γ A B' hU u (congrArg Prod.fst hu)
                ((congrArg Prod.snd hu).trans_le hNU))) =
            min (σ (R c)) (gg ((I.attachment g).toCellScheme.grade c))) ∧
        (w (copyAt H Γ A B' hU u (congrArg Prod.fst hu)
            ((congrArg Prod.snd hu).trans_le hNU)) ≠ ⊥ →
          w (copyLadder H Γ A B' hU (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR,
            Sum.inl ⟨H - 1, by omega⟩)) ≠ ⊥ →
          ∀ y, R y ≠ ⊥ → σ (R y) ≠ ⊥) := by
  set k := copyAt H Γ A B' hU u (congrArg Prod.fst hu) ((congrArg Prod.snd hu).trans_le hNU)
    with hkdef
  obtain ⟨R, hRC, hR, hrowA, hrowL⟩ :=
    Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
      (Γ := Γ) (B' := B') hcard N m hN u hu
  obtain ⟨gg, σ, hwit, hq⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 k hkY
  have hug : (I.attachTower g H Γ A B').toCellScheme.grade u = N + 2 := congrArg Prod.snd hu
  have hkg : (I.replicated g H Γ A B').toCellScheme.gradedIndex k = (U, N + 2) :=
    (gradedIndex_copyAt _ _ _ _).trans (Prod.ext rfl hug)
  -- the reading at the cells below the copy
  have hread (z : Fin (I.replicated g H Γ A B').card)
      (hz : z ∈ (I.replicated g H Γ A B').toCellScheme.below
        ((I.replicated g H Γ A B').toCellScheme.gradedIndex k)) :
      min (w z) (w k) = min (σ ((I.replicated g H Γ A B').rowAt k z))
        (gg ((I.replicated g H Γ A B').toCellScheme.grade z)) := by
    have h := hq ⟨z, hz⟩
    simp only at h
    rw [← Scheme.rowAt_of_mem hz] at h
    exact h
  set a := Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR with ha
  let p : ℕ → Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H := fun i ↦
    (a, Sum.inl ⟨min i (H - 1), by omega⟩)
  have hself (i : ℕ) (hi : i < H) :
      Scheme.baseIndex H (Scheme.rankProf (I.attachmentBase g).S H) a
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H (p i))) = i + 1 := by
    have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H) (p i)
    simp only [p, Scheme.ladderCeil, Sum.elim_inl] at h
    rw [h]
    omega
  let r : ℕ → Fin (I.replicated g H Γ A B').card := fun i ↦ copyLadder H Γ A B' hU (p i)
  have hrg (i : ℕ) : (I.replicated g H Γ A B').toCellScheme.gradedIndex (r i) = (U, 1) :=
    gradedIndex_copyLadder hU _
  have hrk (i : ℕ) : r i ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex k) := by
    rw [CellScheme.mem_below, hrg, hkg]
    exact ⟨subset_rfl, by omega⟩
  have hrY (i : ℕ) : r i ∈ (I.replicated g H Γ A B').toCellScheme.below Y :=
    CellScheme.Rows.mem_below_of_le (hrk i) hkY
  -- the copy reads the copied rungs as the positive table
  have hrung (i : ℕ) (hi : i < H) :
      (I.replicated g H Γ A B').rowAt k (r i) = posTable R (i + 1) := by
    refine (rowAt_copyAt_copyLadder hU _ _ (by rw [hug]; omega) _).trans ?_
    refine (hrowL (p i)).trans ?_
    rw [hself i hi]
  refine ⟨R, hRC, hR, gg, σ, hwit, fun c hcs hcg ↦ ?_, fun hk0 htop y hy ↦ ?_⟩
  · have hmem : I.attachEmb g H Γ A B' c ∈ (I.replicated g H Γ A B').toCellScheme.below
        ((I.replicated g H Γ A B').toCellScheme.gradedIndex k) := by
      rw [CellScheme.mem_below, gradedIndex_attachEmb, hkg]
      exact ⟨hcs, hcg⟩
    refine (hread _ hmem).trans ?_
    have hr1 : (I.replicated g H Γ A B').rowAt k (I.attachEmb g H Γ A B' c) = R c :=
      (rowAt_copyAt_attachEmb hU _ _ hcs (by rw [hug]; exact hcg)).trans (hrowA c hcg)
    have hg1 : (I.replicated g H Γ A B').toCellScheme.grade (I.attachEmb g H Γ A B' c) =
        (I.attachment g).toCellScheme.grade c := congrArg Prod.snd (gradedIndex_attachEmb c)
    rw [hr1, hg1]
  · -- every copied rung is positive
    have hpos : ∀ i < H, w (r i) ≠ ⊥ := by
      refine Scheme.rungs_ne_bot_of_top
        (isWellFormed_replicated (I := I) (g := g)).isWellFormed.grade_pos hw r
        (fun i _ ↦ hrg i) (fun i _ ↦ hrY i) (fun i hi ↦ ?_) (fun i hi hi0 ↦ ?_) ?_
      · refine (rowAt_copyLadder hU _ _).trans ?_
        rw [hself i hi]
        simp only [p, Scheme.ladderCeil, Sum.elim_inl]
        rw [show min i (H - 1) + 1 = i + 1 by omega]
      · refine (rowAt_copyLadder hU _ _).trans ?_
        rw [hself (i - 1) (by omega)]
        simp only [p, Scheme.ladderCeil, Sum.elim_inl]
        rw [show min i (H - 1) + 1 = i + 1 by omega, show i - 1 + 1 = i by omega]
      · have hp : p (H - 1) = (a, Sum.inl ⟨H - 1, by omega⟩) := by simp only [p, min_self]
        change w (copyLadder H Γ A B' hU (p (H - 1))) ≠ ⊥
        rw [hp]
        exact htop
    obtain ⟨-, -, hval⟩ := Scheme.LadderBaseData.ladderController_clauses hH hcard hR
    obtain ⟨i, hi, hiy⟩ := hval y hy
    rw [hiy]
    intro h0
    have h := hread _ (hrk i)
    rw [hrung i hi, h0, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h with h' | h'
    · exact hpos i hi h'
    · exact hk0 h'

/-- **No lift into a mixed face is solved by decoded writings in general**: as for the full faces
(`Seed.not_writingLift_univ`), the bottom prescription and ambient at the cap `⊤` ask for a decoded
writing that is `⊥` at the copied first rung of the member of the state, where the writing is
positive. -/
theorem not_writingLift_mixed (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hU : U ∈ I.mixedFaces g) {X : Finset (Fin (m + 2)) × ℕ} {j : ℕ} (hj : 1 ≤ j)
    (hXY : X ≤ (U, j)) : ¬ I.WritingLift g H Γ A B' X (U, j) hXY := by
  intro hw
  obtain ⟨R, hR, ν, -, hbot, -, hνq⟩ := hw ⊤ (isSelfVisible_top j) (fun _ ↦ ⊥) (fun _ ↦ ⊥)
    (CellScheme.Rows.isLawfulBelow_const_bot _) (CellScheme.Rows.isLawfulBelow_const_bot _)
    (fun _ ↦ rfl)
  have hRl : (I.attachment g).rows.IsLawful R := (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
  let pt : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H :=
    (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hRl, Sum.inl ⟨0, hH⟩)
  have hmem : copyLadder H Γ A B' hU pt ∈ (I.replicated g H Γ A B').toCellScheme.below (U, j) := by
    rw [CellScheme.mem_below, gradedIndex_copyLadder]
    exact ⟨subset_rfl, hj⟩
  have h := hνq ⟨_, hmem⟩
  simp only [min_top_right] at h
  apply ladderTower_v_rung_ne_bot (Γ := Γ) (A := A) (B' := B') hcard hH hRl
  apply hbot
  change ν (((I.attachmentBase g).ladderTower H Γ A B' m).v R
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (copyLadder H Γ A B' hU pt))) = ⊥ at h
  rw [copyLadder] at h
  erw [mirrorOrig_copyAt] at h
  exact h

/-! ### The copied top rung is positive wherever the ambient is positive -/

/-- **A copy carries the label of its original**, in every section lawful below a pair containing
the original (`Scheme.eq_of_mirrorOrig_eq`). -/
theorem eq_copyAt (hU : U ∈ I.mixedFaces g) {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hw : (I.replicated g H Γ A B').rows.IsLawfulBelow Y fun d ↦ w d)
    {f : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    (hfY : (Fin.castAdd _ f : Fin (I.replicated g H Γ A B').card) ∈
      (I.replicated g H Γ A B').toCellScheme.below Y) :
    w (copyAt H Γ A B' hU f hf hfg) = w (Fin.castAdd _ f) := by
  refine Scheme.eq_of_mirrorOrig_eq hw ?_ ?_ hfY
  · rw [mirrorOrig_copyAt, Scheme.mirrorOrig_castAdd]
  · exact subset_trans (subset_univ _) (le_of_eq ((congrArg Prod.fst
      (Scheme.gradedIndex_mirror_castAdd (hmix := I.not_subset_scope_tower g H Γ A B') f)).trans
        hf).symm)

/-- **Positivity of the copied top rung from the ambient.**  Let `q` be lawful below the full face
at a grade `j`, and `x` a cell of the attachment of grade `N`, `2 ≤ N ≤ j`, `N ≤ m + 1`, with
`q` positive at `x`.  Then some cell of full scope at the grade `N` (a controller, of state `R`)
carries at least the label of `x`, and `q` is positive at the top rung of the member of `R` and at
each of its copies: the controller reads the top rung at least as high as `x`
(`Scheme.LadderBaseData.ladderController_clauses`), and the copies carry the label of the rung
(`Seed.eq_copyAt`).  This holds wherever `x` lies, in particular when its scope contains the point
`m`, outside the mixed coatom. -/
theorem exists_copiedTopRung_ne_bot (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty) {j N : ℕ}
    (hN2 : 2 ≤ N) (hNj : N ≤ j) (hNm : N ≤ m + 1)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ q d)
    {x : Fin (I.attachment g).card} (hxN : (I.attachment g).toCellScheme.grade x = N)
    (hx0 : q (I.attachEmb g H Γ A B' x) ≠ ⊥) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A N, ∃ hR : (I.attachment g).rows.IsLawful R,
      q (Fin.castAdd _ (ladCell H Γ A B'
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR, Sum.inl ⟨H - 1, by omega⟩)))
        ≠ ⊥ ∧
      ∀ (V : Finset (Fin (m + 2))) (hV : V ∈ I.mixedFaces g),
        q (copyLadder H Γ A B' hV (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR,
          Sum.inl ⟨H - 1, by omega⟩)) ≠ ⊥ := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  -- a cell of full scope at the grade `N`
  obtain ⟨f, hf⟩ := (I.attachmentBase g).exists_gradedIndex_univ_ladderTower (B' := B') hH hne m N
    (by omega) (by omega)
  have hfE : (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ f) =
      ((univ : Finset (Fin (m + 2))), N) := (Scheme.gradedIndex_mirror_castAdd _).trans hf
  have hfY : (Fin.castAdd _ f : Fin (I.replicated g H Γ A B').card) ∈
      (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hfE]
    exact ⟨subset_rfl, hNj⟩
  have hxg : (I.replicated g H Γ A B').toCellScheme.grade (I.attachEmb g H Γ A B' x) = N :=
    (congrArg Prod.snd (gradedIndex_attachEmb x)).trans hxN
  -- availability above `x`
  obtain ⟨u', hu', hxu⟩ := havail (I.attachEmb g H Γ A B' x) _ hfY
    (subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst hfE).symm))
    (hxg.trans (congrArg Prod.snd hfE).symm)
  have hu'E : (I.replicated g H Γ A B').toCellScheme.gradedIndex u' =
      ((univ : Finset (Fin (m + 2))), N) := hu'.trans hfE
  have hu'Y : u' ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) := CellScheme.Rows.mem_below_of_le (le_of_eq hu') hfY
  obtain ⟨u, rfl⟩ : ∃ u : Fin (I.attachTower g H Γ A B').card, u' = Fin.castAdd _ u := by
    induction u' using Fin.addCases with
    | left u => exact ⟨u, rfl⟩
    | right jj =>
      exfalso
      exact ((I.mem_mixedFaces g).mp (scope_replicated_natAdd jj)).2.1 (congrArg Prod.fst hu'E)
  have hu : (I.attachTower g H Γ A B').toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), N - 2 + 2) := by
    rw [show N - 2 + 2 = N by omega]
    exact (Scheme.gradedIndex_mirror_castAdd u).symm.trans hu'E
  obtain ⟨R, hRC, hR, hrowA, hrowL⟩ :=
    Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
      (Γ := Γ) (B' := B') hcard (N - 2) m (by omega) u hu
  obtain ⟨-, htop, -⟩ := Scheme.LadderBaseData.ladderController_clauses hH hcard hR
  set a := Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR with ha
  set pt : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H :=
    (a, Sum.inl ⟨H - 1, by omega⟩) with hpt
  -- the reading of the controller
  obtain ⟨gg, σ, hwit, hqu⟩ := hloc _ hu'Y
  have hugE : (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ u) =
      ((univ : Finset (Fin (m + 2))), N) := hu'E
  have hxm : I.attachEmb g H Γ A B' x ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ u)) := by
    rw [CellScheme.mem_below, hugE, gradedIndex_attachEmb]
    exact ⟨subset_univ _, hxN.le⟩
  have hgl : (I.replicated g H Γ A B').toCellScheme.gradedIndex
      (Fin.castAdd _ (ladCell H Γ A B' pt)) = ((univ : Finset (Fin (m + 2))), 1) :=
    (Scheme.gradedIndex_mirror_castAdd _).trans (gradedIndex_ladCell pt)
  have hlm : (Fin.castAdd _ (ladCell H Γ A B' pt) : Fin (I.replicated g H Γ A B').card) ∈
      (I.replicated g H Γ A B').toCellScheme.below
        ((I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ u)) := by
    rw [CellScheme.mem_below, hugE, hgl]
    exact ⟨subset_rfl, by omega⟩
  have ex := hqu ⟨_, hxm⟩
  have el := hqu ⟨_, hlm⟩
  simp only at ex el
  rw [← Scheme.rowAt_of_mem hxm, hxg] at ex
  have hgl1 : (I.replicated g H Γ A B').toCellScheme.grade
      (Fin.castAdd _ (ladCell H Γ A B' pt)) = 1 := congrArg Prod.snd hgl
  rw [← Scheme.rowAt_of_mem hlm, hgl1] at el
  have hrx : (I.replicated g H Γ A B').rowAt (Fin.castAdd _ u) (I.attachEmb g H Γ A B' x) = R x :=
    (Scheme.rowAt_mirror_castAdd _ _).trans
      (hrowA x (show (I.attachment g).toCellScheme.grade x ≤ N - 2 + 2 by omega))
  have hrl : (I.replicated g H Γ A B').rowAt (Fin.castAdd _ u)
      (Fin.castAdd _ (ladCell H Γ A B' pt)) = posTable R H := by
    refine (Scheme.rowAt_mirror_castAdd _ _).trans ((hrowL pt).trans ?_)
    have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H) pt
    simp only [hpt, Scheme.ladderCeil, Sum.elim_inl] at h
    rw [h, show H - 1 + 1 = H by omega]
  rw [hrx, min_eq_left hxu] at ex
  rw [hrl] at el
  -- the top rung is positive
  have htop0 : q (Fin.castAdd _ (ladCell H Γ A B' pt)) ≠ ⊥ := by
    intro h0
    have h1 : q (I.attachEmb g H Γ A B' x) ≤ min (q (Fin.castAdd _ (ladCell H Γ A B' pt)))
        (q (Fin.castAdd _ u)) := by
      rw [el, ex]
      exact min_le_min (hwit.monotone (htop x)) (hwit.antitone (by omega))
    rw [h0, min_eq_left bot_le, le_bot_iff] at h1
    exact hx0 h1
  have hlY : (Fin.castAdd _ (ladCell H Γ A B' pt) : Fin (I.replicated g H Γ A B').card) ∈
      (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hgl]
    exact ⟨subset_rfl, by omega⟩
  refine ⟨R, ?_, hR, htop0, fun V hV ↦ ?_⟩
  · have hm := Scheme.LadderBaseData.mem_towerCat.mp hRC
    rw [show N - 2 + 2 = N by omega] at hm
    exact Scheme.LadderBaseData.mem_towerCat.mpr hm
  · have e := eq_copyAt (H := H) (Γ := Γ) (A := A) (B' := B') hV hq
      (f := ladCell H Γ A B' pt) (congrArg Prod.fst (gradedIndex_ladCell pt))
      ((grade_ladCell pt).trans_le (one_le_card_of_mem_mixedFaces hV)) hlY
    intro h0
    apply htop0
    rw [← e]
    exact h0

/-! ### The shape of the copied ladder -/

/-- **The copied ladder is lawful on the ladder table**: a section lawful below a pair above
`(U, 1)`, read on the copied ladder points at the mixed face `U`, is self-visible at `1` and local
at every copied ladder point for the ladder row (`Label.LadderLawful`): the copies at `U` read one
another with the rows of the ladder (`Seed.rowAt_copyLadder`). -/
theorem ladderLawful_copyLadder (hU : U ∈ I.mixedFaces g) {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hw : (I.replicated g H Γ A B').rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    LadderLawful H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
      (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
      fun p ↦ w (copyLadder H Γ A B' hU p) := by
  obtain ⟨hord, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hg1 (p : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      (I.replicated g H Γ A B').toCellScheme.grade (copyLadder H Γ A B' hU p) = 1 :=
    congrArg Prod.snd (gradedIndex_copyLadder hU p)
  have hmY (p : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      copyLadder H Γ A B' hU p ∈ (I.replicated g H Γ A B').toCellScheme.below Y := by
    rw [CellScheme.mem_below, gradedIndex_copyLadder]
    exact hUY
  refine ⟨fun p ↦ ?_, fun c ↦ ?_⟩
  · have h := hord _ (hmY p)
    rwa [hg1] at h
  · have hb (p : Scheme.LadderPt (I.attachmentBase g).S
        (Scheme.RankMember (I.attachmentBase g).S H) H) :
        copyLadder H Γ A B' hU p ∈ (I.replicated g H Γ A B').toCellScheme.below
          ((I.replicated g H Γ A B').toCellScheme.gradedIndex (copyLadder H Γ A B' hU c)) := by
      rw [CellScheme.mem_below, gradedIndex_copyLadder, gradedIndex_copyLadder]
    have h := (hloc _ (hmY c)).reindex fun p ↦ (⟨_, hb p⟩ :
      (I.replicated g H Γ A B').toCellScheme.below
        ((I.replicated g H Γ A B').toCellScheme.gradedIndex (copyLadder H Γ A B' hU c)))
    convert h using 1
    · funext p
      exact (hg1 p).symm
    · funext p
      simp only [Function.comp_apply]
      rw [← Scheme.rowAt_of_mem (hb p), rowAt_copyLadder, Scheme.baseIndex_natAdd,
        Equiv.symm_apply_apply]
      rfl
    · rfl

/-- **The shape of the copied ladder** at a mixed face: a section lawful below a pair above
`(U, 1)` is `⊥` at every copied ladder point at `U`, or there, for the member `a` with the largest
copied top rung, the chart image of the table of `a`, `⊥` exactly at its index `0`
(`Label.LadderLawful.exists_shape`).  In particular the copied shadows of `a` read the ranks of
`a` at every cell of the attachment, inside `U` or not. -/
theorem copyLadder_exists_shape (hH : 0 < H) (hU : U ∈ I.mixedFaces g)
    {Y : Finset (Fin (m + 2)) × ℕ} {w : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hw : (I.replicated g H Γ A B').rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    (∀ p, w (copyLadder H Γ A B' hU p) = ⊥) ∨
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (gg : ℕ → Label.{u})
        (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        (∀ p, w (copyLadder H Γ A B' hU p) = min (σ (ladderSource H
          (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p))) (gg 1)) ∧
        ∀ p, w (copyLadder H Γ A B' hU p) = ⊥ ↔
          ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p = 0 :=
  (ladderLawful_copyLadder hU hw hUY).exists_shape hH
    (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
    (fun a i ↦ (a, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ _ ↦ rfl)
    fun _ i hi ↦ by simp only [Scheme.ladderCeil, Sum.elim_inl]; omega

end Seed

end VaughtConjecture

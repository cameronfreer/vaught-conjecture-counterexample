/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedLiftUniv

/-!
# The lift from a mixed face into the full face at every grade

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

**The lift** (`Seed.cappedLift_mixed_univ`).  For a mixed face `U` and a grade `j` with
`1 ≤ j ≤ m + 1` and `j ≤ |U|`, the replicated scheme lifts capped from `(U, j)` into
`(univ, j)`.  Given a prescription `P` lawful below `(U, j)`, pick at every grade `k ≤ j` a cell
`u k` of full scope whose copy at `U` carries the largest label among the copies at its grade (at
the grade one, the top rung of the member of the shape of the copied ladder), and a capped decoder
`θ k` of `P` at that copy.  The lift reads every cell `d` through the cell of its grade:
`r d = θ k (row of u k at d)`.

* At the cells of full scope and their copies it is the prescription at the copy at `U`; below
  `(U, j)` it is the prescription (`Seed.le_max_copy`).
* It is lawful: at a cell of full scope, with the decoder at its copy as witness, by the readings of
  the cells of the attachment through the dominating cells (`Seed.min_decode_eq_decode`,
  `Seed.min_decode_eq_decode_one`); at a cell of the attachment, through the decoded row of the
  dominating cell of its grade, whose bottom pattern is all or exactly that of the row
  (`Seed.decode_controller_dichotomy`, `Seed.decode_one_dichotomy`).
* It keeps the ambient at the cap (`Label.min_min_eq_of_reader`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

variable (H Γ A B') in
open Classical in
/-- The copy at `U` of a cell of the tower of full scope and grade at most `|U|`; the cell itself
otherwise. -/
noncomputable def cpy (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) : Fin (𝔼).card :=
  if h : (𝕋).toCellScheme.scope v = univ ∧ (𝕋).toCellScheme.grade v ≤ #U then
    copyAt H Γ A B' hU v h.1 h.2 else Fin.castAdd _ v

theorem cpy_eq (hU : U ∈ I.mixedFaces g) {v : Fin (𝕋).card} {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    cpy H Γ A B' hU v = copyFull H Γ A B' hU v hv hk := by
  classical
  unfold cpy
  rw [dite_eq_left ⟨congrArg Prod.fst hv, (congrArg Prod.snd hv).trans_le hk⟩]
  rfl

/-- **The lift from a mixed face into the full face.**  For a mixed face `U` and a grade `j` with
`1 ≤ j ≤ m + 1` and `j ≤ |U|`, the replicated scheme lifts capped from `(U, j)` to `(univ, j)`. -/
theorem cappedLift_mixed_univ (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hU : U ∈ I.mixedFaces g) {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j ≤ m + 1) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  have hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty := fun _ ↦
    ⟨fun _ ↦ ⊥, Scheme.LadderBaseData.mem_towerCat.mpr
      ⟨fun _ ↦ hΓ0, CellScheme.Rows.isLawful_const_bot, hA0 _⟩⟩
  have hXY : ((U, j) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), j) :=
    ⟨subset_univ _, le_rfl⟩
  have hU1 : 1 ≤ #U := hj1.trans hjU
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  -- total labellings
  obtain ⟨P, hPd⟩ : ∃ P : Fin (𝔼).card → Label.{u},
      ∀ d (hd : d ∈ (𝔼).toCellScheme.below (U, j)), P d = p ⟨d, hd⟩ :=
    ⟨CellScheme.Rows.extendBot _ p, fun d hd ↦ CellScheme.Rows.extendBot_of_mem p hd⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Fin (𝔼).card → Label.{u},
      ∀ d (hd : d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j)),
        Q d = q ⟨d, hd⟩ :=
    ⟨CellScheme.Rows.extendBot _ q, fun d hd ↦ CellScheme.Rows.extendBot_of_mem q hd⟩
  have hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d := by
    have e : (fun d : (𝔼).toCellScheme.below (U, j) ↦ P d) = p := funext fun d ↦ hPd d d.2
    rw [e]; exact hp
  have hQ : (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun d ↦ Q d := by
    have e : (fun d : (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) ↦ Q d) = q :=
      funext fun d ↦ hQd d d.2
    rw [e]; exact hq
  have hpq' (d) (hd : d ∈ (𝔼).toCellScheme.below (U, j)) : min (Q d) c = min (P d) c := by
    rw [hQd d (le_trans hd hXY), hPd d hd]
    exact hpq ⟨d, hd⟩
  -- the member of the copied ladder
  obtain ⟨a, ha⟩ : ∃ a : Scheme.RankMember (I.attachmentBase g).S H, ∀ v,
      P (copyLadder H Γ A B' hU v) ≤ P (copyLadder H Γ A B' hU (a, Sum.inl ⟨H - 1, by omega⟩)) := by
    rcases copyLadder_exists_shape hH hU hP (show (U, 1) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
      hall | ⟨a, gg, σ, hwit, hch, -⟩
    · obtain ⟨a0⟩ := (inferInstance : Nonempty (Scheme.RankMember (I.attachmentBase g).S H))
      exact ⟨a0, fun v ↦ by rw [hall v]; exact bot_le⟩
    · refine ⟨a, fun v ↦ ?_⟩
      rw [hch v, hch _]
      refine min_le_min_right _ (hwit.monotone (monotone_ladderSource H ?_))
      have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
        ((a, Sum.inl ⟨H - 1, by omega⟩) : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H)
      change _ ≤ ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
        (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a
        (a, Sum.inl ⟨H - 1, by omega⟩)
      rw [h]
      change _ ≤ H - 1 + 1
      have := ladderIndex_le (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (ceil := Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
        a v
      omega
  set top : Scheme.LadderPt (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  -- the dominating cells
  have hexu : ∀ k : ℕ, ∃ u₀ : Fin (𝕋).card, 1 ≤ k → k ≤ j →
      (𝕋).toCellScheme.gradedIndex u₀ = ((univ : Finset (Fin (m + 2))), k) ∧
      (k = 1 → u₀ = ladCell H Γ A B' top) ∧
      ∀ w, (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k) →
        P (cpy H Γ A B' hU w) ≤ P (cpy H Γ A B' hU u₀) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ j
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        refine ⟨ladCell H Γ A B' top, fun _ _ ↦ ⟨gradedIndex_ladCell top, fun _ ↦ rfl,
          fun w hw ↦ ?_⟩⟩
        rcases tower_grade_one_cases w (congrArg Prod.snd hw) with ⟨v, rfl⟩ | ⟨e, -, rfl⟩
        · rw [cpy_eq hU (gradedIndex_ladCell v) hU1, cpy_eq hU (gradedIndex_ladCell top) hU1]
          exact ha v
        · exfalso
          exact (I.attachmentBase g).scope_ne_univ e
            ((congrArg Prod.fst (Scheme.LadderBaseData.gradedIndex_baseCellEmb (H := H)
              (Γ := Γ) (A := A) (B' := B') m e)).symm.trans (congrArg Prod.fst hw))
      · obtain ⟨f0, hf0⟩ := (I.attachmentBase g).exists_gradedIndex_univ_ladderTower
          (B' := B') hH hne m k (by omega) (by omega)
        obtain ⟨u₀, hu₀, hmax⟩ := (univ.filter fun w : Fin (𝕋).card ↦
            (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)).exists_max_image
          (fun w ↦ P (cpy H Γ A B' hU w)) ⟨f0, by simp [hf0]⟩
        rw [mem_filter] at hu₀
        exact ⟨u₀, fun _ _ ↦ ⟨hu₀.2, fun h ↦ absurd h (by omega),
          fun w hw ↦ hmax w (by simp [hw])⟩⟩
    · exact ⟨ladCell H Γ A B' top, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hk⟩
  choose u hu using hexu
  -- the decoders at their copies
  have hexθ : ∀ k : ℕ, ∃ θ : Label.{u} → Label.{u}, 1 ≤ k → k ≤ j →
      IsWitness (stepSuppressor k) θ ∧ (∀ x, θ x ≤ P (cpy H Γ A B' hU (u k))) ∧
      ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (cpy H Γ A B' hU (u k))),
        θ ((𝔼).rowAt (cpy H Γ A B' hU (u k)) d) = min (P d) (P (cpy H Γ A B' hU (u k))) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ j
    · have hcu := cpy_eq hU (hu k hk.1 hk.2).1 (hk.2.trans hjU)
      have hmem : cpy H Γ A B' hU (u k) ∈ (𝔼).toCellScheme.below (U, j) := by
        rw [hcu, CellScheme.mem_below, gradedIndex_copyFull]; exact ⟨subset_rfl, hk.2⟩
      have hgr : (𝔼).toCellScheme.grade (cpy H Γ A B' hU (u k)) = k := by
        rw [hcu]; exact congrArg Prod.snd (gradedIndex_copyFull hU _ _ _)
      obtain ⟨θ, hθw, hθle, hθr⟩ := Scheme.exists_cappedDecoder_below hP hmem hgr
      exact ⟨θ, fun _ _ ↦ ⟨hθw, hθle, hθr⟩⟩
    · exact ⟨id, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hk⟩
  choose θ hθ using hexθ
  -- the lift
  set r : Fin (𝔼).card → Label.{u} := fun d ↦ θ ((𝔼).toCellScheme.grade d)
    ((𝔼).rowAt (Fin.castAdd _ (u ((𝔼).toCellScheme.grade d))) d) with hr
  have hrdef (d) : r d = θ ((𝔼).toCellScheme.grade d)
      ((𝔼).rowAt (Fin.castAdd _ (u ((𝔼).toCellScheme.grade d))) d) := rfl
  have hgY (d) (hd : d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j)) :
      1 ≤ (𝔼).toCellScheme.grade d ∧ (𝔼).toCellScheme.grade d ≤ j :=
    ⟨(isWellFormed_replicated (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
      (B' := B')).isWellFormed.grade_pos d, hd.2⟩
  have hgiu (k) (h1 : 1 ≤ k) (h2 : k ≤ j) :
      (𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (u k)) =
        ((univ : Finset (Fin (m + 2))), k) :=
    (Scheme.gradedIndex_mirror_castAdd _).trans (hu k h1 h2).1
  have hθc (k) (h1 : 1 ≤ k) (h2 : k ≤ j) : ∀ d ∈ (𝔼).toCellScheme.below
      ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU (u k) (hu k h1 h2).1 (h2.trans hjU))),
      θ k ((𝔼).rowAt (copyFull H Γ A B' hU (u k) (hu k h1 h2).1 (h2.trans hjU)) d) =
        min (P d) (P (copyFull H Γ A B' hU (u k) (hu k h1 h2).1 (h2.trans hjU))) := by
    rw [← cpy_eq hU (hu k h1 h2).1 (h2.trans hjU)]
    exact (hθ k h1 h2).2.2
  have hθcle (k) (h1 : 1 ≤ k) (h2 : k ≤ j) (x) :
      θ k x ≤ P (copyFull H Γ A B' hU (u k) (hu k h1 h2).1 (h2.trans hjU)) := by
    rw [← cpy_eq hU (hu k h1 h2).1 (h2.trans hjU)]
    exact (hθ k h1 h2).2.1 x
  have hmaxc (k) (h1 : 1 ≤ k) (h2 : k ≤ j) (w)
      (hw : (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)) :
      P (copyFull H Γ A B' hU w hw (h2.trans hjU)) ≤
        P (copyFull H Γ A B' hU (u k) (hu k h1 h2).1 (h2.trans hjU)) := by
    rw [← cpy_eq hU hw (h2.trans hjU), ← cpy_eq hU (hu k h1 h2).1 (h2.trans hjU)]
    exact (hu k h1 h2).2.2 w hw
  -- the values of the lift
  have hr_full (d) (hd : d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j))
      (v : Fin (𝕋).card) (hv : (𝕋).mirrorOrig (I.mixedFaces g) d = v) (k : ℕ)
      (hk : (𝔼).toCellScheme.grade d = k)
      (hgv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) :
      r d = P (cpy H Γ A B' hU v) := by
    obtain ⟨h1, h2⟩ := hk ▸ hgY d hd
    have hdu : d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (u k))) := by
      rw [hgiu k h1 h2, CellScheme.mem_below]
      exact ⟨subset_univ _, hk.le⟩
    rw [hrdef, hk, Scheme.rowAt_mirror_of_mem hdu, Scheme.mirrorOrig_castAdd, hv,
      decode_copyFull hU (hu k h1 h2).1 (h2.trans hjU) (hθc k h1 h2) hgv le_rfl,
      cpy_eq hU hgv (h2.trans hjU)]
    exact min_eq_left (hmaxc k h1 h2 v hgv)
  have hr_att (e : Fin (I.attachment g).card) (k : ℕ)
      (hk : (I.attachment g).toCellScheme.grade e = k) :
      r (I.attachEmb g H Γ A B' e) =
        θ k ((𝕋).rowAt (u k) ((I.attachmentBase g).baseCellEmb m e)) := by
    have hg : (𝔼).toCellScheme.grade (I.attachEmb g H Γ A B' e) = k :=
      (congrArg Prod.snd (gradedIndex_attachEmb e)).trans hk
    rw [hrdef, hg]
    exact congrArg (θ k) (Scheme.rowAt_mirror_castAdd _ _)
  -- copies and originals carry the same label
  have hsame (W : Fin (𝔼).card → Label.{u})
      (hW : (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun d ↦ W d)
      (v : Fin (𝕋).card) (k : ℕ)
      (hgv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hkj : k ≤ j)
      (z : Fin (𝔼).card) (hz : (𝕋).mirrorOrig (I.mixedFaces g) z = v) :
      W z = W (Fin.castAdd _ v) := by
    have hcY : (Fin.castAdd _ v : Fin (𝔼).card) ∈
        (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
      rw [CellScheme.mem_below, Scheme.gradedIndex_mirror_castAdd, hgv]
      exact ⟨subset_rfl, hkj⟩
    refine Scheme.eq_of_mirrorOrig_eq hW (by rw [hz, Scheme.mirrorOrig_castAdd]) ?_ hcY
    exact subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst
      ((Scheme.gradedIndex_mirror_castAdd (hmix := I.not_subset_scope_tower g H Γ A B') v).trans
        hgv)).symm)
  have hcfY (v : Fin (𝕋).card) (k : ℕ)
      (hgv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hkj : k ≤ j) :
      cpy H Γ A B' hU v ∈ (𝔼).toCellScheme.below (U, j) := by
    rw [cpy_eq hU hgv (hkj.trans hjU), CellScheme.mem_below, gradedIndex_copyFull]
    exact ⟨subset_rfl, hkj⟩
  have hcfo (v : Fin (𝕋).card) (k : ℕ)
      (hgv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hkj : k ≤ j) :
      (𝕋).mirrorOrig (I.mixedFaces g) (cpy H Γ A B' hU v) = v := by
    rw [cpy_eq hU hgv (hkj.trans hjU), mirrorOrig_copyFull]
  -- the rows of the dominating cells
  have hρ (k) (h1 : 1 ≤ k) (h2 : k ≤ j) :
      (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
        fun e ↦ (𝔼).rowAt (Fin.castAdd _ (u k)) e.1 :=
    Scheme.isLawfulBelow_rowAt (isConsistent_replicated hH hcard hΓ hA) (hgiu k h1 h2)
  have hbelowk (d) : d ∈ (𝔼).toCellScheme.below
      ((univ : Finset (Fin (m + 2))), (𝔼).toCellScheme.grade d) :=
    ⟨subset_univ _, le_rfl⟩
  -- the decoder at the top rung
  have hu1 : u 1 = ladCell H Γ A B' top := (hu 1 le_rfl hj1).2.1 rfl
  have hmaxl (K : ℕ) (hK1 : 1 ≤ K) (hKU : K ≤ #U) (v) :
      P (copyFull H Γ A B' hU (ladCell H Γ A B' v) (gradedIndex_ladCell v) (hK1.trans hKU)) ≤
        P (copyFull H Γ A B' hU (ladCell H Γ A B' top) (gradedIndex_ladCell _)
          (hK1.trans hKU)) := ha v
  have hθ1 : ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex
      (copyFull H Γ A B' hU (ladCell H Γ A B' top) (gradedIndex_ladCell _) hU1)),
      θ 1 ((𝔼).rowAt (copyFull H Γ A B' hU (ladCell H Γ A B' top) (gradedIndex_ladCell _) hU1)
        d) = min (P d) (P (copyFull H Γ A B' hU (ladCell H Γ A B' top)
          (gradedIndex_ladCell _) hU1)) := by
    rw [← cpy_eq hU (gradedIndex_ladCell top) hU1, ← hu1]
    exact (hθ 1 le_rfl hj1).2.2
  -- the reading of a cell of the attachment through the dominating cell of its grade, capped at
  -- a cell of full scope, is the reading by that cell
  have hSC (K : ℕ) (hK1 : 1 ≤ K) (hKj : K ≤ j) (f : Fin (𝕋).card)
      (hgf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
      {θf : Label.{u} → Label.{u}} (hθf_mono : Monotone θf)
      (hθf_le : ∀ x, θf x ≤ P (copyFull H Γ A B' hU f hgf (hKj.trans hjU)))
      (hθf : ∀ d ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU f hgf (hKj.trans hjU))),
        θf ((𝔼).rowAt (copyFull H Γ A B' hU f hgf (hKj.trans hjU)) d) =
          min (P d) (P (copyFull H Γ A B' hU f hgf (hKj.trans hjU))))
      (e : Fin (I.attachment g).card) (k : ℕ) (hek : (I.attachment g).toCellScheme.grade e = k)
      (hkK : k ≤ K) :
      min (θ k ((𝕋).rowAt (u k) ((I.attachmentBase g).baseCellEmb m e)))
        (P (copyFull H Γ A B' hU f hgf (hKj.trans hjU))) =
        θf ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e)) := by
    have hk1 : 1 ≤ k := hek ▸ (I.isWellFormed_attachment g).isWellFormed.grade_pos e
    rcases Nat.lt_or_ge k 2 with hk | hk2
    · have hk' : k = 1 := by omega
      subst hk'
      rw [hu1]
      exact min_decode_eq_decode_one hU hcard hH hK1 (hKj.trans hjm) (hKj.trans hjU) hgf a
        (hmaxl K hK1 (hKj.trans hjU)) hθf_mono hθf_le hθf hθ1 hek
    · exact min_decode_eq_decode hU hcard hΓ hA hk2 hkK (hKj.trans hjm) (hKj.trans hjU) hgf
        (hu k hk1 (hkK.trans hKj)).1 (hmaxc k hk1 (hkK.trans hKj)) hθf_mono hθf_le hθf
        (hθc k hk1 (hkK.trans hKj)) hek
  refine ⟨fun d ↦ r d, ?_, fun d ↦ ?_, fun d ↦ ?_⟩
  · refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_,
      fun s t ht hst hg ↦ ?_⟩
    · -- order
      obtain ⟨h1, h2⟩ := hgY d hd
      have hvis := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ _ h1 h2)).1 d (hbelowk d)
      rw [hrdef]
      exact (hθ _ h1 h2).1.isSelfVisible_apply hvis (by simp)
    · -- locality
      obtain ⟨h1, h2⟩ := hgY s hs
      set K := (𝔼).toCellScheme.grade s with hKdef
      have hbs (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
          d.1 ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) :=
        CellScheme.Rows.mem_below_of_le d.2 hs
      have hdK (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
          (𝔼).toCellScheme.grade d.1 ≤ K := d.2.2
      rcases cell_cases s with ⟨f, hf, hgf⟩ | ⟨es, hes⟩
      · -- a cell of full scope or a copy: the decoder at the copy at `U` is the witness
        have hcf := cpy_eq hU hgf (h2.trans hjU)
        obtain ⟨θf, hθfw, hθfle, hθfr⟩ := Scheme.exists_cappedDecoder_below hP (hcfY f K hgf h2)
          (show (𝔼).toCellScheme.grade (cpy H Γ A B' hU f) = K by
            rw [hcf]; exact congrArg Prod.snd (gradedIndex_copyFull hU _ _ _))
        rw [hcf] at hθfle hθfr
        have hrs : r s = P (copyFull H Γ A B' hU f hgf (h2.trans hjU)) := by
          rw [hr_full s hs f hf K rfl hgf, hcf]
        refine ⟨stepSuppressor K, θf, hθfw, fun d ↦ ?_⟩
        change min (r d.1) (r s) = min (θf ((𝔼).rows.row s d)) (stepSuppressor K
          ((𝔼).toCellScheme.grade d.1))
        rw [stepSuppressor_of_le (hdK d), min_top_right, ← Scheme.rowAt_of_mem d.2,
          Scheme.rowAt_mirror_of_mem d.2, hf, hrs]
        obtain ⟨h1d, h2d⟩ := hgY d.1 (hbs d)
        rcases cell_cases d.1 with ⟨v, hv, hgv⟩ | ⟨e, he⟩
        · rw [hv, hr_full d.1 (hbs d) v hv _ rfl hgv,
            decode_copyFull hU hgf (h2.trans hjU) hθfr hgv (hdK d)]
          exact congrArg₂ min (congrArg P (cpy_eq hU hgv _)) rfl
        · have hek : (I.attachment g).toCellScheme.grade e = (𝔼).toCellScheme.grade d.1 := by
            rw [he]; exact (congrArg Prod.snd (gradedIndex_attachEmb e)).symm
          rw [he, hr_att e _ hek]
          change _ = θf ((𝕋).rowAt f ((𝕋).mirrorOrig (I.mixedFaces g)
            (Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m e))))
          rw [Scheme.mirrorOrig_castAdd]
          exact hSC K h1 h2 f hgf hθfw.monotone hθfle hθfr e _ hek (hek ▸ hdK d)
      · -- a cell of the attachment: through the decoded row of the dominating cell
        have hsc : (𝔼).toCellScheme.scope s ⊆
            univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
            (𝔼).toCellScheme.scope s ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
          rw [hes, scope_attachEmb]
          exact I.scope_attachment g es
        have hds (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
            ∃ e, d.1 = I.attachEmb g H Γ A B' e ∧ (I.attachment g).toCellScheme.grade e ≤ K := by
          obtain ⟨e, he⟩ := mem_range_attachEmb d.1
            (hsc.imp (fun h ↦ d.2.1.trans h) fun h ↦ d.2.1.trans h)
          refine ⟨e, he.symm, ?_⟩
          have := hdK d
          rw [← he] at this
          exact (congrArg Prod.snd (gradedIndex_attachEmb e)).symm.trans_le this
        have hρd (e : Fin (I.attachment g).card) :
            (𝔼).rowAt (Fin.castAdd _ (u K)) (I.attachEmb g H Γ A B' e) =
              (𝕋).rowAt (u K) ((I.attachmentBase g).baseCellEmb m e) :=
          Scheme.rowAt_mirror_castAdd _ _
        have hrs : r s = θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) s) := hrdef s
        -- the lift below `s` is the decoded row of the dominating cell
        have hclaim (d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s)) :
            min (r d.1) (r s) = min (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) d.1))
              (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) s)) := by
          obtain ⟨e, he, hek⟩ := hds d
          rw [← hrs, he, hr_att e _ rfl, hρd e]
          have h := hSC K h1 h2 (u K) (hu K h1 h2).1 (hθ K h1 h2).1.monotone (hθcle K h1 h2)
            (hθc K h1 h2) e _ rfl hek
          have hrsle : r s ≤ P (copyFull H Γ A B' hU (u K) (hu K h1 h2).1 (h2.trans hjU)) := by
            rw [hrs]; exact hθcle K h1 h2 _
          rw [← h, min_assoc, min_eq_right hrsle]
        have hlocρ := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ K h1 h2)).2.1 s
          (hbelowk s)
        have hvisρ := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ K h1 h2)).1 s
          (hbelowk s)
        have hfun : (fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
            min (r d.1) (r s)) = fun d ↦ min (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) d.1))
              (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) s)) := funext hclaim
        change TransformsTo (fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
          (𝔼).toCellScheme.grade d.1) ((𝔼).rows.row s) fun d ↦ min (r d.1) (r s)
        rw [hfun]
        -- the bottom pattern of the decoded row
        have hdich : (∀ d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s),
              θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) d.1) = ⊥) ∨
            ∀ d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s),
              (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) d.1) = ⊥ ↔
                (𝔼).rowAt (Fin.castAdd _ (u K)) d.1 = ⊥) := by
          rcases Nat.lt_or_ge K 2 with hK | hK2
          · have hK1 : K = 1 := by omega
            have huK : u K = ladCell H Γ A B' top := by rw [hK1, hu1]
            have hθK : θ K = θ 1 := by rw [hK1]
            have he1 (e : Fin (I.attachment g).card)
                (hek : (I.attachment g).toCellScheme.grade e ≤ K) :
                (I.attachment g).toCellScheme.grade e = 1 :=
              le_antisymm (hK1 ▸ hek) ((I.isWellFormed_attachment g).isWellFormed.grade_pos e)
            rcases decode_one_dichotomy hU hH hP hj1 hU1 a ha hθ1 with hall | hiff
            · left
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd, huK, hθK]
              exact hall e (he1 e hek)
            · right
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd, huK, hθK]
              exact hiff e (he1 e hek)
          · rcases decode_controller_dichotomy hU hH hcard hP hj1 hK2 (h2.trans hjm) (h2.trans hjU)
                (hu K h1 h2).1 (hθ K h1 h2).1.map_bot (hθc K h1 h2) with hall | hiff
            · left
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd]
              exact hall e hek
            · right
              intro d
              obtain ⟨e, he, hek⟩ := hds d
              rw [he, hρd]
              exact hiff e hek
        rcases hdich with hall | hiff
        · have hs0 : θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) s) = ⊥ :=
            hall ⟨s, CellScheme.mem_below_gradedIndex _ s⟩
          have hfun0 : (fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
              min (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) d.1))
                (θ K ((𝔼).rowAt (Fin.castAdd _ (u K)) s))) = fun _ ↦ ⊥ :=
            funext fun d ↦ by rw [hall d, min_eq_left bot_le]
          rw [hfun0]
          exact TransformsTo.bot _ _
        · exact TransformsTo.map_of_bot_iff (K := K)
            (grade := fun d : (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex s) ↦
              (𝔼).toCellScheme.grade d.1)
            (E := (𝔼).rows.row s)
            (p := fun d ↦ (𝔼).rowAt (Fin.castAdd _ (u K)) d.1)
            (q := fun d ↦ (𝔼).rowAt (Fin.castAdd _ (u K)) d.1)
            (c := ⟨s, CellScheme.mem_below_gradedIndex _ s⟩) (fun d ↦ hdK d) le_rfl hvisρ hlocρ
            hvisρ hlocρ (hθ K h1 h2).1 hiff
    · -- availability
      obtain ⟨h1, h2⟩ := hgY t ht
      obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp (hρ _ h1 h2)
      obtain ⟨z, hz, hle⟩ := havail s t (hbelowk t) hst hg
      have hgz : (𝔼).toCellScheme.grade z = (𝔼).toCellScheme.grade t := congrArg Prod.snd hz
      refine ⟨z, hz, ?_⟩
      rw [hrdef s, hrdef z, hg, hgz]
      exact (hθ _ h1 h2).1.monotone hle
  · -- the observation of the ambient at the cap
    change min (r d) c = min (q d) c
    rw [← hQd d.1 d.2]
    obtain ⟨h1, h2⟩ := hgY d.1 d.2
    rcases cell_cases d.1 with ⟨v, hv, hgv⟩ | ⟨e, he⟩
    · rw [hr_full d.1 d.2 v hv _ rfl hgv, hsame Q hQ v _ hgv h2 d.1 hv,
        ← hsame Q hQ v _ hgv h2 _ (hcfo v _ hgv h2), hpq' _ (hcfY v _ hgv h2)]
    · set k := (I.attachment g).toCellScheme.grade e with hkdef
      have hdk : (𝔼).toCellScheme.grade d.1 = k := by
        rw [he]; exact congrArg Prod.snd (gradedIndex_attachEmb e)
      have hk1 : 1 ≤ k := hdk ▸ h1
      have hkj : k ≤ j := hdk ▸ h2
      obtain ⟨v, hv⟩ := exists_shadow_rowAt_eq (Γ := Γ) (A := A) (B' := B') hcard hk1
        (hkj.trans hjm) (u k) (hu k hk1 hkj).1 hkdef.symm
      have hgl := gradedIndex_ladCell (Γ := Γ) (A := A) (B' := B') v
      have hrd : r d.1 = min (P (cpy H Γ A B' hU (ladCell H Γ A B' v)))
          (P (cpy H Γ A B' hU (u k))) := by
        rw [he, hr_att e k rfl, hv,
          decode_copyFull hU (hu k hk1 hkj).1 (hkj.trans hjU) (hθc k hk1 hkj) hgl hk1]
        exact congrArg₂ min (congrArg P (cpy_eq hU hgl (hk1.trans (hkj.trans hjU))).symm)
          (congrArg P (cpy_eq hU (hu k hk1 hkj).1 (hkj.trans hjU)).symm)
      rw [hrd]
      have hcuY : (Fin.castAdd _ (u k) : Fin (𝔼).card) ∈
          (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
        rw [CellScheme.mem_below, hgiu k hk1 hkj]; exact ⟨subset_rfl, hkj⟩
      have hdu : d.1 ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (u k))) := by
        rw [hgiu k hk1 hkj, CellScheme.mem_below]
        exact ⟨subset_univ _, hdk.le⟩
      have hlu : (Fin.castAdd _ (ladCell H Γ A B' v) : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (u k))) := by
        rw [hgiu k hk1 hkj, CellScheme.mem_below, Scheme.gradedIndex_mirror_castAdd, hgl]
        exact ⟨subset_rfl, hk1⟩
      have hdz := Scheme.min_eq_min_of_rowAt_eq hQ hcuY hdu hlu (by
        rw [he]
        change (𝔼).rowAt (Fin.castAdd _ (u k))
          (Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m e)) = _
        rw [Scheme.rowAt_mirror_castAdd, Scheme.rowAt_mirror_castAdd, hv])
      have hℓ : min (Q (Fin.castAdd _ (ladCell H Γ A B' v))) c =
          min (P (cpy H Γ A B' hU (ladCell H Γ A B' v))) c := by
        rw [← hsame Q hQ _ 1 hgl hj1 _ (hcfo _ 1 hgl hj1), hpq' _ (hcfY _ 1 hgl hj1)]
      have hzM : min (Q (Fin.castAdd _ (u k))) c = min (P (cpy H Γ A B' hU (u k))) c := by
        rw [← hsame Q hQ _ k (hu k hk1 hkj).1 hkj _ (hcfo _ k (hu k hk1 hkj).1 hkj),
          hpq' _ (hcfY _ k (hu k hk1 hkj).1 hkj)]
      obtain ⟨-, -, havailQ⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hQ
      obtain ⟨z, hz, hle⟩ := havailQ d.1 _ hcuY
        (subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst (hgiu k hk1 hkj)).symm))
        (hdk.trans (congrArg Prod.snd (hgiu k hk1 hkj)).symm)
      obtain ⟨w', rfl, hw'⟩ := exists_eq_castAdd_of_scope z
        ((congrArg Prod.fst hz).trans (congrArg Prod.fst (hgiu k hk1 hkj)))
      have hgw' : (𝕋).toCellScheme.gradedIndex w' = ((univ : Finset (Fin (m + 2))), k) :=
        hw'.trans (hz.trans (hgiu k hk1 hkj))
      have hwM : min (Q (Fin.castAdd _ w')) c ≤ min (P (cpy H Γ A B' hU (u k))) c := by
        rw [← hsame Q hQ _ k hgw' hkj _ (hcfo _ k hgw' hkj), hpq' _ (hcfY _ k hgw' hkj)]
        exact min_le_min_right _ ((hu k hk1 hkj).2.2 w' hgw')
      exact Label.min_min_eq_of_reader hdz hℓ hzM hle hwM
  · -- the prescription below `(U, j)`
    change r d.1 = p d
    have hdY : d.1 ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) :=
      le_trans d.2 hXY
    obtain ⟨h1, h2⟩ := hgY d.1 hdY
    rw [← hPd d.1 d.2]
    rcases cell_cases d.1 with ⟨v, hv, hgv⟩ | ⟨e, he⟩
    · rw [hr_full d.1 hdY v hv _ rfl hgv]
      refine (Scheme.eq_of_mirrorOrig_eq hP (by rw [hv, hcfo v _ hgv h2]) ?_
        (hcfY v _ hgv h2)).symm
      rw [cpy_eq hU hgv (h2.trans hjU)]
      exact d.2.1.trans (le_of_eq (congrArg Prod.fst (gradedIndex_copyFull hU v hgv _)).symm)
    · set k := (I.attachment g).toCellScheme.grade e with hkdef
      have hdk : (𝔼).toCellScheme.grade d.1 = k := by
        rw [he]; exact congrArg Prod.snd (gradedIndex_attachEmb e)
      have hk1 : 1 ≤ k := hdk ▸ h1
      have hkj : k ≤ j := hdk ▸ h2
      have hes : (I.attachment g).toCellScheme.scope e ⊆ U := by
        have h := d.2.1
        rw [he] at h
        exact (congrArg Prod.fst (gradedIndex_attachEmb e)).symm.trans_le h
      have hrow := rowAt_copyAt_attachEmb (Γ := Γ) (A := A) (B' := B') hU
        (congrArg Prod.fst (hu k hk1 hkj).1)
        ((congrArg Prod.snd (hu k hk1 hkj).1).trans_le (hkj.trans hjU)) hes
        (le_of_eq (congrArg Prod.snd (hu k hk1 hkj).1).symm)
      have hmem : I.attachEmb g H Γ A B' e ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex
            (copyFull H Γ A B' hU (u k) (hu k hk1 hkj).1 (hkj.trans hjU))) := by
        rw [CellScheme.mem_below, gradedIndex_copyFull, gradedIndex_attachEmb]
        exact ⟨hes, le_rfl⟩
      rw [he, hr_att e k rfl, ← hrow]
      change θ k ((𝔼).rowAt (copyFull H Γ A B' hU (u k) (hu k hk1 hkj).1 (hkj.trans hjU))
        (I.attachEmb g H Γ A B' e)) = _
      rw [hθc k hk1 hkj _ hmem]
      exact min_eq_left (le_max_copy hU hP hkj (hkj.trans hjU) (hu k hk1 hkj).1
        (hmaxc k hk1 hkj) (he ▸ d.2) (congrArg Prod.snd (gradedIndex_attachEmb e)))

end Seed

end VaughtConjecture

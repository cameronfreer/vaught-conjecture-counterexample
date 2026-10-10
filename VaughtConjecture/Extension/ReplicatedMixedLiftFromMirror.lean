/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerTwins
import VaughtConjecture.Extension.ReplicatedGradeOne
import VaughtConjecture.MainTheorem.MirrorMixedLift

/-!
# The mixed lift of the replicated scheme from the lift of a mirrored scheme

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

The replicated scheme is the ladder tower over the attachment (`Seed.attachTower`) mirrored at the
mixed faces, so the lift from a mixed face of a mirrored scheme
(`Seed.cappedLift_mirror_mixed_face`) applies to it, with the cells of the attachment
`baseCellEmb m` and the ladder points `Seed.ladCell`.  The tower meets its hypotheses:

* `Seed.attachTower_reads_ladder`: a cell of full scope at a grade `K ≥ 2` is the cell of a lawful
  state `R` (`Scheme.LadderBaseData.exists_controller_ladderTower`), and reads the ladder and the
  cells of the attachment of grade at most `K` through the positive table of `R`, which is `⊥` at
  `0`;
* `Seed.attachTower_agree_shadow`: two such cells agree at the shadow of the lower one
  (`Scheme.LadderBaseData.exists_controller_agree_ladderTower`,
  `Scheme.LadderBaseData.stateExt_shadow`);
* `Seed.attachTower_twin`: a cell at the grade `K` has a twin at every grade `2 ≤ k ≤ K`, read at
  the top of the grid (`Scheme.LadderBaseData.exists_controller_twin_ladderTower`);
* the grade-one cells are the ladder points (`Seed.tower_grade_one_cases`), and the catalogues are
  nonempty (the bottom state), so there are cells of full scope at every grade up to `m + 1`.

**The lift** (`Seed.cappedLift_mixed_face_of_mirror`) has the statement of
`Seed.cappedLift_mixed_face`.

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

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))

/-- The cells of the tower over the attachment have grade at most `m + 1`. -/
theorem attachTower_grade_le (f : Fin (𝕋).card) : (𝕋).toCellScheme.grade f ≤ m + 1 :=
  Nat.lt_succ_iff.mp (Scheme.LadderBaseData.grade_lt_ladderTower (K := m) (by omega) f)

/-- **A cell of full scope at a grade `K ≥ 2` reads the ladder through one member**, with a
monotone table that is `⊥` at `0`, and the cells of the attachment of grade at most `K` through
the ranks of that member. -/
theorem attachTower_reads_ladder (hcard : (I.attachmentBase g).S.card ≤ H) (f : Fin (𝕋).card)
    (K : ℕ) (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
    (hK : 2 ≤ K) :
    ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
      Φ 0 = ⊥ ∧ (∀ v, (𝕋).rowAt f (ladCell H Γ A B' v) = Φ (idx b v)) ∧
      ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
        (𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e) =
          Φ (Scheme.rankProf (I.attachmentBase g).S H b e) := by
  have hKm := (congrArg Prod.snd hf).symm.trans_le (attachTower_grade_le f)
  obtain ⟨R, -, hR, hrowA, hrowL⟩ :=
    Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
      (Γ := Γ) (B' := B') hcard (K - 2) m (by omega) f (by rw [hf, Nat.sub_add_cancel hK])
  refine ⟨Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR, posTable R,
    monotone_posTable, posTable_zero, fun v ↦ ?_, fun e he ↦ ?_⟩
  · refine (hrowL v).trans ?_
    rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
  · exact (hrowA e (show (I.attachment g).toCellScheme.grade e ≤ K - 2 + 2 by omega)).trans
      (posTable_rankVector ((I.attachmentBase g).isSelfVisible_one_of_isLawful hR) e).symm

/-- **Two cells of full scope at grades `K ≥ k ≥ 2` agree at a shadow** of a cell of the attachment
of grade `k`: a ladder point read by the lower cell as that cell, and read by the higher one, capped
at its reading of the lower one, as that cell. -/
theorem attachTower_agree_shadow (hcard : (I.attachmentBase g).S.card ≤ H) (f u : Fin (𝕋).card)
    (K k : ℕ) (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
    (hu : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k)) (hk2 : 2 ≤ k)
    (hkK : k ≤ K) (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e = k) :
    ∃ v, (𝕋).rowAt u (ladCell H Γ A B' v) = (𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e) ∧
      min ((𝕋).rowAt f (ladCell H Γ A B' v)) ((𝕋).rowAt f u) =
        min ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e)) ((𝕋).rowAt f u) := by
  have hKm := (congrArg Prod.snd hf).symm.trans_le (attachTower_grade_le f)
  obtain ⟨Rf, -, Ru, hRuC, hrf, hru, hagr⟩ :=
    Scheme.LadderBaseData.exists_controller_agree_ladderTower (B := I.attachmentBase g)
      (H := H) (Γ := Γ) (A := A) (B' := B') (k - 2) (K - 2) (by omega) m (by omega) f u
      (by rw [hf, Nat.sub_add_cancel (hk2.trans hkK)]) (by rw [hu, Nat.sub_add_cancel hk2])
  have hRu := (Scheme.LadderBaseData.mem_towerCat.mp hRuC).2.1
  have hgre : ((I.attachmentBase g).ladderBase H).toCellScheme.grade (Fin.castAdd _ e) = k :=
    (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans he
  set w : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H :=
    (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hRu, Sum.inr e)
  have hgw : ((I.attachmentBase g).ladderBase H).toCellScheme.grade
      (Fin.natAdd _ (Scheme.ladderEquiv _ _ H w)) = 1 :=
    Scheme.appendFullCellsScheme_grade_natAdd _ _ _ _
  have hsh : (I.attachmentBase g).stateExt H Ru (Fin.natAdd _ (Scheme.ladderEquiv _ _ H w)) =
      (I.attachmentBase g).stateExt H Ru (Fin.castAdd _ e) :=
    (Scheme.LadderBaseData.stateExt_shadow hcard hRu e).trans
      (Scheme.LadderBaseData.stateExt_castAdd hRu hcard e).symm
  refine ⟨w, (hru _ (by omega)).trans (hsh.trans (hru _ (by omega)).symm), ?_⟩
  change min ((𝕋).rowAt f ((I.attachmentBase g).towerEmb m _)) _ =
    min ((𝕋).rowAt f ((I.attachmentBase g).towerEmb m (Fin.castAdd _ e))) _
  rw [hrf _ (by omega), hrf _ (by omega), hagr, hagr, hsh]

/-- **A cell of full scope at the grade `K` has a twin at every grade `2 ≤ k ≤ K`**: a cell of full
scope at the grade `k` read at least as high as every cell of the attachment of grade `k`. -/
theorem attachTower_twin (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (f : Fin (𝕋).card)
    (K k : ℕ) (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
    (hk2 : 2 ≤ k) (hkK : k ≤ K) (e : Fin (I.attachment g).card)
    (he : (I.attachment g).toCellScheme.grade e = k) :
    ∃ et, (𝕋).toCellScheme.gradedIndex et = ((univ : Finset (Fin (m + 2))), k) ∧
      (𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e) ≤ (𝕋).rowAt f et := by
  have hKm := (congrArg Prod.snd hf).symm.trans_le (attachTower_grade_le f)
  obtain ⟨R, hRC, -, hrowA, -, htwin⟩ :=
    Scheme.LadderBaseData.exists_controller_twin_ladderTower (B := I.attachmentBase g)
      (H := H) (Γ := Γ) (A := A) (B' := B') hcard hΓ hA (K - 2) m (by omega) f
      (by rw [hf, Nat.sub_add_cancel (hk2.trans hkK)])
  obtain ⟨et, het, hrt⟩ := htwin (k - 2) (by omega)
  rw [Nat.sub_add_cancel hk2] at het hrt
  refine ⟨et, het, ?_⟩
  rw [hrt]
  exact (hrowA e (show (I.attachment g).toCellScheme.grade e ≤ K - 2 + 2 by omega)).trans_le
    ((hΓ _ ((Scheme.LadderBaseData.mem_towerCat.mp hRC).1 e)).trans
      (gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, hk2⟩)))

/-- **The lift from a mixed face into a larger face** carrying cells of full scope or their copies,
from the lift of a mirrored scheme (the statement of `Seed.cappedLift_mixed_face`). -/
theorem cappedLift_mixed_face_of_mirror (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hU : U ∈ I.mixedFaces g) {W : Finset (Fin (m + 2))}
    (hUW : U ⊆ W) (τ : Fin (𝕋).card → Fin (𝔼).card)
    (hτo : ∀ v, (𝕋).mirrorOrig (I.mixedFaces g) (τ v) = v) {j : ℕ}
    (hτg : ∀ v k, (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k) → k ≤ j →
      (𝔼).toCellScheme.gradedIndex (τ v) = (W, k)) (hj1 : 1 ≤ j)
    (hjm : j ≤ m + 1) (hjU : j ≤ #U) :
    (𝔼).rows.CappedLift (X := (U, j)) (Y := (W, j)) ⟨hUW, le_rfl⟩ := by
  have hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty := fun _ ↦
    ⟨fun _ ↦ ⊥, Scheme.LadderBaseData.mem_towerCat.mpr
      ⟨fun _ ↦ hΓ0, CellScheme.Rows.isLawful_const_bot, hA0 _⟩⟩
  refine cappedLift_mirror_mixed_face (hmix := I.not_subset_scope_tower g H Γ A B') hH
    (Scheme.LadderBaseData.ladderTower_lawful hH hcard hΓ hA m).1
    (fun d ↦ (Scheme.LadderBaseData.isWellFormed_ladderTower (k := m)
      (by omega)).isWellFormed.grade_pos d)
    (fun e ↦ (I.attachmentBase g).gradedIndex_baseCellEmb (H := H) (Γ := Γ) (A := A) (B' := B') m e)
    (fun x hx ↦ ((I.attachmentBase g).mem_range_baseCellEmb m x hx).elim fun e he ↦ ⟨e, he.symm⟩)
    gradedIndex_ladCell (fun p v ↦ by
      rw [rowAt_ladCell_ladCell, Scheme.baseIndex_natAdd, Equiv.symm_apply_apply])
    (fun p e he ↦ rowAt_ladCell_baseCellEmb p he) (fun x hx ↦ ?_)
    (attachTower_reads_ladder hcard) (attachTower_agree_shadow hcard)
    (attachTower_twin hcard hΓ hA) hU hUW τ hτo hτg
    (fun k hk2 hkj ↦ (I.attachmentBase g).exists_gradedIndex_univ_ladderTower (B' := B') hH hne
      m k (by omega) (by omega)) hj1 hjU
  rcases tower_grade_one_cases x (congrArg Prod.snd hx) with ⟨v, rfl⟩ | ⟨e, -, rfl⟩
  · exact ⟨v, rfl⟩
  · exact ((I.attachmentBase g).scope_ne_univ e
      ((congrArg Prod.fst (Scheme.LadderBaseData.gradedIndex_baseCellEmb (H := H) (Γ := Γ)
        (A := A) (B' := B') m e)).symm.trans (congrArg Prod.fst hx))).elim

end Seed

end VaughtConjecture

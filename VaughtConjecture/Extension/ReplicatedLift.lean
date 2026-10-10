/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerTwins
import VaughtConjecture.Extension.ReplicatedGradeOne

/-!
# Decoded readings through the copies at a mixed face

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

Let `U` be a mixed face and `P` a labelling of the replicated scheme.  For a cell `v` of full
scope of the tower of grade at most `|U|`, its copy at `U` (`Seed.copyFull`) reads the copies at
`U` and the cells of the attachment inside `U` as `v` reads their originals.  A map `θ` reading the
row of the copy of `v` as `P` capped at the copy (a capped decoder of a section lawful below a
pair containing the copy) reads the row of `v` at a cell `w` of full scope as `P` at the copy of
`w`, capped (`Seed.decode_copyFull`).

**Readings of a cell of the attachment by two controllers** (`Seed.min_decode_eq_decode`).  Let
`f` be a cell of full scope at a grade `K` and `u` one at a grade `k` with `2 ≤ k ≤ K`, `u` of
maximal label among the copies at `U` at its grade, and `θf`, `θu` capped decoders at the copies of
`f` and `u`.  Then for every cell `e` of the attachment of grade `k`, inside `U` or not,
`min (θu (row_u e)) (P f') = θf (row_f e)` (`f'` the copy of `f`): the reading of `e` by `u`,
capped at `f`, is the reading by `f`.  The states of `f` and `u` agree capped at the reading of `u`
by `f` (`Scheme.LadderBaseData.exists_controller_agree_ladderTower`), `u` reads `e` as its shadow
(`Scheme.LadderBaseData.stateExt_shadow`), and the reading of `e` by `f` is at most the reading of
the twin of `f` at the grade `k`, whose copy is at most the maximum
(`Scheme.LadderBaseData.exists_controller_twin_ladderTower`).

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Agreement heights and catalogue layers are those of the coatom extension construction
[Kni26, §4.4].
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
/-- The copy at a mixed face of a cell of full scope of grade at most its size. -/
noncomputable def copyFull (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    Fin (𝔼).card :=
  copyAt H Γ A B' hU v (congrArg Prod.fst hv) ((congrArg Prod.snd hv).trans_le hk)

theorem mirrorOrig_copyFull (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    (𝕋).mirrorOrig (I.mixedFaces g) (copyFull H Γ A B' hU v hv hk) = v :=
  mirrorOrig_copyAt hU _ _ _

theorem gradedIndex_copyFull (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    (𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU v hv hk) = (U, k) :=
  (gradedIndex_copyAt hU _ _ _).trans
    (Prod.ext rfl (show (𝕋).toCellScheme.grade v = k from congrArg Prod.snd hv))

/-- **A decoder at a copy reads the row of the original at a cell of full scope** as the labelling
at the copy of that cell, capped. -/
theorem decode_copyFull (hU : U ∈ I.mixedFaces g) {P : Fin (𝔼).card → Label.{u}}
    {v : Fin (𝕋).card} {K : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), K)) (hKU : K ≤ #U)
    {θ : Label.{u} → Label.{u}}
    (hθ : ∀ d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU v hv hKU)),
      θ ((𝔼).rowAt (copyFull H Γ A B' hU v hv hKU) d) =
        min (P d) (P (copyFull H Γ A B' hU v hv hKU)))
    {w : Fin (𝕋).card} {k : ℕ}
    (hw : (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)) (hkK : k ≤ K) :
    θ ((𝕋).rowAt v w) =
      min (P (copyFull H Γ A B' hU w hw (hkK.trans hKU))) (P (copyFull H Γ A B' hU v hv hKU)) := by
  have hmem : copyFull H Γ A B' hU w hw (hkK.trans hKU) ∈ (𝔼).toCellScheme.below
      ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU v hv hKU)) := by
    rw [CellScheme.mem_below, gradedIndex_copyFull, gradedIndex_copyFull]
    exact ⟨subset_rfl, hkK⟩
  rw [← hθ _ hmem, Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_copyFull, mirrorOrig_copyFull]

/-- **The reading of a cell of the attachment by a lower controller, capped at a higher one, is the
reading by the higher one**, through capped decoders at the copies at a mixed face `U`, when the
lower controller is of maximal label among the copies at its grade. -/
theorem min_decode_eq_decode (hU : U ∈ I.mixedFaces g) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {P : Fin (𝔼).card → Label.{u}} {k K : ℕ} (hk2 : 2 ≤ k) (hkK : k ≤ K) (hKm : K ≤ m + 1)
    (hKU : K ≤ #U) {f u : Fin (𝕋).card}
    (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
    (hu : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k))
    (hmax : ∀ w (hw : (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)),
      P (copyFull H Γ A B' hU w hw (hkK.trans hKU)) ≤
        P (copyFull H Γ A B' hU u hu (hkK.trans hKU)))
    {θf θu : Label.{u} → Label.{u}} (hθf_mono : Monotone θf)
    (hθf_le : ∀ x, θf x ≤ P (copyFull H Γ A B' hU f hf hKU))
    (hθf : ∀ d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU f hf hKU)),
      θf ((𝔼).rowAt (copyFull H Γ A B' hU f hf hKU) d) =
        min (P d) (P (copyFull H Γ A B' hU f hf hKU)))
    (hθu : ∀ d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU u hu (hkK.trans hKU))),
      θu ((𝔼).rowAt (copyFull H Γ A B' hU u hu (hkK.trans hKU)) d) =
        min (P d) (P (copyFull H Γ A B' hU u hu (hkK.trans hKU))))
    {e : Fin (I.attachment g).card} (he : (I.attachment g).toCellScheme.grade e = k) :
    min (θu ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)))
        (P (copyFull H Γ A B' hU f hf hKU)) =
      θf ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e)) := by
  have hf' : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K - 2 + 2) := by
    rw [show K - 2 + 2 = K by omega]; exact hf
  have hu' : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k - 2 + 2) := by
    rw [show k - 2 + 2 = k by omega]; exact hu
  obtain ⟨Rf, hRfC, Ru, hRuC, hrf, hru, hagr⟩ :=
    Scheme.LadderBaseData.exists_controller_agree_ladderTower (B := I.attachmentBase g)
      (H := H) (Γ := Γ) (A := A) (B' := B') (k - 2) (K - 2) (by omega) m (by omega) f u hf' hu'
  have hRf := (Scheme.LadderBaseData.mem_towerCat.mp hRfC).2.1
  have hRu := (Scheme.LadderBaseData.mem_towerCat.mp hRuC).2.1
  -- the readings
  have hgre : ((I.attachmentBase g).ladderBase H).toCellScheme.grade (Fin.castAdd _ e) = k :=
    (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans he
  have r_fe : (𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e) = Rf e :=
    (hrf (Fin.castAdd _ e) (by omega)).trans
      (Scheme.LadderBaseData.stateExt_castAdd hRf hcard e)
  have r_ue : (𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e) = Ru e :=
    (hru (Fin.castAdd _ e) (by omega)).trans
      (Scheme.LadderBaseData.stateExt_castAdd hRu hcard e)
  set wu : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H :=
    (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hRu, Sum.inr e) with hwu
  have hgw : ((I.attachmentBase g).ladderBase H).toCellScheme.grade
      (Fin.natAdd _ (Scheme.ladderEquiv _ _ H wu)) = 1 :=
    Scheme.appendFullCellsScheme_grade_natAdd _ _ _ _
  have r_uw : (𝕋).rowAt u (ladCell H Γ A B' wu) = Ru e :=
    (hru _ (by omega)).trans (Scheme.LadderBaseData.stateExt_shadow hcard hRu e)
  have r_fw : (𝕋).rowAt f (ladCell H Γ A B' wu) = (I.attachmentBase g).stateExt H Rf
      (Fin.natAdd _ (Scheme.ladderEquiv _ _ H wu)) := hrf _ (by omega)
  -- the agreement at the shadow and at the cell
  have key : min ((𝕋).rowAt f (ladCell H Γ A B' wu)) ((𝕋).rowAt f u) =
      min ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e)) ((𝕋).rowAt f u) := by
    rw [r_fw, hagr, Scheme.LadderBaseData.stateExt_shadow hcard hRu e, r_fe]
    have h2 := hagr (Fin.castAdd _ e)
    rw [Scheme.LadderBaseData.stateExt_castAdd hRf hcard e,
      Scheme.LadderBaseData.stateExt_castAdd hRu hcard e] at h2
    exact h2.symm
  -- the decoded readings
  have hgwu : (𝕋).toCellScheme.gradedIndex (ladCell H Γ A B' wu) =
      ((univ : Finset (Fin (m + 2))), 1) := gradedIndex_ladCell wu
  have dec_u : θu ((𝕋).rowAt u ((I.attachmentBase g).baseCellEmb m e)) =
      min (P (copyFull H Γ A B' hU _ hgwu ((by omega : 1 ≤ k).trans (hkK.trans hKU))))
        (P (copyFull H Γ A B' hU u hu (hkK.trans hKU))) := by
    rw [r_ue, ← r_uw]
    exact decode_copyFull hU hu (hkK.trans hKU) hθu hgwu (by omega)
  have dec_fw : θf ((𝕋).rowAt f (ladCell H Γ A B' wu)) =
      min (P (copyFull H Γ A B' hU _ hgwu ((by omega : 1 ≤ K).trans hKU)))
        (P (copyFull H Γ A B' hU f hf hKU)) :=
    decode_copyFull hU hf hKU hθf hgwu (by omega)
  have dec_fA : θf ((𝕋).rowAt f u) =
      min (P (copyFull H Γ A B' hU u hu (hkK.trans hKU))) (P (copyFull H Γ A B' hU f hf hKU)) :=
    decode_copyFull hU hf hKU hθf hu hkK
  -- the twin of `f` at the grade `k`
  obtain ⟨-, -, -, -, -, htwin⟩ :=
    Scheme.LadderBaseData.exists_controller_twin_ladderTower (B := I.attachmentBase g)
      (H := H) (Γ := Γ) (A := A) (B' := B') hcard hΓ hA (K - 2) m (by omega) f hf'
  obtain ⟨et, het, hrt⟩ := htwin (k - 2) (by omega)
  have het' : (𝕋).toCellScheme.gradedIndex et = ((univ : Finset (Fin (m + 2))), k) := by
    rw [het, show k - 2 + 2 = k by omega]
  have hrt' : (𝕋).rowAt f et = gridPoint k B' := by
    rw [hrt, show k - 2 + 2 = k by omega]
  have dec_t : θf (gridPoint k B') =
      min (P (copyFull H Γ A B' hU et het' (hkK.trans hKU)))
        (P (copyFull H Γ A B' hU f hf hKU)) := by
    rw [← hrt']
    exact decode_copyFull hU hf hKU hθf het' hkK
  have hRfe : Rf e ≤ gridPoint k B' :=
    (hΓ _ ((Scheme.LadderBaseData.mem_towerCat.mp hRfC).1 e)).trans
      (gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, hk2⟩))
  have hθRf : θf (Rf e) ≤ P (copyFull H Γ A B' hU u hu (hkK.trans hKU)) :=
    (hθf_mono hRfe).trans (dec_t ▸ (min_le_left _ _).trans (hmax et het'))
  -- conclusion
  have h1 := congrArg θf key
  rw [hθf_mono.map_min, hθf_mono.map_min, dec_fw, dec_fA, r_fe] at h1
  rw [dec_u, r_fe]
  rw [min_eq_left (le_min hθRf (hθf_le _))] at h1
  rw [← h1]
  have lat : ∀ a b c : Label.{u}, min (min a b) c = min (min a c) (min b c) := fun a b c ↦ by
    rw [min_min_min_comm, min_self]
  exact lat _ _ _

/-! ### Readings of the ladder -/

/-- **A cell of full scope reads the ladder through the indices of one member**: a cell `f` of the
tower at `(univ, K)`, `1 ≤ K ≤ m + 1`, reads every ladder point `v` as `Φ` of the index of `v` for
some member `b`, `Φ` monotone, and every cell of the attachment of grade one as `Φ` of its rank for
`b` (a ladder point through its codes, a controller through the positive table of its state). -/
theorem exists_ladder_reading (hcard : (I.attachmentBase g).S.card ≤ H) {K : ℕ} (hK1 : 1 ≤ K)
    (hKm : K ≤ m + 1) {f : Fin (𝕋).card}
    (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K)) :
    ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
      (∀ v, (𝕋).rowAt f (ladCell H Γ A B' v) =
        Φ (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) b v)) ∧
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        (𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e) =
          Φ (Scheme.rankProf (I.attachmentBase g).S H b e) := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have hK' : K = 1 := by omega
    subst hK'
    rcases tower_grade_one_cases f (congrArg Prod.snd hf) with ⟨p, rfl⟩ | ⟨e', -, rfl⟩
    · refine ⟨p.1, ladderSource (Scheme.ladderCeil (Scheme.rankProf _ H) p),
        monotone_ladderSource _, fun v ↦ ?_, fun e he ↦ ?_⟩
      · rw [rowAt_ladCell_ladCell, Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
      · rw [rowAt_ladCell_baseCellEmb p he, rowAt_ladCell_ladCell, Scheme.baseIndex_natAdd,
          Equiv.symm_apply_apply]
        congr 1
        exact ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) (p.1, Sum.inr e)
    · exfalso
      exact (I.attachmentBase g).scope_ne_univ e'
        ((congrArg Prod.fst (Scheme.LadderBaseData.gradedIndex_baseCellEmb (H := H) (Γ := Γ)
          (A := A) (B' := B') m e')).symm.trans (congrArg Prod.fst hf))
  · have hf' : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K - 2 + 2) := by
      rw [show K - 2 + 2 = K by omega]; exact hf
    obtain ⟨R, -, hR, hrowA, hrowL⟩ :=
      Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
        (Γ := Γ) (B' := B') hcard (K - 2) m (by omega) f hf'
    refine ⟨Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR, posTable R,
      monotone_posTable, fun v ↦ ?_, fun e he ↦ ?_⟩
    · refine (hrowL v).trans ?_
      rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
    · refine (hrowA e (show (I.attachment g).toCellScheme.grade e ≤ K - 2 + 2 by omega)).trans ?_
      exact (posTable_rankVector ((I.attachmentBase g).isSelfVisible_one_of_isLawful hR) e).symm

/-- **The grade-one reading of a cell of the attachment, capped at a controller, is the
controller's reading**, through capped decoders at the copies at a mixed face `U`, when the
grade-one reading is through the top rung of a member whose copy dominates the copied ladder. -/
theorem min_decode_eq_decode_one (hU : U ∈ I.mixedFaces g)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hH : 0 < H) {P : Fin (𝔼).card → Label.{u}}
    {K : ℕ} (hK1 : 1 ≤ K) (hKm : K ≤ m + 1) (hKU : K ≤ #U) {f : Fin (𝕋).card}
    (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
    (a : Scheme.RankMember (I.attachmentBase g).S H)
    (hmax : ∀ v, P (copyFull H Γ A B' hU (ladCell H Γ A B' v) (gradedIndex_ladCell v)
        (hK1.trans hKU)) ≤
      P (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
        (gradedIndex_ladCell _) (hK1.trans hKU)))
    {θf θ1 : Label.{u} → Label.{u}} (hθf_mono : Monotone θf)
    (hθf_le : ∀ x, θf x ≤ P (copyFull H Γ A B' hU f hf hKU))
    (hθf : ∀ d ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU f hf hKU)),
      θf ((𝔼).rowAt (copyFull H Γ A B' hU f hf hKU) d) =
        min (P d) (P (copyFull H Γ A B' hU f hf hKU)))
    (hθ1 : ∀ d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex
        (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) (hK1.trans hKU))),
      θ1 ((𝔼).rowAt (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) (hK1.trans hKU)) d) =
        min (P d) (P (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
          (gradedIndex_ladCell _) (hK1.trans hKU))))
    {e : Fin (I.attachment g).card} (he : (I.attachment g).toCellScheme.grade e = 1) :
    min (θ1 ((𝕋).rowAt (ladCell H Γ A B' (a, Sum.inl ⟨H - 1, by omega⟩))
        ((I.attachmentBase g).baseCellEmb m e))) (P (copyFull H Γ A B' hU f hf hKU)) =
      θf ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e)) := by
  set top : Scheme.LadderPt (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  have hU1 : 1 ≤ #U := hK1.trans hKU
  -- the grade-one reading
  have r1 : θ1 ((𝕋).rowAt (ladCell H Γ A B' top) ((I.attachmentBase g).baseCellEmb m e)) =
      P (copyFull H Γ A B' hU (ladCell H Γ A B' (a, Sum.inr e)) (gradedIndex_ladCell _) hU1) := by
    rw [rowAt_ladCell_baseCellEmb top he]
    rw [decode_copyFull hU (gradedIndex_ladCell top) hU1 hθ1 (gradedIndex_ladCell _) le_rfl]
    exact min_eq_left (hmax _)
  rw [r1]
  -- the reading by `f`
  obtain ⟨b, Φ, hΦ, hrl, hre⟩ := exists_ladder_reading (Γ := Γ) (A := A) (B' := B') hcard hK1
    hKm hf
  set κ := rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
    (Scheme.rankProf (I.attachmentBase g).S H a) with hκ
  have hagr := rankAgree_rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
    (Scheme.rankProf (I.attachmentBase g).S H a) e
  have hidx_sh : ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
      (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) b
        ((a, Sum.inr e) : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H) =
      min (Scheme.rankProf (I.attachmentBase g).S H b e) κ := by
    change min κ (Scheme.rankProf (I.attachmentBase g).S H a e) = _
    rw [min_comm]
    exact hagr.symm
  have hidx_top : ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
      (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) b top = κ := by
    unfold ladderIndex
    simp only [top, Scheme.ladderCeil, Sum.elim_inl]
    have hκH := rankCut_le H (Scheme.rankProf (I.attachmentBase g).S H b)
      (Scheme.rankProf (I.attachmentBase g).S H a)
    exact min_eq_left (by omega)
  have hrow_sh : (𝕋).rowAt f (ladCell H Γ A B' (a, Sum.inr e)) =
      min ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e))
        ((𝕋).rowAt f (ladCell H Γ A B' top)) := by
    rw [hrl, hrl, hre e he, hidx_sh, hidx_top, hΦ.map_min]
  have hdec_sh := decode_copyFull hU hf hKU hθf (gradedIndex_ladCell (a, Sum.inr e)) hK1
  have hdec_top := decode_copyFull hU hf hKU hθf (gradedIndex_ladCell top) hK1
  -- the reading of `e` by `f` is at most the copied top rung
  have hle_top : θf ((𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e)) ≤
      P (copyFull H Γ A B' hU (ladCell H Γ A B' top) (gradedIndex_ladCell _) hU1) := by
    have hsh : (𝕋).rowAt f ((I.attachmentBase g).baseCellEmb m e) =
        (𝕋).rowAt f (ladCell H Γ A B' (b, Sum.inr e)) := by
      rw [hre e he, hrl]
      congr 1
      exact (ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
        (b, Sum.inr e)).symm
    rw [hsh, decode_copyFull hU hf hKU hθf (gradedIndex_ladCell (b, Sum.inr e)) hK1]
    exact (min_le_left _ _).trans (hmax _)
  have h1 := congrArg θf hrow_sh
  rw [hθf_mono.map_min, hdec_sh, hdec_top,
    min_eq_left (le_min hle_top (hθf_le _))] at h1
  exact h1

/-! ### The cells at a mixed face -/

/-- **The cells at a mixed face are copies**: a cell of the replicated scheme at `(U, k)`, for a
mixed face `U`, is the copy at `U` of a cell of full scope of the tower at the grade `k`. -/
theorem exists_eq_copyFull (hU : U ∈ I.mixedFaces g) {k : ℕ} (hkU : k ≤ #U)
    (z : Fin (𝔼).card) (hz : (𝔼).toCellScheme.gradedIndex z = (U, k)) :
    ∃ v, ∃ hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k),
      z = copyFull H Γ A B' hU v hv hkU := by
  induction z using Fin.addCases with
  | left x =>
    exfalso
    have hs : (𝕋).toCellScheme.scope x = U :=
      (congrArg Prod.fst (Scheme.gradedIndex_mirror_castAdd
        (hmix := I.not_subset_scope_tower g H Γ A B') x)).symm.trans (congrArg Prod.fst hz)
    have hne : (𝕋).toCellScheme.scope x ≠ univ := hs ▸ ((I.mem_mixedFaces g).mp hU).2.1
    exact I.not_subset_scope_tower g H Γ A B' x hne U hU (hs ▸ subset_rfl)
  | right j =>
    set q := ((𝕋).copyEquiv (I.mixedFaces g)).symm j with hq
    have hj : j = (𝕋).copyEquiv (I.mixedFaces g) q := by rw [hq, Equiv.apply_symm_apply]
    obtain ⟨⟨U', f⟩, hU', hf, hfg⟩ := q
    have hsU : U' = U := by
      have h := congrArg Prod.fst hz
      change (𝕋).mirrorScope (I.mixedFaces g) (Fin.natAdd _ j) = U at h
      rw [Scheme.mirrorScope_natAdd, ← hq] at h
      exact h
    subst hsU
    have hfk : (𝕋).toCellScheme.grade f = k := by
      have h := congrArg Prod.snd hz
      change (𝕋).toCellScheme.grade ((𝕋).mirrorOrig (I.mixedFaces g) (Fin.natAdd _ j)) = k at h
      rw [Scheme.mirrorOrig_natAdd, ← hq] at h
      exact h
    exact ⟨f, Prod.ext hf hfk, by rw [hj]; rfl⟩

/-- **The labelling at a cell at a mixed face is at most the maximal copy at its grade**: in a
section lawful below `(U, j)`, every cell below `(U, j)` of grade `k` carries at most the label of
a copy at `U` of grade `k` maximal among them. -/
theorem le_max_copy (hU : U ∈ I.mixedFaces g) {j : ℕ} {P : Fin (𝔼).card → Label.{u}}
    (hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d) {k : ℕ} (hkj : k ≤ j) (hkU : k ≤ #U)
    {u : Fin (𝕋).card} (hu : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k))
    (hmax : ∀ w (hw : (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)),
      P (copyFull H Γ A B' hU w hw hkU) ≤ P (copyFull H Γ A B' hU u hu hkU))
    {d : Fin (𝔼).card} (hd : d ∈ (𝔼).toCellScheme.below (U, j))
    (hdk : (𝔼).toCellScheme.grade d = k) : P d ≤ P (copyFull H Γ A B' hU u hu hkU) := by
  obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hP
  have hcu : copyFull H Γ A B' hU u hu hkU ∈ (𝔼).toCellScheme.below (U, j) := by
    rw [CellScheme.mem_below, gradedIndex_copyFull]; exact ⟨subset_rfl, hkj⟩
  obtain ⟨z, hz, hle⟩ := havail d _ hcu
    (hd.1.trans (le_of_eq (congrArg Prod.fst (gradedIndex_copyFull hU u hu hkU)).symm))
    (hdk.trans (congrArg Prod.snd (gradedIndex_copyFull hU u hu hkU)).symm)
  obtain ⟨v, hv, rfl⟩ := exists_eq_copyFull hU hkU z (hz.trans (gradedIndex_copyFull hU u hu hkU))
  exact hle.trans (hmax v hv)

end Seed

namespace Label

end Label

end VaughtConjecture

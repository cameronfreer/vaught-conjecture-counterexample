/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerTwins
import VaughtConjecture.Extension.ReplicatedForcing

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
      (H := H) (Γ := Γ) (A := A) (B' := B') hcard hA (K - 2) m (by omega) f hf'
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

end Seed

end VaughtConjecture

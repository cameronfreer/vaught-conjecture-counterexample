/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedMixedLiftFromMirror

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

**The proofs.**  The replicated scheme is the ladder tower over the attachment mirrored at the
mixed faces, so each statement here is the statement for a mirrored scheme
(`VaughtConjecture.MainTheorem.MirrorMixedCopies`,
`VaughtConjecture.MainTheorem.MirrorMixedDecode`) specialized to the tower, whose hypotheses it
meets (`VaughtConjecture.Extension.ReplicatedMixedLiftFromMirror`).

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
  mCopyFull (I.not_subset_scope_tower g H Γ A B') hU v hv hk

theorem mirrorOrig_copyFull (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    (𝕋).mirrorOrig (I.mixedFaces g) (copyFull H Γ A B' hU v hv hk) = v :=
  mirrorOrig_mCopyFull hU v hv hk

theorem gradedIndex_copyFull (hU : U ∈ I.mixedFaces g) (v : Fin (𝕋).card) {k : ℕ}
    (hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    (𝔼).toCellScheme.gradedIndex (copyFull H Γ A B' hU v hv hk) = (U, k) :=
  gradedIndex_mCopyFull hU v hv hk

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
      min (P (copyFull H Γ A B' hU w hw (hkK.trans hKU))) (P (copyFull H Γ A B' hU v hv hKU)) :=
  decode_mCopyFull (hmix := I.not_subset_scope_tower g H Γ A B') hU hv hKU hθ hw hkK

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
  have _ := hKm
  exact min_decode_eq_decode_m (hmix := I.not_subset_scope_tower g H Γ A B') hU
    gradedIndex_ladCell (attachTower_agree_shadow hcard) (attachTower_twin hcard hΓ hA) hk2 hkK
    hKU hf hu hmax hθf_mono hθf_le hθf hθu he

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
  have _ := hKm
  exact exists_mladder_reading attachTower_rowAt_lad_lad
    (fun p _ he ↦ rowAt_ladCell_baseCellEmb p he) attachTower_eq_ladCell
    (attachTower_reads_ladder hcard) hK1 hf

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
  have _ := hKm
  exact min_decode_eq_decode_one_m (hmix := I.not_subset_scope_tower g H Γ A B') hU hH
    gradedIndex_ladCell attachTower_rowAt_lad_lad (fun p _ he ↦ rowAt_ladCell_baseCellEmb p he)
    attachTower_eq_ladCell (attachTower_reads_ladder hcard) hK1 hKU hf a hmax hθf_mono hθf_le hθf
    hθ1 he

/-! ### The cells at a mixed face -/

/-- **The cells at a mixed face are copies**: a cell of the replicated scheme at `(U, k)`, for a
mixed face `U`, is the copy at `U` of a cell of full scope of the tower at the grade `k`. -/
theorem exists_eq_copyFull (hU : U ∈ I.mixedFaces g) {k : ℕ} (hkU : k ≤ #U)
    (z : Fin (𝔼).card) (hz : (𝔼).toCellScheme.gradedIndex z = (U, k)) :
    ∃ v, ∃ hv : (𝕋).toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k),
      z = copyFull H Γ A B' hU v hv hkU :=
  exists_eq_mCopyFull (hmix := I.not_subset_scope_tower g H Γ A B') hU hkU z hz

/-- **The labelling at a cell at a mixed face is at most the maximal copy at its grade**: in a
section lawful below `(U, j)`, every cell below `(U, j)` of grade `k` carries at most the label of
a copy at `U` of grade `k` maximal among them. -/
theorem le_max_copy (hU : U ∈ I.mixedFaces g) {j : ℕ} {P : Fin (𝔼).card → Label.{u}}
    (hP : (𝔼).rows.IsLawfulBelow (U, j) fun d ↦ P d) {k : ℕ} (hkj : k ≤ j) (hkU : k ≤ #U)
    {u : Fin (𝕋).card} (hu : (𝕋).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k))
    (hmax : ∀ w (hw : (𝕋).toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)),
      P (copyFull H Γ A B' hU w hw hkU) ≤ P (copyFull H Γ A B' hU u hu hkU))
    {d : Fin (𝔼).card} (hd : d ∈ (𝔼).toCellScheme.below (U, j))
    (hdk : (𝔼).toCellScheme.grade d = k) : P d ≤ P (copyFull H Γ A B' hU u hu hkU) :=
  le_max_mCopy (hmix := I.not_subset_scope_tower g H Γ A B') hU hP hkj hkU hu hmax hd hdk

end Seed

end VaughtConjecture

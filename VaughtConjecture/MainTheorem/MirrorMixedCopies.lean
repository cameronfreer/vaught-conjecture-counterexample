/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachmentMirror

/-!
# Copies at a mixed face of a mirrored scheme over the attachment

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces, for any scheme over the attachment
mirrored at the mixed faces of the seed).

Let `T` be a scheme on the points of the amalgam, mirrored at the mixed faces of the seed
(`Scheme.mirror`, no mixed face inside the scope of a cell of proper scope), and `U` a mixed face.

* **The copies** (`Seed.mCopy`): the copy at `U` of a cell of full scope of `T` of grade at most
  `|U|`, of graded index `(U, grade)` (`Seed.gradedIndex_mCopy`); it reads the cells below it as its
  original reads their originals (`Scheme.rowAt_mirror_of_mem`).  A capped decoder at a copy reads
  the row of the original at a cell of full scope as the labelling at the copy of that cell
  (`Seed.decode_mCopyFull`); the cells at `(U, k)` are copies (`Seed.exists_eq_mCopyFull`); a
  lawful section carries at every cell of grade `k` below `(U, j)` at most the label of a copy at
  `U` of grade `k` maximal among them (`Seed.le_max_mCopy`).
* **The cells** (`Seed.mirror_cell_cases`): a cell has an original of full scope at its grade, or
  is a cell of `T` of proper scope.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {T : Scheme.{u} (m + 2)}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ I.mixedFaces g, ¬ U ⊆ T.toCellScheme.scope c}
  {U : Finset (Fin (m + 2))}

variable (hmix) in
/-- **The copy at the mixed face `U`** of a cell of full scope of `T` of grade at most `|U|`. -/
noncomputable def mCopy (hU : U ∈ I.mixedFaces g) (v : Fin T.card)
    (hv : T.toCellScheme.scope v = univ) (hk : T.toCellScheme.grade v ≤ #U) :
    Fin (Scheme.mirror hmix).card :=
  Fin.natAdd _ (T.copyEquiv (I.mixedFaces g) ⟨(U, v), hU, hv, hk⟩)

theorem mirrorOrig_mCopy (hU : U ∈ I.mixedFaces g) (v : Fin T.card)
    (hv : T.toCellScheme.scope v = univ) (hk : T.toCellScheme.grade v ≤ #U) :
    T.mirrorOrig (I.mixedFaces g) (mCopy hmix hU v hv hk) = v := by
  rw [mCopy, Scheme.mirrorOrig_natAdd, Equiv.symm_apply_apply]

theorem gradedIndex_mCopy (hU : U ∈ I.mixedFaces g) (v : Fin T.card)
    (hv : T.toCellScheme.scope v = univ) (hk : T.toCellScheme.grade v ≤ #U) :
    (Scheme.mirror hmix).toCellScheme.gradedIndex (mCopy hmix hU v hv hk) =
      (U, T.toCellScheme.grade v) := by
  change (T.mirrorScope (I.mixedFaces g) _,
    T.toCellScheme.grade (T.mirrorOrig (I.mixedFaces g) _)) = _
  rw [mCopy, Scheme.mirrorScope_natAdd, Scheme.mirrorOrig_natAdd, Equiv.symm_apply_apply]

variable (hmix) in
/-- The copy at `U` of a cell of graded index `(univ, k)`, `k ≤ |U|`. -/
noncomputable def mCopyFull (hU : U ∈ I.mixedFaces g) (v : Fin T.card) {k : ℕ}
    (hv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    Fin (Scheme.mirror hmix).card :=
  mCopy hmix hU v (congrArg Prod.fst hv) ((congrArg Prod.snd hv).trans_le hk)

theorem mirrorOrig_mCopyFull (hU : U ∈ I.mixedFaces g) (v : Fin T.card) {k : ℕ}
    (hv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    T.mirrorOrig (I.mixedFaces g) (mCopyFull hmix hU v hv hk) = v :=
  mirrorOrig_mCopy hU _ _ _

theorem gradedIndex_mCopyFull (hU : U ∈ I.mixedFaces g) (v : Fin T.card) {k : ℕ}
    (hv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k)) (hk : k ≤ #U) :
    (Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU v hv hk) = (U, k) :=
  (gradedIndex_mCopy hU _ _ _).trans
    (Prod.ext rfl (show T.toCellScheme.grade v = k from congrArg Prod.snd hv))

/-- **A decoder at a copy reads the row of the original at a cell of full scope** as the labelling
at the copy of that cell, capped. -/
theorem decode_mCopyFull (hU : U ∈ I.mixedFaces g) {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    {v : Fin T.card} {K : ℕ}
    (hv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), K)) (hKU : K ≤ #U)
    {θ : Label.{u} → Label.{u}}
    (hθ : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU v hv hKU)),
      θ ((Scheme.mirror hmix).rowAt (mCopyFull hmix hU v hv hKU) d) =
        min (P d) (P (mCopyFull hmix hU v hv hKU)))
    {w : Fin T.card} {k : ℕ}
    (hw : T.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)) (hkK : k ≤ K) :
    θ (T.rowAt v w) =
      min (P (mCopyFull hmix hU w hw (hkK.trans hKU))) (P (mCopyFull hmix hU v hv hKU)) := by
  have hmem : mCopyFull hmix hU w hw (hkK.trans hKU) ∈ (Scheme.mirror hmix).toCellScheme.below
      ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU v hv hKU)) := by
    rw [CellScheme.mem_below, gradedIndex_mCopyFull, gradedIndex_mCopyFull]
    exact ⟨subset_rfl, hkK⟩
  rw [← hθ _ hmem, Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_mCopyFull, mirrorOrig_mCopyFull]

/-- **The cells at a mixed face are copies**: a cell of the mirrored scheme at `(U, k)` is the copy
at `U` of a cell of full scope of `T` at the grade `k`. -/
theorem exists_eq_mCopyFull (hU : U ∈ I.mixedFaces g) {k : ℕ} (hkU : k ≤ #U)
    (z : Fin (Scheme.mirror hmix).card)
    (hz : (Scheme.mirror hmix).toCellScheme.gradedIndex z = (U, k)) :
    ∃ v, ∃ hv : T.toCellScheme.gradedIndex v = ((univ : Finset (Fin (m + 2))), k),
      z = mCopyFull hmix hU v hv hkU := by
  change Fin (T.card + T.copyCount (I.mixedFaces g)) at z
  induction z using Fin.addCases with
  | left x =>
    exfalso
    have hs : T.toCellScheme.scope x = U :=
      (congrArg Prod.fst (Scheme.gradedIndex_mirror_castAdd (hmix := hmix) x)).symm.trans
        (congrArg Prod.fst hz)
    have hne : T.toCellScheme.scope x ≠ univ := hs ▸ ((I.mem_mixedFaces g).mp hU).2.1
    exact hmix x hne U hU (hs ▸ subset_rfl)
  | right j =>
    set q := (T.copyEquiv (I.mixedFaces g)).symm j with hq
    have hj : j = T.copyEquiv (I.mixedFaces g) q := by rw [hq, Equiv.apply_symm_apply]
    obtain ⟨⟨U', f⟩, hU', hf, hfg⟩ := q
    have hsU : U' = U := by
      have h := congrArg Prod.fst hz
      change T.mirrorScope (I.mixedFaces g) (Fin.natAdd _ j) = U at h
      rw [Scheme.mirrorScope_natAdd, ← hq] at h
      exact h
    subst hsU
    have hfk : T.toCellScheme.grade f = k := by
      have h := congrArg Prod.snd hz
      change T.toCellScheme.grade (T.mirrorOrig (I.mixedFaces g) (Fin.natAdd _ j)) = k at h
      rw [Scheme.mirrorOrig_natAdd, ← hq] at h
      exact h
    exact ⟨f, Prod.ext hf hfk, by rw [hj]; rfl⟩

/-- **The labelling at a cell below `(U, j)` is at most the maximal copy at its grade.** -/
theorem le_max_mCopy (hU : U ∈ I.mixedFaces g) {j : ℕ}
    {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hP : (Scheme.mirror hmix).rows.IsLawfulBelow (U, j) fun d ↦ P d) {k : ℕ} (hkj : k ≤ j)
    (hkU : k ≤ #U) {u : Fin T.card}
    (hu : T.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k))
    (hmax : ∀ w (hw : T.toCellScheme.gradedIndex w = ((univ : Finset (Fin (m + 2))), k)),
      P (mCopyFull hmix hU w hw hkU) ≤ P (mCopyFull hmix hU u hu hkU))
    {d : Fin (Scheme.mirror hmix).card} (hd : d ∈ (Scheme.mirror hmix).toCellScheme.below (U, j))
    (hdk : (Scheme.mirror hmix).toCellScheme.grade d = k) :
    P d ≤ P (mCopyFull hmix hU u hu hkU) := by
  obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hP
  have hcu : mCopyFull hmix hU u hu hkU ∈ (Scheme.mirror hmix).toCellScheme.below (U, j) := by
    rw [CellScheme.mem_below, gradedIndex_mCopyFull]; exact ⟨subset_rfl, hkj⟩
  obtain ⟨z, hz, hle⟩ := havail d _ hcu
    (hd.1.trans (le_of_eq (congrArg Prod.fst (gradedIndex_mCopyFull hU u hu hkU)).symm))
    (hdk.trans (congrArg Prod.snd (gradedIndex_mCopyFull hU u hu hkU)).symm)
  obtain ⟨v, hv, rfl⟩ := exists_eq_mCopyFull hU hkU z (hz.trans (gradedIndex_mCopyFull hU u hu hkU))
  exact hle.trans (hmax v hv)

/-- **The cells of the mirrored scheme**: a cell has an original of full scope at its grade (a cell
of full scope of `T` or a copy), or is a cell of `T` of proper scope. -/
theorem mirror_cell_cases (z : Fin (Scheme.mirror hmix).card) :
    (∃ v, T.mirrorOrig (I.mixedFaces g) z = v ∧
        T.toCellScheme.gradedIndex v =
          ((univ : Finset (Fin (m + 2))), (Scheme.mirror hmix).toCellScheme.grade z)) ∨
      ∃ x, z = Fin.castAdd _ x ∧ T.toCellScheme.scope x ≠ univ := by
  change Fin (T.card + T.copyCount (I.mixedFaces g)) at z
  induction z using Fin.addCases with
  | left x =>
    by_cases hx : T.toCellScheme.scope x = univ
    · left
      refine ⟨x, Scheme.mirrorOrig_castAdd _ _ x, Prod.ext hx ?_⟩
      exact (congrArg Prod.snd (Scheme.gradedIndex_mirror_castAdd (hmix := hmix) x)).symm
    · exact .inr ⟨x, rfl, hx⟩
  | right j =>
    left
    refine ⟨_, rfl, Prod.ext ?_ rfl⟩
    rw [Scheme.mirrorOrig_natAdd]
    exact ((T.copyEquiv (I.mixedFaces g)).symm j).2.2.1

end Seed

end VaughtConjecture

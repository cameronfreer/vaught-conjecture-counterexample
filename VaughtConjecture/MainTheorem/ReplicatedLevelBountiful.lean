/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelControl

/-!
# Bountifulness of a replicated level from its lifts into the mixed faces

Roadmap, Layer 3 ((R3) and (R4), the lifts of the levels re-rendered per grade).

For a good level with its copies at the mixed faces (`Seed.ALvl.Good.rep`):

* **The attachment is a lower embedding** into the replicated level, keeping scopes and rows
  (`Seed.ALvl.Good.isLowerEmbedding_repEmb`, `Seed.ALvl.Good.comap_rows_repEmb`); every cell of
  scope inside the context face or the donor face is a cell of the attachment
  (`Seed.ALvl.Good.mem_range_repEmb`).  So below a pair whose face lies in the context face or the
  donor face the replicated level lifts capped as the amalgam does
  (`Seed.ALvl.Good.cappedLift_rep_of_subset`).
* **The context lift at every grade** (`Seed.lvLevel_cappedLift_grade`): the level at the grade
  `j + 1` lifts capped from the context coatom into `(univ, k)` for every `1 ≤ k ≤ j + 1` (the lift
  at the grade `k` of the level at the grade `k`, `Seed.lvLevel_cappedLift'`, carried up the levels
  by `Seed.ALvl.cappedLift_nS_iff`); so does the replicated level
  (`Seed.ALvl.Good.cappedLift_rep`).
* **Bountifulness from two lifts** (`Seed.lvRep_isBountiful_of_lifts`): the replicated top level
  (the grade `m + 1`) is bountiful given (i) the capped lifts into the mixed faces and (ii) the
  lifts from the second coatom (the points other than `m`) into the full face at the grades
  `1, …, m + 1`.  The context lift is proved; the premises `hQ`, `hpair`, `hrel`, `hdL`, `0 < n` of
  the context lift stay explicit.

Both premises are proved for the replicated top level in
`VaughtConjecture.MainTheorem.ReplicatedLevelBountifulTop` (`Seed.lvRep_isBountiful`): (i) by the
lift from a mixed face of a mirrored scheme (`Seed.cappedLift_mirror_mixed_face`, as
`Seed.lvRep_cappedLift_mixed_univ` and `Seed.lvRep_cappedLift_mixed_mixed`), (ii) by the same lift
or, at an onto root, by the lift from the donor face
(`Seed.lvLevel_cappedLift_coatom_of_surjective`).

**Copies are never controllers**: a cell of full scope of the replicated level is a cell of the
level, with its graded index and its readings of the cells of the level
(`Seed.ALvl.Good.exists_castAdd_of_scope_univ`), so the ladder-controller clauses of the level
(`Seed.lvLevel_ladderController`) are those of the replicated level.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

namespace ALvl.Good

variable {j : ℕ} {N : I.ALvl g H j} (hN : N.Good B (lvAdm hd Q))
include hN

/-- A good level reads the cells of the attachment as the attachment does. -/
theorem rowAt_attEmb (s t : Fin (I.attachment g).card) :
    N.S.rowAt (N.attEmb s) (N.attEmb t) = (I.attachment g).rowAt s t := by
  have hiff : N.attEmb t ∈ N.S.toCellScheme.below (N.S.toCellScheme.gradedIndex (N.attEmb s)) ↔
      t ∈ (I.attachment g).toCellScheme.below ((I.attachment g).toCellScheme.gradedIndex s) := by
    rw [CellScheme.mem_below, CellScheme.mem_below, hN.gradedIndex_attEmb, hN.gradedIndex_attEmb]
  by_cases ht :
      t ∈ (I.attachment g).toCellScheme.below ((I.attachment g).toCellScheme.gradedIndex s)
  · rw [Scheme.rowAt_of_mem (hiff.mpr ht), Scheme.rowAt_of_mem ht]
    have h := congrArg (fun R : (I.attachment g).toCellScheme.Rows ↦ R.row s ⟨t, ht⟩) hN.comap_rows
    simp only [CellScheme.Rows.comap_row] at h
    exact h
  · rw [Scheme.rowAt_of_notMem (mt hiff.mp ht), Scheme.rowAt_of_notMem ht]

/-- The cell of the replicated level of a cell of the attachment. -/
noncomputable def repEmb (c : Fin (I.attachment g).card) : Fin hN.rep.card :=
  Fin.castAdd _ (N.attEmb c)

theorem gradedIndex_repEmb (c : Fin (I.attachment g).card) :
    hN.rep.toCellScheme.gradedIndex (hN.repEmb c) = (I.attachment g).toCellScheme.gradedIndex c :=
  (Scheme.gradedIndex_mirror_castAdd (hmix := hN.not_subset_scope) _).trans
    (hN.gradedIndex_attEmb c)

/-- **The cells of the replicated level of scope inside the context face or the donor face are
cells of the attachment**: a copy has a mixed scope, and an old cell of proper scope is a cell of
the attachment. -/
theorem mem_range_repEmb (z : Fin hN.rep.card)
    (hz : hN.rep.toCellScheme.scope z ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      hN.rep.toCellScheme.scope z ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    z ∈ Set.range hN.repEmb := by
  change Fin (N.S.card + N.S.copyCount (I.mixedFaces g)) at z
  induction z using Fin.addCases with
  | right i =>
    exfalso
    have hU := (I.mem_mixedFaces g).mp
      (show hN.rep.toCellScheme.scope (Fin.natAdd _ i) ∈ I.mixedFaces g by
        rw [Scheme.scope_mirror_natAdd]; exact ((N.S.copyEquiv _).symm i).2.1)
    exact hz.elim hU.2.2.1 hU.2.2.2
  | left z =>
    have hsc : hN.rep.toCellScheme.scope (Fin.castAdd _ z) = N.S.toCellScheme.scope z :=
      congrArg Prod.fst (Scheme.gradedIndex_mirror_castAdd (hmix := hN.not_subset_scope) _)
    have hne : N.S.toCellScheme.scope z ≠ univ := fun he ↦ by
      rw [hsc, he] at hz
      rcases hz with h | h
      · exact map_castSuccEmb_ne_univ (univ_subset_iff.mp h)
      · exact map_extendByLast_ne_univ g (univ_subset_iff.mp h)
    obtain ⟨c, rfl⟩ := hN.mem_range z hne
    exact ⟨c, rfl⟩

/-- **The attachment is a lower embedding into the replicated level.** -/
theorem isLowerEmbedding_repEmb :
    (I.attachment g).toCellScheme.IsLowerEmbedding hN.rep.toCellScheme hN.repEmb where
  injective a b hab := hN.lowerEmb.injective (Fin.castAdd_injective _ _ hab)
  grade_eq c := congrArg Prod.snd (hN.gradedIndex_repEmb c)
  le_iff s t := by rw [hN.gradedIndex_repEmb, hN.gradedIndex_repEmb]
  mem_range t z hz := by
    rw [hN.gradedIndex_repEmb] at hz
    exact hN.mem_range_repEmb z ((I.scope_attachment g t).imp (fun h ↦ hz.1.trans h)
      fun h ↦ hz.1.trans h)

theorem rowAt_repEmb (s t : Fin (I.attachment g).card) :
    hN.rep.rowAt (hN.repEmb s) (hN.repEmb t) = (I.attachment g).rowAt s t :=
  (Scheme.rowAt_mirror_castAdd _ _).trans (hN.rowAt_attEmb s t)

/-- **The rows of the replicated level pull back to those of the attachment.** -/
theorem comap_rows_repEmb :
    hN.rep.rows.comap hN.isLowerEmbedding_repEmb = (I.attachment g).rows := by
  ext s t
  rw [CellScheme.Rows.comap_row]
  have h := hN.rowAt_repEmb s t.1
  rw [Scheme.rowAt_of_mem, Scheme.rowAt_of_mem t.2] at h
  exact h

/-- **Below a pair whose face lies in the context face or the donor face, the replicated level
lifts capped**: there it is the attachment, which is the amalgam. -/
theorem cappedLift_rep_of_subset (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ hN.rep.toCellScheme.gradedFaces) (hY : Y ∈ hN.rep.toCellScheme.gradedFaces)
    (h : X ≤ Y)
    (hYc : Y.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      Y.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    hN.rep.rows.CappedLift h := by
  have hpre : (I.attachment g).toCellScheme.IsSourcePrefix hN.rep.toCellScheme hN.repEmb Y :=
    ⟨hN.isLowerEmbedding_repEmb, fun c ↦ congrArg Prod.fst (hN.gradedIndex_repEmb c),
      fun z hz ↦ hN.mem_range_repEmb z (hYc.imp (fun h' ↦ hz.1.trans h') fun h' ↦ hz.1.trans h')⟩
  have hpreA : (I.attachment g).toCellScheme.IsSourcePrefix I.amalgam.toCellScheme
      (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)) Y :=
    ⟨Scheme.isLowerEmbedding_lowerEmb _ _ (I.attachmentCells_lower g), fun _ ↦ rfl,
      fun c hc ↦ by
        have hcL : c ∈ I.attachmentCells g := (I.mem_attachmentCells g).mpr
          (hYc.imp (fun h' ↦ hc.1.trans h') fun h' ↦ hc.1.trans h')
        have h' := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hcL)
        exact h'⟩
  have hgf {Z : Finset (Fin (m + 2)) × ℕ} (hZ : Z ∈ hN.rep.toCellScheme.gradedFaces) :
      Z ∈ I.amalgam.toCellScheme.gradedFaces := ⟨hfaces ▸ hZ.1, hZ.2⟩
  rw [← hpre.cappedLift_iff h le_rfl, hN.comap_rows_repEmb]
  exact (hpreA.cappedLift_iff (R := I.amalgam.rows) h le_rfl).mpr
    (I.isBountiful (hgf hX) (hgf hY) h)

/-- **A cell of full scope of the replicated level is a cell of the level**, with its graded index;
it reads the cells of the level as the level does (`Scheme.rowAt_mirror_castAdd`). -/
theorem exists_castAdd_of_scope_univ (u : Fin hN.rep.card)
    (hu : hN.rep.toCellScheme.scope u = univ) :
    ∃ u' : Fin N.S.card, u = Fin.castAdd _ u' ∧
      hN.rep.toCellScheme.gradedIndex u = N.S.toCellScheme.gradedIndex u' := by
  change Fin (N.S.card + N.S.copyCount (I.mixedFaces g)) at u
  induction u using Fin.addCases with
  | right i =>
    exfalso
    have hU := (I.mem_mixedFaces g).mp
      (show hN.rep.toCellScheme.scope (Fin.natAdd _ i) ∈ I.mixedFaces g by
        rw [Scheme.scope_mirror_natAdd]; exact ((N.S.copyEquiv _).symm i).2.1)
    exact hU.2.1 hu
  | left u' => exact ⟨u', rfl, Scheme.gradedIndex_mirror_castAdd (hmix := hN.not_subset_scope) u'⟩

end ALvl.Good

/-- **The context lift at every grade of a level**: the level at the grade `j + 1` lifts capped
from the context coatom into `(univ, k)` for every `1 ≤ k ≤ j + 1`, under the premises of
`Seed.lvLevel_cappedLift'` (kept explicit). -/
theorem lvLevel_cappedLift_grade (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j k, 1 ≤ k → k ≤ j + 1 → j + 1 ≤ m + 1 →
      (I.lvLevel g H B hd Q j).S.rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩
  | j, k, hk1, hkj, hjm => by
    rcases Nat.lt_or_ge k (j + 1) with hlt | hge
    · cases j with
      | zero => omega
      | succ j =>
        have hlow := lvLevel_cappedLift_grade hH hcard hdp hdL hn hQ hpair hrel hB j k hk1
          (by omega) (by omega)
        exact (ALvl.cappedLift_nS_iff (B := B) (I.lvLevel g H B hd Q j)
          (I.lvCat g B hd Q (j + 2)) _ fun h ↦ absurd h.2 (by simp only; omega)).mpr hlow
    · obtain rfl : k = j + 1 := by omega
      exact Seed.lvLevel_cappedLift' hH hcard hte hdp hdL hn hd hQ hpair hrel hB j hjm

/-- **The replicated top level is bountiful given two lifts**: the capped lifts into the mixed
faces (`hmixed`) and the lifts from the second coatom into the full face (`hsecond`).  Below the
faces inside the context face or the donor face it is the amalgam; the context lift is proved at
every grade (`Seed.lvLevel_cappedLift_grade`, under the explicit premises `hQ`, `hpair`, `hrel`,
`hdL`, `0 < n`). -/
theorem lvRep_isBountiful_of_lifts (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) (hB : 2 * (I.attachment g).card ≤ B)
    (hN : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q))
    (hmixed : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄, X ∈ hN.rep.toCellScheme.gradedFaces →
      Y ∈ hN.rep.toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ∈ I.mixedFaces g →
      hN.rep.rows.CappedLift h)
    (hsecond : ∀ k, 1 ≤ k → k ≤ m + 1 →
      hN.rep.rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last m)), k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩) :
    hN.rep.rows.IsBountiful := by
  classical
  have hfaces := faces_lvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hproper : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄, X ∈ hN.rep.toCellScheme.gradedFaces →
      Y ∈ hN.rep.toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ≠ univ →
      hN.rep.rows.CappedLift h := by
    intro X Y hX hY h hYu
    by_cases hYc : Y.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        Y.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))
    · exact hN.cappedLift_rep_of_subset hfaces hX hY h hYc
    · push Not at hYc
      exact hmixed hX hY h ((I.mem_mixedFaces g).mpr ⟨hfaces ▸ hY.1, hYu, hYc.1, hYc.2⟩)
  have hwf := hN.isWellFormed_rep hfaces
  have hzero (x : Fin (m + 2)) : hN.rep.rows.CappedLift (X := (univ.erase x, 0))
      (Y := ((univ : Finset (Fin (m + 2))), 0)) ⟨erase_subset _ _, le_rfl⟩ := by
    refine CellScheme.Rows.cappedLift_of_below_eq_empty ?_ _
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hz
    have h1 : hN.rep.toCellScheme.grade z ≤ 0 := hz.2
    have h2 := hwf.isWellFormed.grade_pos z
    omega
  have hfull (x : Fin (m + 2)) (hx : x = Fin.last (m + 1) ∨ x = Fin.castSucc (Fin.last m)) :
      ∀ k ≤ #(univ.erase x), hN.rep.rows.CappedLift (X := (univ.erase x, k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩ := by
    intro k hk
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact hzero x
    rcases hx with rfl | rfl
    · exact hN.cappedLift_rep _ rfl subset_rfl
        (lvLevel_cappedLift_grade hH hcard hdp hdL hn hQ hpair hrel hB m k hk1 (by omega) le_rfl)
    · exact hsecond k hk1 (by omega)
  have hleftF : univ.erase (Fin.last (m + 1)) ∈ hN.rep.toCellScheme.faces := by
    change _ ∈ (I.lvLevel g H B hd Q m).S.toCellScheme.faces
    rw [hfaces, ← Coatom.univ_map_left]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hrightF : univ.erase (Fin.castSucc (Fin.last m)) ∈ hN.rep.toCellScheme.faces := by
    change _ ∈ (I.lvLevel g H B hd Q m).S.toCellScheme.faces
    rw [hfaces, ← Coatom.univ_map_right]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (mem_univ (Fin.last (m + 1)))
    (mem_univ (Fin.castSucc (Fin.last m))) (fun B' hB' hBu ↦ ?_) hleftF hrightF hproper
    (hfull _ (.inl rfl)) (hfull _ (.inr rfl))
  exact I.subset_or_subset B' (hfaces ▸ hB') hBu

end Seed

end VaughtConjecture

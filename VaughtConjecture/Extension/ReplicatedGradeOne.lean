/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthCappedDecoder
import VaughtConjecture.Extension.ReplicatedCopies

/-!
# The lift from a mixed face into the full face at the grade one

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

Below `(univ, 1)` the replicated scheme over the attachment has the cells of grade one of the
attachment, the ladder points, and their copies at the mixed faces.  A section lawful below a
mixed face `U` at the grade one is, on the copied ladder at `U`, `⊥` or the chart image of the table
of one member `a` (`Seed.copyLadder_exists_shape`).  Its copied top rung `T'` dominates every cell
below `(U, 1)`, and the **capped decoder** `θ` of the section at `T'`
(`Scheme.exists_cappedDecoder_below`) reads the row of `T'` as the section.

**The lift** (`Seed.cappedLift_mixed_univ_one`).  The row `ρ` of the ORIGINAL top rung of `a` is
lawful below `(univ, 1)` (consistency); its decoding `θ ∘ ρ` has the bottom pattern of `ρ` (every
value of `ρ` is a code of an index, read at a copied ladder point, `⊥` exactly at the index `0`), so
it is lawful (`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`).  It is the section below `(U, 1)`,
and it keeps the observation of every ambient at the cap: every value of `ρ` is its value at a
copied ladder point (`Seed.exists_rowAt_eq_copyLadder`: a cell of grade one of the attachment is
read as the shadow of `a` at that cell), and the ambient reads alike two cells at which `ρ` agrees,
up to its value at the original top rung.  In particular the context cells outside `U` receive the
values of the copied shadows of `a`.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

/-! ### Generic facts -/

variable {n : ℕ} {S : Scheme.{u} n}

/-- **The capped decoder of a section lawful below a pair**, at a cell `c` below the pair of grade
`N`: a witness bounded by `N`, bounded by the label of `c`, reading the row of `c` as the section
capped at `c` (`Scheme.exists_cappedDecoder_isWitness` for sections lawful below a pair). -/
theorem exists_cappedDecoder_below {Y : Finset (Fin n) × ℕ} {w : Fin S.card → Label.{u}}
    (hw : S.rows.IsLawfulBelow Y fun d ↦ w d) {c : Fin S.card}
    (hcY : c ∈ S.toCellScheme.below Y) {N : ℕ} (hcN : S.toCellScheme.grade c = N) :
    ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor N) θ ∧ (∀ x, θ x ≤ w c) ∧
      ∀ d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c),
        θ (S.rowAt c d) = min (w d) (w c) := by
  obtain ⟨hord, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, hwit, hq⟩ := hloc c hcY
  have hcb : c ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex c) :=
    CellScheme.mem_below_gradedIndex _ c
  have hvc : IsSelfVisible N (w c) := hcN ▸ hord c hcY
  have hqc := hq ⟨c, hcb⟩
  simp only [min_self] at hqc
  rw [hcN] at hqc
  have hvcg : w c ≤ g N := hqc ▸ min_le_right _ _
  refine ⟨fun x ↦ min (min (σ x) (g N)) (w c),
    ⟨(IsWitness.id_step N).antitone, (IsWitness.id_step N).isSelfVisible, by simp [hwit.map_bot],
      fun x y hxy ↦ min_le_min_right _ (min_le_min_right _ (hwit.monotone hxy)),
      fun x k hx i hi ↦ ?_⟩, fun x ↦ min_le_right _ _, fun d hd ↦ ?_⟩
  · by_cases hk : k ≤ N
    · rw [hwit.min_visibilityReplace_of_le hk hi,
        visibilityReplace_min_of_isSelfVisible hi (hvc.mono hk)]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]
      rcases min_eq_bot.mp hx with h | h
      · rcases min_eq_bot.mp h with h' | h'
        · rw [hwit.apply_visibilityReplace_eq_bot h' k hi]; simp
        · rw [h']; simp
      · rw [h]; simp
  · have hqd := hq ⟨d, hd⟩
    simp only at hqd
    rw [← rowAt_of_mem hd] at hqd
    have hgd : g N ≤ g (S.toCellScheme.grade d) := by
      apply hwit.antitone
      have := hd.2
      simp only [CellScheme.gradedIndex_snd] at this
      rw [hcN] at this
      exact this
    have hle : min (w d) (w c) ≤ g N := (min_le_right _ _).trans hvcg
    have h1 : min (σ (S.rowAt c d)) (g N) = min (w d) (w c) := by
      apply le_antisymm
      · rw [hqd]
        exact le_min (min_le_left _ _) ((min_le_right _ _).trans hgd)
      · rw [hqd] at hle ⊢
        exact le_min (min_le_left _ _) hle
    beta_reduce
    rw [h1, min_assoc, min_self]

variable {Q : Type} [Fintype Q] {H : ℕ} {prof : Q → Fin S.card → ℕ}

/-- **A ladder point reads an old cell of grade one** through the code, at its ceiling, of the rank
of the cell for its member. -/
theorem rowAt_ladderBase_old {hS : S.NoFullOne} (hwf : S.IsWellFormed) (p : LadderPt S Q H)
    {e : Fin S.card} (he : S.toCellScheme.grade e = 1) :
    (ladderBase H prof hS).rowAt (Fin.natAdd _ (ladderEquiv S Q H p)) (Fin.castAdd _ e) =
      ladderSource (ladderCeil prof p) (prof p.1 e) := by
  have hq : (Fin.castAdd _ e : Fin (S.card + ladderCard S Q H)) ∈
      (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    change (S.appendFullCellsScheme 1 _).gradedIndex _ ≤ _
    rw [appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, he.le⟩
  have hmem : (Fin.castAdd _ e : Fin (S.card + ladderCard S Q H)) ∈
      (ladderBase H prof hS).toCellScheme.below
        ((ladderBase H prof hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (ladderEquiv S Q H p))) := by
    change (S.appendFullCellsScheme 1 _).gradedIndex _ ≤ (S.appendFullCellsScheme 1 _).gradedIndex _
    rw [appendFullCellsScheme_gradedIndex_natAdd]
    exact hq
  rw [rowAt_of_mem hmem]
  have h1 := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
    (r := baseRow H prof) (h := hS) (ladderEquiv S Q H p) ⟨_, hmem⟩
  rw [h1, baseRow_of_mem hwf _ hq, Equiv.symm_apply_apply, baseIndex_castAdd]

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

/-! ### The cells of grade one of the tower -/

/-- **A cell of grade one of the tower is a ladder point or a cell of grade one of the
attachment.** -/
theorem tower_grade_one_cases (x : Fin (I.attachTower g H Γ A B').card)
    (hx : (I.attachTower g H Γ A B').toCellScheme.grade x = 1) :
    (∃ v, x = ladCell H Γ A B' v) ∨
      ∃ e, (I.attachment g).toCellScheme.grade e = 1 ∧
        x = (I.attachmentBase g).baseCellEmb (H := H) (Γ := Γ) (A := A) (B' := B') m e := by
  obtain ⟨t, rfl⟩ := Scheme.mem_range_layerTowerEmb_of_grade
    (B := (I.attachmentBase g).towerBase H) (C := (I.attachmentBase g).towerCat Γ A)
    (G := fun k ↦ grid k B') m x hx.le
  induction t using Fin.addCases with
  | left e =>
    refine .inr ⟨e, ?_, rfl⟩
    have h := congrArg Prod.snd ((I.attachmentBase g).gradedIndex_baseCellEmb
      (H := H) (Γ := Γ) (A := A) (B' := B') m e)
    exact h.symm.trans hx
  | right j =>
    refine .inl ⟨(Scheme.ladderEquiv _ _ H).symm j, ?_⟩
    rw [ladCell, Equiv.apply_symm_apply]

/-- **A ladder point reads a ladder point** through the code of the base index of its member. -/
theorem rowAt_ladCell_ladCell
    (p v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').rowAt (ladCell H Γ A B' p) (ladCell H Γ A B' v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (Scheme.baseIndex H (Scheme.rankProf (I.attachmentBase g).S H) p.1
          (Fin.natAdd _ (Scheme.ladderEquiv _ _ H v))) :=
  (Scheme.rowAt_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ _ m).trans
    (Scheme.rowAt_ladderBase_ladder (hS := (I.attachmentBase g).noFull) (I.attachmentBase g).wf
      p v)

/-- **A ladder point reads a cell of grade one of the attachment as the shadow of its member at
that cell.** -/
theorem rowAt_ladCell_baseCellEmb
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    {e : Fin (I.attachment g).card} (he : (I.attachment g).toCellScheme.grade e = 1) :
    (I.attachTower g H Γ A B').rowAt (ladCell H Γ A B' p)
        ((I.attachmentBase g).baseCellEmb m e) =
      (I.attachTower g H Γ A B').rowAt (ladCell H Γ A B' p)
        (ladCell H Γ A B' (p.1, Sum.inr e)) := by
  refine ((Scheme.rowAt_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ _ m).trans
    (Scheme.rowAt_ladderBase_old (hS := (I.attachmentBase g).noFull) (I.attachmentBase g).wf
      p he)).trans ?_
  rw [rowAt_ladCell_ladCell]
  have h := Scheme.baseIndex_self (Scheme.rankProf_le (I.attachmentBase g).S H)
    ((p.1, Sum.inr e) :
      Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
  simp only [Scheme.ladderCeil] at h
  rw [h]
  rfl

/-! ### The cells of grade one of the replicated scheme -/

/-- The grade of a cell of the replicated scheme is that of its original. -/
theorem grade_replicated (z : Fin (I.replicated g H Γ A B').card) :
    (I.replicated g H Γ A B').toCellScheme.grade z =
      (I.attachTower g H Γ A B').toCellScheme.grade
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) := rfl

/-- **The cells at a mixed face at the grade one are the copied ladder points.** -/
theorem exists_eq_copyLadder (hU : U ∈ I.mixedFaces g) (z : Fin (I.replicated g H Γ A B').card)
    (hz : (I.replicated g H Γ A B').toCellScheme.gradedIndex z = (U, 1)) :
    ∃ v, z = copyLadder H Γ A B' hU v := by
  induction z using Fin.addCases with
  | left x =>
    exfalso
    have hs : (I.attachTower g H Γ A B').toCellScheme.scope x = U :=
      (congrArg Prod.fst (Scheme.gradedIndex_mirror_castAdd
        (hmix := I.not_subset_scope_tower g H Γ A B') x)).symm.trans (congrArg Prod.fst hz)
    have hne : (I.attachTower g H Γ A B').toCellScheme.scope x ≠ univ :=
      hs ▸ ((I.mem_mixedFaces g).mp hU).2.1
    exact I.not_subset_scope_tower g H Γ A B' x hne U hU (hs ▸ subset_rfl)
  | right j =>
    set q := ((I.attachTower g H Γ A B').copyEquiv (I.mixedFaces g)).symm j with hq
    have hj : j = (I.attachTower g H Γ A B').copyEquiv (I.mixedFaces g) q := by
      rw [hq, Equiv.apply_symm_apply]
    obtain ⟨⟨U', f⟩, hU', hf, hfg⟩ := q
    have hsU : U' = U := by
      have h := congrArg Prod.fst hz
      change (I.attachTower g H Γ A B').mirrorScope (I.mixedFaces g) (Fin.natAdd _ j) = U at h
      rw [Scheme.mirrorScope_natAdd, ← hq] at h
      exact h
    subst hsU
    have hfg1 : (I.attachTower g H Γ A B').toCellScheme.grade f = 1 := by
      have h := congrArg Prod.snd hz
      change (I.attachTower g H Γ A B').toCellScheme.grade
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.natAdd _ j)) = 1 at h
      rw [Scheme.mirrorOrig_natAdd, ← hq] at h
      exact h
    rcases tower_grade_one_cases f hfg1 with ⟨v, rfl⟩ | ⟨e, -, rfl⟩
    · exact ⟨v, by rw [hj]; rfl⟩
    · exfalso
      exact (I.attachmentBase g).scope_ne_univ e
        ((Scheme.LadderBaseData.scope_baseCellEmb (H := H) (Γ := Γ) (A := A) (B' := B') m
          e).symm.trans hf)

/-- **The cells of full scope at the grade one are the ladder points.** -/
theorem exists_eq_castAdd_ladCell (z : Fin (I.replicated g H Γ A B').card)
    (hz : (I.replicated g H Γ A B').toCellScheme.gradedIndex z =
      ((univ : Finset (Fin (m + 2))), 1)) :
    ∃ v, z = Fin.castAdd _ (ladCell H Γ A B' v) := by
  induction z using Fin.addCases with
  | right j =>
    exfalso
    exact ((I.mem_mixedFaces g).mp (scope_replicated_natAdd j)).2.1 (congrArg Prod.fst hz)
  | left x =>
    have hx : (I.attachTower g H Γ A B').toCellScheme.gradedIndex x =
        ((univ : Finset (Fin (m + 2))), 1) :=
      (Scheme.gradedIndex_mirror_castAdd (hmix := I.not_subset_scope_tower g H Γ A B') x).symm.trans
        hz
    rcases tower_grade_one_cases x (congrArg Prod.snd hx) with ⟨v, rfl⟩ | ⟨e, -, rfl⟩
    · exact ⟨v, rfl⟩
    · exfalso
      exact (I.attachmentBase g).scope_ne_univ e
        ((congrArg Prod.fst (Scheme.LadderBaseData.gradedIndex_baseCellEmb (H := H) (Γ := Γ)
          (A := A) (B' := B') m e)).symm.trans (congrArg Prod.fst hx))

/-- The original ladder point at the cell of full scope. -/
theorem mirrorOrig_castAdd_ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g)
      (Fin.castAdd _ (ladCell H Γ A B' p)) = ladCell H Γ A B' p :=
  Scheme.mirrorOrig_castAdd _ _ _

theorem gradedIndex_castAdd_ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ (ladCell H Γ A B' p)) =
      ((univ : Finset (Fin (m + 2))), 1) :=
  (Scheme.gradedIndex_mirror_castAdd _).trans (gradedIndex_ladCell p)

/-- A ladder point reads a copied ladder point as the original. -/
theorem rowAt_castAdd_ladCell_copyLadder_eq (hU : U ∈ I.mixedFaces g)
    (p v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').rowAt (Fin.castAdd _ (ladCell H Γ A B' p))
        (copyLadder H Γ A B' hU v) =
      (I.attachTower g H Γ A B').rowAt (ladCell H Γ A B' p) (ladCell H Γ A B' v) := by
  have hcT : copyLadder H Γ A B' hU v ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex
        (Fin.castAdd _ (ladCell H Γ A B' p))) := by
    rw [gradedIndex_castAdd_ladCell, CellScheme.mem_below, gradedIndex_copyLadder]
    exact ⟨subset_univ _, le_rfl⟩
  refine (Scheme.rowAt_mirror_of_mem hcT).trans ?_
  congr 1
  · exact mirrorOrig_castAdd_ladCell p
  · exact mirrorOrig_copyAt hU _ _ _

/-- **Every cell below `(univ, 1)` is read by a ladder point as a copied ladder point at any mixed
face**: as itself if it is a ladder point or a copy of one, as the shadow of the reader's member
at the cell if it is a cell of the attachment. -/
theorem exists_rowAt_eq_copyLadder (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    {z : Fin (I.replicated g H Γ A B').card}
    (hz : z ∈ (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), 1)) :
    ∃ v, (I.replicated g H Γ A B').rowAt (Fin.castAdd _ (ladCell H Γ A B' p)) z =
      (I.replicated g H Γ A B').rowAt (Fin.castAdd _ (ladCell H Γ A B' p))
        (copyLadder H Γ A B' hU v) := by
  have hzT : z ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex
        (Fin.castAdd _ (ladCell H Γ A B' p))) := by
    rw [gradedIndex_castAdd_ladCell]; exact hz
  have hcT (v : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      copyLadder H Γ A B' hU v ∈ (I.replicated g H Γ A B').toCellScheme.below
        ((I.replicated g H Γ A B').toCellScheme.gradedIndex
          (Fin.castAdd _ (ladCell H Γ A B' p))) := by
    rw [gradedIndex_castAdd_ladCell, CellScheme.mem_below, gradedIndex_copyLadder]
    exact ⟨subset_univ _, le_rfl⟩
  have hg1 : (I.attachTower g H Γ A B').toCellScheme.grade
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) = 1 := by
    have h1 : (I.replicated g H Γ A B').toCellScheme.grade z ≤ 1 := hz.2
    have h2 := (isWellFormed_replicated (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
      (B' := B')).isWellFormed.grade_pos z
    rw [grade_replicated] at h1 h2
    omega
  rw [Scheme.rowAt_mirror_of_mem hzT, mirrorOrig_castAdd_ladCell]
  rcases tower_grade_one_cases _ hg1 with ⟨v, hv⟩ | ⟨e, he, he'⟩
  · refine ⟨v, ?_⟩
    rw [hv, rowAt_castAdd_ladCell_copyLadder_eq]
  · refine ⟨(p.1, Sum.inr e), ?_⟩
    rw [he', rowAt_ladCell_baseCellEmb p he, rowAt_castAdd_ladCell_copyLadder_eq]

/-- A ladder point reads a copied ladder point as the original. -/
theorem rowAt_castAdd_ladCell_copyLadder (hU : U ∈ I.mixedFaces g)
    (p v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').rowAt (Fin.castAdd _ (ladCell H Γ A B' p))
        (copyLadder H Γ A B' hU v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) p.1 v) := by
  rw [rowAt_castAdd_ladCell_copyLadder_eq, rowAt_ladCell_ladCell, Scheme.baseIndex_natAdd,
    Equiv.symm_apply_apply]

end Seed

end VaughtConjecture

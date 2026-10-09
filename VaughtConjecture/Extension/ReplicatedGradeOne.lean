/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthCappedDecoder
import VaughtConjecture.Extension.FlattenedSource
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

namespace Label

/-- **Agreement at the cap through a dominating reader.**  The arithmetic of the lift at the grade
one: if `a` and `b` agree capped at `c`, a reader of value `z` agreeing with `m` at `c` reads `d`
and `b` alike, `a ≤ m`, and `d ≤ z` whenever `z < c`, then `a` and `d` agree capped at `c`. -/
theorem min_eq_min_of_reader {a b d z m c : Label.{u}} (hab : min a c = min b c)
    (hzm : min z c = min m c) (hdb : min d z = min b z) (ham : a ≤ m)
    (hdz : z < c → d ≤ z) : min a c = min d c := by
  rcases le_or_gt c z with hcz | hzc
  · have h1 : min d c = min (min d z) c := by rw [min_assoc, min_eq_right hcz]
    have h2 : min b c = min (min b z) c := by rw [min_assoc, min_eq_right hcz]
    rw [hab, h2, ← hdb, ← h1]
  · rw [min_eq_left hzc.le] at hzm
    have hmc : m < c := by
      by_contra h
      rw [min_eq_right (not_lt.mp h)] at hzm
      exact hzc.ne hzm
    rw [min_eq_left hmc.le] at hzm
    have hac : a < c := lt_of_le_of_lt ham hmc
    rw [min_eq_left hac.le] at hab ⊢
    have hb : b = a := by
      rcases le_or_gt c b with hcb | hbc
      · rw [min_eq_right hcb] at hab
        exact absurd hab hac.ne
      · rw [min_eq_left hbc.le] at hab
        exact hab.symm
    rw [min_eq_left (hdz hzc), hb, min_eq_left (ham.trans hzm.symm.le)] at hdb
    rw [hdb, min_eq_left hac.le]

end Label

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
    (G := fun k ↦ Scheme.heightSet Γ B' k) m x hx.le
  induction t using Fin.addCases with
  | left e =>
    refine .inr ⟨e, ?_, rfl⟩
    have h := congrArg Prod.snd ((I.attachmentBase g).gradedIndex_baseCellEmb
      (H := H) (Γ := Γ) (A := A) (B' := B') (G := fun k ↦ Scheme.heightSet Γ B' k) m e)
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
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) _ _ m).trans
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
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) _ _ m).trans
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

theorem mirrorOrig_copyLadder (hU : U ∈ I.mixedFaces g)
    (v : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (copyLadder H Γ A B' hU v) =
      ladCell H Γ A B' v :=
  mirrorOrig_copyAt hU _ _ _

/-- The cells below `(univ, 1)` have grade one. -/
theorem grade_eq_one_of_mem_below_univ_one {z : Fin (I.replicated g H Γ A B').card}
    (hz : z ∈ (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), 1)) :
    (I.replicated g H Γ A B').toCellScheme.grade z = 1 := by
  have h1 : (I.replicated g H Γ A B').toCellScheme.grade z ≤ 1 := hz.2
  have h2 := (isWellFormed_replicated (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
    (B' := B')).isWellFormed.grade_pos z
  omega

/-! ### The lift -/

/-- The replicated scheme, in the lift at the grade one. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The full face at the grade one. -/
local notation "𝕌₁" => ((univ : Finset (Fin (m + 2))), 1)

/-- **The lift from a mixed face into the full face at the grade one.**  For a mixed face `U`, the
replicated scheme lifts capped from `(U, 1)` to `(univ, 1)`.  If the prescription is `⊥` on the
copied ladder at `U`, it is `⊥` below `(U, 1)` (availability), and the ambient capped at the cap
is the lift.  Otherwise its shape picks a member `a`; the lift is the capped decoder at the copied
top rung of `a` applied to the row of the original top rung of `a`: lawful by the bottom pattern of
that row, equal to the prescription below `(U, 1)`, and keeping the observation of the ambient at
the cap (`Label.min_eq_min_of_reader`, through the capped decoder of the ambient at the original
top rung). -/
theorem cappedLift_mixed_univ_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hU : U ∈ I.mixedFaces g) :
    (𝔼).rows.CappedLift (X := (U, 1)) (Y := 𝕌₁)
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  have hXY : ((U, 1) : Finset (Fin (m + 2)) × ℕ) ≤ 𝕌₁ :=
    ⟨subset_univ _, le_rfl⟩
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  -- total labellings
  obtain ⟨P, hPd⟩ : ∃ P : Fin (𝔼).card → Label.{u},
      ∀ d (hd : d ∈ (𝔼).toCellScheme.below (U, 1)), P d = p ⟨d, hd⟩ :=
    ⟨CellScheme.Rows.extendBot _ p, fun d hd ↦ CellScheme.Rows.extendBot_of_mem p hd⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Fin (𝔼).card → Label.{u},
      ∀ d (hd : d ∈ (𝔼).toCellScheme.below 𝕌₁),
        Q d = q ⟨d, hd⟩ :=
    ⟨CellScheme.Rows.extendBot _ q, fun d hd ↦ CellScheme.Rows.extendBot_of_mem q hd⟩
  have hP : (𝔼).rows.IsLawfulBelow (U, 1) fun d ↦ P d := by
    have e : (fun d : (𝔼).toCellScheme.below (U, 1) ↦ P d) = p := funext fun d ↦ hPd d d.2
    rw [e]; exact hp
  have hQ : (𝔼).rows.IsLawfulBelow 𝕌₁ fun d ↦ Q d := by
    have e : (fun d : (𝔼).toCellScheme.below 𝕌₁ ↦ Q d) = q :=
      funext fun d ↦ hQd d d.2
    rw [e]; exact hq
  have hpq' (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) : min (Q d) c = min (P d) c := by
    rw [hQd d (le_trans hd hXY), hPd d hd]
    exact hpq ⟨d, hd⟩
  have hcl (v : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      copyLadder H Γ A B' hU v ∈ (𝔼).toCellScheme.below (U, 1) := by
    rw [CellScheme.mem_below, gradedIndex_copyLadder]
  have hgX (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) : (𝔼).toCellScheme.grade d = 1 :=
    grade_eq_one_of_mem_below_univ_one (le_trans hd hXY)
  have hsX (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) (v) :
      (𝔼).toCellScheme.scope d ⊆ (𝔼).toCellScheme.scope (copyLadder H Γ A B' hU v) := by
    exact hd.1.trans (le_of_eq (congrArg Prod.fst
      (gradedIndex_copyLadder (Γ := Γ) (A := A) (B' := B') hU v)).symm)
  obtain ⟨-, -, havailP⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hP
  obtain ⟨-, -, havailQ⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hQ
  rcases copyLadder_exists_shape hH hU hP le_rfl with hall | ⟨a, gg, σ, hwit, hch, hbot⟩
  · -- the prescription is `⊥` below `(U, 1)`
    obtain ⟨a0⟩ := (inferInstance : Nonempty (Scheme.RankMember (I.attachmentBase g).S H))
    have hp0 (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) : P d = ⊥ := by
      let v0 : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H := (a0, Sum.inl ⟨0, hH⟩)
      obtain ⟨u, hu, hle⟩ := havailP d _ (hcl v0) (hsX d hd v0)
        ((hgX d hd).trans (congrArg Prod.snd (gradedIndex_copyLadder hU v0)).symm)
      obtain ⟨v, rfl⟩ := exists_eq_copyLadder hU u (hu.trans (gradedIndex_copyLadder hU v0))
      exact le_bot_iff.mp (hle.trans (hall v).le)
    refine ⟨fun d ↦ min (q d) c, ?_, fun d ↦ by rw [min_assoc, min_self], fun d ↦ ?_⟩
    · by_cases hc0 : c = ⊥
      · have e : (fun d : (𝔼).toCellScheme.below 𝕌₁ ↦
            min (q d) c) = fun _ ↦ ⊥ := funext fun d ↦ by rw [hc0, min_bot_right]
        rw [e]
        exact CellScheme.Rows.isLawfulBelow_const_bot _
      · exact hq.map_of_bot_iff hq (fun d ↦ (grade_eq_one_of_mem_below_univ_one d.2).le)
          ((IsWitness.id_step 1).min_const hc)
          fun d ↦ ⟨fun h ↦ (min_eq_bot.mp h).resolve_right hc0, fun h ↦ by simp [h]⟩
    · have h0 : p d = ⊥ := by rw [← hp0 d.1 d.2, hPd d.1 d.2]
      change min (q (Set.inclusion _ d)) c = p d
      rw [hpq d, h0, min_eq_left bot_le]
  · -- the shape: the member `a`
    let top : Scheme.LadderPt (I.attachmentBase g).S
        (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩)
    have hidxtop : ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
        (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a top = H := by
      have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) top
      simp only [top, Scheme.ladderCeil, Sum.elim_inl] at h
      rw [h]
      omega
    have hMv (v) : P (copyLadder H Γ A B' hU v) ≤ P (copyLadder H Γ A B' hU top) := by
      rw [hch v, hch top, hidxtop]
      exact min_le_min_right _ (hwit.monotone (monotone_ladderSource H (ladderIndex_le a v)))
    have hMX (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) :
        P d ≤ P (copyLadder H Γ A B' hU top) := by
      obtain ⟨u, hu, hle⟩ := havailP d _ (hcl top) (hsX d hd top)
        ((hgX d hd).trans (congrArg Prod.snd (gradedIndex_copyLadder hU top)).symm)
      obtain ⟨v, rfl⟩ := exists_eq_copyLadder hU u (hu.trans (gradedIndex_copyLadder hU top))
      exact hle.trans (hMv v)
    obtain ⟨θ, hθ, -, hθrow⟩ := Scheme.exists_cappedDecoder_below hP (hcl top)
      (congrArg Prod.snd (gradedIndex_copyLadder hU top))
    have hTst := gradedIndex_castAdd_ladCell (Γ := Γ) (A := A) (B' := B') top
    have hTstY : (Fin.castAdd _ (ladCell H Γ A B' top) : Fin (𝔼).card) ∈
        (𝔼).toCellScheme.below 𝕌₁ := le_of_eq hTst
    have horig : (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g)
        (copyLadder H Γ A B' hU top) = (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g)
          (Fin.castAdd _ (ladCell H Γ A B' top)) :=
      (mirrorOrig_copyLadder hU top).trans (mirrorOrig_castAdd_ladCell top).symm
    have hsT : (𝔼).toCellScheme.scope (copyLadder H Γ A B' hU top) ⊆
        (𝔼).toCellScheme.scope (Fin.castAdd _ (ladCell H Γ A B' top)) :=
      subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst hTst).symm)
    -- the copied and the original top rung read alike below the copy
    have hρT (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) :
        (𝔼).rowAt (copyLadder H Γ A B' hU top) d =
          (𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d := by
      have hd1 : d ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (copyLadder H Γ A B' hU top)) := by
        rw [gradedIndex_copyLadder]; exact hd
      have hd2 : d ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (ladCell H Γ A B' top))) := by
        rw [hTst]; exact le_trans hd hXY
      rw [Scheme.rowAt_mirror_of_mem hd1, Scheme.rowAt_mirror_of_mem hd2, horig]
    have hrX (d) (hd : d ∈ (𝔼).toCellScheme.below (U, 1)) :
        θ ((𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d) = P d := by
      have hd1 : d ∈ (𝔼).toCellScheme.below
          ((𝔼).toCellScheme.gradedIndex (copyLadder H Γ A B' hU top)) := by
        rw [gradedIndex_copyLadder]; exact hd
      rw [← hρT d hd, hθrow d hd1, min_eq_left (hMX d hd)]
    have hρlaw : (𝔼).rows.IsLawfulBelow 𝕌₁
        fun d ↦ (𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d := by
      have h := Scheme.isLawfulBelow_rowAt (isConsistent_replicated hH hcard hΓ hA) hTst
      exact h
    have hbotρ (d) (hd : d ∈ (𝔼).toCellScheme.below 𝕌₁) :
        θ ((𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d) = ⊥ ↔
          (𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d = ⊥ := by
      obtain ⟨v, hv⟩ := exists_rowAt_eq_copyLadder hU top hd
      rw [hv, hrX _ (hcl v), hbot v, rowAt_castAdd_ladCell_copyLadder hU top v,
        ladderSource_eq_bot_iff]
      simp only [top, Scheme.ladderCeil, Sum.elim_inl]
      constructor
      · intro h; rw [h]; simp
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · exact h'
        · omega
    refine ⟨fun d ↦ θ ((𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d),
      hρlaw.map_of_bot_iff hρlaw (fun d ↦ (grade_eq_one_of_mem_below_univ_one d.2).le) hθ
        (fun d ↦ hbotρ d d.2), fun d ↦ ?_, fun d ↦ ?_⟩
    · -- the observation of the ambient at the cap
      obtain ⟨v, hv⟩ := exists_rowAt_eq_copyLadder hU top d.2
      have hl : min (θ ((𝔼).rowAt (Fin.castAdd _ (ladCell H Γ A B' top)) d)) c =
          min (P (copyLadder H Γ A B' hU v)) c := by
        rw [hv, hrX _ (hcl v)]
      rw [hl, ← hQd d.1 d.2]
      have hab := (hpq' _ (hcl v)).symm
      have he : Q (copyLadder H Γ A B' hU top) = Q (Fin.castAdd _ (ladCell H Γ A B' top)) :=
        Scheme.eq_of_mirrorOrig_eq hQ horig hsT hTstY
      have hZM : min (Q (Fin.castAdd _ (ladCell H Γ A B' top))) c =
          min (P (copyLadder H Γ A B' hU top)) c := by
        rw [← he]; exact hpq' _ (hcl top)
      obtain ⟨θq, -, -, hθq⟩ := Scheme.exists_cappedDecoder_below hQ hTstY
        (congrArg Prod.snd hTst)
      have hdb : min (Q d) (Q (Fin.castAdd _ (ladCell H Γ A B' top))) =
          min (Q (copyLadder H Γ A B' hU v)) (Q (Fin.castAdd _ (ladCell H Γ A B' top))) := by
        have hd2 : d.1 ∈ (𝔼).toCellScheme.below
            ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (ladCell H Γ A B' top))) := by
          rw [hTst]; exact d.2
        have hv2 : copyLadder H Γ A B' hU v ∈ (𝔼).toCellScheme.below
            ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ (ladCell H Γ A B' top))) := by
          rw [hTst]; exact le_trans (hcl v) hXY
        rw [← hθq _ hd2, ← hθq _ hv2, hv]
      have hdz : Q (Fin.castAdd _ (ladCell H Γ A B' top)) < c →
          Q d ≤ Q (Fin.castAdd _ (ladCell H Γ A B' top)) := by
        intro hzc
        obtain ⟨u, hu, hle⟩ := havailQ d.1 _ hTstY
          (subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst hTst).symm))
          ((grade_eq_one_of_mem_below_univ_one d.2).trans (congrArg Prod.snd hTst).symm)
        obtain ⟨v', rfl⟩ := exists_eq_castAdd_ladCell u (hu.trans hTst)
        have huY : (Fin.castAdd _ (ladCell H Γ A B' v') : Fin (𝔼).card) ∈
            (𝔼).toCellScheme.below 𝕌₁ := le_of_eq (hu.trans hTst)
        have e' : Q (copyLadder H Γ A B' hU v') = Q (Fin.castAdd _ (ladCell H Γ A B' v')) :=
          Scheme.eq_of_mirrorOrig_eq hQ
            ((mirrorOrig_copyLadder hU v').trans (mirrorOrig_castAdd_ladCell v').symm)
            (subset_trans (subset_univ _) (le_of_eq
              (congrArg Prod.fst (gradedIndex_castAdd_ladCell v')).symm)) huY
        have h1 : min (Q (copyLadder H Γ A B' hU v')) c ≤
            Q (Fin.castAdd _ (ladCell H Γ A B' top)) := by
          rw [hpq' _ (hcl v')]
          calc min (P (copyLadder H Γ A B' hU v')) c
              ≤ min (P (copyLadder H Γ A B' hU top)) c := min_le_min_right _ (hMv v')
            _ = min (Q (Fin.castAdd _ (ladCell H Γ A B' top))) c := hZM.symm
            _ = Q (Fin.castAdd _ (ladCell H Γ A B' top)) := min_eq_left hzc.le
        have h2 : Q (copyLadder H Γ A B' hU v') ≤ Q (Fin.castAdd _ (ladCell H Γ A B' top)) := by
          rcases le_or_gt c (Q (copyLadder H Γ A B' hU v')) with h' | h'
          · rw [min_eq_right h'] at h1
            exact absurd h1 (not_le.mpr hzc)
          · rwa [min_eq_left h'.le] at h1
        exact hle.trans (e' ▸ h2)
      exact Label.min_eq_min_of_reader hab hZM hdb (hMv v) hdz
    · -- the prescription below `(U, 1)`
      rw [← hPd d.1 d.2]
      exact hrX d.1 d.2

end Seed

end VaughtConjecture

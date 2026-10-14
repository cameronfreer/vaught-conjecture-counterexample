/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StronglyCodedCarrierObstruction
import VaughtConjecture.Extension.StronglyCodedCompletion
import VaughtConjecture.MainTheorem.LevelCarrier
import VaughtConjecture.MainTheorem.ReplicatedCompletion
import VaughtConjecture.MainTheorem.SeedLevelChoice

/-!
# The first construction of the ladder carrier that is not strongly coded

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels) and Correspondence, item 1 (the
strongly coded legal stage types).  All results here are native constructions of this repository.

The strongly coded finite target of (R4) (`StageType.HasStronglyCodedCutoffStableRecovery`, in
`VaughtConjecture.Continuation.StronglyCodedRecoveryTarget`) asks for a strongly coded carrier `q`
of cutoff stable recovery.  The compiled carrier for the margin calibration is the ladder carrier
of the seed (`StageType.hasLadderGrowthCarriersStableAtSeed_levels`, through
`Seed.exists_lvRepCarrier`), and the carrier `q` it gives lies on the carrier scheme
(`GrowthCarrier.isStableRecoveryScheme`).  In the order of that construction, the seed and its
attachment are strongly coded when both coatom types are (`Seed.isStronglyCoded_attachment`; the
second coatom type from the strongly coded pinned extension
`StageType.exists_stronglyCoded_pinned_extension`); the next
construction, the **padded grade-one base** (`Scheme.LadderBaseData.ladderBase`, appending the
ladder points at `(univ, 1)` with the rows `Scheme.baseRow`), is not.

* `Scheme.LadderBaseData.not_isStronglyCoded_ladderBase`: for every height `H ≥ 2` the padded
  grade-one base is not strongly coded.  The cell is the rung `1` of a rank member (the members are
  nonempty), the row value is its entry at itself, `ladderSource 2 2 = ω + 3`, at grade one.
* `Seed.isStronglyCoded_attachment`: the attachment is strongly coded when both coatom types of
  the seed are.
* `Seed.one_lt_seedHeightLevel`: the height of the seed choice is at least `2` (the attachment has
  a cell: the context is legal, hence complete at `(univ, 1)`).
* `Seed.not_isStronglyCoded_lvBase_seedHeightLevel`: so the base of the seed construction is not
  strongly coded.
* `Seed.not_isStronglyCoded_lvRepCompletion`: nor is the completion of the replicated level at any
  height `H ≥ 2`, whose scheme is the scheme of the carrier of `Seed.exists_lvRepCarrier`.

**Scope.**  These statements concern the existing ladder construction at heights `H ≥ 2` only.
They do not refute the finite target, which asks for some strongly coded carrier, not this one.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme.LadderBaseData

variable {n : ℕ}

/-- **The padded grade-one base is not strongly coded at height `H ≥ 2`** (native construction).
The rung `1` of a rank member (`Scheme.RankMember`, a nonempty type) is a cell of grade one whose
row reads itself at its ceiling `2`: `ladderSource 2 2 = ω + 3`, of finite part `3 > 1 + 1`. -/
theorem not_isStronglyCoded_ladderBase (B : LadderBaseData.{u} n) {H : ℕ} (hH : 1 < H) :
    ¬ (B.ladderBase H).rows.IsStronglyCoded := by
  obtain ⟨a⟩ : Nonempty (RankMember B.S H) := inferInstance
  set p : LadderPt B.S (RankMember B.S H) H := (a, Sum.inl ⟨1, hH⟩)
  refine Scheme.not_isStronglyCoded_of_rowAt_ladderSource_diag (i := 1)
    (c := Fin.natAdd _ (ladderEquiv B.S (RankMember B.S H) H p))
    (appendFullCellsScheme_grade_natAdd _ _ _ _).le le_rfl ?_
  rw [rowAt_ladderBase_ladder B.wf p p, baseIndex_self (rankProf_le B.S H) p]
  rfl

end Scheme.LadderBaseData

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-- **The attachment of a seed with strongly coded coatom types is strongly coded** (native
construction): the amalgam is strongly coded (`Seed.isStronglyCoded_amalgam`) and the attachment is
its restriction to a lower set of cells.  So the constructions of the seed before the padded
grade-one base keep strong coding when both coatom types are strongly coded (for the second, the
strongly coded pinned extension `StageType.exists_stronglyCoded_pinned_extension`; the seed of
`StageType.exists_growthSeed_of_isSuccLimit` uses the exact pinned extension instead). -/
theorem isStronglyCoded_attachment (hl : I.left.rows.IsStronglyCoded)
    (hr : I.right.rows.IsStronglyCoded) : (I.attachment g).rows.IsStronglyCoded :=
  (I.isStronglyCoded_amalgam hl hr).comap
    (I.amalgam.toScheme.isLowerEmbedding_lowerEmb _ (I.attachmentCells_lower g))

/-- **The height of the seed choice is at least `2`**: the context `I.left` is legal, hence has a
cell of graded index `(univ, 1)`, and its cells are cells of the attachment
(`Seed.attachCtxCell`). -/
theorem one_lt_seedHeightLevel : 1 < I.seedHeightLevel g := by
  obtain ⟨w, -⟩ := I.isLegal_left.isComplete ((univ : Finset (Fin (m + 1))), 1)
    ⟨I.left.univ_mem_faces, one_pos, by simp⟩
  have h : 0 < (I.attachmentBase g).S.card := Fin.pos (I.attachCtxCell g w)
  unfold seedHeightLevel
  omega

/-- **The base of the seed construction is not strongly coded** (native construction): the padded
grade-one base over the attachment at the height of the seed choice, which is at least `2`. -/
theorem not_isStronglyCoded_lvBase_seedHeightLevel :
    ¬ (I.lvBase g (I.seedHeightLevel g)).rows.IsStronglyCoded :=
  (I.attachmentBase g).not_isStronglyCoded_ladderBase (I.one_lt_seedHeightLevel g)

variable {I g} {H B : ℕ} {d : StageType.{u} α (n + 1)}
  {hd : StageType.restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : StageType.GrowthRequests I.left d.toScheme}

/-- **The completion of the replicated level is not strongly coded at height `H ≥ 2`** (native
construction): its rung `1` of a rank member has grade one and reads itself at
`ladderSource 2 2 = ω + 3` (`Seed.lvRepCompletion_rung_rows`).  Its scheme is the scheme of the
carrier of `Seed.exists_lvRepCarrier`. -/
theorem not_isStronglyCoded_lvRepCompletion (hα : Order.IsSuccPrelimit α) (hH : 1 < H)
    (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q) :
    ¬ (lvRepCompletion hα hNm hL hq).rows.IsStronglyCoded := by
  obtain ⟨a⟩ : Nonempty (Scheme.RankMember (I.attachmentBase g).S H) := inferInstance
  have hH0 : 0 < H := by omega
  have hgi := (gradedIndex_lvRepCompletion_castSucc hα hL hq _).trans
    ((hNm.rep_gradedIndex_castAdd _).trans (lvLevel_gradedIndex_lad m
      ((a, Sum.inl ⟨min 1 (H - 1), by omega⟩) :
        Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)))
  exact Scheme.not_isStronglyCoded_of_rowAt_ladderSource_diag (i := 1)
    (congrArg Prod.snd hgi).le le_rfl (lvRepCompletion_rung_rows hα hH0 hNm hL hq a 1 hH).1

end Seed

end VaughtConjecture

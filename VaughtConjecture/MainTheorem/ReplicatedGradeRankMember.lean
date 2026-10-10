/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeTwoStage

/-!
# Rank members of states lawful only at the grade one

Roadmap, Layer 3 ((R3) and (R4), the base of the ladder tower for the values per grade).

The extension `stateExt` of a state to the padded base reads the positive table of the state at
the base indices of its rank member, built by `Scheme.RankMember.ofLawful` from a lawful state.  A
rank member asks dense ranks and **lawful tables**: every positive table read at the ranks on the
cells of grade one, `⊥` above, is lawful.  The tables read only the cells of grade one: their
lawfulness needs the state lawful **below `(univ, 1)`** only
(`Scheme.isLawful_rankTable_of_isLawfulBelow_one`).  So a state lawful below a pair of any grade at
least `1`, such as the orbit code at the grade `k` of a lawful state
(`CellScheme.Rows.IsLawfulBelow.orbitCode`), has a rank member
(`Scheme.RankMember.ofLawfulBelowOne`), equal to that of `Scheme.RankMember.ofLawful` on lawful
states (`Scheme.RankMember.ofLawfulBelowOne_eq_ofLawful`).  The extension with this member
(`Scheme.LadderBaseData.stateExtOf`) is the state on the base cells and the positive table at the
base indices of the member on the ladder; on lawful states it is `stateExt`
(`Scheme.LadderBaseData.stateExtOf_eq_stateExt`).

Tested at the three-point seed with an apex: at the grade `2` the orbit code of a lawful state
has a rank member there, where it is not lawful (`ApexInstance.exists_rankMember_orbitCode_two`).

The lawfulness of the extension below `(univ, k)` from the lawfulness of the state below
`(univ, k)` is not proved here (`Scheme.isLawful_ladderExtend` asks the state lawful on the base).

**The catalogues per grade increase** (`Label.gridPoint_mem_codeGrid_not_mem`): a value of the
code grid at `k + 3` need not lie in the code grid at `k + 2`.  The lawfulness of the layer tower
(`Scheme.layerTower_lawful`) passes from the states of the catalogue at `k + 2`, written lawfully at
the height `k`, to those at `k + 3` through the inclusion `C (k + 3) ⊆ C (k + 2)`; with the
catalogues per grade that step has no replacement here.

## References

Lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

/-- **The values per grade increase with the grade**: the grid point `k + 3` of the block `0` is a
value of the code grid at `k + 3` and not of the code grid at `k + 2` (it is self-visible at
`k + 3`, while the code grid at `k + 2` is short at `k + 2`).  So the catalogues with values in the
code grid at the grade are not nested downward, as the lawfulness of the layer tower
(`Scheme.layerTower_lawful`, through `Scheme.LadderBaseData.towerCat_succ_subset`) asks. -/
theorem gridPoint_mem_codeGrid_not_mem (k B : ℕ) :
    gridPoint.{u} (k + 3) 0 ∈ codeGrid (k + 3) B ∧
      gridPoint.{u} (k + 3) 0 ∉ codeGrid (k + 2) B := by
  refine ⟨mem_codeGrid.mpr (.inr ⟨0, Nat.zero_le _, k + 3, le_rfl, rfl⟩), fun hx ↦ ?_⟩
  have hs := isShort_of_mem_codeGrid hx
  have hv : IsSelfVisible (k + 3) (gridPoint.{u} (k + 3) 0) :=
    isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) le_rfl
  rw [gridPoint, isShort_coe] at hs
  rw [gridPoint, isSelfVisible_coe] at hv
  have : ((k + 3 : ℕ) : Ordinal.{u}) ≤ ((k + 2 : ℕ) : Ordinal.{u}) := hv.trans hs
  exact absurd (by exact_mod_cast this) (show ¬ k + 3 ≤ k + 2 by omega)

end Label

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **A state lawful below `(univ, k)`, truncated to `⊥` above the grade `k`, is lawful**: the
cells above `k` read and are read at `⊥`, and below `k` the order, locality and availability are
those below `(univ, k)`. -/
theorem isLawful_truncate {R : Fin S.card → Label.{u}} {k : ℕ}
    (hR : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun d ↦ R d) :
    S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d ≤ k then R d else ⊥ := by
  classical
  obtain ⟨hord, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hR
  have hmem (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) :
      d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), k) := by
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff]; exact ⟨subset_univ _, hd⟩
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · split_ifs with hd
    · exact hord d (hmem d hd)
    · exact isSelfVisible_bot _
  · by_cases hs : S.toCellScheme.grade s ≤ k
    · have hle (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
          S.toCellScheme.grade d ≤ k := (d.2.2 : S.toCellScheme.grade d ≤ _).trans hs
      have e : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
          min ((fun d ↦ if S.toCellScheme.grade d ≤ k then R d else ⊥) d.1)
            (if S.toCellScheme.grade s ≤ k then R s else ⊥)) =
          fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦ min (R d) (R s) := by
        funext d; beta_reduce; rw [ite_eq_left (hle d), ite_eq_left hs]
      rw [e]
      exact hloc s (hmem s hs)
    · have e : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
          min ((fun d ↦ if S.toCellScheme.grade d ≤ k then R d else ⊥) d.1)
            (if S.toCellScheme.grade s ≤ k then R s else ⊥)) = fun _ ↦ ⊥ := by
        funext d; rw [ite_eq_right hs, min_bot_right]
      rw [e]
      exact TransformsTo.bot _ _
  · by_cases ht : S.toCellScheme.grade t ≤ k
    · obtain ⟨u, hu, hle⟩ := havail s t (hmem t ht) hst hg
      have hgu : S.toCellScheme.grade u ≤ k := (congrArg Prod.snd hu).trans_le ht
      refine ⟨u, hu, ?_⟩
      simp only [ite_eq_left (hg.trans_le ht), ite_eq_left hgu]
      exact hle
    · refine ⟨t, rfl, ?_⟩
      simp only [ite_eq_right (hg ▸ ht : ¬ S.toCellScheme.grade s ≤ k)]
      exact bot_le

/-- **The rank tables of a state lawful below `(univ, 1)` are lawful**: the tables read the cells
of grade one only, where the state's order, locality and availability are those below
`(univ, 1)`. -/
theorem isLawful_rankTable_of_isLawfulBelow_one (hwf : S.IsWellFormed) {R : Fin S.card → Label.{u}}
    (hR : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d) {H : ℕ}
    (hH : ∀ d, rankVector R d ≤ H) {f : ℕ → Label.{u}}
    (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, IsSelfVisible 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then f (rankVector R d) else ⊥ := by
  obtain ⟨hord, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hR
  have hmem (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) :
      d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff]
    exact ⟨subset_univ _, hd.le⟩
  have hfb (d : Fin S.card) : f (rankVector R d) = ⊥ ↔ R d = ⊥ := by
    rw [← rankVector_eq_zero_iff (R := R)]
    refine ⟨fun h ↦ by_contra fun h' ↦ hp _ (Nat.pos_of_ne_zero h') (hH d) h, fun h ↦ ?_⟩
    rw [h, h0]
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · split_ifs with hd
    · rw [hd]; exact hv _
    · exact isSelfVisible_bot _
  · by_cases hs : S.toCellScheme.grade s = 1
    swap
    · have hz : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
          min ((fun d ↦ if S.toCellScheme.grade d = 1 then f (rankVector R d) else ⊥) d.1)
            (if S.toCellScheme.grade s = 1 then f (rankVector R s) else ⊥)) = fun _ ↦ ⊥ := by
        funext d; rw [ite_eq_right hs, min_bot_right]
      rw [hz]
      exact TransformsTo.bot _ _
    have hg1 (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        S.toCellScheme.grade d = 1 := by
      have h1 : S.toCellScheme.grade d ≤ 1 := hs ▸ d.2.2
      have h2 := hwf.isWellFormed.grade_pos d.1
      omega
    have hl := hloc s (hmem s hs)
    have hgr : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
        S.toCellScheme.grade d) = fun _ ↦ 1 := funext hg1
    rw [hgr] at hl ⊢
    have hvis (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) : IsSelfVisible 1 (R d) :=
      hd ▸ hord d (hmem d hd)
    have hqv (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        IsSelfVisible 1 (min (R d) (R s)) := (hvis _ (hg1 d)).min (hvis _ hs)
    have hmin (d : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        f (valueRank R (min (R d) (R s))) = min (f (rankVector R d)) (f (rankVector R s)) := by
      rw [(monotone_valueRank R).map_min, hf.map_min]; rfl
    have h := hl.comp_one hqv (θ := fun y ↦ f (valueRank R y)) (hf.comp (monotone_valueRank R))
      (fun d ↦ by rw [hmin]; exact (hv _).min (hv _)) fun d ↦ by
        rcases min_choice (R d) (R s) with h | h <;> rw [h]
        · exact hfb d
        · exact hfb s
    convert h using 2 with d
    rw [hmin, ite_eq_left (hg1 d), ite_eq_left hs]
  · by_cases ht : S.toCellScheme.grade t = 1
    · obtain ⟨u, hu, hle⟩ := havail s t (hmem t ht) hst hg
      have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
      refine ⟨u, hu, ?_⟩
      simp only [ite_eq_left (hg.trans ht), ite_eq_left hgu]
      exact hf (rankVector_le_rankVector hle)
    · refine ⟨t, rfl, ?_⟩
      simp only [ite_eq_right (hg ▸ ht : ¬ S.toCellScheme.grade s = 1)]
      exact bot_le

/-- **The rank member of a state lawful below `(univ, 1)`**: its rank vector, with dense ranks and
lawful tables (`Scheme.isLawful_rankTable_of_isLawfulBelow_one`). -/
noncomputable def RankMember.ofLawfulBelowOne {H : ℕ} (hwf : S.IsWellFormed) (hcard : S.card ≤ H)
    {R : Fin S.card → Label.{u}}
    (hR : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d) : RankMember S H :=
  ⟨fun d ↦ ⟨rankVector R d, Nat.lt_succ_of_le ((rankVector_le d).trans (by simpa using hcard))⟩,
    fun i hi d hd ↦ by
      obtain ⟨e, -, he⟩ := exists_valueRank_eq (Z := R) hi
        ((show i ≤ valueRank R (R d) from hd).trans (valueRank_le_card_values _))
      exact ⟨e, he⟩,
    fun _ hf h0 hv hp ↦ isLawful_rankTable_of_isLawfulBelow_one hwf hR
      (fun d ↦ (rankVector_le d).trans (by simpa using hcard)) hf h0 hv hp⟩

/-- **The translation**: on a lawful state the rank member from the grade one is that of
`Scheme.RankMember.ofLawful`. -/
theorem RankMember.ofLawfulBelowOne_eq_ofLawful {H : ℕ} (hwf : S.IsWellFormed)
    (hcard : S.card ≤ H) {R : Fin S.card → Label.{u}} (hR : S.rows.IsLawful R) :
    RankMember.ofLawfulBelowOne hwf hcard (hR.isLawfulBelow _) = RankMember.ofLawful hwf hcard hR :=
  rfl

end Scheme

namespace Scheme.LadderBaseData

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ}

/-- **The extension of a state with a given rank member**: the state on the base cells, the
positive table of the state at the base indices of the member on the ladder. -/
noncomputable def stateExtOf (R : Fin B.S.card → Label.{u}) (a : RankMember B.S H) :
    Fin (B.ladderBase H).card → Label.{u} :=
  Fin.append R fun j ↦ posTable R (baseIndex H (rankProf B.S H) a (Fin.natAdd _ j))

/-- **The translation**: on a lawful state, the extension with the rank member from the grade one
is `stateExt`. -/
theorem stateExtOf_eq_stateExt (hcard : B.S.card ≤ H) {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) :
    B.stateExtOf R (RankMember.ofLawfulBelowOne B.wf hcard (hR.isLawfulBelow _)) =
      B.stateExt H R := by
  rw [stateExt_of_isLawful hR hcard, RankMember.ofLawfulBelowOne_eq_ofLawful]
  rfl

/-- **The extension with the rank member from the grade one is lawful below the grade `k`**,
for a state lawful below `(univ, k)` (`k ≥ 1`) whose values are self-visible at `1`: it agrees below
`(univ, k)` with the extension of the truncation of the state to the grades at most `k`, a lawful
state, along the same rank member (`Scheme.isLawful_ladderExtend`). -/
theorem isLawfulBelow_stateExtOf (hH : 0 < H) (hcard : B.S.card ≤ H) {k : ℕ} (hk : 1 ≤ k)
    {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun d ↦ R d)
    (hv1 : ∀ e, IsSelfVisible 1 (R e)) :
    (B.ladderBase H).rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun t ↦
      B.stateExtOf R (RankMember.ofLawfulBelowOne B.wf hcard
        (hR.mono (show ((univ : Finset (Fin n)), 1) ≤ ((univ : Finset (Fin n)), k) from
          ⟨subset_rfl, hk⟩))) t := by
  classical
  set a := RankMember.ofLawfulBelowOne B.wf hcard
    (hR.mono (show ((univ : Finset (Fin n)), 1) ≤ ((univ : Finset (Fin n)), k) from
      ⟨subset_rfl, hk⟩)) with ha
  set T : Fin B.S.card → Label.{u} := fun d ↦ if B.S.toCellScheme.grade d ≤ k then R d else ⊥
    with hT
  set v : Fin (B.ladderBase H).card → Label.{u} :=
    Fin.append T fun j ↦ posTable R (baseIndex H (rankProf B.S H) a (Fin.natAdd _ j)) with hv
  have hlaw : (B.ladderBase H).rows.IsLawful v := by
    refine isLawful_ladderExtend B.wf hH (rankProf_le _ H) a (monotone_posTable)
      posTable_zero (isSelfVisible_posTable hv1) (fun _ hi _ ↦ posTable_ne_bot (by omega))
      ?_ fun t ht ↦ ?_
    · have e : (fun d ↦ v (Fin.castAdd _ d)) = T := funext fun d ↦ Fin.append_left _ _ d
      rw [e]
      exact isLawful_truncate hR
    · induction t using Fin.addCases with
      | left d =>
        rw [appendFullCellsScheme_grade_castAdd] at ht
        change Fin.append T _ (Fin.castAdd _ d) = _
        rw [Fin.append_left, baseIndex_castAdd]
        change (if B.S.toCellScheme.grade d ≤ k then R d else ⊥) = _
        rw [ite_eq_left (ht.trans_le hk)]
        exact (posTable_rankVector hv1 d).symm
      | right j => exact Fin.append_right _ _ j
  have e : (fun t : (B.ladderBase H).toCellScheme.below ((univ : Finset (Fin n)), k) ↦
      B.stateExtOf R a t) =
      fun t : (B.ladderBase H).toCellScheme.below ((univ : Finset (Fin n)), k) ↦ v t := by
    funext t
    obtain ⟨t, htk⟩ := t
    induction t using Fin.addCases with
    | left d =>
      have hd : B.S.toCellScheme.grade d ≤ k := by
        have := htk.2
        change (B.S.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k at this
        rwa [appendFullCellsScheme_grade_castAdd] at this
      change Fin.append R _ (Fin.castAdd _ d) = Fin.append T _ (Fin.castAdd _ d)
      rw [Fin.append_left, Fin.append_left, hT]
      beta_reduce
      rw [ite_eq_left hd]
    | right j =>
      change Fin.append R _ (Fin.natAdd _ j) = Fin.append T _ (Fin.natAdd _ j)
      rw [Fin.append_right, Fin.append_right]
  rw [e]
  exact hlaw.isLawfulBelow _

end Scheme.LadderBaseData

end VaughtConjecture

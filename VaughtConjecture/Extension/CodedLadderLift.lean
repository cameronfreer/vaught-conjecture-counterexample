/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.BaseLadderTower
import VaughtConjecture.Extension.CodedLadderBase

/-!
# Recognition and lifts on the strongly coded grade-one base

Roadmap, Layer 3 ((R3) and (R4), legality of the grade-one base at the ladder) and
Correspondence, item 1 (the strongly coded legal stage types).  All results here are native
constructions of this repository.

The statements used from the padded grade-one base (`Scheme.ladderBase`) by the ladder
carrier, proved for the coded ladder base (`Scheme.codedLadderBase`) with the same premises:

* `Scheme.exists_codedRender_of_isLawful`: every lawful section is, at grade one, `⊥` or a
  rendered table (`Scheme.render`), through the chart of the top rung on the coded sources;
* `Scheme.cappedLift_codedLadderBase_one`, `Scheme.cappedLift_codedLadderBase_rankMember`,
  `Scheme.cappedLift_codedLadderBase_rankMember_of_union`: the lifts into the full face of grade
  one, when `S` lifts and the members glue (`Scheme.RankGlue`, `Scheme.rankGlue_rankMember`);
* `Scheme.isConsistent_codedLadderBase_rankMember`: consistency over the rank members;
* `Scheme.isLawful_codedLadderExtend`: the extension lemma for states;
* over ladder base data (`Scheme.LadderBaseData.codedLadderBase`): well formed, consistent, coded,
  **strongly coded** when the base scheme is, and the extension of a lawful state
  (`Scheme.LadderBaseData.stateExt`) is lawful.

## References

Lawful sections are [Kni26, Definition 2.5.4]; bountifulness is [Kni26, Definition 2.5.14].

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {S : Scheme.{u} n} {Q : Type} [Fintype Q] {H : ℕ} {prof : Q → Fin S.card → ℕ}

/-! ### Lawful sections are rendered tables at grade one -/

/-- **Every lawful section of the coded ladder base is a rendered table at grade one**: it is `⊥`
at every cell of grade one, or for the member `b` with the largest top rung it reads a positive
table `F` at the base indices of `b` at every cell of grade one, the old cells included.  The table
is the chart of the top rung of `b` on the coded sources. -/
theorem exists_codedRender_of_isLawful [Nonempty Q] {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H) {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (codedLadderBase H prof hS).rows.IsLawful v) :
    (∀ t, (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 → v t = ⊥) ∨
      ∃ (b : Q) (F : ℕ → Label.{u}), Monotone F ∧ F 0 = ⊥ ∧ (∀ i, IsSelfVisible 1 (F i)) ∧
        (∀ i, 0 < i → i ≤ H → F i ≠ ⊥) ∧
        ∀ t, (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 →
          v t = F (baseIndex H prof b t) := by
  classical
  have hHl : H - 1 < H := by omega
  set top : Q → Fin (S.card + ladderCard S Q H) := fun b ↦
    Fin.natAdd _ (ladderEquiv S Q H (b, Sum.inl ⟨H - 1, hHl⟩)) with htop
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (fun b ↦ v (top b))
    Finset.univ_nonempty
  have hL := codedLadderLawful_of_isLawful hwf hv
  -- every cell of grade one lies below the top rung of `b`
  have hlad (p : LadderPt S Q H) : v (Fin.natAdd _ (ladderEquiv S Q H p)) ≤ v (top b) :=
    (hL.le_top (ladderCeil_le hprof) (fun a ↦ (a, Sum.inl ⟨H - 1, hHl⟩)) (fun _ ↦ rfl)
      (fun _ ↦ by simp only [ladderCeil, Sum.elim_inl]; omega) p).trans (hb _ (mem_univ _))
  have hgtop : (S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (top b) =
      ((univ : Finset (Fin n)), 1) := appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  have hdom (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) : v t ≤ v (top b) := by
    obtain ⟨u, hu, hle⟩ := hv.availability t (top b)
      (by rw [show (S.appendFullCellsScheme 1 (ladderCard S Q H)).scope (top b) = univ from
        congrArg Prod.fst hgtop]; exact subset_univ _)
      (by rw [ht, show (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade (top b) = 1 from
        congrArg Prod.snd hgtop])
    obtain ⟨p, rfl⟩ := exists_eq_ladder_of_gradedIndex hS (hu.trans hgtop)
    exact hle.trans (hlad p)
  by_cases h0 : v (top b) = ⊥
  · exact Or.inl fun t ht ↦ le_bot_iff.mp (h0 ▸ hdom t ht)
  right
  obtain ⟨g, σ, hw, heq⟩ := hv.locality (top b)
  set F : ℕ → Label.{u} := fun i ↦ min (σ (codedLadderSource H i)) (g 1) with hF
  have hmemb (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) :
      t ∈ (codedLadderBase H prof hS).toCellScheme.below
        ((codedLadderBase H prof hS).toCellScheme.gradedIndex (top b)) := by
    change _ ≤ (S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (top b)
    rw [hgtop]
    exact ⟨subset_univ _, ht.le⟩
  have hval (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) :
      v t = F (baseIndex H prof b t) := by
    have h := heq ⟨t, hmemb t ht⟩
    simp only at h
    rw [min_eq_left (hdom t ht)] at h
    have hrow := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
      (r := codedBaseRow H prof) (h := hS) (ladderEquiv S Q H (b, Sum.inl ⟨H - 1, hHl⟩))
      ⟨t, hmemb t ht⟩
    have ht1 : t ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) :=
      ⟨subset_univ _, ht.le⟩
    rw [codedBaseRow_of_mem hwf _ ht1, Equiv.symm_apply_apply] at hrow
    have hc : ladderCeil prof ((b, Sum.inl ⟨H - 1, hHl⟩) : LadderPt S Q H) = H := by
      simp only [ladderCeil, Sum.elim_inl]; omega
    rw [hc] at hrow
    rw [h, hF]
    simp only
    rw [← hrow]
    exact congrArg _ (congrArg g ht)
  -- the rungs of `b`
  have hrung (j : ℕ) (hj : j < H) :
      v (Fin.natAdd _ (ladderEquiv S Q H (b, Sum.inl ⟨j, hj⟩))) = F (j + 1) := by
    have hs := baseIndex_self hprof (b, Sum.inl ⟨j, hj⟩)
    simp only [ladderCeil, Sum.elim_inl] at hs
    rw [hval _ (appendFullCellsScheme_grade_natAdd _ _ _ _), hs]
  have hFmin (i : ℕ) : F (min i H) = F i := by
    simp only [hF, codedLadderSource_min]
  -- the rungs of `b` are positive
  obtain ⟨-, -, -, -, hrefl⟩ : ∃ (g' : ℕ → Label.{u}) (σ' : Label.{u} → Label.{u}),
      IsWitness g' σ' ∧ _ ∧ _ := hL.reflects hH (ladderCeil_le hprof) b
      (fun i ↦ (b, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ ↦ rfl)
      (fun i hi ↦ by simp only [ladderCeil, Sum.elim_inl]; omega) (by
        have hfin : (⟨min (H - 1) (H - 1), by omega⟩ : Fin H) = ⟨H - 1, hHl⟩ :=
          Fin.ext (min_self _)
        simp only [hfin]
        exact h0)
  refine ⟨b, F, fun i j hij ↦ min_le_min_right _ (hw.monotone (monotone_codedLadderSource H hij)),
    by simp only [hF, codedLadderSource_zero, hw.map_bot, min_eq_left bot_le], fun i ↦ ?_,
    fun i hi hiH ↦ ?_, hval⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [hF, codedLadderSource_zero, hw.map_bot, min_eq_left bot_le]
      exact isSelfVisible_bot _
    · have hm : min i H - 1 < H := by omega
      rw [← hFmin, show min i H = min i H - 1 + 1 by omega, ← hrung _ hm]
      have h := hv.orderly (Fin.natAdd S.card (ladderEquiv S Q H (b, Sum.inl ⟨_, hm⟩)))
      rwa [appendFullCellsScheme_grade_natAdd] at h
  · have hm : i - 1 < H := by omega
    rw [show i = i - 1 + 1 by omega, ← hrung _ hm]
    intro hz
    have h := (hrefl (b, Sum.inl ⟨i - 1, hm⟩)).not.mpr (by
      have hp := ladderIndex_parent (H := H) (prof := prof) (parent := Prod.fst)
        (ladderCeil_le hprof) ((b, Sum.inl ⟨i - 1, hm⟩) : LadderPt S Q H)
      simp only [ladderCeil, Sum.elim_inl] at hp
      rw [hp]; omega)
    exact h (by simp only [hz, min_eq_left bot_le])

/-! ### The lift into the full face of grade one -/

/-- **The old cells of a lawful section of the coded ladder base form a lawful section of `S`.** -/
theorem isLawful_castAdd_of_isLawful_coded {hS : S.NoFullOne}
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (codedLadderBase H prof hS).rows.IsLawful v) :
    S.rows.IsLawful fun d ↦ v (Fin.castAdd _ d) := by
  have h := hv.comap
    (isLowerEmbedding_castAdd (S := S) 1 (ladderCard S Q H) (codedBaseRow H prof) hS)
  rw [comap_rows_castAdd] at h
  exact h

/-- **The lift into the full face of grade one** (native construction): for `X ≤ (univ, 1)` not
above `(univ, 1)`, the coded ladder base lifts capped from `X` to `(univ, 1)` when `S` does and the
members glue. -/
theorem cappedLift_codedLadderBase_one [Nonempty Q] {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H) (hglue : RankGlue S H prof)
    {X : Finset (Fin n) × ℕ} (hXU : X ≤ ((univ : Finset (Fin n)), 1))
    (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X) (hold : S.rows.CappedLift hXU) :
    (codedLadderBase H prof hS).rows.CappedLift hXU := by
  classical
  refine CellScheme.Rows.cappedLift_of_forall_full hXU fun c hc w v hw hv hwv ↦ ?_
  have hc1 : IsSelfVisible 1 c := hc
  -- the cells below the full face of grade one are the cells of grade one
  have hgpos (t : Fin (S.card + ladderCard S Q H)) :
      0 < (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t := by
    induction t using Fin.addCases with
    | left d => rw [appendFullCellsScheme_grade_castAdd]; exact hwf.isWellFormed.grade_pos d
    | right j => rw [appendFullCellsScheme_grade_natAdd]; omega
  have hU (t : Fin (S.card + ladderCard S Q H)) :
      t ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) ↔
        (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 :=
    ⟨fun ht ↦ grade_eq_one_of_mem_below (prof := prof) (hS := hS) hwf ht,
      fun ht ↦ ⟨subset_univ _, ht.le⟩⟩
  have hSU (d : Fin S.card) : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), 1) ↔
      S.toCellScheme.grade d = 1 :=
    ⟨fun hd ↦ by
      have h1 := hwf.isWellFormed.grade_pos d
      have h2 : S.toCellScheme.grade d ≤ 1 := hd.2
      omega,
      fun hd ↦ ⟨subset_univ _, hd.le⟩⟩
  -- the cells below `X` are old cells of grade one
  have hXold (e : Fin (S.card + ladderCard S Q H))
      (he : e ∈ (codedLadderBase H prof hS).toCellScheme.below X) :
      ∃ d, e = Fin.castAdd _ d ∧ d ∈ S.toCellScheme.below X ∧
        S.toCellScheme.grade d = 1 := by
    rw [← image_castAdd_below (r := codedBaseRow H prof) (h := hS) hX] at he
    obtain ⟨d, hd, rfl⟩ := he
    exact ⟨d, rfl, hd, (hSU d).mp (S.toCellScheme.below_mono hXU hd)⟩
  -- the section `v`, made `⊥` above grade one, is lawful on the base
  set v0 : Fin (S.card + ladderCard S Q H) → Label.{u} := fun t ↦
    if (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 then v t else ⊥ with hv0
  have hv0l : (codedLadderBase H prof hS).rows.IsLawful v0 := by
    have h := isLawful_splice_bot (S := codedLadderBase H prof hS) (k := 1) hv
    convert h using 1
    funext t
    simp only [hv0, CellScheme.splice]
    by_cases ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1
    · rw [ite_eq_left ht, ite_eq_left ht.le]
    · rw [ite_eq_right ht, ite_eq_right (by have := hgpos t; omega)]
  -- the lift of `S`
  have hwold : S.rows.IsLawfulBelow X fun d ↦ w (Fin.castAdd _ d) :=
    (isLawfulBelow_codedLadderBase_iff hX).mp hw
  have hvold : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1)
      fun d ↦ v (Fin.castAdd _ d) := by
    have h := (isLawful_castAdd_of_isLawful_coded hv0l).isLawfulBelow ((univ : Finset (Fin n)), 1)
    convert h using 1
    funext d
    simp only [hv0, appendFullCellsScheme_grade_castAdd, ite_eq_left ((hSU d).mp d.2)]
  obtain ⟨q', hq', hq'c, hq'w⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXU).mp hold c hc
    (fun d ↦ w (Fin.castAdd _ d)) (fun d ↦ v (Fin.castAdd _ d)) hwold hvold
    fun d ↦ by
      have h := hwv (Fin.castAdd _ d) (by
        rw [← image_castAdd_below (r := codedBaseRow H prof) (h := hS) hX]
        exact ⟨d, d.2, rfl⟩)
      exact h
  set Y : Fin S.card → Label.{u} := CellScheme.Rows.extendBot _ q' with hY
  have hYl : S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then Y d else ⊥ := by
    have h := isLawful_splice_bot (S := S) (k := 1)
      (CellScheme.Rows.isLawfulBelow_extendBot.mpr hq')
    convert h using 1
    funext d
    simp only [CellScheme.splice]
    by_cases hd : S.toCellScheme.grade d = 1
    · rw [ite_eq_left hd, ite_eq_left hd.le]
    · rw [ite_eq_right hd, ite_eq_right (by have := hwf.isWellFormed.grade_pos d; omega)]
  have hYv (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) :
      min (Y d) c = min (v (Fin.castAdd _ d)) c := by
    rw [hY, CellScheme.Rows.extendBot_of_mem _ ((hSU d).mpr hd)]
    exact hq'c ⟨d, (hSU d).mpr hd⟩
  have hYw (d : Fin S.card) (hd : d ∈ S.toCellScheme.below X) : Y d = w (Fin.castAdd _ d) := by
    rw [hY, CellScheme.Rows.extendBot_of_mem _ (S.toCellScheme.below_mono hXU hd)]
    exact hq'w ⟨d, hd⟩
  -- the rendering of a glued table is the lift
  have hfinish (a : Q) (F' : ℕ → Label.{u}) (hF' : Monotone F') (hF'0 : F' 0 = ⊥)
      (hF'v : ∀ i, IsSelfVisible 1 (F' i)) (hF'p : ∀ i, 0 < i → i ≤ H → F' i ≠ ⊥)
      (hF'Y : ∀ d, S.toCellScheme.grade d = 1 → F' (prof a d) = Y d)
      (hcap : ∀ e ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1),
        min (render S H prof a F' e) c = min (v e) c) :
      ∃ r : Fin (S.card + ladderCard S Q H) → Label.{u},
        (codedLadderBase H prof hS).rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) (fun e ↦ r e) ∧
        (∀ e ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1),
          min (r e) c = min (v e) c) ∧
        ∀ e ∈ (codedLadderBase H prof hS).toCellScheme.below X, r e = w e := by
    refine ⟨render S H prof a F',
      (isLawful_codedRender hwf hH hprof a hF' hF'0 hF'v hF'p ?_).isLawfulBelow _,
      hcap, fun e he ↦ ?_⟩
    · convert hYl using 1
      funext d
      by_cases hd : S.toCellScheme.grade d = 1
      · rw [ite_eq_left hd, ite_eq_left hd, hF'Y d hd]
      · rw [ite_eq_right hd, ite_eq_right hd]
    · obtain ⟨d, rfl, hdX, hd1⟩ := hXold e he
      rw [render_castAdd, ite_eq_left hd1, hF'Y d hd1, hYw d hdX]
  by_cases hcb : c = ⊥
  · -- the cap `⊥`: gluing at the cut `0`
    obtain ⟨b⟩ := ‹Nonempty Q›
    obtain ⟨a, F', hF', hF'0, hF'v, hF'p, -, -, -, hF'Y⟩ := hglue b (codedLadderSource H) 0 c Y
      (monotone_codedLadderSource H) (codedLadderSource_zero H) (isSelfVisible_codedLadderSource H)
      (fun i hi hiH h0 ↦ by rw [codedLadderSource_eq_bot_iff] at h0; omega) (Nat.zero_le _)
      (fun _ h ↦ absurd h (Nat.not_lt_zero _)) (hcb ▸ bot_le) hc1 hYl
      (fun d _ ↦ by rw [hcb, min_bot_right, min_bot_right])
    exact hfinish a F' hF' hF'0 hF'v hF'p hF'Y fun e _ ↦ by rw [hcb, min_bot_right, min_bot_right]
  -- a positive cap: the shape of `v`
  rcases exists_codedRender_of_isLawful hwf hH hprof hv0l with
    hzero | ⟨b, F, hF, hF0, hFv, hFp, hFv0⟩
  · -- `v` is `⊥` at grade one: it is the lift
    refine ⟨v, hv, fun _ _ ↦ rfl, fun e he ↦ ?_⟩
    obtain ⟨d, rfl, -, hd1⟩ := hXold e he
    have hg : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade (Fin.castAdd _ d) = 1 :=
      by
      rw [appendFullCellsScheme_grade_castAdd]; exact hd1
    have h0 : v (Fin.castAdd _ d) = ⊥ := by
      have := hzero _ hg
      simpa only [hv0, ite_eq_left hg] using this
    have h := hwv _ he
    rw [h0, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h.symm with h' | h'
    · rw [h0, h']
    · exact absurd h' hcb
  have hvF (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) :
      v t = F (baseIndex H prof b t) := by
    have := hFv0 t ht
    simpa only [hv0, ite_eq_left ht] using this
  by_cases hreach : ∃ i, i ≤ H ∧ c ≤ F i
  swap
  · -- `F` stays below the cap: `v` is the lift
    push Not at hreach
    refine ⟨v, hv, fun _ _ ↦ rfl, fun e he ↦ ?_⟩
    obtain ⟨d, rfl, -, hd1⟩ := hXold e he
    have hg : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade (Fin.castAdd _ d) = 1 :=
      by
      rw [appendFullCellsScheme_grade_castAdd]; exact hd1
    have hlt : v (Fin.castAdd _ d) < c := by
      rw [hvF _ hg]; exact hreach _ (baseIndex_le hprof b _)
    have h := hwv _ he
    rw [min_eq_left hlt.le] at h
    rcases le_total (w (Fin.castAdd _ d)) c with hle | hle
    · rw [min_eq_left hle] at h; exact h
    · rw [min_eq_right hle] at h; exact absurd h hlt.ne
  -- the first rank where `F` reaches the cap
  set k := Nat.find hreach with hk
  obtain ⟨hkH, hck⟩ := Nat.find_spec hreach
  have hlow (i : ℕ) (hi : i < k) : F i < c := by
    have := Nat.find_min hreach hi
    push Not at this
    exact this (by omega)
  obtain ⟨a, F', hF', hF'0, hF'v, hF'p, hab, hF'low, hF'k, hF'Y⟩ := hglue b F k c Y hF hF0 hFv hFp
    hkH hlow hck hc1 hYl fun d hd ↦ by
      rw [hYv d hd, hvF _ (by rw [appendFullCellsScheme_grade_castAdd]; exact hd),
        baseIndex_castAdd]
  refine hfinish a F' hF' hF'0 hF'v hF'p hF'Y fun e he ↦ ?_
  have he1 := (hU e).mp he
  rw [min_render_eq_of_prefix hkH hab hF' hF hF'low hF'k hck e, hvF e he1, render, ite_eq_left he1]

/-! ### Over the rank members -/

/-- **The coded ladder base over the rank members is consistent.** -/
theorem isConsistent_codedLadderBase_rankMember {S : Scheme.{u} n} {H : ℕ} {hS : S.NoFullOne}
    (hwf : S.IsWellFormed) (hcons : S.rows.IsConsistent) (hH : 0 < H) :
    (codedLadderBase H (rankProf.{u} S H) hS).rows.IsConsistent :=
  isConsistent_codedLadderBase hwf hcons hH (rankProf_le S H) (rankTablesLawful_rankMember S H)

/-- **The lift into the full face of grade one over the rank members** (native construction): for
`X ≤ (univ, 1)` not above `(univ, 1)`, the coded ladder base over the rank members lifts capped
from `X` to `(univ, 1)` whenever `S` does, at a height at least the number of cells. -/
theorem cappedLift_codedLadderBase_rankMember {S : Scheme.{u} n} {H : ℕ} {hS : S.NoFullOne}
    (hwf : S.IsWellFormed) (hH : 0 < H) (hcard : S.card ≤ H) {X : Finset (Fin n) × ℕ}
    (hXU : X ≤ ((univ : Finset (Fin n)), 1)) (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X)
    (hold : S.rows.CappedLift hXU) :
    (codedLadderBase H (rankProf.{u} S H) hS).rows.CappedLift hXU :=
  cappedLift_codedLadderBase_one hwf hH (rankProf_le S H) (rankGlue_rankMember hwf hcard) hXU hX
    hold

/-- **The lift into the full face of grade one through two faces**, for the coded ladder base over
the rank members (`CellScheme.Rows.cappedLift_of_union`). -/
theorem cappedLift_codedLadderBase_rankMember_of_union {S : Scheme.{u} n} {H : ℕ}
    {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hcard : S.card ≤ H) {I U V O : Finset (Fin n) × ℕ}
    (hIU : I ≤ U) (hOU : O ≤ U) (hOV : O ≤ V) (hUY : U ≤ ((univ : Finset (Fin n)), 1))
    (hVY : V ≤ ((univ : Finset (Fin n)), 1)) (hI : ¬ ((univ : Finset (Fin n)), 1) ≤ I)
    (hcover : ∀ d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), 1),
      d ∈ S.toCellScheme.below U ∨ d ∈ S.toCellScheme.below V)
    (hinter : ∀ d ∈ S.toCellScheme.below U, d ∈ S.toCellScheme.below V →
      d ∈ S.toCellScheme.below O)
    (hleft : S.rows.CappedLift hIU) (hright : S.rows.CappedLift hOV) :
    (codedLadderBase H (rankProf.{u} S H) hS).rows.CappedLift (hIU.trans hUY) :=
  cappedLift_codedLadderBase_rankMember hwf hH hcard _ hI
    (CellScheme.Rows.cappedLift_of_union hIU hOU hOV hUY hVY hcover hinter hleft hright)

/-! ### States -/

/-- **The extension lemma** (native construction): a labelling `v` of the coded ladder base, lawful
on the old cells, reading a positive table `f` at the base indices of a member `a` at every cell of
grade one, is lawful. -/
theorem isLawful_codedLadderExtend {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hH : 0 < H)
    (hprof : ∀ a d, prof a d ≤ H) (a : Q) {f : ℕ → Label.{u}} (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, IsSelfVisible 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥)
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hold : S.rows.IsLawful fun d ↦ v (Fin.castAdd _ d))
    (hgr : ∀ t, (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 →
      v t = f (baseIndex H prof a t)) :
    (codedLadderBase H prof hS).rows.IsLawful v := by
  classical
  have hgr1 (t : Fin (S.card + ladderCard S Q H))
      (ht : t ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1)) :
      v t = f (baseIndex H prof a t) :=
    hgr t (grade_eq_one_of_mem_below (prof := prof) (hS := hS) hwf ht)
  refine isLawful_appendFullCells hold (fun j ↦ by
      rw [hgr _ (appendFullCellsScheme_grade_natAdd _ _ _ _)]; exact hv _)
    (fun i' ↦ ?_) (fun s hs ↦ ?_)
  · -- locality at the ladder point `i'`
    set c' := (ladderEquiv S Q H).symm i' with hc'
    set e := baseIndex H prof a (Fin.natAdd _ i') with he
    have hec : e ≤ ladderCeil prof c' := by
      rw [he, baseIndex_natAdd]; exact min_le_right _ _
    have hecut : e ≤ rankCut H (prof a) (prof c'.1) := by
      rw [he, baseIndex_natAdd]; exact min_le_left _ _
    have hmem (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        t.1 ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      refine ⟨subset_univ _, ?_⟩
      have h2 := t.2.2
      simp only [appendFullCellsScheme_gradedIndex_natAdd] at h2
      exact h2
    have hown : Fin.natAdd S.card i' ∈
        (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
    have htarget : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          min (v t) (v (Fin.natAdd _ i'))) =
        fun t ↦ f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e) := by
      funext t
      rw [hgr1 _ (hmem t), hgr1 _ hown, ← he, ← hf.map_min, min_assoc,
        min_eq_right hec, ← min_eq_right hecut, ← min_assoc, baseIndex_agree a c'.1 t.1,
        min_assoc]
    have hsource : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          codedBaseRow H prof i' t.1) =
        fun t ↦ codedLadderSource (ladderCeil prof c') (baseIndex H prof c'.1 t.1) := by
      funext t
      exact codedBaseRow_of_mem hwf i' (hmem t)
    have hgrade : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t) = fun _ ↦ 1 :=
      funext fun t ↦ grade_eq_one_of_mem_below (prof := prof) (hS := hS) hwf (hmem t)
    rw [hsource, htarget, hgrade]
    by_cases he0 : e = 0
    · have hz : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e)) =
          fun _ ↦ ⊥ := by
        funext t; rw [he0, Nat.min_zero, h0]
      rw [hz]
      exact TransformsTo.bot _ _
    · exact transformsTo_codedLadderSource
        (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            baseIndex H prof c'.1 t.1)
        (f := fun k ↦ f (min k e)) (fun _ _ h ↦ hf (min_le_min_right _ h)) (by simp [h0])
        (fun _ ↦ hv _) fun k hk _ ↦ hp _ (by omega) ((min_le_right _ _).trans
          (hecut.trans (rankCut_le H _ _)))
  · -- availability: the top rung of `a` dominates
    have hHl : H - 1 < H := by omega
    refine ⟨ladderEquiv S Q H (a, Sum.inl ⟨H - 1, hHl⟩), ?_⟩
    rw [hgr s hs, hgr _ (appendFullCellsScheme_grade_natAdd _ _ _ _),
      baseIndex_self hprof (a, Sum.inl ⟨H - 1, hHl⟩)]
    exact hf ((baseIndex_le hprof a s).trans (by simp only [ladderCeil, Sum.elim_inl]; omega))


/-! ### Over ladder base data -/

namespace LadderBaseData

variable {n : ℕ} (B : LadderBaseData.{u} n) (H : ℕ)

/-- **The coded ladder base over the rank members** of ladder base data (native construction). -/
noncomputable abbrev codedLadderBase : Scheme.{u} n :=
  Scheme.codedLadderBase H (rankProf B.S H) B.noFull

/-- The coded ladder base has the cell scheme of the padded grade-one base. -/
theorem codedLadderBase_toCellScheme :
    (B.codedLadderBase H).toCellScheme = (B.ladderBase H).toCellScheme := rfl

theorem isWellFormed_codedLadderBase (hn : 1 ≤ n) : (B.codedLadderBase H).IsWellFormed :=
  Scheme.isWellFormed_codedLadderBase B.wf hn

theorem isConsistent_codedLadderBase (hH : 0 < H) : (B.codedLadderBase H).rows.IsConsistent :=
  isConsistent_codedLadderBase_rankMember B.wf B.cons hH

theorem isCoded_codedLadderBase : (B.codedLadderBase H).IsCoded :=
  Scheme.isCoded_codedLadderBase B.coded

/-- **The coded ladder base of strongly coded ladder base data is strongly coded** (native
construction), at every height. -/
theorem isStronglyCoded_codedLadderBase (hsc : B.S.rows.IsStronglyCoded) :
    (B.codedLadderBase H).rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_codedLadderBase hsc

variable {B H}

/-- **The extension of a lawful state is a lawful section of the coded ladder base.** -/
theorem isLawful_stateExt_codedLadderBase {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (hH : 0 < H) (hcard : B.S.card ≤ H) :
    (B.codedLadderBase H).rows.IsLawful (B.stateExt H R) :=
  isLawful_codedLadderExtend B.wf hH (rankProf_le _ H)
    (RankMember.ofLawful B.wf hcard hR) monotone_posTable posTable_zero
    (isSelfVisible_posTable (B.isSelfVisible_one_of_isLawful hR))
    (fun _ hi _ ↦ posTable_ne_bot (by omega))
    (by
      convert hR using 1
      funext d
      exact stateExt_castAdd hR hcard d)
    (stateExt_of_grade_one hR hcard)

/-- **The lift into the full face of grade one** for the coded ladder base of ladder base data, at
a height at least the number of cells. -/
theorem cappedLift_codedLadderBase (hH : 0 < H) (hcard : B.S.card ≤ H)
    {X : Finset (Fin n) × ℕ} (hXU : X ≤ ((univ : Finset (Fin n)), 1))
    (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X) (hold : B.S.rows.CappedLift hXU) :
    (B.codedLadderBase H).rows.CappedLift hXU :=
  cappedLift_codedLadderBase_rankMember B.wf hH hcard hXU hX hold

end LadderBaseData

end VaughtConjecture.Scheme

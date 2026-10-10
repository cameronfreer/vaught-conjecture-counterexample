/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderSeedBase

/-!
# Complete states on the padded grade-one base

Roadmap, Layer 3 ((R3) and (R4), the controller rows of the recognizing growth carrier).

A **complete state** is a lawful section `R` of the amalgam of a seed: all cells, all grades.  Its
**positive table** (`Label.posTable R`) is `⊥` at `0` and above it the value table of `R`, at least
`1`: it is monotone, self-visible at `1` when `R` is, positive at every
positive rank, and reads `R` at its rank vector (`Label.posTable_rankVector`).

**The extension of a state to the base** (`Seed.stateExt`): `R` on the cells of the amalgam, and on
the ladder its positive table at the base indices of its rank member (`Scheme.RankMember.ofLawful`).
It is a lawful section of the padded grade-one base (`Seed.isLawful_stateExt`), by the general
**extension lemma** (`Scheme.isLawful_ladderExtend`): a labelling of the base, lawful on the old
cells and reading a positive table at the base indices of a member at every cell of grade one, is
lawful.  On the ladder the extension reads the rungs of the member of `R` as the table
(`Seed.stateExt_rung`), and its top rung dominates every value of `R` (`Seed.le_stateExt_top`).

## References

Lawful sections are [Kni26, Definition 2.5.4]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

variable {ι : Type*} [Fintype ι] {Z : ι → Label.{u}}

/-- A label self-visible at `1` other than `⊥` is at least `1`. -/
theorem one_le_of_isSelfVisible {x : Label.{u}} (hx : IsSelfVisible 1 x) (h0 : x ≠ ⊥) :
    (1 : Label.{u}) ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl h0
  | coe o =>
    have h1 : (1 : Ordinal.{u}) ≤ o % Ordinal.omega0 := by exact_mod_cast isSelfVisible_coe.mp hx
    have h2 : (1 : Ordinal.{u}) ≤ o := h1.trans (Ordinal.mod_le _ _)
    exact_mod_cast h2
  | top => exact le_top

/-- The **positive table** of `Z`: `⊥` at `0`, and at a positive rank the value table of `Z`, at
least `1`. -/
noncomputable def posTable (Z : ι → Label.{u}) (i : ℕ) : Label.{u} :=
  if i = 0 then ⊥ else max (valueTable Z i) 1

theorem posTable_zero : posTable Z 0 = ⊥ := by simp [posTable]

theorem monotone_posTable : Monotone (posTable Z) := by
  intro i i' hii'
  by_cases hi : i = 0
  · simp only [posTable, hi, ite_true]; exact bot_le
  · simp only [posTable, hi, ite_false, show i' ≠ 0 by omega]
    exact max_le_max (monotone_valueTable hii') le_rfl

theorem posTable_ne_bot {i : ℕ} (hi : i ≠ 0) : posTable Z i ≠ ⊥ := by
  simp only [posTable, hi, ite_false]
  exact fun h ↦ absurd (le_bot_iff.mp ((le_max_right _ _).trans h.le))
    (WithBot.coe_ne_bot (a := (1 : WithTop Ordinal.{u})))

theorem isSelfVisible_posTable (hZ : ∀ e, IsSelfVisible 1 (Z e)) (i : ℕ) :
    IsSelfVisible 1 (posTable Z i) := by
  unfold posTable
  split_ifs
  · exact isSelfVisible_bot _
  · exact (isSelfVisible_valueTable hZ i).max (isSelfVisible_one.mpr le_rfl)

/-- **The positive table reads `Z` at its rank vector**, for `Z` self-visible at `1`. -/
theorem posTable_rankVector (hZ : ∀ e, IsSelfVisible 1 (Z e)) (d : ι) :
    posTable Z (rankVector Z d) = Z d := by
  by_cases h0 : rankVector Z d = 0
  · rw [h0, posTable_zero, (rankVector_eq_zero_iff d).mp h0]
  · have hZd : Z d ≠ ⊥ := fun h ↦ h0 ((rankVector_eq_zero_iff d).mpr h)
    simp only [posTable, h0, ite_false]
    rw [rankVector, valueTable_valueRank, max_eq_left (one_le_of_isSelfVisible (hZ d) hZd)]

/-- Every value of `Z` lies below the positive table at any rank at least its rank. -/
theorem le_posTable (hZ : ∀ e, IsSelfVisible 1 (Z e)) {d : ι} {i : ℕ}
    (hi : rankVector Z d ≤ i) : Z d ≤ posTable Z i :=
  (posTable_rankVector hZ d).symm.le.trans (monotone_posTable hi)

/-- The positive table takes the values `⊥`, `1` and the values of `Z`. -/
theorem posTable_eq (i : ℕ) : posTable Z i = ⊥ ∨ posTable Z i = 1 ∨ ∃ e, posTable Z i = Z e := by
  classical
  unfold posTable
  split_ifs
  · exact .inl rfl
  · rcases max_choice (valueTable Z i) 1 with h | h <;> rw [h]
    · by_cases hne : (univ.filter fun e ↦ valueRank Z (Z e) ≤ i).Nonempty
      · obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_sup _ hne Z
        exact .inr (.inr ⟨e, he⟩)
      · rw [not_nonempty_iff_eq_empty] at hne
        exact .inl (by rw [valueTable, hne, sup_empty])
    · exact .inr (.inl rfl)

end Label

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {Q : Type} [Fintype Q] {H : ℕ} {prof : Q → Fin S.card → ℕ}

/-- **The extension lemma**: a labelling `v` of the ladder base, lawful on the old cells, reading a
positive table `f` at the base indices of a member `a` at every cell of grade one, is lawful. -/
theorem isLawful_ladderExtend {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hH : 0 < H)
    (hprof : ∀ a d, prof a d ≤ H) (a : Q) {f : ℕ → Label.{u}} (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, IsSelfVisible 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥)
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hold : S.rows.IsLawful fun d ↦ v (Fin.castAdd _ d))
    (hgr : ∀ t, (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 →
      v t = f (baseIndex H prof a t)) :
    (ladderBase H prof hS).rows.IsLawful v := by
  classical
  have hgr1 (t : Fin (S.card + ladderCard S Q H))
      (ht : t ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1)) :
      v t = f (baseIndex H prof a t) := hgr t (grade_eq_one_of_mem_below hwf ht)
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
        t.1 ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      refine ⟨subset_univ _, ?_⟩
      have h2 := t.2.2
      simp only [appendFullCellsScheme_gradedIndex_natAdd] at h2
      exact h2
    have hown : Fin.natAdd S.card i' ∈
        (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
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
          baseRow H prof i' t.1) =
        fun t ↦ ladderSource (ladderCeil prof c') (baseIndex H prof c'.1 t.1) := by
      funext t
      exact baseRow_of_mem hwf i' (hmem t)
    have hgrade : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t) = fun _ ↦ 1 :=
      funext fun t ↦ grade_eq_one_of_mem_below hwf (hmem t)
    rw [hsource, htarget, hgrade]
    by_cases he0 : e = 0
    · have hz : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e)) =
          fun _ ↦ ⊥ := by
        funext t; rw [he0, Nat.min_zero, h0]
      rw [hz]
      exact TransformsTo.bot _ _
    · exact transformsTo_ladderSource (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            baseIndex H prof c'.1 t.1) (by omega)
        (f := fun k ↦ f (min k e)) (fun _ _ h ↦ hf (min_le_min_right _ h)) (by simp [h0])
        (fun _ ↦ hv _) fun k hk _ ↦ hp _ (by omega) ((min_le_right _ _).trans
          (hecut.trans (rankCut_le H _ _)))
  · -- availability: the top rung of `a` dominates
    have hHl : H - 1 < H := by omega
    refine ⟨ladderEquiv S Q H (a, Sum.inl ⟨H - 1, hHl⟩), ?_⟩
    rw [hgr s hs, hgr _ (appendFullCellsScheme_grade_natAdd _ _ _ _),
      baseIndex_self hprof (a, Sum.inl ⟨H - 1, hHl⟩)]
    exact hf ((baseIndex_le hprof a s).trans (by simp only [ladderCeil, Sum.elim_inl]; omega))

end Scheme

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {Q : Type} [Fintype Q] {H : ℕ} {prof : Q → Fin S.card → ℕ}

/-- **A ladder point reads another** through the code, at its ceiling, of the base index of its
member. -/
theorem rowAt_ladderBase_ladder {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (p q : LadderPt S Q H) :
    (ladderBase H prof hS).rowAt (Fin.natAdd _ (ladderEquiv S Q H p))
      (Fin.natAdd _ (ladderEquiv S Q H q)) =
    ladderSource (ladderCeil prof p)
      (baseIndex H prof p.1 (Fin.natAdd _ (ladderEquiv S Q H q))) := by
  have hq : Fin.natAdd S.card (ladderEquiv S Q H q) ∈
      (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
  have hmem : Fin.natAdd S.card (ladderEquiv S Q H q) ∈
      (ladderBase H prof hS).toCellScheme.below
        ((ladderBase H prof hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (ladderEquiv S Q H p))) := by
    change (S.appendFullCellsScheme 1 _).gradedIndex _ ≤ (S.appendFullCellsScheme 1 _).gradedIndex _
    rw [appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
  rw [rowAt_of_mem hmem]
  have h1 := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
    (r := baseRow H prof) (h := hS) (ladderEquiv S Q H p) ⟨_, hmem⟩
  rw [h1, baseRow_of_mem hwf _ hq, Equiv.symm_apply_apply]

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (H : ℕ)

/-- The values of a lawful state are self-visible at `1`. -/
theorem isSelfVisible_one_of_isLawful {R : Fin I.amalgam.card → Label.{u}}
    (hR : I.amalgam.rows.IsLawful R) (d : Fin I.amalgam.card) : IsSelfVisible 1 (R d) :=
  (hR.orderly d).mono (I.amalgam.isWellFormed.isWellFormed.grade_pos d)

open Classical in
/-- **The extension of a state to the base**: `R` on the cells of the amalgam, and on the ladder
the positive table of `R` at the base indices of its rank member; `⊥` for a state that is not
lawful or a height below the number of cells. -/
noncomputable def stateExt (R : Fin I.amalgam.card → Label.{u}) :
    Fin (I.ladderBase H).card → Label.{u} :=
  if h : I.amalgam.rows.IsLawful R ∧ I.amalgam.card ≤ H then
    Fin.append R fun j ↦ posTable R (Scheme.baseIndex H (Scheme.rankProf I.amalgam.toScheme H)
      (Scheme.RankMember.ofLawful I.amalgam.isWellFormed h.2 h.1) (Fin.natAdd _ j))
  else fun _ ↦ ⊥

variable {I H}

theorem stateExt_of_isLawful {R : Fin I.amalgam.card → Label.{u}}
    (hR : I.amalgam.rows.IsLawful R) (hcard : I.amalgam.card ≤ H) :
    I.stateExt H R = Fin.append R fun j ↦ posTable R (Scheme.baseIndex H
      (Scheme.rankProf I.amalgam.toScheme H)
        (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR) (Fin.natAdd _ j)) := by
  unfold stateExt
  rw [dite_eq_left ⟨hR, hcard⟩]

/-- **The extension reads the state on the amalgam.** -/
theorem stateExt_castAdd {R : Fin I.amalgam.card → Label.{u}} (hR : I.amalgam.rows.IsLawful R)
    (hcard : I.amalgam.card ≤ H) (d : Fin I.amalgam.card) :
    I.stateExt H R (Fin.castAdd _ d) = R d := by
  rw [stateExt_of_isLawful hR hcard, Fin.append_left]

/-- **At grade one the extension reads the positive table of the state at the base indices of
its rank member.** -/
theorem stateExt_of_grade_one {R : Fin I.amalgam.card → Label.{u}}
    (hR : I.amalgam.rows.IsLawful R) (hcard : I.amalgam.card ≤ H)
    (t : Fin (I.ladderBase H).card)
    (ht : (I.amalgam.toScheme.appendFullCellsScheme 1
      (Scheme.ladderCard I.amalgam.toScheme (Scheme.RankMember I.amalgam.toScheme H) H)).grade t
        = 1) :
    I.stateExt H R t = posTable R (Scheme.baseIndex H (Scheme.rankProf I.amalgam.toScheme H)
      (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR) t) := by
  rw [stateExt_of_isLawful hR hcard]
  induction t using Fin.addCases with
  | left d =>
    rw [Fin.append_left, Scheme.baseIndex_castAdd, Scheme.rankProf_ofLawful,
      posTable_rankVector (I.isSelfVisible_one_of_isLawful hR)]
  | right j => rw [Fin.append_right]

/-- **The extension of a lawful state is a lawful section of the base.** -/
theorem isLawful_stateExt {R : Fin I.amalgam.card → Label.{u}} (hR : I.amalgam.rows.IsLawful R)
    (hH : 0 < H) (hcard : I.amalgam.card ≤ H) : (I.ladderBase H).rows.IsLawful (I.stateExt H R) :=
  Scheme.isLawful_ladderExtend I.amalgam.isWellFormed hH (Scheme.rankProf_le _ H)
    (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR) monotone_posTable posTable_zero
    (isSelfVisible_posTable (I.isSelfVisible_one_of_isLawful hR))
    (fun _ hi _ ↦ posTable_ne_bot (by omega))
    (by
      convert hR using 1
      funext d
      exact stateExt_castAdd hR hcard d)
    (stateExt_of_grade_one hR hcard)

end Seed

end VaughtConjecture

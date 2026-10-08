/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralBelow
import VaughtConjecture.Extension.UnionFillCounterexample

/-!
# The extension above the grade `1` fails on three points (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

**`H2.ExtAbove` is not a property of every legal stage type** (`H2.not_extAbove_T`,
`H2.not_extAboveAt_two`): for the legal type `T` on three points of
`VaughtConjecture.Extension.UnionFillCounterexample` (the coupling row of its cell at
`(univ, 2)` reads the cell of the common face `{0, 1}` at the grade `2` at most the cell at
`({2}, 1)`), with its face on `{0, 1}`, the extension above the grade `1` to the grade `2` fails
at the cap `2`: the face `labelling 2 ⊥` (the cells of grade `1` at `2`), the root prescription
`labelling ⊤ ⊤` (the cell of the common face at the grade `2` at `⊤`), and the reference
`labelling 2 2` satisfy every hypothesis, and an extension would have `⊤ ≤ 2` by the coupling.

This is the union-fill failure (`UnionFillCounterexample.not_unionFill_seed`) on the faces
`(univ, 1)` and `({0, 1}, 2)` of one stage type.  So `H2.ExtAboveAt 2` is false, and the engine
below the full grade (`H2.admittedCompletionsBelowAt_of_ext`) cannot take the extension above `K`
as a property of every legal type for `K < k`: the lift at the grades above `K` must use more of
the context (the clause allows raising the designated tops, which the extension holds fixed).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType CellScheme UnionFillCounterexample

variable {α : Ordinal.{u}}

/-- A labelling of the cells of `S`, carried to `T` with `⊥` at the apex. -/
noncomputable def extT (f : Fin 9 → Label.{u}) : Fin (T α).card → Label.{u} :=
  fun c ↦ if h : (c : ℕ) < 9 then f ⟨c, h⟩ else ⊥

theorem extT_castSucc (f : Fin 9 → Label.{u}) (d : Fin 9) :
    extT (α := α) f (Fin.castSucc d) = f d := by
  change (if h : (d : ℕ) < 9 then f ⟨d, h⟩ else ⊥) = f d
  exact dite_eq_left d.2

theorem cases_T' (c : Fin (T α).card) : c = Fin.last 9 ∨ ∃ d : Fin 9, c = Fin.castSucc d := by
  change Fin (9 + 1) at c
  induction c using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

theorem extT_last (f : Fin 9 → Label.{u}) : extT (α := α) f (Fin.last 9) = ⊥ := by
  change (if h : 9 < 9 then f ⟨9, h⟩ else ⊥) = ⊥
  exact dite_eq_right (by omega)

theorem grade_T_castSucc (d : Fin 9) :
    (T α).toCellScheme.grade (Fin.castSucc d) = cellGrade d :=
  congrArg Prod.snd (gradedIndex_T_castSucc d)

theorem grade_T_last : (T α).toCellScheme.grade (Fin.last 9) = 3 :=
  congrArg Prod.snd (gradedIndex_T_last (α := α))

private theorem not_univ_three_le' {k : ℕ} (hk : k < 3) {B : Finset (Fin 3)} :
    ¬ ((univ : Finset (Fin 3)), 3) ≤ (B, k) := fun h ↦ absurd h.2 (by simpa using hk)

theorem scope_T_castSucc (d : Fin 9) :
    (T α).toCellScheme.scope (Fin.castSucc d) = cellScope d :=
  congrArg Prod.fst (gradedIndex_T_castSucc d)

theorem scope_T_last : (T α).toCellScheme.scope (Fin.last 9) = univ :=
  congrArg Prod.fst (gradedIndex_T_last (α := α))

/-- `labelling A F`, carried to `T`, is lawful below `(univ, k)`, `k ≤ 2`. -/
theorem isLawfulBelow_extT {A F : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F)
    (hFA : F ≤ A) {k : ℕ} (hk : k ≤ 2) :
    (T α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), k)
      (fun c ↦ extT (α := α) (labelling A F) c) := by
  refine (isLawfulBelow_T_iff (not_univ_three_le' (by omega))).mpr ?_
  have := (isLawfulBelow_iff (Y := ((univ : Finset (Fin 3)), k))
    (x := fun d ↦ extT (α := α) (labelling A F) (Fin.castSucc d))).mpr
    ⟨A, F, hA, hF, hFA, fun d _ ↦ extT_castSucc _ d⟩
  exact this

/-- **The extension above the grade `1` fails for `T`** with its face on `{0, 1}`. -/
theorem not_extAbove_T : ¬ ExtAbove (T α) restrictFace_T 1 := by
  intro hext
  have h2sv1 : IsSelfVisible 1 (2 : Label.{u}) := by simp
  have h2sv2 : IsSelfVisible 2 (2 : Label.{u}) := by simp
  have hbot2 : IsSelfVisible 2 (⊥ : Label.{u}) := isSelfVisible_bot 2
  have htop1 : IsSelfVisible 1 (⊤ : Label.{u}) := isSelfVisible_top 1
  have htop2 : IsSelfVisible 2 (⊤ : Label.{u}) := isSelfVisible_top 2
  let w : Fin (T α).card → Label.{u} := extT (labelling 2 ⊥)
  let R : Fin (T α).card → Label.{u} := extT (labelling 2 2)
  let ytop : Fin (T α).card → Label.{u} := extT (labelling ⊤ ⊤)
  let y : Fin (faceT α).card → Label.{u} := fun i ↦ ytop (StageType.faceCell restrictFace_T i)
  have hwv (d : Fin 9) : w (Fin.castSucc d) = labelling 2 ⊥ d := extT_castSucc _ d
  have hRv (d : Fin 9) : R (Fin.castSucc d) = labelling 2 2 d := extT_castSucc _ d
  have hyv (d : Fin 9) : ytop (Fin.castSucc d) = labelling ⊤ ⊤ d := extT_castSucc _ d
  have hwlast : w (Fin.last 9) = ⊥ := extT_last _
  have hdead : ∀ d : Fin 9, cellScope d ⊆ {0, 1} → cellGrade d ≤ 1 → live d = false := by
    decide
  have hlab_dead {A F : Label.{u}} {d : Fin 9} (hd : live d = false) : labelling A F d = ⊥ := by
    unfold labelling; exact ite_eq_right (by simp [hd])
  -- the grade-`1` face
  have hwL : LawfulAt (T α) 1 w := by
    refine ⟨isLawfulBelow_extT h2sv1 hbot2 bot_le (by omega), fun c hc ↦ ?_⟩
    rcases cases_T' c with rfl | ⟨d, rfl⟩
    · exact hwlast
    · refine (hwv d).trans ?_
      have hc' : ¬ cellGrade d ≤ 1 := fun h ↦ hc ((grade_T_castSucc (α := α) d).trans_le h)
      unfold labelling
      split_ifs <;> simp_all
  have hRl := isLawfulBelow_extT (α := α) h2sv1 h2sv2 le_rfl (k := 2) le_rfl
  have hyl : (faceT α).rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) (fun i ↦ y i) :=
    isLawfulBelow_face restrictFace_T (isLawfulBelow_extT htop1 htop2 le_rfl le_rfl)
  -- the cells of the face
  have hface (i : Fin (faceT α).card) : ∃ d : Fin 9, StageType.faceCell restrictFace_T i =
      Fin.castSucc d ∧ cellScope d ⊆ {0, 1} := by
    have hs := StageType.scope_faceCell restrictFace_T i
    rcases cases_T' (StageType.faceCell restrictFace_T i) with h | ⟨d, h⟩
    · exfalso
      have hs' : (univ : Finset (Fin 3)) =
          ((faceT α).toCellScheme.scope i).map (Coatom.face 2) :=
        (scope_T_last (α := α)).symm.trans ((congrArg (T α).toCellScheme.scope h).symm.trans hs)
      have h2 : (2 : Fin 3) ∈ ((faceT α).toCellScheme.scope i).map (Coatom.face 2) :=
        hs' ▸ mem_univ _
      obtain ⟨x, -, hx⟩ := mem_map.mp h2
      exact absurd hx ((by decide : ∀ x : Fin 2, (Coatom.face 2) x ≠ 2) x)
    · refine ⟨d, h, ?_⟩
      have hs' : cellScope d = ((faceT α).toCellScheme.scope i).map (Coatom.face 2) :=
        (scope_T_castSucc (α := α) d).symm.trans
          ((congrArg (T α).toCellScheme.scope h).symm.trans hs)
      rw [hs']
      intro x hx
      obtain ⟨z, -, rfl⟩ := mem_map.mp hx
      exact (by decide : ∀ z : Fin 2, (Coatom.face 2) z ∈ ({0, 1} : Finset (Fin 3))) z
  have hgrade_face (i : Fin (faceT α).card) (d : Fin 9)
      (hd : StageType.faceCell restrictFace_T i = Fin.castSucc d) :
      (faceT α).toCellScheme.grade i = cellGrade d :=
    (StageType.grade_faceCell restrictFace_T i).symm.trans
      ((congrArg (T α).toCellScheme.grade hd).trans (grade_T_castSucc d))
  have hwy (i : Fin (faceT α).card) (hi : (faceT α).toCellScheme.grade i ≤ 1) :
      w (StageType.faceCell restrictFace_T i) = y i := by
    obtain ⟨d, hd, hds⟩ := hface i
    have hl := hdead d hds ((hgrade_face i d hd).symm.trans_le hi)
    exact (congrArg w hd).trans ((hwv d).trans ((hlab_dead hl).trans ((hlab_dead hl).symm.trans
      ((hyv d).symm.trans (congrArg ytop hd).symm))))
  have hwR (c : Fin (T α).card) (hc : (T α).toCellScheme.grade c ≤ 1) :
      min (w c) 2 = min (R c) 2 := by
    rcases cases_T' c with rfl | ⟨d, rfl⟩
    · exact absurd ((grade_T_last (α := α)).symm.trans_le hc) (by omega)
    · have hc' : cellGrade d ≤ 1 := (grade_T_castSucc (α := α) d).symm.trans_le hc
      have hpos : 1 ≤ cellGrade d := (by decide : ∀ d : Fin 9, 1 ≤ cellGrade d) d
      have e : min (labelling (2 : Label.{u}) ⊥ d) 2 = min (labelling 2 2 d) 2 := by
        unfold labelling
        split_ifs with h1 h2
        · rfl
        · omega
        · rfl
      exact (congrArg (min · 2) (hwv d)).trans (e.trans (congrArg (min · 2) (hRv d)).symm)
  have hyR (i : Fin (faceT α).card) (_ : (faceT α).toCellScheme.grade i ≤ 2) :
      min (y i) 2 = min (R (StageType.faceCell restrictFace_T i)) 2 := by
    obtain ⟨d, hd, -⟩ := hface i
    have e : min (labelling (⊤ : Label.{u}) ⊤ d) 2 = min (labelling 2 2 d) 2 := by
      unfold labelling
      split_ifs <;> simp
    exact (congrArg (min · 2) ((congrArg ytop hd).trans (hyv d))).trans
      (e.trans (congrArg (min · 2) ((congrArg R hd).trans (hRv d))).symm)
  obtain ⟨W, hW, hWK, hWr, -⟩ := hext (j := 2) (by omega) (by omega) h2sv2 hwL hRl hyl hwy hwR hyR
  -- the coupling in `T`
  have hW' := (isLawfulBelow_T_iff (α := α) (w := W) (not_univ_three_le' (by omega))).mp hW
  obtain ⟨A, F, -, -, hFA, hAF⟩ := (isLawfulBelow_iff (x := fun e ↦ W (Fin.castSucc e))).mp hW'
  have hA : A = 2 := by
    have e1 : W (Fin.castSucc (2 : Fin 9)) = labelling A F 2 :=
      hAF (2 : Fin 9) ⟨subset_univ _, by decide⟩
    have e2 : W (Fin.castSucc (2 : Fin 9)) = w (Fin.castSucc (2 : Fin 9)) :=
      hWK (Fin.castSucc (2 : Fin 9)) ((grade_T_castSucc (α := α) 2).trans_le (by decide))
    have e3 : labelling A F 2 = labelling (2 : Label.{u}) ⊥ 2 :=
      e1.symm.trans (e2.trans (hwv 2))
    unfold labelling at e3
    simpa [live, cellGrade] using e3
  have hF : F = ⊤ := by
    have hvis : Fin.castSucc (6 : Fin 9) ∈
        (T α).toScheme.visibleCells (Coatom.face 2) := by
      refine Scheme.mem_visibleCells.mpr fun x hx ↦ ?_
      have hx' : x ∈ cellScope 6 := (scope_T_castSucc (α := α) 6) ▸ mem_coe.mp hx
      rcases (by decide : ∀ x : Fin 3, x ∈ cellScope 6 → x = 0 ∨ x = 1) x hx' with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace restrictFace_T) hvis
    have hi' : StageType.faceCell restrictFace_T i = Fin.castSucc (6 : Fin 9) := hi
    have e1 : W (Fin.castSucc (6 : Fin 9)) = labelling A F 6 :=
      hAF (6 : Fin 9) ⟨subset_univ _, by decide⟩
    have e2 : W (StageType.faceCell restrictFace_T i) =
        ytop (StageType.faceCell restrictFace_T i) :=
      hWr i ((hgrade_face i 6 hi').trans_le (by decide))
    have e3 : labelling A F 6 = labelling (⊤ : Label.{u}) ⊤ 6 :=
      e1.symm.trans ((congrArg W hi').symm.trans (e2.trans ((congrArg ytop hi').trans (hyv 6))))
    unfold labelling at e3
    simpa [live, cellGrade] using e3
  rw [hA, hF] at hFA
  have h2top : (2 : Label.{u}) ≠ ⊤ := by
    have h23 : ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u}) := natCast_label_lt.mpr (by norm_num)
    have h2 : ((2 : ℕ) : Label.{u}) = 2 := Nat.cast_ofNat
    rw [h2] at h23
    exact ne_top_of_lt h23
  exact h2top (top_le_iff.mp hFA)

/-- **`H2.ExtAboveAt 2` is false.** -/
theorem not_extAboveAt_two : ¬ ExtAboveAt.{u} 2 := fun h ↦
  not_extAbove_T (α := 0) (h (T 0) (isLegal_T 0) restrictFace_T one_pos one_lt_two)

end VaughtConjecture.H2

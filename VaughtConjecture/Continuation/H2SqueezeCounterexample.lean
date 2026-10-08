/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralRaised
import VaughtConjecture.Continuation.H2SqueezeType

/-!
# The raised extension above the grade `1` fails on three points (work file)

WORK FILE (branch `research/work-h2-squeeze`).  No `sorry`.

**`H2.ExtAboveRaised` is not a property of every legal stage type**
(`H2.not_extAboveRaised_squeeze`, `H2.not_extAboveRaisedAt_two`).  On the legal squeeze type
`SqueezeType.T` on three points, with its face on `{0, 1}`, at `K = 1`, `j = 2`, and the cap
`h = 2`, take `v = 3` and
* the grade-`1` face `w = lab 2 3 ⊥` (the cell `2` at `({2}, 1)` labelled `h`, the root cell `3`
  at `({0, 1}, 1)` labelled `v`);
* the reference `R = lab 3 3 3`, and the root prescription `y` its restriction to the face (the
  root cells `3` and `6`, at `({0, 1}, 1)` and `({0, 1}, 2)`, at `v`).
Every extension `W` lawful below `(univ, 2)` is some `lab A B F` with `F ≤ A ≤ B`; the root fixes
`B = W 3 = v` and `F = W 6 = v`, so `W 2 = A = v`.  The raised form allows at the cell `2` only
`w 2 = h` or `⊤`: it fails.  (The cell `6` lies below the cell `2` through the row of the cell `8`
at `(univ, 2)`; the cell `2` lies below the cell `3` through the row of the cell `5` at
`(univ, 1)`, which reads them differently, so `w 2 < w 3` is allowed at the grade `1`.)

**What this does not refute (argued).**  The clause itself is not refuted by the squeeze at a
source-gap context.  If the cell `2` of a donor is a designated top, the coupling of the cell `2`
below the root cell `3` in every lawful labelling makes the root cell `3` a top of the common
face, hence a top of the context avoiding the lost point.  The frontier of every lawful labelling
of a source-gap context is at most its value at every such top
(`StageType.IsSourceGapContextAt.frontier_le`, compiled for lawful labellings of the context), so
at most `v`, and the forced value `W 2 = v` meets the clause.  So the squeeze refutes the raise
rule (only `w` or `⊤`), not the clause.  For the grade-`K` faces read by the clause:
`H2.frontierAt_le_of_lawfulAt` (the frontier of a grade-`K` face of a legal source-gap context is
at most its value at every top avoiding the lost point) and `H2.selfLow_of_le_top` (the clause
holds when every designated top of the donor face is at least such a value of the context face).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType CellScheme SqueezeType

variable {α : Ordinal.{u}}

/-! ### Cells of the squeeze type -/

/-- A labelling of the cells of `S`, carried to the squeeze type with `⊥` at the cell of grade
`3`. -/
noncomputable def extSq (f : Fin 9 → Label.{u}) : Fin (SqueezeType.T α).card → Label.{u} :=
  fun c ↦ if h : (c : ℕ) < 9 then f ⟨c, h⟩ else ⊥

theorem extSq_castSucc (f : Fin 9 → Label.{u}) (d : Fin 9) :
    extSq (α := α) f (Fin.castSucc d) = f d := by
  change (if h : (d : ℕ) < 9 then f ⟨d, h⟩ else ⊥) = f d
  exact dite_eq_left d.2

theorem extSq_last (f : Fin 9 → Label.{u}) : extSq (α := α) f (Fin.last 9) = ⊥ := by
  change (if h : 9 < 9 then f ⟨9, h⟩ else ⊥) = ⊥
  exact dite_eq_right (by omega)

theorem cases_Sq (c : Fin (SqueezeType.T α).card) :
    c = Fin.last 9 ∨ ∃ d : Fin 9, c = Fin.castSucc d := by
  change Fin (9 + 1) at c
  induction c using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

theorem grade_Sq_castSucc (d : Fin 9) :
    (SqueezeType.T α).toCellScheme.grade (Fin.castSucc d) = cellGrade d :=
  Scheme.appendFullCellScheme_grade_castSucc SqueezeType.S.{u} 3 d

theorem grade_Sq_last : (SqueezeType.T α).toCellScheme.grade (Fin.last 9) = 3 :=
  Scheme.appendFullCellScheme_grade_last SqueezeType.S.{u} 3

theorem scope_Sq_castSucc (d : Fin 9) :
    (SqueezeType.T α).toCellScheme.scope (Fin.castSucc d) = cellScope d :=
  Scheme.appendFullCellScheme_scope_castSucc SqueezeType.S.{u} 3 d

theorem scope_Sq_last : (SqueezeType.T α).toCellScheme.scope (Fin.last 9) = univ :=
  Scheme.appendFullCellScheme_scope_last SqueezeType.S.{u} 3

private theorem not_univ_three_le_sq {k : ℕ} (hk : k < 3) {B : Finset (Fin 3)} :
    ¬ ((univ : Finset (Fin 3)), 3) ≤ (B, k) := fun h ↦ absurd h.2 (by simpa using hk)

/-- Below a pair not above `(univ, 3)`, lawfulness in the squeeze type is lawfulness in `S`. -/
theorem isLawfulBelow_Sq_iff {X : Finset (Fin 3) × ℕ} (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X)
    {w : Fin (SqueezeType.T α).card → Label.{u}} :
    (SqueezeType.T α).rows.IsLawfulBelow X (fun d ↦ w d) ↔
      SqueezeType.rows.IsLawfulBelow X (fun d ↦ w (Fin.castSucc d.1)) :=
  Scheme.isLawfulBelow_appendFullCell_iff (S := SqueezeType.S) (r := fun _ ↦ ⊥)
    (h := isLegalBelow_S.{u}.not_le) hX

/-- `lab a b F`, carried to the squeeze type, is lawful below `(univ, k)`, `k ≤ 2`. -/
theorem isLawfulBelow_extSq {a b F : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hF : IsSelfVisible 2 F) (hFa : F ≤ a) (hab : a ≤ b) {k : ℕ} (hk : k ≤ 2) :
    (SqueezeType.T α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), k)
      (fun c ↦ extSq (α := α) (lab a b F) c) :=
  (isLawfulBelow_Sq_iff (not_univ_three_le_sq (by omega))).mpr
    ((isLawfulBelow_iff (x := fun d ↦ extSq (α := α) (lab a b F) (Fin.castSucc d))).mpr
      ⟨a, b, F, ha, hb, hF, hFa, hab, fun d _ ↦ extSq_castSucc _ d⟩)

/-- The face of the squeeze type on `{0, 1}` is a face. -/
theorem mem_faces_Sq :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (SqueezeType.T α).toCellScheme.faces := by
  change univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The face of the squeeze type on `{0, 1}`. -/
noncomputable def faceSq (α : Ordinal.{u}) : StageType.{u} α 2 :=
  (SqueezeType.T α).comap Fin.castSuccEmb mem_faces_Sq

theorem restrictFace_Sq : restrictFace Fin.castSuccEmb (SqueezeType.T α) = some (faceSq α) :=
  restrictFace_of_mem _ _ mem_faces_Sq

/-! ### The refutation -/

private theorem lab_eq_of_root : ∀ d : Fin 9, (2 : Fin 3) ∉ cellScope d → cellGrade d ≤ 1 →
    cls d = 0 ∨ cls d = 2 := by decide

private theorem cls_of_grade_one : ∀ d : Fin 9, cellGrade d ≤ 1 → cls d ≠ 3 := by decide

private theorem cls_of_grade_two : ∀ d : Fin 9, ¬ cellGrade d ≤ 1 → cls d = 0 ∨ cls d = 3 := by
  decide

/-- **The raised extension above the grade `1` fails for the squeeze type** with its face on
`{0, 1}`. -/
theorem not_extAboveRaised_squeeze :
    ¬ ExtAboveRaised (SqueezeType.T α) restrictFace_Sq 1 := by
  intro hext
  set h : Label.{u} := ((2 : ℕ) : Label.{u}) with hhdef
  set v : Label.{u} := ((3 : ℕ) : Label.{u}) with hvdef
  have hh1 : IsSelfVisible 1 h := (isSelfVisible_natCast 2).mpr (by omega)
  have hh2 : IsSelfVisible 2 h := (isSelfVisible_natCast 2).mpr le_rfl
  have hv1 : IsSelfVisible 1 v := (isSelfVisible_natCast 3).mpr (by omega)
  have hv2 : IsSelfVisible 2 v := (isSelfVisible_natCast 3).mpr (by omega)
  have hhv : h < v := natCast_label_lt.mpr (by omega)
  let w : Fin (SqueezeType.T α).card → Label.{u} := extSq (lab h v ⊥)
  let R : Fin (SqueezeType.T α).card → Label.{u} := extSq (lab v v v)
  let y : Fin (faceSq α).card → Label.{u} := fun i ↦ R (faceCell restrictFace_Sq i)
  have hwv (d : Fin 9) : w (Fin.castSucc d) = lab h v ⊥ d := extSq_castSucc _ d
  have hRv (d : Fin 9) : R (Fin.castSucc d) = lab v v v d := extSq_castSucc _ d
  -- the grade-`1` face
  have hwL : LawfulAt (SqueezeType.T α) 1 w := by
    refine ⟨isLawfulBelow_extSq hh1 hv1 (isSelfVisible_bot 2) bot_le hhv.le (by omega),
      fun c hc ↦ ?_⟩
    rcases cases_Sq c with rfl | ⟨d, rfl⟩
    · exact extSq_last _
    · refine (hwv d).trans ?_
      have hc' : ¬ cellGrade d ≤ 1 := fun e ↦ hc ((grade_Sq_castSucc (α := α) d).trans_le e)
      rcases cls_of_grade_two d hc' with e | e
      · exact lab_dead e
      · exact lab_F e
  have hRl := isLawfulBelow_extSq (α := α) hv1 hv1 hv2 le_rfl le_rfl (k := 2) le_rfl
  have hyl : (faceSq α).rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) (fun i ↦ y i) :=
    isLawfulBelow_face restrictFace_Sq hRl
  -- the cells of the face
  have hface (i : Fin (faceSq α).card) : ∃ d : Fin 9,
      faceCell restrictFace_Sq i = Fin.castSucc d ∧ (2 : Fin 3) ∉ cellScope d := by
    have hl := last_notMem_scope_faceCell restrictFace_Sq i
    rcases cases_Sq (faceCell restrictFace_Sq i) with e | ⟨d, e⟩
    · rw [e] at hl
      exact absurd ((scope_Sq_last (α := α)).symm ▸ mem_univ _) hl
    · refine ⟨d, e, ?_⟩
      rw [e] at hl
      exact fun h2 ↦ hl ((scope_Sq_castSucc (α := α) d).symm ▸ h2)
  have hgrade (i : Fin (faceSq α).card) (d : Fin 9) (e : faceCell restrictFace_Sq i =
      Fin.castSucc d) : (faceSq α).toCellScheme.grade i = cellGrade d := by
    rw [← grade_faceCell restrictFace_Sq i, e]
    exact grade_Sq_castSucc d
  have hwy (i : Fin (faceSq α).card) (hi : (faceSq α).toCellScheme.grade i ≤ 1) :
      w (faceCell restrictFace_Sq i) = y i := by
    obtain ⟨d, e, hd⟩ := hface i
    change w (faceCell restrictFace_Sq i) = R (faceCell restrictFace_Sq i)
    rw [e, hwv, hRv]
    rcases lab_eq_of_root d hd ((hgrade i d e).symm.trans_le hi) with c | c
    · rw [lab_dead c, lab_dead c]
    · rw [lab_B c, lab_B c]
  have hwR (c : Fin (SqueezeType.T α).card) (hc : (SqueezeType.T α).toCellScheme.grade c ≤ 1) :
      min (w c) h = min (R c) h := by
    rcases cases_Sq c with rfl | ⟨d, rfl⟩
    · exact absurd ((grade_Sq_last (α := α)).symm.trans_le hc) (by omega)
    · rw [hwv, hRv]
      have hc' : cellGrade d ≤ 1 := (grade_Sq_castSucc (α := α) d).symm.trans_le hc
      rcases cls_cases d with e | e | e | e
      · rw [lab_dead e, lab_dead e]
      · rw [lab_A e, lab_A e, min_self, min_eq_right hhv.le]
      · rw [lab_B e, lab_B e]
      · exact absurd e (cls_of_grade_one d hc')
  have hyR (i : Fin (faceSq α).card) (_ : (faceSq α).toCellScheme.grade i ≤ 2) :
      min (y i) h = min (R (faceCell restrictFace_Sq i)) h := rfl
  obtain ⟨W, hW, hWK, hWr, -⟩ :=
    hext (j := 2) (by omega) (by omega) hh2 hwL hRl hyl hwy hwR hyR
  -- every extension is `lab A B F` with `F ≤ A ≤ B`
  have hW' := (isLawfulBelow_Sq_iff (α := α) (w := W) (not_univ_three_le_sq (by omega))).mp hW
  obtain ⟨A, B, F, -, -, -, hFA, hAB, hlab⟩ :=
    (isLawfulBelow_iff (x := fun e ↦ W (Fin.castSucc e))).mp hW'
  have hall (d : Fin 9) : d ∈ cells.below ((univ : Finset (Fin 3)), 2) :=
    ⟨subset_univ _, (by decide : ∀ d : Fin 9, cellGrade d ≤ 2) d⟩
  -- the root fixes `B` and `F`
  have hroot (d : Fin 9) (hd : (2 : Fin 3) ∉ cellScope d) : W (Fin.castSucc d) = lab v v v d := by
    obtain ⟨i, hi⟩ := exists_faceCell_eq_of_last_notMem restrictFace_Sq
      (s := Fin.castSucc d) fun h2 ↦ hd ((scope_Sq_castSucc (α := α) d) ▸ h2)
    have hgi : (faceSq α).toCellScheme.grade i ≤ 2 := by
      rw [hgrade i d hi]; exact (by decide : ∀ d : Fin 9, cellGrade d ≤ 2) d
    have := hWr i hgi
    rw [hi] at this
    rw [this]
    change R (faceCell restrictFace_Sq i) = _
    rw [hi, hRv]
  have hB : B = v := by
    have e := (hlab 3 (hall 3)).symm.trans (hroot 3 (by decide))
    rwa [lab_B (by decide), lab_B (by decide)] at e
  have hF : F = v := by
    have e := (hlab 6 (hall 6)).symm.trans (hroot 6 (by decide))
    rwa [lab_F (by decide), lab_F (by decide)] at e
  have hA : A = v := le_antisymm (hAB.trans hB.le) (hF ▸ hFA)
  -- the raise rule at the cell `2`
  have hW2 : W (Fin.castSucc 2) = v := by
    rw [hlab 2 (hall 2), lab_A (by decide), hA]
  rcases hWK (Fin.castSucc 2) ((grade_Sq_castSucc (α := α) 2).trans_le (by decide)) with e | ⟨-, e⟩
  · rw [hW2, hwv, lab_A (by decide)] at e
    exact hhv.ne' e
  · rw [hW2] at e
    exact (natCast_label_lt_omega 3).ne_top e

/-! ### The clause at the squeeze -/

/-- **The frontier of a grade-`K` face of a legal source-gap context is at most its value at every
top avoiding the lost point**: extend the face at the cap `⊥` to a lawful labelling
(`H2.exists_ext_bot_at`), unchanged at the grades at most `K`, and apply
`StageType.IsSourceGapContextAt.frontier_le`. -/
theorem frontierAt_le_of_lawfulAt {m n K : ℕ} {t' : StageType.{u} α m} (hleg : t'.IsLegal)
    {g : Fin n ↪ Fin m} {l : Fin m} {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K g l o r)
    {f : Fin t'.card → Label.{u}} (hf : LawfulAt t' K f) {a : Fin t'.card} (ha : t'.label a = ⊤)
    (hla : l ∉ t'.toCellScheme.scope a) : FieldAdmission.frontierAt o r K f ≤ f a := by
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKm : K ≤ m := hs.grade_owner ▸ t'.grade_le o
  have hgr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hga : t'.toCellScheme.grade a ≤ K := hs.topGrade_eq ▸ grade_le_topGrade ha
  obtain ⟨f', hf', hff'⟩ := exists_ext_bot_at hleg hK0 hKm hf
  have := hs.frontier_le hf' ha hla
  rw [hff' o hs.grade_owner.le, hff' r hgr, hff' a hga] at this
  exact this

/-- **The clause holds when every designated top is at least a value of the context face at a top
avoiding the lost point**, at a legal source-gap context. -/
theorem selfLow_of_le_top {m n K : ℕ} {t' : StageType.{u} α m} (hleg : t'.IsLegal)
    {g : Fin n ↪ Fin m} {l : Fin m} {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K g l o r)
    {ιD : Type*} {Lo Tops : Finset ιD} {f : Fin t'.card → Label.{u}} (hf : LawfulAt t' K f)
    {W : ιD → Label.{u}}
    (hW : ∀ x ∈ Tops, ∃ a, t'.label a = ⊤ ∧ l ∉ t'.toCellScheme.scope a ∧ f a ≤ W x) :
    SelfLowG o r K Lo Tops f W := fun x hx _ ↦ by
  obtain ⟨a, ha, hla, hle⟩ := hW x hx
  exact (frontierAt_le_of_lawfulAt hleg hs hf ha hla).trans hle

/-- **`H2.ExtAboveRaisedAt 2` is false.** -/
theorem not_extAboveRaisedAt_two : ¬ ExtAboveRaisedAt.{u} 2 := fun h ↦
  not_extAboveRaised_squeeze (α := 0)
    (h (SqueezeType.T 0) (SqueezeType.isLegal_T 0) restrictFace_Sq one_pos one_lt_two)

end VaughtConjecture.H2

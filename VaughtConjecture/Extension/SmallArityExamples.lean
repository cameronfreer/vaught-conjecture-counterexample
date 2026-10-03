/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SmallArities
import VaughtConjecture.Extension.CodingExamples

/-!
# Examples: the completion at arity zero, and the flat catalogue

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities); semantic contract, item 3.

**The seed with four cells on one point** (`fourCellSeed`): the left coatom has four cells of
graded index `({0}, 1)` with rows `ω * (j + 1) + 1`, `j < 4`; the right coatom one cell of graded
index `({1}, 1)` with row `1`.  Both are legal (`isLegal_onePointScheme`: a scheme on one point
whose row is monotone in the cell, below `ω ^ 2`, and self-visible at `1`), so their amalgam over
the empty face is a seed at every stage.

* **R1, the flat catalogue is not bountiful** (`not_isBountiful_flatRows`).  The flat layer over
  the scheme of this seed (the same cells, faces and rows, written out directly and identified
  with the amalgam by inspection) indexes its new cells by
  every lawful labelling of the old cells with values in the flattened coded alphabet
  `(codedAlphabet B 2).image (flatten 1)`, short at `1`, never the formal top, and uses agreement
  heights on the grid as rows between new cells.  It is consistent (`isConsistent_flatRows`), but
  for every block bound `B = n + 3` it does not lift capped from `({0}, 1)` to `(univ, 1)`
  (`not_cappedLift_flatRows`): with the ambient the row of the cell of the constant `ω * B + 1`,
  the cap `ω * (B - 1) + 1`, and the prescription `ω * (B + 1 + j) + 1` on the left cells, the cap
  pins the cells of the constants `ω * (B - 3) + 1` and `ω * (B - 2) + 1`, availability gives a
  new cell above `ω * (B + 4) + 1`, its locality forces four distinct entry values above
  `ω * (B - 3) + 1`, and only three blocks are left.  A catalogue containing a pattern at the top
  of its alphabet leaves no room above the cap.
* **R2, the same lift on the canonical layer** (`cappedLift_fourCellSeed`,
  `exists_lift_fourCellSeed`): the canonical field layer over the seed is bountiful by the
  completion at arity zero, so at the cap `ω * 10 + 1` every lawful prescription below `({0}, 1)`
  and every lawful ambient with the same observation there have a lift keeping the observation at
  every cell.  The canonical catalogue has no constant at a high
  block, so the ambient of R1 has no counterpart.
* **R3, relative room** (`canonicalCode_roomCanonical` and the example after it): the canonical
  labelling `(ω + 1, ω * 3 + 1, …, ω * 3 + 1)` of six cells and a labelling agreeing with it capped
  at `ω * 3 + 1` with five distinct values above it; its canonical code still agrees with the
  canonical labelling capped at `ω * 3 + 1`.
* **R4, the literal-reading decoder at a strip** (the example after
  `canonicalCode_stripLabelling`): the least code above the cut is the cut itself, and no witness
  bounded by grade `1` that fixes the start of the block of the cut reads it literally.

**Regressions at arity zero.**

1. Long rows with bottom labels: `longRowSeed`, the coatoms `pointRow 3` and `pointRow (ω + 5)` of
   `VaughtConjecture.Extension.CodingExamples`, whose row values exceed the grade plus one, has a
   completion.
2. A label `⊤`: in the completion of every seed on two points, an old cell labelled `⊤` keeps `⊤`
   and some new cell of graded index `(univ, 1)` is labelled `⊤`.
3. Labels above the grade plus one (`3` and `ω * 5 + 3`) are read literally from their canonical
   code.
4. Several cells on one point: `fourCellSeed`.  The section `(1, ω * 5 + 1)` of the two cells on
   one point of `VaughtConjecture.Extension.TransformationExamples` is not run here.
5. The caps `⊤` (the lift is exact), `⊥` (every lawful prescription extends), and `ω * 10 + 1`
   (`exists_lift_fourCellSeed`).
6. The literal coatom faces of the completions
   (`CompletionBelowFullGrade.restrictFace_left_completion`,
   `CompletionBelowFullGrade.restrictFace_right_completion`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the completion of [Kni26, Definition 4.3.14] indexes
its cells of full scope by efficient stacks, whose bindings are open, and is not the flat layer of
R1.
-/

universe u

namespace VaughtConjecture

open Finset CellScheme Label
open scoped Ordinal

namespace SmallArityExamples

/-! ### A seed with four cells on one point -/

/-- A scheme on one point with `c` cells of graded index `({0}, 1)`, each with the row `r`. -/
def onePointScheme (c : ℕ) (r : Fin c → Label.{u}) : Scheme.{u} 1 where
  card := c
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩
  rows := ⟨fun _ t ↦ r t.1⟩

/-- The only graded face of a scheme on one point is `({0}, 1)`. -/
private theorem eq_of_mem_gradedFaces {c : ℕ} {r : Fin c → Label.{u}} {X : Finset (Fin 1) × ℕ}
    (hX : X ∈ (onePointScheme c r).toCellScheme.gradedFaces) : X = (univ, 1) := by
  obtain ⟨C, j⟩ := X
  obtain ⟨_, hpos, hle⟩ := hX
  have hC : #C ≤ 1 := card_le_univ C
  simp only at hpos hle
  have hC' : C = univ := (card_eq_iff_eq_univ C).mp (by simp; omega)
  subst hC'
  simp only [card_univ, Fintype.card_fin] at hle
  ext <;> simp; omega

/-- **A scheme on one point is legal** when its row is monotone in the cell, below `ω ^ 2`, and
self-visible at `1`: every cell transforms its row to itself capped at its own entry. -/
theorem isLegal_onePointScheme {c : ℕ} (hc : 0 < c) {r : Fin c → Label.{u}} (hr : Monotone r)
    (hcoded : ∀ i, r i < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) (hvis : ∀ i, IsSelfVisible 1 (r i)) :
    (onePointScheme c r).IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [onePointScheme, CellScheme.gradedIndex]⟩⟩
  isCoded _ t := hcoded t.1
  isConsistent s := by
    refine (Rows.isLawfulBelow_iff_forall (w := r)).mpr ⟨fun d _ ↦ hvis d, fun s' _ ↦ ?_,
      fun s' t _ _ _ ↦ ⟨⟨c - 1, by omega⟩, rfl, hr (Fin.mk_le_mk.mpr (by omega))⟩⟩
    exact (TransformsTo.refl _ _).min_const (K := 1) (fun _ ↦ le_rfl) (hvis s')
  isBountiful X Y hX hY h := by
    obtain rfl := eq_of_mem_gradedFaces hX
    obtain rfl := eq_of_mem_gradedFaces hY
    exact Rows.cappedLift_refl _
  isComplete X hX := ⟨⟨0, hc⟩, by rw [eq_of_mem_gradedFaces hX]; rfl⟩

/-- The point `ω * b + 1`. -/
noncomputable abbrev P (b : ℕ) : Label.{u} := gridPoint 1 b

/-- The four cells of the left coatom: rows `ω * (j + 1) + 1`. -/
noncomputable def leftScheme : Scheme.{u} 1 := onePointScheme 4 fun j ↦ P (j.val + 1)

/-- The one cell of the right coatom: row `1`. -/
def rightScheme : Scheme.{u} 1 := onePointScheme 1 fun _ ↦ 1

/-- The left coatom is legal. -/
theorem isLegal_left : leftScheme.{u}.IsLegal :=
  isLegal_onePointScheme (by decide) (fun a b h ↦ gridPoint_le_gridPoint.mpr (by
    have : a.val ≤ b.val := h
    omega)) (fun _ ↦ gridPoint_lt_omega0_sq _ _) (fun _ ↦ isSelfVisible_gridPoint _ _)

/-- The right coatom is legal. -/
theorem isLegal_right : rightScheme.{u}.IsLegal :=
  isLegal_onePointScheme (by decide) (fun _ _ _ ↦ le_rfl)
    (fun _ ↦ lt_omega0_sq_iff.mpr (.inr ⟨0, 1, by simp⟩)) (fun _ ↦ by simp)

/-- **The seed with four cells on one point**, at every stage `α`: the amalgam over the empty
face of the left coatom (four cells of graded index `({0}, 1)`, rows `ω * (j + 1) + 1`) and the
right coatom (one cell, row `1`), with bottom labels. -/
noncomputable def fourCellSeed (α : Ordinal.{u}) : Seed.{u} α 0 :=
  let ta := isLegal_left.toStageType α
  let tb := isLegal_right.toStageType α
  have hpa := Option.isSome_iff_exists.mp (ta.isSome_restrictFace_of_zero (Coatom.face 0))
  have hpb := Option.isSome_iff_exists.mp (tb.isSome_restrictFace_of_zero (Coatom.face 0))
  Seed.ofCoatoms (isLegal_left.isLegal_toStageType α) (isLegal_right.isLegal_toStageType α)
    hpa.choose_spec (hpb.choose_spec.trans (congrArg some (StageType.eq_of_zero _ _)))

/-! ### R1: the flat catalogue is not bountiful -/

section FlatCatalogue

/-! The flat layer, over the scheme of the seed with four cells on one point (cells `0, 1, 2, 3`
of graded index `({0}, 1)` with rows `ω * (j + 1) + 1`, cell `4` of graded index `({1}, 1)` with
row `1`), indexes its new cells by every lawful labelling with values in the flattened coded
alphabet `(codedAlphabet B 2).image (flatten 1)`, short at `1` and never the formal top, with the
agreement heights on the grid `{⊥} ∪ {ω * b + 1 : b ≤ B + 1}` as rows between new cells.  The
block bound is `B = n + 3`. -/

private theorem P_inj {a b : ℕ} (h : P.{0} a = P b) : a = b :=
  le_antisymm (gridPoint_le_gridPoint.mp h.le) (gridPoint_le_gridPoint.mp h.ge)

/-- The flattened coded alphabet with block bound `B = n + 3`. -/
noncomputable def alphabet (n : ℕ) : Finset Label.{0} := (codedAlphabet (n + 3) 2).image (flatten 1)

private theorem P_mem_alphabet {n b : ℕ} (hb : b ≤ n + 3) : P b ∈ alphabet n :=
  mem_image.mpr ⟨P b, mem_codedAlphabet.mpr (.inr ⟨b, hb, 1, by omega, rfl⟩),
    (isShort_gridPoint 1 b).flatten_eq⟩

/-- A self-visible member of the flattened alphabet is `⊥` or a point `ω * b + 1`, `b ≤ B`. -/
private theorem alphabet_cases {n : ℕ} {x : Label.{0}} (hx : x ∈ alphabet n)
    (hv : IsSelfVisible 1 x) :
    x = ⊥ ∨ ∃ b ≤ n + 3, x = P b := by
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  rcases mem_codedAlphabet.mp hy with rfl | ⟨a, ha, m, hm, rfl⟩
  · exact .inl rfl
  · refine .inr ⟨a, ha, ?_⟩
    have hmin : min ((m : ℕ) : Ordinal.{0}) ((1 : ℕ) : Ordinal.{0}) =
        ((min m 1 : ℕ) : Ordinal.{0}) := by
      rcases le_total m 1 with h | h
      · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
      · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
    have hf : flatten 1 (((ω * (a : Ordinal.{0}) + (m : Ordinal.{0}) : Ordinal.{0})) : Label.{0}) =
        (((ω * (a : Ordinal.{0}) + ((min m 1 : ℕ) : Ordinal.{0}) : Ordinal.{0})) : Label.{0}) := by
      rw [flatten_coe, flattenOrd, omega0_mul_add_natCast_div, omega0_mul_add_natCast_mod, hmin]
    rw [hf] at hv ⊢
    have h1 := isSelfVisible_coe.mp hv
    rw [omega0_mul_add_natCast_mod] at h1
    have h1' : 1 ≤ min m 1 := by exact_mod_cast h1
    have : min m 1 = 1 := le_antisymm (min_le_right _ _) h1'
    rw [this]
    rfl

/-- The scopes of the old cells: `{0}` for cells `0, 1, 2, 3`, `{1}` for cell `4`. -/
def oldScope (i : Fin 5) : Finset (Fin 2) := if i = 4 then {1} else {0}

private theorem oldScope_subset_iff (i j : Fin 5) : oldScope j ⊆ oldScope i ↔ (j = 4 ↔ i = 4) := by
  revert i j; decide

private theorem not_univ_subset_oldScope (i : Fin 5) :
    ¬ ((univ : Finset (Fin 2)) ⊆ oldScope i) := by
  revert i; decide

private theorem oldScope_subset_zero_iff (i : Fin 5) : oldScope i ⊆ {0} ↔ i ≠ 4 := by
  revert i; decide

private theorem oldScope_of_ne {i : Fin 5} (hi : i ≠ 4) : oldScope i = {0} := by
  simp [oldScope, hi]

/-- The old scheme: the cells, faces and rows of the amalgam of the two coatoms of
`fourCellSeed`, written out directly (the identification is by inspection, not compiled). -/
def oldCells : CellScheme (Fin 5) (Fin 2) := ⟨univ, {∅, {0}, {1}, univ}, oldScope, fun _ ↦ 1⟩

/-- The old rows: `ω * (j + 1) + 1` on the left coatom and `1` on the right. -/
noncomputable def oldRowFn (i j : Fin 5) : Label.{0} := if i = 4 then 1 else P (j.val + 1)

/-- The old rows as semantic rows. -/
noncomputable def oldRows : oldCells.Rows.{0} := ⟨fun s t ↦ oldRowFn s t.1⟩

private theorem oldRowFn_ne_bot (i j : Fin 5) : oldRowFn i j ≠ ⊥ := by
  unfold oldRowFn; split_ifs
  · exact WithBot.coe_ne_bot
  · exact gridPoint_ne_bot _ _

private theorem isSelfVisible_oldRowFn (i j : Fin 5) : IsSelfVisible 1 (oldRowFn i j) := by
  unfold oldRowFn; split_ifs
  · simp
  · exact isSelfVisible_gridPoint _ _

open Classical in
/-- The shifter sending every label other than `⊥` to `v`. -/
noncomputable def constShifter (v x : Label.{0}) : Label.{0} := if x = ⊥ then ⊥ else v

private theorem isWitness_constShifter {v : Label.{0}} (hv : IsSelfVisible 1 v) :
    IsWitness (stepSuppressor.{0} 1) (constShifter v) where
  antitone := (IsWitness.id_step 1).antitone
  isSelfVisible := (IsWitness.id_step 1).isSelfVisible
  map_bot := ite_eq_left rfl
  monotone x y h := by
    by_cases hx : x = ⊥
    · simp [constShifter, hx]
    · have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ h))
      simp [constShifter, hx, hy]
  visibilityReplace_comm x k hx i hi := by
    by_cases hx0 : x = ⊥
    · subst hx0
      simp [constShifter]
    · have h1 : visibilityReplace k i x ≠ ⊥ := by simpa using hx0
      unfold constShifter at hx ⊢
      rw [ite_eq_right h1, ite_eq_right hx0]
      rw [ite_eq_right hx0] at hx
      rcases le_or_gt k 1 with hk | hk
      · exact ((hv.mono hk).visibilityReplace_eq i).symm
      · rw [stepSuppressor_of_lt hk, le_bot_iff] at hx
        subst hx
        simp

private theorem transformsTo_const {D' : Type*} {grade : D' → ℕ} (hg : ∀ d, grade d ≤ 1)
    {E : D' → Label.{0}} (hE : ∀ d, E d ≠ ⊥) {v : Label.{0}} (hv : IsSelfVisible 1 v) :
    TransformsTo grade E (fun _ ↦ v) :=
  ⟨stepSuppressor 1, constShifter v, isWitness_constShifter hv, fun d ↦ by
    rw [stepSuppressor_of_le (hg d), min_top_right, constShifter, ite_eq_right (hE d)]⟩

/-- The flat catalogue: the lawful labellings of the old cells with values in the flattened
coded alphabet, short at `1`, never the formal top. -/
def IsFlatEntry (n : ℕ) (a : Fin 5 → Label.{0}) : Prop :=
  oldRows.IsLawful a ∧ (∀ i, a i ∈ alphabet n) ∧ (∀ i, IsShort 1 (a i)) ∧ ∀ i, a i ≠ ⊤

/-- The entries of the flat catalogue. -/
def FlatEntry (n : ℕ) := {a : Fin 5 → Label.{0} // IsFlatEntry n a}

private theorem isFlatEntry_const {n b : ℕ} (hb : b ≤ n + 3) : IsFlatEntry n (fun _ ↦ P b) :=
  ⟨⟨fun _ ↦ isSelfVisible_gridPoint 1 b, fun s ↦ by
      have h := transformsTo_const (grade := fun d : oldCells.below (oldCells.gradedIndex s) ↦
        oldCells.grade d) (fun _ ↦ le_rfl) (E := oldRows.row s)
        (fun t ↦ oldRowFn_ne_bot s t.1) (isSelfVisible_gridPoint 1 b)
      simpa only [min_self] using h,
      fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩⟩,
    fun _ ↦ P_mem_alphabet hb, fun _ ↦ isShort_gridPoint 1 b, fun _ ↦ gridPoint_ne_top 1 b⟩

private theorem FlatEntry.val_cases {n : ℕ} (a : FlatEntry n) (i : Fin 5) :
    a.1 i = ⊥ ∨ ∃ b ≤ n + 3, a.1 i = P b :=
  alphabet_cases (a.2.2.1 i) (a.2.1.orderly i)

/-- The agreement height on the grid with block bound `B + 1 = n + 4`. -/
noncomputable abbrev cut (n : ℕ) (a b : Fin 5 → Label.{0}) : Label.{0} :=
  agreementHeight (grid 1 (n + 4)) a b

private theorem cut_le (n : ℕ) (a b : Fin 5 → Label.{0}) : cut n a b ≤ P (n + 4) :=
  agreementHeight_le fun _ hx ↦ le_gridPoint_of_mem_grid hx

private theorem cut_self (n : ℕ) (a : Fin 5 → Label.{0}) : cut n a a = P (n + 4) :=
  agreementHeight_self (gridPoint_mem_grid le_rfl)
    (fun _ hx ↦ le_gridPoint_of_mem_grid hx) a

private theorem isSelfVisible_cut (n : ℕ) (a b : Fin 5 → Label.{0}) : IsSelfVisible 1 (cut n a b) :=
  isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) a b).1

/-- The agreement height of two constant labellings. -/
private theorem cut_const_const {n t b : ℕ} (hbt : b < t) (hbn : b ≤ n + 4) :
    cut n (fun _ ↦ P t) (fun _ ↦ P b) = P b := by
  apply le_antisymm
  · obtain ⟨-, hag⟩ := agreementHeight_spec (bot_mem_grid 1 (n + 4))
      (fun _ : Fin 5 ↦ P.{0} t) (fun _ ↦ P b)
    have h := hag 0
    by_contra hlt
    rw [not_le] at hlt
    rw [min_eq_left hlt.le] at h
    exact (lt_min (gridPoint_lt_gridPoint.mpr hbt) hlt).ne' h
  · exact le_agreementHeight (gridPoint_mem_grid hbn) fun _ ↦ by
      rw [min_eq_right (gridPoint_le_gridPoint.mpr hbt.le), min_self]

/-- **The tie.**  If some value of `a` is at most `ω * m + 1` and `a` is not constant, then `a`
has the same agreement height with the constants `ω * m + 1` and `ω * (m + 1) + 1`. -/
private theorem cut_const_eq {N m : ℕ} (a : Fin 5 → Label.{0}) (hlow : ∃ i, a i ≤ P m)
    (hnc : a 0 ≠ a 1) : cut N a (fun _ ↦ P m) = cut N a (fun _ ↦ P (m + 1)) := by
  obtain ⟨i₀, -, hmin⟩ := exists_min_image (univ : Finset (Fin 5)) a univ_nonempty
  replace hmin : ∀ i, a i₀ ≤ a i := fun i ↦ hmin i (mem_univ i)
  have hlow' : a i₀ ≤ P m := by
    obtain ⟨i, hi⟩ := hlow
    exact (hmin i).trans hi
  have key : ∀ v : Label.{0}, a i₀ ≤ v → (a i₀ < v ∨ a 0 ≠ a 1) → ∀ x,
      ((∀ i, min (a i) x = min ((fun _ ↦ v) i) x) ↔ x ≤ a i₀) := by
    intro v hv hcase x
    constructor
    · intro h
      by_contra hx
      rw [not_le] at hx
      have h0 := h i₀
      rw [min_eq_left hx.le] at h0
      by_cases hvlt : a i₀ < v
      · exact (lt_min hvlt hx).ne h0
      · have hveq : a i₀ = v := le_antisymm hv (not_lt.mp hvlt)
        have hall : ∀ i, a i = a i₀ := fun i ↦ by
          have hi := h i
          rw [← h0] at hi
          by_cases hix : x ≤ a i
          · rw [min_eq_right hix] at hi
            exact absurd hi hx.ne'
          · rw [min_eq_left (not_le.mp hix).le] at hi
            exact hi
        rcases hcase with hlt | hnc'
        · exact hvlt hlt
        · exact hnc' ((hall 0).trans (hall 1).symm)
    · intro hx i
      dsimp only
      rw [min_eq_right (hx.trans (hmin i)), min_eq_right (hx.trans hv)]
  have hG := bot_mem_grid.{0} 1 (N + 4)
  have hP0 : a i₀ ≤ P (m + 1) := hlow'.trans (gridPoint_le_gridPoint.mpr (by omega))
  have hP1 : a i₀ < P (m + 1) := hlow'.trans_lt (gridPoint_lt_gridPoint.mpr (by omega))
  apply le_antisymm
  · obtain ⟨hmem, hag⟩ := agreementHeight_spec hG a (fun _ ↦ P m)
    exact le_agreementHeight hmem ((key (P (m + 1)) hP0 (.inl hP1) _).mpr
      ((key (P m) hlow' (.inr hnc) _).mp hag))
  · obtain ⟨hmem, hag⟩ := agreementHeight_spec hG a (fun _ ↦ P (m + 1))
    exact le_agreementHeight hmem ((key (P m) hlow' (.inr hnc) _).mpr
      ((key (P (m + 1)) hP0 (.inl hP1) _).mp hag))

/-- The cells of the flat layer: the old cells and one new cell per entry of the flat
catalogue. -/
abbrev FlatCell (n : ℕ) := Fin 5 ⊕ FlatEntry n

/-- The scopes of the flat layer. -/
def flatScope {n : ℕ} : FlatCell n → Finset (Fin 2)
  | .inl i => oldScope i
  | .inr _ => univ

/-- The cell scheme of the flat layer. -/
def flatCells (n : ℕ) : CellScheme (FlatCell n) (Fin 2) :=
  ⟨univ, {∅, {0}, {1}, univ}, flatScope, fun _ ↦ 1⟩

/-- The rows of the flat layer: old rows on old cells; on a new cell, its catalogue labelling on
the old cells and the agreement height on the new cells, the ceiling of the grid on itself. -/
noncomputable def flatRowFn {n : ℕ} : FlatCell n → FlatCell n → Label.{0}
  | .inl i, .inl j => oldRowFn i j
  | .inl _, .inr _ => ⊥
  | .inr a, .inl j => a.1 j
  | .inr a, .inr b => cut n a.1 b.1

/-- The rows of the flat layer, as semantic rows. -/
noncomputable def flatRows (n : ℕ) : (flatCells n).Rows.{0} := ⟨fun s t ↦ flatRowFn s t.1⟩

private theorem mem_below_univ {n : ℕ} (y : FlatCell n) :
    y ∈ (flatCells n).below ((univ : Finset (Fin 2)), 1) :=
  ⟨subset_univ _, le_rfl⟩

private theorem below_old {n : ℕ} (i : Fin 5)
    (d : (flatCells n).below ((flatCells n).gradedIndex (.inl i))) :
    ∃ j, d.1 = .inl j ∧ oldScope j ⊆ oldScope i := by
  rcases d with ⟨d | b, hd⟩
  · exact ⟨d, rfl, hd.1⟩
  · exact absurd hd.1 (not_univ_subset_oldScope i)

private theorem FlatEntry.val_le {n : ℕ} (a : FlatEntry n) (i : Fin 5) : a.1 i ≤ P (n + 4) := by
  rcases a.val_cases i with h | ⟨b, hb, h⟩ <;> rw [h]
  · exact bot_le
  · exact gridPoint_le_gridPoint.mpr (by omega)

private theorem flatRowFn_inr_le {n : ℕ} (a : FlatEntry n) (y : FlatCell n) :
    flatRowFn (.inr a) y ≤ P (n + 4) := by
  rcases y with j | b
  · exact a.val_le j
  · exact cut_le n a.1 b.1

/-- **The row of every new cell is a lawful section of the flat layer**: the consistency at the
new cells, and the ambient of the failing lift. -/
theorem isLawful_flatRowFn {n : ℕ} (a : FlatEntry n) :
    (flatRows n).IsLawful (fun y ↦ flatRowFn (.inr a) y) where
  orderly d := by
    rcases d with j | b
    · exact a.2.1.orderly j
    · exact isSelfVisible_cut n a.1 b.1
  locality s := by
    rcases s with i | b
    · obtain ⟨g, σ, hw, heq⟩ := a.2.1.locality i
      refine ⟨g, σ, hw, fun d ↦ ?_⟩
      obtain ⟨j, hj, hji⟩ := below_old i d
      have h := heq ⟨j, ⟨hji, le_rfl⟩⟩
      change min (flatRowFn (.inr a) d.1) (a.1 i) = min (σ (flatRowFn (.inl i) d.1)) (g 1)
      rw [hj]
      exact h
    · have h := (TransformsTo.refl (fun d : (flatCells n).below ((flatCells n).gradedIndex (.inr b))
        ↦ (flatCells n).grade d) ((flatRows n).row (.inr b))).min_const (K := 1) (fun _ ↦ le_rfl)
        (isSelfVisible_cut n a.1 b.1)
      convert h using 1
      funext d
      rcases d with ⟨j | c, hd⟩
      · exact (agreementHeight_spec (bot_mem_grid _ _) a.1 b.1).2 j
      · exact agreementHeight_tri (bot_mem_grid _ _) a.1 b.1 c.1
  availability s t hst hg := by
    rcases t with j | b
    · rcases s with i | c
      · obtain ⟨u', hu', hle⟩ := a.2.1.availability i j hst rfl
        exact ⟨.inl u', hu', hle⟩
      · exact absurd hst (not_univ_subset_oldScope j)
    · refine ⟨.inr a, rfl, ?_⟩
      change flatRowFn (.inr a) s ≤ cut n a.1 a.1
      rw [cut_self]
      exact flatRowFn_inr_le a s

/-- **The flat layer is consistent.** -/
theorem isConsistent_flatRows (n : ℕ) : (flatRows n).IsConsistent := by
  intro s
  rcases s with i | a
  · change (flatRows n).IsLawfulBelow _
      (fun d : (flatCells n).below ((flatCells n).gradedIndex (.inl i)) ↦ flatRowFn (.inl i) d.1)
    refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d _ ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · rcases d with j | b
      · exact isSelfVisible_oldRowFn i j
      · exact isSelfVisible_bot 1
    · rcases s with k | b
      · have hk : oldScope k ⊆ oldScope i := hs.1
        have h := (TransformsTo.refl (fun d : (flatCells n).below ((flatCells n).gradedIndex
          (.inl k)) ↦ (flatCells n).grade d) ((flatRows n).row (.inl k))).min_const (K := 1)
          (fun _ ↦ le_rfl) (isSelfVisible_oldRowFn i k)
        convert h using 1
        funext d
        obtain ⟨l, hl, hlk⟩ := below_old k d
        simp only [flatRows, hl, flatRowFn, oldRowFn]
        have e1 := (oldScope_subset_iff i k).mp hk
        by_cases hi : i = 4
        · have hk4 : k = 4 := e1.mpr hi
          simp only [hi, hk4, ite_true]
        · have hk4 : k ≠ 4 := fun h ↦ hi (e1.mp h)
          simp only [hi, hk4, ite_false]
      · exact absurd hs.1 (not_univ_subset_oldScope i)
    · rcases t with l | b
      · rcases s with k | c
        · by_cases hl : l = 4
          · subst hl
            have hk : k = 4 := ((oldScope_subset_iff 4 k).mp hst).mpr rfl
            subst hk
            exact ⟨.inl 4, rfl, le_rfl⟩
          · have hk : k ≠ 4 := fun h ↦ hl (((oldScope_subset_iff l k).mp hst).mp h)
            refine ⟨.inl 3, ?_, ?_⟩
            · change ((oldScope 3, 1) : Finset (Fin 2) × ℕ) = (oldScope l, 1)
              rw [oldScope_of_ne (by decide), oldScope_of_ne hl]
            · change oldRowFn i k ≤ oldRowFn i 3
              unfold oldRowFn
              split_ifs
              · exact le_rfl
              · exact gridPoint_le_gridPoint.mpr (by
                  have := k.isLt
                  have : k.val ≠ 4 := fun h ↦ hk (Fin.ext h)
                  omega)
        · exact absurd hst (not_univ_subset_oldScope l)
      · exact absurd ht.1 (not_univ_subset_oldScope i)
  · exact (isLawful_flatRowFn a).isLawfulBelow _

/-- The ambient's catalogue entry: the constant `ω * B + 1`. -/
noncomputable def topEntry (n : ℕ) : FlatEntry n := ⟨fun _ ↦ P (n + 3), isFlatEntry_const le_rfl⟩

/-- The lower of the two catalogue entries pinned by the cap: the constant `ω * (B - 3) + 1`. -/
noncomputable def lowEntry₀ (n : ℕ) : FlatEntry n := ⟨fun _ ↦ P n, isFlatEntry_const (by omega)⟩

/-- The upper of the two catalogue entries pinned by the cap: the constant `ω * (B - 2) + 1`. -/
noncomputable def lowEntry₁ (n : ℕ) : FlatEntry n :=
  ⟨fun _ ↦ P (n + 1), isFlatEntry_const (by omega)⟩

/-- The prescription on the four left cells: `ω * (B + 1 + j) + 1`, and bottom elsewhere. -/
noncomputable def prescription {n : ℕ} : FlatCell n → Label.{0}
  | .inl j => P (j.val + n + 4)
  | .inr _ => ⊥

/-- The translation by `ω * m` is a witness with the constant suppressor `⊤`. -/
private theorem isWitness_translate (m : ℕ) :
    IsWitness (fun _ ↦ (⊤ : Label.{0})) (translate (ω * (m : Ordinal.{0})) 0) where
  antitone := antitone_const
  isSelfVisible _ := isSelfVisible_top _
  map_bot := translate_bot _ _
  monotone := monotone_translate _ _
  visibilityReplace_comm x k _ i _ := by
    induction x using recBotCoeTop with
    | bot => simp
    | coe o =>
      exact translate_visibilityReplace (Ordinal.isSuccPrelimit_mul_left Ordinal.isSuccLimit_omega0)
        Ordinal.isSuccPrelimit_zero
        (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (zero_le : (0 : Ordinal.{0}) ≤ o))) k i
    | top =>
      exact translate_visibilityReplace (Ordinal.isSuccPrelimit_mul_left Ordinal.isSuccLimit_omega0)
        Ordinal.isSuccPrelimit_zero le_top k i

private theorem translate_P (m b : ℕ) : translate (ω * (m : Ordinal.{0})) 0 (P b) = P (m + b) := by
  simp only [P, gridPoint, translate_coe, Ordinal.sub_zero]
  congr 2
  rw [← add_assoc, ← mul_add, Nat.cast_add]

/-- The pair `({0}, 1)` lies below `(univ, 1)`. -/
theorem lift_le : ((({0} : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ (univ, 1) :=
  ⟨subset_univ _, le_rfl⟩

/-- The prescription is lawful below `({0}, 1)`: translation by `ω * (B + 3)`, then the cap. -/
private theorem isLawfulBelow_prescription (n : ℕ) :
    (flatRows n).IsLawfulBelow (({0} : Finset (Fin 2)), 1)
      (fun d : (flatCells n).below (({0} : Finset (Fin 2)), 1) ↦ prescription d.1) := by
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d _ ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · rcases d with j | b
    · exact isSelfVisible_gridPoint _ _
    · exact isSelfVisible_bot 1
  · rcases s with i | b
    · have hi : i ≠ 4 := (oldScope_subset_zero_iff i).mp hs.1
      have h1 : TransformsTo (fun d : (flatCells n).below ((flatCells n).gradedIndex (.inl i)) ↦
          (flatCells n).grade d) ((flatRows n).row (.inl i))
          (fun d ↦ translate (ω * ((n + 3 : ℕ) : Ordinal.{0})) 0 ((flatRows n).row (.inl i) d)) :=
        ⟨fun _ ↦ ⊤, _, isWitness_translate (n + 3), fun _ ↦ (min_top_right _).symm⟩
      have h2 := h1.min_const (K := 1) (fun _ ↦ le_rfl) (isSelfVisible_gridPoint 1 (i.val + n + 4))
      convert h2 using 1
      funext d
      obtain ⟨j, hj, hji⟩ := below_old i d
      have hj4 : j ≠ 4 := fun h ↦ hi (((oldScope_subset_iff i j).mp hji).mp h)
      simp only [flatRows, hj, flatRowFn, oldRowFn, ite_eq_right hi, translate_P, prescription]
      congr 2
      omega
    · exact absurd hs.1 (show ¬ ((univ : Finset (Fin 2)) ⊆ {0}) by decide)
  · rcases t with l | b
    · have hl : l ≠ 4 := (oldScope_subset_zero_iff l).mp ht.1
      rcases s with i | c
      · have hi : i ≠ 4 := fun h ↦ hl (((oldScope_subset_iff l i).mp hst).mp h)
        refine ⟨.inl 3, ?_, ?_⟩
        · change ((oldScope 3, 1) : Finset (Fin 2) × ℕ) = (oldScope l, 1)
          rw [oldScope_of_ne (by decide), oldScope_of_ne hl]
        · change P (i.val + n + 4) ≤ P ((3 : Fin 5).val + n + 4)
          refine gridPoint_le_gridPoint.mpr ?_
          have : i.val ≠ 4 := fun h ↦ hi (Fin.ext h)
          have := i.isLt
          have h3 : ((3 : Fin 5) : ℕ) = 3 := rfl
          rw [h3]
          omega
      · exact absurd hst (not_univ_subset_oldScope l)
    · exact absurd ht.1 (show ¬ ((univ : Finset (Fin 2)) ⊆ {0}) by decide)

/-- **R1: the flat layer does not lift capped from `({0}, 1)` to `(univ, 1)`**, for every block
bound `B = n + 3`.  The ambient is the row of the catalogue cell of the constant `ω * B + 1`, the
cap `ω * (B - 1) + 1`, the prescription `ω * (B + 1 + j) + 1` on the four left cells.  The cap
pins the cells of the constants `ω * (B - 3) + 1` and `ω * (B - 2) + 1`; availability at the
fourth left cell gives a new cell `z` above `ω * (B + 4) + 1`; locality at `z` makes its entry
injective on the left cells and separates the two pinned cells, which forces every value of the
entry above `ω * (B - 3) + 1` (the tie); and four distinct values do not fit in the three blocks
left. -/
theorem not_cappedLift_flatRows (n : ℕ) : ¬ (flatRows n).CappedLift lift_le := by
  intro hl
  rw [Rows.cappedLift_iff_forall_exists] at hl
  set Y : Finset (Fin 2) × ℕ := (univ, 1)
  set qAll : FlatCell n → Label.{0} := fun y ↦ flatRowFn (.inr (topEntry n)) y with hqAll
  have hq : (flatRows n).IsLawfulBelow Y (fun d : (flatCells n).below Y ↦ qAll d.1) :=
    (isLawful_flatRowFn (topEntry n)).isLawfulBelow Y
  obtain ⟨q', hq', hcap, hres⟩ := hl (P (n + 2)) (isSelfVisible_gridPoint _ _)
    (fun d : (flatCells n).below (({0} : Finset (Fin 2)), 1) ↦ prescription d.1)
    (fun d : (flatCells n).below Y ↦ qAll d.1) (isLawfulBelow_prescription n) hq (fun d ↦ by
      rcases d with ⟨i | b, hd⟩
      · change min (P (n + 3)) (P (n + 2)) = min (P (i.val + n + 4)) (P (n + 2))
        rw [min_eq_right (gridPoint_le_gridPoint.mpr (by omega)),
          min_eq_right (gridPoint_le_gridPoint.mpr (by omega))]
      · exact absurd hd.1 (show ¬ ((univ : Finset (Fin 2)) ⊆ {0}) by decide))
  -- The lift, as a labelling of all cells.
  set w : FlatCell n → Label.{0} := fun y ↦ q' ⟨y, mem_below_univ y⟩ with hw
  have hlaw : (flatRows n).IsLawfulBelow Y (fun d ↦ w d) := by
    convert hq' using 1
  obtain ⟨-, hloc, hav⟩ := Rows.isLawfulBelow_iff_forall.mp hlaw
  -- The prescribed face is read literally.
  have hwd : ∀ j : Fin 5, j ≠ 4 → w (.inl j) = P (j.val + n + 4) := fun j hj ↦
    hres ⟨.inl j, ⟨(oldScope_subset_zero_iff j).mpr hj, le_rfl⟩⟩
  -- Step 1: the cap pins the low catalogue cells.
  have hpin : ∀ (c : FlatEntry n) (b : ℕ), b < n + 2 → c.1 = (fun _ ↦ P b) →
      w (.inr c) = P b := by
    intro c b hb hc
    have h := hcap ⟨.inr c, mem_below_univ _⟩
    have hqc : qAll (.inr c) = P b := by
      change cut n (fun _ ↦ P (n + 3)) c.1 = P b
      rw [hc, cut_const_const (by omega) (by omega)]
    change min (w (.inr c)) (P (n + 2)) = min (qAll (.inr c)) (P (n + 2)) at h
    rw [hqc, min_eq_left (gridPoint_le_gridPoint.mpr (by omega))] at h
    by_contra hne
    rcases le_or_gt (P (n + 2)) (w (.inr c)) with hge | hlt
    · rw [min_eq_right hge] at h
      exact absurd (P_inj h) (by omega)
    · rw [min_eq_left hlt.le] at h
      exact hne h
  have hw0 : w (.inr (lowEntry₀ n)) = P n := hpin _ _ (by omega) rfl
  have hw1 : w (.inr (lowEntry₁ n)) = P (n + 1) := hpin _ _ (by omega) rfl
  -- Step 2: availability at the fourth left cell forces a high new cell.
  obtain ⟨z, hz, hz3⟩ := hav (.inl 3) (.inr (topEntry n)) (mem_below_univ _) (subset_univ _) rfl
  rw [hwd 3 (by decide)] at hz3
  have h3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  rw [h3] at hz3
  rcases z with i | a
  · exact absurd (congrArg Prod.fst hz) (fun h ↦ not_univ_subset_oldScope i h.ge)
  -- Step 3: locality at `z`.
  obtain ⟨g, σ, -, heq⟩ := hloc (.inr a) (mem_below_univ _)
  have hd : ∀ j : Fin 5, j ≠ 4 → P (j.val + n + 4) = min (σ (a.1 j)) (g 1) := by
    intro j hj
    have h := heq ⟨.inl j, ⟨subset_univ _, le_rfl⟩⟩
    change min (w (.inl j)) (w (.inr a)) = min (σ (a.1 j)) (g 1) at h
    rw [hwd j hj, min_eq_left ((gridPoint_le_gridPoint.mpr (by have := j.isLt; omega)).trans hz3)]
      at h
    exact h
  have hc : ∀ (c : FlatEntry n) (b : ℕ), w (.inr c) = P b → b < n + 2 →
      P b = min (σ (cut n a.1 c.1)) (g 1) := by
    intro c b hwc hb
    have h := heq ⟨.inr c, ⟨subset_univ _, le_rfl⟩⟩
    change min (w (.inr c)) (w (.inr a)) = min (σ (cut n a.1 c.1)) (g 1) at h
    rw [hwc, min_eq_left ((gridPoint_le_gridPoint.mpr (by omega)).trans hz3)] at h
    exact h
  -- The catalogue labelling of `z` is injective on the four left cells.
  have hinj : ∀ j j' : Fin 5, j ≠ 4 → j' ≠ 4 → a.1 j = a.1 j' → j = j' := by
    intro j j' hj hj' he
    have h := (hd j hj).trans ((congrArg (fun x ↦ min (σ x) (g 1)) he).trans (hd j' hj').symm)
    have := P_inj h
    exact Fin.ext (by omega)
  -- Step 4: the agreement heights with the two pinned cells differ.
  have hcut : cut n a.1 (lowEntry₀ n).1 ≠ cut n a.1 (lowEntry₁ n).1 := by
    intro he
    have h0 := hc (lowEntry₀ n) n hw0 (by omega)
    have h1 := hc (lowEntry₁ n) (n + 1) hw1 (by omega)
    rw [he] at h0
    exact absurd (P_inj (h0.trans h1.symm)) (by omega)
  have hhigh : ∀ i, P n < a.1 i := by
    intro i
    by_contra hle
    rw [not_lt] at hle
    exact hcut (cut_const_eq a.1 ⟨i, hle⟩
      (fun h ↦ absurd (hinj 0 1 (by decide) (by decide) h) (by decide)))
  -- Step 5: four distinct values in the three top blocks.
  have hblock : ∀ j : Fin 5, ∃ b, n < b ∧ b ≤ n + 3 ∧ a.1 j = P b := by
    intro j
    rcases a.val_cases j with h | ⟨b, hb, h⟩
    · exact absurd (h ▸ hhigh j) (not_lt.mpr bot_le)
    · exact ⟨b, gridPoint_lt_gridPoint.mp (h ▸ hhigh j), hb, h⟩
  obtain ⟨b0, h0l, h0u, h0⟩ := hblock 0
  obtain ⟨b1, h1l, h1u, h1⟩ := hblock 1
  obtain ⟨b2, h2l, h2u, h2⟩ := hblock 2
  obtain ⟨b3, h3l, h3u, h3⟩ := hblock 3
  have n01 : b0 ≠ b1 := fun h ↦ absurd (hinj 0 1 (by decide) (by decide) (by rw [h0, h1, h]))
    (by decide)
  have n02 : b0 ≠ b2 := fun h ↦ absurd (hinj 0 2 (by decide) (by decide) (by rw [h0, h2, h]))
    (by decide)
  have n03 : b0 ≠ b3 := fun h ↦ absurd (hinj 0 3 (by decide) (by decide) (by rw [h0, h3, h]))
    (by decide)
  have n12 : b1 ≠ b2 := fun h ↦ absurd (hinj 1 2 (by decide) (by decide) (by rw [h1, h2, h]))
    (by decide)
  have n13 : b1 ≠ b3 := fun h ↦ absurd (hinj 1 3 (by decide) (by decide) (by rw [h1, h3, h]))
    (by decide)
  have n23 : b2 ≠ b3 := fun h ↦ absurd (hinj 2 3 (by decide) (by decide) (by rw [h2, h3, h]))
    (by decide)
  omega

/-- **R1: the flat layer is consistent but not bountiful**, for every block bound: both pairs
of the failing lift are graded faces. -/
theorem not_isBountiful_flatRows (n : ℕ) : ¬ (flatRows n).IsBountiful := fun h ↦
  not_cappedLift_flatRows n
    (h (by simp [flatCells, CellScheme.gradedFaces]) (by simp [flatCells, CellScheme.gradedFaces])
      lift_le)

/-- The instance with five old cells, block bound `2 * 5 + 1 = 11`. -/
example : ¬ (flatRows 8).IsBountiful ∧ (flatRows 8).IsConsistent :=
  ⟨not_isBountiful_flatRows 8, isConsistent_flatRows 8⟩

end FlatCatalogue

/-! ### R2: the canonical layer lifts on the same seed -/

/-- The first coatom of a seed on two points is `{0}`. -/
private theorem erase_last_one : univ.erase (Fin.last 1) = ({0} : Finset (Fin 2)) := by decide

/-- **R2: the lift of R1 succeeds on the canonical layer.**  Over the seed with four cells on one
point, the canonical field layer lifts capped from `({0}, 1)` to `(univ, 1)`: by the completion at
arity zero, it is bountiful. -/
theorem cappedLift_fourCellSeed (α : Ordinal.{u}) :
    (fourCellSeed α).fieldLayerZero.rows.CappedLift
      (X := (({0} : Finset (Fin 2)), 1)) (Y := (univ, 1)) ⟨subset_univ _, le_rfl⟩ :=
  (fourCellSeed α).isBountiful_fieldLayerZero
    ⟨erase_last_one ▸ (fourCellSeed α).erase_last_mem_faces, one_pos, by simp⟩
    ⟨(fourCellSeed α).isWellFormed_fieldLayerZero.univ_mem_faces, one_pos, by simp⟩ _

/-- **R2, at the cap of R1.**  At the cap `ω * 10 + 1`, every prescription lawful below `({0}, 1)`
and every lawful ambient with the same observation at the cap below `({0}, 1)` have a lift that
reads the prescription literally and keeps the observation of the ambient at the cap at every cell
below `(univ, 1)`: the new cells of full scope and the cell of the other coatom included. -/
theorem exists_lift_fourCellSeed (α : Ordinal.{u})
    (p : (fourCellSeed α).fieldLayerZero.toCellScheme.below (({0} : Finset (Fin 2)), 1) →
      Label.{u})
    (q : (fourCellSeed α).fieldLayerZero.toCellScheme.below (univ, 1) → Label.{u})
    (hp : (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ p)
    (hq : (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ q)
    (hpq : ∀ d : (fourCellSeed α).fieldLayerZero.toCellScheme.below (({0} : Finset (Fin 2)), 1),
      min (q (Set.inclusion (CellScheme.below_mono _
        (show ((({0} : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ (univ, 1) from
          ⟨subset_univ _, le_rfl⟩)) d)) (P 10) = min (p d) (P 10)) :
    ∃ q' : (fourCellSeed α).fieldLayerZero.toCellScheme.below (univ, 1) → Label.{u},
      (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ q' ∧
        (∀ d, min (q' d) (P 10) = min (q d) (P 10)) ∧
        ∀ d : (fourCellSeed α).fieldLayerZero.toCellScheme.below (({0} : Finset (Fin 2)), 1),
          q' (Set.inclusion (CellScheme.below_mono _
            (show ((({0} : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ (univ, 1) from
              ⟨subset_univ _, le_rfl⟩)) d) = p d :=
  (Rows.cappedLift_iff_forall_exists _).mp (cappedLift_fourCellSeed α) (P 10)
    (isSelfVisible_gridPoint 1 10) p q hp hq hpq

/-- The inclusion of the cells below `({0}, 1)` among those below `(univ, 1)` in the canonical
layer over `fourCellSeed`. -/
private abbrev inclZero (α : Ordinal.{u}) :
    (fourCellSeed α).fieldLayerZero.toCellScheme.below (({0} : Finset (Fin 2)), 1) →
      (fourCellSeed α).fieldLayerZero.toCellScheme.below (univ, 1) :=
  Set.inclusion (CellScheme.below_mono _ lift_le)

/-- **Regression 5, the caps `⊤` and `⊥`** (the positive cap `ω * 10 + 1` is
`exists_lift_fourCellSeed`): at the cap `⊤` the lift of a prescription equal to the restriction of
the ambient is the ambient itself, and at the cap `⊥` every lawful prescription below `({0}, 1)`
extends to a labelling lawful below `(univ, 1)`. -/
example (α : Ordinal.{u}) :
    (∀ (p : (fourCellSeed α).fieldLayerZero.toCellScheme.below (({0} : Finset (Fin 2)), 1) →
        Label.{u}) (q : (fourCellSeed α).fieldLayerZero.toCellScheme.below (univ, 1) → Label.{u}),
      (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ p →
      (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ q → (∀ d, q (inclZero α d) = p d) →
      ∃ q', (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ q' ∧ q' = q ∧
        ∀ d, q' (inclZero α d) = p d) ∧
    ∀ p : (fourCellSeed α).fieldLayerZero.toCellScheme.below (({0} : Finset (Fin 2)), 1) →
        Label.{u}, (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ p →
      ∃ q' : (fourCellSeed α).fieldLayerZero.toCellScheme.below (univ, 1) → Label.{u},
        (fourCellSeed α).fieldLayerZero.rows.IsLawfulBelow _ q' ∧ ∀ d, q' (inclZero α d) = p d := by
  have h := (Rows.cappedLift_iff_forall_exists _).mp (cappedLift_fourCellSeed α)
  refine ⟨fun p q hp hq hpq ↦ ?_, fun p hp ↦ ?_⟩
  · obtain ⟨q', hq', hcap, hres⟩ := h ⊤ (isSelfVisible_top 1) p q hp hq fun d ↦ by
      rw [min_top_right, min_top_right]
      exact hpq d
    exact ⟨q', hq', funext fun d ↦ by simpa using hcap d, hres⟩
  · obtain ⟨q', hq', -, hres⟩ := h ⊥ (isSelfVisible_bot 1) p (fun _ ↦ ⊥) hp
      (Rows.isLawfulBelow_const_bot _) fun d ↦ by simp
    exact ⟨q', hq', hres⟩

/-- **Regression 6, literal faces**: at every stage that is zero or a limit, the completion of
the seed with four cells on one point has the two coatom types as its faces, labels included. -/
example (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    StageType.restrictFace (Coatom.left 0)
        ((fourCellSeed α).completionBelowFullGradeZero.completion hα) =
      some (fourCellSeed α).left ∧
    StageType.restrictFace (Coatom.right 0)
        ((fourCellSeed α).completionBelowFullGradeZero.completion hα) =
      some (fourCellSeed α).right :=
  ⟨CompletionBelowFullGrade.restrictFace_left_completion _ hα,
    CompletionBelowFullGrade.restrictFace_right_completion _ hα⟩

/-! ### R3 and R4: relative room and the literal-reading decoder, on explicit labellings -/

/-- The canonical code of a strictly increasing labelling `w` of `m` cells, with values other than
bottom and self-visible at `k`, is the canonical point of rank `i + 1` at the cell `i`. -/
private theorem canonicalCode_of_strictMono {k m : ℕ} {w : Fin m → Label.{u}} (hw : StrictMono w)
    (hv : ∀ i, IsSelfVisible k (w i)) (h0 : ∀ i, w i ≠ ⊥) (i : Fin m) :
    canonicalCode k w i = canonicalPoint k (i + 1) := by
  rw [canonicalCode_of_ne_bot (hv i) (h0 i)]
  congr 1
  have hset : ({y ∈ univ.image w | y ≠ ⊥ ∧ y ≤ w i} : Finset Label.{u}) =
      (Iic i).image w := by
    ext y
    simp only [mem_filter, mem_image, mem_univ, true_and, mem_Iic]
    constructor
    · rintro ⟨⟨j, rfl⟩, -, hj⟩
      exact ⟨j, hw.le_iff_le.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, h0 j, hw.monotone hj⟩
  rw [valueRank, hset, card_image_of_injective _ hw.injective, Fin.card_Iic]

/-- The canonical labelling of R3: `ω + 1` at the first of six cells, `ω * 3 + 1` elsewhere. -/
noncomputable def roomCanonical (i : Fin 6) : Label.{u} := if (i : ℕ) = 0 then P 1 else P 3

/-- The labelling of R3: `ω + 1` at the first cell, then `ω * (i + 3) + 1`, five distinct values
above `ω * 3 + 1`. -/
noncomputable def roomLabelling (i : Fin 6) : Label.{u} := P (if (i : ℕ) = 0 then 1 else i + 3)

/-- The canonical code of `roomLabelling`: the canonical points `ω * (2 i + 1) + 1`. -/
noncomputable def roomCode (i : Fin 6) : Label.{u} := P (2 * i + 1)

private theorem canonicalCode_roomLabelling : canonicalCode 1 roomLabelling.{u} = roomCode := by
  have hmono : StrictMono roomLabelling.{u} := fun i j hij ↦ gridPoint_lt_gridPoint.mpr (by
    have : (i : ℕ) < j := hij
    split_ifs <;> omega)
  funext i
  rw [canonicalCode_of_strictMono hmono (fun _ ↦ isSelfVisible_gridPoint _ _)
    (fun _ ↦ gridPoint_ne_bot _ _), canonicalPoint, roomCode]
  congr 2

private theorem canonicalCode_roomCode : canonicalCode 1 roomCode.{u} = roomCode := by
  rw [← canonicalCode_roomLabelling]
  exact canonicalCode_canonicalCode fun _ ↦ isSelfVisible_gridPoint _ _

/-- The canonical labelling of R3 agrees with `roomCode` capped at `ω * 3 + 1`. -/
private theorem min_roomCanonical (i : Fin 6) :
    min (roomCanonical.{u} i) (P 3) = min (roomCode i) (P 3) := by
  unfold roomCanonical roomCode
  split_ifs with h
  · rw [h]
  · rw [min_self, min_eq_right (gridPoint_le_gridPoint.mpr (by omega))]

/-- **The labelling `(ω + 1, ω * 3 + 1, …, ω * 3 + 1)` is canonical**: at the first cell by prefix
stability against `roomCode`, elsewhere at least `ω * 3 + 1` by relative room against `roomCode`
and at most the canonical point of rank `2`, since it takes two values. -/
theorem canonicalCode_roomCanonical : canonicalCode 1 roomCanonical.{u} = roomCanonical := by
  have hv (i : Fin 6) : IsSelfVisible 1 (roomCanonical.{u} i) := by
    unfold roomCanonical; split_ifs <;> exact isSelfVisible_gridPoint _ _
  have h0 (i : Fin 6) : roomCanonical.{u} i ≠ ⊥ := by
    unfold roomCanonical; split_ifs <;> exact gridPoint_ne_bot _ _
  funext i
  by_cases hi : (i : ℕ) = 0
  · have hlt : roomCanonical.{u} i < P 3 := by
      rw [roomCanonical, ite_eq_left hi]
      exact gridPoint_lt_gridPoint.mpr (by decide)
    rw [canonicalCode_eq_of_min_eq (w' := roomCode) hv (fun _ ↦ isSelfVisible_gridPoint _ _)
        min_roomCanonical hlt,
      canonicalCode_roomCode, roomCode, roomCanonical, ite_eq_left hi, hi]
  · have hge := min_canonicalCode_eq hv canonicalCode_roomCode min_roomCanonical i
    rw [roomCode, min_eq_right (gridPoint_le_gridPoint.mpr (by omega))] at hge
    have hlow : P 3 ≤ canonicalCode 1 roomCanonical.{u} i := min_eq_right_iff.mp hge
    have himage : (univ : Finset (Fin 6)).image roomCanonical.{u} ⊆ {P 1, P 3} := by
      intro y hy
      obtain ⟨j, -, rfl⟩ := mem_image.mp hy
      unfold roomCanonical
      split_ifs <;> simp
    have hrank : valueRank roomCanonical.{u} (roomCanonical i) ≤ 2 :=
      (card_filter_le _ _).trans ((card_le_card himage).trans card_le_two)
    have hup : canonicalCode 1 roomCanonical.{u} i ≤ P 3 := by
      rw [canonicalCode_of_ne_bot (hv i) (h0 i)]
      exact canonicalPoint_le_canonicalPoint.mpr hrank
    rw [le_antisymm hup hlow, roomCanonical, ite_eq_right hi]

/-- **R3, relative room.**  The canonical labelling `a = (ω + 1, ω * 3 + 1, …, ω * 3 + 1)` and the
labelling `w = (ω + 1, ω * 4 + 1, …, ω * 8 + 1)` agree capped at `ω * 3 + 1`, and `w` takes five
distinct values above it, while `a` takes one.  The canonical code of `w`,
`(ω + 1, ω * 3 + 1, ω * 5 + 1, …, ω * 11 + 1)`, still agrees with `a` capped at `ω * 3 + 1`
(`Label.min_canonicalCode_eq`). -/
example (d : Fin 6) :
    min (roomLabelling.{u} d) (P 3) = min (roomCanonical d) (P 3) ∧
      min (canonicalCode 1 roomLabelling.{u} d) (P 3) = min (roomCanonical d) (P 3) := by
  have hag (i : Fin 6) : min (roomLabelling.{u} i) (P 3) = min (roomCanonical i) (P 3) := by
    unfold roomLabelling roomCanonical
    split_ifs with h
    · rfl
    · rw [min_self, min_eq_right (gridPoint_le_gridPoint.mpr (by omega))]
  exact ⟨hag d, min_canonicalCode_eq (fun _ ↦ isSelfVisible_gridPoint _ _)
    canonicalCode_roomCanonical hag d⟩

/-- The labelling of R4: `(ω + 1, ω * 7 + 1)`. -/
noncomputable def stripLabelling (i : Fin 2) : Label.{u} := if (i : ℕ) = 0 then P 1 else P 7

private theorem isSelfVisible_stripLabelling (i : Fin 2) :
    IsSelfVisible 1 (stripLabelling.{u} i) := by
  unfold stripLabelling
  split_ifs
  exacts [isSelfVisible_gridPoint _ _, isSelfVisible_gridPoint _ _]

private theorem stripLabelling_ne_bot (i : Fin 2) : stripLabelling.{u} i ≠ ⊥ := by
  unfold stripLabelling
  split_ifs
  exacts [gridPoint_ne_bot _ _, gridPoint_ne_bot _ _]

/-- Its canonical code is `(ω + 1, ω * 3 + 1)`: the least code above the cut `ω * 3 + 1` is the cut
itself. -/
theorem canonicalCode_stripLabelling (i : Fin 2) :
    canonicalCode 1 stripLabelling.{u} i = if (i : ℕ) = 0 then P 1 else P 3 := by
  have hmono : StrictMono stripLabelling.{u} := fun i j hij ↦ by
    have : (i : ℕ) < j := hij
    unfold stripLabelling
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    exact gridPoint_lt_gridPoint.mpr (by decide)
  rw [canonicalCode_of_strictMono hmono isSelfVisible_stripLabelling stripLabelling_ne_bot,
    canonicalPoint]
  split_ifs with h
  · rw [h]
  · rw [show (i : ℕ) = 1 by omega]

/-- **R4, the literal-reading decoder at a strip.**  At the cut `h = ω * 3 + 1`, the literal-reading
decoder of `(ω + 1, ω * 7 + 1)` reads its canonical code `(ω + 1, ω * 3 + 1)` back literally, and
`ω * 3 + 1 = h` is read as `ω * 7 + 1`.  No witness bounded by grade `1` that is the identity on the
strip `[ω * 3, h)` does this: it would send `h = vr 1 1 (ω * 3)` to `vr 1 1 (ω * 3) = h`. -/
example : (∀ i, literalDecoder 1 stripLabelling.{u} (P 3) (canonicalCode 1 stripLabelling i) =
      stripLabelling i) ∧
    ¬ ∃ κ : Label.{u} → Label.{u}, IsWitness (stepSuppressor 1) κ ∧
      κ (gridPoint 0 3) = gridPoint 0 3 ∧ κ (P 3) = P 7 := by
  refine ⟨literalDecoder_canonicalCode isSelfVisible_stripLabelling fun i ↦ ?_, ?_⟩
  · rw [canonicalCode_stripLabelling]
    unfold stripLabelling
    split_ifs
    · rfl
    · rw [min_self, min_eq_right (gridPoint_le_gridPoint.mpr (by decide))]
  · rintro ⟨κ, hκ, h0, h1⟩
    have hvr : visibilityReplace 1 1 (gridPoint.{u} 0 3) = P 3 := by
      rw [gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
      rfl
    have h := hκ.visibilityReplace_comm (gridPoint 0 3) 1 (by simp [stepSuppressor]) 1 le_rfl
    rw [hvr, h1, h0, hvr] at h
    exact absurd (gridPoint_le_gridPoint.mp h.le) (by decide)

/-! ### Regressions at arity zero -/

/-- `CodingExamples.pointRow x`, one cell on one point with row `x`, is legal for every row value
below `ω ^ 2` self-visible at `1`. -/
private theorem isLegal_pointRow {x : Label.{u}} (hx : x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}))
    (hv : IsSelfVisible 1 x) : (CodingExamples.pointRow x).IsLegal :=
  isLegal_onePointScheme (c := 1) (r := fun _ ↦ x) one_pos (fun _ _ _ ↦ le_rfl) (fun _ ↦ hx)
    fun _ ↦ hv

private theorem isLegal_pointRow_three : (CodingExamples.pointRow (3 : Label.{u})).IsLegal :=
  isLegal_pointRow (lt_omega0_sq_iff.mpr (.inr ⟨0, 3, by simp⟩)) (by simp)

private theorem isLegal_pointRow_omega0_add_five :
    (CodingExamples.pointRow (gridPoint.{u} 5 1)).IsLegal :=
  isLegal_pointRow (gridPoint_lt_omega0_sq 5 1) ((isSelfVisible_gridPoint 5 1).mono (by omega))

/-- **The seed with long rows** (regression 1): the amalgam over the empty face of
`pointRow 3` and `pointRow (ω + 5)`, whose row values exceed the grade plus one, with bottom
labels. -/
noncomputable def longRowSeed (α : Ordinal.{u}) : Seed.{u} α 0 :=
  let ta := isLegal_pointRow_three.toStageType α
  let tb := isLegal_pointRow_omega0_add_five.toStageType α
  have hpa := Option.isSome_iff_exists.mp (ta.isSome_restrictFace_of_zero (Coatom.face 0))
  have hpb := Option.isSome_iff_exists.mp (tb.isSome_restrictFace_of_zero (Coatom.face 0))
  Seed.ofCoatoms (isLegal_pointRow_three.isLegal_toStageType α)
    (isLegal_pointRow_omega0_add_five.isLegal_toStageType α) hpa.choose_spec
    (hpb.choose_spec.trans (congrArg some (StageType.eq_of_zero _ _)))

/-- **Regressions 1 and 6, long rows with bottom labels**: the seed with long rows has a
completion below the full grade, and at every stage that is zero or a limit its completion has the
two coatom types as its faces, labels included. -/
example (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    Nonempty (CompletionBelowFullGrade (longRowSeed α)) ∧
    StageType.restrictFace (Coatom.left 0)
        ((longRowSeed α).completionBelowFullGradeZero.completion hα) =
      some (longRowSeed α).left ∧
    StageType.restrictFace (Coatom.right 0)
        ((longRowSeed α).completionBelowFullGradeZero.completion hα) =
      some (longRowSeed α).right :=
  ⟨(longRowSeed α).nonempty_completionBelowFullGrade_zero,
    CompletionBelowFullGrade.restrictFace_left_completion _ hα,
    CompletionBelowFullGrade.restrictFace_right_completion _ hα⟩

/-- **Regression 2, a label `⊤`**: in the completion at arity zero of any seed, an old cell
labelled `⊤` keeps `⊤`, and some new cell of graded index `(univ, 1)` is labelled `⊤`. -/
example {α : Ordinal.{u}} (I : Seed.{u} α 0) (d : Fin I.amalgam.card)
    (hd : I.amalgam.label d = ⊤) :
    I.completionBelowFullGradeZero.label (I.completionBelowFullGradeZero.embed d) = ⊤ ∧
      ∃ u, I.completionBelowFullGradeZero.scheme.toCellScheme.gradedIndex u = (univ, 1) ∧
        I.completionBelowFullGradeZero.label u = ⊤ := by
  set F := I.completionBelowFullGradeZero
  have htop : F.label (F.embed d) = ⊤ := (F.label_embed d).trans hd
  refine ⟨htop, ?_⟩
  obtain ⟨t, ht⟩ := I.exists_gradedIndex_eq_univ
  obtain ⟨u, hu, hle⟩ := F.isLawful.availability (F.embed d) t
    (by rw [show F.scheme.toCellScheme.scope t = univ from congrArg Prod.fst ht]
        exact subset_univ _)
    ((I.fieldLayerZero_grade _).trans (I.fieldLayerZero_grade t).symm)
  exact ⟨u, hu.trans ht, top_le_iff.mp (htop ▸ hle)⟩

/-- **Regression 3, labels above the grade plus one**: the labelling `(3, ω * 5 + 3)` of two
cells of grade `1` has the canonical code `(ω + 1, ω * 3 + 1)`, short at `1`, and the
literal-reading decoder at the least grid point reads it literally. -/
example : canonicalCode 1 (fun i : Fin 2 ↦ if (i : ℕ) = 0 then gridPoint.{u} 3 0 else gridPoint 3 5)
      = (fun i : Fin 2 ↦ if (i : ℕ) = 0 then P 1 else P 3) ∧
    ∀ i : Fin 2, literalDecoder 1 (fun i : Fin 2 ↦ if (i : ℕ) = 0 then gridPoint.{u} 3 0
      else gridPoint 3 5) (gridPoint 1 0) (canonicalCode 1 (fun i : Fin 2 ↦
        if (i : ℕ) = 0 then gridPoint.{u} 3 0 else gridPoint 3 5) i) =
      if (i : ℕ) = 0 then gridPoint 3 0 else gridPoint 3 5 := by
  set w : Fin 2 → Label.{u} := fun i ↦ if (i : ℕ) = 0 then gridPoint 3 0 else gridPoint 3 5
  have hv (i : Fin 2) : IsSelfVisible 1 (w i) := by
    simp only [w]
    split_ifs
    exacts [(isSelfVisible_gridPoint 3 0).mono (by omega),
      (isSelfVisible_gridPoint 3 5).mono (by omega)]
  have h0 (i : Fin 2) : w i ≠ ⊥ := by
    simp only [w]
    split_ifs
    exacts [gridPoint_ne_bot _ _, gridPoint_ne_bot _ _]
  have hmono : StrictMono w := fun i j hij ↦ by
    have : (i : ℕ) < j := hij
    simp only [w]
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      (omega0_mul_add_natCast_lt (by exact_mod_cast (by decide : 0 < 5)) _ _))
  refine ⟨funext fun i ↦ ?_, literalDecoder_canonicalCode hv (min_canonicalCode_gridPoint_zero hv)⟩
  rw [canonicalCode_of_strictMono hmono hv h0, canonicalPoint]
  split_ifs with h
  · rw [h]
  · rw [show (i : ℕ) = 1 by omega]

end SmallArityExamples

end VaughtConjecture

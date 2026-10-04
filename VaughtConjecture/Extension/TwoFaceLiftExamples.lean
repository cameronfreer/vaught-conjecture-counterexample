/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLift
import VaughtConjecture.Extension.TowerExamples
import VaughtConjecture.Extension.UnionFillCounterexample
import VaughtConjecture.Extension.SmallArityOneExamples

/-!
# Special cases of the two-face lift at the grade one, and completions at arity two

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here the special cases of
`2FL(1)` and of the completion at the arities `m ≤ 2`); semantic contract, items 2–4.

Write `Q b f` for the label `ω * b + f`.

* **The ambient as its own extension** (`exists_twoFaceLift_of_eq`,
  `exists_twoFaceLift_of_lt`, `exists_twoFaceLift_top`).  At every grade `j`, if the prescription
  agrees with the catalogue entry on the old cells of grade at most `j`, the entry itself,
  restricted below `(univ, j)`, is a two-face lift.  This is the case when the prescription stays
  below the cap there (the first branch of the proof of `Seed.twoFaceLift_one`) and when the cap is
  `⊤`.
* **The seed of the union-fill counterexample** (`twoFaceLift_one_seed`,
  `nonempty_completionBelowFullGrade_seed`, `not_isLawfulBelow_pairLabelling_top`).  On the seed
  of `UnionFillCounterexample.T` with itself, on which the union fill fails, `2FL(1)` holds and
  there is a completion below the full grade.  The labelling that defeats the union fill is not
  lawful below the coatom `({0, 1, 3}, 2)`, so it is not a prescription of `2FL(1)`: the coupling
  `F ≤ A` of the second coatom is part of the hypothesis of the two-face lift, and is used by the
  step through the gluing at the grade `2`, not by `2FL(1)`.
* **Exactness above the cap on both faces** (`twoFaceLabelling`,
  `isLawfulBelow_twoFaceLabelling`, `exists_twoFaceLift_exact`).  On that seed, the
  prescription with the label `A_L` on the live cells of grade `1` of the first coatom, `A_R` on
  those of the second, and `F` on the live cells of grade `2`, is lawful below both coatoms at the
  grade `2` whenever `F ≤ A_L, A_R`.  With `A_L = ω + 1`, `A_R = ω * 2 + 1`, `F = 2` and the cap
  `2`, the two-face lift reads `ω + 1` at the cell `({2}, 1)` and `ω * 2 + 1` at the cell
  `({3}, 1)`, both above the cap, while agreeing with the catalogue entry capped at `2` on the new
  cells.  A lift from one coatom with the other free
  keeps the other coatom's labels only capped; here both are read literally.
* **`fourCellTripleSeed`** (`fourCellTripleSeed`, `restrictFace_completion_fourCellTripleSeed`):
  the seed on four points whose two coatom types are both the completion of
  `SmallArityOneExamples.fourCellPairSeed`.  It has a completion below the full grade, with no
  hypothesis, and that completion has the two coatom types as its faces, literally.
* **The examples of the tower at arity two, unconditionally** (`towerInvariant_two`,
  `towerInvariant_three`, `exists_lift_three`): the conditional statements of
  `VaughtConjecture.Extension.TowerExamples`, with `2FL(1)` supplied by `Seed.twoFaceLift_one`.

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.TwoFaceLiftExamples

open Finset Label CellScheme

/-! ### The ambient as its own extension -/

section Ambient

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **The catalogue entry is a two-face lift when the prescription is the entry on the old
cells**: at every grade `j` and cap `h`, if `w` agrees with the catalogue entry `a` at the old
cells of grade at most `j`, then `a` restricted below `(univ, j)` is lawful there, reads `w` at
those old cells, and agrees with `a` capped at `h`. -/
theorem exists_twoFaceLift_of_eq {j : ℕ} {a : Fin (I.tower j).card → Label.{u}}
    (ha : a ∈ (I.tower j).catalogue (j + 1)) {w : Fin I.amalgam.card → Label.{u}}
    (hw : ∀ d, I.amalgam.toCellScheme.grade d ≤ j → w d = a (I.towerEmbed j d)) (h : Label.{u}) :
    ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      (∀ e, min (r e) h = min (a e) h) ∧ ∀ e, r e = a e :=
  ⟨fun e ↦ a e, (Scheme.mem_catalogue.mp ha).1.isLawfulBelow _, fun d hd ↦ (hw d hd).symm,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- **Below the cap the two-face lift is the catalogue entry**: if the prescription stays below
the cap `h` at the old cells of grade at most `j` and agrees there with the entry capped at `h`,
it is the entry there, and the entry restricted below `(univ, j)` is a two-face lift. -/
theorem exists_twoFaceLift_of_lt {j : ℕ} {a : Fin (I.tower j).card → Label.{u}}
    (ha : a ∈ (I.tower j).catalogue (j + 1)) {h : Label.{u}} {w : Fin I.amalgam.card → Label.{u}}
    (hlt : ∀ d, I.amalgam.toCellScheme.grade d ≤ j → w d < h)
    (hag : ∀ d, I.amalgam.toCellScheme.grade d ≤ j → min (w d) h = min (a (I.towerEmbed j d)) h) :
    ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      (∀ e, min (r e) h = min (a e) h) ∧ ∀ e, r e = a e :=
  exists_twoFaceLift_of_eq I ha (fun d hd ↦ (eq_of_min_eq_of_lt (hag d hd) (hlt d hd)).symm) h

/-- **At the cap `⊤` the two-face lift is the catalogue entry**: agreement capped at `⊤` is
equality, so the prescription is the entry at the old cells. -/
theorem exists_twoFaceLift_top {j : ℕ} {a : Fin (I.tower j).card → Label.{u}}
    (ha : a ∈ (I.tower j).catalogue (j + 1)) {w : Fin I.amalgam.card → Label.{u}}
    (hag : ∀ d, I.amalgam.toCellScheme.grade d ≤ j + 1 →
      min (w d) ⊤ = min (a (I.towerEmbed j d)) ⊤) :
    ∃ r : (I.tower j).toCellScheme.below (univ, j) → Label.{u},
      (I.tower j).rows.IsLawfulBelow (univ, j) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ j),
        r ⟨I.towerEmbed j d, I.towerEmbed_mem_below hd⟩ = w d) ∧
      (∀ e, min (r e) ⊤ = min (a e) ⊤) ∧ ∀ e, r e = a e :=
  exists_twoFaceLift_of_eq I ha (fun d hd ↦ by simpa using hag d (by omega)) ⊤

end Ambient

/-! ### The seed of the union-fill counterexample -/

section UnionFillSeed

open UnionFillCounterexample

variable {α : Ordinal.{u}}

/-- **`2FL(1)` holds for the seed on which the union fill fails.** -/
theorem twoFaceLift_one_seed : (seed α).TwoFaceLift 1 :=
  (seed α).twoFaceLift_one

/-- **The seed on which the union fill fails has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_seed :
    Nonempty (CompletionBelowFullGrade (seed α)) :=
  (seed α).nonempty_completionBelowFullGrade_of_le_two le_rfl

/-- **The labelling that defeats the union fill is not a prescription of `2FL(1)`**: it is not
lawful below both coatoms at the grade `2` (`not_isLawfulBelow_pairLabelling_top`). -/
theorem not_isLawfulBelow_coatoms_pairLabelling_top :
    ¬ ((seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 3), 2)
        (fun d ↦ pairLabelling rowValue ⊤ ((seed α).amalgam.toCellScheme.gradedIndex d)) ∧
      (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 2)
        (fun d ↦ pairLabelling rowValue ⊤ ((seed α).amalgam.toCellScheme.gradedIndex d))) :=
  fun h ↦ not_isLawfulBelow_pairLabelling_top h.2

/-! ### Exactness above the cap on both faces -/

/-- The graded indices of the live cells of grade `1` of the first coatom, in `Fin 4`. -/
def leftPairs : Finset (Finset (Fin 4) × ℕ) := {({2}, 1), ({1, 2}, 1), ({0, 1, 2}, 1)}

/-- The graded indices of the live cells of grade `1` of the second coatom, in `Fin 4`. -/
def rightPairs : Finset (Finset (Fin 4) × ℕ) := {({3}, 1), ({1, 3}, 1), ({0, 1, 3}, 1)}

/-- The graded indices of the live cells of grade `2`, in `Fin 4`. -/
def gradeTwoPairs : Finset (Finset (Fin 4) × ℕ) := {({0, 1}, 2), ({0, 1, 2}, 2), ({0, 1, 3}, 2)}

/-- The kind of a graded index in `Fin 4`: `1` on the first coatom's live pairs of grade `1`, `2`
on the second's, `3` on the live pairs of grade `2`, and `0` otherwise. -/
def pairKind (X : Finset (Fin 4) × ℕ) : Fin 4 :=
  if X ∈ leftPairs then 1 else if X ∈ rightPairs then 2 else if X ∈ gradeTwoPairs then 3 else 0

/-- **The two-face labelling** `twoFaceLabelling A_L A_R F`, read off graded indices: `A_L` on the
live cells of grade `1` of the first coatom, `A_R` on those of the second, `F` on the live cells of
grade `2`, and `⊥` elsewhere. -/
noncomputable def twoFaceLabelling (AL AR F : Label.{u}) (X : Finset (Fin 4) × ℕ) : Label.{u} :=
  ![⊥, AL, AR, F] (pairKind X)

/-- The kind of a cell of `UnionFillCounterexample.S`: `0` if not live, `1` if live of grade `1`,
`2` if live of grade `2`. -/
private def liveKind (d : Fin 9) : Fin 3 :=
  if live d = true then (if cellGrade d = 1 then 1 else 2) else 0

private theorem labelling_eq_liveKind (A F : Label.{u}) (d : Fin 9) :
    labelling A F d = ![⊥, A, F] (liveKind d) := by
  unfold labelling liveKind
  split_ifs <;> rfl

private theorem pairKind_left : ∀ d : Fin 9,
    pairKind (Prod.map (Finset.map (Coatom.left 2)) id (cells.gradedIndex d)) =
      ![0, 1, 3] (liveKind d) := by
  decide +kernel

private theorem pairKind_right : ∀ d : Fin 9,
    pairKind (Prod.map (Finset.map (Coatom.right 2)) id (cells.gradedIndex d)) =
      ![0, 2, 3] (liveKind d) := by
  decide +kernel

/-- Read along the first coatom, the two-face labelling is `labelling A_L F`. -/
private theorem twoFaceLabelling_left (AL AR F : Label.{u}) (d : Fin 9) :
    twoFaceLabelling AL AR F (Prod.map (Finset.map (Coatom.left 2)) id (cells.gradedIndex d)) =
      labelling AL F d := by
  rw [twoFaceLabelling, pairKind_left, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

/-- Read along the second coatom, the two-face labelling is `labelling A_R F`. -/
private theorem twoFaceLabelling_right (AL AR F : Label.{u}) (d : Fin 9) :
    twoFaceLabelling AL AR F (Prod.map (Finset.map (Coatom.right 2)) id (cells.gradedIndex d)) =
      labelling AR F d := by
  rw [twoFaceLabelling, pairKind_right, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

/-- Lawfulness transported along the restriction to a face. -/
private theorem isLawfulBelow_comap_cellMap_iff {n k : ℕ} (S' : Scheme.{u} n) (f : Fin k ↪ Fin n)
    (X : Finset (Fin k) × ℕ) (x : Fin S'.card → Label.{u}) :
    (S'.comap f).rows.IsLawfulBelow X (fun i ↦ x (S'.cellMap f i)) ↔
      S'.rows.IsLawfulBelow (Prod.map (Finset.map f) id X) (fun d ↦ x d) :=
  CellScheme.Rows.isLawfulBelow_comap_iff (R := S'.rows) (S'.isLowerEmbedding_comap f)
    (S'.image_cellMap_below f X) (r := fun d ↦ x d)

/-- A labelling of `T` that is a labelling `L` of graded indices, read along `f`, where `L` read
along `f` is `labelling A F`, is lawful below every pair not above the apex. -/
private theorem isLawfulBelow_T_of_eq {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hFA : F ≤ A) {f : Fin 3 ↪ Fin 4}
    {L : Finset (Fin 4) × ℕ → Label.{u}}
    (hL : ∀ d, L (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F d)
    {X : Finset (Fin 3) × ℕ} (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X)
    (x : Fin (T α).toScheme.card → Label.{u})
    (hx : ∀ i, x i = L (Prod.map (Finset.map f) id ((T α).toScheme.toCellScheme.gradedIndex i))) :
    (T α).toScheme.rows.IsLawfulBelow X (fun i ↦ x i) := by
  refine (isLawfulBelow_T_iff hX).mpr ?_
  convert (isLawful_labelling hA hF hFA).isLawfulBelow X using 1
  funext d
  refine (hx _).trans ?_
  rw [gradedIndex_T_castSucc]
  exact hL d.1

/-- **The two-face labelling is lawful below a coatom** `univ.map f` at the grade `2`, for a stage
type whose face along `f` is `T`, when its reading along `f` is `labelling A F` with `F ≤ A`. -/
private theorem isLawfulBelow_coatom {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hFA : F ≤ A) {f : Fin 3 ↪ Fin 4} {Am : StageType.{u} α 4}
    (hf : StageType.restrictFace f Am = some (T α)) {L : Finset (Fin 4) × ℕ → Label.{u}}
    (hL : ∀ d, L (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F d) :
    Am.rows.IsLawfulBelow (univ.map f, 2) (fun d ↦ L (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = L (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun i ↦ x i) := by
    rw [heq]
    exact fun x hx ↦ isLawfulBelow_T_of_eq hA hF hFA hL (fun h ↦ absurd h.2 (by decide)) x hx
  exact (isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 3)), 2)
    fun d ↦ L (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg L (Am.toScheme.map_comap_gradedIndex f i).symm)

/-- **The seed of `T` with itself has `T` as both coatom types.** -/
theorem left_seed_right_seed : (seed α).left = T α ∧ (seed α).right = T α := ⟨rfl, rfl⟩

/-- **The two-face labelling is lawful below both coatoms at the grade `2`**, on a seed on four
points whose two coatom types are `T` (such as `seed α`, `left_seed_right_seed`), when `A_L` and
`A_R` are self-visible at `1`, `F` at `2`, and `F ≤ A_L, A_R`. -/
theorem isLawfulBelow_twoFaceLabelling {I : Seed.{u} α 2} (hIL : I.left = T α)
    (hIR : I.right = T α) {AL AR F : Label.{u}} (hAL : IsSelfVisible 1 AL)
    (hAR : IsSelfVisible 1 AR) (hF : IsSelfVisible 2 F) (hFL : F ≤ AL) (hFR : F ≤ AR) :
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 3), 2)
        (fun d ↦ twoFaceLabelling AL AR F (I.amalgam.toCellScheme.gradedIndex d)) ∧
      I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 2)
        (fun d ↦ twoFaceLabelling AL AR F (I.amalgam.toCellScheme.gradedIndex d)) := by
  constructor
  · rw [← Coatom.univ_map_left]
    exact isLawfulBelow_coatom hAL hF hFL (hIL ▸ I.restrictFace_left)
      (twoFaceLabelling_left AL AR F)
  · rw [← Coatom.univ_map_right]
    exact isLawfulBelow_coatom hAR hF hFR (hIR ▸ I.restrictFace_right)
      (twoFaceLabelling_right AL AR F)

section Labels

open Ordinal

/-- The label `ω * b + f`. -/
noncomputable def Q (b f : ℕ) : Label.{u} :=
  ((ω * (b : Ordinal.{u}) + (f : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

private theorem Q_le_Q_iff {b b' f f' : ℕ} : Q.{u} b f ≤ Q b' f' ↔ b < b' ∨ b = b' ∧ f ≤ f' := by
  rw [Q, Q, WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff, Nat.cast_lt,
    Nat.cast_inj]

private theorem isSelfVisible_Q {k b f : ℕ} : IsSelfVisible k (Q.{u} b f) ↔ k ≤ f := by
  rw [Q, isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

end Labels

/-- **Exactness above the cap on both faces.**  On a seed on four points whose two coatom types are
`T` (such as `seed α`, on which the union fill fails), take the prescription
`twoFaceLabelling (ω + 1) (ω * 2 + 1) 2`, lawful below both coatoms at the grade `2`, the cap `2`,
and a catalogue entry `a` of the layer at the grade `2` agreeing with it capped at `2`.  Then
`2FL(1)` gives a labelling lawful below `(univ, 1)` that reads `ω + 1` at the old cell `({2}, 1)`
of the first coatom and `ω * 2 + 1` at the old cell `({3}, 1)` of the second, both above the cap,
and agrees with `a` capped at `2` at every cell below `(univ, 1)`, new cells included. -/
theorem exists_twoFaceLift_exact {I : Seed.{u} α 2} (hIL : I.left = T α) (hIR : I.right = T α)
    {a : Fin (I.tower 1).card → Label.{u}} (ha : a ∈ (I.tower 1).catalogue (1 + 1))
    (hag : ∀ d, I.amalgam.toCellScheme.grade d ≤ 2 →
      min (twoFaceLabelling (Q 1 1) (Q 2 1) (Q 0 2) (I.amalgam.toCellScheme.gradedIndex d))
        (Q 0 2) = min (a (I.towerEmbed 1 d)) (Q 0 2)) :
    ∃ r : (I.tower 1).toCellScheme.below (univ, 1) → Label.{u},
      (I.tower 1).rows.IsLawfulBelow (univ, 1) r ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ 1),
        I.amalgam.toCellScheme.gradedIndex d = ({2}, 1) →
          r ⟨I.towerEmbed 1 d, I.towerEmbed_mem_below hd⟩ = Q 1 1) ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ 1),
        I.amalgam.toCellScheme.gradedIndex d = ({3}, 1) →
          r ⟨I.towerEmbed 1 d, I.towerEmbed_mem_below hd⟩ = Q 2 1) ∧
      (∀ e, min (r e) (Q 0 2) = min (a e) (Q 0 2)) ∧ Q 0 2 < Q.{u} 1 1 ∧ Q 0 2 < Q.{u} 2 1 := by
  have hlt (b : ℕ) (hb : 0 < b) : Q.{u} 0 2 < Q b 1 :=
    lt_of_le_of_ne (Q_le_Q_iff.mpr (.inl hb)) fun h ↦ by
      have := Q_le_Q_iff.mp h.ge
      omega
  obtain ⟨hwC, hwD⟩ := isLawfulBelow_twoFaceLabelling hIL hIR (isSelfVisible_Q.mpr le_rfl)
    (isSelfVisible_Q.mpr le_rfl) (isSelfVisible_Q.mpr le_rfl) (hlt 1 one_pos).le
    (hlt 2 two_pos).le
  obtain ⟨r, hr, hrw, hra⟩ := I.twoFaceLift_one a ha (Q 0 2) (isSelfVisible_Q.mpr le_rfl)
    (isShort_gridPoint 2 0) (bot_lt_iff_ne_bot.mpr WithBot.coe_ne_bot)
    (fun d ↦ twoFaceLabelling (Q 1 1) (Q 2 1) (Q 0 2) (I.amalgam.toCellScheme.gradedIndex d))
    hwC hwD hag
  refine ⟨r, hr, fun d hd hX ↦ ?_, fun d hd hX ↦ ?_, hra, hlt 1 one_pos, hlt 2 two_pos⟩
  · rw [hrw d hd, hX]; rfl
  · rw [hrw d hd, hX]; rfl

end UnionFillSeed

/-! ### `fourCellTripleSeed` -/

section TripleSeed

variable (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α)

/-- **The seed on four points with four cells on its common point.**  Its two coatom types are both
the completion of `SmallArityOneExamples.fourCellPairSeed`, a legal stage type on three points,
whose face along `Fin.castSuccEmb` is the first coatom type of that seed. -/
noncomputable def fourCellTripleSeed : Seed.{u} α 2 :=
  let F := (SmallArityOneExamples.fourCellPairSeed α hα).completionBelowFullGradeOne
  Seed.ofCoatoms (F.isLegal_completion hα) (F.isLegal_completion hα)
    (F.restrictFace_left_completion hα) (F.restrictFace_left_completion hα)

/-- **`fourCellTripleSeed` has a completion below the full grade, with literal faces**: with no
hypothesis (`Seed.nonempty_completionBelowFullGrade_of_le_two`), and its completion has the
completion of `SmallArityOneExamples.fourCellPairSeed` as its faces along both coatoms, labels
included. -/
theorem restrictFace_completion_fourCellTripleSeed :
    ∃ F : CompletionBelowFullGrade (fourCellTripleSeed α hα),
      StageType.restrictFace (Coatom.left 2) (F.completion hα) =
          some ((SmallArityOneExamples.fourCellPairSeed α hα).completionBelowFullGradeOne.completion
            hα) ∧
        StageType.restrictFace (Coatom.right 2) (F.completion hα) =
          some ((SmallArityOneExamples.fourCellPairSeed α hα).completionBelowFullGradeOne.completion
            hα) :=
  let F := ((fourCellTripleSeed α hα).nonempty_completionBelowFullGrade_of_le_two le_rfl).some
  ⟨F, F.restrictFace_left_completion hα, F.restrictFace_right_completion hα⟩

end TripleSeed

/-! ### The examples of the tower at arity two, unconditionally -/

section ArityTwo

variable {α : Ordinal.{u}} (I : Seed.{u} α 2)

/-- **The invariant at the grade `2` at arity two**, with no hypothesis. -/
theorem towerInvariant_two : I.TowerInvariant 2 :=
  TowerExamples.towerInvariant_two_of_twoFaceLift I I.twoFaceLift_one

/-- **The invariant at the grade `3` at arity two**, with no hypothesis. -/
theorem towerInvariant_three : I.TowerInvariant 3 :=
  TowerExamples.towerInvariant_three_of_twoFaceLift I I.twoFaceLift_one

/-- **The lift at the grade `3` at arity two, coordinate by coordinate**, with no hypothesis: at
every cap `c` self-visible at `3`, a prescription lawful below the coatom `({0, 1, 2}, 3)` and an
ambient lawful below `(univ, 3)` with the same observation at `c` below the coatom have a lift that
reads the prescription literally and keeps the observation of the ambient at every cell below
`(univ, 3)`. -/
theorem exists_lift_three {c : Label.{u}} (hc : IsSelfVisible 3 c)
    (p : (I.tower 3).toCellScheme.below (univ.erase (Fin.last 3), 3) → Label.{u})
    (q : (I.tower 3).toCellScheme.below (univ, 3) → Label.{u})
    (hp : (I.tower 3).rows.IsLawfulBelow _ p) (hq : (I.tower 3).rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((univ.erase (Fin.last 3), 3) : Finset (Fin 4) × ℕ) ≤ (univ, 3) from
        ⟨erase_subset _ _, le_rfl⟩)) d)) c = min (p d) c) :
    ∃ q' : (I.tower 3).toCellScheme.below (univ, 3) → Label.{u},
      (I.tower 3).rows.IsLawfulBelow _ q' ∧ (∀ d, min (q' d) c = min (q d) c) ∧
        ∀ d, q' (Set.inclusion (CellScheme.below_mono _
          (show ((univ.erase (Fin.last 3), 3) : Finset (Fin 4) × ℕ) ≤ (univ, 3) from
            ⟨erase_subset _ _, le_rfl⟩)) d) = p d :=
  TowerExamples.exists_lift_three_of_twoFaceLift I I.twoFaceLift_one hc p q hp hq hpq

end ArityTwo

end VaughtConjecture.TwoFaceLiftExamples

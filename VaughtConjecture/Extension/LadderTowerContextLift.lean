/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SeedLadderCompletion
import VaughtConjecture.Extension.SeedAttachment

/-!
# The lift of the ladder tower from the context coatom: the reduction

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the recognizing growth carrier).

**Superseded.**  The carrier is now built over the replicated scheme of the attachment
(`Seed.replicated`), not over the ladder tower of the amalgam; the context lift there is reduced in
`VaughtConjecture.Extension.LadderTowerContextLiftReplicated` and
`VaughtConjecture.Extension.LadderTowerContextLiftState`.  This file is kept; its statements are
about the amalgam tower only.

Let `T` be the ladder tower of a seed at the height `m` (`Seed.ladderTower`), on the points
`Fin (m + 2)`, with the context coatom `univ.erase (Fin.last (m + 1))`.  Bountifulness of `T` is
reduced to the lifts from the two coatoms into the full faces `(univ, j)`, `2 ≤ j ≤ m + 1`
(`Seed.isBountiful_ladderTower_of_coatomLifts`).  This file reduces the lift from the **context
coatom** to two statements, each a finite statement about the seed and the tower:

* **the state lift** (`Seed.ContextStateLift j`): from a cap `c` self-visible at `j`, an ambient
  `q` lawful below `(univ, j)` and a prescription `p` lawful below `(univ.erase (Fin.last _), j)`
  with the same observation at `c`, a complete lawful state `P` of the amalgam satisfying the
  catalogue predicate `A (m + 2)`, equal to `p` on the cells of the context coatom below the
  grade, with the observation of `q` at `c` on the cells of the amalgam below the grade;
* **the coding of states** (`Seed.StateCoding j`): such a state is the decoded reading of a state
  `R` of the catalogue (values in `Γ`, lawful, satisfying `A (m + 2)`) by a witness `ν` bounded by
  the grade `j` (sending no non-bottom label to bottom when the cap is `⊥`), on the cells of the
  amalgam below the grade; and the decoded writing `ν ∘ T.v R` of `R` in the tower has the
  observation of `q` at `c` at every cell below `(univ, j)`: on the ladder and on the layers of
  full scope as well.

**The reduction** (`Seed.cappedLift_context_of_stateLift`): the two give the capped lift of `T`
from `(univ.erase (Fin.last (m + 1)), j)` to `(univ, j)`, in the shape of
`Seed.isBountiful_ladderTower_of_coatomLifts`.  The lift is `ν ∘ T.v R`: the writing of a state of
the catalogue is lawful on the tower (`Seed.ladderTower_lawful`), and decoding keeps lawfulness,
with the ambient as lawful companion at a positive cap
(`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`) and by bottom reflection at the cap `⊥`
(`Seed.isLawfulBelow_map_writing`); at the cells of the amalgam the writing of a lawful state is
the state (`Seed.ladderTower_v_towerAmalgamEmb`), and every cell below the context coatom is a cell
of the amalgam (`Seed.exists_towerAmalgamEmb_eq_of_mem_below`).

**The state lift from bountifulness** (`Seed.contextStateLift_of_vanishing`): when the catalogue
predicate holds for every lawful state vanishing above the grade `j` (for the admission predicate,
every grade below the threshold), the state lift holds: the amalgam lifts capped from the context
coatom into `(univ, j)` (`Seed.isBountiful`), and the lifted section, extended by `⊥` above the
grade (`CellScheme.Rows.isLawfulBelow_extendAbove`), is a complete lawful state.

What is not proved here: the coding of states, at any grade; the state lift at the grades from the
threshold on.  No (R3) or (R4) claim.

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the coatom amalgam and its bountifulness are
[Kni26, Definition 4.3.1 and Lemma 4.3.2].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin I.amalgam.card → Label.{u}) → Prop} {B' : ℕ}

/-! ### The writing of a state -/

/-- **The tower writes a lawful state as the state** at the cells of the amalgam. -/
theorem ladderTower_v_towerAmalgamEmb (hcard : I.amalgam.card ≤ H)
    {R : Fin I.amalgam.card → Label.{u}} (hR : I.amalgam.rows.IsLawful R)
    (a : Fin I.amalgam.card) :
    (I.ladderTower H Γ A B' m).v R (I.towerAmalgamEmb H Γ A B' a) = R a := by
  rw [towerAmalgamEmb_apply]
  refine (Scheme.layerTower_v_emb (B := I.towerBase H) (C := I.towerCat Γ A)
    (G := fun k ↦ grid k B') R _ m).trans ?_
  change I.stateExt H R (Fin.castAdd _ a) = R a
  rw [stateExt_of_isLawful hR hcard, Fin.append_left]

/-- **The decoded writing of a state of the catalogue is lawful** below `(univ, j)`, for a witness
`ν` bounded by the grade `j` that sends no non-bottom label to bottom. -/
theorem isLawfulBelow_map_writing (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {R : Fin I.amalgam.card → Label.{u}} (hR : R ∈ I.towerCat Γ A (m + 2)) {j : ℕ}
    {ν : Label.{u} → Label.{u}} (hν : IsWitness (stepSuppressor j) ν)
    (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ ν ((I.ladderTower H Γ A B' m).v R d) :=
  (((I.ladderTower_lawful hH hcard hΓ hA m).2 R hR).1.isLawfulBelow _).map_of_apply_eq_bot
    (fun d ↦ d.2.2) hν fun _ h ↦ hbot _ h

/-! ### The cells of the amalgam -/

/-- **Every cell of the tower of proper scope is a cell of the amalgam**, with its graded index:
below a pair of proper scope, the cells of the tower are the cells of the amalgam below it. -/
theorem exists_towerAmalgamEmb_eq_of_mem_below {X : Finset (Fin (m + 2)) × ℕ} (hX : X.1 ≠ univ)
    {z : Fin (I.ladderTower H Γ A B' m).S.card}
    (hz : z ∈ (I.ladderTower H Γ A B' m).S.toCellScheme.below X) :
    ∃ a, I.towerAmalgamEmb H Γ A B' a = z := by
  have hscope : (I.ladderTower H Γ A B' m).S.toCellScheme.scope z ≠ univ := fun he ↦
    hX (univ_subset_iff.mp (he ▸ (hz.1 : _ ⊆ X.1)))
  obtain ⟨a, ha⟩ := I.mem_range_towerAmalgamEmb H Γ A B' z hscope
  exact ⟨a, ha⟩

/-- A cell of the amalgam lies below a pair in the tower exactly when it does in the amalgam. -/
theorem towerAmalgamEmb_mem_below_iff (a : Fin I.amalgam.card) (X : Finset (Fin (m + 2)) × ℕ) :
    I.towerAmalgamEmb H Γ A B' a ∈ (I.ladderTower H Γ A B' m).S.toCellScheme.below X ↔
      a ∈ I.amalgam.toCellScheme.below X := by
  have hg := (I.isLowerEmbedding_towerAmalgamEmb H Γ A B').gradedIndex_eq_of_scope_eq
    (I.scope_towerAmalgamEmb H Γ A B') a
  change (I.ladderTower H Γ A B' m).S.toCellScheme.gradedIndex _ ≤ X ↔
    I.amalgam.toCellScheme.gradedIndex a ≤ X
  rw [hg]

/-! ### The two statements and the reduction -/

variable (I H Γ A B') in
/-- **The state lift from the context coatom at the grade `j`**: for a cap `c` self-visible at
`j`, an ambient `q` lawful below `(univ, j)` and a prescription `p` lawful below the context coatom
at `j` with the same observation at `c`, some complete lawful state of the amalgam satisfying
`A (m + 2)` reads `p` on the cells of the context coatom below the grade and has the observation of
`q` at `c` on the cells of the amalgam below the grade. -/
def ContextStateLift (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ (p : (I.ladderTower H Γ A B' m).S.toCellScheme.below (ctxCoatom m, j) → Label.{u})
      (q : (I.ladderTower H Γ A B' m).S.toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
      (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow (ctxCoatom m, j) p →
      (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
      (∀ d, min (q (Set.inclusion (CellScheme.below_mono _ (ctxCoatom_le j)) d)) c =
        min (p d) c) →
      ∃ P : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful P ∧ A (m + 2) P ∧
        (∀ (d : (I.ladderTower H Γ A B' m).S.toCellScheme.below (ctxCoatom m, j)) a,
          I.towerAmalgamEmb H Γ A B' a = d.1 → P a = p d) ∧
        ∀ (d : (I.ladderTower H Γ A B' m).S.toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
          I.towerAmalgamEmb H Γ A B' a = d.1 → min (P a) c = min (q d) c

variable (I H Γ A B') in
/-- **The coding of states at the grade `j`**: every complete lawful state `P` of the amalgam
satisfying `A (m + 2)` with the observation at a cap `c` of an ambient `q` lawful below
`(univ, j)` on the cells of the amalgam below the grade is the decoded reading, on those cells, of
a state `R` of the catalogue by a witness `ν` bounded by `j`, which sends no non-bottom label to
bottom when the cap is `⊥`; and the decoded writing of `R` has the observation of `q` at `c` at
every cell below `(univ, j)`.  At a positive cap the witness may send positive labels to bottom
(the writing of a state is positive at the first rung of its table, where the ambient may be
`⊥`); lawfulness then comes from the ambient as lawful companion. -/
def StateCoding (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ (q : (I.ladderTower H Γ A B' m).S.toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j) → Label.{u}),
      (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q →
      ∀ P : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful P → A (m + 2) P →
      (∀ (d : (I.ladderTower H Γ A B' m).S.toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j)) a,
        I.towerAmalgamEmb H Γ A B' a = d.1 → min (P a) c = min (q d) c) →
      ∃ R ∈ I.towerCat Γ A (m + 2), ∃ ν : Label.{u} → Label.{u},
        IsWitness (stepSuppressor j) ν ∧ (c ≠ ⊥ ∨ ∀ x, ν x = ⊥ → x = ⊥) ∧
        (∀ a, I.amalgam.toCellScheme.grade a ≤ j → ν (R a) = P a) ∧
        ∀ d : (I.ladderTower H Γ A B' m).S.toCellScheme.below
          ((univ : Finset (Fin (m + 2))), j),
          min (ν ((I.ladderTower H Γ A B' m).v R d)) c = min (q d) c

/-- **The lift from the context coatom from the state lift and the coding of states**: the decoded
writing of the coded state is lawful below `(univ, j)`, reads the prescription below the context
coatom, and keeps the observation of the ambient at the cap. -/
theorem cappedLift_context_of_stateLift (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j : ℕ}
    (hS : ContextStateLift I H Γ A B' j) (hC : StateCoding I H Γ A B' j) :
    (I.ladderTower H Γ A B' m).S.rows.CappedLift (X := (ctxCoatom m, j))
      (Y := ((univ : Finset (Fin (m + 2))), j)) (ctxCoatom_le j) := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨P, hPl, hPA, hPp, hPq⟩ := hS c hc p q hp hq hpq
  obtain ⟨R, hR, ν, hν, hbot, hνR, hνq⟩ := hC c hc q hq P hPl hPA hPq
  have hRl : I.amalgam.rows.IsLawful R := (mem_towerCat.mp hR).2.1
  have hlaw : (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ ν ((I.ladderTower H Γ A B' m).v R d) := by
    rcases hbot with hc0 | hbot
    · exact (((I.ladderTower_lawful hH hcard hΓ hA m).2 R hR).1.isLawfulBelow _).map_of_min_eq
        hq (fun d ↦ d.2.2) hν hc0 hνq
    · exact isLawfulBelow_map_writing hH hcard hΓ hA hR hν hbot
  refine ⟨fun d ↦ ν ((I.ladderTower H Γ A B' m).v R d), hlaw, hνq, fun d ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_towerAmalgamEmb_eq_of_mem_below (by simp [ctxCoatom]) d.2
  have hag : I.amalgam.toCellScheme.grade a ≤ j := by
    have h := (towerAmalgamEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a
      (ctxCoatom m, j)).mp (ha ▸ d.2)
    exact h.2
  change ν ((I.ladderTower H Γ A B' m).v R d.1) = p d
  rw [← ha, ladderTower_v_towerAmalgamEmb hcard hRl, hνR a hag]
  exact hPp d a ha

/-! ### The state lift below the predicate -/

/-- **The amalgam lift from the context coatom**: for a cap `c` self-visible at `j`, an ambient `q`
lawful below `(univ, j)` and a prescription `p` lawful below the context coatom at `j` with the same
observation at `c`, some complete lawful state of the amalgam vanishing above the grade reads `p`
on the cells of the context coatom below the grade and has the observation of `q` at `c` on the
cells of the amalgam below the grade.  The prescription and the ambient are read on the cells of
the amalgam (a lower embedding keeping scopes); the amalgam lifts capped from the context coatom
into `(univ, j)`; the lifted section, extended by `⊥` above the grade, is lawful. -/
theorem exists_amalgamLift {j : ℕ} (hj : 0 < j) (hjm : j ≤ m + 1) (c : Label.{u})
    (hc : IsSelfVisible j c)
    (p : (I.ladderTower H Γ A B' m).S.toCellScheme.below (ctxCoatom m, j) → Label.{u})
    (q : (I.ladderTower H Γ A B' m).S.toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u})
    (hp : (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow (ctxCoatom m, j) p)
    (hq : (I.ladderTower H Γ A B' m).S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _ (ctxCoatom_le j)) d)) c =
      min (p d) c) :
    ∃ P : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful P ∧
      (∀ a, j < I.amalgam.toCellScheme.grade a → P a = ⊥) ∧
      (∀ (d : (I.ladderTower H Γ A B' m).S.toCellScheme.below (ctxCoatom m, j)) a,
        I.towerAmalgamEmb H Γ A B' a = d.1 → P a = p d) ∧
      ∀ (d : (I.ladderTower H Γ A B' m).S.toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) a,
        I.towerAmalgamEmb H Γ A B' a = d.1 → min (P a) c = min (q d) c := by
  classical
  have hφ := I.isLowerEmbedding_towerAmalgamEmb H Γ A B'
  have hsc := I.scope_towerAmalgamEmb H Γ A B'
  have hrows := I.comap_rows_towerAmalgamEmb H Γ A B'
  -- the prescription and the ambient on the amalgam
  have hp' := Rows.IsLawfulBelow.comap_of_scope_eq hφ hsc hp
  have hq' := Rows.IsLawfulBelow.comap_of_scope_eq hφ hsc hq
  rw [hrows] at hp' hq'
  -- the lift in the amalgam
  have hleftF : ctxCoatom m ∈ I.amalgam.toCellScheme.faces := by
    change univ.erase (Fin.last (m + 1)) ∈ _
    rw [← Coatom.univ_map_left]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hXg : ((ctxCoatom m, j) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces :=
    ⟨hleftF, hj, by simp [ctxCoatom, card_erase_of_mem]; omega⟩
  have hYg : (((univ : Finset (Fin (m + 2))), j) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.amalgam.isWellFormed.univ_mem_faces, hj, by simp; omega⟩
  have hlift := I.isBountiful hXg hYg (ctxCoatom_le j)
  obtain ⟨P₁, hP₁, hP₁c, hP₁p⟩ := (Rows.cappedLift_iff_forall_exists _).mp hlift c hc _ _ hp' hq'
    (fun t ↦ hpq ⟨I.towerAmalgamEmb H Γ A B' t.1, hφ.mem_below_of_scope_eq hsc t.2⟩)
  -- the complete state
  let w : Fin I.amalgam.card → Label.{u} := fun a ↦
    if h : I.amalgam.toCellScheme.grade a ≤ j then P₁ ⟨a, ⟨subset_univ _, h⟩⟩ else ⊥
  have hw_of_le (a : Fin I.amalgam.card) (h : I.amalgam.toCellScheme.grade a ≤ j) :
      w a = P₁ ⟨a, ⟨subset_univ _, h⟩⟩ := by
    simp only [w, h, dite_true]
  have hw_of_lt (a : Fin I.amalgam.card) (h : j < I.amalgam.toCellScheme.grade a) :
      w a = ⊥ := by
    simp only [w, not_le.mpr h, dite_false]
  have hwY : (fun t : I.amalgam.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) ↦ w t) =
      P₁ := funext fun t ↦ hw_of_le t.1 t.2.2
  have hwl : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun t ↦ w t := by rw [hwY]; exact hP₁
  have hext := Rows.isLawfulBelow_extendAbove (K := m + 2) hwl
  have hext' : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m + 2)
      fun d ↦ w d := by
    refine (Rows.isLawfulBelow_congr (w := fun a ↦ if I.amalgam.toCellScheme.grade a ≤ j
      then w a else ⊥) fun a _ ↦ ?_).mp hext
    by_cases h : I.amalgam.toCellScheme.grade a ≤ j
    · exact ite_eq_left h
    · rw [ite_eq_right h, hw_of_lt a (not_le.mp h)]
  have hPl : I.amalgam.rows.IsLawful w := Rows.isLawful_of_isLawfulBelow
    (fun a ↦ ⟨subset_univ _, (I.amalgam.isWellFormed.isWellFormed.grade_le_card a).trans
      ((card_le_univ _).trans (by simp))⟩) hext'
  refine ⟨w, hPl, hw_of_lt, ?_, ?_⟩
  · intro d a ha
    have hab : a ∈ I.amalgam.toCellScheme.below (ctxCoatom m, j) :=
      (towerAmalgamEmb_mem_below_iff a _).mp (ha ▸ d.2)
    rw [hw_of_le a hab.2]
    refine (hP₁p ⟨a, hab⟩).trans ?_
    exact congrArg p (Subtype.ext ha)
  · intro d a ha
    have hab : a ∈ I.amalgam.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) :=
      (towerAmalgamEmb_mem_below_iff a _).mp (ha ▸ d.2)
    rw [hw_of_le a hab.2]
    refine (hP₁c ⟨a, hab⟩).trans ?_
    exact congrArg (fun z ↦ min (q z) c) (Subtype.ext ha)

/-- **The state lift from the bountifulness of the amalgam**, when the catalogue predicate
`A (m + 2)` holds for every lawful state vanishing above the grade `j`
(`Seed.exists_amalgamLift`). -/
theorem contextStateLift_of_vanishing {j : ℕ} (hj : 0 < j) (hjm : j ≤ m + 1)
    (hAj : ∀ P : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful P →
      (∀ a, j < I.amalgam.toCellScheme.grade a → P a = ⊥) → A (m + 2) P) :
    ContextStateLift I H Γ A B' j := by
  intro c hc p q hp hq hpq
  obtain ⟨P, hPl, hP0, hPp, hPq⟩ := exists_amalgamLift hj hjm c hc p q hp hq hpq
  exact ⟨P, hPl, hAj P hPl hP0, hPp, hPq⟩

end Seed

end VaughtConjecture

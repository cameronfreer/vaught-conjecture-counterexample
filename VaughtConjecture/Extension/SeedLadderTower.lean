/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderStates
import VaughtConjecture.Extension.LayerTower

/-!
# The ladder tower of a seed

Roadmap, Layer 3 ((R3) and (R4), the one-scope full layers of the recognizing growth carrier).

Over the padded grade-one base of a seed (`Seed.ladderBase`), the **ladder tower**
(`Seed.ladderTower`) is the tower of catalogue layers (`Scheme.layerTower`) writing complete states
by their extension to the base (`Seed.stateExt`): at the grade `k + 2` one cell of full scope per
state of the **catalogue** `Seed.towerCat I Γ A (k + 2)`, the lawful states of the amalgam with
values in a finite set `Γ` satisfying a predicate `A (k + 2)` (for instance admission on the exact
class from the threshold on), and agreement heights in the grid of the grade.  The row of the cell
of a state `R` is `R` on the amalgam, the positive table of `R` on the ladder (at the base indices
of its rank member), and agreement heights on the earlier layers.

* **Laws** (`Seed.isWellFormed_ladderTower`, `Seed.isConsistent_ladderTower`,
  `Seed.isCoded_ladderTower`, `Seed.exists_gradedIndex_ladderTower`, `Seed.grade_lt_ladderTower`):
  at the height `m`, the tower is well formed, consistent, coded (for `Γ` below `ω ^ 2`), complete
  below the full grade `m + 2` (for nonempty catalogues), and every cell has grade below `m + 2`.
  Every law of `Scheme.IsLegalBelowFullGrade` holds except bountifulness.
* **The controllers** (`Seed.exists_controller_ladderTower`): at every height `K ≥ k + 1`, every
  cell of full scope at the grade `k + 2` is the cell of a state `R` of the catalogue, whose row
  reads `R` at every cell of the amalgam of grade at most `k + 2` and the positive table of `R` at
  every ladder point (all of grade one). So every such cell is a **ladder controller by
  construction**: the rungs of the rank member of `R` are read as the table, the top rung dominates
  every value of `R`, and every positive value of `R` is a value of the table.

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (H : ℕ)

/-- The **base of the ladder tower**: the padded grade-one base, writing states by their
extension. -/
noncomputable def towerBase :
    Scheme.LayerTower.{u} (m + 2) (Fin I.amalgam.card → Label.{u}) 0 where
  S := I.ladderBase H
  v := I.stateExt H
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [Scheme.appendFullCellsScheme_scope_castAdd]
      exact .inr (I.scope_ne_univ d)
    | right j => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ j).le

open Classical in
/-- The **catalogue** of the ladder tower at the grade `k`: the lawful states of the amalgam with
values in `Γ` satisfying `A k`. -/
noncomputable def towerCat (Γ : Finset Label.{u})
    (A : ℕ → (Fin I.amalgam.card → Label.{u}) → Prop) (k : ℕ) :
    Finset (Fin I.amalgam.card → Label.{u}) :=
  (Fintype.piFinset fun _ ↦ Γ).filter fun R ↦ I.amalgam.rows.IsLawful R ∧ A k R

variable {I} in
theorem mem_towerCat {Γ : Finset Label.{u}} {A : ℕ → (Fin I.amalgam.card → Label.{u}) → Prop}
    {k : ℕ} {R : Fin I.amalgam.card → Label.{u}} :
    R ∈ I.towerCat Γ A k ↔ (∀ d, R d ∈ Γ) ∧ I.amalgam.rows.IsLawful R ∧ A k R := by
  classical
  simp only [towerCat, mem_filter, Fintype.mem_piFinset]

/-- **The ladder tower** of a seed, with values of the states in `Γ`, predicates `A`, and agreement
heights in the grids of block bound `B'`. -/
noncomputable abbrev ladderTower (Γ : Finset Label.{u})
    (A : ℕ → (Fin I.amalgam.card → Label.{u}) → Prop) (B' : ℕ) (k : ℕ) :
    Scheme.LayerTower.{u} (m + 2) (Fin I.amalgam.card → Label.{u}) k :=
  Scheme.layerTower (I.towerBase H) (I.towerCat Γ A) (fun k ↦ grid k B') k

/-! ### Values of the written states -/

variable {I H}

/-- The values of the extension of a lawful state are `⊥`, `1`, or values of the state. -/
theorem stateExt_eq {R : Fin I.amalgam.card → Label.{u}} (hR : I.amalgam.rows.IsLawful R)
    (hcard : I.amalgam.card ≤ H) (x : Fin (I.ladderBase H).card) :
    I.stateExt H R x = ⊥ ∨ I.stateExt H R x = 1 ∨ ∃ d, I.stateExt H R x = R d := by
  rw [stateExt_of_isLawful hR hcard]
  induction x using Fin.addCases with
  | left d => exact .inr (.inr ⟨d, Fin.append_left _ _ d⟩)
  | right j => rw [Fin.append_right]; exact posTable_eq _

theorem one_le_gridPoint_two (B' : ℕ) : (1 : Label.{u}) ≤ gridPoint 2 B' := by
  have h : (1 : Label.{u}) = gridPoint 1 0 := by simp [gridPoint]
  rw [h, gridPoint_le_gridPoint_iff_lex]
  omega

/-! ### Laws -/

variable {Γ : Finset Label.{u}} {A : ℕ → (Fin I.amalgam.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The ladder tower is well formed** up to the height `m`. -/
theorem isWellFormed_ladderTower {k : ℕ} (hk : k ≤ m + 1) :
    (I.ladderTower H Γ A B' k).S.IsWellFormed :=
  Scheme.isWellFormed_layerTower (I.isWellFormed_ladderBase H) k (by omega)

/-- The catalogues of the ladder tower decrease when the predicates do. -/
theorem towerCat_succ_subset (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    I.towerCat Γ A (k + 3) ⊆ I.towerCat Γ A (k + 2) := fun R hR ↦ by
  obtain ⟨h1, h2, h3⟩ := mem_towerCat.mp hR
  exact mem_towerCat.mpr ⟨h1, h2, hA k R h3⟩

/-- The base writes the states of the first catalogue lawfully, below the top of the grid at the
grade `2`. -/
theorem towerBase_lawful (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (R : Fin I.amalgam.card → Label.{u})
    (hR : R ∈ I.towerCat Γ A 2) :
    (I.towerBase H).S.rows.IsLawful ((I.towerBase H).v R) ∧
      ∀ x, (I.towerBase H).v R x ≤ gridPoint 2 B' := by
  obtain ⟨hRΓ, hRl, -⟩ := mem_towerCat.mp hR
  change (I.ladderBase H).rows.IsLawful (I.stateExt H R) ∧ ∀ x, I.stateExt H R x ≤ _
  refine ⟨isLawful_stateExt hRl hH hcard, fun x ↦ ?_⟩
  rcases stateExt_eq hRl hcard x with h | h | ⟨d, h⟩ <;> rw [h]
  · exact bot_le
  · exact one_le_gridPoint_two B'
  · exact hΓ _ (hRΓ d)

/-- The base writes the states of the first catalogue below `ω ^ 2`. -/
theorem towerBase_lt (hcard : I.amalgam.card ≤ H)
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (R : Fin I.amalgam.card → Label.{u}) (hR : R ∈ I.towerCat Γ A 2)
    (x : Fin (I.towerBase H).S.card) :
    (I.towerBase H).v R x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨hRΓ, hRl, -⟩ := mem_towerCat.mp hR
  change I.stateExt H R x < _
  rcases stateExt_eq hRl hcard x with h | h | ⟨d, h⟩ <;> rw [h]
  · exact WithBot.bot_lt_coe _
  · exact_mod_cast natCast_label_lt_omega0_sq 1
  · exact hΓω _ (hRΓ d)

/-- **The ladder tower is consistent, and writes every state of the next catalogue lawfully.** -/
theorem ladderTower_lawful (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    (I.ladderTower H Γ A B' k).S.rows.IsConsistent ∧ ∀ R ∈ I.towerCat Γ A (k + 2),
      (I.ladderTower H Γ A B' k).S.rows.IsLawful ((I.ladderTower H Γ A B' k).v R) ∧
        ∀ x, (I.ladderTower H Γ A B' k).v R x ≤ gridPoint (k + 2) B' := by
  have h := Scheme.layerTower_lawful (B := I.towerBase H) (C := I.towerCat Γ A)
    (G := fun k ↦ grid k B') (y := fun k ↦ gridPoint k B') (towerCat_succ_subset hA)
    (fun k ↦ bot_mem_grid _ _) (fun k _ hx ↦ isSelfVisible_of_mem_grid hx)
    (fun k ↦ gridPoint_mem_grid le_rfl) (fun k _ hx ↦ le_gridPoint_of_mem_grid hx)
    (fun k ↦ gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩))
    (I.isConsistent_ladderBase H hH) (towerBase_lawful hH hcard hΓ) k
  exact h

/-- **The ladder tower is coded** when `Γ` lies below `ω ^ 2`. -/
theorem isCoded_ladderTower (hcard : I.amalgam.card ≤ H)
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    (I.ladderTower H Γ A B' k).S.IsCoded := by
  have h := Scheme.isCoded_layerTower (B := I.towerBase H) (C := I.towerCat Γ A)
    (G := fun k ↦ grid k B') (towerCat_succ_subset hA) (fun k ↦ bot_mem_grid _ _)
    (fun k _ hx ↦ lt_omega0_sq_of_mem_grid hx) (I.isCoded_ladderBase H)
    (towerBase_lt hcard hΓω) k
  exact h.1

/-- **The ladder tower at the height `m` is complete below the full grade**, for nonempty
catalogues. -/
theorem exists_gradedIndex_ladderTower (hH : 0 < H) (hne : ∀ k, (I.towerCat Γ A (k + 2)).Nonempty)
    {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ (I.ladderTower H Γ A B' m).S.toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ d, (I.ladderTower H Γ A B' m).S.toCellScheme.gradedIndex d = X := by
  refine Scheme.exists_gradedIndex_layerTower (B := I.towerBase H) (G := fun k ↦ grid k B')
    (fun X hX hX1 ↦ ?_) hne m X hX (.inl (by omega))
  by_cases hXu : X.1 = univ
  · have hX1' : X.2 ≤ 1 := hX1.resolve_right (not_not.mpr hXu)
    have hX0 : 0 < X.2 := hX.2.1
    obtain ⟨a⟩ := (inferInstance : Nonempty (Scheme.RankMember I.amalgam.toScheme H))
    refine ⟨Fin.natAdd _ (Scheme.ladderEquiv _ _ H (a, Sum.inl ⟨0, hH⟩)), ?_⟩
    change (I.amalgam.toScheme.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = X
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact Prod.ext hXu.symm (by omega)
  · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq X hX hXu
    refine ⟨Fin.castAdd _ d, ?_⟩
    change (I.amalgam.toScheme.appendFullCellsScheme 1 _).gradedIndex (Fin.castAdd _ d) = X
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact hd

/-- **Every cell of the ladder tower at the height `m` has grade below the full grade.** -/
theorem grade_lt_ladderTower (d : Fin (I.ladderTower H Γ A B' m).S.card) :
    (I.ladderTower H Γ A B' m).S.toCellScheme.grade d < m + 2 := by
  rcases (I.ladderTower H Γ A B' m).inv d with h | h
  · omega
  · have hlt : #((I.ladderTower H Γ A B' m).S.toCellScheme.scope d) < m + 2 := by
      simpa using card_lt_card (ssubset_univ_iff.mpr h)
    exact ((I.isWellFormed_ladderTower (k := m) (by omega)).isWellFormed.grade_le_card d).trans_lt
      hlt

/-! ### The controllers -/

/-- The cells of the base in the ladder tower at the height `K`. -/
noncomputable abbrev towerEmb (K : ℕ) :
    Fin (I.ladderBase H).card → Fin (I.ladderTower H Γ A B' K).S.card :=
  Scheme.layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A) (G := fun k ↦ grid k B') K

/-- **Every cell of full scope of the ladder tower is a ladder controller by construction**: at
every height `K ≥ k + 1`, a cell of full scope at the grade `k + 2` is the cell of a state `R` of
the catalogue at `k + 2` whose row reads `R` at every cell of the amalgam of grade at most `k + 2`
and the positive table of `R`, at the base indices of its rank member, at every ladder point. -/
theorem exists_controller_ladderTower (hcard : I.amalgam.card ≤ H) (k K : ℕ) (hK : k + 1 ≤ K)
    (u : Fin (I.ladderTower H Γ A B' K).S.card)
    (hu : (I.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), k + 2)) :
    ∃ R ∈ I.towerCat Γ A (k + 2), ∃ hR : I.amalgam.rows.IsLawful R,
      (∀ d : Fin I.amalgam.card, I.amalgam.toCellScheme.grade d ≤ k + 2 →
        (I.ladderTower H Γ A B' K).S.rowAt u (I.towerEmb K (Fin.castAdd _ d)) = R d) ∧
      ∀ p, (I.ladderTower H Γ A B' K).S.rowAt u
          (I.towerEmb K (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))) =
        posTable R (Scheme.baseIndex H (Scheme.rankProf I.amalgam.toScheme H)
          (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR)
          (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))) := by
  obtain ⟨R, hRC, hrow⟩ := Scheme.exists_layerTower_controller (B := I.towerBase H)
    (C := I.towerCat Γ A) (G := fun k ↦ grid k B') k K hK u hu
  have hRl := (mem_towerCat.mp hRC).2.1
  refine ⟨R, hRC, hRl, fun d hd ↦ ?_, fun p ↦ ?_⟩
  · have h := hrow (Fin.castAdd _ d) (by
      change (I.amalgam.toScheme.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k + 2
      rw [Scheme.appendFullCellsScheme_grade_castAdd]; exact hd)
    exact h.trans (stateExt_castAdd hRl hcard d)
  · have h := hrow (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p)) (by
      change (I.amalgam.toScheme.appendFullCellsScheme 1 _).grade (Fin.natAdd _ _) ≤ k + 2
      rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega)
    exact h.trans
      (stateExt_of_grade_one hRl hcard _ (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ _))

/-- **The ladder-controller clauses** for the cell of a state `R`: its rungs are read as the
positive table, the top rung at least every value of `R`, and every positive value of `R` is a
value of the table at a rung. -/
theorem ladderController_clauses (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    {R : Fin I.amalgam.card → Label.{u}} (hR : I.amalgam.rows.IsLawful R) :
    (∀ i (hi : i < H), Scheme.baseIndex H (Scheme.rankProf I.amalgam.toScheme H)
        (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR)
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H
          (Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR, Sum.inl ⟨i, hi⟩))) =
        i + 1) ∧
      (∀ d, R d ≤ posTable R H) ∧
      ∀ d, R d ≠ ⊥ → ∃ i < H, R d = posTable R (i + 1) := by
  have hv := I.isSelfVisible_one_of_isLawful hR
  have hrk (d : Fin I.amalgam.card) : rankVector R d ≤ H :=
    (rankVector_le d).trans (by simpa using hcard)
  refine ⟨fun i hi ↦ ?_, fun d ↦ le_posTable hv (hrk d), fun d hd ↦ ?_⟩
  · have h := Scheme.baseIndex_self (Scheme.rankProf_le _ H)
      ((Scheme.RankMember.ofLawful I.amalgam.isWellFormed hcard hR, Sum.inl ⟨i, hi⟩) :
        Scheme.LadderPt I.amalgam.toScheme (Scheme.RankMember I.amalgam.toScheme H) H)
    simpa [Scheme.ladderCeil] using h
  · have h0 : rankVector R d ≠ 0 := fun h ↦ hd ((rankVector_eq_zero_iff d).mp h)
    refine ⟨rankVector R d - 1, by have := hrk d; omega, ?_⟩
    rw [show rankVector R d - 1 + 1 = rankVector R d by omega, posTable_rankVector hv]

end Seed

end VaughtConjecture

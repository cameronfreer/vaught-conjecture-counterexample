/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderGlue
import VaughtConjecture.Extension.LadderStates
import VaughtConjecture.Extension.LayerTower

/-!
# The ladder tower over any base scheme

Roadmap, Layer 3 ((R3) and (R4), the one-scope full layers of the recognizing growth carrier).

The ladder tower of `VaughtConjecture.Extension.SeedLadderTower`, over any **ladder base data**
(`Scheme.LadderBaseData`: a scheme with no cell of full scope at grade one or above, well formed,
consistent and coded) in place of the amalgam of a seed.  The intended base is the attachment of a
donor to a context (`Seed.attachmentType`), whose mixed faces carry no cell (the copies of the
cells of full scope are installed there afterwards).

* `Scheme.LadderBaseData.stateExt`, `isLawful_stateExt`: the extension of a lawful state to the
  padded grade-one base by its positive table on the ladder.
* `towerBase`, `towerCat`, `ladderTower`; `isWellFormed_ladderTower`, `ladderTower_lawful`,
  `isCoded_ladderTower`, `exists_gradedIndex_ladderTower` (completeness at the full faces and at
  the faces the base completes), `grade_lt_ladderTower`.
* `exists_controller_ladderTower`, `ladderController_clauses`: every cell of full scope at a grade
  `k + 2` reads a catalogue state on the base cells and its positive table on the ladder.

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

/-- **Ladder base data**: a scheme with no cell of full scope at grade one or above, well formed,
consistent and coded. -/
structure LadderBaseData (n : ℕ) where
  /-- The base scheme. -/
  S : Scheme.{u} n
  /-- No cell of full scope at grade one or above. -/
  noFull : S.NoFullOne
  /-- Well formed. -/
  wf : S.IsWellFormed
  /-- Consistent rows. -/
  cons : S.rows.IsConsistent
  /-- Coded rows. -/
  coded : S.IsCoded

namespace LadderBaseData

variable {n : ℕ} (B : LadderBaseData.{u} n) (H : ℕ)

/-- The padded grade-one base over the rank members. -/
noncomputable abbrev ladderBase : Scheme.{u} n :=
  Scheme.ladderBase H (rankProf B.S H) B.noFull

theorem scope_ne_univ (d : Fin B.S.card) : B.S.toCellScheme.scope d ≠ univ := fun h ↦
  B.noFull d ⟨h ▸ subset_rfl, B.wf.isWellFormed.grade_pos d⟩

theorem isWellFormed_ladderBase (hn : 1 ≤ n) : (B.ladderBase H).IsWellFormed :=
  Scheme.isWellFormed_ladderBase B.wf hn

theorem isConsistent_ladderBase (hH : 0 < H) : (B.ladderBase H).rows.IsConsistent :=
  isConsistent_ladderBase_rankMember B.wf B.cons hH

theorem isCoded_ladderBase : (B.ladderBase H).IsCoded :=
  Scheme.isCoded_ladderBase B.coded



/-- The values of a lawful state are self-visible at `1`. -/
theorem isSelfVisible_one_of_isLawful {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (d : Fin B.S.card) : IsSelfVisible 1 (R d) :=
  (hR.orderly d).mono (B.wf.isWellFormed.grade_pos d)

open Classical in
/-- **The extension of a state to the base**: `R` on the cells of the base, and on the ladder
the positive table of `R` at the base indices of its rank member; `⊥` for a state that is not
lawful or a height below the number of cells. -/
noncomputable def stateExt (R : Fin B.S.card → Label.{u}) :
    Fin (B.ladderBase H).card → Label.{u} :=
  if h : B.S.rows.IsLawful R ∧ B.S.card ≤ H then
    Fin.append R fun j ↦ posTable R (baseIndex H (rankProf B.S H)
      (RankMember.ofLawful B.wf h.2 h.1) (Fin.natAdd _ j))
  else fun _ ↦ ⊥

variable {B H}

theorem stateExt_of_isLawful {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (hcard : B.S.card ≤ H) :
    B.stateExt H R = Fin.append R fun j ↦ posTable R (baseIndex H
      (rankProf B.S H)
        (RankMember.ofLawful B.wf hcard hR) (Fin.natAdd _ j)) := by
  unfold stateExt
  rw [dite_eq_left ⟨hR, hcard⟩]

/-- **The extension reads the state on the base.** -/
theorem stateExt_castAdd {R : Fin B.S.card → Label.{u}} (hR : B.S.rows.IsLawful R)
    (hcard : B.S.card ≤ H) (d : Fin B.S.card) :
    B.stateExt H R (Fin.castAdd _ d) = R d := by
  rw [stateExt_of_isLawful hR hcard, Fin.append_left]

/-- **At grade one the extension reads the positive table of the state at the base indices of
its rank member.** -/
theorem stateExt_of_grade_one {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (hcard : B.S.card ≤ H)
    (t : Fin (B.ladderBase H).card)
    (ht : (B.S.appendFullCellsScheme 1
      (ladderCard B.S (RankMember B.S H) H)).grade t
        = 1) :
    B.stateExt H R t = posTable R (baseIndex H (rankProf B.S H)
      (RankMember.ofLawful B.wf hcard hR) t) := by
  rw [stateExt_of_isLawful hR hcard]
  induction t using Fin.addCases with
  | left d =>
    rw [Fin.append_left, baseIndex_castAdd, rankProf_ofLawful,
      posTable_rankVector (B.isSelfVisible_one_of_isLawful hR)]
  | right j => rw [Fin.append_right]

/-- **The extension of a lawful state is a lawful section of the base.** -/
theorem isLawful_stateExt {R : Fin B.S.card → Label.{u}} (hR : B.S.rows.IsLawful R)
    (hH : 0 < H) (hcard : B.S.card ≤ H) : (B.ladderBase H).rows.IsLawful (B.stateExt H R) :=
  isLawful_ladderExtend B.wf hH (rankProf_le _ H)
    (RankMember.ofLawful B.wf hcard hR) monotone_posTable posTable_zero
    (isSelfVisible_posTable (B.isSelfVisible_one_of_isLawful hR))
    (fun _ hi _ ↦ posTable_ne_bot (by omega))
    (by
      convert hR using 1
      funext d
      exact stateExt_castAdd hR hcard d)
    (stateExt_of_grade_one hR hcard)



variable {n : ℕ} (B : LadderBaseData.{u} n) (H : ℕ)

/-- The **base of the ladder tower**: the padded grade-one base, writing states by their
extension. -/
noncomputable def towerBase :
    LayerTower.{u} n (Fin B.S.card → Label.{u}) 0 where
  S := B.ladderBase H
  v := B.stateExt H
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [appendFullCellsScheme_scope_castAdd]
      exact .inr (B.scope_ne_univ d)
    | right j => exact .inl (appendFullCellsScheme_grade_natAdd _ _ _ j).le

open Classical in
/-- The **catalogue** of the ladder tower at the grade `k`: the lawful states of the base with
values in `Γ` satisfying `A k`. -/
noncomputable def towerCat (Γ : Finset Label.{u})
    (A : ℕ → (Fin B.S.card → Label.{u}) → Prop) (k : ℕ) :
    Finset (Fin B.S.card → Label.{u}) :=
  (Fintype.piFinset fun _ ↦ Γ).filter fun R ↦ B.S.rows.IsLawful R ∧ A k R

variable {B} in
theorem mem_towerCat {Γ : Finset Label.{u}} {A : ℕ → (Fin B.S.card → Label.{u}) → Prop}
    {k : ℕ} {R : Fin B.S.card → Label.{u}} :
    R ∈ B.towerCat Γ A k ↔ (∀ d, R d ∈ Γ) ∧ B.S.rows.IsLawful R ∧ A k R := by
  classical
  simp only [towerCat, mem_filter, Fintype.mem_piFinset]

/-- **The ladder tower** , with values of the states in `Γ`, predicates `A`, and agreement
heights in the grids of block bound `B'`. -/
noncomputable abbrev ladderTower (Γ : Finset Label.{u})
    (A : ℕ → (Fin B.S.card → Label.{u}) → Prop) (B' : ℕ) (k : ℕ) :
    LayerTower.{u} n (Fin B.S.card → Label.{u}) k :=
  layerTower (B.towerBase H) (B.towerCat Γ A) (fun k ↦ grid k B') k

/-! ### Values of the written states -/

variable {B H}

/-- The values of the extension of a lawful state are `⊥`, `1`, or values of the state. -/
theorem stateExt_eq {R : Fin B.S.card → Label.{u}} (hR : B.S.rows.IsLawful R)
    (hcard : B.S.card ≤ H) (x : Fin (B.ladderBase H).card) :
    B.stateExt H R x = ⊥ ∨ B.stateExt H R x = 1 ∨ ∃ d, B.stateExt H R x = R d := by
  rw [stateExt_of_isLawful hR hcard]
  induction x using Fin.addCases with
  | left d => exact .inr (.inr ⟨d, Fin.append_left _ _ d⟩)
  | right j => rw [Fin.append_right]; exact posTable_eq _

theorem one_le_gridPoint_two (B' : ℕ) : (1 : Label.{u}) ≤ gridPoint 2 B' := by
  have h : (1 : Label.{u}) = gridPoint 1 0 := by simp [gridPoint]
  rw [h, gridPoint_le_gridPoint_iff_lex]
  omega

/-! ### Laws -/

variable {Γ : Finset Label.{u}} {A : ℕ → (Fin B.S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The ladder tower is well formed** up to the height `m`. -/
theorem isWellFormed_ladderTower {k : ℕ} (hk : k + 1 ≤ n) :
    (B.ladderTower H Γ A B' k).S.IsWellFormed :=
  isWellFormed_layerTower (B.isWellFormed_ladderBase H (by omega)) k hk

/-- The catalogues of the ladder tower decrease when the predicates do. -/
theorem towerCat_succ_subset (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    B.towerCat Γ A (k + 3) ⊆ B.towerCat Γ A (k + 2) := fun R hR ↦ by
  obtain ⟨h1, h2, h3⟩ := mem_towerCat.mp hR
  exact mem_towerCat.mpr ⟨h1, h2, hA k R h3⟩

/-- The base writes the states of the first catalogue lawfully, below the top of the grid at the
grade `2`. -/
theorem towerBase_lawful (hH : 0 < H) (hcard : B.S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (R : Fin B.S.card → Label.{u})
    (hR : R ∈ B.towerCat Γ A 2) :
    (B.towerBase H).S.rows.IsLawful ((B.towerBase H).v R) ∧
      ∀ x, (B.towerBase H).v R x ≤ gridPoint 2 B' := by
  obtain ⟨hRΓ, hRl, -⟩ := mem_towerCat.mp hR
  change (B.ladderBase H).rows.IsLawful (B.stateExt H R) ∧ ∀ x, B.stateExt H R x ≤ _
  refine ⟨isLawful_stateExt hRl hH hcard, fun x ↦ ?_⟩
  rcases stateExt_eq hRl hcard x with h | h | ⟨d, h⟩ <;> rw [h]
  · exact bot_le
  · exact one_le_gridPoint_two B'
  · exact hΓ _ (hRΓ d)

/-- The base writes the states of the first catalogue below `ω ^ 2`. -/
theorem towerBase_lt (hcard : B.S.card ≤ H)
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (R : Fin B.S.card → Label.{u}) (hR : R ∈ B.towerCat Γ A 2)
    (x : Fin (B.towerBase H).S.card) :
    (B.towerBase H).v R x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨hRΓ, hRl, -⟩ := mem_towerCat.mp hR
  change B.stateExt H R x < _
  rcases stateExt_eq hRl hcard x with h | h | ⟨d, h⟩ <;> rw [h]
  · exact WithBot.bot_lt_coe _
  · exact_mod_cast natCast_label_lt_omega0_sq 1
  · exact hΓω _ (hRΓ d)

/-- **The ladder tower is consistent, and writes every state of the next catalogue lawfully.** -/
theorem ladderTower_lawful (hH : 0 < H) (hcard : B.S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    (B.ladderTower H Γ A B' k).S.rows.IsConsistent ∧ ∀ R ∈ B.towerCat Γ A (k + 2),
      (B.ladderTower H Γ A B' k).S.rows.IsLawful ((B.ladderTower H Γ A B' k).v R) ∧
        ∀ x, (B.ladderTower H Γ A B' k).v R x ≤ gridPoint (k + 2) B' := by
  have h := layerTower_lawful (B := B.towerBase H) (C := B.towerCat Γ A)
    (G := fun k ↦ grid k B') (y := fun k ↦ gridPoint k B') (towerCat_succ_subset hA)
    (fun k ↦ bot_mem_grid _ _) (fun k _ hx ↦ isSelfVisible_of_mem_grid hx)
    (fun k ↦ gridPoint_mem_grid le_rfl) (fun k _ hx ↦ le_gridPoint_of_mem_grid hx)
    (fun k ↦ gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩))
    (B.isConsistent_ladderBase H hH) (towerBase_lawful hH hcard hΓ) k
  exact h

/-- **The ladder tower is coded** when `Γ` lies below `ω ^ 2`. -/
theorem isCoded_ladderTower (hcard : B.S.card ≤ H)
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    (B.ladderTower H Γ A B' k).S.IsCoded := by
  have h := isCoded_layerTower (B := B.towerBase H) (C := B.towerCat Γ A)
    (G := fun k ↦ grid k B') (towerCat_succ_subset hA) (fun k ↦ bot_mem_grid _ _)
    (fun k _ hx ↦ lt_omega0_sq_of_mem_grid hx) (B.isCoded_ladderBase H)
    (towerBase_lt hcard hΓω) k
  exact h.1

/-- **Completeness of the ladder tower** at the height `K`, for nonempty catalogues: every graded
face of full scope at a grade at most `K + 1`, and every graded face of proper scope that the base
completes, is the graded index of a cell. -/
theorem exists_gradedIndex_ladderTower (hH : 0 < H) (hne : ∀ k, (B.towerCat Γ A (k + 2)).Nonempty)
    (hBcomp : ∀ X ∈ B.S.toCellScheme.gradedFaces, X.1 ≠ univ →
      ∃ d, B.S.toCellScheme.gradedIndex d = X)
    (K : ℕ) {X : Finset (Fin n) × ℕ}
    (hX : X ∈ (B.ladderTower H Γ A B' K).S.toCellScheme.gradedFaces) (hX2 : X.2 ≤ K + 1) :
    ∃ d, (B.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex d = X := by
  refine exists_gradedIndex_layerTower (B := B.towerBase H) (G := fun k ↦ grid k B')
    (fun X hX hX1 ↦ ?_) hne K X hX (.inl hX2)
  by_cases hXu : X.1 = univ
  · have hX1' : X.2 ≤ 1 := hX1.resolve_right (not_not.mpr hXu)
    have hX0 : 0 < X.2 := hX.2.1
    obtain ⟨a⟩ := (inferInstance : Nonempty (RankMember B.S H))
    refine ⟨Fin.natAdd _ (ladderEquiv _ _ H (a, Sum.inl ⟨0, hH⟩)), ?_⟩
    change (B.S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = X
    rw [appendFullCellsScheme_gradedIndex_natAdd]
    exact Prod.ext hXu.symm (by omega)
  · obtain ⟨d, hd⟩ := hBcomp X hX hXu
    refine ⟨Fin.castAdd _ d, ?_⟩
    change (B.S.appendFullCellsScheme 1 _).gradedIndex (Fin.castAdd _ d) = X
    rw [appendFullCellsScheme_gradedIndex_castAdd]
    exact hd

/-- **Every cell of the ladder tower at a height `K` with `K + 1 < n` has grade below `n`.** -/
theorem grade_lt_ladderTower {K : ℕ} (hK : K + 1 < n) (d : Fin (B.ladderTower H Γ A B' K).S.card) :
    (B.ladderTower H Γ A B' K).S.toCellScheme.grade d < n := by
  rcases (B.ladderTower H Γ A B' K).inv d with h | h
  · omega
  · have hlt : #((B.ladderTower H Γ A B' K).S.toCellScheme.scope d) < n := by
      simpa using card_lt_card (ssubset_univ_iff.mpr h)
    exact ((B.isWellFormed_ladderTower (k := K) (by omega)).isWellFormed.grade_le_card d).trans_lt
      hlt

/-! ### The controllers -/

/-- The cells of the base in the ladder tower at the height `K`. -/
noncomputable abbrev towerEmb (K : ℕ) :
    Fin (B.ladderBase H).card → Fin (B.ladderTower H Γ A B' K).S.card :=
  layerTowerEmb (B := B.towerBase H) (C := B.towerCat Γ A) (G := fun k ↦ grid k B') K

/-- **Every cell of full scope of the ladder tower is a ladder controller by construction**: at
every height `K ≥ k + 1`, a cell of full scope at the grade `k + 2` is the cell of a state `R` of
the catalogue at `k + 2` whose row reads `R` at every cell of the base of grade at most `k + 2`
and the positive table of `R`, at the base indices of its rank member, at every ladder point. -/
theorem exists_controller_ladderTower (hcard : B.S.card ≤ H) (k K : ℕ) (hK : k + 1 ≤ K)
    (u : Fin (B.ladderTower H Γ A B' K).S.card)
    (hu : (B.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex u =
      ((univ : Finset (Fin n)), k + 2)) :
    ∃ R ∈ B.towerCat Γ A (k + 2), ∃ hR : B.S.rows.IsLawful R,
      (∀ d : Fin B.S.card, B.S.toCellScheme.grade d ≤ k + 2 →
        (B.ladderTower H Γ A B' K).S.rowAt u (B.towerEmb K (Fin.castAdd _ d)) = R d) ∧
      ∀ p, (B.ladderTower H Γ A B' K).S.rowAt u
          (B.towerEmb K (Fin.natAdd _ (ladderEquiv _ _ H p))) =
        posTable R (baseIndex H (rankProf B.S H)
          (RankMember.ofLawful B.wf hcard hR)
          (Fin.natAdd _ (ladderEquiv _ _ H p))) := by
  obtain ⟨R, hRC, hrow⟩ := exists_layerTower_controller (B := B.towerBase H)
    (C := B.towerCat Γ A) (G := fun k ↦ grid k B') k K hK u hu
  have hRl := (mem_towerCat.mp hRC).2.1
  refine ⟨R, hRC, hRl, fun d hd ↦ ?_, fun p ↦ ?_⟩
  · have h := hrow (Fin.castAdd _ d) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k + 2
      rw [appendFullCellsScheme_grade_castAdd]; exact hd)
    exact h.trans (stateExt_castAdd hRl hcard d)
  · have h := hrow (Fin.natAdd _ (ladderEquiv _ _ H p)) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.natAdd _ _) ≤ k + 2
      rw [appendFullCellsScheme_grade_natAdd]; omega)
    exact h.trans
      (stateExt_of_grade_one hRl hcard _ (appendFullCellsScheme_grade_natAdd _ _ _ _))

/-- **The ladder-controller clauses** for the cell of a state `R`: its rungs are read as the
positive table, the top rung at least every value of `R`, and every positive value of `R` is a
value of the table at a rung. -/
theorem ladderController_clauses (hH : 0 < H) (hcard : B.S.card ≤ H)
    {R : Fin B.S.card → Label.{u}} (hR : B.S.rows.IsLawful R) :
    (∀ i (hi : i < H), baseIndex H (rankProf B.S H)
        (RankMember.ofLawful B.wf hcard hR)
        (Fin.natAdd _ (ladderEquiv _ _ H
          (RankMember.ofLawful B.wf hcard hR, Sum.inl ⟨i, hi⟩))) =
        i + 1) ∧
      (∀ d, R d ≤ posTable R H) ∧
      ∀ d, R d ≠ ⊥ → ∃ i < H, R d = posTable R (i + 1) := by
  have hv := B.isSelfVisible_one_of_isLawful hR
  have hrk (d : Fin B.S.card) : rankVector R d ≤ H :=
    (rankVector_le d).trans (by simpa using hcard)
  refine ⟨fun i hi ↦ ?_, fun d ↦ le_posTable hv (hrk d), fun d hd ↦ ?_⟩
  · have h := baseIndex_self (rankProf_le _ H)
      ((RankMember.ofLawful B.wf hcard hR, Sum.inl ⟨i, hi⟩) :
        LadderPt B.S (RankMember B.S H) H)
    simpa [ladderCeil] using h
  · have h0 : rankVector R d ≠ 0 := fun h ↦ hd ((rankVector_eq_zero_iff d).mp h)
    refine ⟨rankVector R d - 1, by have := hrk d; omega, ?_⟩
    rw [show rankVector R d - 1 + 1 = rankVector R d by omega, posTable_rankVector hv]

end LadderBaseData

end VaughtConjecture.Scheme

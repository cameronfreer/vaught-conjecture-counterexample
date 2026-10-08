/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.RankProfileScheme
import VaughtConjecture.Extension.TowerSection

/-!
# Selected sections through the tower at the grade two, read by a layer of profiles

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the interface between the lower layers of the tower and a grade-`3` layer of rank-normalized
profiles).

Let `I` be a seed on five points and `T 2 = I.tower 2` the tower of field layers up to the grade `2`
(module `VaughtConjecture.Extension.Tower`).  A grade-`3` layer of profiles over `T 2` gives the
cell of a profile `P` of `RankProfile.rankCat I 3` a row reading the old cells by `P` and the new
cells of `T 2` by a labelling chosen for `P`.  A **section operator** (`SectionOp`) is one function
`σ` from profiles to labellings of the cells of `T 2`, fixed before any prescription, cap or ambient
labelling.  The clauses asked of it, for the profiles of the catalogue:

* (i) **lawful** (`SectionOp.IsLawful`): `σ P` is lawful below `(univ, 2)` in `T 2`;
* (ii) **short** (`SectionOp.IsShort`): every value of `σ P` is short at `3` and not the formal top,
  as the rows of the cells at `(univ, 3)` must be for the one-grade lift;
* (iii) **literal** (`SectionOp.IsLiteral`): `σ P` reads every old cell by `P`;
* (iv) **capped agreement at a cap `h`** (`SectionOp.IsCapAgreeingAt`): profiles `P`, `Q` of the
  catalogue that agree capped at `h` at every old cell have sections that agree capped at `h` at
  every cell of `T 2`.

**The cap class.**  The one-grade lift `CellScheme.Rows.cappedLift_of_boundaries_short` uses the
extension from the boundary at the caps self-visible and short at `3`, and the consistency of the
rows of a grade-`3` layer of profiles uses (iv) at agreement heights in `Label.grid 3`, which are
self-visible and short at `3`.  So (iv) is needed at the caps self-visible and short at `3`.

**The interface theorem** (`exists_sectionOp`; compiled in this repository, for every seed on five
points).  The tower section operator `towerSectionOp`, the tower section at the grade `2`
(`Seed.towerSection`, module `VaughtConjecture.Extension.TowerSection`) read by the upper decoder
(`Label.upperDecoderAt` at the cap grade `3`, module `VaughtConjecture.Extension.UpperDecoderAt`),
satisfies (i) (`towerSectionOp_isLawful`), (ii) (`towerSectionOp_isShort`: its values lie in
`Label.codeGrid 3 (2 N + 2)`), (iii) (`towerSectionOp_isLiteral`), and (iv) at every cap
self-visible and short at `3` (`towerSectionOp_isCapAgreeingAt`).  It is one function of the
profile; its only hypothesis is the seed.  The orbit decoder of the tower's own extension at `⊥`
reads an agreement height between the codes of two keys as the lower key, which breaks (iv) at a cap
`ω * γ + 3` that is not short at the grade of the layer; the upper decoder reads it as the largest
label of the code grid self-visible at `3` and at most the next value.

**(iv) at every cap short at `3` fails** (`not_isCapAgreeingAt_of_collision`,
`not_isCapAgreeingAt_one`, `not_isCapAgreeingAt_one_seedL`, `not_forall_isCapAgreeingAt_of_isShort`;
refuted, negative special case named).  For every seed whose coatom types are `TL` and `T5` (`seedL`
among them), and every section operator that is lawful and literal at the profiles of the catalogue,
(iv) fails at the cap `1`, which is short at `3` (`isShort_three_one`) and not self-visible at `3`
(`not_isSelfVisible_three_one`).  The two profiles are the profiles of five parameters
(`ProfileCatalogue.tripleProfile`) `P₁ = (1, 2, 1, 2, ⊥)` and `Q₁ = (1, 2, 2, 2, ⊥)`; they lie in
the catalogue (`tripleProfile_mem_rankCat`, all their values lie in the natural strip below `3`,
which the orbit code keeps) and agree capped at `1`.  The argument: availability for `σ Q₁` from the
cell at `({0, 1, 2, 3}, 2)`, labelled `2`, gives a cell `u` at `(univ, 2)` with `σ Q₁ u ≥ 2`;
locality at `u` with `Q₁ ({3}, 1) = 1 < 2 = Q₁ ({4}, 1)` makes the row of `u` read `({3}, 1)`
strictly below `({4}, 1)`; capped agreement at `1` gives `σ P₁ u ≥ 1`, hence `σ P₁ u > 1`, the label
`1` not being self-visible at the grade `2` of `u`; and then `σ P₁` has a collision at `u`
(`Label.eq_of_transformsTo_collision`): the label `1`, not self-visible at `2`, at both cells, below
the label at `u`, which forces the row of `u` to read them alike.  The general form
(`not_isCapAgreeingAt_of_collision`) holds for every seed on five points and every pair of profiles
with such a collision.

So the cap class of (iv) cannot be widened to the caps short at `3`; this refutes that widened
statement, not (iv) at the caps self-visible and short at `3`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`, Layer 3,
3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.SectionInterface

open Finset Label CellScheme
open ProfileCatalogue (Profile IsCutLawful)
open RankProfile (rankCat mem_rankCat)

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- A **section operator**: one labelling of the cells of `T 2` for each profile. -/
abbrev SectionOp := Profile I → Fin (I.tower 2).card → Label.{u}

namespace SectionOp

variable {I}

/-- (i) **Lawful**: the section of every profile of the catalogue at the grade `3` is lawful below
`(univ, 2)` in `T 2`. -/
def IsLawful (σ : SectionOp I) : Prop :=
  ∀ P ∈ rankCat I 3, (I.tower 2).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 2) fun t ↦ σ P t

/-- (ii) **Short**: every value of the section of a profile of the catalogue is short at `3` and not
the formal top. -/
def IsShort (σ : SectionOp I) : Prop :=
  ∀ P ∈ rankCat I 3, ∀ t, Label.IsShort 3 (σ P t) ∧ σ P t ≠ ⊤

/-- (iii) **Literal**: the section of a profile reads every old cell by the profile. -/
def IsLiteral (σ : SectionOp I) : Prop := ∀ P d, σ P (I.towerEmbed 2 d) = P d

/-- (iv) **Capped agreement at the cap `h`**: profiles of the catalogue agreeing capped at `h` at
every old cell have sections agreeing capped at `h` at every cell of `T 2`. -/
def IsCapAgreeingAt (σ : SectionOp I) (h : Label.{u}) : Prop :=
  ∀ P ∈ rankCat I 3, ∀ Q ∈ rankCat I 3, (∀ d, min (P d) h = min (Q d) h) →
    ∀ t, min (σ P t) h = min (σ Q t) h

end SectionOp

/-! ### The interface at the caps self-visible and short at `3`
-/

variable {I}

variable (I) in
/-- **The tower section operator**: the tower section at the grade `2` (`Seed.towerSection`), with
the block bound `2 N + 2` of the catalogue (`RankProfile.gridBound`), read by the upper decoder
(`Label.upperDecoderAt` at the cap grade `3`).  One function of the profile. -/
noncomputable def towerSectionOp : SectionOp I :=
  fun P ↦ I.towerSection (RankProfile.gridBound I) 2 P

/-- (i) The tower section operator is lawful. -/
theorem towerSectionOp_isLawful : (towerSectionOp I).IsLawful := fun P hP ↦ by
  obtain ⟨⟨hC, hD⟩, -⟩ := mem_rankCat.mp hP
  exact Seed.isLawfulBelow_towerSection
    (I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp)
      (by decide)) 2 (by omega)
    (hC.mono (X := (OrderedLayer.coatomC, 2)) ⟨subset_rfl, by omega⟩)
    (hD.mono (X := (OrderedLayer.coatomD, 2)) ⟨subset_rfl, by omega⟩)

/-- (ii) The tower section operator is short at `3` and never the formal top: its values lie in the
code grid `codeGrid 3 (2 N + 2)`. -/
theorem towerSectionOp_isShort : (towerSectionOp I).IsShort := fun P hP t ↦ by
  have hm := Seed.towerSection_mem_codeGrid 2 (by omega)
    (fun d ↦ RankProfile.mem_codeGrid_of_mem_rankCat hP d) t
  exact ⟨isShort_of_mem_codeGrid hm, ne_top_of_mem_codeGrid hm⟩

/-- (iii) The tower section operator is literal. -/
theorem towerSectionOp_isLiteral : (towerSectionOp I).IsLiteral := fun P d ↦
  Seed.towerSection_towerEmbed 2 P d

/-- (iv) **The tower section operator agrees capped at every cap self-visible and short at `3`**
(`Seed.min_towerSection_eq`). -/
theorem towerSectionOp_isCapAgreeingAt {h : Label.{u}} (hh : IsSelfVisible 3 h)
    (hs : Label.IsShort 3 h) : (towerSectionOp I).IsCapAgreeingAt h := fun _ hP _ _ hPQ t ↦
  Seed.min_towerSection_eq hh hs 2 le_rfl
    (fun d ↦ RankProfile.mem_codeGrid_of_mem_rankCat hP d) hPQ t

/-- **The interface theorem at the caps self-visible and short at `3`**, for every seed on five
points: one section operator through `T 2` is lawful, short at `3` and never the formal top,
literal, and agrees capped at every cap self-visible and short at `3` (`towerSectionOp`). -/
theorem exists_sectionOp : ∃ σ : SectionOp I, σ.IsLawful ∧ σ.IsShort ∧ σ.IsLiteral ∧
    ∀ h, IsSelfVisible 3 h → Label.IsShort 3 h → σ.IsCapAgreeingAt h :=
  ⟨towerSectionOp I, towerSectionOp_isLawful, towerSectionOp_isShort, towerSectionOp_isLiteral,
    fun _ hh hs ↦ towerSectionOp_isCapAgreeingAt hh hs⟩

/-! ### The collision
-/

/-- **Capped agreement fails at a collision.**  Let `σ` be lawful and literal, and let `P`, `Q` be
profiles of the catalogue that agree capped at a label `e` not self-visible at `2`.  Let `d₁`, `d₂`
be cells of grade `1` and `s` a cell of grade `2` of the amalgam, with `P = e` at `d₁` and `d₂`,
`Q d₁ = e < Q d₂ ≤ Q s`.  Then `σ` is not cap-agreeing at `e`: availability for `σ Q` from `s` gives
a cell `u` at `(univ, 2)` with `σ Q u ≥ Q s`, locality there makes its row read `d₁` strictly below
`d₂`, and capped agreement would put `σ P u` above `e`, a collision at `u` that forces the row to
read `d₁` and `d₂` alike (`Label.eq_of_transformsTo_collision`). -/
theorem not_isCapAgreeingAt_of_collision {σ : SectionOp I} (hlaw : σ.IsLawful)
    (hlit : σ.IsLiteral) {P Q : Profile I} (hP : P ∈ rankCat I 3) (hQ : Q ∈ rankCat I 3)
    {e : Label.{u}} (hev : ¬ IsSelfVisible 2 e) (hPQ : ∀ d, min (P d) e = min (Q d) e)
    {d₁ d₂ s : Fin I.amalgam.card} (hg₁ : I.amalgam.toCellScheme.grade d₁ = 1)
    (hg₂ : I.amalgam.toCellScheme.grade d₂ = 1) (hgs : I.amalgam.toCellScheme.grade s = 2)
    (hP₁ : P d₁ = e) (hP₂ : P d₂ = e) (hQ₁ : Q d₁ = e) (hQ₂ : e < Q d₂) (hQs : Q d₂ ≤ Q s) :
    ¬ σ.IsCapAgreeingAt e := by
  intro hcap
  obtain ⟨hvisQ, hlocQ, havQ⟩ := Rows.isLawfulBelow_iff_forall.mp (hlaw Q hQ)
  obtain ⟨hvisP, hlocP, -⟩ := Rows.isLawfulBelow_iff_forall.mp (hlaw P hP)
  -- A cell at `(univ, 2)`, and availability for `σ Q` from the old cell `s`.
  obtain ⟨t₀, ht₀⟩ : ∃ t, (I.tower 2).toCellScheme.gradedIndex t = ((univ : Finset (Fin 5)), 2) :=
    I.exists_gradedIndex_eq_univ_tower 1
  have ht₀m : t₀ ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) := by
    rw [CellScheme.mem_below, ht₀]
  obtain ⟨u, hu, hle⟩ := havQ (I.towerEmbed 2 s) t₀ ht₀m
    (by rw [show (I.tower 2).toCellScheme.scope t₀ = univ from congrArg Prod.fst ht₀]
        exact subset_univ _)
    (by rw [I.grade_towerEmbed, hgs]; exact (congrArg Prod.snd ht₀).symm)
  rw [ht₀] at hu
  have huY : u ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) := by
    rw [CellScheme.mem_below, hu]
  have hQu : Q d₂ ≤ σ Q u := by rw [hlit] at hle; exact hQs.trans hle
  -- The old cells `d₁`, `d₂` lie below `u`.
  have hmem (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d = 1) :
      I.towerEmbed 2 d ∈ (I.tower 2).toCellScheme.below
        ((I.tower 2).toCellScheme.gradedIndex u) := by
    rw [hu]; exact I.towerEmbed_mem_below (by omega)
  have hG (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d = 1) :
      (I.tower 2).toCellScheme.grade (I.towerEmbed 2 d) = 1 := by
    rw [I.grade_towerEmbed, hd]
  have hgu : (I.tower 2).toCellScheme.grade u = 2 := congrArg Prod.snd hu
  -- Locality for `σ Q` at `u`: the row of `u` reads `d₁` strictly below `d₂`.
  have hsep :
      (I.tower 2).rows.row u ⟨_, hmem d₁ hg₁⟩ < (I.tower 2).rows.row u ⟨_, hmem d₂ hg₂⟩ := by
    by_contra hns
    have h := (hlocQ u huY).le_of_le (d := ⟨_, hmem d₂ hg₂⟩) (d' := ⟨_, hmem d₁ hg₁⟩)
      (not_lt.mp hns) (by simp only [hG d₁ hg₁, hG d₂ hg₂, le_rfl])
    -- The targets at the old cells `d₂` and `d₁`.
    change min (σ Q (I.towerEmbed 2 d₂)) (σ Q u) ≤ min (σ Q (I.towerEmbed 2 d₁)) (σ Q u) at h
    rw [hlit, hlit, hQ₁, min_eq_left (hQ₂.le.trans hQu), min_eq_left hQu] at h
    exact absurd (h.trans_lt hQ₂) (lt_irrefl _)
  -- Capped agreement at `e` puts `σ P u` strictly above `e`.
  have hPu : e < σ P u := by
    have h := hcap P hP Q hQ hPQ u
    rw [min_eq_right (hQ₂.le.trans hQu)] at h
    have hle' : e ≤ σ P u := min_eq_right_iff.mp h
    refine lt_of_le_of_ne hle' fun heq ↦ hev ?_
    have hv := hvisP u huY
    rw [hgu] at hv
    rwa [← heq] at hv
  -- The collision at `u`.
  have hor (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d = 1) :
      IsSelfVisible 1 ((I.tower 2).rows.row u ⟨_, hmem d hd⟩) := by
    have h := (I.isConsistent_tower 2).isOrderly u ⟨_, hmem d hd⟩
    rwa [hG d hd] at h
  have htg (d : Fin I.amalgam.card) (hd : P d = e) : min (σ P (I.towerEmbed 2 d)) (σ P u) = e := by
    rw [hlit, hd]; exact min_eq_left hPu.le
  have heq := eq_of_transformsTo_collision (hlocP u huY) (d₁ := ⟨_, hmem d₁ hg₁⟩)
    (d₂ := ⟨_, hmem d₂ hg₂⟩) (z := ⟨u, (I.tower 2).toCellScheme.mem_below_gradedIndex u⟩)
    (hG d₁ hg₁) (hG d₂ hg₂) hgu (hor d₁ hg₁) (hor d₂ hg₂) (htg d₁ hP₁) (htg d₂ hP₂) hev
    (show e < min (σ P u) (σ P u) by rw [min_self]; exact hPu)
  exact absurd heq hsep.ne

/-! ### The seeds of `TL` and `T5`
-/

section Seeds

open TwoFaceLiftExistsCounterexample (TL)
open CaseSplitCounterexample (T5 tripleLabelling tripleKind)
open ProfileCatalogue (tripleProfile tripleProfile_apply exists_test_cells)

/-- The label `1`, at the grade `1`. -/
private noncomputable abbrev one : Label.{u} := gridPoint 1 0

/-- The label `2`, at the grade `2`. -/
private noncomputable abbrev two : Label.{u} := gridPoint 2 0

private theorem one_lt_two : one.{u} < two := gridPoint_lt_gridPoint_iff_lex.mpr (by omega)

private theorem lt_three {x : Label.{u}} (hx : x = ⊥ ∨ x = one ∨ x = two) : x < gridPoint 3 0 := by
  rcases hx with rfl | rfl | rfl
  · exact bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 3 0)
  · exact gridPoint_lt_gridPoint_iff_lex.mpr (by omega)
  · exact gridPoint_lt_gridPoint_iff_lex.mpr (by omega)

/-- The label `1` is not self-visible at `2`. -/
private theorem not_isSelfVisible_two_one : ¬ IsSelfVisible 2 one.{u} := fun h ↦
  absurd (gridPoint_zero_le h (gridPoint_ne_bot 1 0))
    (not_le.mpr (gridPoint_lt_gridPoint_iff_lex.mpr (by omega)))

/-- The value of a profile of five parameters through the kind of its graded index. -/
private theorem tripleLabelling_eq (AC FC AD FD G : Label.{u}) (X : Finset (Fin 5) × ℕ) :
    tripleLabelling AC FC AD FD G X = ![⊥, AC, FC, AD, FD, G] (tripleKind X) := rfl

/-- A profile of five parameters with values among `⊥`, `1`, `2` takes its values there. -/
private theorem tripleProfile_cases {AC FC AD FD : Label.{u}}
    (hAC : AC = one ∨ AC = two) (hFC : FC = one ∨ FC = two) (hAD : AD = one ∨ AD = two)
    (hFD : FD = one ∨ FD = two) (d : Fin I.amalgam.card) :
    tripleProfile I AC FC AD FD ⊥ d = ⊥ ∨ tripleProfile I AC FC AD FD ⊥ d = one ∨
      tripleProfile I AC FC AD FD ⊥ d = two := by
  rw [tripleProfile_apply, tripleLabelling_eq]
  generalize tripleKind (I.amalgam.toCellScheme.gradedIndex d) = c
  fin_cases c <;> simp_all

variable (hIL : I.left = TL α) (hIR : I.right = T5 α)
include hIL hIR

/-- **The profiles `(A_C, F_C, A_D, F_D, ⊥)` with values `1` or `2` are in the catalogue at the
grade `3`**: they are lawful below both coatoms (`TwoFaceLiftExistsCounterexample`,
`isLawfulBelow_tripleLabelling`), and all their values lie below `3`, where the orbit code agrees
with them (`Label.min_orbitCode_gridPoint_zero`). -/
theorem tripleProfile_mem_rankCat {AC FC AD FD : Label.{u}}
    (hAC : AC = gridPoint 1 0 ∨ AC = gridPoint 2 0) (hFC : FC = gridPoint 2 0)
    (hAD : AD = gridPoint 1 0 ∨ AD = gridPoint 2 0) (hFD : FD = gridPoint 2 0) :
    tripleProfile I AC FC AD FD ⊥ ∈ rankCat I 3 := by
  subst hFC hFD
  have hv1 {A : Label.{u}} (hA : A = one ∨ A = two) : IsSelfVisible 1 A := by
    rcases hA with rfl | rfl
    exacts [isSelfVisible_gridPoint 1 0, (isSelfVisible_gridPoint 2 0).mono (by omega)]
  obtain ⟨hC, hD⟩ := TwoFaceLiftExistsCounterexample.isLawfulBelow_tripleLabelling hIL hIR
    (hv1 hAC) (isSelfVisible_gridPoint 2 0) (hv1 hAD) (isSelfVisible_gridPoint 2 0)
    (isSelfVisible_bot 3) bot_le (fun h ↦ absurd h (not_lt.mpr bot_le)) bot_le bot_le
  refine mem_rankCat.mpr ⟨⟨hC, hD⟩, funext fun d ↦ ?_⟩
  have hlt := lt_three (tripleProfile_cases (I := I) hAC (.inr rfl) hAD (.inr rfl) d)
  exact eq_of_min_eq_of_lt (min_orbitCode_gridPoint_zero d).symm hlt

/-- **(iv) fails at the cap `1`**, for every seed of the coatom types `TL` and `T5` and every
section operator lawful and literal at the profiles of the catalogue: the profiles
`P₁ = (1, 2, 1, 2, ⊥)` and `Q₁ = (1, 2, 2, 2, ⊥)` agree capped at `1`, and they collide at the cell
at `(univ, 2)` that serves `Q₁` from `({0, 1, 2, 3}, 2)` (`not_isCapAgreeingAt_of_collision`).  The
cap `1` is short at `3` and not self-visible at `3`; the caps the one-grade lift uses are
self-visible at `3`. -/
theorem not_isCapAgreeingAt_one {σ : SectionOp I} (hlaw : σ.IsLawful) (hlit : σ.IsLiteral) :
    ¬ σ.IsCapAgreeingAt (gridPoint 1 0) := by
  obtain ⟨d₁, sC, -, d₂, hd₁, hsC, -, hd₂⟩ := exists_test_cells hIL hIR
  have hk₁ : tripleKind (I.amalgam.toCellScheme.gradedIndex d₁) = 1 := by rw [hd₁]; decide
  have hk₂ : tripleKind (I.amalgam.toCellScheme.gradedIndex d₂) = 3 := by rw [hd₂]; decide
  have hks : tripleKind (I.amalgam.toCellScheme.gradedIndex sC) = 2 := by rw [hsC]; decide
  refine not_isCapAgreeingAt_of_collision hlaw hlit
    (tripleProfile_mem_rankCat hIL hIR (.inl rfl) rfl (.inl rfl) rfl)
    (tripleProfile_mem_rankCat hIL hIR (.inl rfl) rfl (.inr rfl) rfl)
    not_isSelfVisible_two_one (fun d ↦ ?_) (congrArg Prod.snd hd₁) (congrArg Prod.snd hd₂)
    (congrArg Prod.snd hsC) (s := sC) ?_ ?_ ?_ ?_ ?_
  · rw [tripleProfile_apply, tripleProfile_apply, tripleLabelling_eq, tripleLabelling_eq]
    generalize tripleKind (I.amalgam.toCellScheme.gradedIndex d) = c
    fin_cases c <;> simp [min_eq_right one_lt_two.le]
  · rw [tripleProfile_apply, tripleLabelling_eq, hk₁]; rfl
  · rw [tripleProfile_apply, tripleLabelling_eq, hk₂]; rfl
  · rw [tripleProfile_apply, tripleLabelling_eq, hk₁]; rfl
  · rw [tripleProfile_apply, tripleLabelling_eq, hk₂]; exact one_lt_two
  · rw [tripleProfile_apply, tripleProfile_apply, tripleLabelling_eq, tripleLabelling_eq, hk₂,
      hks]
    exact le_rfl

omit hIL hIR in
/-- The cap `1` is short at `3`. -/
theorem isShort_three_one : Label.IsShort 3 (gridPoint.{u} 1 0) := by
  have h1 := isShort_gridPoint.{u} 1 0
  rw [gridPoint, isShort_coe] at h1 ⊢
  exact h1.trans (by exact_mod_cast (by omega : 1 ≤ 3))

/-- **(iv) at every cap short at `3` fails**, for every seed of the coatom types `TL` and `T5` and
every section operator lawful and literal at the profiles of the catalogue: the cap `1` is short at
`3` (`not_isCapAgreeingAt_one`). -/
theorem not_forall_isCapAgreeingAt_of_isShort {σ : SectionOp I} (hlaw : σ.IsLawful)
    (hlit : σ.IsLiteral) : ¬ ∀ h, Label.IsShort 3 h → σ.IsCapAgreeingAt h := fun hall ↦
  not_isCapAgreeingAt_one hIL hIR hlaw hlit (hall _ isShort_three_one)

end Seeds

/-- The cap `1` is not self-visible at `3`. -/
theorem not_isSelfVisible_three_one : ¬ IsSelfVisible 3 (gridPoint.{u} 1 0) := fun h ↦
  absurd (gridPoint_zero_le h (gridPoint_ne_bot 1 0))
    (not_le.mpr (gridPoint_lt_gridPoint_iff_lex.mpr (by omega)))

/-- **(iv) fails at the cap `1` for `seedL`** (`not_isCapAgreeingAt_one`). -/
theorem not_isCapAgreeingAt_one_seedL {σ : SectionOp (TwoFaceLiftExistsCounterexample.seedL α)}
    (hlaw : σ.IsLawful) (hlit : σ.IsLiteral) : ¬ σ.IsCapAgreeingAt (gridPoint 1 0) :=
  not_isCapAgreeingAt_one rfl rfl hlaw hlit

end VaughtConjecture.SectionInterface

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledReading
import VaughtConjecture.Extension.SmallArityOne

/-!
# The coatom step for a donor other than the context

Roadmap, Layer 3 ((R2) of the table of 3.4, the coatom step of
`VaughtConjecture.Continuation.SourceGapCoatomStep`).

The coatom step `StageType.HasTopReadingCoatomSteps α` at the arity one is the case of a context
`t'` on two points, the coatom `Fin.castSuccEmb` (the point `0`), its face `p`, and a legal donor
`d'` on two points with face `p` along `Fin.castSuccEmb`.  When `d' = t'` it is compiled through the
doubling (`StageType.exists_coatomStep_self`).  This file treats donors other than the context.

**The doubling does not carry a twist** (`Seed.eq_of_isLawful_doubled`).  In the doubled completion
of a seed with equal coatom types, every lawful labelling takes one value on the two copies of a
cell of `T` along the two coatoms.  So a donor with the scheme of the context and other labels is
not a face of any labelling of the doubled completion: at the input `SeparationObstruction.T α`,
with the donor `TwistedDonor.U α w s` for `s ≠ ⊤`, the copies of the lost top `r` would carry `⊤`
and `s` (`TwistedDonor.not_exists_isLawful_doubled`).  The map that breaks is the collapse
`Seed.doubledCell`: every cell of full scope reads the two copies of a cell alike, and the twist
labels them apart.

**New tops forced by a root top are read by every coface**
(`StageType.readsEachNewTop_of_forall_unique`).  Suppose that each cell `x` of the donor containing
the new point and labelled `⊤` is the only cell of its graded index in the donor and lies above a
cell `y` of the common face, labelled `⊤`, of the same grade and of scope inside that of `x`.  Then
every legal one-point coface of `t'` with face `d'` reads each new top along every root through the
coatom, at every cell of full scope, with `y` as both private cells: the row of a cell of full scope
is lawful (consistency), and availability in it puts `y` below the only cell of the graded index of
`x` (`Scheme.rowAt_le_of_forall_eq`).  At the arity one and a stage that is zero or a limit, the
completion at arity one (`Seed.completionBelowFullGradeOne`, with the apex) is such a coface, so the
top-reading coatom step holds for every legal context and every such donor
(`StageType.exists_coatomStep_of_forall_unique`); the donor need not be the context.

**The twisted donor** (`TwistedDonor.U α w s`): the scheme of `SeparationObstruction.T α` labelled
`(⊤, ⊥, ⊤, w, s)`, for `s ≤ w` self-visible at `2`; it has the face of the input on `{0}`
(`TwistedDonor.restrictFace_U`).  For `w ≠ ⊤` it is not the input (`TwistedDonor.U_ne_T`), its only
new top is `z`, forced by `y` (`TwistedDonor.forall_newTop_U`), and the top-reading coatom step
holds at the source-gap context `T α` with this donor (`TwistedDonor.exists_coatomStep_U`), through
the completion at arity one and not through the doubling.  For `w = ⊤` and `s ≠ ⊤` the new top `o`,
of grade `2`, is not forced by a root top; the coatom step for that donor is not decided here.

**The lift test** (`StageType.min_le_of_forall_rowAt_le`).  If every cell of graded index
`(univ, grade w)` labelled `⊤` in a legal coface reads a new top `x` at least as `s`, then every
lawful labelling `q` agreeing with the coface at a cap above its labels other than `⊤` has
`min (q s) (q w) ≤ q x`.  A lawful labelling violating this excludes the pair `(w, s)` for `x`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **A row reads a cell at least as a cell below it of the same grade**, when the first cell is
the only cell of its graded index: availability in the row (a lawful labelling, by consistency)
puts the second cell below a cell of the graded index of the first. -/
theorem rowAt_le_of_forall_eq (hS : S.rows.IsConsistent) {u y x : Fin S.card}
    (hyx : S.toCellScheme.scope y ⊆ S.toCellScheme.scope x)
    (hg : S.toCellScheme.grade y = S.toCellScheme.grade x)
    (hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (huniq : ∀ x', S.toCellScheme.gradedIndex x' = S.toCellScheme.gradedIndex x → x' = x) :
    S.rowAt u y ≤ S.rowAt u x := by
  obtain ⟨-, -, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall (w := S.rowAt u).mp
    (isLawfulBelow_rowAt hS rfl)
  obtain ⟨u', hu', hle⟩ := ha y x hx hyx hg
  rwa [huniq u' hu'] at hle

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {k m n : ℕ}

/-- **A coface reads each new top that a root top forces by availability**: if every cell `x` of
the donor `d'` containing the new point and labelled `⊤` is the only cell of its graded index in
`d'`, and lies above a cell `y` of the common face `p`, labelled `⊤`, of the same grade and of
scope inside that of `x`, then **every** legal one-point coface `D'` of `t'` with face `d'` along
`f` followed by the new point reads each new top along every root `g.trans f`, at every cell of
full scope (with `y` as both private cells). -/
theorem readsEachNewTop_of_forall_unique {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : D' ∈ t'.cofaces) {f : Fin m ↪ Fin k} {p : StageType.{u} α m}
    {d' : StageType.{u} α (m + 1)} (hD'd : restrictFace (extendByLast f) D' = some d')
    (hp : restrictFace f t' = some p) (hp' : restrictFace Fin.castSuccEmb d' = some p)
    (hnew : ∀ x : Fin d'.card, Fin.last m ∈ d'.toCellScheme.scope x → d'.label x = ⊤ →
      ∃ y : Fin p.card, p.label y = ⊤ ∧
        d'.toCellScheme.scope (faceCell hp' y) ⊆ d'.toCellScheme.scope x ∧
        p.toCellScheme.grade y = d'.toCellScheme.grade x ∧
        ∀ x', d'.toCellScheme.gradedIndex x' = d'.toCellScheme.gradedIndex x → x' = x)
    (g : Fin n ↪ Fin m) : ReadsEachNewTop hD'.2 (g.trans f) := by
  intro x hx hxl hxt
  -- the new top is a cell of the donor
  have hxv : x ∈ D'.visibleCells (extendByLast f) := by
    rw [Scheme.mem_visibleCells] at hx ⊢
    refine hx.trans ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨extendByLast g i, by rw [← extendByLast_trans]; rfl⟩
  obtain ⟨x₀, hx₀⟩ := D'.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hD'd) hxv
  change faceCell hD'd x₀ = x at hx₀
  subst hx₀
  rw [last_mem_scope_faceCell_iff] at hxl
  rw [label_faceCell] at hxt
  obtain ⟨y, hyt, hys, hyg, huniq⟩ := hnew x₀ hxl hxt
  -- the private cell: the root top `y`, as a cell of the context
  have hyy := faceCell_faceCell hD'.2 hD'd hp hp' y
  have hgx : D'.toCellScheme.grade (faceCell hD'd x₀) = d'.toCellScheme.grade x₀ :=
    grade_faceCell _ _
  refine ⟨faceCell hp y, faceCell hp y, by rw [label_faceCell, hyt], by rw [label_faceCell, hyt],
    le_rfl, by rw [hgx, grade_faceCell, hyg], fun u hu ↦ ?_⟩
  rw [hyy]
  refine Scheme.rowAt_le_of_forall_eq hD'.1.isConsistent ?_ ?_ ?_ ?_
  · rw [scope_faceCell hD'd, scope_faceCell hD'd]
    exact map_subset_map.mpr hys
  · rw [grade_faceCell hD'd, grade_faceCell hD'd, grade_faceCell hp', hyg]
  · rw [CellScheme.mem_below, hu]
    refine ⟨subset_univ _, ?_⟩
    change D'.toCellScheme.grade (faceCell hD'd x₀) ≤ _
    rw [hgx, grade_faceCell, hyg]
  · -- the new top is the only cell of its graded index in the coface
    intro x' hx'
    have hsc : D'.toCellScheme.scope x' = D'.toCellScheme.scope (faceCell hD'd x₀) :=
      congrArg Prod.fst hx'
    have hx'v : x' ∈ D'.visibleCells (extendByLast f) := by
      rw [Scheme.mem_visibleCells, hsc]
      exact (Scheme.mem_visibleCells.mp (D'.toScheme.faceCell_mem_visibleCells _ x₀))
    obtain ⟨x₁, hx₁⟩ :=
      D'.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hD'd) hx'v
    change faceCell hD'd x₁ = x' at hx₁
    subst hx₁
    rw [huniq x₁ (Prod.ext ?_ ?_)]
    · change d'.toCellScheme.scope x₁ = d'.toCellScheme.scope x₀
      have := hsc
      rw [scope_faceCell, scope_faceCell] at this
      exact map_injective _ this
    · have := congrArg Prod.snd hx'
      change D'.toCellScheme.grade (faceCell hD'd x₁) =
        D'.toCellScheme.grade (faceCell hD'd x₀) at this
      rwa [grade_faceCell, grade_faceCell] at this

/-- **The lift test for reading at the tops.**  Let `D'` be legal, `c` a cap above every label of
`D'` other than `⊤`, and `q` a lawful labelling of `D'` agreeing with `D'` at the cap `c`.  If every
cell of graded index `(univ, grade w)` labelled `⊤` in `D'` reads `x` at least as `s`, with `x`
labelled `⊤` and `s`, `x` of grade at most that of `w`, then `min (q s) (q w) ≤ q x`.
Availability from `w` in `q` gives a cell `u` of graded index `(univ, grade w)` with
`q w ≤ q u`; if `min (q s) (q w)` exceeds `c`, then `u` is labelled `⊤` in `D'` and its row,
transformed by locality, gives the inequality.  So a lawful labelling agreeing with `D'` at such a
cap with `q x < min (q s) (q w)` excludes the pair `(w, s)` for `x`. -/
theorem min_le_of_forall_rowAt_le {N : ℕ} {D' : StageType.{u} α N} (hD' : D'.IsLegal)
    {w s x : Fin D'.card} (hsw : D'.toCellScheme.grade s ≤ D'.toCellScheme.grade w)
    (hxw : D'.toCellScheme.grade x ≤ D'.toCellScheme.grade w)
    (hread : ∀ u, D'.toCellScheme.gradedIndex u = (univ, D'.toCellScheme.grade w) →
      D'.label u = ⊤ → D'.rowAt u s ≤ D'.rowAt u x)
    (hxt : D'.label x = ⊤) {c : Label.{u}} (hc : ∀ j, D'.label j ≠ ⊤ → D'.label j < c)
    {q : Fin D'.card → Label.{u}} (hq : D'.rows.IsLawful q)
    (hqc : ∀ j, min (q j) c = min (D'.label j) c) : min (q s) (q w) ≤ q x := by
  have hcx : c ≤ q x := by
    have := hqc x
    rw [hxt, min_top_left] at this
    exact min_eq_right_iff.mp this
  by_cases hm : min (q s) (q w) ≤ c
  · exact hm.trans hcx
  obtain ⟨hcs, hcw⟩ := lt_min_iff.mp (not_le.mp hm)
  -- a cell of graded index `(univ, grade w)` above `w` in `q`
  have hwf := D'.isWellFormed.isWellFormed
  obtain ⟨u₀, hu₀⟩ := (isLegal_iff.mp hD').2.2 (univ, D'.toCellScheme.grade w)
    ⟨D'.univ_mem_faces, hwf.grade_pos w, (hwf.grade_le_card w).trans (card_le_card
      (subset_univ _))⟩
  obtain ⟨u, hu, hwu⟩ := hq.availability w u₀ (by
    rw [show D'.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
    exact subset_univ _) (congrArg Prod.snd hu₀).symm
  rw [hu₀] at hu
  -- it is labelled `⊤` in `D'`
  have hut : D'.label u = ⊤ := by
    by_contra hne
    have h1 := hqc u
    rw [min_eq_left (hc u hne).le] at h1
    have h2 : min (q u) c < c := h1 ▸ hc u hne
    exact (not_le.mpr h2) (le_min (hcw.le.trans hwu) le_rfl)
  have hr := hread u hu hut
  have hmem {e : Fin D'.card} (he : D'.toCellScheme.grade e ≤ D'.toCellScheme.grade w) :
      e ∈ D'.toCellScheme.below (D'.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]
    exact ⟨subset_univ _, he⟩
  rw [Scheme.rowAt_of_mem (hmem hsw), Scheme.rowAt_of_mem (hmem hxw)] at hr
  obtain ⟨g, σ, hW, he⟩ := hq.locality u
  have hgu : D'.toCellScheme.grade u = D'.toCellScheme.grade w := congrArg Prod.snd hu
  have hqu : q u ≤ g (D'.toCellScheme.grade x) := by
    have := he ⟨u, CellScheme.mem_below_gradedIndex _ u⟩
    simp only [min_self] at this
    rw [this]
    exact (min_le_right _ _).trans (hW.antitone (hgu ▸ hxw))
  have hs' := he ⟨s, hmem hsw⟩
  have hx' := he ⟨x, hmem hxw⟩
  simp only at hs' hx'
  calc min (q s) (q w) ≤ min (q s) (q u) := min_le_min_left _ hwu
    _ ≤ min (σ (D'.rows.row u ⟨x, hmem hxw⟩)) (g (D'.toCellScheme.grade x)) := by
        refine le_min ?_ ((min_le_right _ _).trans hqu)
        rw [hs']
        exact (min_le_left _ _).trans (hW.monotone hr)
    _ = min (q x) (q u) := hx'.symm
    _ ≤ q x := min_le_left _ _

/-- **The coatom step at arity one for a donor whose new tops are forced by root tops**, at a
stage that is zero or a limit: for legal `t'` and `d'` on two points with a common face `p` along
`Fin.castSuccEmb`, if every cell of `d'` containing the new point and labelled `⊤` is the only cell
of its graded index and lies above a cell of `p` labelled `⊤`, of the same grade, the completion at
arity one (`Seed.completionBelowFullGradeOne`) with the apex is a legal one-point coface of `t'`
with face `d'` that reads each new top along every root `g.trans Fin.castSuccEmb`.  No hypothesis
on the context; the donor need not be the context. -/
theorem exists_coatomStep_of_forall_unique (hα : Order.IsSuccPrelimit α)
    {t' d' : StageType.{u} α 2} (ht' : t'.IsLegal) (hd' : d'.IsLegal) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p)
    (hp' : restrictFace Fin.castSuccEmb d' = some p)
    (hnew : ∀ x : Fin d'.card, Fin.last 1 ∈ d'.toCellScheme.scope x → d'.label x = ⊤ →
      ∃ y : Fin p.card, p.label y = ⊤ ∧
        d'.toCellScheme.scope (faceCell hp' y) ⊆ d'.toCellScheme.scope x ∧
        p.toCellScheme.grade y = d'.toCellScheme.grade x ∧
        ∀ x', d'.toCellScheme.gradedIndex x' = d'.toCellScheme.gradedIndex x → x' = x)
    {n : ℕ} (g : Fin n ↪ Fin 1) {h : Fin n ↪ Fin 2} (hg : g.trans Fin.castSuccEmb = h) :
    ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ t'.cofaces),
      restrictFace (extendByLast Fin.castSuccEmb) D' = some d' ∧ ReadsEachNewTop hD'.2 h ∧
        ReadsEachNewTopAtTops hD'.2 h := by
  obtain ⟨D', hD', h₁, h₂, -⟩ :=
    (Seed.ofCoatoms ht' hd' hp hp').completionBelowFullGradeOne.exists_coatomExtension hα
  subst hg
  have hr := readsEachNewTop_of_forall_unique ⟨hD', h₁⟩ h₂ hp hp' hnew g
  exact ⟨D', ⟨hD', h₁⟩, h₂, hr, hr.atTops⟩

end StageType

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)

/-- **The doubled completion carries no twist**: in every lawful labelling of the doubled
completion, the two copies of a cell of `T` along the two coatoms have one label.  So no lawful
labelling of it restricts to `T` on one coatom and to `T` with other labels on the other. -/
theorem eq_of_isLawful_doubled (hI : I.left.IsLegal) {q : Fin (I.doubled hLR).card → Label.{u}}
    (hq : (I.doubled hLR).rows.IsLawful q) (c : Fin I.left.card) :
    q (I.old hLR (StageType.faceCell I.restrictFace_left c)) =
      q (I.old hLR (StageType.faceCell (I.restrictFace_right_left hLR) c)) := by
  have hmem (e : Fin I.amalgam.card) : I.old hLR e ∈
      (I.doubled hLR).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
    rw [CellScheme.mem_below, gradedIndex_old]
    exact ⟨subset_univ _, I.grade_le_two e⟩
  refine I.eq_of_isLawfulBelow_doubled hLR hI le_rfl (hq.isLawfulBelow _) (hmem _) (hmem _) ?_
  rw [doubledCell_old, doubledCell_old, doublingCell_faceCell_left, doublingCell_faceCell_right]

end Seed

namespace TwistedDonor

open SeparationObstruction

variable (α : Ordinal.{u}) {w s : Label.{u}}

/-- **The twisted donor**: the scheme of the input `SeparationObstruction.T α`, labelled
`(⊤, ⊥, ⊤, w, s)`; lawful for `w`, `s` self-visible at `2` with `s ≤ w`. -/
noncomputable def U (hw : IsSelfVisible 2 w) (hs : IsSelfVisible 2 s) (hsw : s ≤ w)
    (hwα : AtStage α w) (hsα : AtStage α s) : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊤ w s
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_top 1) hw hs le_top (by simp [min_eq_right hsw])
  atStage d := by
    fin_cases d
    exacts [Or.inr rfl, Or.inl (WithBot.bot_lt_coe _), Or.inr rfl, hwα, hsα]

variable {α} (hw : IsSelfVisible 2 w) (hs : IsSelfVisible 2 s) (hsw : s ≤ w)
  (hwα : AtStage α w) (hsα : AtStage α s)

theorem isLegal_U : (U α hw hs hsw hwα hsα).IsLegal := isLegal_S

/-- The face on `{0}` of the input. -/
theorem mem_faces : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ cells.faces := by
  change _ ∈ Geometry.intervalPlan univ
  decide

/-- **The donor has the face of the input on `{0}`**: the only cell visible there is `y`,
labelled `⊤` in both. -/
theorem restrictFace_U :
    restrictFace Fin.castSuccEmb (U α hw hs hsw hwα hsα) =
      restrictFace Fin.castSuccEmb (T α) := by
  rw [restrictFace_of_mem _ _ mem_faces, restrictFace_of_mem _ _ mem_faces]
  congr 1
  refine StageType.ext rfl fun i j hij ↦ ?_
  have key : ∀ d : Fin 5, d ∈ S.{u}.visibleCells (Fin.castSuccEmb : Fin 1 ↪ Fin 2) → d = 0 := by
    intro d hd
    rw [Scheme.mem_visibleCells] at hd
    have hd' : cells.scope d ⊆ univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) := by
      intro x hx
      obtain ⟨i, hi⟩ := hd hx
      exact mem_map.mpr ⟨i, mem_univ _, hi⟩
    clear hd
    revert hd'
    revert d
    decide
  change lab ⊤ w s (S.cellMap _ i) = lab ⊤ ⊤ ⊤ (S.cellMap _ j)
  rw [key _ (S.cellMap_mem _ i), key _ (S.cellMap_mem _ j)]
  rfl

/-- **The donor is not the context** when `w` is not `⊤`. -/
theorem U_ne_T (hwt : w ≠ ⊤) : U α hw hs hsw hwα hsα ≠ T α := fun he ↦
  hwt (label_congr he (i := (3 : Fin 5)) (j := (3 : Fin 5)) rfl)

variable (α) in
/-- The face of the input on `{0}`: the cell `y`, labelled `⊤`. -/
noncomputable abbrev face : StageType.{u} α 1 := (T α).comap Fin.castSuccEmb mem_faces

variable (α) in
theorem restrictFace_T : restrictFace Fin.castSuccEmb (T α) = some (face α) :=
  restrictFace_of_mem _ _ mem_faces

theorem restrictFace_U_face :
    restrictFace Fin.castSuccEmb (U α hw hs hsw hwα hsα) = some (face α) :=
  (restrictFace_U hw hs hsw hwα hsα).trans (restrictFace_T α)

/-- **The new tops of the donor are forced by the root top**, when `w` is not `⊤`: the only cell
containing the new point and labelled `⊤` is `z`, the only cell of its graded index, above `y` of
the same grade. -/
theorem forall_newTop_U (hwt : w ≠ ⊤) (x : Fin (U α hw hs hsw hwα hsα).card)
    (hxl : Fin.last 1 ∈ (U α hw hs hsw hwα hsα).toCellScheme.scope x)
    (hxt : (U α hw hs hsw hwα hsα).label x = ⊤) :
    ∃ y : Fin (face α).card, (face α).label y = ⊤ ∧
      (U α hw hs hsw hwα hsα).toCellScheme.scope
          (faceCell (restrictFace_U_face hw hs hsw hwα hsα) y) ⊆
        (U α hw hs hsw hwα hsα).toCellScheme.scope x ∧
      (face α).toCellScheme.grade y = (U α hw hs hsw hwα hsα).toCellScheme.grade x ∧
      ∀ x', (U α hw hs hsw hwα hsα).toCellScheme.gradedIndex x' =
        (U α hw hs hsw hwα hsα).toCellScheme.gradedIndex x → x' = x := by
  have hst : s ≠ ⊤ := fun h ↦ hwt (top_le_iff.mp (h ▸ hsw))
  have key : ∀ x : Fin 5, 1 ∈ cells.scope x → x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  rcases key x hxl with rfl | rfl | rfl | rfl
  · exact absurd hxt (by simp [U, lab])
  · obtain ⟨y, hy⟩ := exists_faceCell_eq_of_last_notMem (restrictFace_U_face hw hs hsw hwα hsα)
      (s := (0 : Fin 5)) (show (1 : Fin 2) ∉ cells.scope 0 by decide)
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · rw [← label_faceCell (restrictFace_U_face hw hs hsw hwα hsα), hy]
      rfl
    · rw [hy]
      change cells.scope 0 ⊆ cells.scope 2
      decide
    · rw [← grade_faceCell (restrictFace_U_face hw hs hsw hwα hsα), hy]
      rfl
    · intro x' hx'
      have key' : ∀ x' : Fin 5, cells.gradedIndex x' = cells.gradedIndex 2 → x' = 2 := by decide
      exact key' x' hx'
  · exact absurd hxt (by simpa [U, lab] using hwt)
  · exact absurd hxt (by simpa [U, lab] using hst)

/-- **The coatom step for the twisted donor**, at a stage that is zero or a limit: when `w` is not
`⊤` (so the donor is not the context, `TwistedDonor.U_ne_T`), some legal one-point coface of the
source-gap context `SeparationObstruction.T α` has face the donor along `extendByLast
Fin.castSuccEmb` and reads each new top along the root `{0}`, at every cell of full scope. -/
theorem exists_coatomStep_U (hα : Order.IsSuccPrelimit α) (hwt : w ≠ ⊤) :
    ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ (T α).cofaces),
      restrictFace (extendByLast Fin.castSuccEmb) D' = some (U α hw hs hsw hwα hsα) ∧
      ReadsEachNewTop hD'.2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∧
      ReadsEachNewTopAtTops hD'.2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) :=
  exists_coatomStep_of_forall_unique hα (isLegal_T α) (isLegal_U hw hs hsw hwα hsα)
    (restrictFace_T α)
    (restrictFace_U_face hw hs hsw hwα hsα) (forall_newTop_U hw hs hsw hwα hsα hwt)
    (Function.Embedding.refl _) (Function.Embedding.ext fun _ ↦ rfl)

variable (α) in
/-- The seed of the input with itself. -/
noncomputable abbrev seed : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_T α) (isLegal_T α) (restrictFace_T α) (restrictFace_T α)

/-- **The doubling breaks for the twisted donor**: when `s` is not `⊤`, no lawful labelling of the
doubled completion of the input with itself restricts to the labels of the input on the first
coatom and to those of the donor on the second; the copies of the lost top `r` would carry `⊤`
and `s` (`Seed.eq_of_isLawful_doubled`). -/
theorem not_exists_isLawful_doubled (hst : s ≠ ⊤) :
    ¬ ∃ q : Fin ((seed α).doubled rfl).card → Label.{u}, ((seed α).doubled rfl).rows.IsLawful q ∧
      (∀ c, q ((seed α).old rfl (faceCell (seed α).restrictFace_left c)) = (T α).label c) ∧
      ∀ c, q ((seed α).old rfl (faceCell ((seed α).restrictFace_right_left rfl) c)) =
        (U α hw hs hsw hwα hsα).label c := by
  rintro ⟨q, hq, hl, hr⟩
  have he := (seed α).eq_of_isLawful_doubled rfl (isLegal_T α) hq (cellT α 4)
  have h4 : (T α).label (cellT α 4) = (U α hw hs hsw hwα hsα).label (cellT α 4) :=
    ((hl _).symm.trans he).trans (hr _)
  exact hst h4.symm

end TwistedDonor

end VaughtConjecture

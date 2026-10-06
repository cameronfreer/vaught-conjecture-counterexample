/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.AvailableTopDetermination
import VaughtConjecture.Extension.CompletionBelowFullGrade
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.TwoFaceLift
import VaughtConjecture.Extension.UnionFillCounterexample

/-!
# Determination over anchored contexts with a top fails

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4; the exact pinned extension of row 6); the
refuting instance for the anchored context with a top of
`VaughtConjecture.Continuation.AvailableTopDetermination`, and an instance of the graded predicate
over which determination holds.

**Pinned extensions on at most three points.**  Every seed with `m ≤ 2` has a completion below the
full grade (`Seed.nonempty_completionBelowFullGrade_of_le_two`), so at a stage that is zero or a
limit two legal stage types on `m + 1 ≤ 3` points with a common face along the initial segment
are the coatom faces of one legal stage type (`exists_coatomExtension_of_le_two`), and the exact
pinned extension of a legal stage type on at most three points exists
(`exists_pinned_extension_of_le_three`, through `StageType.exists_pinned_extension_of_lt`).  No
hypothesis is used.

**The legal type** `topType α` is the scheme `S` on three points of
`VaughtConjecture.Extension.UnionFillCounterexample` (interval plan, one cell at every graded face
of grade at most `2`; the live cells are at `({2}, 1)`, `({1, 2}, 1)`, `(univ, 1)`, `({0, 1}, 2)`
and `(univ, 2)`) with its lawful labelling `labelling ⊤ ⊤` (the live cells `⊤`, the others `⊥`),
with the apex added (`StageType.addApex`).  Its faces on `{0, 1}`, `{0}` and `{2}` are `pairFace α`,
`pointFace α` and `newPointFace α`.

**The refuting instance** (`exists_not_isDeterminedWithin`, at every limit stage):

* the **context** (`context`) is `topType α` with its cells of grade at least `2` capped at an
  ordinal `c < α` self-visible at `3` (`StageType.capOn`; availability relates cells of equal
  grades, so the cap is lawful).  It is legal, its tops are the live cells of grade `1`, so its top
  grade is `1` (`topGrade_context_le`), and its apex, of graded index `(univ, 3)`, is labelled `c`;
* the **root** is `pointFace α`, the face on `{0}`, along `pointEmb`; its only cell is dead, so it
  is top-free, and the context agrees with `topType α` there (`restrictFace_context`);
* the **donor** is `pairFace α`, the face on `{0, 1}` with new point `1`.  It is a legal coface of
  the root, and its cell at `({0, 1}, 2)` is a new top of grade `2`; the root is not a rigid core
  of it (`StageType.not_isRigidCoreIn_of_restrictFace_isTopFree`).

The context is an anchored context with a top for the donor along `pointEmb`
(`isAnchoredContextWithTop_context`): the apex is a private cap above the labels `⊥` of the donor,
anchoring holds vacuously, the context is not top-free, and the exact pinned extension on three
points gives a legal coface carrying the donor.  The new top of the donor has grade `2`, above the
top grade `1` of the context, so the donor is determined over the context within the receiving
family of no coface at any permitted cutoff
(`StageType.not_isDeterminedWithin_receivingFamily_of_topGrade_lt`), and cutoff determination with
a donor fails for the anchored context with a top (`not_cutoffDonorDetermination`).  The refuted
statement is determination for this predicate; nothing here refutes (R2) or (R3).

**An instance of the graded predicate over which determination holds**
(`exists_isGradedTopContext_isDeterminedWithin`).  Over the empty root, the face on `{0, 1}` is a
graded anchored context with a top (`StageType.IsGradedTopContext`) for the face on `{2}`, a
one-point donor labelled `⊤` in which the empty root is not a rigid core: its cell at `({0, 1}, 2)`
is a private cap labelled `⊤`, of grade `2`.  The only cell of `topType α` at `(univ, 2)` reads the
donor's cell as it reads that private top (both row entries are the row value `2`), so
`topType α` makes it a reading context (`isReadingContext_pairFace`) and the donor is determined
within the receiving family of `topType α` at a permitted cutoff.  Determination for the graded
predicate in general is open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.AvailableTopDeterminationCounterexample

open Finset StageType Realization Label UnionFillCounterexample

variable {α : Ordinal.{u}}

/-! ### Coatom extensions and pinned extensions at small arity -/

/-- **The coatom extension at arity at most `2`**: at a stage that is zero or a limit, two legal
stage types on `m + 1 ≤ 3` points with the same face along the initial segment are the faces along
the two coatoms of one legal stage type on `m + 2` points.  Every seed with `m ≤ 2` has a
completion below the full grade (`Seed.nonempty_completionBelowFullGrade_of_le_two`), and the
completion is such a type (`CompletionBelowFullGrade.exists_coatomExtension`). -/
theorem exists_coatomExtension_of_le_two (hα : Order.IsSuccPrelimit α) {m : ℕ} (hm : m ≤ 2)
    (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m) (hla : ta.IsLegal)
    (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
    (hpb : restrictFace Fin.castSuccEmb tb = some p) :
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧ restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb := by
  obtain ⟨F⟩ := (Seed.ofCoatoms hla hlb hpa hpb).nonempty_completionBelowFullGrade_of_le_two hm
  obtain ⟨t, ht, h₁, h₂, -⟩ := F.exists_coatomExtension hα
  exact ⟨t, ht, h₁, h₂⟩

/-- **The exact pinned extension on at most three points**: at a stage that is zero or a limit,
for a legal stage type `P` on `n ≤ 3` points, a closed face `f` of `P` with restriction `p`, and a
legal one-point coface `d` of `p`, some legal one-point coface of `P` has face `d` along
`extendByLast f`.  The coatom extensions used are at arities below `n`, at most `2`. -/
theorem exists_pinned_extension_of_le_three (hα : Order.IsSuccPrelimit α) {n m : ℕ} (hn : n ≤ 3)
    {P : StageType.{u} α n} (hP : P.IsLegal) {f : Fin m ↪ Fin n} {p : StageType.{u} α m}
    {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d :=
  exists_pinned_extension_of_lt
    (fun _ hm' ↦ exists_coatomExtension_of_le_two hα (by omega)) hP hPf hd hdp

/-! ### The legal type on three points with its live cells labelled `⊤` -/

/-- The scheme `UnionFillCounterexample.S` on three points with the labelling `labelling ⊤ ⊤`:
the live cells labelled `⊤`, the others `⊥`. -/
noncomputable def topBase (α : Ordinal.{u}) : StageType.{u} α 3 where
  toScheme := S
  label := labelling ⊤ ⊤
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling (isSelfVisible_top 1) (isSelfVisible_top 2) le_rfl
  atStage d := by
    unfold labelling
    split_ifs
    · exact atStage_top
    · exact atStage_top
    · exact atStage_bot

/-- **The legal type** `topType α`: `topBase α` with the apex added. -/
noncomputable def topType (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (topBase α).addApex isLegalBelowFullGrade_S (by omega)

/-- `topType α` is legal. -/
theorem isLegal_topType : (topType α).IsLegal :=
  isLegal_addApex _ _

/-- The cell of `topType α` coming from the cell `d` of `S`. -/
noncomputable def oldCell (d : Fin 9) : Fin (topType α).card :=
  Fin.castSucc (n := (topBase α).card) d

/-- The apex of `topType α`. -/
noncomputable def apexCell : Fin (topType α).card := Fin.last (topBase α).card

/-- The cells of `topType α` are the cells of `S` and the apex. -/
theorem cases_topType (x : Fin (topType α).card) : x = apexCell ∨ ∃ d : Fin 9, x = oldCell d := by
  change Fin ((topBase α).card + 1) at x
  induction x using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- The cells of `S` keep their graded indices in `topType α`. -/
theorem gradedIndex_oldCell (d : Fin 9) :
    (topType α).toCellScheme.gradedIndex (oldCell d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc S 3 d

/-- The cells of `S` keep their grades in `topType α`. -/
theorem grade_oldCell (d : Fin 9) :
    (topType α).toCellScheme.grade (oldCell d) = cellGrade d :=
  congrArg Prod.snd (gradedIndex_oldCell d)

/-- The cells of `S` keep their scopes in `topType α`. -/
theorem scope_oldCell (d : Fin 9) :
    (topType α).toCellScheme.scope (oldCell d) = cellScope d :=
  congrArg Prod.fst (gradedIndex_oldCell d)

/-- The apex of `topType α` has graded index `(univ, 3)`. -/
theorem gradedIndex_apexCell :
    (topType α).toCellScheme.gradedIndex apexCell = ((univ : Finset (Fin 3)), 3) :=
  Scheme.appendFullCellScheme_gradedIndex_last S 3

/-- The apex of `topType α` has full scope. -/
theorem scope_apexCell : (topType α).toCellScheme.scope apexCell = univ :=
  congrArg Prod.fst (gradedIndex_apexCell (α := α))

/-- The apex of `topType α` has grade `3`. -/
theorem grade_apexCell : (topType α).toCellScheme.grade apexCell = 3 :=
  congrArg Prod.snd (gradedIndex_apexCell (α := α))

/-- The labels of the cells of `S` in `topType α`. -/
theorem label_oldCell (d : Fin 9) : (topType α).label (oldCell d) = labelling ⊤ ⊤ d :=
  addApex_label_castSucc (t := topBase α) _ _ d

/-- The apex of `topType α` is labelled `⊤`. -/
theorem label_apexCell : (topType α).label apexCell = ⊤ :=
  addApex_label_last (t := topBase α) _ _

/-- Every label of `topType α` is `⊥` or `⊤`. -/
theorem label_topType_eq_bot_or_top (x : Fin (topType α).card) :
    (topType α).label x = ⊥ ∨ (topType α).label x = ⊤ := by
  rcases cases_topType x with rfl | ⟨d, rfl⟩
  · exact .inr label_apexCell
  · rw [label_oldCell]
    unfold labelling
    split_ifs
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl rfl

/-! ### The context, the root, and the donor -/

/-- The cells of grade at least `2` form an upper set. -/
private theorem two_le_grade_upper {t : StageType.{u} α 3} (x s : Fin t.card)
    (hx : 2 ≤ t.toCellScheme.grade x)
    (hxs : t.toCellScheme.gradedIndex x ≤ t.toCellScheme.gradedIndex s) :
    2 ≤ t.toCellScheme.grade s :=
  hx.trans hxs.2

/-- **The context** at a cap `c < α` self-visible at `3`: `topType α` with its cells of grade at
least `2` capped at `c` (`StageType.capOn`).  Availability relates cells of equal grades, so no
condition is needed. -/
noncomputable def context {c : Ordinal.{u}} (hc : IsSelfVisible 3 (c : Label.{u})) (hcα : c < α) :
    StageType.{u} α 3 :=
  (topType α).capOn (fun x ↦ 2 ≤ (topType α).toCellScheme.grade x) c hc hcα two_le_grade_upper
    fun _ _ _ hg hs hs' ↦ absurd (hg ▸ hs') hs

variable {c : Ordinal.{u}} (hc : IsSelfVisible 3 (c : Label.{u})) (hcα : c < α)

/-- The context is legal: it has the scheme of `topType α`. -/
theorem isLegal_context : (context hc hcα).IsLegal :=
  isLegal_topType

/-- **The top grade of the context is at most `1`**: its cells of grade at least `2` are capped
at the ordinal `c`. -/
theorem topGrade_context_le : (context hc hcα).topGrade ≤ 1 := by
  refine topGrade_le_iff.mpr fun x hx ↦ ?_
  by_contra hlt
  -- the label of the context at `x` (`StageType.capOn_label`) is capped at `c`
  change (if 2 ≤ (topType α).toCellScheme.grade x then min ((topType α).label x) c
    else (topType α).label x) = ⊤ at hx
  have hx2 : 2 ≤ (topType α).toCellScheme.grade x := by
    change 2 ≤ (context hc hcα).toCellScheme.grade x
    omega
  rw [ite_eq_left hx2] at hx
  have hle : min ((topType α).label x) (c : Label.{u}) ≤ c := min_le_right _ _
  rw [hx, top_le_iff] at hle
  exact WithBot.coe_injective.ne WithTop.coe_ne_top hle

/-- The context is not top-free: its cell at `({2}, 1)`, of grade `1`, is not capped. -/
theorem not_isTopFree_context : ¬ (context hc hcα).IsTopFree := fun h ↦ h (oldCell 2) (by
  -- unfold the label of the context (`StageType.capOn_label`)
  change (if 2 ≤ (topType α).toCellScheme.grade (oldCell 2) then
    min ((topType α).label (oldCell 2)) c else (topType α).label (oldCell 2)) = ⊤
  rw [grade_oldCell, label_oldCell]
  rfl)

/-- The face `{0, 1}` is a face of `topType α`. -/
theorem face_mem_topType :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (topType α).toCellScheme.faces := by
  -- the faces of `topType α` are those of the interval plan
  change univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The root embedding: the point `0` of the three points. -/
def pointEmb : Fin 1 ↪ Fin 3 := (Fin.castSuccEmb : Fin 1 ↪ Fin 2).trans Fin.castSuccEmb

/-- The face `{0}` is a face of `topType α`. -/
theorem pointFace_mem_topType : univ.map pointEmb ∈ (topType α).toCellScheme.faces := by
  -- the faces of `topType α` are those of the interval plan
  change univ.map pointEmb ∈ Geometry.intervalPlan univ
  decide +kernel

/-- **The face on `{0, 1}`** of `topType α`, the donor of the refuting instance (with new point
`1`). -/
noncomputable def pairFace (α : Ordinal.{u}) : StageType.{u} α 2 :=
  (topType α).comap Fin.castSuccEmb face_mem_topType

/-- **The face on `{0}`** of `topType α`, the root of the refuting instance. -/
noncomputable def pointFace (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (topType α).comap pointEmb pointFace_mem_topType

/-- The face on `{0, 1}` is legal. -/
theorem isLegal_pairFace : (pairFace α).IsLegal :=
  isLegal_topType.comap _ face_mem_topType

/-- The face on `{0}` is the face of the face on `{0, 1}` along the initial segment. -/
theorem restrictFace_pairFace : restrictFace Fin.castSuccEmb (pairFace α) = some (pointFace α) :=
  (restrictFace_trans _ _ _ (restrictFace_of_mem _ _ face_mem_topType)).trans
    (restrictFace_of_mem _ _ pointFace_mem_topType)

/-- The face on `{0, 1}` is a one-point coface of the face on `{0}`. -/
theorem pairFace_mem_cofaces : pairFace α ∈ (pointFace α).cofaces :=
  ⟨isLegal_pairFace, restrictFace_pairFace⟩

/-- A cell of a face along `pointEmb` has grade `1`: its scope is a single point. -/
private theorem grade_le_one_of_mem_visibleCells {t : StageType.{u} α 3} {x : Fin t.card}
    (hx : x ∈ t.visibleCells pointEmb) : t.toCellScheme.grade x ≤ 1 := by
  have hs := Scheme.mem_visibleCells.mp hx
  have hcard : #(t.toCellScheme.scope x) ≤ 1 := card_le_one.mpr fun a ha b hb ↦ by
    obtain ⟨i, rfl⟩ := hs (mem_coe.mpr ha)
    obtain ⟨j, rfl⟩ := hs (mem_coe.mpr hb)
    rw [Subsingleton.elim i j]
  exact (t.isWellFormed.isWellFormed.grade_le_card x).trans hcard

/-- **The face on `{0}` is the face of the context along `pointEmb`**: the context agrees with
`topType α` on the cells of grade `1`. -/
theorem restrictFace_context : restrictFace pointEmb (context hc hcα) = some (pointFace α) := by
  rw [context, restrictFace_capOn fun x hx h2 ↦ by
    have := grade_le_one_of_mem_visibleCells hx
    omega]
  exact restrictFace_of_mem _ _ pointFace_mem_topType

/-- Every cell of `S` whose scope lies in `{0}` is dead. -/
private theorem live_eq_false_of_scope : ∀ d : Fin 9, cellScope d ⊆ {0} → live d = false := by
  decide +kernel

/-- **The face on `{0}` is top-free**: its only cell is dead. -/
theorem isTopFree_pointFace : (pointFace α).IsTopFree := fun i hi ↦ by
  -- the label of the root at `i` is that of its cell in `topType α`
  change (topType α).label ((topType α).cellMap pointEmb i) = ⊤ at hi
  have hvis := Scheme.mem_visibleCells.mp ((topType α).cellMap_mem pointEmb i)
  revert hi hvis
  generalize (topType α).cellMap pointEmb i = x
  rcases cases_topType x with rfl | ⟨d, rfl⟩
  · intro _ hvis
    -- the apex has full scope, not inside `{0}`
    have h1 := hvis (mem_coe.mpr (show (1 : Fin 3) ∈ (topType α).toCellScheme.scope apexCell by
      rw [scope_apexCell]
      exact mem_univ _))
    revert h1
    decide
  · intro hi hvis
    rw [label_oldCell] at hi
    have hd : cellScope d ⊆ {0} := by
      intro z hz
      obtain ⟨i, rfl⟩ := hvis (mem_coe.mpr (by rwa [scope_oldCell]))
      obtain rfl : i = 0 := Subsingleton.elim _ _
      decide
    rw [labelling, ite_eq_right (by simp [live_eq_false_of_scope d hd])] at hi
    exact bot_ne_top hi

/-- **The face on `{0, 1}` has a new top of grade `2`**: its cell at `({0, 1}, 2)`, the live cell
`6` of `S`, contains the new point `1` and is labelled `⊤`. -/
theorem exists_new_top_pairFace : ∃ j, Fin.last 1 ∈ (pairFace α).toCellScheme.scope j ∧
    (pairFace α).toCellScheme.grade j = 2 ∧ (pairFace α).label j = ⊤ := by
  have hvis : oldCell (α := α) 6 ∈ (topType α).visibleCells Fin.castSuccEmb := by
    refine Scheme.mem_visibleCells.mpr fun z hz ↦ ?_
    rw [scope_oldCell, mem_coe] at hz
    refine Fin.exists_castSucc_eq.mpr ?_
    revert hz
    revert z
    decide
  obtain ⟨j, hj⟩ : oldCell (α := α) 6 ∈ Set.range ((topType α).cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap]
    exact hvis
  refine ⟨j, ?_, ?_, ?_⟩
  · have hm := Scheme.map_comap_scope (topType α).toScheme Fin.castSuccEmb j
    change ((pairFace α).toCellScheme.scope j).map Fin.castSuccEmb =
      (topType α).toCellScheme.scope ((topType α).cellMap Fin.castSuccEmb j) at hm
    rw [hj, scope_oldCell] at hm
    have h1 : Fin.castSuccEmb (Fin.last 1) ∈ ((pairFace α).toCellScheme.scope j).map
        Fin.castSuccEmb := by
      rw [hm]
      decide
    exact (mem_map' _).mp h1
  · change (topType α).toCellScheme.grade ((topType α).cellMap Fin.castSuccEmb j) = 2
    rw [hj, grade_oldCell]
    rfl
  · change (topType α).label ((topType α).cellMap Fin.castSuccEmb j) = ⊤
    rw [hj, label_oldCell]
    rfl

/-- The face on `{0, 1}` is not top-free. -/
theorem not_isTopFree_pairFace : ¬ (pairFace α).IsTopFree := fun h ↦
  let ⟨j, _, _, hj⟩ := exists_new_top_pairFace (α := α)
  h j hj

/-- **The face on `{0}` is not a rigid core of the face on `{0, 1}`**, at a limit stage: the first
is top-free and the second is not. -/
theorem not_isRigidCoreIn_pairFace (hα : Order.IsSuccLimit α) :
    ¬ (pairFace α).IsRigidCoreIn Fin.castSuccEmb :=
  not_isRigidCoreIn_of_restrictFace_isTopFree hα isLegal_pairFace restrictFace_pairFace
    isTopFree_pointFace not_isTopFree_pairFace

/-- **The context is an anchored context for the face on `{0, 1}`**: `1 + 1 < 3`, its apex, of
graded index `(univ, 3)`, is labelled `c` (capped), above the label `⊥` of every cell of the donor
not labelled `⊤`, and the donor, labelled `⊥` or `⊤`, is anchored vacuously. -/
theorem isAnchoredContext_context : (context hc hcα).IsAnchoredContext (pairFace α) := by
  refine ⟨by omega, apexCell, gradedIndex_apexCell, fun j hj ↦ ?_,
    isAnchored_of_forall_label_eq_bot_or_top _ _ fun j _ ↦ label_topType_eq_bot_or_top _⟩
  -- a label of the face on `{0, 1}` other than `⊤` is `⊥`, below the capped apex
  have hbot : (pairFace α).label j = ⊥ := (label_topType_eq_bot_or_top _).resolve_right hj
  rw [hbot]
  change ⊥ < (if 2 ≤ (topType α).toCellScheme.grade apexCell then
    min ((topType α).label apexCell) c else (topType α).label apexCell)
  rw [ite_eq_left (by rw [grade_apexCell]; omega), label_apexCell,
    min_eq_right le_top]
  exact WithBot.bot_lt_coe _

/-- **The context is an anchored context with a top for the face on `{0, 1}` along `pointEmb`**, at
a limit stage: it is an anchored context, it is not top-free, and the exact pinned extension on
three points (`exists_pinned_extension_of_le_three`) gives a legal one-point coface carrying the
donor; its private top is available by completeness. -/
theorem isAnchoredContextWithTop_context (hα : Order.IsSuccLimit α) :
    (context hc hcα).IsAnchoredContextWithTop pointEmb (pairFace α) := by
  obtain ⟨D', hD', hD't', hD'd⟩ := exists_pinned_extension_of_le_three hα.isSuccPrelimit le_rfl
    (isLegal_context hc hcα) (restrictFace_context hc hcα) isLegal_pairFace restrictFace_pairFace
  exact isAnchoredContextWithTop_iff.mpr ⟨isAnchoredContext_context hc hcα,
    not_isTopFree_context hc hcα, D', ⟨hD', hD't'⟩, hD'd⟩

/-- **The refuting instance**: at a limit stage, the context is a legal anchored context with a
top for the donor `pairFace α` along `pointEmb`, its face along `pointEmb` is the root
`pointFace α`, the donor is a coface of the root in which the root is not a rigid core, and over
the context along `pointEmb` the donor is determined neither within the receiving family of any
coface at any permitted cutoff nor within the stage types on the scheme of any coface: its new top
has grade `2`, above the top grade of the context
(`StageType.not_isDeterminedWithin_receivingFamily_of_topGrade_lt`). -/
theorem exists_not_isDeterminedWithin (hα : Order.IsSuccLimit α) :
    ∃ (t' : StageType.{u} α 3) (t : StageType.{u} α 1),
      t'.IsLegal ∧ t'.IsAnchoredContextWithTop pointEmb (pairFace α) ∧
        restrictFace pointEmb t' = some t ∧ pairFace α ∈ t.cofaces ∧
        ¬ (pairFace α).IsRigidCoreIn Fin.castSuccEmb ∧
        ∀ D' : StageType.{u} α 4, restrictFace Fin.castSuccEmb D' = some t' →
          (∀ δ, IsPermittedCutoff α δ →
            ¬ IsDeterminedWithin (receivingFamily D' δ) t' pointEmb (pairFace α)) ∧
          ¬ IsDeterminedWithin (saturationFamily D'.toScheme) t' pointEmb (pairFace α) := by
  obtain ⟨c, -, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit hα.bot_lt 3
  obtain ⟨j, hjs, hjg, hjt⟩ := exists_new_top_pairFace (α := α)
  have hd : ∃ j, Fin.last 1 ∈ (pairFace α).toCellScheme.scope j ∧
      (context hc hcα).topGrade < (pairFace α).toCellScheme.grade j ∧ (pairFace α).label j = ⊤ :=
    ⟨j, hjs, by have := topGrade_context_le hc hcα; omega, hjt⟩
  exact ⟨context hc hcα, pointFace α, isLegal_context hc hcα,
    isAnchoredContextWithTop_context hc hcα hα,
    restrictFace_context hc hcα, pairFace_mem_cofaces, not_isRigidCoreIn_pairFace hα, fun D' hD' ↦
      ⟨fun _ hδ ↦ not_isDeterminedWithin_receivingFamily_of_topGrade_lt hα hD' hd hδ,
        not_isDeterminedWithin_saturationFamily_of_topGrade_lt hα hD' hd⟩⟩

/-- **Cutoff determination with a donor fails for anchored contexts with a top**, already at `ω`.
This refutes determination for this predicate only. -/
theorem not_cutoffDonorDetermination :
    ¬ CutoffDonorDetermination.{u} fun t' h d ↦ t'.IsAnchoredContextWithTop h d := by
  intro hdet
  obtain ⟨t', t, ht', hP, ht, hd, hnr, hno⟩ :=
    exists_not_isDeterminedWithin Ordinal.isSuccLimit_omega0.{u}
  obtain ⟨D', hD', δ, hδ, hdet'⟩ :=
    hdet.exists_coface t' pointEmb _ Ordinal.isSuccLimit_omega0 ht' hP t ht hd hnr
  exact (hno D' hD'.2).1 δ hδ hdet'

/-! ### A graded context with a top over which determination holds -/

/-- The empty embedding into the two points `{0, 1}`. -/
def emptyEmb : Fin 0 ↪ Fin 2 := Function.Embedding.ofIsEmpty

/-- The face `{2}` is a face of `topType α`. -/
theorem newPoint_mem_topType :
    univ.map (extendByLast emptyEmb) ∈ (topType α).toCellScheme.faces := by
  -- the faces of `topType α` are those of the interval plan
  change univ.map (extendByLast emptyEmb) ∈ Geometry.intervalPlan univ
  decide +kernel

/-- **The face on `{2}`** of `topType α`, a donor over the empty root. -/
noncomputable def newPointFace (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (topType α).comap (extendByLast emptyEmb) newPoint_mem_topType

/-- The face on `{2}` is legal. -/
theorem isLegal_newPointFace : (newPointFace α).IsLegal :=
  isLegal_topType.comap _ newPoint_mem_topType

/-- `topType α` is a legal one-point coface of the face on `{0, 1}`. -/
theorem topType_mem_cofaces : topType α ∈ (pairFace α).cofaces :=
  ⟨isLegal_topType, restrictFace_of_mem _ _ face_mem_topType⟩

/-- The cell of the face on `{0, 1}` at the live cell `6` of `S`, of graded index `(univ, 2)`. -/
theorem exists_cell_six_pairFace : ∃ j : Fin (pairFace α).card,
    (topType α).cellMap Fin.castSuccEmb j = oldCell 6 ∧
      (pairFace α).toCellScheme.gradedIndex j = (univ, 2) ∧ (pairFace α).label j = ⊤ := by
  have hvis : oldCell (α := α) 6 ∈ (topType α).visibleCells Fin.castSuccEmb := by
    refine Scheme.mem_visibleCells.mpr fun z hz ↦ ?_
    rw [scope_oldCell, mem_coe] at hz
    refine Fin.exists_castSucc_eq.mpr ?_
    revert hz
    revert z
    decide
  obtain ⟨j, hj⟩ : oldCell (α := α) 6 ∈ Set.range ((topType α).cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap]
    exact hvis
  have hm := Scheme.map_comap_scope (topType α).toScheme Fin.castSuccEmb j
  change ((pairFace α).toCellScheme.scope j).map Fin.castSuccEmb =
    (topType α).toCellScheme.scope ((topType α).cellMap Fin.castSuccEmb j) at hm
  rw [hj, scope_oldCell] at hm
  have hscope : (pairFace α).toCellScheme.scope j = univ := eq_univ_of_forall fun z ↦ by
    refine (mem_map' Fin.castSuccEmb).mp ?_
    rw [hm]
    revert z
    decide
  refine ⟨j, hj, Prod.ext hscope ?_, ?_⟩
  · change (topType α).toCellScheme.grade ((topType α).cellMap Fin.castSuccEmb j) = 2
    rw [hj, grade_oldCell]
    rfl
  · change (topType α).label ((topType α).cellMap Fin.castSuccEmb j) = ⊤
    rw [hj, label_oldCell]
    rfl

/-- **The face on `{0, 1}` is a graded anchored context with a top for the face on `{2}`** along
the empty embedding: it has more points, its cell at `({0, 1}, 2)` (graded index `(univ, 2)` in
the face) is labelled `⊤`, above every other label, the donor is labelled `⊥` or `⊤`, `topType α`
is a legal coface carrying the donor, and the top grade of the context, `2`, is at least that of
the one-point donor. -/
theorem isGradedTopContext_pairFace :
    (pairFace α).IsGradedTopContext emptyEmb (newPointFace α) := by
  obtain ⟨j, -, hj, hjt⟩ := exists_cell_six_pairFace (α := α)
  refine ⟨isAnchoredContextWithTop_iff.mpr ⟨⟨by omega, j, hj, fun i hi ↦ ?_,
    isAnchored_of_forall_label_eq_bot_or_top _ _ fun i _ ↦ label_topType_eq_bot_or_top _⟩,
    fun htf ↦ htf j hjt, topType α, topType_mem_cofaces,
    restrictFace_of_mem _ _ newPoint_mem_topType⟩, ?_⟩
  · rw [hjt]
    exact lt_top_iff_ne_top.mpr hi
  · have h1 : (newPointFace α).topGrade ≤ 1 := topGrade_le_iff.mpr fun i _ ↦ grade_le _ i
    have h2 : 2 ≤ (pairFace α).topGrade := by
      have := grade_le_topGrade (t := pairFace α) (d := j) hjt
      have hg : (pairFace α).toCellScheme.grade j = 2 := congrArg Prod.snd hj
      rwa [hg] at this
    omega

/-- The cells of `S` whose scope lies in `{2}`: the cell `2`. -/
private theorem eq_two_of_scope : ∀ d : Fin 9, cellScope d ⊆ {2} → d = 2 := by
  decide +kernel

/-- The cells of `S` of graded index `(univ, 2)`: the cell `8`. -/
private theorem eq_eight_of_gradedIndex : ∀ d : Fin 9,
    cells.gradedIndex d = ((univ : Finset (Fin 3)), 2) → d = 8 := by
  decide +kernel

/-- **`topType α` reads its new top visible in `{2}` as a private top**: the only new cell visible
in `{2}` is the live cell `2`, labelled `⊤`, and the only cell of graded index `(univ, 2)`, the live
cell `8`, reads it as it reads the private live cell `6` at `({0, 1}, 2)`, labelled `⊤`: both
entries of its row are the row value `2`. -/
theorem readsAtLeast_topType : ∀ x ∈ (topType α).visibleCells (extendByLast emptyEmb),
    Fin.last 2 ∈ (topType α).toCellScheme.scope x → (topType α).label x = ⊤ →
      ∃ s, Fin.last 2 ∉ (topType α).toCellScheme.scope s ∧ (topType α).label s = ⊤ ∧
        (topType α).ReadsAtLeast s x := by
  refine fun x hx _ _ ↦ ⟨oldCell 6, ?_, ?_, ?_⟩
  · rw [scope_oldCell]
    decide
  · rw [label_oldCell]
    rfl
  -- the visible cell is the cell `2`
  have hvis := Scheme.mem_visibleCells.mp hx
  have hx2 : x = oldCell 2 := by
    rcases cases_topType x with rfl | ⟨d, rfl⟩
    · have h1 := hvis (mem_coe.mpr (show (0 : Fin 3) ∈ (topType α).toCellScheme.scope apexCell by
        rw [scope_apexCell]
        exact mem_univ _))
      obtain ⟨i, hi⟩ := h1
      exact absurd hi (by revert i; decide)
    · have hd : cellScope d ⊆ {2} := by
        intro z hz
        obtain ⟨i, rfl⟩ := hvis (mem_coe.mpr (by rwa [scope_oldCell]))
        obtain rfl : i = 0 := Fin.fin_one_eq_zero i
        decide
      rw [eq_two_of_scope d hd]
  subst hx2
  refine ⟨by rw [grade_oldCell, grade_oldCell]; decide, fun u hu a b ha hb ↦ ?_⟩
  -- the cell of graded index `(univ, 2)` is the cell `8`
  rw [grade_oldCell] at hu
  have hu8 : u = oldCell 8 := by
    rcases cases_topType u with rfl | ⟨d, rfl⟩
    · have := congrArg Prod.snd hu
      change (topType α).toCellScheme.grade apexCell = cellGrade 6 at this
      rw [grade_apexCell] at this
      exact absurd this (by decide)
    · rw [gradedIndex_oldCell] at hu
      rw [eq_eight_of_gradedIndex d hu]
  subst hu8
  obtain ⟨a, ha'⟩ := a
  obtain ⟨b, hb'⟩ := b
  simp only at ha hb
  subst ha hb
  exact le_of_eq rfl

/-- **The face on `{0, 1}` is a reading context for the face on `{2}`** along the empty embedding,
through `topType α` (`readsAtLeast_topType`). -/
theorem isReadingContext_pairFace :
    (pairFace α).IsReadingContext emptyEmb (newPointFace α) :=
  ⟨topType α, topType_mem_cofaces, restrictFace_of_mem _ _ newPoint_mem_topType,
    readsAtLeast_topType⟩

/-- **Determination over a graded context with a top, at a non-rigid donor**: at a limit stage,
the face on `{2}` is a coface of the empty face of the face on `{0, 1}` in which the empty root is
not a rigid core, the face on `{0, 1}` is a graded anchored context with a top for it along the
empty embedding (`StageType.IsGradedTopContext`), and the donor is determined over it within the
receiving family of `topType α` at a permitted cutoff (by
`StageType.isDeterminedWithin_receivingFamily_of_readsAtLeast`).  So the graded predicate is not
refuted by this instance; whether determination holds for it in general is open. -/
theorem exists_isGradedTopContext_isDeterminedWithin (hα : Order.IsSuccLimit α) :
    ∃ t : StageType.{u} α 0, restrictFace emptyEmb (pairFace α) = some t ∧
      newPointFace α ∈ t.cofaces ∧ ¬ (newPointFace α).IsRigidCoreIn Fin.castSuccEmb ∧
      (pairFace α).IsGradedTopContext emptyEmb (newPointFace α) ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily (topType α) δ) (pairFace α) emptyEmb
          (newPointFace α) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((pairFace α).isSome_restrictFace_of_zero emptyEmb)
  obtain ⟨δ, hδα, hδ⟩ := (topType α).exists_lt_forall_label_lt hα
  -- the donor is not top-free: its cell is the live cell `2`
  have hntf : ¬ (newPointFace α).IsTopFree := fun htf ↦ by
    have hvis : oldCell (α := α) 2 ∈ (topType α).visibleCells (extendByLast emptyEmb) := by
      refine Scheme.mem_visibleCells.mpr fun z hz ↦ ?_
      rw [scope_oldCell, mem_coe] at hz
      refine ⟨0, ?_⟩
      revert hz
      revert z
      decide
    obtain ⟨i, hi⟩ : oldCell (α := α) 2 ∈
        Set.range ((topType α).cellMap (extendByLast emptyEmb)) := by
      rw [Scheme.range_cellMap]
      exact hvis
    refine htf i ?_
    change (topType α).label ((topType α).cellMap (extendByLast emptyEmb) i) = ⊤
    rw [hi, label_oldCell]
    rfl
  exact ⟨t, ht, mem_cofaces_of_zero isLegal_newPointFace, fun hr ↦ hntf
    ((isRigidCoreIn_empty_iff_isTopFree hα isLegal_newPointFace Fin.castSuccEmb).mp hr),
    isGradedTopContext_pairFace, δ, isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩,
    isDeterminedWithin_receivingFamily_of_readsAtLeast isLegal_topType
      (restrictFace_of_mem _ _ face_mem_topType) (restrictFace_of_mem _ _ newPoint_mem_topType)
      readsAtLeast_topType hδ⟩

end VaughtConjecture.AvailableTopDeterminationCounterexample

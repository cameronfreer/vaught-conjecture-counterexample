/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrier
import VaughtConjecture.Extension.FieldLayer
import VaughtConjecture.Label.StepWitness

/-!
# Forced tops in the field layer: the top reading does not pass through the canonical completion

Roadmap, Layer 3 ((R3) of the table of 3.4).

A top-reading carrier (`StageType.IsTopReadingCarrier`) asks every cell of graded index
`(univ, N)` labelled `⊤` to read the new tops at least as the marker.  A route to it through the
canonical completion would carry the invariant "a new cell labelled `⊤` for the catalogue entry `e`
has `e x = e r` whenever the input labelling is `⊤` at `x` and at `r`".  The invariant fails, and
for every lawful labelling, not only the canonical one:

* **Forced tops** (`Scheme.eq_top_natAdd_of_le_agreementHeight`, compiled in this repository
  (theorem named)): in a lawful labelling of the field layer, a new cell labelled `⊤`, of catalogue
  entry `b`, and an old cell `x` labelled `⊤` force `⊤` at the new cell of every entry `e` whose
  agreement height with `b` is at least the value `b x` of the entry (the labelling, not the entry,
  is `⊤` at the new cell).  This is `CellScheme.Rows.IsLawful.eq_top_of_row_le`
  at the new cell of `b`, whose row is `b` at the old cells and the agreement heights at the new
  ones.
* **The instance** (`FieldLayerForcedTops.exists_forced_top`, compiled in this repository (theorem
  named)): two old cells of scopes `{0}` and `{1}` and grade `1` on two points, every row `⊤`.  The
  input labelling is `⊤` at both, with code `b = (ω + 1, ω + 1)`, and the catalogue has the entry
  `e = (ω + 1, ω * 3 + 1)`, the code of `(1, ⊤)`, whose agreement height with `b` is at least
  `ω + 1`.  Every lawful labelling of the field layer that is `⊤` at the first old cell and at the
  new cell of `b` is `⊤` at the new cell of `e`, and `e 0 < e 1`.
* **The canonical labelling** (`FieldLayerForcedTops.orbitDecoder_fieldRow_eq_top`, compiled in
  this repository (theorem named)): the labelling of `Scheme.exists_isLawfulBelow_fieldLayer`, the
  orbit decoder at the least grid point applied to the field row of `b`, is `⊤` at the new cell of
  `e`: the cell reading of the first old cell at the agreement height is `⊤`.

So a new cell labelled `⊤` need not have equal values of its entry at two cells where the input is
`⊤`, in the canonical completion or in any completion that labels the new cell of the input's code
`⊤`.  A completion with the top reading has to keep such entries off the catalogue at the tops or
label their new cells below `⊤` by other means (argued, not formalized).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n k : ℕ} {S : Scheme.{u} n}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **Forced tops in the field layer.**  In a lawful labelling `q` of the field layer, if the new
cell of the entry `i` and the old cell `x` (of grade at most `k`) are labelled `⊤`, then the new
cell of every entry `j` whose agreement height with the entry `i` is at least its value at `x` is
labelled `⊤`. -/
theorem eq_top_natAdd_of_le_agreementHeight {q : Fin (S.fieldLayer k hS).card → Label.{u}}
    (hq : (S.fieldLayer k hS).rows.IsLawful q) {i j : Fin (S.catalogue k).card} {x : Fin S.card}
    (hx : S.toCellScheme.grade x ≤ k) (hi : q (Fin.natAdd S.card i) = ⊤)
    (hxq : q (Fin.castAdd _ x) = ⊤)
    (hle : S.catalogueEntry k i x ≤
      agreementHeight (S.fieldGrid k) (S.catalogueEntry k i) (S.catalogueEntry k j)) :
    q (Fin.natAdd S.card j) = ⊤ := by
  have hb : (S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i) =
      ((univ : Finset (Fin n)), k) :=
    appendFullCellsScheme_gradedIndex_natAdd S k _ i
  have hxb : Fin.castAdd _ x ∈
      (S.fieldLayer k hS).toCellScheme.below
        ((S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [hb]
    exact castAdd_mem_below hx
  have hjb : Fin.natAdd S.card j ∈
      (S.fieldLayer k hS).toCellScheme.below
        ((S.fieldLayer k hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [hb]
    exact natAdd_mem_below j
  refine hq.eq_top_of_row_le hxb hjb hi hxq ?_
  rw [fieldLayer_row_natAdd, fieldLayer_row_natAdd, fieldRow_castAdd, fieldRow_natAdd]
  exact hle

end Scheme

namespace FieldLayerForcedTops

open Scheme

/-- Two cells of scopes `{0}` and `{1}` and grade `1` on two points. -/
def twoCells : CellScheme (Fin 2) (Fin 2) := ⟨univ, {∅, {0}, {1}, univ}, fun i ↦ {i}, fun _ ↦ 1⟩

/-- The scheme of `twoCells` with every row `⊤`. -/
abbrev twoScheme : Scheme.{u} 2 := ⟨2, twoCells, ⟨fun _ _ ↦ ⊤⟩⟩

/-- No cell of `twoScheme` lies at or above `(univ, 1)`. -/
theorem not_univ_le : ∀ d, ¬ ((univ : Finset (Fin 2)), 1) ≤ twoScheme.{u}.toCellScheme.gradedIndex d
  | d, h => by
    have hmem := h.1 (mem_univ (d + 1))
    -- the scope of `d` is `{d}`
    change d + 1 ∈ ({d} : Finset (Fin 2)) at hmem
    rw [mem_singleton] at hmem
    revert d
    decide

/-- A cell below another cell of `twoScheme` is that cell. -/
private theorem eq_of_mem_below {s t : Fin 2}
    (ht : t ∈ twoCells.below (twoCells.gradedIndex s)) : t = s :=
  mem_singleton.mp (ht.1 (mem_singleton_self t))

/-- **Every labelling of `twoScheme` self-visible at `1` is lawful.** -/
theorem isLawful_of_isSelfVisible {p : Fin 2 → Label.{u}} (hp : ∀ d, IsSelfVisible 1 (p d)) :
    twoScheme.{u}.rows.IsLawful p where
  orderly d := hp d
  locality s := transformsTo_of_eq_bot_iff _ (K := 1) (fun _ ↦ le_rfl) (hp s) _ _ fun d ↦ by
    rw [eq_of_mem_below d.2, min_self]
    -- the row of `s` is `⊤`
    change _ = if (⊤ : Label.{u}) = ⊥ then ⊥ else p s
    simp
  availability s t hst _ := ⟨t, rfl, by
    rw [mem_singleton.mp (hst (mem_singleton_self s))]⟩

/-- The input labelling: `⊤` at both cells. -/
def topInput : Fin 2 → Label.{u} := fun _ ↦ ⊤

/-- The labelling `(1, ⊤)`. -/
noncomputable def oneTop : Fin 2 → Label.{u} := ![gridPoint 1 0, ⊤]

/-- The splice of the input at `1` with bottom is the input: every cell has grade `1`. -/
theorem splice_topInput :
    twoScheme.{u}.toCellScheme.splice 1 (fun _ ↦ ⊥) topInput.{u} = topInput.{u} :=
  funext fun _ ↦ CellScheme.splice_of_le le_rfl

/-- The value rank of `⊤` for the constant labelling `⊤` is `1`. -/
private theorem valueRank_topInput : valueRank topInput.{u} ⊤ = 1 := by
  have hset : ({y ∈ univ.image topInput.{u} | y ≠ ⊥ ∧ y ≤ ⊤} : Finset Label.{u}) = {⊤} := by
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hy, -, -⟩
      obtain ⟨_, -, rfl⟩ := mem_image.mp hy
      rfl
    · rintro rfl
      exact ⟨mem_image_of_mem _ (mem_univ 0), top_ne_bot, le_rfl⟩
  rw [valueRank, hset, card_singleton]

/-- **The code of the input**: `ω + 1` at both cells. -/
theorem orbitCode_topInput : orbitCode 1 topInput.{u} = fun _ ↦ gridPoint 1 1 := by
  rw [orbitCode_eq_canonicalCode (w := topInput.{u}) fun _ ↦ isSelfVisible_top 1]
  funext d
  rw [canonicalCode_of_ne_bot (w := topInput.{u}) (d := d) (isSelfVisible_top 1) top_ne_bot]
  -- the value of the input at `d` is `⊤`
  change canonicalPoint 1 (valueRank topInput.{u} (⊤ : Label.{u})) = _
  rw [valueRank_topInput]
  rfl

/-- `oneTop` is strictly increasing. -/
private theorem strictMono_oneTop : StrictMono oneTop.{u} := by
  intro i j hij
  have hi : i = 0 := by omega
  have hj : j = 1 := by omega
  subst hi hj
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

/-- `oneTop` is never `⊥`. -/
private theorem oneTop_ne_bot : ∀ i, oneTop.{u} i ≠ ⊥ :=
  Fin.forall_fin_two.mpr ⟨gridPoint_ne_bot 1 0, WithBot.coe_ne_bot⟩

/-- The value rank of the value of `oneTop` at `i` is `i + 1`. -/
private theorem valueRank_oneTop (i : Fin 2) : valueRank oneTop.{u} (oneTop i) = i + 1 := by
  have hset : ({y ∈ univ.image oneTop.{u} | y ≠ ⊥ ∧ y ≤ oneTop.{u} i} : Finset Label.{u}) =
      (Iic i).image oneTop.{u} := by
    ext y
    simp only [mem_filter, mem_image, mem_univ, true_and, mem_Iic]
    constructor
    · rintro ⟨⟨j, rfl⟩, -, hj⟩
      exact ⟨j, strictMono_oneTop.le_iff_le.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, oneTop_ne_bot j, strictMono_oneTop.monotone hj⟩
  rw [valueRank, hset, card_image_of_injective _ strictMono_oneTop.injective, Fin.card_Iic]

/-- `oneTop` is self-visible at `1`. -/
private theorem isSelfVisible_oneTop : ∀ i, IsSelfVisible 1 (oneTop.{u} i) :=
  Fin.forall_fin_two.mpr ⟨isSelfVisible_gridPoint 1 0, isSelfVisible_top 1⟩

/-- **The code of `(1, ⊤)`**: `ω * (2 i + 1) + 1` at the cell `i`, so `(ω + 1, ω * 3 + 1)`. -/
theorem orbitCode_oneTop (i : Fin 2) :
    orbitCode 1 oneTop.{u} i = gridPoint 1 (2 * i + 1) := by
  rw [orbitCode_eq_canonicalCode isSelfVisible_oneTop,
    canonicalCode_of_ne_bot (isSelfVisible_oneTop i) (oneTop_ne_bot i), valueRank_oneTop,
    canonicalPoint]
  congr 1

/-- The code of the input is in the catalogue at the grade `1`. -/
theorem orbitCode_topInput_mem :
    orbitCode 1 topInput.{u} ∈ twoScheme.{u}.catalogue 1 := by
  have h := orbitCode_splice_bot_mem_catalogue (S := twoScheme.{u}) (k := 1)
    ((isLawful_of_isSelfVisible (p := topInput.{u}) fun _ ↦ isSelfVisible_top 1).isLawfulBelow
      ((univ : Finset (Fin 2)), 1))
  rwa [splice_topInput] at h

/-- The code of `(1, ⊤)` is in the catalogue at the grade `1`. -/
theorem orbitCode_oneTop_mem : orbitCode 1 oneTop.{u} ∈ twoScheme.{u}.catalogue 1 := by
  rw [orbitCode_eq_canonicalCode isSelfVisible_oneTop]
  exact canonicalCode_mem_catalogue (S := twoScheme.{u}) (p := oneTop.{u}) (fun _ ↦ rfl)
    (isLawful_of_isSelfVisible isSelfVisible_oneTop)

/-- The agreement height of the two codes in the field grid is at least `ω + 1`. -/
theorem gridPoint_le_agreementHeight :
    gridPoint 1 1 ≤ agreementHeight (twoScheme.{u}.fieldGrid 1) (orbitCode 1 topInput.{u})
      (orbitCode 1 oneTop.{u}) := by
  refine le_agreementHeight (mem_grid.mpr (Or.inr ⟨1, by omega, rfl⟩)) fun d ↦ ?_
  rw [orbitCode_topInput, orbitCode_oneTop, min_self,
    min_eq_right (gridPoint_le_gridPoint.mpr (by omega))]

/-- **The forced top.**  The field layer of `twoScheme` at the grade `1` has new cells `i` (the
code `b = (ω + 1, ω + 1)` of the input `⊤`) and `j` (the code `e = (ω + 1, ω * 3 + 1)` of
`(1, ⊤)`) with `e 0 < e 1`, such that every lawful labelling of the field layer that is `⊤` at the
first old cell and at the new cell `i` is `⊤` at the new cell `j`. -/
theorem exists_forced_top :
    ∃ i j : Fin (twoScheme.{u}.catalogue 1).card,
      twoScheme.{u}.catalogueEntry 1 i = orbitCode 1 topInput.{u} ∧
      twoScheme.{u}.catalogueEntry 1 j = orbitCode 1 oneTop.{u} ∧
      twoScheme.{u}.catalogueEntry 1 j 0 < twoScheme.{u}.catalogueEntry 1 j 1 ∧
      ∀ q, (twoScheme.{u}.fieldLayer 1 not_univ_le).rows.IsLawful q →
        q (Fin.castAdd _ 0) = ⊤ → q (Fin.natAdd twoScheme.{u}.card i) = ⊤ →
          q (Fin.natAdd twoScheme.{u}.card j) = ⊤ := by
  obtain ⟨i, hi⟩ := exists_catalogueEntry_eq orbitCode_topInput_mem.{u}
  obtain ⟨j, hj⟩ := exists_catalogueEntry_eq orbitCode_oneTop_mem.{u}
  refine ⟨i, j, hi, hj, ?_, fun q hq h0 hiq ↦
    eq_top_natAdd_of_le_agreementHeight hq (x := 0) le_rfl hiq h0 ?_⟩
  · rw [hj, orbitCode_oneTop, orbitCode_oneTop]
    exact gridPoint_lt_gridPoint.mpr (by simp)
  · rw [hi, hj]
    exact (congrFun orbitCode_topInput 0).le.trans gridPoint_le_agreementHeight

/-- **The canonical labelling has the forced top.**  The labelling of
`Scheme.exists_isLawfulBelow_fieldLayer` for the input `⊤` (the orbit decoder of the splice at the
least grid point, applied to the field row of its code) is `⊤` at the new cell of the code of
`(1, ⊤)`, whose values at the two cells differ. -/
theorem orbitDecoder_fieldRow_eq_top {j : Fin (twoScheme.{u}.catalogue 1).card}
    (hj : twoScheme.{u}.catalogueEntry 1 j = orbitCode 1 oneTop.{u}) :
    orbitDecoder 1 (twoScheme.{u}.toCellScheme.splice 1 (fun _ ↦ ⊥) topInput.{u}) (gridPoint 1 0)
      (twoScheme.{u}.fieldRow 1
        (orbitCode 1 (twoScheme.{u}.toCellScheme.splice 1 (fun _ ↦ ⊥) topInput.{u}))
        (Fin.natAdd _ j)) = ⊤ := by
  rw [splice_topInput, fieldRow_natAdd, hj]
  set a := agreementHeight (twoScheme.{u}.fieldGrid 1) (orbitCode 1 topInput) (orbitCode 1 oneTop)
  have ha : gridPoint 1 1 ≤ a := gridPoint_le_agreementHeight
  have hmem : (0 : Fin 2) ∈
      ({d | gridPoint 1 0 ≤ visibilityReplace 1 1 (orbitCode 1 topInput.{u} d)} :
        Finset (Fin 2)) := by
    rw [mem_filter, orbitCode_topInput, isSelfVisible_gridPoint 1 1]
    exact ⟨mem_univ _, gridPoint_le_gridPoint.mpr (by omega)⟩
  have hread : cellReading 1 topInput.{u} 0 a = ⊤ := by
    have hnot : ¬ IsOrbitKey 1 topInput.{u} (topInput.{u} 0) := fun ⟨_, _, he⟩ ↦
      he (isSelfVisible_top 1)
    have hle : visibilityReplace 1 1 (orbitCode 1 topInput.{u} 0) ≤ visibilityReplace 1 1 a := by
      rw [orbitCode_topInput, isSelfVisible_gridPoint 1 1, ← isSelfVisible_gridPoint.{u} 1 1]
      exact monotone_visibilityReplace le_rfl ha
    rw [cellReading, ite_eq_right (not_lt.mpr hle), ite_eq_right fun h ↦ hnot h.2]
    rfl
  refine top_unique (le_max_of_le_right ?_)
  rw [← hread]
  exact le_sup (f := fun d ↦ cellReading 1 topInput.{u} d a) hmem

end FieldLayerForcedTops

end VaughtConjecture

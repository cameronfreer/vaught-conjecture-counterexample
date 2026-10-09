/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedServingCell

/-!
# Agreement heights stopping at a value of the catalogue

Roadmap, Layer 3 ((R3) and (R4), the agreement heights of the ladder tower).

The agreement heights of the ladder tower over the attachment range over the height set
(`Scheme.heightSet Γ B' k`: the grid at `k` and the values of `Γ` self-visible at `k`).  With the
grid alone two writings agreeing capped at a value `y` of finite part above `k` are separated only
at a grid point below `y`, so a cell whose state breaks a tie of the ambient above the grid points
has its writing value below `y` (the obstruction of an ambient tied inside a block).  With `y` a
height the tie is broken (`Scheme.LadderBaseData.exists_cell_le_v_of_capAgree`).

* **Ranks and tables capped at `y`** (`Label.rankAgree_of_min_eq`, `Label.min_valueTable_eq`,
  `Label.min_posTable_eq`): two labellings agreeing capped at `y ≠ ⊥` agree in rank below
  `lowCount + 1` (one more than the number of their positive values below `y`), their value tables
  agree capped at `y` at every index, and their positive tables agree capped at `y` at indices
  agreeing up to `lowCount + 1`.
* **Agreement heights capped at a height** (`Label.min_agreementHeight_eq_of_mem`): for `y` a
  height, two labellings agreeing capped at `y` have agreement heights with a third agreeing
  capped at `y`.
* **Writings capped at `y`** (`Scheme.LadderBaseData.min_stateExt_eq`,
  `Scheme.LadderBaseData.min_v_eq_of_capAgree`): two states agreeing capped at a value `y ≠ ⊥` of
  `Γ` have writings agreeing capped at `y` at every height `K` with `y` self-visible at `K + 1`.
* **The cell above the tie** (`Scheme.exists_layerTower_cell_of_mem_v`,
  `Scheme.LadderBaseData.exists_cell_le_v_of_capAgree`): the cell of a state `R` of the catalogue
  at `k + 2` carries the writing of every `R'` agreeing with `R` capped at `y` (self-visible at
  `k + 2`) at a value at least `y`; it reads `R` on the base, so it separates whatever `R`
  separates.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

variable {ι : Type*} [Fintype ι] {Z Z' : ι → Label.{u}} {y : Label.{u}}

/-- The number of positive values of `Z` below `y`. -/
noncomputable def lowCount (Z : ι → Label.{u}) (y : Label.{u}) : ℕ :=
  #((univ.image Z).filter fun w ↦ w ≠ ⊥ ∧ w < y)

omit [Fintype ι] in
theorem eq_of_capAgree_of_lt (hag : ∀ d, min (Z' d) y = min (Z d) y) {d : ι} (h : Z d < y) :
    Z' d = Z d := by
  have e := hag d
  rw [min_eq_left h.le] at e
  rcases le_total (Z' d) y with hle | hle
  · rwa [min_eq_left hle] at e
  · rw [min_eq_right hle] at e; exact absurd e h.ne'

omit [Fintype ι] in
theorem lt_iff_of_capAgree (hag : ∀ d, min (Z' d) y = min (Z d) y) (d : ι) :
    Z' d < y ↔ Z d < y :=
  ⟨fun h ↦ eq_of_capAgree_of_lt (fun d ↦ (hag d).symm) h ▸ h,
    fun h ↦ (eq_of_capAgree_of_lt hag h).symm ▸ h⟩

/-- The positive values below `y` of two labellings agreeing capped at `y` are the same. -/
theorem filter_image_eq (hag : ∀ d, min (Z' d) y = min (Z d) y) {v : Label.{u}}
    (hv : v < y) :
    (univ.image Z').filter (fun w ↦ w ≠ ⊥ ∧ w ≤ v) =
      (univ.image Z).filter fun w ↦ w ≠ ⊥ ∧ w ≤ v := by
  ext w
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨e, rfl⟩, h0, hw⟩
    have he := eq_of_capAgree_of_lt (fun d ↦ (hag d).symm) (hw.trans_lt hv)
    exact ⟨⟨e, he⟩, h0, hw⟩
  · rintro ⟨⟨e, rfl⟩, h0, hw⟩
    exact ⟨⟨e, eq_of_capAgree_of_lt hag (hw.trans_lt hv)⟩, h0, hw⟩

theorem lowCount_eq (hag : ∀ d, min (Z' d) y = min (Z d) y) : lowCount Z' y = lowCount Z y := by
  unfold lowCount
  congr 1
  ext w
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨e, rfl⟩, h0, hw⟩
    exact ⟨⟨e, eq_of_capAgree_of_lt (fun d ↦ (hag d).symm) hw⟩, h0, hw⟩
  · rintro ⟨⟨e, rfl⟩, h0, hw⟩
    exact ⟨⟨e, (eq_of_capAgree_of_lt hag hw)⟩, h0, hw⟩

/-- A cell below `y` has the same rank in two labellings agreeing capped at `y`. -/
theorem rankVector_eq_of_lt (hag : ∀ d, min (Z' d) y = min (Z d) y) {d : ι} (h : Z d < y) :
    rankVector Z' d = rankVector Z d := by
  unfold rankVector valueRank
  rw [eq_of_capAgree_of_lt hag h, filter_image_eq hag h]

/-- A cell of value at least `y ≠ ⊥` has rank above the number of positive values below `y`. -/
theorem lowCount_lt_rankVector (hy0 : y ≠ ⊥) {d : ι} (h : y ≤ Z d) :
    lowCount Z y < rankVector Z d := by
  classical
  unfold lowCount rankVector valueRank
  refine card_lt_card ⟨fun w hw ↦ ?_, fun hsub ↦ ?_⟩
  · obtain ⟨hwZ, h0, hwy⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨hwZ, h0, hwy.le.trans h⟩
  · have := hsub (mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ d),
      fun h0 ↦ hy0 (le_bot_iff.mp (h0 ▸ h)), le_rfl⟩)
    exact absurd (mem_filter.mp this).2.2 (not_lt.mpr h)

/-- A cell below `y` has rank at most the number of positive values below `y`. -/
theorem rankVector_le_lowCount {d : ι} (h : Z d < y) : rankVector Z d ≤ lowCount Z y := by
  classical
  unfold lowCount rankVector valueRank
  exact card_le_card fun w hw ↦ by
    obtain ⟨hwZ, h0, hwd⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨hwZ, h0, hwd.trans_lt h⟩

/-- A cell of least value at least `y ≠ ⊥` has rank exactly one more than the number of positive
values below `y`. -/
theorem rankVector_eq_of_min (hy0 : y ≠ ⊥) {d : ι} (h : y ≤ Z d)
    (hmin : ∀ e, y ≤ Z e → Z d ≤ Z e) : rankVector Z d = lowCount Z y + 1 := by
  classical
  refine le_antisymm ?_ (lowCount_lt_rankVector hy0 h)
  unfold lowCount rankVector valueRank
  refine (card_le_card (show _ ⊆ insert (Z d) ((univ.image Z).filter fun w ↦ w ≠ ⊥ ∧ w < y)
    from fun w hw ↦ ?_)).trans (card_insert_le _ _)
  obtain ⟨hwZ, h0, hwd⟩ := mem_filter.mp hw
  obtain ⟨e, -, rfl⟩ := mem_image.mp hwZ
  rcases lt_or_ge (Z e) y with he | he
  · exact mem_insert_of_mem (mem_filter.mpr ⟨hwZ, h0, he⟩)
  · rw [le_antisymm hwd (hmin e he)]; exact mem_insert_self _ _

/-- **Two labellings agreeing capped at `y ≠ ⊥` agree in rank below one more than the number of
their positive values below `y`.** -/
theorem rankAgree_of_min_eq (hag : ∀ d, min (Z' d) y = min (Z d) y) (hy0 : y ≠ ⊥) :
    RankAgree (rankVector Z') (rankVector Z) (lowCount Z y + 1) := by
  intro d
  rcases lt_or_ge (Z d) y with h | h
  · rw [rankVector_eq_of_lt hag h]
  · have h' : y ≤ Z' d :=
      not_lt.mp fun h' ↦ absurd ((lt_iff_of_capAgree hag d).mp h') (not_lt.mpr h)
    have e1 := lowCount_lt_rankVector hy0 h'
    rw [lowCount_eq hag] at e1
    rw [min_eq_right e1, min_eq_right (lowCount_lt_rankVector hy0 h)]

/-- **Above the rank `lowCount + 1` the value table capped at `y` is constant.** -/
theorem min_valueTable_eq_of_le (hy0 : y ≠ ⊥) {i : ℕ} (hi : lowCount Z y + 1 ≤ i) :
    min (valueTable Z i) y = min (valueTable Z (lowCount Z y + 1)) y := by
  classical
  by_cases hhigh : ∃ e, y ≤ Z e
  · -- a least value at least `y` has rank `lowCount + 1`
    obtain ⟨e, he, hmin⟩ := (univ.filter fun e ↦ y ≤ Z e).exists_min_image Z
      (let ⟨e, he⟩ := hhigh; ⟨e, mem_filter.mpr ⟨mem_univ _, he⟩⟩)
    have he' := (mem_filter.mp he).2
    have hre := rankVector_eq_of_min hy0 he' fun e' h' ↦ hmin e' (mem_filter.mpr ⟨mem_univ _, h'⟩)
    have hy (j : ℕ) (hj : lowCount Z y + 1 ≤ j) : y ≤ valueTable Z j :=
      he'.trans (Finset.le_sup (f := Z) (mem_filter.mpr ⟨mem_univ _, by
        change rankVector Z e ≤ j; omega⟩))
    rw [min_eq_right (hy i hi), min_eq_right (hy _ le_rfl)]
  · push Not at hhigh
    have hall (j : ℕ) (hj : lowCount Z y ≤ j) :
        valueTable Z j = univ.sup Z := by
      unfold valueTable
      congr 1
      exact filter_true_of_mem fun e _ ↦ (rankVector_le_lowCount (hhigh e)).trans hj
    rw [hall i (by omega), hall _ (by omega)]

/-- The positive table capped at `y ≥ 1` is that of the value table. -/
theorem min_posTable_eq_max (hy1 : (1 : Label.{u}) ≤ y) (i : ℕ) (hi : i ≠ 0) :
    min (posTable Z i) y = max (min (valueTable Z i) y) 1 := by
  unfold posTable
  rw [ite_eq_right hi]
  rcases le_total (valueTable Z i) y with h | h
  · rw [min_eq_left h, min_eq_left (max_le h hy1)]
  · rw [min_eq_right h, min_eq_right (le_max_of_le_left h), max_eq_left hy1]

/-- A least value at least `y ≠ ⊥`, if any, lies in the value table from the index
`lowCount + 1` on. -/
theorem le_valueTable_of_high (hy0 : y ≠ ⊥) {e : ι} (he : y ≤ Z e) {i : ℕ}
    (hi : lowCount Z y + 1 ≤ i) : y ≤ valueTable Z i := by
  classical
  obtain ⟨e', he', hmin⟩ := (univ.filter fun e ↦ y ≤ Z e).exists_min_image Z
    ⟨e, mem_filter.mpr ⟨mem_univ _, he⟩⟩
  have he'' := (mem_filter.mp he').2
  have hre := rankVector_eq_of_min hy0 he'' fun e₁ h₁ ↦ hmin e₁ (mem_filter.mpr ⟨mem_univ _, h₁⟩)
  exact he''.trans (Finset.le_sup (f := Z) (mem_filter.mpr ⟨mem_univ _, by
    change rankVector Z e' ≤ i; omega⟩))

/-- One half of the agreement of the value tables capped at `y`. -/
theorem min_valueTable_le (hag : ∀ d, min (Z' d) y = min (Z d) y) (hy0 : y ≠ ⊥) (i : ℕ) :
    min (valueTable Z' i) y ≤ min (valueTable Z i) y := by
  classical
  by_cases hY : y ≤ valueTable Z i
  · rw [min_eq_right hY]; exact min_le_right _ _
  refine min_le_min_right _ ?_
  unfold valueTable
  refine Finset.sup_le fun e he ↦ ?_
  have hei := (mem_filter.mp he).2
  rcases lt_or_ge (Z e) y with h | h
  · rw [eq_of_capAgree_of_lt hag h]
    refine Finset.le_sup (f := Z) (mem_filter.mpr ⟨mem_univ _, ?_⟩)
    change rankVector Z e ≤ i
    rw [← rankVector_eq_of_lt hag h]; exact hei
  · have h' : y ≤ Z' e :=
      not_lt.mp fun h' ↦ absurd ((lt_iff_of_capAgree hag e).mp h') (not_lt.mpr h)
    have hlt := lowCount_lt_rankVector hy0 h'
    rw [lowCount_eq hag] at hlt
    exact absurd (le_valueTable_of_high hy0 h (i := i)
      (by change rankVector Z' e ≤ i at hei; omega)) hY

/-- **The value tables of two labellings agreeing capped at `y ≠ ⊥` agree capped at `y`.** -/
theorem min_valueTable_eq (hag : ∀ d, min (Z' d) y = min (Z d) y) (hy0 : y ≠ ⊥) (i : ℕ) :
    min (valueTable Z' i) y = min (valueTable Z i) y :=
  le_antisymm (min_valueTable_le hag hy0 i) (min_valueTable_le (fun d ↦ (hag d).symm) hy0 i)

/-- The positive table capped at `y` depends on the index only up to `lowCount + 1`. -/
theorem min_posTable_eq_min_index (hy0 : y ≠ ⊥) (hy1 : (1 : Label.{u}) ≤ y) (i : ℕ) :
    min (posTable Z i) y = min (posTable Z (min i (lowCount Z y + 1))) y := by
  rcases le_total i (lowCount Z y + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, min_posTable_eq_max hy1 _ (by omega),
      min_posTable_eq_max hy1 _ (by omega), min_valueTable_eq_of_le hy0 h]

/-- **The positive tables of two labellings agreeing capped at `y ≥ 1` agree capped at `y`** at
indices agreeing capped at `lowCount + 1`. -/
theorem min_posTable_eq (hag : ∀ d, min (Z' d) y = min (Z d) y) (hy1 : (1 : Label.{u}) ≤ y)
    {i i' : ℕ} (hii : min i' (lowCount Z y + 1) = min i (lowCount Z y + 1)) :
    min (posTable Z' i') y = min (posTable Z i) y := by
  have hy0 : y ≠ ⊥ := fun h ↦ by rw [h] at hy1; exact absurd hy1 (by simp)
  rw [min_posTable_eq_min_index hy0 hy1 i', min_posTable_eq_min_index hy0 hy1 i, lowCount_eq hag,
    hii]
  set j := min i (lowCount Z y + 1)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, posTable_zero, posTable_zero]
  · rw [min_posTable_eq_max hy1 _ hpos.ne', min_posTable_eq_max hy1 _ hpos.ne',
      min_valueTable_eq hag hy0]

omit [Fintype ι] in
/-- Agreement capped at `x ≤ y` transfers along an agreement capped at `y`. -/
theorem capAgree_trans {a a' e : ι → Label.{u}} {x : Label.{u}}
    (hag : ∀ d, min (a' d) y = min (a d) y) (hxy : x ≤ y) (h : ∀ d, min (a' d) x = min (e d) x) :
    ∀ d, min (a d) x = min (e d) x := fun d ↦ by
  have e1 : min (a d) x = min (min (a d) y) x := by rw [min_assoc, min_eq_right hxy]
  have e2 : min (a' d) x = min (min (a' d) y) x := by rw [min_assoc, min_eq_right hxy]
  rw [e1, ← hag, ← e2, h]

/-- **Agreement heights capped at a height `y` of `G`**: two labellings agreeing capped at `y`
have agreement heights with any third labelling agreeing capped at `y`. -/
theorem min_agreementHeight_eq_of_mem {G : Finset Label.{u}} (hG0 : ⊥ ∈ G) (hyG : y ∈ G)
    {a a' : ι → Label.{u}} (hag : ∀ d, min (a' d) y = min (a d) y) (e : ι → Label.{u}) :
    min (agreementHeight G a' e) y = min (agreementHeight G a e) y := by
  have hag' : ∀ d, min (a d) y = min (a' d) y := fun d ↦ (hag d).symm
  obtain ⟨-, h'⟩ := agreementHeight_spec hG0 a' e
  obtain ⟨-, h⟩ := agreementHeight_spec hG0 a e
  -- a height at least `y` on one side gives `y` on the other
  have up {b b' : ι → Label.{u}} (hbb : ∀ d, min (b' d) y = min (b d) y)
      (hb' : ∀ d, min (b' d) (agreementHeight G b' e) = min (e d) (agreementHeight G b' e))
      (hy : y ≤ agreementHeight G b' e) : y ≤ agreementHeight G b e :=
    le_agreementHeight hyG (capAgree_trans hbb le_rfl fun d ↦ by
      have := congrArg (min · y) (hb' d)
      simp only [min_assoc, min_eq_right hy] at this
      exact this)
  rcases le_or_gt y (agreementHeight G a' e) with h1 | h1
  · rw [min_eq_right h1, min_eq_right (up hag h' h1)]
  rcases le_or_gt y (agreementHeight G a e) with h2 | h2
  · exact absurd (up hag' h h2) (not_le.mpr h1)
  rw [min_eq_left h1.le, min_eq_left h2.le]
  exact le_antisymm (le_agreementHeight (agreementHeight_spec hG0 a' e).1
      (capAgree_trans hag h1.le h'))
    (le_agreementHeight (agreementHeight_spec hG0 a e).1 (capAgree_trans hag' h2.le h))

end Label

namespace Scheme

variable {n : ℕ} {σ : Type*} {B : LayerTower.{u} n σ 0} {C : ℕ → Finset σ}
  {G : ℕ → Finset Label.{u}}

/-- **The cell of a state and the writings there**: for a state `R` of `C (k + 2)`, at every
height `K ≥ k + 1` some cell at `(univ, k + 2)` reads the writing of `R` on the base, and every
state is written there as the agreement height of its writing with that of `R` at the height
`k`. -/
theorem exists_layerTower_cell_of_mem_v (k : ℕ) {R : σ} (hR : R ∈ C (k + 2)) :
    ∀ K, k + 1 ≤ K → ∃ u : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) ∧
      (∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ k + 2 →
        (layerTower B C G K).S.rowAt u (layerTowerEmb K t) = B.v R t) ∧
      ∀ R' : σ, (layerTower B C G K).v R' u =
        agreementHeight (G (k + 2)) ((layerTower B C G k).v R') ((layerTower B C G k).v R) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    set T := layerTower B C G k with hT
    classical
    obtain ⟨i, hi⟩ := exists_layerEntry_eq (C := T.entries (C (k + 2)))
      (mem_image_of_mem T.v hR)
    refine ⟨Fin.natAdd _ i, ?_, fun t ht ↦ ?_, fun R' ↦ ?_⟩
    · change (T.S.appendFullCellsScheme (k + 2) _).gradedIndex (Fin.natAdd _ i) = _
      rw [appendFullCellsScheme_gradedIndex_natAdd]
    · have hgt : T.S.toCellScheme.grade (layerTowerEmb k t) ≤ k + 2 := by
        have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t k)
        change T.S.toCellScheme.grade (layerTowerEmb k t) = B.S.toCellScheme.grade t at this
        omega
      change (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
        T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (layerTowerEmb k t)) = _
      rw [rowAt_catalogueLayer_castAdd i hgt, hi]
      exact layerTower_v_emb R t k
    · change layerRow T.S (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2))) (T.v R')
        (Fin.natAdd _ i) = _
      rw [layerRow_natAdd, hi]
  | succ K hK ih =>
    set T := layerTower B C G K with hT
    obtain ⟨u, hu, hrow, hv⟩ := ih
    refine ⟨Fin.castAdd _ u, ?_, fun t ht ↦ ?_, fun R' ↦ ?_⟩
    · change (T.S.appendFullCellsScheme (K + 2) _).gradedIndex (Fin.castAdd _ u) = _
      rw [appendFullCellsScheme_gradedIndex_castAdd]
      exact hu
    · change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
        T.not_le).rowAt (Fin.castAdd _ u) (Fin.castAdd _ (layerTowerEmb K t)) = _
      rw [rowAt_appendFullCells_castAdd]
      exact hrow t ht
    · change layerRow T.S (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2))) (T.v R')
        (Fin.castAdd _ u) = _
      rw [layerRow_castAdd]
      exact hv R'

end Scheme

namespace Scheme.LadderBaseData

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin B.S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The extensions of two states agreeing capped at `y` agree capped at `y`** on the padded base:
on the ladder the indices of their rank members agree up to `lowCount + 1`, through the cut of the
two rank vectors (`Scheme.baseIndex_agree`, `Label.rankAgree_of_min_eq`), and the positive tables
agree capped at `y` there (`Label.min_posTable_eq`). -/
theorem min_stateExt_eq (hcard : B.S.card ≤ H) {y : Label.{u}} (hy0 : y ≠ ⊥)
    (hy1 : IsSelfVisible 1 y) {R R' : Fin B.S.card → Label.{u}} (hR : B.S.rows.IsLawful R)
    (hR' : B.S.rows.IsLawful R') (hag : ∀ d, min (R' d) y = min (R d) y)
    (t : Fin (B.ladderBase H).card) :
    min (B.stateExt H R' t) y = min (B.stateExt H R t) y := by
  rw [stateExt_of_isLawful hR hcard, stateExt_of_isLawful hR' hcard]
  induction t using Fin.addCases with
  | left d => rw [Fin.append_left, Fin.append_left]; exact hag d
  | right j =>
    rw [Fin.append_right, Fin.append_right]
    set a := RankMember.ofLawful B.wf hcard hR with ha
    set a' := RankMember.ofLawful B.wf hcard hR' with ha'
    set L := lowCount R y with hL
    have hag' : RankAgree (rankProf B.S H a') (rankProf B.S H a) (L + 1) :=
      rankAgree_of_min_eq hag hy0
    have hcut := baseIndex_agree (H := H) (prof := rankProf B.S H) a' a (Fin.natAdd _ j)
    have hle (b : RankMember B.S H) : baseIndex H (rankProf B.S H) b (Fin.natAdd _ j) ≤ H :=
      baseIndex_le (rankProf_le _ H) b _
    refine min_posTable_eq hag (one_le_of_isSelfVisible hy1 hy0) ?_
    rcases le_or_gt (L + 1) H with hLH | hLH
    · have hc : L + 1 ≤ rankCut H (rankProf B.S H a') (rankProf B.S H a) := le_rankCut hLH hag'
      have e := congrArg (min · (L + 1)) hcut
      simp only [min_assoc, min_eq_right hc] at e
      exact e
    · have hc : H ≤ rankCut H (rankProf B.S H a') (rankProf B.S H a) :=
        le_rankCut le_rfl (hag'.mono hLH.le)
      rw [min_eq_left ((hle a').trans hc), min_eq_left ((hle a).trans hc)] at hcut
      rw [hcut]

/-- **The writings of two states agreeing capped at a value `y` of `Γ` agree capped at `y`** at
every height `K` with `y` self-visible at `K + 1`: on the padded base by `min_stateExt_eq`, and on
every layer through the agreement heights, `y` being a height there
(`Label.min_agreementHeight_eq_of_mem`). -/
theorem min_v_eq_of_capAgree (hcard : B.S.card ≤ H) {y : Label.{u}} (hyΓ : y ∈ Γ) (hy0 : y ≠ ⊥)
    {R R' : Fin B.S.card → Label.{u}} (hR : B.S.rows.IsLawful R) (hR' : B.S.rows.IsLawful R')
    (hag : ∀ d, min (R' d) y = min (R d) y) :
    ∀ K, IsSelfVisible (K + 1) y → ∀ x,
      min ((B.ladderTower H Γ A B' K).v R' x) y = min ((B.ladderTower H Γ A B' K).v R x) y
  | 0, hy, x => min_stateExt_eq hcard hy0 hy hR hR' hag x
  | K + 1, hy, x => by
    have ih := min_v_eq_of_capAgree hcard hyΓ hy0 hR hR' hag K (hy.mono (by omega))
    set T := B.ladderTower H Γ A B' K with hT
    change min (layerRow T.S (fun d ↦ d) (heightSet Γ B' (K + 2))
        (T.entries (B.towerCat Γ A (K + 2))) (T.v R') x) y =
      min (layerRow T.S (fun d ↦ d) (heightSet Γ B' (K + 2))
        (T.entries (B.towerCat Γ A (K + 2))) (T.v R) x) y
    induction x using Fin.addCases with
    | left x => rw [layerRow_castAdd, layerRow_castAdd]; exact ih x
    | right i =>
      rw [layerRow_natAdd, layerRow_natAdd]
      exact min_agreementHeight_eq_of_mem (bot_mem_heightSet _ _ _)
        (mem_heightSet.mpr (.inr ⟨hyΓ, hy⟩)) ih _

/-- **The tie is broken by the height set** (tower form): for a state `R` of the catalogue at
`k + 2` and a lawful state `R'` agreeing with it capped at a value `y ≠ ⊥` of `Γ` self-visible at
`k + 2`, at every height `K ≥ k + 1` some cell at `(univ, k + 2)` reads `R` on the base and the
ladder, and the writing of `R'` there is at least `y`: `y` is a height at the grade `k + 2`, and
the writings of `R'` and `R` agree capped at `y` below (`min_v_eq_of_capAgree`).  With heights in
the grid alone, `y` (of finite part above `k + 2`) is not a height. -/
theorem exists_cell_le_v_of_capAgree (hcard : B.S.card ≤ H) {k K : ℕ} (hK : k + 1 ≤ K)
    {y : Label.{u}} (hyΓ : y ∈ Γ) (hy0 : y ≠ ⊥) (hyv : IsSelfVisible (k + 2) y)
    {R R' : Fin B.S.card → Label.{u}} (hRC : R ∈ B.towerCat Γ A (k + 2))
    (hR' : B.S.rows.IsLawful R') (hag : ∀ d, min (R' d) y = min (R d) y) :
    ∃ (u : Fin (B.ladderTower H Γ A B' K).S.card) (hR : B.S.rows.IsLawful R),
      (B.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin n)), k + 2) ∧
      (∀ d : Fin B.S.card, B.S.toCellScheme.grade d ≤ k + 2 →
        (B.ladderTower H Γ A B' K).S.rowAt u (B.towerEmb K (Fin.castAdd _ d)) = R d) ∧
      (∀ p, (B.ladderTower H Γ A B' K).S.rowAt u
          (B.towerEmb K (Fin.natAdd _ (ladderEquiv _ _ H p))) =
        posTable R (baseIndex H (rankProf B.S H)
          (RankMember.ofLawful B.wf hcard hR)
          (Fin.natAdd _ (ladderEquiv _ _ H p)))) ∧
      y ≤ (B.ladderTower H Γ A B' K).v R' u := by
  have hRl := (mem_towerCat.mp hRC).2.1
  obtain ⟨u, hu, hrow, hv⟩ := Scheme.exists_layerTower_cell_of_mem_v (B := B.towerBase H)
    (C := B.towerCat Γ A) (G := fun k ↦ heightSet Γ B' k) k hRC K hK
  refine ⟨u, hRl, hu, fun d hd ↦ ?_, fun p ↦ ?_, ?_⟩
  · have h := hrow (Fin.castAdd _ d) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k + 2
      rw [appendFullCellsScheme_grade_castAdd]; exact hd)
    exact h.trans (stateExt_castAdd hRl hcard d)
  · have h := hrow (Fin.natAdd _ (ladderEquiv _ _ H p)) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.natAdd _ _) ≤ k + 2
      rw [appendFullCellsScheme_grade_natAdd]; omega)
    exact h.trans
      (stateExt_of_grade_one hRl hcard _ (appendFullCellsScheme_grade_natAdd _ _ _ _))
  · rw [hv R']
    exact le_agreementHeight (mem_heightSet.mpr (.inr ⟨hyΓ, hyv⟩))
      (min_v_eq_of_capAgree hcard hyΓ hy0 hRl hR' hag k (hyv.mono (by omega)))

end Scheme.LadderBaseData

end VaughtConjecture

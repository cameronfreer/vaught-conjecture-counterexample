/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Encoders
import VaughtConjecture.Extension.ProfileTowerCompletion

/-!
# Strong coding of the completion of a seed

Roadmap, Layer 3, 3.1, (R6) (the coatom extension construction) and Correspondence, item 1 (the
legal templates of [AFK26]); semantic contract, item 3.

The range clause of the legal templates of [AFK26, Definition "legal"] (its last clause: every
entry of the row of a cell `d` is `-∞` or `ω · n + i` with `i ≤ g(d) + 1`) is the strong coding of
the rows (`CellScheme.Rows.IsStronglyCoded`).  Legality here (`Scheme.IsLegal`) imposes only the
range normalization `Scheme.IsCoded`, and is not changed.  This file proves that the construction
of the coatom extension keeps strong coding: every row it inherits is a row of its inputs, and
every row it builds is strongly coded at the grade of its cell, the apex row once the block coding
of the labels is replaced by the strongly coded encoder.

* **Labels.**  A label of the code grid at the grade `k` is strongly coded at `k`
  (`Label.isStronglyCoded_of_mem_codeGrid`): its finite part is at most `k`.
* **Restriction.**  Strong coding passes to every restriction (`Scheme.isStronglyCoded_comap`), and
  a cell visible through `f` is strongly coded when the restriction along `f` is
  (`Scheme.isStronglyCodedAt_of_comap`).
* **Appended cells.**  Appending cells of full scope whose rows are strongly coded at their grade
  keeps strong coding (`Scheme.isStronglyCoded_appendFullCells`,
  `Scheme.isStronglyCoded_appendFullCell`); so does the canonical field layer, whose new rows take
  their values in the code grid (`Scheme.isStronglyCoded_fieldLayer`).
* **The seed.**  The amalgam of two strongly coded coatom types is strongly coded
  (`Seed.isStronglyCoded_amalgam`): every cell has a proper face as its scope, which lies in a
  coatom.  Then the tower (`Seed.isStronglyCoded_tower`), the levels
  (`ProfileTower.Lvl.Good.isStronglyCoded_next`, `ProfileTower.isStronglyCoded_lvl`), and the
  completion below the full grade of `Seed.nonempty_completionBelowFullGrade` are strongly coded
  (`Seed.exists_completionBelowFullGrade_isStronglyCoded`).
* **The apex.**  The row of the apex of `StageType.addApex` is the block coding of the labels
  (`Label.blockEncode`), which keeps the finite part of every label; the labels of a stage type
  are bounded below in finite part by self-visibility, not above, so that row need not be strongly
  coded.  The **strongly coded apex** (`StageType.addStrongApex`) takes as its row the strongly
  coded encoding of the labels (`StageType.strongApexRow`, from `Label.strongEncode`), strongly
  coded at the full grade (`StageType.isStronglyCoded_strongApexRow`).  It is lawful
  (`StageType.isLawful_strongApexRow`, since the encoder is a bottom-reflecting witness bounded by
  the full grade), the decoder transforms it back to the labels
  (`StageType.isLawful_apexLabel_strongApexRow`), and the result is legal
  (`StageType.isLegal_addStrongApex`), strongly coded when `t` is
  (`StageType.isStronglyCoded_addStrongApex`), has the apex (`StageType.exists_apex_addStrongApex`),
  and has the proper faces of `t`
  (`StageType.restrictFace_addStrongApex`).

The coatom extension property and amalgamation within the strongly coded legal stage types are in
`VaughtConjecture.Extension.StronglyCodedAmalgamation`.

## References

The range clause is that of [AFK26, Definition "legal"]; the offset bound of [Kni26, Lemma 2.5.13]
is the same bound.  The amalgam is [Kni26, Definition 4.3.1] and the apex that of
[Kni26, Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The code grid is strongly coded -/

namespace Label

variable {k B : ℕ} {x : Label.{u}}

/-- A member of the code grid at grade `k` is strongly coded at `k`: its finite part is at most
`k`. -/
theorem isStronglyCoded_of_mem_codeGrid (hx : x ∈ codeGrid k B) : IsStronglyCoded k x := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, -, f, hf, rfl⟩
  · exact isStronglyCoded_bot k
  · exact .inr ⟨b, f, by omega, rfl⟩

end Label

/-! ### Restriction, appended cells, and field layers -/

namespace Scheme

variable {n m : ℕ}

/-- **Strong coding passes to the restriction** along any embedding of points. -/
theorem isStronglyCoded_comap {S : Scheme.{u} n} (hS : S.rows.IsStronglyCoded)
    (f : Fin m ↪ Fin n) : (S.comap f).rows.IsStronglyCoded :=
  hS.comap (S.isLowerEmbedding_comap f)

/-- **A visible cell is strongly coded when the restriction is**: the row of the cell
`S.cellMap f i` is the row of `i` in the restriction, read through the cell map. -/
theorem isStronglyCodedAt_cellMap {S : Scheme.{u} n} {f : Fin m ↪ Fin n}
    (h : (S.comap f).rows.IsStronglyCoded) (i : Fin (S.comap f).card) :
    S.rows.IsStronglyCodedAt (S.cellMap f i) := fun t ↦ by
  obtain ⟨t', -, ht'⟩ := CellScheme.Rows.exists_row_eq_of_isLowerEmbedding
    (S.isLowerEmbedding_comap f) rfl i t
  rw [ht']
  exact h i t'

/-- **A cell visible through `f` is strongly coded when the restriction along `f` is.** -/
theorem isStronglyCodedAt_of_comap {S : Scheme.{u} n} {f : Fin m ↪ Fin n}
    (h : (S.comap f).rows.IsStronglyCoded) {d : Fin S.card} (hd : d ∈ S.visibleCells f) :
    S.rows.IsStronglyCodedAt d := by
  obtain ⟨i, rfl⟩ : d ∈ Set.range (S.cellMap f) := by rwa [range_cellMap]
  exact isStronglyCodedAt_cellMap h i

variable {S : Scheme.{u} n} {k M : ℕ} {r : Fin M → Fin (S.card + M) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **Appending cells keeps strong coding** when the new rows, of grade `k`, are strongly coded
at `k`. -/
theorem isStronglyCoded_appendFullCells (hS : S.rows.IsStronglyCoded)
    (hr : ∀ i d, IsStronglyCoded k (r i d)) : (S.appendFullCells k M r h).rows.IsStronglyCoded := by
  intro s t
  induction s using Fin.addCases with
  | right i =>
    rw [appendFullCells_row_natAdd i t]
    exact (appendFullCellsScheme_grade_natAdd S k M i).symm ▸ hr i _
  | left s =>
    rw [appendFullCells_row_castAdd]
    exact (appendFullCellsScheme_grade_castAdd S k M s).symm ▸ hS s _

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **The canonical field layer keeps strong coding**: its new rows, of grade `k`, take their
values in the code grid at `k`. -/
theorem isStronglyCoded_fieldLayer (hc : S.rows.IsStronglyCoded) :
    (S.fieldLayer k hS).rows.IsStronglyCoded :=
  isStronglyCoded_appendFullCells hc fun i x ↦
    isStronglyCoded_of_mem_codeGrid (fieldRow_mem_codeGrid (catalogueEntry_mem i) x)

end Scheme

/-! ### The amalgam and the tower of a seed -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **The amalgam of two strongly coded coatom types is strongly coded**: every cell of the
amalgam has a proper face as its scope, which lies in one of the two coatoms, and the restrictions
of the amalgam to the coatoms are the two coatom types. -/
theorem isStronglyCoded_amalgam (hl : I.left.rows.IsStronglyCoded)
    (hr : I.right.rows.IsStronglyCoded) : I.amalgam.rows.IsStronglyCoded := by
  intro d
  have hface : I.amalgam.toCellScheme.scope d ∈ I.amalgam.toCellScheme.faces :=
    (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).1
  rcases I.subset_or_subset _ hface (I.scope_ne_univ d) with hsub | hsub
  · refine Scheme.isStronglyCodedAt_of_comap (f := Coatom.left m) ?_ ?_
    · rw [StageType.comap_toScheme_of_restrictFace I.restrictFace_left]
      exact hl
    · rw [Scheme.visibleCells, mem_filter, Coatom.univ_map_left]
      exact ⟨mem_univ _, hsub⟩
  · refine Scheme.isStronglyCodedAt_of_comap (f := Coatom.right m) ?_ ?_
    · rw [StageType.comap_toScheme_of_restrictFace I.restrictFace_right]
      exact hr
    · rw [Scheme.visibleCells, mem_filter, Coatom.univ_map_right]
      exact ⟨mem_univ _, hsub⟩

/-- **Every scheme of the tower is strongly coded** when the amalgam is. -/
theorem isStronglyCoded_tower (h : I.amalgam.rows.IsStronglyCoded) :
    (j : ℕ) → (I.tower j).rows.IsStronglyCoded
  | 0 => h
  | j + 1 => Scheme.isStronglyCoded_fieldLayer (hS := I.not_univ_succ_le_tower j)
      (isStronglyCoded_tower h j)

end Seed

/-! ### The levels -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {L : Lvl I g}

/-- **The next level keeps strong coding**: its new rows, of grade `g + 1`, take their values in
the code grid at `g + 1`. -/
theorem Lvl.Good.isStronglyCoded_next (hL : L.Good) (h : L.S.rows.IsStronglyCoded) :
    L.next.S.rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_appendFullCells (h := L.not_le) h fun i d ↦
    isStronglyCoded_of_mem_codeGrid (hL.Φ_mem_codeGrid (mem_codeGrid_of_mem_cat (entry_mem i)) d)

/-- **Every good level is strongly coded** when the amalgam is. -/
theorem isStronglyCoded_lvl (hm : 2 ≤ m) (h : I.amalgam.rows.IsStronglyCoded) :
    (j : ℕ) → j + 2 ≤ m → (lvl I j).S.rows.IsStronglyCoded
  | 0, _ => I.isStronglyCoded_tower h 2
  | j + 1, hj => (lvl_good hm j (by omega)).isStronglyCoded_next
      (isStronglyCoded_lvl hm h j (by omega))

end ProfileTower

/-! ### The completion below the full grade -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **A strongly coded completion below the full grade**: every seed whose amalgam is strongly
coded has a completion below the full grade whose scheme is strongly coded.  It is the completion
of `Seed.nonempty_completionBelowFullGrade`: the tower at `m ≤ 2`, and the top field layer over
the levels at `m ≥ 3`; every new row takes its values in the code grid at its grade. -/
theorem exists_completionBelowFullGrade_isStronglyCoded (h : I.amalgam.rows.IsStronglyCoded) :
    ∃ F : CompletionBelowFullGrade I, F.scheme.rows.IsStronglyCoded := by
  rcases le_or_gt m 2 with hm | hm
  · exact ⟨I.completionBelowFullGradeOfTowerInvariant (I.towerInvariant_of_twoFaceLift
      (I.forall_twoFaceLift_of_two_le fun j hj hjm ↦ absurd hjm (by omega)) (m + 1) le_rfl),
      I.isStronglyCoded_tower h (m + 1)⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    have hL := ProfileTower.lvl_good (I := I) (by omega) j (by omega)
    exact ⟨(hL.next (by omega)).completion hL.hasBotExtension_next (by omega),
      Scheme.isStronglyCoded_fieldLayer (hS := (ProfileTower.lvl I j).next.not_le)
        (hL.isStronglyCoded_next (ProfileTower.isStronglyCoded_lvl (by omega) h j (by omega)))⟩

end Seed

/-! ### Appending one cell, and the strongly coded apex -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- **Appending one cell keeps strong coding** when its row is strongly coded at its grade `j`. -/
theorem isStronglyCoded_appendFullCell (hS : S.rows.IsStronglyCoded)
    (hr : ∀ d, IsStronglyCoded j (r d)) : (S.appendFullCell j r h).rows.IsStronglyCoded := by
  intro s t
  induction s using Fin.lastCases with
  | last =>
    rw [appendFullCell_row_last t]
    exact (appendFullCellScheme_grade_last S j).symm ▸ hr _
  | cast s =>
    obtain ⟨t', -, ht'⟩ := CellScheme.Rows.exists_row_eq_of_isLowerEmbedding
      (isLowerEmbedding_castSucc j r h) comap_rows_castSucc s t
    rw [ht']
    exact (appendFullCellScheme_grade_castSucc S j s).symm ▸ hS s t'

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {t : StageType.{u} α n}

variable (t) in
open Classical in
/-- The labels coded by the strongly coded apex row: the labels of `t` and the formal top. -/
noncomputable def strongApexCodes : Finset Label.{u} := insert ⊤ (univ.image t.label)

/-- Every label of `t` is among the labels coded by the strongly coded apex row. -/
theorem label_mem_strongApexCodes (d : Fin t.card) : t.label d ∈ t.strongApexCodes := by
  classical
  exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ d))

/-- The formal top is among the labels coded by the strongly coded apex row. -/
theorem top_mem_strongApexCodes : (⊤ : Label.{u}) ∈ t.strongApexCodes := by
  classical
  exact mem_insert_self _ _

variable (t) in
/-- The **strongly coded apex row**: the strongly coded encoding at the grade `n` of the labels of
`t`, and the code of the formal top at the apex itself.  Its values are strongly coded at `n`
(`Label.isStronglyCoded_strongEncode`). -/
noncomputable def strongApexRow : Fin (t.card + 1) → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) (strongEncode t.strongApexCodes n ∘ t.label)
    (strongEncode t.strongApexCodes n ⊤)

/-- The strongly coded apex row at an old cell. -/
@[simp] theorem strongApexRow_castSucc (d : Fin t.card) :
    t.strongApexRow d.castSucc = strongEncode t.strongApexCodes n (t.label d) :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The strongly coded apex row at the apex. -/
@[simp] theorem strongApexRow_last :
    t.strongApexRow (Fin.last _) = strongEncode t.strongApexCodes n ⊤ :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- The strongly coded apex row is strongly coded at `n`. -/
theorem isStronglyCoded_strongApexRow (d : Fin (t.card + 1)) :
    IsStronglyCoded n (t.strongApexRow d) := by
  induction d using Fin.lastCases with
  | last => rw [strongApexRow_last]; exact isStronglyCoded_strongEncode _
  | cast d => rw [strongApexRow_castSucc]; exact isStronglyCoded_strongEncode _

variable (ht : t.IsLegalBelowFullGrade)

/-- **The strongly coded apex row is lawful**: on the old cells it is the encoded section of the
labels, lawful since the encoder is a bottom-reflecting witness bounded by `n`; at the apex it is
the code of the formal top, above every code. -/
theorem isLawful_strongApexRow :
    (t.toScheme.appendFullCell n t.strongApexRow ht.not_le).rows.IsLawful t.strongApexRow := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful.strongEncode (V := t.strongApexCodes) (K := n)
      (fun d ↦ (ht.grade_lt d).le) using 1
    funext d
    exact strongApexRow_castSucc d
  · rw [strongApexRow_last]
    exact isSelfVisible_strongEncode (isSelfVisible_top n)
  · convert TransformsTo.refl _ t.strongApexRow using 1
    funext d
    refine min_eq_left ?_
    rw [strongApexRow_last]
    induction d using Fin.lastCases with
    | last => rw [strongApexRow_last]
    | cast d => rw [strongApexRow_castSucc]; exact monotone_strongEncode le_top

/-- **The labels with the apex are lawful for the strongly coded apex row**: the decoder, a
witness bounded by `n`, transforms the apex row back to the labels, with the formal top at the
apex. -/
theorem isLawful_apexLabel_strongApexRow :
    (t.toScheme.appendFullCell n t.strongApexRow ht.not_le).rows.IsLawful (apexLabel (t := t)) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact apexLabel_castSucc d
  · rw [apexLabel_last]
    exact isSelfVisible_top n
  · refine ⟨stepSuppressor n, strongDecode t.strongApexCodes n, isWitness_strongDecode,
      fun d ↦ ?_⟩
    beta_reduce
    rw [apexLabel_last, min_top_right, stepSuppressor_of_le
      (ht.grade_appendFullCellScheme_le d), min_top_right]
    induction d using Fin.lastCases with
    | last =>
      rw [apexLabel_last, strongApexRow_last, strongDecode_strongEncode top_mem_strongApexCodes]
    | cast d =>
      rw [apexLabel_castSucc, strongApexRow_castSucc,
        strongDecode_strongEncode (label_mem_strongApexCodes d)]

variable (hn : 0 < n)

/-- **Adding the strongly coded apex** to a stage type legal below the full grade: as
`StageType.addApex`, one cell of full scope and full grade `n` appended last and labelled with the
formal top, but whose row is the strongly coded encoding of the labels (`StageType.strongApexRow`)
in place of their block coding, which keeps the finite parts of the labels. -/
noncomputable def addStrongApex : StageType.{u} α n where
  toScheme := t.toScheme.appendFullCell n t.strongApexRow ht.not_le
  label := apexLabel
  isWellFormed := Scheme.isWellFormed_appendFullCell t.isWellFormed hn le_rfl
  isCoded := Scheme.isCoded_appendFullCell t.isCoded fun d ↦
    (isStronglyCoded_strongApexRow d).lt_omega0_sq
  isLawful := isLawful_apexLabel_strongApexRow ht
  atStage d := by
    induction d using Fin.lastCases with
    | last => rw [apexLabel_last]; exact atStage_top
    | cast d => rw [apexLabel_castSucc]; exact t.atStage d

/-- **Adding the strongly coded apex gives a legal stage type.** -/
theorem isLegal_addStrongApex : (t.addStrongApex ht hn).IsLegal :=
  isLegal_iff.mpr ⟨Scheme.isConsistent_appendFullCell ht.isConsistent (isLawful_strongApexRow ht),
    Scheme.isBountiful_appendFullCell (h := ht.not_le) ht.isBountiful,
    Scheme.isComplete_appendFullCell (h := ht.not_le) ht.exists_gradedIndex_eq⟩

/-- **Adding the strongly coded apex keeps strong coding.** -/
theorem isStronglyCoded_addStrongApex (h : t.rows.IsStronglyCoded) :
    (t.addStrongApex ht hn).rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_appendFullCell (h := ht.not_le) h isStronglyCoded_strongApexRow

/-- **The strongly coded apex**: the new cell has full scope and full grade `n`, and carries the
largest label, the formal top. -/
theorem exists_apex_addStrongApex :
    ∃ d, (t.addStrongApex ht hn).toCellScheme.gradedIndex d = (univ, n) ∧
      ∀ e, (t.addStrongApex ht hn).label e ≤ (t.addStrongApex ht hn).label d :=
  ⟨Fin.last _, Scheme.appendFullCellScheme_gradedIndex_last _ _,
    fun _ ↦ by change _ ≤ apexLabel (Fin.last _); rw [apexLabel_last]; exact le_top⟩

/-- **The proper faces after adding the strongly coded apex are those of `t`**, including
definedness. -/
theorem restrictFace_addStrongApex (f : Fin m ↪ Fin n) (hf : univ.map f ≠ univ) :
    restrictFace f (t.addStrongApex ht hn) = restrictFace f t := by
  refine restrictFace_eq_of_strictMono (t := t.addStrongApex ht hn) (s := t) f
    (φ := (Fin.castSucc : Fin t.card → Fin (t.card + 1))) Fin.strictMono_castSucc
    (Scheme.isLowerEmbedding_castSucc n t.strongApexRow ht.not_le)
    (Scheme.appendFullCellScheme_scope_castSucc _ _) (Scheme.comap_rows_castSucc (h := ht.not_le))
    rfl rfl (fun d ↦ apexLabel_castSucc d) fun z hz ↦ ?_
  induction z using Fin.lastCases with
  | last =>
    refine absurd (eq_univ_of_forall fun x ↦ ?_) hf
    obtain ⟨y, rfl⟩ : x ∈ Set.range f :=
      hz (mem_coe.mpr ((Scheme.appendFullCellScheme_scope_last _ _).symm ▸ mem_univ x))
    exact mem_map_of_mem _ (mem_univ y)
  | cast z => exact ⟨z, rfl⟩

end StageType

end VaughtConjecture

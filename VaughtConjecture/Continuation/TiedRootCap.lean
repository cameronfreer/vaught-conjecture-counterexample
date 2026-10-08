/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.RaisedNewTops

/-!
# A cap whose row separates tied root cells

Roadmap, Layer 3 ((R3) of the table of 3.4).

A marked-cap context with top cap `c` and marker `r`, a donor `d` and a lawful labelling `a` of
the context with `a r = a c = ⊤` meet the refutation schema of `VaughtConjecture.Continuation.
RaisedNewTops` when a new top of `d` ties two root cells that `a` inverts.  Under an apex the
schema never applies (`StageType.le_of_tie_addApex`).  This file isolates what the schema needs of
the cap and gives the tools for a legal instance (`VaughtConjecture.Continuation.
TiedRootCapCounterexample`).

* **The collapsing shifter** (`Label.collapseShifter`, `Label.isWitness_collapseShifter`, compiled
  in this repository (theorem named)): the map keeping `⊥` and `⊤` and sending every other label
  to a label `v` self-visible at `K` is a witness bounded by grade `K`; it sends only `⊥` to `⊥`
  and only `⊤` to `⊤`.
* **The coded cap** (`StageType.addCodedCap`, `StageType.isLegal_addCodedCap`, compiled): over a
  stage type `t` legal below the full grade, a lawful labelling `ℓ` whose coded copy relative to
  `V` is lawful gives a legal stage type with one more cell of full scope and full grade, labelled
  `⊤`, whose row is the coded copy of `ℓ` (`StageType.codedRow`).  Its labels are lawful when
  `t.label = κ ∘ ℓ` for a witness `κ` bounded by the full grade that fixes `⊤` and sends only `⊥`
  to `⊥` (`StageType.isLawful_apexLabel_codedScheme`), and `ℓ` with `⊤` at the new cell is lawful
  (`StageType.isLawful_topExtension`).  The proper faces are those of `t`
  (`StageType.restrictFace_addCodedCap`, `StageType.faceCell_addCodedCap`).  The apex
  (`StageType.addApex`) is the case `ℓ = t.label`.
* **Rows keeping the root ties** (`StageType.KeepsRootTies`, defined here): at two cells visible
  through `h`, the second of grade at most the first, labels in order give row values of `c` in
  the same order.  Where the row of a cap of full scope keeps the root ties, every lawful
  labelling with `⊤` at the cap keeps them (`StageType.le_of_keepsRootTies`), so the schema never
  applies with `s = c` (`StageType.le_of_tie_of_keepsRootTies`, compiled); the apex keeps them
  (`StageType.keepsRootTies_addApex`, compiled).  This is a sufficient exclusion property for the
  schema at the top cap, not a sufficient condition for the raise.
* **The raise in the bottom class** (`StageType.RaisesNewTopsInClass`, defined here): the raise
  requirement asked only at the lawful labellings `⊥` exactly where the labels of the context are.
  The schema refutes it when the inverting labelling is in the bottom class
  (`StageType.not_raisesNewTopsInClass_of_row_le`, compiled).  **Correctness at cap and marker
  `⊤` forces it** (`StageType.raisesNewTopsInClass_of_correct`, compiled): if in a legal
  one-point extension `D` carrying `d`, at every cell of graded index `(univ, N)` labelled `⊤` by
  a lawful labelling of `D` whose part on the context is in the bottom class and `⊤` at `r` and
  `s` (of grade `N`), that labelling is `⊤` at the new tops of `d`, then the raise holds in the
  bottom class.  This is the step "bountifulness at the cap `⊥`, availability, recognition,
  correctness" of a capped admission whose class is the bottom pattern of the context, with the
  recognition and correctness clauses stated as one hypothesis.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The collapsing shifter -/

namespace Label

open Classical in
/-- The **collapsing shifter** at `v`: it keeps `⊥` and the formal top and sends every other
label to `v`. -/
noncomputable def collapseShifter (v x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else if x = ⊤ then ⊤ else v

variable {v x : Label.{u}}

theorem collapseShifter_bot : collapseShifter v ⊥ = ⊥ := ite_eq_left rfl

theorem collapseShifter_top : collapseShifter v ⊤ = ⊤ := by
  simp [collapseShifter]

theorem collapseShifter_of_ne (hb : x ≠ ⊥) (ht : x ≠ ⊤) : collapseShifter v x = v := by
  simp [collapseShifter, hb, ht]

/-- The collapsing shifter sends a label to `⊥` only if it is `⊥`. -/
theorem eq_bot_of_collapseShifter_eq_bot (hv : v ≠ ⊥) (h : collapseShifter v x = ⊥) : x = ⊥ := by
  by_contra hb
  by_cases ht : x = ⊤
  · rw [ht, collapseShifter_top] at h
    exact top_ne_bot h
  · exact hv ((collapseShifter_of_ne hb ht).symm.trans h)

/-- The collapsing shifter sends a label to `⊤` only if it is `⊤`. -/
theorem eq_top_of_collapseShifter_eq_top (hv : v ≠ ⊤) (h : collapseShifter v x = ⊤) : x = ⊤ := by
  by_contra ht
  by_cases hb : x = ⊥
  · rw [hb, collapseShifter_bot] at h
    exact bot_ne_top h
  · exact hv ((collapseShifter_of_ne hb ht).symm.trans h)

/-- **The collapsing shifter is a witness bounded by grade `K`** when `v` is self-visible at `K`
and is not `⊥`. -/
theorem isWitness_collapseShifter {K : ℕ} (hv : IsSelfVisible K v) (hvb : v ≠ ⊥) :
    IsWitness (stepSuppressor.{u} K) (collapseShifter v) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := collapseShifter_bot
  monotone a b hab := by
    by_cases ha : a = ⊥
    · rw [ha, collapseShifter_bot]
      exact bot_le
    have hb : b ≠ ⊥ := fun hb ↦ ha (le_bot_iff.mp (hb ▸ hab))
    by_cases hbt : b = ⊤
    · rw [hbt, collapseShifter_top]
      exact le_top
    have hat : a ≠ ⊤ := fun hat ↦ hbt (top_le_iff.mp (hat ▸ hab))
    rw [collapseShifter_of_ne ha hat, collapseShifter_of_ne hb hbt]
  visibilityReplace_comm y k hy i hi := by
    induction y using recBotCoeTop with
    | bot => simp [collapseShifter_bot]
    | top => simp [collapseShifter_top]
    | coe o =>
      have h₁ : (o : Label.{u}) ≠ ⊥ := WithBot.coe_ne_bot
      have h₂ : (o : Label.{u}) ≠ ⊤ := by simp
      rw [collapseShifter_of_ne h₁ h₂] at hy ⊢
      rw [visibilityReplace_coe, collapseShifter_of_ne WithBot.coe_ne_bot (by simp)]
      rcases le_or_gt k K with hk | hk
      · exact ((hv.mono hk).visibilityReplace_eq i).symm
      · rw [stepSuppressor_of_lt hk, le_bot_iff] at hy
        exact absurd hy hvb

end Label

/-! ### Old cells of a proper face after appending a cell of full scope -/

namespace Scheme

variable {n m : ℕ} {S : Scheme.{u} n} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- After appending a cell of full scope, the cells visible through a proper face are old. -/
theorem mem_range_castSucc_of_appendFullCell (f : Fin m ↪ Fin n) (hf : univ.map f ≠ univ)
    (z : Fin (S.appendFullCell j r h).card)
    (hz : ((S.appendFullCell j r h).toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f) :
    z ∈ Set.range (Fin.castSucc : Fin S.card → Fin (S.card + 1)) := by
  induction z using Fin.lastCases with
  | last =>
    refine absurd (eq_univ_of_forall fun x ↦ ?_) hf
    obtain ⟨y, rfl⟩ : x ∈ Set.range f :=
      hz (mem_coe.mpr ((appendFullCellScheme_scope_last S j).symm ▸ mem_univ x))
    exact mem_map_of_mem _ (mem_univ y)
  | cast z => exact ⟨z, rfl⟩

/-- **The cells of a proper face after appending a cell of full scope are the old ones.** -/
theorem faceCell_appendFullCell (f : Fin m ↪ Fin n) (hf : univ.map f ≠ univ)
    {T : Scheme.{u} m} (he : S.comap f = T) (he' : (S.appendFullCell j r h).comap f = T)
    (i : Fin T.card) :
    (S.appendFullCell j r h).faceCell f he' i = (S.faceCell f he i).castSucc :=
  cellMap_eq_of_strictMono_of_mem_range (S := S) (T := S.appendFullCell j r h) f
    (φ := Fin.castSucc) Fin.strictMono_castSucc (appendFullCellScheme_scope_castSucc S j)
    (mem_range_castSucc_of_appendFullCell f hf) rfl

end Scheme

/-! ### A full cell carrying the code of a lawful labelling -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
  (V : Finset Label.{u}) (ℓ : Fin t.card → Label.{u})

/-- The **coded row** of a labelling `ℓ` of the cells of `t`: its coded copy relative to `V` at the
threshold `n`, and the code of the formal top at one more cell. -/
noncomputable def codedRow : Fin (t.card + 1) → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) (blockEncode V n ∘ ℓ) (blockEncode V n ⊤)

@[simp] theorem codedRow_castSucc (d : Fin t.card) :
    codedRow V ℓ d.castSucc = blockEncode V n (ℓ d) :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

@[simp] theorem codedRow_last : codedRow V ℓ (Fin.last _) = blockEncode V n ⊤ :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- The scheme of `t` with one cell of full scope and full grade `n` whose row is the coded row of
`ℓ`. -/
noncomputable abbrev codedScheme : Scheme.{u} n :=
  t.toScheme.appendFullCell n (codedRow V ℓ) ht.not_le

/-- The labelling `ℓ` with the formal top at one more cell. -/
def topExtension : Fin (t.card + 1) → Label.{u} := Fin.snoc (α := fun _ ↦ Label.{u}) ℓ ⊤

@[simp] theorem topExtension_castSucc (d : Fin t.card) : topExtension ℓ d.castSucc = ℓ d :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

@[simp] theorem topExtension_last : topExtension ℓ (Fin.last _) = ⊤ :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

variable {V ℓ}

/-- **The coded row is lawful** when the coded copy of `ℓ` is. -/
theorem isLawful_codedRow (hℓ : t.rows.IsLawful (blockEncode V n ∘ ℓ)) :
    (codedScheme ht V ℓ).rows.IsLawful (codedRow V ℓ) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert hℓ using 1
    funext d
    exact codedRow_castSucc V ℓ d
  · rw [codedRow_last]
    exact isSelfVisible_blockEncode_top le_rfl
  · convert TransformsTo.refl _ (codedRow V ℓ) using 1
    funext d
    refine min_eq_left ?_
    rw [codedRow_last]
    induction d using Fin.lastCases with
    | last => rw [codedRow_last]
    | cast d => rw [codedRow_castSucc]; exact blockEncode_le_blockEncode_top _

/-- **The labelling `ℓ` with the formal top at the new cell is lawful**: the block decoding
transforms the coded row back to `ℓ`, and the code of the formal top to the formal top. -/
theorem isLawful_topExtension (hℓ : t.rows.IsLawful ℓ) (hV : ∀ d, ℓ d ∈ V) :
    (codedScheme ht V ℓ).rows.IsLawful (topExtension ℓ) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert hℓ using 1
    funext d
    exact topExtension_castSucc ℓ d
  · rw [topExtension_last]
    exact isSelfVisible_top n
  · refine ⟨fun _ ↦ ⊤, blockDecode V, isWitness_blockDecode, fun d ↦ ?_⟩
    beta_reduce
    rw [topExtension_last, min_top_right, min_top_right]
    induction d using Fin.lastCases with
    | last => rw [topExtension_last, codedRow_last, blockDecode_blockEncode_top]
    | cast d => rw [topExtension_castSucc, codedRow_castSucc, blockDecode_blockEncode (hV d)]

/-- **The labels of `t` with the formal top at the new cell are lawful** when they collapse `ℓ`:
`t.label = κ ∘ ℓ` for a witness `κ` bounded by grade `n` fixing the formal top and sending only
`⊥` to `⊥`. -/
theorem isLawful_apexLabel_codedScheme {κ : Label.{u} → Label.{u}}
    (hκ : IsWitness (stepSuppressor n) κ) (hκb : ∀ x, κ x = ⊥ → x = ⊥) (hκt : κ ⊤ = ⊤)
    (hV : ∀ d, ℓ d ∈ V) (hlab : ∀ d, t.label d = κ (ℓ d)) :
    (codedScheme ht V ℓ).rows.IsLawful (apexLabel (t := t)) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact apexLabel_castSucc d
  · rw [apexLabel_last]
    exact isSelfVisible_top n
  · have hbd : IsWitness (stepSuppressor.{u} n) (blockDecode V) := isWitness_blockDecode.truncate n
    refine ⟨stepSuppressor n, κ ∘ blockDecode V,
      hbd.comp_of_bot_reflecting hκ fun x hx ↦ hκb _ hx, fun d ↦ ?_⟩
    have hg : (t.toScheme.appendFullCellScheme n).grade d ≤ n :=
      ht.grade_appendFullCellScheme_le d
    beta_reduce
    rw [stepSuppressor_of_le hg, min_top_right, apexLabel_last, min_top_right]
    induction d using Fin.lastCases with
    | last =>
      rw [apexLabel_last, Function.comp_apply, codedRow_last, blockDecode_blockEncode_top, hκt]
    | cast d =>
      rw [apexLabel_castSucc, Function.comp_apply, codedRow_castSucc,
        blockDecode_blockEncode (hV d), hlab]

variable (hn : 0 < n) (hlab : (codedScheme ht V ℓ).rows.IsLawful (apexLabel (t := t)))

/-- **The coded cap**: `t` with one cell of full scope and full grade `n` appended last, labelled
with the formal top, whose row is the coded row of `ℓ`.  The apex (`StageType.addApex`) is the
case `ℓ = t.label`. -/
noncomputable def addCodedCap : StageType.{u} α n where
  toScheme := codedScheme ht V ℓ
  label := apexLabel
  isWellFormed := Scheme.isWellFormed_appendFullCell t.isWellFormed hn le_rfl
  isCoded := Scheme.isCoded_appendFullCell t.isCoded fun d ↦ by
    induction d using Fin.lastCases with
    | last => rw [codedRow_last]; exact blockEncode_lt _
    | cast d => rw [codedRow_castSucc]; exact blockEncode_lt _
  isLawful := hlab
  atStage d := by
    induction d using Fin.lastCases with
    | last => rw [apexLabel_last]; exact atStage_top
    | cast d => rw [apexLabel_castSucc]; exact t.atStage d

/-- **The coded cap is legal** when the coded copy of `ℓ` is lawful. -/
theorem isLegal_addCodedCap (hℓ : t.rows.IsLawful (blockEncode V n ∘ ℓ)) :
    (t.addCodedCap ht hn hlab).IsLegal :=
  isLegal_iff.mpr ⟨Scheme.isConsistent_appendFullCell ht.isConsistent (isLawful_codedRow ht hℓ),
    Scheme.isBountiful_appendFullCell (h := ht.not_le) ht.isBountiful,
    Scheme.isComplete_appendFullCell (h := ht.not_le) ht.exists_gradedIndex_eq⟩

@[simp] theorem addCodedCap_label_castSucc (d : Fin t.card) :
    (t.addCodedCap ht hn hlab).label d.castSucc = t.label d :=
  apexLabel_castSucc d

@[simp] theorem addCodedCap_label_last : (t.addCodedCap ht hn hlab).label (Fin.last _) = ⊤ :=
  apexLabel_last

/-- The new cell has graded index `(univ, n)`. -/
theorem addCodedCap_gradedIndex_last :
    (t.addCodedCap ht hn hlab).toCellScheme.gradedIndex (Fin.last _) = (univ, n) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- Every cell lies below the new cell. -/
theorem mem_below_addCodedCap_last (z : Fin (t.addCodedCap ht hn hlab).card) :
    z ∈ (t.addCodedCap ht hn hlab).toCellScheme.below
      ((t.addCodedCap ht hn hlab).toCellScheme.gradedIndex (Fin.last _)) := by
  rw [CellScheme.mem_below, addCodedCap_gradedIndex_last]
  exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t.addCodedCap ht hn hlab).grade_le z⟩

/-- **The row of the new cell is the coded row of `ℓ`.** -/
theorem rowAt_addCodedCap_last (z : Fin (t.addCodedCap ht hn hlab).card) :
    (t.addCodedCap ht hn hlab).toScheme.rowAt (Fin.last _) z = codedRow V ℓ z := by
  rw [Scheme.rowAt_of_mem (mem_below_addCodedCap_last ht hn hlab z)]
  exact Scheme.appendFullCell_row_last (h := ht.not_le) _

/-- **The proper faces of the coded cap are those of `t`.** -/
theorem restrictFace_addCodedCap (f : Fin m ↪ Fin n) (hf : univ.map f ≠ univ) :
    restrictFace f (t.addCodedCap ht hn hlab) = restrictFace f t :=
  restrictFace_eq_of_strictMono (t := t.addCodedCap ht hn hlab) (s := t) f
    (φ := (Fin.castSucc : Fin t.card → Fin (t.card + 1))) Fin.strictMono_castSucc
    (Scheme.isLowerEmbedding_castSucc n (codedRow V ℓ) ht.not_le)
    (Scheme.appendFullCellScheme_scope_castSucc _ _) (Scheme.comap_rows_castSucc (h := ht.not_le))
    rfl rfl (fun d ↦ apexLabel_castSucc d)
    (Scheme.mem_range_castSucc_of_appendFullCell (h := ht.not_le) f hf)

/-- The cells of a proper face of the coded cap are old cells. -/
theorem faceCell_addCodedCap {f : Fin m ↪ Fin n} (hf : univ.map f ≠ univ)
    {s : StageType.{u} α m} (hs : restrictFace f t = some s)
    (hs' : restrictFace f (t.addCodedCap ht hn hlab) = some s) (i : Fin s.card) :
    faceCell hs' i = (faceCell hs i).castSucc :=
  Scheme.faceCell_appendFullCell (h := ht.not_le) f hf _ _ i

end StageType

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {t : StageType.{u} α n}

/-- The cells of a proper face after adding the apex are old cells. -/
theorem faceCell_addApex (ht : t.IsLegalBelowFullGrade) (hn : 0 < n) {f : Fin m ↪ Fin n}
    (hf : univ.map f ≠ univ) {s : StageType.{u} α m} (hs : restrictFace f t = some s)
    (hs' : restrictFace f (t.addApex ht hn) = some s) (i : Fin s.card) :
    faceCell hs' i = (faceCell hs i).castSucc :=
  Scheme.faceCell_appendFullCell (h := ht.not_le) f hf _ _ i

end StageType

/-! ### Rows keeping the ties of the root, and the raise at labellings in the bottom class -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- The row of a cell `c` of `t'` **keeps the ties of the labels on the root** along `h`: at two
cells visible through `h`, the second of grade at most the first, labels in order give row values
of `c` in the same order. -/
def KeepsRootTies (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c : Fin t'.card) : Prop :=
  ∀ y₁ ∈ t'.visibleCells h, ∀ y₂ ∈ t'.visibleCells h, t'.label y₁ ≤ t'.label y₂ →
    t'.toCellScheme.grade y₂ ≤ t'.toCellScheme.grade y₁ → t'.rowAt c y₁ ≤ t'.rowAt c y₂

/-- A cell visible through `h : Fin n ↪ Fin k` lies below every cell of full scope and grade at
least `n`. -/
theorem mem_below_of_mem_visibleCells {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {c y : Fin t'.card} (hc : t'.toCellScheme.scope c = univ)
    (hn : n ≤ t'.toCellScheme.grade c) (hy : y ∈ t'.visibleCells h) :
    y ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := by
  rw [CellScheme.mem_below]
  refine Prod.mk_le_mk.mpr ⟨by rw [hc]; exact subset_univ _, ?_⟩
  have hsub : t'.toCellScheme.scope y ⊆ univ.map h := (mem_filter.mp hy).2
  calc t'.toCellScheme.grade y ≤ #(t'.toCellScheme.scope y) :=
        t'.isWellFormed.isWellFormed.grade_le_card y
    _ ≤ #(univ.map h) := card_le_card hsub
    _ = n := by simp
    _ ≤ _ := hn

/-- A cell of a face along `h` is visible through `h`. -/
theorem faceCell_mem_visibleCells {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) (i : Fin t.card) :
    faceCell ht i ∈ t'.visibleCells h :=
  t'.toScheme.cellMap_mem h _

/-- Every cell visible through `h` is a cell of the face along `h`. -/
theorem exists_faceCell_eq {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {i : Fin t'.card}
    (hi : i ∈ t'.visibleCells h) : ∃ y, faceCell ht y = i := by
  obtain ⟨z, rfl⟩ : i ∈ Set.range (t'.toScheme.cellMap h) := by
    rw [Scheme.range_cellMap]
    exact hi
  exact ⟨Fin.cast (congrArg Scheme.card (comap_toScheme_of_restrictFace ht)) z, by
    simp [faceCell, Scheme.faceCell]⟩

/-- **Where the row of a cap keeps the root ties, a labelling with `⊤` at the cap keeps them.** -/
theorem le_of_keepsRootTies {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {c : Fin t'.card}
    (hk : t'.KeepsRootTies h c) (hc : t'.toCellScheme.scope c = univ)
    (hn : n ≤ t'.toCellScheme.grade c) {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a)
    (hac : a c = ⊤) {y₁ y₂ : Fin t'.card} (hy₁ : y₁ ∈ t'.visibleCells h)
    (hy₂ : y₂ ∈ t'.visibleCells h) (hl : t'.label y₁ ≤ t'.label y₂)
    (hg : t'.toCellScheme.grade y₂ ≤ t'.toCellScheme.grade y₁) : a y₁ ≤ a y₂ := by
  have hb₁ := mem_below_of_mem_visibleCells hc hn hy₁
  have hb₂ := mem_below_of_mem_visibleCells hc hn hy₂
  have hrow := hk y₁ hy₁ y₂ hy₂ hl hg
  rw [Scheme.rowAt_of_mem hb₁, Scheme.rowAt_of_mem hb₂] at hrow
  have h' := (ha.locality c).le_of_le (d := ⟨y₁, hb₁⟩) (d' := ⟨y₂, hb₂⟩) hrow hg
  change min (a y₁) (a c) ≤ min (a y₂) (a c) at h'
  rwa [hac, min_top_right, min_top_right] at h'

/-- **The refutation schema never applies at a cap keeping the root ties.**  Over `t'` along `h`,
let a new top `j` of a donor `d` read the root cell `y₁` at most as the root cell `y₂`, of grade
at most that of `y₁`.  If the row of a cell `c` of full scope and grade at least `n` keeps the root
ties, every lawful labelling of `t'` with `⊤` at `c` labels `y₁` at most as `y₂`. -/
theorem le_of_tie_of_keepsRootTies {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {c : Fin t'.card}
    (hk : t'.KeepsRootTies h c) (hc : t'.toCellScheme.scope c = univ)
    (hn : n ≤ t'.toCellScheme.grade c) {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a)
    (hac : a c = ⊤) {j : Fin d.card} (hjt : d.label j = ⊤) {y₁ y₂ : Fin t.card}
    (hy₁ : faceCell hd y₁ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hy₂ : faceCell hd y₂ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hrow : d.rows.row j ⟨_, hy₁⟩ ≤ d.rows.row j ⟨_, hy₂⟩)
    (hg : t.toCellScheme.grade y₂ ≤ t.toCellScheme.grade y₁) :
    a (faceCell ht y₁) ≤ a (faceCell ht y₂) := by
  have hloc := (d.isLawful.locality j).le_of_le (d := ⟨_, hy₁⟩) (d' := ⟨_, hy₂⟩) hrow
    (by rw [grade_faceCell, grade_faceCell]; exact hg)
  change min (d.label (faceCell hd y₁)) (d.label j) ≤
    min (d.label (faceCell hd y₂)) (d.label j) at hloc
  rw [hjt, min_top_right, min_top_right, label_faceCell, label_faceCell] at hloc
  refine le_of_keepsRootTies hk hc hn ha hac (faceCell_mem_visibleCells ht y₁)
    (faceCell_mem_visibleCells ht y₂) ?_ ?_
  · rwa [label_faceCell, label_faceCell]
  · rw [grade_faceCell, grade_faceCell]
    exact hg

/-- **The apex keeps the root ties**: its row is the code of the labels. -/
theorem keepsRootTies_addApex {t₀ : StageType.{u} α k} (ht₀ : t₀.IsLegalBelowFullGrade)
    (hk : 0 < k) (h : Fin n ↪ Fin k) : (t₀.addApex ht₀ hk).KeepsRootTies h (Fin.last _) := by
  intro y₁ _ y₂ _ hl _
  have hlast : (t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _) = (univ, k) :=
    addApex_gradedIndex_last ht₀ hk
  have hmem (z : Fin (t₀.addApex ht₀ hk).card) : z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _)) := by
    rw [CellScheme.mem_below, hlast]
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t₀.addApex ht₀ hk).grade_le z⟩
  rw [Scheme.rowAt_of_mem (hmem y₁), Scheme.rowAt_of_mem (hmem y₂), row_addApex_last_eq,
    row_addApex_last_eq]
  exact monotone_blockEncode hl

/-- The **raise requirement in the bottom class**: `StageType.RaisesNewTops` asked only at the
lawful labellings of `t'` that are `⊥` exactly where the labels of `t'` are. -/
def RaisesNewTopsInClass (t' : StageType.{u} α k) {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (r s : Fin t'.card) : Prop :=
  ∀ a : Fin t'.card → Label.{u}, t'.rows.IsLawful a → (∀ z, a z = ⊥ ↔ t'.label z = ⊥) →
    a r = ⊤ → a s = ⊤ →
    ∃ b : Fin d.card → Label.{u}, d.rows.IsLawful b ∧
      (∀ i, b (faceCell hd i) = a (faceCell ht i)) ∧
      ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → b j = ⊤

/-- The raise requirement gives it in the bottom class. -/
theorem RaisesNewTops.inClass {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} {ht : restrictFace h t' = some t} {d : StageType.{u} α (n + 1)}
    {hd : restrictFace Fin.castSuccEmb d = some t} {r s : Fin t'.card}
    (hraise : t'.RaisesNewTops ht d hd r s) : t'.RaisesNewTopsInClass ht d hd r s :=
  fun a ha _ ↦ hraise a ha

/-- **The refutation schema in the bottom class**: under the hypotheses of
`StageType.not_raisesNewTops_of_row_le`, with the inverting labelling in the bottom class of the
labels of `t'`, the raise requirement fails in the bottom class. -/
theorem not_raisesNewTopsInClass_of_row_le {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {r s : Fin t'.card}
    {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a)
    (hcl : ∀ z, a z = ⊥ ↔ t'.label z = ⊥) (har : a r = ⊤) (has : a s = ⊤)
    {j : Fin d.card} (hj : Fin.last n ∈ d.toCellScheme.scope j) (hjt : d.label j = ⊤)
    {y₁ y₂ : Fin t.card}
    (hy₁ : faceCell hd y₁ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hy₂ : faceCell hd y₂ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hrow : d.rows.row j ⟨_, hy₁⟩ ≤ d.rows.row j ⟨_, hy₂⟩)
    (hg : t.toCellScheme.grade y₂ ≤ t.toCellScheme.grade y₁)
    (hlt : a (faceCell ht y₂) < a (faceCell ht y₁)) :
    ¬ t'.RaisesNewTopsInClass ht d hd r s := by
  intro hraise
  obtain ⟨b, hb, hagree, htop⟩ := hraise a ha hcl har has
  have hloc := (hb.locality j).le_of_le (d := ⟨_, hy₁⟩) (d' := ⟨_, hy₂⟩) hrow
    (by rw [grade_faceCell, grade_faceCell]; exact hg)
  change min (b (faceCell hd y₁)) (b j) ≤ min (b (faceCell hd y₂)) (b j) at hloc
  rw [htop j hj hjt, min_top_right, min_top_right, hagree, hagree] at hloc
  exact absurd hloc (not_le.mpr hlt)

/-- **Correctness at the cap forces the raise in the bottom class.**  Let `D` be a legal one-point
extension of `t'` carrying `d`, and `s` a cell of `t'` of grade `N`.  Suppose that at every cell of
`D` of graded index `(univ, N)` labelled `⊤` by a lawful labelling `a'` of `D` whose part on `t'`
is in the bottom class of `t'` and `⊤` at `r` and `s`, the labelling `a'` is `⊤` at every new cell
of `d` labelled `⊤` (the clause of a capped correctness at cap and marker `⊤`, read at the cells
that availability reaches).  Then the raise requirement holds in the bottom class.  The proof is
the extension from the face at the cap `⊥` and availability from `s`. -/
theorem raisesNewTopsInClass_of_correct {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {D : StageType.{u} α (k + 1)}
    (hD : D.IsLegal) (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (h₂ : restrictFace (extendByLast h) D = some d) {N : ℕ} {r s : Fin t'.card}
    (hs : t'.toCellScheme.grade s = N)
    (hcorr : ∀ a' : Fin D.card → Label.{u}, D.rows.IsLawful a' → ∀ u,
      D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), N) → a' u = ⊤ →
      (∀ z, a' (faceCell h₁ z) = ⊥ ↔ t'.label z = ⊥) → a' (faceCell h₁ r) = ⊤ →
      a' (faceCell h₁ s) = ⊤ →
      ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → a' (faceCell h₂ j) = ⊤) :
    t'.RaisesNewTopsInClass ht d hd r s := by
  intro a ha hcl har has
  obtain ⟨a', ha', hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁ ha
  have hNk : N ≤ k := hs ▸ t'.grade_le s
  have hpos : 0 < N := hs ▸ t'.isWellFormed.isWellFormed.grade_pos s
  obtain ⟨u₀, hu₀⟩ := hD.isComplete ((univ : Finset (Fin (k + 1))), N)
    ⟨D.univ_mem_faces, hpos, by simpa using hNk.trans (Nat.le_succ k)⟩
  have hsN : D.toCellScheme.grade (faceCell h₁ s) = N := (grade_faceCell h₁ s).trans hs
  obtain ⟨u, hu, hsu⟩ := ha'.availability (faceCell h₁ s) u₀
    (by rw [show D.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]; exact subset_univ _)
    (hsN.trans (congrArg Prod.snd hu₀).symm)
  have hau : a' u = ⊤ := top_le_iff.mp (by rw [← has, ← hext]; exact hsu)
  have htop := hcorr a' ha' u (hu.trans hu₀) hau (fun z ↦ by rw [hext]; exact hcl z)
    (by rw [hext, har]) (by rw [hext, has])
  refine ⟨fun j ↦ a' (faceCell h₂ j), isLawful_comp_faceCell h₂ ha', fun i ↦ ?_,
    fun j hj hjt ↦ htop j hj hjt⟩
  change a' (faceCell h₂ (faceCell hd i)) = a (faceCell ht i)
  rw [← faceCell_faceCell h₁ h₂ ht hd i, hext]

end StageType

/-! ### The old cells of a completion -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- A lawful labelling of the completion is lawful on the old cells of the completed scheme. -/
theorem isLawful_comp_castSucc {a' : Fin (F.completion hα).card → Label.{u}}
    (ha' : (F.completion hα).rows.IsLawful a') : F.scheme.rows.IsLawful fun d ↦ a' d.castSucc := by
  have h₀ : ((F.truncate hα).toScheme.appendFullCell (m + 2)
      (StageType.apexRow (t := F.truncate hα) F.isLegalBelowFullGrade)
      F.isLegalBelowFullGrade.not_le).rows.IsLawful a' := ha'
  have h₁ := h₀.comap (Scheme.isLowerEmbedding_castSucc (m + 2)
    (StageType.apexRow (t := F.truncate hα) F.isLegalBelowFullGrade)
    F.isLegalBelowFullGrade.not_le)
  rw [Scheme.comap_rows_castSucc (S := (F.truncate hα).toScheme)
    (h := F.isLegalBelowFullGrade.not_le)] at h₁
  exact h₁

/-- The cells of a proper face of the completion are cells of the truncation. -/
theorem faceCell_completion {n : ℕ} {f : Fin n ↪ Fin (m + 2)} (hf : univ.map f ≠ univ)
    {s : StageType.{u} α n} (hs : StageType.restrictFace f (F.truncate hα) = some s)
    (hs' : StageType.restrictFace f (F.completion hα) = some s) (i : Fin s.card) :
    StageType.faceCell hs' i = (StageType.faceCell hs i).castSucc :=
  StageType.faceCell_addApex _ _ hf hs hs' i

end CompletionBelowFullGrade

end VaughtConjecture

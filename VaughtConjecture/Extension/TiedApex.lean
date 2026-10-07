/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Stage.Threshold

/-!
# The tied apex: a full cell whose row ties it to a chosen cell

Roadmap, Layer 3 (finite extension constructions), for Layer 4, output 2 (forcing donors,
`ForcingDonors`); semantic contract, items 3–4.

**The tied apex** (`StageType.addTiedApex`).  Let `t` be a stage type on `n` points, `0 < n`,
whose scheme is legal below the full grade, and `e` a cell of `t` whose label is self-visible at
`n`.  Append one cell `C` of full scope and full grade `n` (`Scheme.appendFullCell`), with

* the row of `C`: the coded copy of the labels of `t` on the old cells (as for the apex,
  `StageType.apexRow`), and at `C` itself the code of the label of `e`
  (`StageType.tiedApexRow`), so that the row of `C` takes the same value at `C` and at `e`: a
  **tie**;
* the label of `C`: the label of `e` (`StageType.tiedApexLabel`).

The construction differs from adding the apex (`StageType.addApex`) only in the value of the row
at the new cell and in its label.  The apex row has the code of the formal top at the apex, which
exceeds every other code, so the apex ties exactly the cells labelled the formal top; for a cell
with an ordinal label the tied apex is needed.

**Laws.**  Appending a full cell accepts any row at the new cell; its laws need only:

* consistency: the old rows are those of `t`, and the tie row is lawful (`isLawful_tiedApexRow`):
  the coded copy is lawful, its value at `C` is self-visible at `n`, and locality at `C` is the
  coded copy capped at that value (`Label.TransformsTo.min_const`);
* lawfulness of the labels (`isLawful_tiedApexLabel`): the block decoding transforms the tie row
  to the labels with the label of `e` at `C`, and capping at the label of `e`, self-visible at
  `n`, gives the locality target at `C`;
* bountifulness, which at the full grade is trivial (a lift to `(univ, n)` starts at `(univ, n)`),
  and completeness, which comes from `t` below the full grade.

So the tied apex is legal (`StageType.isLegal_addTiedApex`), and its faces along embeddings onto
proper subsets are those of `t` (`StageType.restrictFace_addTiedApex`).  Its only hypothesis
beyond those of the apex is that the label of `e` is self-visible at `n`.

**Forcing** (`StageType.forcesThreshold_addTiedApex`).  If `t` restricts to `p` along a proper
face `f`, the cell `d` of `p` is carried to `e`, and the label of `e` is at least a stage `β` that
is zero or a limit, then the reduction of the tied apex to `β` forces `n` at `d`, with `f`: `C` is
labelled the formal top in the reduction, `e` lies below `C`, and the tie is literal, so the tie
lemma `StageType.forcesThreshold_of_row_le` applies.

**A donor from a type legal below the full grade**
(`StageType.exists_donor_of_isLegalBelowFullGrade`): if `t` is the face of `T` along a proper face
`g`, `T` is legal below the full grade on `N` points, and the label of `d` is at least `β` and
self-visible at `N`, then some legal `D` on `N` points has `t` as its face along `g` and its
reduction to `β` forces `N` at `d`.  When `β` is zero or a limit and the label lies at the stage
`β + ω`, self-visibility at `N` is the bound `β + N ≤` label
(`Label.isSelfVisible_of_coe_add_le`).

**The tie is an upper bound only.**  A tie asks that the label of `C` be at most that of `e` in
every lawful labelling, and that `C` be the formal top after reduction; nothing is prescribed at
the other cells of the graded index of `C`.  In a capped lift, lowering `C` to the cap keeps
locality at `C` and the inequality (`Label.TransformsTo.cap_tied`), so locality at a tied cell, and
the tie, never need a value above the cap.  Availability at the graded index of `C` and the rows
of the cells that read `C` are not covered.

The construction uses no realization, no uniqueness of expansions, and no receiving: it is a
statement about stage types.

## Placement

Layer 3 of `roadmap/README.md` (the finite construction for forcing donors, Layer 4, output 2).

## References

The apex is the cell `Ξ` of [Kni26, Corollary 4.3.22]; the tied apex is a variant of it, with a
row that is not the row of that corollary.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n}

section TiedApex

variable (ht : t.IsLegalBelowFullGrade) (e : Fin t.card)

/-- The **row of the tied apex**: the coded copy of the labels of `t`, and the code of the label of
`e` at the new cell. -/
noncomputable def tiedApexRow : Fin (t.card + 1) → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) (blockEncode (apexCodes ht) n ∘ t.label)
    (blockEncode (apexCodes ht) n (t.label e))

/-- The labels with the tied apex: the labels of `t`, and the label of `e` at the new cell. -/
def tiedApexLabel : Fin (t.card + 1) → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) t.label (t.label e)

/-- The tied apex row at an old cell. -/
@[simp] theorem tiedApexRow_castSucc (d : Fin t.card) :
    tiedApexRow ht e d.castSucc = blockEncode (apexCodes ht) n (t.label d) :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The tied apex row at the new cell. -/
@[simp] theorem tiedApexRow_last :
    tiedApexRow ht e (Fin.last _) = blockEncode (apexCodes ht) n (t.label e) :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- The label of an old cell with the tied apex. -/
@[simp] theorem tiedApexLabel_castSucc (d : Fin t.card) : tiedApexLabel e d.castSucc = t.label d :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The label of the tied apex is the label of `e`. -/
@[simp] theorem tiedApexLabel_last : tiedApexLabel e (Fin.last _) = t.label e :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

variable {e} (he : IsSelfVisible n (t.label e))
include he

/-- **The tied apex row is lawful**: the coded copy of the labels, with a value at the new cell
self-visible at `n`, at which locality caps the coded copy. -/
theorem isLawful_tiedApexRow :
    (t.toScheme.appendFullCell n (tiedApexRow ht e) ht.not_le).rows.IsLawful
      (tiedApexRow ht e) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert isLawful_blockEncode_apexCodes ht using 1
    funext d
    exact tiedApexRow_castSucc ht e d
  · rw [tiedApexRow_last]
    exact he.blockEncode le_rfl
  · exact (TransformsTo.refl _ _).min_const ht.grade_appendFullCellScheme_le
      (by rw [tiedApexRow_last]; exact he.blockEncode le_rfl)

/-- **The labels with the tied apex are lawful**: the decoding transforms the tie row to the labels
with the label of `e` at the new cell, and capping at the label of `e` (self-visible at `n`) gives
the locality target. -/
theorem isLawful_tiedApexLabel :
    (t.toScheme.appendFullCell n (tiedApexRow ht e) ht.not_le).rows.IsLawful
      (tiedApexLabel e) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact tiedApexLabel_castSucc e d
  · rw [tiedApexLabel_last]
    exact he
  · have hdec : TransformsTo (t.toScheme.appendFullCellScheme n).grade (tiedApexRow ht e)
        (tiedApexLabel e) := by
      refine ⟨fun _ ↦ ⊤, blockDecode (apexCodes ht), isWitness_blockDecode, fun d ↦ ?_⟩
      rw [min_top_right]
      induction d using Fin.lastCases with
      | last =>
        rw [tiedApexLabel_last, tiedApexRow_last,
          blockDecode_blockEncode (label_mem_apexCodes ht e)]
      | cast d =>
        rw [tiedApexLabel_castSucc, tiedApexRow_castSucc,
          blockDecode_blockEncode (label_mem_apexCodes ht d)]
    exact hdec.min_const ht.grade_appendFullCellScheme_le (by rw [tiedApexLabel_last]; exact he)

variable (hn : 0 < n)

/-- **The tied apex** over `t` at the cell `e`: one cell of full scope and full grade `n` appended
last, labelled with the label of `e`, whose row is the coded copy of the labels with the code of
the label of `e` at the new cell (`StageType.tiedApexRow`).

It is not `StageType.addApex` with another label: the row of the new cell is part of the scheme,
and here it takes the code of the label of `e` at the new cell, not the code of the formal top.
The two constructions share the laws of a full cell (`Scheme.isLawful_appendFullCell`,
`Scheme.isConsistent_appendFullCell`, `Scheme.isBountiful_appendFullCell`,
`Scheme.isComplete_appendFullCell`). -/
noncomputable def addTiedApex : StageType.{u} α n where
  toScheme := t.toScheme.appendFullCell n (tiedApexRow ht e) ht.not_le
  label := tiedApexLabel e
  isWellFormed := Scheme.isWellFormed_appendFullCell t.isWellFormed hn le_rfl
  isCoded := Scheme.isCoded_appendFullCell t.isCoded fun d ↦ by
    induction d using Fin.lastCases with
    | last => rw [tiedApexRow_last]; exact blockEncode_lt _
    | cast d => rw [tiedApexRow_castSucc]; exact blockEncode_lt _
  isLawful := isLawful_tiedApexLabel ht he
  atStage d := by
    induction d using Fin.lastCases with
    | last => rw [tiedApexLabel_last]; exact t.atStage e
    | cast d => rw [tiedApexLabel_castSucc]; exact t.atStage d

/-- The label of an old cell with the tied apex is its label in `t`. -/
@[simp] theorem addTiedApex_label_castSucc (d : Fin t.card) :
    (t.addTiedApex ht he hn).label d.castSucc = t.label d :=
  tiedApexLabel_castSucc e d

/-- The label of the tied apex is the label of `e`. -/
@[simp] theorem addTiedApex_label_last : (t.addTiedApex ht he hn).label (Fin.last _) = t.label e :=
  tiedApexLabel_last e

/-- **The tied apex is legal**: consistency, and the bountifulness and completeness of the apex,
unchanged. -/
theorem isLegal_addTiedApex : (t.addTiedApex ht he hn).IsLegal :=
  isLegal_iff.mpr ⟨Scheme.isConsistent_appendFullCell ht.isConsistent (isLawful_tiedApexRow ht he),
    Scheme.isBountiful_appendFullCell (h := ht.not_le) ht.isBountiful,
    Scheme.isComplete_appendFullCell (h := ht.not_le) ht.exists_gradedIndex_eq⟩

/-- The cells of the tied apex visible through a proper face are old. -/
theorem mem_range_castSucc_of_addTiedApex {k : ℕ} (f : Fin k ↪ Fin n) (hf : univ.map f ≠ univ)
    (z : Fin (t.addTiedApex ht he hn).card)
    (hz : ((t.addTiedApex ht he hn).toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f) :
    z ∈ Set.range (Fin.castSucc : Fin t.card → Fin (t.card + 1)) := by
  induction z using Fin.lastCases with
  | last =>
    refine absurd (eq_univ_of_forall fun x ↦ ?_) hf
    obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (by
      -- the cell scheme of the tied apex is `appendFullCellScheme` by definition
      change x ∈ (t.toScheme.appendFullCellScheme n).scope (Fin.last _)
      rw [Scheme.appendFullCellScheme_scope_last]; exact mem_univ x))
    exact mem_map_of_mem _ (mem_univ y)
  | cast z => exact ⟨z, rfl⟩

/-- **The proper faces of the tied apex are those of `t`**, including definedness. -/
theorem restrictFace_addTiedApex {k : ℕ} (f : Fin k ↪ Fin n) (hf : univ.map f ≠ univ) :
    restrictFace f (t.addTiedApex ht he hn) = restrictFace f t :=
  restrictFace_eq_of_strictMono (t := t.addTiedApex ht he hn) (s := t) f
    (φ := (Fin.castSucc : Fin t.card → Fin (t.card + 1))) Fin.strictMono_castSucc
    (Scheme.isLowerEmbedding_castSucc n (tiedApexRow ht e) ht.not_le)
    (Scheme.appendFullCellScheme_scope_castSucc _ _) (Scheme.comap_rows_castSucc (h := ht.not_le))
    rfl rfl (addTiedApex_label_castSucc ht he hn) (mem_range_castSucc_of_addTiedApex ht he hn f hf)

/-- **The tied apex forces its grade at the tied cell.**  If `t` restricts to `p` along a proper
face `f`, the cell `d` of `p` is carried to `e`, and `e` is labelled at least `β`, a stage that is
zero or a limit, then the reduction of the tied apex to `β`, with `f`, forces `n` at `d`. -/
theorem forcesThreshold_addTiedApex {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) {k : ℕ}
    {f : Fin k ↪ Fin n} (hf : univ.map f ≠ univ) {p : StageType.{u} α k}
    (hfp : restrictFace f t = some p) {d : Fin p.card}
    (hde : ∀ i : Fin (t.toScheme.comap f).card, (i : ℕ) = d → t.cellMap f i = e)
    (hβe : (β : Label.{u}) ≤ t.label e) :
    ForcesThreshold α hβ ((t.addTiedApex ht he hn).reduce hβ) f (p.reduce hβ) d n := by
  set D := t.addTiedApex ht he hn
  have hfp' : restrictFace f (D.reduce hβ) = some (p.reduce hβ) := by
    rw [restrictFace_reduce, restrictFace_addTiedApex ht he hn f hf, hfp, Option.map_some]
  have heC : e.castSucc ∈ (D.reduce hβ).toCellScheme.below
      ((D.reduce hβ).toCellScheme.gradedIndex (Fin.last _)) := by
    -- the reduction keeps the scheme, which is `appendFullCellScheme` by definition
    change (t.toScheme.appendFullCellScheme n).gradedIndex e.castSucc ≤
      (t.toScheme.appendFullCellScheme n).gradedIndex (Fin.last _)
    rw [Scheme.appendFullCellScheme_gradedIndex_castSucc,
      Scheme.appendFullCellScheme_gradedIndex_last]
    exact ⟨subset_univ _, (ht.grade_lt e).le⟩
  have h := forcesThreshold_of_row_le (α := α) (hβ := hβ) (q := D.reduce hβ) (f := f)
    (d := d) (C := Fin.last _) (e := e.castSucc) hfp' ?_ ?_ heC ?_
  · rwa [show (D.reduce hβ).toCellScheme.grade (Fin.last _) = n from
      Scheme.appendFullCellScheme_grade_last _ _] at h
  · intro i hi
    have hlt : (i : ℕ) < (t.toScheme.comap f).card := by
      obtain ⟨hf', rfl⟩ := (restrictFace_eq_some_iff t f).mp hfp
      exact hi ▸ d.2
    -- the reduction keeps the scheme, hence the cell map
    change D.toScheme.cellMap f i = e.castSucc
    rw [Scheme.cellMap_eq_of_strictMono_of_mem_range (S := t.toScheme) (T := D.toScheme) f
      Fin.strictMono_castSucc (Scheme.appendFullCellScheme_scope_castSucc _ _)
      (mem_range_castSucc_of_addTiedApex ht he hn f hf) (i := ⟨i, hlt⟩) rfl,
      hde ⟨i, hlt⟩ hi]
  · -- the reduced label of the new cell is `Label.reduce β` of its label (`reduce_label`)
    exact Label.reduce_eq_top_iff.mpr (hβe.trans_eq (addTiedApex_label_last ht he hn).symm)
  · -- the reduction keeps the rows; both entries are read in the row of the new cell
    refine le_of_eq ((Scheme.appendFullCell_row_last (h := ht.not_le) _).trans
      (Eq.trans ?_ (Scheme.appendFullCell_row_last (h := ht.not_le) _).symm))
    rw [tiedApexRow_last, tiedApexRow_castSucc]

end TiedApex

/-! ### A forcing donor from a type legal below the full grade -/

variable {β : Ordinal.{u}} {N k : ℕ} {T : StageType.{u} α N} {t : StageType.{u} α k}

/-- **A forcing donor from a type legal below the full grade.**  If `t` is the face of `T` along a
proper face `g`, `T` is legal below the full grade on `N` points, and the label of `d` is at least
`β` (zero or a limit) and self-visible at `N`, then the tied apex over `T` at the cell carrying `d`
is a legal stage type with `t` as its face along `g`, whose reduction to `β` forces `N` at `d`.
The hypothesis `hg` gives `N > 0`: on no points, every face is the whole ground set. -/
theorem exists_donor_of_isLegalBelowFullGrade (hβ : Order.IsSuccPrelimit β)
    (hT : T.IsLegalBelowFullGrade) {g : Fin k ↪ Fin N} (hg : univ.map g ≠ univ)
    (hgt : restrictFace g T = some t) {d : Fin t.card} (hβd : (β : Label.{u}) ≤ t.label d)
    (hv : IsSelfVisible N (t.label d)) :
    ∃ D : StageType.{u} α N, D.IsLegal ∧ restrictFace g D = some t ∧
      ForcesThreshold α hβ (D.reduce hβ) g (t.reduce hβ) d N := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h ↦ hg (by subst h; exact Subsingleton.elim _ _)
  obtain ⟨hf, hcomap⟩ := (restrictFace_eq_some_iff T g).mp hgt
  have hcard : (T.comap g hf).card = t.card :=
    congrArg (fun s : StageType.{u} α k ↦ s.card) hcomap
  set i₀ : Fin (T.toScheme.comap g).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
  have hle : T.label (T.cellMap g i₀) = t.label d := by
    rw [← comap_label T g hf i₀]
    exact label_congr hcomap rfl
  have he : IsSelfVisible N (T.label (T.cellMap g i₀)) := hle ▸ hv
  exact ⟨T.addTiedApex hT he hN, isLegal_addTiedApex hT he hN,
    (restrictFace_addTiedApex hT he hN g hg).trans hgt,
    forcesThreshold_addTiedApex hT he hN hβ hg hgt
      (fun i hi ↦ congrArg (T.cellMap g) (Fin.ext hi)) (hle ▸ hβd)⟩

end StageType

end VaughtConjecture

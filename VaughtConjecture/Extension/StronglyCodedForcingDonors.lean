/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.NormalizationInClass
import VaughtConjecture.Extension.ForcingDonorsCoatom
import VaughtConjecture.Extension.StronglyCodedAmalgamation

/-!
# Strongly coded forcing donors

Roadmap, Layer 3 (the finite construction for forcing donors) and Correspondence, item 1 (the
strongly coded legal stage types), for Layer 4, output 2 (`ForcingDonorsIn`, in
`VaughtConjecture.Continuation.NormalizationInClass`); semantic contract, items 3–4.  All results
here are native constructions of this repository.

Write `λ_η = blockStage η`.  **Forcing donors hold within the strongly coded stage types at every
block index** (`forcingDonorsIn_stronglyCoded_blockStage`): for a legal `t` at `λ_{η+1}` with
strongly coded rows, a cell `d` reducing to the formal top, and `λ_η + n ≤ t.label d`, some legal
`D` with strongly coded rows has `t` as a face and forces `n` at `d` after reduction to `λ_η`.  The
construction is that of `forcingDonors_of_hasCoatomExtensions`, with every step kept inside the
strongly coded legal stage types (`StageType.IsStronglyCodedLegal`):

1. a strongly coded legal one-point type labelled `λ_η + n`
   (`StageType.exists_stronglyCoded_onePoint_label`, from the strongly coded apex
   `StageType.addStrongApex` over the cellless scheme), padded to `n` points by strongly coded
   pinned extensions over the empty face
   (`StageType.exists_stronglyCodedLegal_restrictFace_castLEEmb`), cut to its part below the full
   grade (strongly coded, `StageType.isStronglyCoded_partBelowFullGrade`), and closed by the
   **strongly coded tied apex** (`StageType.addStrongTiedApex`) at the cell labelled `λ_η + n`
   (`StageType.exists_stronglyCodedLegal_tiedApex`);
2. the strongly coded amalgam over the empty face
   (`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit`), padded by one point;
3. the strongly coded apex over its part below the full grade, which forces through its row
   (`StageType.forcesThreshold_addStrongApex_of_label_le`): the row of the strongly coded apex is
   the strongly coded encoding of the labels (`StageType.strongApexRow`), monotone in the labels
   (`Label.monotone_strongEncode`).

**The strongly coded tie.**  The tied apex of `VaughtConjecture.Extension.TiedApex` has as row the
block coding of the labels, with the code of the tied label at the new cell.  The strongly coded
tied apex replaces the block coding by the strongly coded encoder at the full grade `n`, relative to
the labels of `t` and the formal top (`StageType.strongApexCodes`): every value of the row,
including the tie value `strongEncode (t.label e)`, is strongly coded at `n`
(`Label.isStronglyCoded_strongEncode`), is self-visible at `n` when the tied label is
(`Label.isSelfVisible_strongEncode`), and is decoded back to the labels
(`Label.strongDecode_strongEncode`), so the laws of the tied apex hold as before.

The two-point inputs, which `forcingDonorsUpTo_two_four` treats separately, are covered by the same
construction: strongly coded amalgamation holds at every arity at a stage that is zero or a limit.

With these donors the normalization interface of
`VaughtConjecture.Continuation.NormalizationInClass` holds for the strongly coded class
(`Realization.label_eq_stableLabel_stronglyCoded`,
`Realization.eq_of_reduce_eq_stronglyCoded`, `Realization.eq_stableCandidate_stronglyCoded`).

## Placement

Layer 3 of `roadmap/README.md` (3.1, (R6): forcing donors), for Layer 4, output 2.

## References

The apex is the cell `Ξ` of [Kni26, Corollary 4.3.22]; the strongly coded tied apex is a variant of
it, with a row that is not the row of that corollary.  The range clause is that of
[AFK26, Definition "legal"].
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n}

/-! ### Forcing at the strongly coded apex -/

section StrongApex

variable (ht : t.IsLegalBelowFullGrade) (hn : 0 < n)

/-- The cells of the strongly coded apex visible through a proper face are old. -/
theorem mem_range_castSucc_of_addStrongApex {k : ℕ} (f : Fin k ↪ Fin n) (hf : univ.map f ≠ univ)
    (z : Fin (t.addStrongApex ht hn).card)
    (hz : ((t.addStrongApex ht hn).toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f) :
    z ∈ Set.range (Fin.castSucc : Fin t.card → Fin (t.card + 1)) := by
  induction z using Fin.lastCases with
  | last =>
    refine absurd (eq_univ_of_forall fun x ↦ ?_) hf
    obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (by
      -- the cell scheme of the strongly coded apex is `appendFullCellScheme` by definition
      change x ∈ (t.toScheme.appendFullCellScheme n).scope (Fin.last _)
      rw [Scheme.appendFullCellScheme_scope_last]; exact mem_univ x))
    exact mem_map_of_mem _ (mem_univ y)
  | cast z => exact ⟨z, rfl⟩

/-- **The strongly coded apex forces through its row** (native construction): as
`StageType.forcesThreshold_addApex_of_label_le`, with the strongly coded apex.  If `t` restricts to
`p` along a proper face `f`, the cell `d` of `p` is carried to `e`, and a cell `x` of `t` with label
at least `β` (zero or a limit) and at most the label of `e` has grade at least that of `e`, then
the reduction to `β` of `t` with the strongly coded apex added forces the grade of `x` at `d`. -/
theorem forcesThreshold_addStrongApex_of_label_le {β : Ordinal.{u}}
    (hβ : Order.IsSuccPrelimit β) {k : ℕ} {f : Fin k ↪ Fin n} (hf : univ.map f ≠ univ)
    {p : StageType.{u} α k} (hfp : restrictFace f t = some p) {d : Fin p.card} {e x : Fin t.card}
    (hde : ∀ i : Fin (t.toScheme.comap f).card, (i : ℕ) = d → t.cellMap f i = e)
    (hβx : (β : Label.{u}) ≤ t.label x) (hxe : t.label x ≤ t.label e)
    (hgrade : t.toCellScheme.grade e ≤ t.toCellScheme.grade x) :
    ForcesThreshold α hβ ((t.addStrongApex ht hn).reduce hβ) f (p.reduce hβ) d
      (t.toCellScheme.grade x) := by
  set D := t.addStrongApex ht hn
  have hfp' : restrictFace f (D.reduce hβ) = some (p.reduce hβ) := by
    rw [restrictFace_reduce, restrictFace_addStrongApex ht hn f hf, hfp, Option.map_some]
  -- the reduction keeps the scheme, which is `appendFullCellScheme` by definition
  have hgr (z : Fin t.card) :
      (D.reduce hβ).toCellScheme.grade z.castSucc = t.toCellScheme.grade z := by
    change (t.toScheme.appendFullCellScheme n).grade z.castSucc = _
    exact Scheme.appendFullCellScheme_grade_castSucc _ _ z
  have hbelow (z : Fin t.card) : z.castSucc ∈ (D.reduce hβ).toCellScheme.below
      ((D.reduce hβ).toCellScheme.gradedIndex (Fin.last _)) := by
    change (t.toScheme.appendFullCellScheme n).gradedIndex z.castSucc ≤
      (t.toScheme.appendFullCellScheme n).gradedIndex (Fin.last _)
    rw [Scheme.appendFullCellScheme_gradedIndex_castSucc,
      Scheme.appendFullCellScheme_gradedIndex_last]
    exact ⟨subset_univ _, (ht.grade_lt z).le⟩
  refine forcesThreshold_of_row_le_of_grade_le (q := D.reduce hβ) (C := Fin.last _)
    (x := x.castSucc) (e := e.castSucc) hfp' (fun i hi ↦ ?_) ?_ ?_ (hbelow x) (hbelow e) ?_
    (by rw [hgr, hgr]; exact hgrade) ?_ (by rw [hgr])
  · have hlt : (i : ℕ) < (t.toScheme.comap f).card := by
      obtain ⟨hf', rfl⟩ := (restrictFace_eq_some_iff t f).mp hfp
      exact hi ▸ d.2
    -- the reduction keeps the scheme, hence the cell map
    change D.toScheme.cellMap f i = e.castSucc
    rw [Scheme.cellMap_eq_of_strictMono_of_mem_range (S := t.toScheme) (T := D.toScheme) f
      Fin.strictMono_castSucc (Scheme.appendFullCellScheme_scope_castSucc _ _)
      (mem_range_castSucc_of_addStrongApex ht hn f hf) (i := ⟨i, hlt⟩) rfl, hde ⟨i, hlt⟩ hi]
  · -- the reduced label of the apex is `Label.reduce β ⊤` (`reduce_label`)
    refine Label.reduce_eq_top_iff.mpr ?_
    change _ ≤ apexLabel (t := t) (Fin.last _)
    rw [apexLabel_last]
    exact le_top
  · exact Label.reduce_eq_top_iff.mpr (hβx.trans_eq (apexLabel_castSucc (t := t) x).symm)
  · -- the reduction keeps the rows; both entries are read in the row of the apex
    refine le_of_eq_of_le (Scheme.appendFullCell_row_last (h := ht.not_le) _)
      (le_of_le_of_eq ?_ (Scheme.appendFullCell_row_last (h := ht.not_le) _).symm)
    rw [strongApexRow_castSucc, strongApexRow_castSucc]
    exact monotone_strongEncode hxe
  · -- the grade of the apex is `n`, above every grade of `t`
    rw [show (D.reduce hβ).toCellScheme.grade (Fin.last _) = n from
      Scheme.appendFullCellScheme_grade_last _ _]
    exact (ht.grade_lt x).le

end StrongApex

/-! ### The strongly coded tied apex -/

section StrongTiedApex

variable (e : Fin t.card)

variable (t) in
/-- The **row of the strongly coded tied apex**: the strongly coded encoding at the grade `n` of the
labels of `t`, and the code of the label of `e` at the new cell. -/
noncomputable def strongTiedApexRow : Fin (t.card + 1) → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) (strongEncode t.strongApexCodes n ∘ t.label)
    (strongEncode t.strongApexCodes n (t.label e))

/-- The strongly coded tied apex row at an old cell. -/
@[simp] theorem strongTiedApexRow_castSucc (d : Fin t.card) :
    t.strongTiedApexRow e d.castSucc = strongEncode t.strongApexCodes n (t.label d) :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The strongly coded tied apex row at the new cell: the tie value. -/
@[simp] theorem strongTiedApexRow_last :
    t.strongTiedApexRow e (Fin.last _) = strongEncode t.strongApexCodes n (t.label e) :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- **The strongly coded tied apex row is strongly coded at `n`**, the tie value included. -/
theorem isStronglyCoded_strongTiedApexRow (d : Fin (t.card + 1)) :
    IsStronglyCoded n (t.strongTiedApexRow e d) := by
  induction d using Fin.lastCases with
  | last => rw [strongTiedApexRow_last]; exact isStronglyCoded_strongEncode _
  | cast d => rw [strongTiedApexRow_castSucc]; exact isStronglyCoded_strongEncode _

variable (ht : t.IsLegalBelowFullGrade) {e} (he : IsSelfVisible n (t.label e))
include he

/-- **The strongly coded tied apex row is lawful**: the strongly coded encoding of the labels, with
a tie value self-visible at `n`, at which locality caps the encoding. -/
theorem isLawful_strongTiedApexRow :
    (t.toScheme.appendFullCell n (t.strongTiedApexRow e) ht.not_le).rows.IsLawful
      (t.strongTiedApexRow e) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful.strongEncode (V := t.strongApexCodes) (K := n)
      (fun d ↦ (ht.grade_lt d).le) using 1
    funext d
    exact strongTiedApexRow_castSucc e d
  · rw [strongTiedApexRow_last]
    exact isSelfVisible_strongEncode he
  · exact (TransformsTo.refl _ _).min_const ht.grade_appendFullCellScheme_le
      (by rw [strongTiedApexRow_last]; exact isSelfVisible_strongEncode he)

/-- **The labels with the tied apex are lawful for the strongly coded tied apex row**: the
decoder, a witness bounded by `n`, transforms the row back to the labels with the label of `e` at
the new cell, and capping at the label of `e` gives the locality target. -/
theorem isLawful_tiedApexLabel_strongTiedApexRow :
    (t.toScheme.appendFullCell n (t.strongTiedApexRow e) ht.not_le).rows.IsLawful
      (tiedApexLabel e) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact tiedApexLabel_castSucc e d
  · rw [tiedApexLabel_last]
    exact he
  · have hdec : TransformsTo (t.toScheme.appendFullCellScheme n).grade (t.strongTiedApexRow e)
        (tiedApexLabel e) := by
      refine ⟨stepSuppressor n, strongDecode t.strongApexCodes n, isWitness_strongDecode,
        fun d ↦ ?_⟩
      rw [stepSuppressor_of_le (ht.grade_appendFullCellScheme_le d), min_top_right]
      induction d using Fin.lastCases with
      | last =>
        rw [tiedApexLabel_last, strongTiedApexRow_last,
          strongDecode_strongEncode (label_mem_strongApexCodes e)]
      | cast d =>
        rw [tiedApexLabel_castSucc, strongTiedApexRow_castSucc,
          strongDecode_strongEncode (label_mem_strongApexCodes d)]
    exact hdec.min_const ht.grade_appendFullCellScheme_le (by rw [tiedApexLabel_last]; exact he)

variable (hn : 0 < n)

/-- **The strongly coded tied apex** over `t` at the cell `e`: as `StageType.addTiedApex`, one cell
of full scope and full grade `n` appended last and labelled with the label of `e`, whose row is the
strongly coded encoding of the labels, with the code of the label of `e` at the new cell
(`StageType.strongTiedApexRow`). -/
noncomputable def addStrongTiedApex : StageType.{u} α n where
  toScheme := t.toScheme.appendFullCell n (t.strongTiedApexRow e) ht.not_le
  label := tiedApexLabel e
  isWellFormed := Scheme.isWellFormed_appendFullCell t.isWellFormed hn le_rfl
  isCoded := Scheme.isCoded_appendFullCell t.isCoded fun d ↦
    (isStronglyCoded_strongTiedApexRow e d).lt_omega0_sq
  isLawful := isLawful_tiedApexLabel_strongTiedApexRow ht he
  atStage d := by
    induction d using Fin.lastCases with
    | last => rw [tiedApexLabel_last]; exact t.atStage e
    | cast d => rw [tiedApexLabel_castSucc]; exact t.atStage d

/-- The label of an old cell with the strongly coded tied apex is its label in `t`. -/
@[simp] theorem addStrongTiedApex_label_castSucc (d : Fin t.card) :
    (t.addStrongTiedApex ht he hn).label d.castSucc = t.label d :=
  tiedApexLabel_castSucc e d

/-- The label of the strongly coded tied apex is the label of `e`. -/
@[simp] theorem addStrongTiedApex_label_last :
    (t.addStrongTiedApex ht he hn).label (Fin.last _) = t.label e :=
  tiedApexLabel_last e

/-- **The strongly coded tied apex is legal.** -/
theorem isLegal_addStrongTiedApex : (t.addStrongTiedApex ht he hn).IsLegal :=
  isLegal_iff.mpr ⟨Scheme.isConsistent_appendFullCell ht.isConsistent
      (isLawful_strongTiedApexRow ht he),
    Scheme.isBountiful_appendFullCell (h := ht.not_le) ht.isBountiful,
    Scheme.isComplete_appendFullCell (h := ht.not_le) ht.exists_gradedIndex_eq⟩

/-- **The strongly coded tied apex keeps strong coding**: the new row is strongly coded at its
grade `n`, the tie value included. -/
theorem isStronglyCoded_addStrongTiedApex (h : t.rows.IsStronglyCoded) :
    (t.addStrongTiedApex ht he hn).rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_appendFullCell (h := ht.not_le) h (isStronglyCoded_strongTiedApexRow e)

/-- The cells of the strongly coded tied apex visible through a proper face are old. -/
theorem mem_range_castSucc_of_addStrongTiedApex {k : ℕ} (f : Fin k ↪ Fin n)
    (hf : univ.map f ≠ univ) (z : Fin (t.addStrongTiedApex ht he hn).card)
    (hz : ((t.addStrongTiedApex ht he hn).toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f) :
    z ∈ Set.range (Fin.castSucc : Fin t.card → Fin (t.card + 1)) := by
  induction z using Fin.lastCases with
  | last =>
    refine absurd (eq_univ_of_forall fun x ↦ ?_) hf
    obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (by
      change x ∈ (t.toScheme.appendFullCellScheme n).scope (Fin.last _)
      rw [Scheme.appendFullCellScheme_scope_last]; exact mem_univ x))
    exact mem_map_of_mem _ (mem_univ y)
  | cast z => exact ⟨z, rfl⟩

/-- **The proper faces of the strongly coded tied apex are those of `t`**, including
definedness. -/
theorem restrictFace_addStrongTiedApex {k : ℕ} (f : Fin k ↪ Fin n) (hf : univ.map f ≠ univ) :
    restrictFace f (t.addStrongTiedApex ht he hn) = restrictFace f t :=
  restrictFace_eq_of_strictMono (t := t.addStrongTiedApex ht he hn) (s := t) f
    (φ := (Fin.castSucc : Fin t.card → Fin (t.card + 1))) Fin.strictMono_castSucc
    (Scheme.isLowerEmbedding_castSucc n (t.strongTiedApexRow e) ht.not_le)
    (Scheme.appendFullCellScheme_scope_castSucc _ _) (Scheme.comap_rows_castSucc (h := ht.not_le))
    rfl rfl (addStrongTiedApex_label_castSucc ht he hn)
    (mem_range_castSucc_of_addStrongTiedApex ht he hn f hf)

end StrongTiedApex

/-! ### Strongly coded legal types with prescribed cells -/

/-- **The part below the full grade keeps strong coding**: its rows are restrictions of those of
`t`. -/
theorem isStronglyCoded_partBelowFullGrade (h : t.rows.IsStronglyCoded) :
    t.partBelowFullGrade.rows.IsStronglyCoded :=
  h.comap t.toScheme.isLowerEmbedding_embBelowFullGrade

variable (α) in
/-- The stage type on the cellless one-point scheme, with no labels. -/
def celllessStageType : StageType.{u} α 1 :=
  ⟨cellless, fun _ ↦ ⊥, isLegalBelowFullGrade_cellless.isWellFormed,
    isLegalBelowFullGrade_cellless.isCoded, CellScheme.Rows.isLawful_const_bot,
    fun _ ↦ atStage_bot⟩

/-- The cellless one-point stage type is strongly coded: it has no cells. -/
theorem isStronglyCoded_celllessStageType : (celllessStageType α).rows.IsStronglyCoded :=
  fun s ↦ s.elim0

/-- **A strongly coded legal one-point stage type with a prescribed label** (native construction):
as `StageType.exists_onePoint_label`, with the strongly coded apex over the cellless scheme, for
`c < α` self-visible at `1`. -/
theorem exists_stronglyCoded_onePoint_label {c : Ordinal.{u}}
    (hc : IsSelfVisible 1 (c : Label.{u})) (hcα : c < α) :
    ∃ d : StageType.{u} α 1, d.IsStronglyCodedLegal ∧
      ∃ i, d.toCellScheme.grade i = 1 ∧ d.label i = c := by
  set t := (celllessStageType α).addStrongApex isLegalBelowFullGrade_cellless one_pos
  have hgr (d : Fin t.card) : t.toCellScheme.grade d ≤ 1 :=
    (t.isWellFormed.isWellFormed.grade_le_card d).trans ((card_le_univ _).trans_eq (by simp))
  refine ⟨⟨t.toScheme, fun d ↦ min (t.label d) c, t.isWellFormed, t.isCoded,
    t.isLawful.min_const_of_isSelfVisible hgr hc, fun _ ↦ .inl ((min_le_right _ _).trans_lt ?_)⟩,
    ⟨isLegal_addStrongApex isLegalBelowFullGrade_cellless one_pos,
      isStronglyCoded_addStrongApex isLegalBelowFullGrade_cellless one_pos
        isStronglyCoded_celllessStageType⟩,
    Fin.last _, Scheme.appendFullCellScheme_grade_last _ _, ?_⟩
  · exact_mod_cast hcα
  · -- the label of the capped type at the apex is `min ⊤ c`
    change min (apexLabel (t := celllessStageType α) (Fin.last _)) _ = _
    rw [apexLabel_last, min_top_left]

/-- **A strongly coded legal one-point stage type** exists at every stage: the strongly coded apex
over the cellless scheme, labelled the formal top. -/
theorem exists_stronglyCodedLegal_onePoint : ∃ d : StageType.{u} α 1, d.IsStronglyCodedLegal :=
  ⟨_, isLegal_addStrongApex isLegalBelowFullGrade_cellless one_pos,
    isStronglyCoded_addStrongApex (t := celllessStageType α) _ one_pos
      isStronglyCoded_celllessStageType⟩

/-- **One-point extension within the strongly coded legal stage types**, at a stage that is zero or
a limit: every strongly coded legal stage type is the face along `Fin.castSuccEmb` of a strongly
coded legal stage type on one more point (`StageType.exists_stronglyCoded_pinned_extension` over
the empty face). -/
theorem exists_stronglyCoded_extension (hα : Order.IsSuccPrelimit α) {P : StageType.{u} α n}
    (hP : P.IsStronglyCodedLegal) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsStronglyCodedLegal ∧
      restrictFace Fin.castSuccEmb Q = some P := by
  obtain ⟨d, hd⟩ := exists_stronglyCodedLegal_onePoint (α := α)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (d.isSome_restrictFace_of_zero Fin.castSuccEmb)
  obtain ⟨Q, hQ, hQP, -⟩ := exists_stronglyCoded_pinned_extension
    (hasStronglyCodedApexCoatomExtensions hα) hP hp hd (hp'.trans (congrArg some (eq_of_zero p' p)))
  exact ⟨Q, hQ, hQP⟩

variable {k N : ℕ}

/-- **Padding within the strongly coded legal stage types**, at a stage that is zero or a limit:
every strongly coded legal stage type on `k` points is the face along `Fin.castLEEmb` of a strongly
coded legal stage type on any `N ≥ k` points. -/
theorem exists_stronglyCodedLegal_restrictFace_castLEEmb (hα : Order.IsSuccPrelimit α)
    {P : StageType.{u} α k} (hP : P.IsStronglyCodedLegal) (hkN : k ≤ N) :
    ∃ Q : StageType.{u} α N, Q.IsStronglyCodedLegal ∧
      restrictFace (Fin.castLEEmb hkN) Q = some P := by
  induction N, hkN using Nat.le_induction with
  | base =>
    refine ⟨P, hP, ?_⟩
    rw [show Fin.castLEEmb (le_refl k) = Function.Embedding.refl _ from
      Function.Embedding.ext fun _ ↦ Fin.ext rfl]
    exact restrictFace_refl P
  | succ N hkN ih =>
    obtain ⟨Q, hQ, hQP⟩ := ih
    obtain ⟨Q', hQ', hQ'Q⟩ := exists_stronglyCoded_extension hα hQ
    refine ⟨Q', hQ', ?_⟩
    rw [show Fin.castLEEmb (hkN.trans (Nat.le_succ N)) =
        (Fin.castLEEmb hkN).trans Fin.castSuccEmb from Function.Embedding.ext fun _ ↦ Fin.ext rfl,
      ← restrictFace_trans _ _ _ hQ'Q]
    exact hQP

variable {l : ℕ}

/-- **A strongly coded cell of full grade tied to a cell of a proper face** (native construction):
as `StageType.exists_isLegal_tiedApex`, with the strongly coded tied apex.  If `W` is strongly coded
legal on `N` points, `r` is its face along a proper face `h`, and the label of the cell `i` of `r`
is self-visible at `N`, then some strongly coded legal `U` on `N` points has the proper faces of `W`
and a cell of grade `N` labelled as `i`. -/
theorem exists_stronglyCodedLegal_tiedApex {W : StageType.{u} α N} (hW : W.IsStronglyCodedLegal)
    {h : Fin l ↪ Fin N} (hh : univ.map h ≠ univ) {r : StageType.{u} α l}
    (hhr : restrictFace h W = some r) (i : Fin r.card) (hv : IsSelfVisible N (r.label i)) :
    ∃ U : StageType.{u} α N, U.IsStronglyCodedLegal ∧
      (∀ {k : ℕ} (g : Fin k ↪ Fin N), univ.map g ≠ univ → restrictFace g U = restrictFace g W) ∧
      ∃ x : Fin U.card, U.toCellScheme.grade x = N ∧ U.label x = r.label i := by
  have hN := pos_of_univ_map_ne hh
  set T := W.partBelowFullGrade
  have hT := hW.1.isLegalBelowFullGrade_partBelowFullGrade
  obtain ⟨j, -, hjl, -⟩ := exists_cellMap_of_restrictFace_eq
    ((restrictFace_partBelowFullGrade W h hh).trans hhr) i
  have he : IsSelfVisible N (T.label (T.cellMap h j)) := hjl ▸ hv
  exact ⟨T.addStrongTiedApex hT he hN,
    ⟨isLegal_addStrongTiedApex hT he hN,
      isStronglyCoded_addStrongTiedApex hT he hN (isStronglyCoded_partBelowFullGrade hW.2)⟩,
    fun g hg ↦ (restrictFace_addStrongTiedApex hT he hN g hg).trans
      (restrictFace_partBelowFullGrade W g hg),
    Fin.last _, Scheme.appendFullCellScheme_grade_last _ _,
    (addStrongTiedApex_label_last hT he hN).trans hjl⟩

/-- **A strongly coded donor from a strongly coded legal type with two proper faces** (native
construction): as `StageType.exists_donor_addApex_of_isLegal`, with the strongly coded apex. -/
theorem exists_stronglyCoded_donor_addStrongApex {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    {W : StageType.{u} α N} (hW : W.IsStronglyCodedLegal) {g : Fin k ↪ Fin N}
    (hg : univ.map g ≠ univ) {t : StageType.{u} α k} (hgt : restrictFace g W = some t)
    {h : Fin l ↪ Fin N} (hh : univ.map h ≠ univ) {U : StageType.{u} α l}
    (hhU : restrictFace h W = some U) {d : Fin t.card} {x : Fin U.card}
    (hβx : (β : Label.{u}) ≤ U.label x) (hxd : U.label x ≤ t.label d)
    (hgrade : t.toCellScheme.grade d ≤ U.toCellScheme.grade x) :
    ∃ D : StageType.{u} α N, D.IsStronglyCodedLegal ∧ restrictFace g D = some t ∧
      ForcesThreshold α hβ (D.reduce hβ) g (t.reduce hβ) d (U.toCellScheme.grade x) := by
  have hN := pos_of_univ_map_ne hg
  set T := W.partBelowFullGrade
  have hT := hW.1.isLegalBelowFullGrade_partBelowFullGrade
  have hTt : restrictFace g T = some t := (restrictFace_partBelowFullGrade W g hg).trans hgt
  have hTU : restrictFace h T = some U := (restrictFace_partBelowFullGrade W h hh).trans hhU
  obtain ⟨jd, hjd, hjdl, hjdg⟩ := exists_cellMap_of_restrictFace_eq hTt d
  obtain ⟨jx, -, hjxl, hjxg⟩ := exists_cellMap_of_restrictFace_eq hTU x
  refine ⟨T.addStrongApex hT hN, ⟨isLegal_addStrongApex hT hN,
    isStronglyCoded_addStrongApex hT hN (isStronglyCoded_partBelowFullGrade hW.2)⟩,
    (restrictFace_addStrongApex hT hN g hg).trans hTt, ?_⟩
  have hF := forcesThreshold_addStrongApex_of_label_le hT hN hβ hg hTt (e := T.cellMap g jd)
    (x := T.cellMap h jx) (fun i hi ↦ congrArg (T.cellMap g) (Fin.ext (hi.trans hjd.symm)))
    (hjxl ▸ hβx) (by rw [hjxl, hjdl]; exact hxd) (by rw [hjdg, hjxg]; exact hgrade)
  rwa [hjxg] at hF

/-- **A strongly coded legal type with a cell of full grade labelled `β + n`** (native
construction), for `2 ≤ n`, `β` zero or a limit, and `β + n < α` with `α` zero or a limit: a
strongly coded legal one-point type labelled `β + n`, padded to `n` points, cut to its part below
the full grade, and closed by the strongly coded tied apex at the cell labelled `β + n`. -/
theorem exists_stronglyCodedLegal_grade_label_coe_add (hα : Order.IsSuccPrelimit α)
    {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) {n : ℕ} (hn : 2 ≤ n) (hlt : β + n < α) :
    ∃ U : StageType.{u} α n, U.IsStronglyCodedLegal ∧ ∃ x : Fin U.card,
      U.toCellScheme.grade x = n ∧ U.label x = ((β + n : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨t₁, ht₁, i₁, -, hi₁⟩ :=
    exists_stronglyCoded_onePoint_label (α := α) (isSelfVisible_coe_add hβ (by omega : 1 ≤ n)) hlt
  obtain ⟨V, hV, hVt⟩ := exists_stronglyCodedLegal_restrictFace_castLEEmb hα ht₁ (by omega : 1 ≤ n)
  obtain ⟨U, hU, -, x, hx, hxl⟩ := exists_stronglyCodedLegal_tiedApex hV
    (univ_map_castLEEmb_ne (by omega)) hVt i₁ (by rw [hi₁]; exact isSelfVisible_coe_add hβ le_rfl)
  exact ⟨U, hU, x, hx, hxl.trans hi₁⟩

end StageType

/-! ### Strongly coded forcing donors -/

/-- **Strongly coded forcing donors at every block index** (native construction): forcing donors
within the stage types with strongly coded rows.  For a legal `t` at `λ_{η+1}` with strongly coded
rows, the donor is `t` itself when the threshold is at most the grade of the cell (the order law),
and otherwise the strongly coded apex over the strongly coded amalgam of `t` with a strongly coded
legal type carrying a cell of grade `n` labelled `λ_η + n`, padded by one point; it forces `n`
through the row of the apex.  Every arity is covered, the two-point inputs included. -/
theorem forcingDonorsIn_stronglyCoded_blockStage (η : Ordinal.{u}) :
    ForcingDonorsIn (fun t ↦ t.rows.IsStronglyCoded) η := by
  intro k t ht ht𝒮 d hd n hn
  have hβ := isSuccPrelimit_blockStage η
  have hα := isSuccPrelimit_blockStage (η + 1)
  -- The order law.
  by_cases hgd : n ≤ (t.reduce hβ).toCellScheme.grade d
  · exact ⟨k, t, Function.Embedding.refl _, ht, ht𝒮, StageType.restrictFace_refl t,
      StageType.forcesThreshold_of_le_grade (StageType.restrictFace_refl _) hd hgd⟩
  rw [not_le] at hgd
  have hgd' : t.toCellScheme.grade d < n := hgd
  have hn2 : 2 ≤ n := lt_of_le_of_lt (t.isWellFormed.isWellFormed.grade_pos d) hgd'
  -- 1. A strongly coded legal `U` on `n` points with a cell `xU` of grade `n` labelled `λ_η + n`.
  obtain ⟨U, hU, xU, hxUg, hxUl⟩ := StageType.exists_stronglyCodedLegal_grade_label_coe_add hα hβ
    hn2 (coe_add_lt_blockStage_add_one n)
  -- 2. The strongly coded amalgam of `t` and `U` over the empty face, padded by one point.
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    (t.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin k))
  obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp
    (U.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  rw [StageType.eq_of_zero q₀ p₀] at hq₀
  obtain ⟨N, W, i, j, hW, hWt, hWU, -⟩ :=
    StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit hα ⟨ht, ht𝒮⟩ hU hp₀ hq₀
  obtain ⟨W', hW', hW'W⟩ := StageType.exists_stronglyCoded_extension hα hW
  -- the faces of `t` and `U` miss the last point
  have hproper {l : ℕ} (g : Fin l ↪ Fin N) : univ.map (g.trans Fin.castSuccEmb) ≠ univ :=
    fun h ↦ by
      have hmem := mem_univ (Fin.last N)
      rw [← h, mem_map] at hmem
      obtain ⟨y, -, hy⟩ := hmem
      exact Fin.castSucc_ne_last _ hy
  -- 3. The strongly coded apex over the part below the full grade.
  obtain ⟨D, hD, hDt, hF⟩ := StageType.exists_stronglyCoded_donor_addStrongApex hβ hW' (hproper i)
    ((StageType.restrictFace_trans _ _ _ hW'W).symm.trans hWt) (hproper j)
    ((StageType.restrictFace_trans _ _ _ hW'W).symm.trans hWU) (d := d) (x := xU)
    (by rw [hxUl]; exact Label.coe_le_coe_add _ _) (by rw [hxUl]; exact hn)
    (by rw [hxUg]; exact hgd'.le)
  exact ⟨N + 1, D, _, hD.1, hD.2, hDt, by rwa [hxUg] at hF⟩

/-! ### The normalization interface for the strongly coded class -/

namespace Realization

variable {M : Type v} {k : ℕ} {η : Ordinal.{u}} {R : Realization.{u, v} (blockStage (η + 1)) M}

/-- **Normalization of labels for the strongly coded class** (native construction):
`Realization.label_eq_stableLabel_in` with the strongly coded forcing donors
(`forcingDonorsIn_stronglyCoded_blockStage`), for an exactly consistent realization with legal types
whose types have strongly coded rows, with finite-extension receiving for the strongly coded legal
donors. -/
theorem label_eq_stableLabel_stronglyCoded (hR : R.IsConsistent) (hl : R.HasLegalTypes)
    (h𝒮 : ∀ x : R.Occurrence, x.type.rows.IsStronglyCoded)
    (hrec : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    {t : StageType.{u} (blockStage (η + 1)) k} {c : Fin k → M} (hc : R.Covers t c)
    (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) :
    t.label d = (R.reduce (isSuccPrelimit_blockStage η)).stableLabel (blockStage (η + 1))
      (isSuccPrelimit_blockStage η) c (t.reduce (isSuccPrelimit_blockStage η)) d :=
  label_eq_stableLabel_in hR hl h𝒮 hrec (forcingDonorsIn_stronglyCoded_blockStage η) hc d hd

/-- **Determination by the reduction for the strongly coded class** (native construction):
`Realization.eq_of_reduce_eq_of_forcingDonorsIn` with the strongly coded forcing donors. -/
theorem eq_of_reduce_eq_stronglyCoded {R' : Realization.{u, v} (blockStage (η + 1)) M}
    (hR : R.IsConsistent) (hR' : R'.IsConsistent) (hl : R.HasLegalTypes)
    (hl' : R'.HasLegalTypes) (h𝒮 : ∀ x : R.Occurrence, x.type.rows.IsStronglyCoded)
    (h𝒮' : ∀ x : R'.Occurrence, x.type.rows.IsStronglyCoded)
    (hrec : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (hrec' : R'.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (h : R.reduce (isSuccPrelimit_blockStage η) = R'.reduce (isSuccPrelimit_blockStage η)) :
    R = R' :=
  eq_of_reduce_eq_of_forcingDonorsIn (forcingDonorsIn_stronglyCoded_blockStage η) hR hR' hl hl'
    h𝒮 h𝒮' hrec hrec' h

/-- **A strongly coded realization is the candidate of its reduction** (native construction):
`Realization.eq_stableCandidate_of_reduce_eq_in_of_isCovering` with the strongly coded forcing
donors.  An exactly consistent, covering realization at `λ_{η+1}` with legal types whose rows are
strongly coded, with finite-extension receiving for the strongly coded legal donors, is the stable
candidate of its reduction to `λ_η`, which is stably lawful by exact consistency, covering and
legal types. -/
theorem eq_stableCandidate_stronglyCoded
    (h𝒮 : ∀ x : R.Occurrence, x.type.rows.IsStronglyCoded) (hR : R.IsConsistent)
    (hcov : R.IsCovering) (hl : R.HasLegalTypes)
    (hrec : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded) :
    R = (R.reduce (isSuccPrelimit_blockStage η)).stableCandidate
      (isStablyLawful_of_hasLegalTypes (hR.reduce _) (hcov.reduce _) (hl.reduce _)) :=
  eq_stableCandidate_of_reduce_eq_in_of_isCovering (forcingDonorsIn_stronglyCoded_blockStage η)
    h𝒮 hR hcov hl hrec

end Realization

end VaughtConjecture

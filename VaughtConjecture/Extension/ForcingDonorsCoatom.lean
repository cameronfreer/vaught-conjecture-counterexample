/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.ForcingDonors
import VaughtConjecture.Extension.PartBelowFullGrade
import VaughtConjecture.Extension.TiedApex

/-!
# Forcing donors from the coatom extension property

Roadmap, Layer 3 (the finite construction for forcing donors), for Layer 4, output 2
(`ForcingDonors`, in `VaughtConjecture.Continuation.Normalization`); semantic contract, items 3–4.

Write `λ_η = blockStage η`.  **The coatom extension property at `λ_{η+1}` implies the forcing-donor
property at `η`** (`forcingDonors_of_hasCoatomExtensions`), at every input: every arity `k`, every
cell, every threshold.  Hence the coatom extension property with apex implies it too
(`forcingDonors_of_hasApexCoatomExtensions`).  So `ForcingDonors ξ` for all `ξ < ω₁` follows from
`StageType.HasCoatomExtensions (blockStage (ξ + 1))` for all `ξ < ω₁`
(`forcingDonors_of_forall_hasCoatomExtensions`), hence from
`StageType.HasApexCoatomExtensions (blockStage η)` for all `η < ω₁`
(`forcingDonors_of_forall_hasApexCoatomExtensions`).  The construction uses no completion below the
full grade, no tie at an intermediate grade, and nothing about the stage beyond its being a block
stage.

**Forcing through the row of a cell** (`StageType.forcesThreshold_of_row_le_of_grade_le`, in
`VaughtConjecture.Stage.Threshold`).  Let `C` and `x` be cells of `q` labelled the formal top, with
`x` and the cell `e` carrying `d` both below `C`.  If the row of `C` is at most as large at `x` as
at `e`, and the grade of `e` is at most that of `x`, then `(q, f)` forces at `d` every threshold up
to the grades of `C` and `x`.  Locality of a lift `Q` at `C` gives
`min (Q x) (Q C) ≤ min (Q e) (Q C)` (`Label.TransformsTo.le_of_le`: monotone in the row, antitone
in the grade), and the order law bounds `Q x` and `Q C` from below.  For `x = C` this is the tie
(`StageType.forcesThreshold_of_row_le`).  Here `x` need not lie above `e`: the bound reaches `e`
through the row of `C`, and the grade of `C` may exceed the label offset of `d`.

**At the apex** (`StageType.forcesThreshold_addApex_of_label_le`).  The row of the apex
(`StageType.addApex`) is the coded copy of the labels, monotone in the labels
(`Label.monotone_blockEncode`).  So if `t` is legal below the full grade, `f` is proper, and a cell
`x` of `t` with label at least `λ_η` and at most the label of `e` has grade at least that of `e`,
then the apex added to `t`, reduced to `λ_η`, forces the grade of `x` at `d`.

**The donor.**  Let `t` be legal at `λ_{η+1}` on `k` points, `d` a cell reducing to the formal top,
and `λ_η + n ≤ q(d)`.  If `n` is at most the grade of `d`, the type `t` itself forces `n` (the order
law).  Otherwise:

1. a legal stage type `U` on `n` points has a cell `x` of grade `n` labelled exactly `λ_η + n`
   (`StageType.exists_isLegal_grade_label_coe_add`): a legal one-point type labelled `λ_η + n`
   (`StageType.exists_onePoint_label`), padded by one-point extensions over the empty face to `n`
   points (`StageType.exists_isLegal_restrictFace_castLEEmb`), cut to its part below the full grade
   (`StageType.partBelowFullGrade`), and closed by the tied apex at the cell labelled `λ_η + n`
   (`StageType.addTiedApex`);
2. `t` and `U` are amalgamated over the empty face (`StageType.exists_amalgam`), padded by one
   point, and cut to the part below the full grade; along the (now proper) faces of `t` and `U`
   nothing changes (`StageType.restrictFace_partBelowFullGrade`);
3. the apex is added.  The cell `e` carrying `d` has grade below `n` and label `q(d) ≥ λ_η + n`;
   the copy of `x` has grade `n` and label `λ_η + n`; so the apex forces `n` at `d`.

Steps 1 and 2 use the coatom extension property through one-point extensions
(`StageType.exists_extension`) and amalgams (`StageType.exists_amalgam`); step 3 uses
nothing.  The two constructions on a legal type with a proper face, the tied apex at a cell of the
face (`StageType.exists_isLegal_tiedApex`) and the apex forcing through the row
(`StageType.exists_donor_addApex_of_isLegal`), are stated separately.

**What this settles.**  Every input of `ForcingDonors η` has a donor once
`StageType.HasCoatomExtensions (blockStage (η + 1))` holds.  The inputs that no tie of full grade
can serve (`grade d < n ≤ j ≤ #(scope d)`, where `q(d) = λ_η + j`; see
`VaughtConjecture.Extension.ForcingDonors`) are served through `x`, so no completion with a tie at
an intermediate grade is needed.

**Unconditionally** (`ForcingDonorsUpTo η k M`: the inputs on `k` points at the thresholds
`n ≤ M`; `ForcingDonors η` is this at every `k` and `M`,
`forcingDonors_iff_forall_forcingDonorsUpTo`): one-point inputs up to `4`
(`forcingDonorsUpTo_one_four`), and two-point inputs up to `4` (`forcingDonorsUpTo_two_four`).
For two points at `n ≤ 2` the same apex row works over completions at the arities `0` and `1`
(`exists_forcingDonor_twoPoint_le_two`): `U` is the tied apex over the completion of the first
point of `t` with a one-point type labelled `λ_η + 2`, and `t` and `U` are the two coatom types of a
seed over the first point.  Beyond, the construction needs coatom extensions at the arity `3` and
above, still to be proved.

## Placement

Layer 3 of `roadmap/README.md` (3.1, (R6): forcing donors from the plain form).
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

/-! ### Forcing at the apex -/

section Apex

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
  (hn : 0 < n)

/-- **The apex forces through its row.**  If `t` restricts to `p` along a proper face `f`, the cell
`d` of `p` is carried to `e`, and a cell `x` of `t` with label at least `β` (zero or a limit) and at
most the label of `e` has grade at least that of `e`, then the reduction to `β` of `t` with the
apex added forces the grade of `x` at `d`. -/
theorem forcesThreshold_addApex_of_label_le {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    {k : ℕ} {f : Fin k ↪ Fin n} (hf : univ.map f ≠ univ) {p : StageType.{u} α k}
    (hfp : restrictFace f t = some p) {d : Fin p.card} {e x : Fin t.card}
    (hde : ∀ i : Fin (t.toScheme.comap f).card, (i : ℕ) = d → t.cellMap f i = e)
    (hβx : (β : Label.{u}) ≤ t.label x) (hxe : t.label x ≤ t.label e)
    (hgrade : t.toCellScheme.grade e ≤ t.toCellScheme.grade x) :
    ForcesThreshold α hβ ((t.addApex ht hn).reduce hβ) f (p.reduce hβ) d
      (t.toCellScheme.grade x) := by
  set D := t.addApex ht hn
  have hfp' : restrictFace f (D.reduce hβ) = some (p.reduce hβ) := by
    rw [restrictFace_reduce, restrictFace_addApex ht hn f hf, hfp, Option.map_some]
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
      (mem_range_castSucc_of_addApex ht hn f hf) (i := ⟨i, hlt⟩) rfl, hde ⟨i, hlt⟩ hi]
  · -- the reduced label of the apex is `Label.reduce β ⊤` (`reduce_label`)
    exact Label.reduce_eq_top_iff.mpr ((addApex_label_last ht hn).symm ▸ le_top)
  · exact Label.reduce_eq_top_iff.mpr (hβx.trans_eq (addApex_label_castSucc ht hn x).symm)
  · -- the reduction keeps the rows; both entries are read in the row of the apex
    refine le_of_eq_of_le (Scheme.appendFullCell_row_last (h := ht.not_le) _)
      (le_of_le_of_eq ?_ (Scheme.appendFullCell_row_last (h := ht.not_le) _).symm)
    rw [apexRow_castSucc, apexRow_castSucc]
    exact monotone_blockEncode hxe
  · -- the grade of the apex is `n`, above every grade of `t`
    rw [show (D.reduce hβ).toCellScheme.grade (Fin.last _) = n from
      Scheme.appendFullCellScheme_grade_last _ _]
    exact (ht.grade_lt x).le

end Apex

/-! ### Two constructions on a legal type -/

section Constructions

variable {α : Ordinal.{u}} {k l N : ℕ}

/-- **A cell of full grade tied to a cell of a proper face.**  If `W` is legal on `N` points, `r`
is its face along a proper face `h`, and the label of the cell `i` of `r` is self-visible at `N`,
then some legal `U` on `N` points has the proper faces of `W` and a cell of grade `N` labelled as
`i`: the tied apex over the part of `W` below the full grade. -/
theorem exists_isLegal_tiedApex {W : StageType.{u} α N} (hW : W.IsLegal) {h : Fin l ↪ Fin N}
    (hh : univ.map h ≠ univ) {r : StageType.{u} α l} (hhr : restrictFace h W = some r)
    (i : Fin r.card) (hv : IsSelfVisible N (r.label i)) :
    ∃ U : StageType.{u} α N, U.IsLegal ∧
      (∀ {k : ℕ} (g : Fin k ↪ Fin N), univ.map g ≠ univ → restrictFace g U = restrictFace g W) ∧
      ∃ x : Fin U.card, U.toCellScheme.grade x = N ∧ U.label x = r.label i := by
  have hN := pos_of_univ_map_ne hh
  set T := W.partBelowFullGrade
  have hT := hW.isLegalBelowFullGrade_partBelowFullGrade
  obtain ⟨j, -, hjl, -⟩ := exists_cellMap_of_restrictFace_eq
    ((restrictFace_partBelowFullGrade W h hh).trans hhr) i
  have he : IsSelfVisible N (T.label (T.cellMap h j)) := hjl ▸ hv
  exact ⟨T.addTiedApex hT he hN, isLegal_addTiedApex hT he hN,
    fun g hg ↦ (restrictFace_addTiedApex hT he hN g hg).trans
      (restrictFace_partBelowFullGrade W g hg),
    Fin.last _, Scheme.appendFullCellScheme_grade_last _ _,
    (addTiedApex_label_last hT he hN).trans hjl⟩

/-- **A donor from a legal type with two proper faces.**  If `W` is legal on `N` points with faces
`t` and `U` along proper faces `g` and `h`, and a cell `x` of `U` with label at least `β` (zero or a
limit) and at most the label of the cell `d` of `t` has grade at least that of `d`, then the apex
over the part of `W` below the full grade is a legal `D` with `t` as its face along `g`, whose
reduction to `β` forces the grade of `x` at `d`. -/
theorem exists_donor_addApex_of_isLegal {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    {W : StageType.{u} α N} (hW : W.IsLegal) {g : Fin k ↪ Fin N} (hg : univ.map g ≠ univ)
    {t : StageType.{u} α k} (hgt : restrictFace g W = some t) {h : Fin l ↪ Fin N}
    (hh : univ.map h ≠ univ) {U : StageType.{u} α l} (hhU : restrictFace h W = some U)
    {d : Fin t.card} {x : Fin U.card} (hβx : (β : Label.{u}) ≤ U.label x)
    (hxd : U.label x ≤ t.label d) (hgrade : t.toCellScheme.grade d ≤ U.toCellScheme.grade x) :
    ∃ D : StageType.{u} α N, D.IsLegal ∧ restrictFace g D = some t ∧
      ForcesThreshold α hβ (D.reduce hβ) g (t.reduce hβ) d (U.toCellScheme.grade x) := by
  have hN := pos_of_univ_map_ne hg
  set T := W.partBelowFullGrade
  have hT := hW.isLegalBelowFullGrade_partBelowFullGrade
  have hTt : restrictFace g T = some t := (restrictFace_partBelowFullGrade W g hg).trans hgt
  have hTU : restrictFace h T = some U := (restrictFace_partBelowFullGrade W h hh).trans hhU
  obtain ⟨jd, hjd, hjdl, hjdg⟩ := exists_cellMap_of_restrictFace_eq hTt d
  obtain ⟨jx, -, hjxl, hjxg⟩ := exists_cellMap_of_restrictFace_eq hTU x
  refine ⟨T.addApex hT hN, isLegal_addApex hT hN, (restrictFace_addApex hT hN g hg).trans hTt, ?_⟩
  have hF := forcesThreshold_addApex_of_label_le hT hN hβ hg hTt (e := T.cellMap g jd)
    (x := T.cellMap h jx) (fun i hi ↦ congrArg (T.cellMap g) (Fin.ext (hi.trans hjd.symm)))
    (hjxl ▸ hβx) (by rw [hjxl, hjdl]; exact hxd) (by rw [hjdg, hjxg]; exact hgrade)
  rwa [hjxg] at hF

end Constructions

/-! ### Legal types with a prescribed proper face, from coatom extensions -/

section Padding

variable {α : Ordinal.{u}} {k N : ℕ}

/-- **A legal type with a cell of full grade labelled `β + n`**, for `2 ≤ n`, `β` zero or a limit,
and `β + n < α`, under the coatom extension property: a legal one-point type labelled `β + n`,
padded to `n` points, cut to its part below the full grade, and closed by the tied apex at the cell
labelled `β + n`. -/
theorem exists_isLegal_grade_label_coe_add (hext : HasCoatomExtensions.{u} α) {β : Ordinal.{u}}
    (hβ : Order.IsSuccPrelimit β) {n : ℕ} (hn : 2 ≤ n) (hlt : β + n < α) :
    ∃ U : StageType.{u} α n, U.IsLegal ∧ ∃ x : Fin U.card, U.toCellScheme.grade x = n ∧
      U.label x = ((β + n : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨t₁, ht₁, i₁, -, hi₁⟩ :=
    exists_onePoint_label (α := α) (isSelfVisible_coe_add hβ (by omega : 1 ≤ n)) hlt
  obtain ⟨V, hV, hVt⟩ := exists_isLegal_restrictFace_castLEEmb hext ht₁ (by omega : 1 ≤ n)
  obtain ⟨U, hU, -, x, hx, hxl⟩ := exists_isLegal_tiedApex hV (univ_map_castLEEmb_ne (by omega))
    hVt i₁ (by rw [hi₁]; exact isSelfVisible_coe_add hβ le_rfl)
  exact ⟨U, hU, x, hx, hxl.trans hi₁⟩

end Padding

end StageType

/-! ### Forcing donors -/

section Forcing

variable {η : Ordinal.{u}}

/-- **The coatom extension property at `λ_{η+1}` gives forcing donors at `η`**, at every input:
the order law when the threshold is at most the grade of the cell, and otherwise the apex over
the amalgam of the input with a legal type carrying a cell of grade `n` labelled `λ_η + n`, which
forces `n` through the row of the apex. -/
theorem forcingDonors_of_hasCoatomExtensions
    (hext : StageType.HasCoatomExtensions.{u} (blockStage (η + 1))) : ForcingDonors.{u} η := by
  intro k t ht d hd n hn
  have hβ := isSuccPrelimit_blockStage η
  -- The order law.
  by_cases hgd : n ≤ (t.reduce hβ).toCellScheme.grade d
  · exact ⟨k, t, Function.Embedding.refl _, ht, StageType.restrictFace_refl t,
      StageType.forcesThreshold_of_le_grade (StageType.restrictFace_refl _) hd hgd⟩
  rw [not_le] at hgd
  have hgd' : t.toCellScheme.grade d < n := hgd
  have hn2 : 2 ≤ n := lt_of_le_of_lt (t.isWellFormed.isWellFormed.grade_pos d) hgd'
  -- 1. A legal type `U` on `n` points with a cell `xU` of grade `n` labelled `λ_η + n`.
  obtain ⟨U, hU, xU, hxUg, hxUl⟩ :=
    StageType.exists_isLegal_grade_label_coe_add hext hβ hn2 (coe_add_lt_blockStage_add_one n)
  -- 2. The amalgam of `t` and `U` over the empty face, padded by one point.
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    (t.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin k))
  obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp
    (U.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  rw [StageType.eq_of_zero q₀ p₀] at hq₀
  obtain ⟨N, W, i, j, hW, hWt, hWU, -⟩ := StageType.exists_amalgam hext ht hU hp₀ hq₀
  obtain ⟨W', hW', hW'W⟩ := StageType.exists_extension hext hW
  -- the faces of `t` and `U` miss the last point
  have hproper {l : ℕ} (g : Fin l ↪ Fin N) : univ.map (g.trans Fin.castSuccEmb) ≠ univ :=
    fun h ↦ by
      have hmem := mem_univ (Fin.last N)
      rw [← h, mem_map] at hmem
      obtain ⟨y, -, hy⟩ := hmem
      exact Fin.castSucc_ne_last _ hy
  -- 3. The apex over the part below the full grade.
  obtain ⟨D, hD, hDt, hF⟩ := StageType.exists_donor_addApex_of_isLegal hβ hW' (hproper i)
    ((StageType.restrictFace_trans _ _ _ hW'W).symm.trans hWt) (hproper j)
    ((StageType.restrictFace_trans _ _ _ hW'W).symm.trans hWU) (d := d) (x := xU)
    (by rw [hxUl]; exact Label.coe_le_coe_add _ _) (by rw [hxUl]; exact hn)
    (by rw [hxUg]; exact hgd'.le)
  exact ⟨N + 1, D, _, hD, hDt, by rwa [hxUg] at hF⟩

/-- **The coatom extension property with apex at `λ_{η+1}` gives forcing donors at `η`.** -/
theorem forcingDonors_of_hasApexCoatomExtensions
    (hext : StageType.HasApexCoatomExtensions.{u} (blockStage (η + 1))) : ForcingDonors.{u} η :=
  forcingDonors_of_hasCoatomExtensions hext.hasCoatomExtensions

/-- **Forcing donors at every countable block index from the coatom extension property at every
countable successor block stage**: `ForcingDonors ξ` for `ξ < ω₁` follows from
`StageType.HasCoatomExtensions (blockStage (ξ + 1))` for `ξ < ω₁`. -/
theorem forcingDonors_of_forall_hasCoatomExtensions
    (hext : ∀ ξ < Ordinal.omega 1, StageType.HasCoatomExtensions.{0} (blockStage (ξ + 1))) :
    ∀ ξ < Ordinal.omega 1, ForcingDonors.{0} ξ := fun ξ hξ ↦
  forcingDonors_of_hasCoatomExtensions (hext ξ hξ)

/-- **Forcing donors at every countable block index from the coatom extension property with apex
at every countable block stage**: the hypothesis `ForcingDonors ξ` for `ξ < ω₁` follows from
`StageType.HasApexCoatomExtensions (blockStage η)` for `η < ω₁`, at `η = ξ + 1`. -/
theorem forcingDonors_of_forall_hasApexCoatomExtensions
    (hext : ∀ η < Ordinal.omega 1, StageType.HasApexCoatomExtensions.{0} (blockStage η)) :
    ∀ ξ < Ordinal.omega 1, ForcingDonors.{0} ξ := fun _ hξ ↦
  forcingDonors_of_hasApexCoatomExtensions (hext _ ((Cardinal.isSuccLimit_omega 1).succ_lt hξ))

end Forcing

/-! ### Unconditional cases through the apex row -/

section Unconditional

variable {η : Ordinal.{u}}

/-- **Forcing donors for two-point types at the thresholds `n ≤ 2`, unconditionally**, including
the inputs no tie serves (a cell of grade `1` and scope `{0, 1}` labelled exactly `λ_η + 2`, at
the threshold `2`).  Beyond the order law, `n = 2` and the cell has grade `1`.  With `p` the first
point of `t`: the completion of the seed of `p` and a one-point type labelled `λ_η + 2`, with a cell
of grade `2` tied to that label, gives a legal `U` on two points with first point `p`; the
completion of the seed of `t` and `U` (at the arity `1`) has `t` and `U` as proper faces, and the
apex over its part below the full grade forces `2` through the copy of the tied cell. -/
theorem exists_forcingDonor_twoPoint_le_two (t : StageType.{u} (blockStage (η + 1)) 2)
    (ht : t.IsLegal) (d : Fin t.card) (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤)
    (n : ℕ) (hn : ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d) (hn2 : n ≤ 2) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 2 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
        (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
          d n := by
  have hβ := isSuccPrelimit_blockStage η
  have hα := isSuccPrelimit_blockStage (η + 1)
  -- The order law.
  by_cases hgd : n ≤ (t.reduce hβ).toCellScheme.grade d
  · exact ⟨2, t, Function.Embedding.refl _, ht, StageType.restrictFace_refl t,
      StageType.forcesThreshold_of_le_grade (StageType.restrictFace_refl _) hd hgd⟩
  rw [not_le] at hgd
  have hgd' : t.toCellScheme.grade d < n := hgd
  have hn' : n = 2 := by have := t.isWellFormed.isWellFormed.grade_pos d; omega
  subst hn'
  -- The first point `p` of `t`, and a one-point type `t₁` labelled `λ_η + 2`.
  obtain ⟨p, hp⟩ := StageType.exists_restrictFace_castSuccEmb_of_two t
  have hpl : p.IsLegal := ht.restrictFace _ hp
  obtain ⟨t₁, ht₁, i₁, -, hi₁⟩ := StageType.exists_onePoint_label (α := blockStage (η + 1))
    (isSelfVisible_coe_add hβ (by omega : 1 ≤ 2)) (coe_add_lt_blockStage_add_one 2)
  obtain ⟨e₀, he₀⟩ := Option.isSome_iff_exists.mp (p.isSome_restrictFace_of_zero Fin.castSuccEmb)
  obtain ⟨e₁, he₁⟩ := Option.isSome_iff_exists.mp (t₁.isSome_restrictFace_of_zero Fin.castSuccEmb)
  rw [StageType.eq_of_zero e₁ e₀] at he₁
  -- `U`: first point `p`, and a cell `x` of grade `2` labelled `λ_η + 2`.
  obtain ⟨F₀⟩ := Seed.nonempty_completionBelowFullGrade_of_le_two
    (Seed.ofCoatoms hpl ht₁ he₀ he₁) (by omega)
  obtain ⟨U, hU, hUW, x, hx, hxl⟩ := StageType.exists_isLegal_tiedApex (r := t₁)
    (F₀.isLegal_completion hα) Coatom.univ_map_right_ne (F₀.restrictFace_right_completion hα) i₁
    (by rw [hi₁]; exact isSelfVisible_coe_add hβ le_rfl)
  have hUp : StageType.restrictFace Fin.castSuccEmb U = some p :=
    (hUW _ Coatom.univ_map_left_ne).trans (F₀.restrictFace_left_completion hα)
  -- The completion of the seed of `t` and `U`, and the apex over it.
  obtain ⟨F⟩ := Seed.nonempty_completionBelowFullGrade_of_le_two
    (Seed.ofCoatoms ht hU hp hUp) (by omega)
  obtain ⟨D, hD, hDt, hF⟩ := StageType.exists_donor_addApex_of_isLegal (t := t) (U := U) hβ
    (F.isLegal_completion hα) Coatom.univ_map_left_ne (F.restrictFace_left_completion hα)
    Coatom.univ_map_right_ne (F.restrictFace_right_completion hα) (d := d) (x := x)
    (by rw [hxl, hi₁]; exact Label.coe_le_coe_add _ _) (by rw [hxl, hi₁]; exact hn)
    (by rw [hx]; exact hgd'.le)
  exact ⟨3, D, _, hD, hDt, by rwa [hx] at hF⟩

end Unconditional

/-! ### Forcing donors by arity and threshold -/

section UpTo

/-- **Forcing donors on `k` points up to the threshold `M`**: the inputs of `ForcingDonors η` on
`k` points at the thresholds `n ≤ M`. -/
def ForcingDonorsUpTo (η : Ordinal.{u}) (k M : ℕ) : Prop :=
  ∀ t : StageType.{u} (blockStage (η + 1)) k, t.IsLegal → ∀ d : Fin t.card,
    (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤ → ∀ n ≤ M,
      ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label d →
        ∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin k ↪ Fin m),
          D.IsLegal ∧ StageType.restrictFace g D = some t ∧
          StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
            (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η)) d n

variable {η : Ordinal.{u}}

/-- `ForcingDonors η` is `ForcingDonorsUpTo η k M` at every arity `k` and every bound `M`. -/
theorem forcingDonors_iff_forall_forcingDonorsUpTo :
    ForcingDonors.{u} η ↔ ∀ k M, ForcingDonorsUpTo.{u} η k M :=
  ⟨fun hF _ _ t ht d hd n _ hn ↦ hF t ht d hd n hn,
    fun hF k t ht d hd n hn ↦ hF k n t ht d hd n le_rfl hn⟩

/-- **One-point inputs up to the threshold `4`, unconditionally**
(`exists_forcingDonor_onePoint`). -/
theorem forcingDonorsUpTo_one_four : ForcingDonorsUpTo.{u} η 1 4 :=
  fun t ht d hd n hn4 hn ↦ exists_forcingDonor_onePoint t ht d hd n hn hn4

/-- **Two-point inputs up to the threshold `4`, unconditionally**: through the apex row for
`n ≤ 2` (`exists_forcingDonor_twoPoint_le_two`), through the doubling chain for `n ∈ {3, 4}`
(`exists_forcingDonor_twoPoint`). -/
theorem forcingDonorsUpTo_two_four : ForcingDonorsUpTo.{u} η 2 4 := by
  intro t ht d hd n hn4 hn
  rcases le_or_gt n 2 with h2 | h2
  · exact exists_forcingDonor_twoPoint_le_two t ht d hd n hn h2
  · exact exists_forcingDonor_twoPoint t ht d hd n (by rwa [max_eq_left (by omega : 3 ≤ n)]) hn4

/-- **Every arity and threshold under the coatom extension property** at `λ_{η+1}`. -/
theorem forcingDonorsUpTo_of_hasCoatomExtensions
    (hext : StageType.HasCoatomExtensions.{u} (blockStage (η + 1))) (k M : ℕ) :
    ForcingDonorsUpTo.{u} η k M :=
  forcingDonors_iff_forall_forcingDonorsUpTo.mp (forcingDonors_of_hasCoatomExtensions hext) k M

end UpTo

end VaughtConjecture

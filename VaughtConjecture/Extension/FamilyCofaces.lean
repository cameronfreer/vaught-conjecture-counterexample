/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Extension.SectionTheorem
import VaughtConjecture.Realization.Families

/-!
# Nonempty uniformity and dominance instances from coatom extensions

Roadmap, Layer 3, 3.4 (the cap-to-model theorem, and the apex of row 6 of the table); semantic
contract, item 5 (the four unchanged extension families).

At a stage `α` that is zero or a limit, for a legal stage type `p` on `n` points and `γ < α`:

* **uniformity** [Kni26, Lemma 4.4.2] (`StageType.nonempty_cofaces_inter_uniformityFamily`): some
  coface of `p` has a label in `[γ, γ + ω)`, under the coatom extension property
  `StageType.HasCoatomExtensions α`.  No hypothesis on `γ` is used.
* **high-arity dominance** [Kni26, Lemma 4.4.3]
  (`StageType.nonempty_cofaces_inter_dominanceFamily`): some coface of `p` has a label above `γ`
  at a cell of grade `n + 1`, under the coatom extension property with apex
  `StageType.HasApexCoatomExtensions α`.

Neither uses top-freeness of `p`.

**The donor.**  A legal stage type on one point with a single cell, of grade `1`, carrying any
label `c < α` self-visible at `1` (`StageType.exists_onePoint_label`).  It is the cell-less stage
type on one point, legal below the full grade, with the apex added (`StageType.addApex`), a cell
labelled `⊤`, and then capped at `c` ([Kni26, Lemma 2.5.8],
`CellScheme.Rows.IsLawful.min_const_of_isSelfVisible`).  The one-point scheme with the bottom rows
(`Scheme.onePoint`) does not do: a cell whose row is bottom at itself has the bottom label in every
lawful section (`CellScheme.Rows.IsLawful.eq_bot_of_row_self_eq_bot`), so the one-point extension
`StageType.exists_extension` gives no control over labels.

**Uniformity.**  The exact pinned extension (`StageType.exists_pinned_extension`) of `p` over the
empty face, with the donor of a label `c ∈ (γ, γ + ω)`, is a coface of `p` whose face along the new
point is the donor, so it has the label `c`.

**Dominance.**  The plain coatom extension property gives no control over the label of a cell of
full grade.  The exact pinned extension with apex (`StageType.exists_pinned_extension_apex`) is
the induction of `StageType.exists_pinned_extension` with the apex form of the coatom extension at
its last step; the apex is a cell of full scope and grade `n + 1` whose label is the largest,
hence at least the label `c > γ` of the donor.  The apex survives the final reindexing along a
bijection of points (`StageType.exists_apex_of_reindex`).  For `n = 0` the donor is itself the
coface.

## Placement

This file belongs to Layer 3, 3.4, of `roadmap/README.md`.

## References

The nonemptiness of the uniformity and dominance instances is [Kni26, Lemmas 4.4.2 and 4.4.3];
the coatom extension with apex is [Kni26, Corollary 4.3.22]; capping is [Kni26, Lemma 2.5.8].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-! ### A one-point stage type with a prescribed label -/

/-- The scheme on one point with no cells: legal below the full grade, since every graded face has
a positive grade. -/
private def cellless : Scheme.{u} 1 where
  card := 0
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, Fin.elim0, Fin.elim0⟩
  rows := CellScheme.Rows.bot _

private theorem isLegalBelowFullGrade_cellless : cellless.{u}.IsLegalBelowFullGrade where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ d.elim0⟩⟩
  isCoded s := s.elim0
  isConsistent := CellScheme.Rows.isConsistent_bot
  isBountiful := CellScheme.Rows.isBountiful_bot
  grade_lt d := d.elim0
  exists_gradedIndex_eq _ hX hX1 := absurd hX.2.1 (by omega)

/-- **A legal one-point stage type with a prescribed label**: for `c < α` self-visible at `1`,
some legal stage type on one point has a cell of grade `1` labelled `c`. -/
theorem exists_onePoint_label {c : Ordinal.{u}} (hc : IsSelfVisible 1 (c : Label.{u}))
    (hcα : c < α) :
    ∃ d : StageType.{u} α 1, d.IsLegal ∧ ∃ i, d.toCellScheme.grade i = 1 ∧ d.label i = c := by
  set t0 : StageType.{u} α 1 := ⟨cellless, fun _ ↦ ⊥, isLegalBelowFullGrade_cellless.isWellFormed,
    isLegalBelowFullGrade_cellless.isCoded, CellScheme.Rows.isLawful_const_bot,
    fun _ ↦ atStage_bot⟩
  set t := t0.addApex isLegalBelowFullGrade_cellless one_pos
  have hgr (d : Fin t.card) : t.toCellScheme.grade d ≤ 1 :=
    (t.isWellFormed.isWellFormed.grade_le_card d).trans ((card_le_univ _).trans_eq (by simp))
  refine ⟨⟨t.toScheme, fun d ↦ min (t.label d) c, t.isWellFormed, t.isCoded,
    t.isLawful.min_const_of_isSelfVisible hgr hc, fun _ ↦ .inl ((min_le_right _ _).trans_lt ?_)⟩,
    isLegal_addApex _ one_pos, Fin.last _, Scheme.appendFullCellScheme_grade_last _ _, ?_⟩
  · exact_mod_cast hcα
  · -- the label of the capped type at the apex is `min ⊤ c`
    change min (t.label (Fin.last _)) _ = _
    rw [addApex_label_last, min_top_left]

/-- A legal stage type on one point is a coface of the stage type on no points. -/
theorem mem_cofaces_of_zero {p : StageType.{u} α 0} {d : StageType.{u} α 1} (hd : d.IsLegal) :
    d ∈ p.cofaces := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (d.isSome_restrictFace_of_zero Fin.castSuccEmb)
  exact ⟨hd, hq.trans (congrArg some (eq_of_zero q p))⟩

/-- A face of a stage type carries its labels and grades on cells of the stage type. -/
theorem exists_label_eq_of_restrictFace_eq {Q : StageType.{u} α n} {g : Fin m ↪ Fin n}
    {d : StageType.{u} α m} (h : restrictFace g Q = some d) (i : Fin d.card) :
    ∃ j, Q.label j = d.label i ∧ Q.toCellScheme.grade j = d.toCellScheme.grade i := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff Q g).mp h
  exact ⟨Q.cellMap g i, rfl, rfl⟩

/-- The pinned extension over the empty face of a one-point donor `d`: a coface of `p` with the
labels of `d`. -/
private theorem exists_pinned_extension_empty (hext : HasCoatomExtensions.{u} α)
    {p : StageType.{u} α n} (hp : p.IsLegal) {d : StageType.{u} α 1} (hd : d.IsLegal) :
    ∃ Q ∈ p.cofaces, restrictFace (extendByLast Function.Embedding.ofIsEmpty) Q = some d := by
  obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp
    (p.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  obtain ⟨Q, hQ, hQp, hQd⟩ := exists_pinned_extension hext hp hp0 hd (mem_cofaces_of_zero hd).2
  exact ⟨Q, ⟨hQ, hQp⟩, hQd⟩

/-! ### Uniformity -/

/-- **Nonempty uniformity instances** [Kni26, Lemma 4.4.2]: under the coatom extension property at
a stage `α` that is zero or a limit, for `γ < α`, some coface of a legal stage type has a label in
`[γ, γ + ω)`.  The donor is the one-point stage type with a label in `(γ, γ + ω)` self-visible at
`1`. -/
theorem nonempty_cofaces_inter_uniformityFamily (hext : HasCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) {p : StageType.{u} α n} (hp : p.IsLegal) {γ : Ordinal.{u}}
    (hγα : γ < α) : (p.cofaces ∩ uniformityFamily γ).Nonempty := by
  obtain ⟨c, hγc, hcγ, hc⟩ := exists_lt_lt_isSelfVisible
    (Ordinal.isSuccLimit_add γ Ordinal.isSuccLimit_omega0).isSuccPrelimit
    (lt_add_of_pos_right γ Ordinal.omega0_pos) 1
  obtain ⟨d, hd, i, -, hdi⟩ :=
    exists_onePoint_label hc (hcγ.trans_le (Ordinal.add_omega0_le_of_isSuccPrelimit hα hγα))
  obtain ⟨Q, hQ, hQd⟩ := exists_pinned_extension_empty hext hp hd
  obtain ⟨j, hj, -⟩ := exists_label_eq_of_restrictFace_eq hQd i
  exact ⟨Q, hQ, j, by rw [hj, hdi]; exact_mod_cast hγc.le, by rw [hj, hdi]; exact_mod_cast hcγ⟩

/-! ### The pinned extension with apex -/

/-- **The apex survives reindexing**: if a reindexing of `t` along a bijection of points has a cell
of full scope and grade `j` carrying the largest label, so does `t`. -/
theorem exists_apex_of_reindex {t : StageType.{u} α k} (e : Fin k ≃ Fin k) {j : ℕ}
    (h : ∃ a, (t.reindex e).toCellScheme.gradedIndex a = (univ, j) ∧
      ∀ b, (t.reindex e).label b ≤ (t.reindex e).label a) :
    ∃ a, t.toCellScheme.gradedIndex a = (univ, j) ∧ ∀ b, t.label b ≤ t.label a := by
  obtain ⟨a, ha, hmax⟩ := h
  refine ⟨t.cellMap e.toEmbedding a, ?_, fun b ↦ ?_⟩
  · rw [← t.toScheme.map_comap_gradedIndex e.toEmbedding a]
    -- the scheme of `t.reindex e` is the restriction of the scheme of `t` along `e`
    change Prod.map _ id ((t.reindex e).toCellScheme.gradedIndex a) = _
    rw [ha]
    simp
  · obtain ⟨b, rfl⟩ := t.toScheme.surjective_cellMap_equiv e b
    exact hmax b

/-- **The exact pinned extension with apex** (row 6 of the table of Layer 3, 3.4, with the apex of
[Kni26, Corollary 4.3.22]): under the coatom extension property with apex, over a closed face `f`
of a legal `P` that is not onto, the one-point pinned extension of `P` exact over `f` can be taken
with a cell of full scope and full grade `n + 1` carrying the largest label.  The induction of
`exists_pinned_extension`, with the apex form at the last coatom step; the apex is carried through
the final reindexing (`exists_apex_of_reindex`). -/
theorem exists_pinned_extension_apex (hext : HasApexCoatomExtensions.{u} α)
    {P : StageType.{u} α n} (hP : P.IsLegal) {f : Fin m ↪ Fin n} {p : StageType.{u} α m}
    {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hf : ¬ Function.Surjective f) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d ∧
      ∃ a, Q.toCellScheme.gradedIndex a = (univ, n + 1) ∧ ∀ e, Q.label e ≤ Q.label a := by
  induction hk : n - m using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    subst hk
    -- A point `x` outside the face whose addition keeps the face closed, as in
    -- `exists_pinned_extension`.
    have hfP : univ.map f ∈ P.toCellScheme.faces := ((restrictFace_eq_some_iff P f).mp hPf).1
    have hplan := P.isWellFormed.isWellFormed.isPlan
    rw [P.isWellFormed.ground_eq] at hplan
    have hne : univ.map f ≠ univ := fun he ↦ hf fun y ↦ by
      have hy : y ∈ univ.map f := he ▸ mem_univ y
      simpa using hy
    obtain ⟨x, hx, hxP⟩ := hplan.exists_insert_mem hfP hne
    have hx' : x ∉ Set.range f := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set f' := Fin.Embedding.snoc f hx'
    have hff' : Fin.castSuccEmb.trans f' = f := Fin.Embedding.init_snoc f hx'
    have hf'P : univ.map f' ∈ P.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    have hPf' : restrictFace f' P = some (P.comap f' hf'P) := restrictFace_of_mem P f' hf'P
    have hp'p : restrictFace Fin.castSuccEmb (P.comap f' hf'P) = some p := by
      rw [restrictFace_trans P f' _ hPf', hff', hPf]
    have hface {Q : StageType.{u} α (n + 1)} {t : StageType.{u} α (m + 2)}
        (hQt : restrictFace (extendByLast f') Q = some t)
        (htd : restrictFace (extendByLast Fin.castSuccEmb) t = some d) :
        restrictFace (extendByLast f) Q = some d := by
      rw [← hff', ← extendByLast_trans, ← restrictFace_trans Q _ _ hQt, htd]
    by_cases hsurj : Function.Surjective f'
    · -- The last coatom step, in the apex form.
      obtain ⟨t, ht, htp', htd, hapex⟩ :=
        hext m _ d p (hP.restrictFace f' hPf') hd hp'p hdp
      obtain ⟨Q, hQ, hQP, hQt⟩ := exists_pinned_extension_of_surjective hsurj hPf' ht htp'
      refine ⟨Q, hQ, hQP, hface hQt htd, ?_⟩
      obtain rfl : n = m + 1 := le_antisymm
        (by simpa using Fintype.card_le_of_surjective f' hsurj)
        (by simpa using Fintype.card_le_of_embedding f')
      set E := Equiv.ofBijective (extendByLast f')
        ((Fintype.bijective_iff_injective_and_card _).mpr ⟨(extendByLast f').injective, rfl⟩)
      have hE : E.toEmbedding = extendByLast f' := Function.Embedding.ext fun _ ↦ rfl
      have hQE : Q.reindex E = t := by
        have h := restrictFace_equiv Q E
        rw [hE, hQt] at h
        exact (Option.some_injective _ h).symm
      exact exists_apex_of_reindex E (hQE ▸ hapex)
    · obtain ⟨t, ht, htp', htd⟩ :=
        hext.hasCoatomExtensions m _ d p (hP.restrictFace f' hPf') hd hp'p hdp
      have hmn : m < n := by
        refine lt_of_le_of_ne (by simpa using Fintype.card_le_of_embedding f) fun he ↦ hf ?_
        exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp [he]⟩).2
      obtain ⟨Q, hQ, hQP, hQt, hapex⟩ := ih (n - (m + 1)) (by omega) hPf' ht htp' hsurj rfl
      exact ⟨Q, hQ, hQP, hface hQt htd, hapex⟩

/-! ### Dominance -/

/-- **Nonempty dominance instances** [Kni26, Lemma 4.4.3]: under the coatom extension property
with apex at a stage `α` that is zero or a limit, for `γ < α`, some coface of a legal stage type on
`n` points has a label above `γ` at a cell of grade `n + 1`: the apex of the pinned extension of a
donor with a label in `(γ, α)` self-visible at `1`. -/
theorem nonempty_cofaces_inter_dominanceFamily (hext : HasApexCoatomExtensions.{u} α)
    (hα : Order.IsSuccPrelimit α) {p : StageType.{u} α n} (hp : p.IsLegal) {γ : Ordinal.{u}}
    (hγα : γ < α) : (p.cofaces ∩ dominanceFamily γ).Nonempty := by
  obtain ⟨c, hγc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα hγα 1
  obtain ⟨d, hd, i, hgi, hdi⟩ := exists_onePoint_label hc hcα
  have hγd : (γ : Label.{u}) < d.label i := by rw [hdi]; exact_mod_cast hγc
  cases n with
  | zero => exact ⟨d, mem_cofaces_of_zero hd, i, hgi, hγd⟩
  | succ n =>
    obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp
      (p.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin (n + 1)))
    obtain ⟨Q, hQ, hQp, hQd, a, ha, hmax⟩ := exists_pinned_extension_apex hext hp hp0 hd
      (mem_cofaces_of_zero hd).2 fun h ↦ (h 0).elim fun j ↦ j.elim0
    obtain ⟨j, hj, -⟩ := exists_label_eq_of_restrictFace_eq hQd i
    exact ⟨Q, ⟨hQ, hQp⟩, a, congrArg Prod.snd ha, hγd.trans_le (hj ▸ hmax j)⟩

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CodingExamples
import VaughtConjecture.Extension.StronglyCodedAmalgamation
import VaughtConjecture.Language.Density
import VaughtConjecture.Realization.Expansion

/-!
# Occurrences whose rows are not strongly coded

Every receiving realization at a positive stage, every model at any stage, and every structure
satisfying the density sentence realizes a type whose rows violate the range clause (5) of
[AFK26, Definition 4.29].  Under every reading of the printed base symbols satisfying
`baseLanguage.SymbolReading.PresentsStronglyCoded` (a printed symbol holds only of tuples carrying
a type with strongly coded rows), a structure satisfying the density sentence cannot satisfy both
the clause (Singletons) of [AFK26, Definition 4.13] and the first clause of
[AFK26, Definition 4.22 (b)] at arity `1`, whatever the reading of `P_1`.  Neither clause is
claimed to fail on its own.  The conclusion is restricted to such readings; the comparison of the
density sentence with the sentence `σ[L]` itself is not proved here (see the last paragraph).

Results are marked **[native]** (statements about realizations and structures of the base
language) or **[printed correspondence]** (statements about readings of the printed symbols).

**The range clause** [native].  Clause (5) asks of each row `ℓ_d` that
`range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : n ∈ ω, i ≤ g(d) + 1}`.  For the rows of a scheme this is
`CellScheme.Rows.IsStronglyCodedAt`, as a set inclusion
(`CellScheme.Rows.isStronglyCodedAt_iff_range_subset`).  `CodingExamples.pointRow 3` is a legal
scheme on one point whose only cell has grade `1` and row value `3 > 1 + 1`
(`Scheme.isLegal_pointRow_three`, `Scheme.pointRow_three_row`,
`Scheme.not_isStronglyCoded_pointRow_three`).

**The occurrence** [native].  Over a typed empty tuple, which exists on a nonempty carrier under
exact consistency and covering (`Realization.exists_eval_zero`), the bottom labelling of every
legal one-point scheme is a coface (`Realization.mem_cofaces_toStageType`).  Hence:
* with the finite-cut receiving property at a positive stage, at the cutoff `0`, some one-point
  tuple has a type on that scheme (`Realization.exists_eval_toScheme_eq_of_hasFiniteCutReceiving`);
* in a model, at every stage, by generalized saturation, with no cutoff
  (`Realization.IsModel.exists_eval_toScheme_eq`).
For the scheme `pointRow 3` the point of that tuple lies in typed tuples, and every typed tuple
through it has rows that are not strongly coded
(`Realization.exists_point_not_isStronglyCoded_of_hasFiniteCutReceiving`,
`Realization.IsModel.exists_point_not_isStronglyCoded`): a strongly coded type has strongly coded
faces (`StageType.isStronglyCoded_of_restrictFace`).  The structure forms are
`baseLanguage.exists_not_isStronglyCoded_of_realize_densitySentence` and
`baseLanguage.exists_not_isStronglyCoded_of_realize_fourFamilySentence`.  At stage `0` there is no
permitted cutoff, so receiving alone is vacuous there (`Realization.hasFiniteCutReceiving_zero`);
this is why the receiving forms assume a positive stage.

**Invariance of the offending row** [native].
* **The cap.**  Receiving at the cutoff `c` returns a member of the receiving family, whose scheme,
  rows included, is the donor's; the cutoff caps the labels only, `min (q.label i) c =
  min (d.label i) c` (`StageType.isStronglyCoded_iff_of_mem_receivingFamily`).  Stage reduction
  keeps the scheme as well (`StageType.isStronglyCoded_reduce_iff`).  The truncation of
  [AFK26, Definition 4.10] also leaves the rows: it sends `(c, Σ, p)` to `(c, Σ, trunc_β ∘ p)`.
* **Cell renaming.**  `Scheme.IsCellRenaming S T e` transcribes [AFK26, Definition 4.6] (frame
  `c ∘ ι`, rows `ℓ_{ι(d)} ∘ ι`).  Strong coding reflects along every surjective lower embedding
  (`CellScheme.Rows.isStronglyCoded_comap_iff`), so a cell renaming preserves and reflects it
  (`Scheme.IsCellRenaming.isStronglyCoded_iff`).
* **The reading.**  A reading of printed base symbols (`baseLanguage.SymbolReading`) assigns to
  each printed symbol a relation on the carrier.  The class reading (`SymbolReading.ofClasses`)
  reads a symbol as the disjunction of the positional symbols of its renaming class.
  `SymbolReading.PresentsStronglyCoded` is the interface used here: a printed symbol holds only of
  tuples carrying a positional symbol with strongly coded rows.  The class reading has it when
  every member of a class is a cell renaming of a scheme with strongly coded rows
  (`SymbolReading.presentsStronglyCoded_ofClasses_of_isCellRenaming`).

**The incompatibility** [printed correspondence].  Let `M` satisfy the density sentence and let
the printed symbols be read so as to present strongly coded templates.  Then there is no reading
`P` of `P_1` with both `∀ x, P x` (Singletons) and `∀ x, P x ↔ ⋁_s R_s(x)` (the first clause of
(b) at arity `1`) (`baseLanguage.not_singletons_and_typing_of_realize_densitySentence`); each of
the two may hold separately.  Only for the particular reading of `P_n` as "typed" does the first
clause of (b) fail by itself (`baseLanguage.not_typing_of_realize_densitySentence`).  The template presented at the offending
point fails clause (5) in every cell renaming
(`baseLanguage.exists_not_isStronglyCoded_isCellRenaming_of_realize_densitySentence`).

**What the sentence comparison still needs.**  To conclude that no model of the density sentence
is carried to a model of `σ[L]`, three facts are needed, none of them proved here, so that
conclusion remains open:
1. the sentence `σ[L]` over `L_c[L]` as a Lean sentence, and an interpretation reading `R_t` as
   the class disjunction (`SymbolReading.ofClasses`) and `P_n` by any formula;
2. satisfaction of `σ[L]` in the interpreted structure gives clause (Singletons) and the first
   clause of (b) at arity `1`, as the two hypotheses of
   `baseLanguage.not_singletons_and_typing_of_realize_densitySentence`;
3. every positional symbol in the class of a template of `L` is a cell renaming of a scheme with
   strongly coded rows.  This is the identification of clause (5) with strong coding for the
   chosen templates, combined with `Scheme.IsCellRenaming.isStronglyCoded_iff`.
-/

universe u v w

namespace VaughtConjecture

open Finset FirstOrder Language Structure Label StageType
open scoped Ordinal

/-! ### The range clause and its invariance -/

namespace CellScheme.Rows

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β} {φ : κ → ι}
  {R : D.Rows.{u}}

/-- **The range clause as a set inclusion** [native]: the row of a cell `s` is strongly coded
exactly when its range lies in `{⊥} ∪ {ω · n + i : n ∈ ℕ, i ≤ g(s) + 1}`, the set of clause (5)
of [AFK26, Definition 4.29]. -/
theorem isStronglyCodedAt_iff_range_subset (s : ι) :
    R.IsStronglyCodedAt s ↔ Set.range (R.row s) ⊆ insert ⊥
      {x | ∃ n i : ℕ, i ≤ D.grade s + 1 ∧ x = ((ω * n + i : Ordinal.{u}) : Label.{u})} := by
  rw [Set.range_subset_iff]
  exact Iff.rfl

/-- **Strong coding reflects along a surjective lower embedding** [native]: pulled-back rows are
strongly coded exactly when the rows are. -/
theorem isStronglyCoded_comap_iff (hφ : E.IsLowerEmbedding D φ) (hs : Function.Surjective φ) :
    (R.comap hφ).IsStronglyCoded ↔ R.IsStronglyCoded := by
  refine ⟨fun h s t ↦ ?_, fun h ↦ h.comap hφ⟩
  obtain ⟨s, rfl⟩ := hs s
  obtain ⟨t', -, ht'⟩ := exists_row_eq_of_isLowerEmbedding hφ rfl s t
  rw [ht', hφ.grade_eq s]
  exact h s t'

end CellScheme.Rows

namespace Scheme

variable {n : ℕ}

/-- A **cell renaming** of a scheme `S` to a scheme `T` on the same points along a bijection `e`
of cells [AFK26, Definition 4.6]: the same ground set and faces, the scope and grade of each cell
`i` of `T` those of `e i` in `S` (the frame `c ∘ ι`), and the rows of `T` those of `S` pulled back
along `e` (the rows `ℓ_{ι(d)} ∘ ι`).  Labels are not part of a scheme. -/
structure IsCellRenaming (S T : Scheme.{u} n) (e : Fin T.card ≃ Fin S.card) : Prop where
  /-- The same ground set. -/
  ground_eq : T.toCellScheme.ground = S.toCellScheme.ground
  /-- The same faces. -/
  faces_eq : T.toCellScheme.faces = S.toCellScheme.faces
  /-- Scopes and grades are carried along `e`. -/
  gradedIndex_eq (i : Fin T.card) :
    S.toCellScheme.gradedIndex (e i) = T.toCellScheme.gradedIndex i
  /-- The rows are pulled back along `e`. -/
  rows_eq : S.rows.comap (CellScheme.IsLowerEmbedding.of_equiv e gradedIndex_eq) = T.rows

/-- **Cell renaming preserves and reflects strong coding** [native]. -/
theorem IsCellRenaming.isStronglyCoded_iff {S T : Scheme.{u} n} {e : Fin T.card ≃ Fin S.card}
    (h : S.IsCellRenaming T e) : T.rows.IsStronglyCoded ↔ S.rows.IsStronglyCoded := by
  rw [← h.rows_eq]
  exact CellScheme.Rows.isStronglyCoded_comap_iff _ e.surjective

/-- Every scheme is a cell renaming of itself along the identity. -/
theorem isCellRenaming_refl (S : Scheme.{u} n) : S.IsCellRenaming S (Equiv.refl _) :=
  ⟨rfl, rfl, fun _ ↦ rfl, rfl⟩

/-! ### The scheme `pointRow 3` -/

/-- **`pointRow 3` is legal** [native]. -/
theorem isLegal_pointRow_three : (CodingExamples.pointRow (3 : Label.{u})).IsLegal :=
  CodingExamples.isLegal_pointRow (lt_omega0_sq_iff.mpr (.inr ⟨0, 3, by simp⟩)) (by simp)

/-- The only cell of `pointRow 3` has grade `1`, and its row takes the value `3` at the cell
itself. -/
theorem pointRow_three_row :
    (CodingExamples.pointRow (3 : Label.{u})).toCellScheme.grade (0 : Fin 1) = 1 ∧
      (CodingExamples.pointRow (3 : Label.{u})).rows.row (0 : Fin 1)
        ⟨(0 : Fin 1), CellScheme.mem_below_gradedIndex _ _⟩ = 3 :=
  ⟨rfl, rfl⟩

/-- **`pointRow 3` is not strongly coded** [native]: the value `3` at grade `1` has finite part
above `1 + 1`. -/
theorem not_isStronglyCoded_pointRow_three :
    ¬ (CodingExamples.pointRow (3 : Label.{u})).rows.IsStronglyCoded := fun h ↦ by
  simpa [CodingExamples.pointRow] using
    h (0 : Fin 1) ⟨(0 : Fin 1), CellScheme.mem_below_gradedIndex _ _⟩

/-- The label `3` violates the range clause at grade `1`. -/
theorem not_isStronglyCoded_one_three : ¬ Label.IsStronglyCoded 1 (3 : Label.{u}) :=
  fun h ↦ not_isStronglyCoded_pointRow_three fun _ _ ↦ h

end Scheme

/-! ### The cap and stage reduction keep the rows -/

namespace StageType

variable {α β : Ordinal.{u}} {n : ℕ}

/-- **The receiving cap keeps the rows** [native]: a member `q` of the receiving family of `d` at
any cutoff `c` has the scheme of `d`, rows included; the cutoff caps the labels only. -/
theorem isStronglyCoded_iff_of_mem_receivingFamily {d q : StageType.{u} α n} {c : Label.{u}}
    (hq : q ∈ receivingFamily d c) : q.rows.IsStronglyCoded ↔ d.rows.IsStronglyCoded := by
  rw [hq.1]

/-- **Stage reduction keeps the rows** [native]. -/
theorem isStronglyCoded_reduce_iff (t : StageType.{u} α n) (hβ : Order.IsSuccPrelimit β) :
    (t.reduce hβ).rows.IsStronglyCoded ↔ t.rows.IsStronglyCoded :=
  Iff.rfl

end StageType

/-! ### The occurrence -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **The empty root is typed** [native] on a nonempty carrier under exact consistency and
covering: the empty face of a typed tuple through a point is typed. -/
theorem exists_eval_zero (hne : Nonempty M) (hc : R.IsConsistent) (hcov : R.IsCovering) :
    ∃ (t : Fin 0 ↪ M) (p : StageType.{u} α 0), R.eval t = some p := by
  obtain ⟨a⟩ := hne
  obtain ⟨m, u, -, -, hu⟩ := hcov (⟨fun _ ↦ a, fun i j _ ↦ Subsingleton.elim i j⟩ : Fin 1 ↪ M)
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hu
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  exact ⟨_, p, (hc u P _ hP).trans hp⟩

/-- **Every legal one-point scheme gives a coface of the empty root** [native]: its bottom
labelling, whose face on no points is the unique stage type there. -/
theorem mem_cofaces_toStageType {S : Scheme.{u} 1} (hS : S.IsLegal) (p : StageType.{u} α 0) :
    hS.toStageType α ∈ p.cofaces := by
  obtain ⟨p', hp'⟩ :=
    Option.isSome_iff_exists.mp ((hS.toStageType α).isSome_restrictFace_of_zero Fin.castSuccEmb)
  exact ⟨hS.isLegal_toStageType α, hp'.trans (congrArg some (eq_of_zero p' p))⟩

/-- At stage `0` there is no permitted cutoff, so every realization has the finite-cut receiving
property there. -/
theorem hasFiniteCutReceiving_zero (R : Realization.{u, v} 0 M) : R.HasFiniteCutReceiving :=
  fun _ _ _ _ hc ↦ by
    obtain ⟨δ, hδ, -⟩ := isPermittedCutoff_iff.mp hc
    exact (not_lt_zero hδ).elim

/-- **Receiving realizes every legal one-point scheme** [native]: with the finite-cut receiving
property at a positive stage, on a nonempty carrier, under exact consistency and covering, some
one-point tuple has a type on the scheme; the request is over the empty root at the cutoff `0`,
which caps the labels only. -/
theorem exists_eval_toScheme_eq_of_hasFiniteCutReceiving (hne : Nonempty M)
    (hc : R.IsConsistent) (hcov : R.IsCovering) (hR : R.HasFiniteCutReceiving) (hα : 0 < α)
    {S : Scheme.{u} 1} (hS : S.IsLegal) :
    ∃ (u : Fin 1 ↪ M) (q : StageType.{u} α 1), R.eval u = some q ∧ q.toScheme = S := by
  obtain ⟨t, p, ht⟩ := exists_eval_zero hne hc hcov
  obtain ⟨u, -, q, hq, hu⟩ :=
    hR ⟨0, t, p, ht⟩ _ (mem_cofaces_toStageType hS p) 0 (isPermittedCutoff_zero.mpr hα)
  exact ⟨u, q, hu, hq.1⟩

/-- **A model realizes every legal one-point scheme** [native], at every stage, by generalized
saturation over the empty root. -/
theorem IsModel.exists_eval_toScheme_eq (hR : R.IsModel) {S : Scheme.{u} 1} (hS : S.IsLegal) :
    ∃ (u : Fin 1 ↪ M) (q : StageType.{u} α 1), R.eval u = some q ∧ q.toScheme = S := by
  obtain ⟨t, p, ht⟩ := exists_eval_zero hR.nonempty hR.isConsistent hR.isCovering
  obtain ⟨u, -, q, hq, hu⟩ :=
    hR.saturation ⟨0, t, p, ht⟩ S ⟨_, mem_cofaces_toStageType hS p, rfl⟩
  exact ⟨u, q, hu, hq⟩

/-- **A point whose type is not strongly coded lies in no strongly coded typed tuple** [native]:
under exact consistency the type of the point is a face of the type of every typed tuple through
it, and strong coding passes to faces. -/
theorem not_isStronglyCoded_of_mem_range (hc : R.IsConsistent) {u : Fin 1 ↪ M}
    {q : StageType.{u} α 1} (hu : R.eval u = some q) (hq : ¬ q.rows.IsStronglyCoded)
    (y : R.Occurrence) (hy : u 0 ∈ Set.range y.tuple) : ¬ y.type.rows.IsStronglyCoded := by
  obtain ⟨i, hi⟩ := hy
  let f : Fin 1 ↪ Fin y.arity := ⟨fun _ ↦ i, fun a b _ ↦ Subsingleton.elim a b⟩
  have hf : f.trans y.tuple = u := Function.Embedding.ext fun j ↦ by
    rw [Subsingleton.elim j 0]
    exact hi
  have h := hc y.tuple y.type f y.eval_tuple
  rw [hf, hu] at h
  exact fun hy ↦ hq (isStronglyCoded_of_restrictFace h.symm hy)

/-- The common conclusion of the occurrence theorems: a typed one-point tuple on `pointRow 3`
gives a point lying in typed tuples, none of them strongly coded. -/
private theorem exists_point_of_eval (hc : R.IsConsistent) {u : Fin 1 ↪ M}
    {q : StageType.{u} α 1} (hu : R.eval u = some q)
    (hq : q.toScheme = CodingExamples.pointRow 3) :
    ∃ u : Fin 1 ↪ M, (R.eval u).isSome ∧
      ∀ x : R.Occurrence, u 0 ∈ Set.range x.tuple → ¬ x.type.rows.IsStronglyCoded := by
  have hnq : ¬ q.rows.IsStronglyCoded := by
    rw [hq]
    exact Scheme.not_isStronglyCoded_pointRow_three
  exact ⟨u, by rw [hu]; rfl, not_isStronglyCoded_of_mem_range hc hu hnq⟩

/-- **A point in no strongly coded typed tuple, for receiving realizations** [native]: on a
nonempty carrier, under exact consistency and covering, with the finite-cut receiving property at
a positive stage, some typed one-point tuple `u` has the property that every typed tuple through
`u 0` has rows that are not strongly coded.  The type of `u` has the scheme of `pointRow 3`. -/
theorem exists_point_not_isStronglyCoded_of_hasFiniteCutReceiving (hne : Nonempty M)
    (hc : R.IsConsistent) (hcov : R.IsCovering) (hR : R.HasFiniteCutReceiving) (hα : 0 < α) :
    ∃ u : Fin 1 ↪ M, (R.eval u).isSome ∧
      ∀ x : R.Occurrence, u 0 ∈ Set.range x.tuple → ¬ x.type.rows.IsStronglyCoded :=
  let ⟨_, _, hu, hq⟩ := exists_eval_toScheme_eq_of_hasFiniteCutReceiving hne hc hcov hR hα
    Scheme.isLegal_pointRow_three
  exists_point_of_eval hc hu hq

/-- **A point in no strongly coded typed tuple, for models** [native], at every stage. -/
theorem IsModel.exists_point_not_isStronglyCoded (hR : R.IsModel) :
    ∃ u : Fin 1 ↪ M, (R.eval u).isSome ∧
      ∀ x : R.Occurrence, u 0 ∈ Set.range x.tuple → ¬ x.type.rows.IsStronglyCoded :=
  let ⟨_, _, hu, hq⟩ := hR.exists_eval_toScheme_eq Scheme.isLegal_pointRow_three
  exists_point_of_eval hR.isConsistent hu hq

/-- **An occurrence that is not strongly coded** [native], under the hypotheses of
`exists_point_not_isStronglyCoded_of_hasFiniteCutReceiving`. -/
theorem exists_occurrence_not_isStronglyCoded (hne : Nonempty M) (hc : R.IsConsistent)
    (hcov : R.IsCovering) (hR : R.HasFiniteCutReceiving) (hα : 0 < α) :
    ∃ x : R.Occurrence, ¬ x.type.rows.IsStronglyCoded := by
  obtain ⟨u, hu, h⟩ := exists_point_not_isStronglyCoded_of_hasFiniteCutReceiving hne hc hcov hR hα
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hu
  exact ⟨⟨1, u, q, hq⟩, h ⟨1, u, q, hq⟩ ⟨0, rfl⟩⟩

/-- **At every block stage** [native]: a receiving realization at `λ_ξ = ω + ω · ξ` has an
occurrence that is not strongly coded. -/
theorem exists_occurrence_not_isStronglyCoded_blockStage {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hne : Nonempty M) (hc : R.IsConsistent)
    (hcov : R.IsCovering) (hR : R.HasFiniteCutReceiving) :
    ∃ x : R.Occurrence, ¬ x.type.rows.IsStronglyCoded :=
  exists_occurrence_not_isStronglyCoded hne hc hcov hR
    (Ordinal.omega0_pos.trans_le (omega0_le_blockStage ξ))

end Realization

/-! ### Structures of the base language -/

namespace baseLanguage

variable {M : Type v} [baseLanguage.{u}.Structure M] {n : ℕ}

omit [baseLanguage.Structure M] in
/-- A one-point embedding is the vector of its value. -/
private theorem coe_eq_vecCons (u : Fin 1 ↪ M) : (⇑u : Fin 1 → M) = ![u 0] := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

/-- The structure form of the native conclusion. -/
private theorem exists_not_isStronglyCoded_of_isTypeAssignment (hT : IsTypeAssignment M)
    (h : ∃ u : Fin 1 ↪ M, ((toRealization M).eval u).isSome ∧ ∀ x : (toRealization M).Occurrence,
      u 0 ∈ Set.range x.tuple → ¬ x.type.rows.IsStronglyCoded) :
    ∃ a : M, (∃ p : baseLanguage.{u}.Relations 1, RelMap p ![a]) ∧
      ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
        a ∈ Set.range xs → ¬ (type p).rows.IsStronglyCoded := by
  obtain ⟨u, hu, hall⟩ := h
  refine ⟨u 0, ?_, fun n p xs hp ha ↦ hall (hT.occurrence p xs hp) ha⟩
  rw [← coe_eq_vecCons]
  exact (isSome_toRealization_eval_iff u).mp hu

/-- **A point in no strongly coded tuple, for the density sentence** [native]: in every
structure satisfying the density sentence some point `a` satisfies a unary relation, and no
relation with strongly coded rows holds of any tuple through `a`. -/
theorem exists_not_isStronglyCoded_of_realize_densitySentence (h : densitySentence.Realize M) :
    ∃ a : M, (∃ p : baseLanguage.{u}.Relations 1, RelMap p ![a]) ∧
      ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
        a ∈ Set.range xs → ¬ (type p).rows.IsStronglyCoded := by
  obtain ⟨hT, hne, hc, hcov, hR⟩ := (realize_densitySentence_iff M).mp h
  exact exists_not_isStronglyCoded_of_isTypeAssignment hT
    ((toRealization M).exists_point_not_isStronglyCoded_of_hasFiniteCutReceiving hne hc hcov hR
      Ordinal.omega0_pos)

/-- **A point in no strongly coded tuple, for the four-family sentence** [native], by
generalized saturation. -/
theorem exists_not_isStronglyCoded_of_realize_fourFamilySentence
    (h : fourFamilySentence.Realize M) :
    ∃ a : M, (∃ p : baseLanguage.{u}.Relations 1, RelMap p ![a]) ∧
      ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
        a ∈ Set.range xs → ¬ (type p).rows.IsStronglyCoded := by
  obtain ⟨hT, hM⟩ := (realize_fourFamilySentence_iff M).mp h
  exact exists_not_isStronglyCoded_of_isTypeAssignment hT hM.exists_point_not_isStronglyCoded

/-- **The template presented at the point fails the range clause in every cell renaming**
[native]: in a structure satisfying the density sentence, some point satisfies a unary relation
`p` such that no cell renaming of the scheme of `p` has strongly coded rows. -/
theorem exists_not_isStronglyCoded_isCellRenaming_of_realize_densitySentence
    (h : densitySentence.Realize M) :
    ∃ (a : M) (p : baseLanguage.{u}.Relations 1), RelMap p ![a] ∧
      ∀ (T : Scheme.{u} 1) (e : Fin T.card ≃ Fin (type p).card),
        (type p).toScheme.IsCellRenaming T e → ¬ T.rows.IsStronglyCoded := by
  obtain ⟨a, ⟨p, hp⟩, hall⟩ := exists_not_isStronglyCoded_of_realize_densitySentence h
  exact ⟨a, p, hp, fun T e he hT ↦ hall p _ hp ⟨0, rfl⟩ (he.isStronglyCoded_iff.mp hT)⟩

/-! ### Readings of the printed base symbols -/

variable (M) in
/-- A **reading of printed base symbols** [printed correspondence] in a structure of the base
language: a type `Sym n` of printed symbols of each arity, and the relation read for each. -/
structure SymbolReading where
  /-- The printed symbols of each arity. -/
  Sym : ℕ → Type w
  /-- The relation read for a printed symbol. -/
  holds ⦃n : ℕ⦄ : Sym n → (Fin n → M) → Prop

namespace SymbolReading

/-- The **class reading** [printed correspondence]: a printed symbol is read as the disjunction of
the positional symbols in its class (for a template `t`, the positional symbols in the renaming
class of `t`). -/
def ofClasses (Sym : ℕ → Type w)
    (cls : ∀ ⦃n : ℕ⦄, Sym n → Set (baseLanguage.{u}.Relations n)) : SymbolReading.{v, w} M where
  Sym := Sym
  holds _ s xs := ∃ p ∈ cls s, RelMap p xs

/-- A reading **presents strongly coded templates** [printed correspondence]: a printed symbol
holds only of tuples of which a positional symbol with strongly coded rows holds (clause (5) of
[AFK26, Definition 4.29]). -/
def PresentsStronglyCoded (I : SymbolReading.{v, w} M) : Prop :=
  ∀ ⦃n : ℕ⦄ (s : I.Sym n) (xs : Fin n → M), I.holds s xs →
    ∃ p : baseLanguage.{u}.Relations n, (type p).rows.IsStronglyCoded ∧ RelMap p xs

/-- **The class reading of strongly coded classes presents strongly coded templates.** -/
theorem presentsStronglyCoded_ofClasses {Sym : ℕ → Type w}
    {cls : ∀ ⦃n : ℕ⦄, Sym n → Set (baseLanguage.{u}.Relations n)}
    (h : ∀ ⦃n : ℕ⦄ (s : Sym n), ∀ p ∈ cls s, (type p).rows.IsStronglyCoded) :
    (ofClasses (M := M) Sym cls).PresentsStronglyCoded :=
  fun _ s _ ⟨p, hp, hpx⟩ ↦ ⟨p, h s p hp, hpx⟩

/-- **Renaming classes of strongly coded representatives** [printed correspondence]: if every
member of the class of `s` is a cell renaming of a scheme `rep s` with strongly coded rows, the
class reading presents strongly coded templates. -/
theorem presentsStronglyCoded_ofClasses_of_isCellRenaming {Sym : ℕ → Type w}
    {cls : ∀ ⦃n : ℕ⦄, Sym n → Set (baseLanguage.{u}.Relations n)}
    (rep : ∀ ⦃n : ℕ⦄, Sym n → Scheme.{u} n)
    (hrep : ∀ ⦃n : ℕ⦄ (s : Sym n), (rep s).rows.IsStronglyCoded)
    (hcls : ∀ ⦃n : ℕ⦄ (s : Sym n), ∀ p ∈ cls s,
      ∃ e : Fin (type p).card ≃ Fin (rep s).card, (rep s).IsCellRenaming (type p).toScheme e) :
    (ofClasses (M := M) Sym cls).PresentsStronglyCoded :=
  presentsStronglyCoded_ofClasses fun _ s p hp ↦
    let ⟨_, he⟩ := hcls s p hp
    he.isStronglyCoded_iff.mpr (hrep s)

end SymbolReading

/-! ### The incompatibility -/

/-- **The incompatibility against an explicit interface** [printed correspondence]: let `M`
satisfy the density sentence and let the printed symbols be read so as to present strongly coded
templates.  For every reading `P` of `P_1`, the clause (Singletons) `∀ x, P_1(x)` of
[AFK26, Definition 4.13] and the first clause of [AFK26, Definition 4.22 (b)] at arity `1`,
`∀ x, P_1(x) ↔ ⋁_s R_s(x)`, do not both hold. -/
theorem not_singletons_and_typing_of_realize_densitySentence (h : densitySentence.Realize M)
    (I : SymbolReading.{v, w} M) (hI : I.PresentsStronglyCoded) (P : M → Prop) :
    ¬ ((∀ x, P x) ∧ ∀ x, P x ↔ ∃ s : I.Sym 1, I.holds s ![x]) := by
  rintro ⟨hP, hb⟩
  obtain ⟨a, -, hall⟩ := exists_not_isStronglyCoded_of_realize_densitySentence h
  obtain ⟨s, hs⟩ := (hb a).mp (hP a)
  obtain ⟨q, hq, hqa⟩ := hI s _ hs
  exact hall q _ hqa ⟨0, rfl⟩ hq

/-- **The incompatibility with `P_n` read as "typed"** [printed correspondence]: under a reading
presenting strongly coded templates, the first clause of [AFK26, Definition 4.22 (b)],
`P_n(xs) ↔ ⋁_s R_s(xs)`, fails in every structure satisfying the density sentence. -/
theorem not_typing_of_realize_densitySentence (h : densitySentence.Realize M)
    (I : SymbolReading.{v, w} M) (hI : I.PresentsStronglyCoded) :
    ¬ ∀ ⦃n : ℕ⦄ (xs : Fin n → M),
      (∃ p : baseLanguage.{u}.Relations n, RelMap p xs) ↔ ∃ s : I.Sym n, I.holds s xs := by
  intro hb
  obtain ⟨a, hpa, hall⟩ := exists_not_isStronglyCoded_of_realize_densitySentence h
  obtain ⟨s, hs⟩ := (hb ![a]).mp hpa
  obtain ⟨q, hq, hqa⟩ := hI s _ hs
  exact hall q _ hqa ⟨0, rfl⟩ hq

end baseLanguage

end VaughtConjecture

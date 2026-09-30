/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CoatomScheme

/-!
# Coding transport under the range normalization

Roadmap, Library conventions (legality imposes coding as the range normalization only) and
Layer 3, 3.1, row 6 (the completion of the coatom amalgam by cells of full scope: its coding);
semantic contract, item 3.

The rows of a legal scheme are **coded** (`Scheme.IsCoded`): every row value lies below `ω ^ 2`,
that is, it is bottom or an ordinal `ω · i + j` (`Label.lt_omega0_sq_iff`).  The bound `j ≤ k + 1`
at a row of grade `k`, the offset bound of [Kni26, Lemma 2.5.13], is not correct as stated and is
not part of legality.  This file records the coding facts that the completion of the amalgam
needs, stated under the range normalization alone: the offset bound is asked of no input.

**Coding of labels.**

* `Label.IsStronglyCoded k x`: `x` is bottom or `ω · i + j` with `j ≤ k + 1`, the range of a row of
  grade `k` in [Kni26, Lemma 2.5.13]: coded, and in addition bounded in its finite part.  On
  ordinals, `IsStronglyCoded k o ↔ o < ω ^ 2 ∧ o % ω ≤ k + 1` (`Label.isStronglyCoded_coe`): strong
  coding bounds the finite part from above, where self-visibility (`Label.isSelfVisible_coe`) bounds
  it from below.  A label lies below `ω ^ 2` exactly when it is strongly coded at some grade
  (`Label.lt_omega0_sq_iff_exists_isStronglyCoded`), so the range normalization is strong coding
  with no bound on the offset in terms of the grade.
* The **coded alphabet** `Label.codedAlphabet i j`, the finite set of `⊥` and the ordinals
  `ω · a + b` with `a ≤ i` and `b ≤ j`.  The labels below `ω ^ 2` form an infinite set
  (`Label.infinite_setOf_lt_omega0_sq`), so a finite catalogue needs a finite alphabet; the
  labels strongly coded at `k` and below `ω · (i + 1)` lie in one
  (`Label.finite_setOf_isStronglyCoded_lt`).

**Coding of rows.**  For rows `R` of a cell scheme (`CellScheme.Rows.IsCoded`, of which
`Scheme.IsCoded` is the instance for the rows of a scheme, `Scheme.isCoded_iff`) and a lower
embedding `φ` of a cell scheme with rows `Q` whose rows pull back to `Q`, the cells outside the
range of `φ` being the new cells:

* (a) the amalgam of two coded schemes is coded: `Coatom.isCoded_amalgam`, in
  `VaughtConjecture.Extension.CoatomAmalgam`;
* (b) **appending cells** keeps coding: `R` is coded when `Q` is and every new row takes values
  below `ω ^ 2` (`CellScheme.Rows.isCoded_of_isLowerEmbedding`, and
  `Scheme.isCoded_of_isLowerEmbedding` for schemes), for instance values in a coded alphabet
  (`Label.lt_omega0_sq_of_mem_codedAlphabet`);
* (c) **a bottom row**: a new cell whose row is constantly bottom is strongly coded
  (`CellScheme.Rows.isStronglyCodedAt_of_forall_eq_bot`), so it keeps coding;
* (d) **strong coding of the new rows** is a sufficient condition for (b): a cell is strongly
  coded (`CellScheme.Rows.IsStronglyCodedAt`) when its row is strongly coded at its grade, and if
  every new cell is, then `R` is coded when `Q` is
  (`CellScheme.Rows.isCoded_of_isLowerEmbedding_of_isStronglyCodedAt`, and
  `Scheme.isCoded_of_isLowerEmbedding_of_isStronglyCodedAt`).  Strongly coded rows are coded
  (`CellScheme.Rows.IsStronglyCoded.isCoded`), and strong coding pulls back along lower
  embeddings (`CellScheme.Rows.IsStronglyCoded.comap`);
* (e) **finiteness**: over a finite type of cells, the labellings with values in finite sets of
  labels form a finite set, `Set.Finite.pi'`, and a catalogue is finite as a subset of such a set
  (`Set.Finite.subset`); lawfulness plays no role.  The finite sets of labels are given by
  `Label.finite_setOf_isStronglyCoded_lt`.

**Orderliness from consistency.**  Orderliness of rows is not a law of its own: consistent rows
are orderly (`CellScheme.Rows.IsConsistent.isOrderly`), and a labelling lawful below a pair is
orderly by the `orderly` clause of lawfulness (`CellScheme.Rows.isLawfulBelow_iff`).  Consistency
transports over appended cells (`CellScheme.Rows.isConsistent_of_isLowerEmbedding`): the
inherited cells keep their laws, and the new rows need theirs.  The orderliness of the extended
rows is then `(isConsistent_of_isLowerEmbedding …).isOrderly`, derived and not assumed.

**Universes.**  Every statement is universe polymorphic: labels are `Label.{u}`, rows
`CellScheme.Rows.{u}`, and schemes `Scheme.{u}`, for an arbitrary universe `u`.

## Verdict

The verdict concerns the construction chosen for the completion of the amalgam (roadmap, Layer 3,
3.1, row 6): it builds the completion grade by grade over the boundary, in one fixed order of its
cells, and tops out in a single apex cell.  The completion of [Kni26, Definition 4.3.14] is
background only.

*Proved here.*  The transport lemmas (b)–(d) ask of their inputs no coding beyond the range
normalization `Scheme.IsCoded`, and of the new rows only values below `ω ^ 2`; strong coding of
the new rows is sufficient, not required.  `VaughtConjecture.Extension.CodingExamples` exhibits
legal schemes with the row values `3` and `ω + 5` at a cell of grade `1`, so not strongly coded,
to which the transport lemmas apply.

*An analysis of the construction chosen, not a proved fact.*  Checkpoints 2.3–2.6 of the
completion (the roadmap's Layer 3, the coatom extension construction: transformation algebra,
lifting and alignment, the two small arities, the recursion on the
grade) are not yet formalized.  In the construction chosen, the coding of the inputs enters only
to conclude the coding of the output: the inherited rows are copied literally, so (b) applies
with the input's `IsCoded`; the amalgam of the two inputs is coded by (a); the apex row is the
coded copy of the labels (`VaughtConjecture.Extension.Apex`), below `ω ^ 2` by
`Label.bandEncode_lt`, so (b) applies; and every other new row takes its values in a coded
alphabet fixed by its grade (the values `ω · b + k`, normal forms, and their visibility
replacements at grades `≤ k`), so it is coded,
indeed strongly coded (d), by its construction and not by the coding of the inputs.  Consistency,
capped lifting, lawful sections, normalization, decoding, and the finiteness of the catalogue use
no coding of the inputs; the catalogue is finite because its vectors take values in a coded
alphabet (e).  One step of the construction uses the coding of an input row, and not its offset
bound: it needs the values of that row below `ω ^ 2`, which `IsCoded` gives.

## Placement

The label statements belong in `VaughtConjecture.Label.Basic`; `CellScheme.Rows.IsCoded`, its
strong form, and their transport in `VaughtConjecture.Scheme.Row`; and `Scheme.isCoded_iff` with
the transport for schemes in `VaughtConjecture.Stage.Scheme`.  They are stated here so that those
files are unchanged.

## References

The coding of rows is the range normalization of [Kni26, Lemma 2.5.13], whose offset bound is not
used; the amalgam is [Kni26, Definition 4.3.1]; consistency is [Kni26, Definition 2.5.12].
-/

universe u

open Ordinal

namespace VaughtConjecture

open Finset

namespace Label

variable {k : ℕ} {x : Label.{u}}

/-! ### Labels below `ω ^ 2` -/

/-- The labels below `ω ^ 2` are bottom and the ordinals `ω · i + j`: the range normalization of
[Kni26, Lemma 2.5.13], without its offset bound. -/
theorem lt_omega0_sq_iff :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) ↔
      x = ⊥ ∨ ∃ i j : ℕ, x = ((ω * i + j : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o =>
    simp only [WithBot.coe_lt_coe, WithTop.coe_lt_coe, WithBot.coe_ne_bot, false_or,
      WithBot.coe_inj, WithTop.coe_inj, pow_two, lt_mul_iff, lt_omega0]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩
      exact ⟨i, j, h⟩
    · rintro ⟨i, j, h⟩
      exact ⟨i, ⟨i, rfl⟩, j, ⟨j, rfl⟩, h⟩
  | top =>
    simp only [not_top_lt, false_iff, not_or]
    exact ⟨WithBot.coe_ne_bot, fun ⟨_, _, h⟩ ↦ WithTop.top_ne_coe (WithBot.coe_injective h)⟩

/-- The labels below `ω ^ 2` form an infinite set: they contain all natural numbers.  A finite
catalogue therefore needs a finite alphabet, not merely the range normalization. -/
theorem infinite_setOf_lt_omega0_sq :
    {x : Label.{u} | x < ((ω ^ 2 : Ordinal.{u}) : Label.{u})}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ ((n : Ordinal.{u}) : Label.{u}))
    (fun a b h ↦ ?_) fun n ↦ ?_
  · exact Nat.cast_injective (R := Ordinal.{u}) (WithTop.coe_injective (WithBot.coe_injective h))
  · refine lt_omega0_sq_iff.mpr (.inr ⟨0, n, ?_⟩)
    simp

/-! ### Strong coding -/

/-- A label is **strongly coded** at grade `k`: it is bottom or an ordinal `ω · i + j` with
`j ≤ k + 1`.  Equivalently (`Label.isStronglyCoded_coe`), it is coded, that is, below `ω ^ 2` (the
range normalization of [Kni26, Lemma 2.5.13], which legality imposes on rows), and in addition
its finite part satisfies the offset bound `j ≤ k + 1` displayed in that lemma.  The two are
distinct: coding bounds the label, strong coding also bounds its finite part in terms of the
grade.  Every coded label is strongly coded at some grade
(`Label.lt_omega0_sq_iff_exists_isStronglyCoded`), but `3` is coded and not strongly coded at
grade `1`.  Strong coding is not part of legality; a
construction that needs it imposes it on the rows it builds. -/
def IsStronglyCoded (k : ℕ) (x : Label.{u}) : Prop :=
  x = ⊥ ∨ ∃ i j : ℕ, j ≤ k + 1 ∧ x = ((ω * i + j : Ordinal.{u}) : Label.{u})

/-- Bottom is strongly coded at every grade. -/
@[simp] theorem isStronglyCoded_bot (k : ℕ) : IsStronglyCoded k (⊥ : Label.{u}) := .inl rfl

/-- The formal top is not strongly coded. -/
@[simp] theorem not_isStronglyCoded_top (k : ℕ) : ¬ IsStronglyCoded k (⊤ : Label.{u}) := by
  rintro (h | ⟨_, _, _, h⟩)
  · exact WithBot.coe_ne_bot h
  · exact WithTop.top_ne_coe (WithBot.coe_injective h)

/-- An ordinal is strongly coded at grade `k` exactly when it lies below `ω ^ 2` and its finite
part is at most `k + 1`.  Strong coding bounds the finite part from above, where self-visibility
at `k` bounds it from below (`Label.isSelfVisible_coe`: `k ≤ o % ω`). -/
@[simp] theorem isStronglyCoded_coe {o : Ordinal.{u}} :
    IsStronglyCoded k (o : Label.{u}) ↔ o < ω ^ 2 ∧ o % ω ≤ k + 1 := by
  simp only [IsStronglyCoded, WithBot.coe_ne_bot, false_or, WithBot.coe_inj, WithTop.coe_inj]
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    refine ⟨WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp
      (lt_omega0_sq_iff.mpr (.inr ⟨i, j, rfl⟩))), ?_⟩
    simp only [mul_add_mod_self, natCast_mod_omega0]
    exact_mod_cast hj
  · rintro ⟨ho, hj⟩
    obtain h | ⟨i, j, h⟩ := lt_omega0_sq_iff.mp (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ho))
    · exact absurd h WithBot.coe_ne_bot
    · have h : o = ω * i + j := WithTop.coe_injective (WithBot.coe_injective h)
      subst h
      simp only [mul_add_mod_self, natCast_mod_omega0] at hj
      exact ⟨i, j, by exact_mod_cast hj, rfl⟩

/-- `ω · i + j` is strongly coded at grade `k` exactly when `j ≤ k + 1`. -/
theorem isStronglyCoded_coe_omega0_mul_add (k i j : ℕ) :
    IsStronglyCoded k ((ω * i + j : Ordinal.{u}) : Label.{u}) ↔ j ≤ k + 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ .inr ⟨i, j, h, rfl⟩⟩
  have h := (isStronglyCoded_coe.mp h).2
  simp only [mul_add_mod_self, natCast_mod_omega0] at h
  exact_mod_cast h

/-- A natural number `n` is strongly coded at grade `k` exactly when `n ≤ k + 1`. -/
@[simp] theorem isStronglyCoded_natCast (k n : ℕ) :
    IsStronglyCoded k (n : Label.{u}) ↔ n ≤ k + 1 := by
  have h : (n : Label.{u}) = ((ω * (0 : ℕ) + n : Ordinal.{u}) : Label.{u}) := by
    simp only [Nat.cast_zero, mul_zero, zero_add]
    rfl
  rw [h, isStronglyCoded_coe_omega0_mul_add]

/-- A numeral `n` is strongly coded at grade `k` exactly when `n ≤ k + 1`. -/
@[simp] theorem isStronglyCoded_ofNat (k n : ℕ) [n.AtLeastTwo] :
    IsStronglyCoded k (ofNat(n) : Label.{u}) ↔ ofNat(n) ≤ k + 1 :=
  isStronglyCoded_natCast k n

/-- Ordinal zero is strongly coded at every grade. -/
@[simp] theorem isStronglyCoded_zero (k : ℕ) : IsStronglyCoded k (0 : Label.{u}) := by
  simpa using (isStronglyCoded_natCast k 0 : IsStronglyCoded k ((0 : ℕ) : Label.{u}) ↔ _)

/-- The ordinal `1` is strongly coded at every grade. -/
@[simp] theorem isStronglyCoded_one (k : ℕ) : IsStronglyCoded k (1 : Label.{u}) := by
  simpa using (isStronglyCoded_natCast k 1 : IsStronglyCoded k ((1 : ℕ) : Label.{u}) ↔ _)

/-- A strongly coded label lies below `ω ^ 2`. -/
theorem IsStronglyCoded.lt_omega0_sq (h : IsStronglyCoded k x) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases h with h | ⟨i, j, -, h⟩
  · exact lt_omega0_sq_iff.mpr (.inl h)
  · exact lt_omega0_sq_iff.mpr (.inr ⟨i, j, h⟩)

/-- A label lies below `ω ^ 2` exactly when it is strongly coded at some grade: the range
normalization is strong coding with no bound on the offset in terms of the grade. -/
theorem lt_omega0_sq_iff_exists_isStronglyCoded :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) ↔ ∃ k, IsStronglyCoded k x := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ h.lt_omega0_sq⟩
  rcases lt_omega0_sq_iff.mp h with h | ⟨i, j, h⟩
  · exact ⟨0, .inl h⟩
  · exact ⟨j, .inr ⟨i, j, by omega, h⟩⟩

/-! ### The coded alphabet -/

/-- The **coded alphabet** with block bound `i` and offset bound `j`: bottom together with the
ordinals `ω · a + b` for `a ≤ i` and `b ≤ j`.  It is a finite set of labels below `ω ^ 2`, in
which the codes of the strongly coded encoder lie (`Label.strongEncode_mem_codedAlphabet`). -/
noncomputable def codedAlphabet (i j : ℕ) : Finset Label.{u} :=
  insert ⊥ ((range (i + 1) ×ˢ range (j + 1)).image
    fun ab ↦ ((ω * ab.1 + ab.2 : Ordinal.{u}) : Label.{u}))

/-- Membership in the coded alphabet. -/
theorem mem_codedAlphabet {i j : ℕ} :
    x ∈ codedAlphabet i j ↔
      x = ⊥ ∨ ∃ a ≤ i, ∃ b ≤ j, x = ((ω * a + b : Ordinal.{u}) : Label.{u}) := by
  simp only [codedAlphabet, mem_insert, mem_image, mem_product, mem_range, Prod.exists,
    Nat.lt_succ_iff]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

/-- Every label of the coded alphabet lies below `ω ^ 2`: new rows with values in a coded
alphabet are coded, by (b). -/
theorem lt_omega0_sq_of_mem_codedAlphabet {i j : ℕ} (h : x ∈ codedAlphabet i j) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_codedAlphabet.mp h with h | ⟨a, -, b, -, h⟩
  · exact lt_omega0_sq_iff.mpr (.inl h)
  · exact lt_omega0_sq_iff.mpr (.inr ⟨a, b, h⟩)

/-- A label strongly coded at `k` and below `ω · (i + 1)` lies in the coded alphabet with block
bound `i` and offset bound `k + 1`. -/
theorem mem_codedAlphabet_of_isStronglyCoded_of_lt {i : ℕ} (h : IsStronglyCoded k x)
    (hlt : x < ((ω * (i + 1) : Ordinal.{u}) : Label.{u})) : x ∈ codedAlphabet i (k + 1) := by
  rcases h with h | ⟨a, b, hb, rfl⟩
  · exact mem_codedAlphabet.mpr (.inl h)
  · refine mem_codedAlphabet.mpr (.inr ⟨a, ?_, b, hb, rfl⟩)
    have hlt : (ω * a : Ordinal.{u}) < ω * (i + 1) :=
      le_self_add.trans_lt (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt))
    have ha : (a : Ordinal.{u}) < i + 1 := (mul_lt_mul_iff_right₀ omega0_pos).mp hlt
    exact Nat.lt_succ_iff.mp (by exact_mod_cast ha)

/-- **Finitely many strongly coded labels lie below `ω · (i + 1)`**: they lie in the coded
alphabet with block bound `i` and offset bound `k + 1`.  The labels below `ω · (i + 1)` alone
do not form a finite set.  So over finitely many cells, the labellings with strongly coded values
below `ω · (i + 1)` form a finite set, (e). -/
theorem finite_setOf_isStronglyCoded_lt (k i : ℕ) :
    {x : Label.{u} | IsStronglyCoded k x ∧ x < ((ω * (i + 1) : Ordinal.{u}) : Label.{u})}.Finite :=
  (codedAlphabet i (k + 1)).finite_toSet.subset fun _ hx ↦
    mem_codedAlphabet_of_isStronglyCoded_of_lt hx.1 hx.2

end Label

/-! ### Coded rows -/

namespace CellScheme.Rows

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β} {φ : κ → ι}

/-- Rows are **coded**: every row value lies below `ω ^ 2`, that is, is bottom or an ordinal
`ω · i + j` [Kni26, Lemma 2.5.13, range normalization]. -/
def IsCoded (R : D.Rows.{u}) : Prop :=
  ∀ s t, R.row s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u})

/-- The row of a cell `s` is **strongly coded**: its values are strongly coded at the grade of
`s` (finite part at most the grade plus one). -/
def IsStronglyCodedAt (R : D.Rows.{u}) (s : ι) : Prop :=
  ∀ t, Label.IsStronglyCoded (D.grade s) (R.row s t)

/-- Rows are **strongly coded**: the row of every cell is strongly coded at its grade. -/
def IsStronglyCoded (R : D.Rows.{u}) : Prop := ∀ s, R.IsStronglyCodedAt s

variable {R : D.Rows.{u}} {Q : E.Rows.{u}}

/-- The values of a strongly coded row lie below `ω ^ 2`. -/
theorem IsStronglyCodedAt.lt_omega0_sq {s : ι} (h : R.IsStronglyCodedAt s)
    (t : D.below (D.gradedIndex s)) : R.row s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  (h t).lt_omega0_sq

/-- Strongly coded rows are coded. -/
theorem IsStronglyCoded.isCoded (h : R.IsStronglyCoded) : R.IsCoded :=
  fun s t ↦ (h s).lt_omega0_sq t

/-- A row that is constantly bottom is strongly coded. -/
theorem isStronglyCodedAt_of_forall_eq_bot {s : ι} (h : ∀ t, R.row s t = ⊥) :
    R.IsStronglyCodedAt s :=
  fun t ↦ h t ▸ Label.isStronglyCoded_bot _

/-- Coded rows pull back to coded rows along a lower embedding. -/
theorem IsCoded.comap (h : R.IsCoded) (hφ : E.IsLowerEmbedding D φ) : (R.comap hφ).IsCoded :=
  fun _ _ ↦ h _ _

/-- Strongly coded rows pull back to strongly coded rows along a lower embedding, which preserves
grades. -/
theorem IsStronglyCoded.comap (h : R.IsStronglyCoded) (hφ : E.IsLowerEmbedding D φ) :
    (R.comap hφ).IsStronglyCoded :=
  fun s _ ↦ hφ.grade_eq s ▸ h (φ s) _

/-- The row of an inherited cell `φ s` is the row of `s`, when the rows pull back to `Q` along
the lower embedding `φ`: every cell `t` below `φ s` is the image `φ t'` of a cell `t'` below `s`,
and the row of `φ s` takes at `t` the value of the row of `s` at `t'`. -/
theorem exists_row_eq_of_isLowerEmbedding (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    (s : κ) (t : D.below (D.gradedIndex (φ s))) :
    ∃ t' : E.below (E.gradedIndex s), φ t' = t ∧ R.row (φ s) t = Q.row s t' := by
  obtain ⟨t', ht'⟩ := hφ.mem_range s t.1 t.2
  refine ⟨⟨t', (hφ.le_iff t' s).mp (ht' ▸ t.2)⟩, ht', ?_⟩
  subst hRQ
  exact R.row_congr rfl ht'.symm

/-- **Appending cells keeps coding.**  Let `φ` be a lower embedding along which the rows `R` pull
back to coded rows `Q`.  If the row of every cell outside the range of `φ` (every new cell) takes
values below `ω ^ 2`, then `R` is coded. -/
theorem isCoded_of_isLowerEmbedding (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    (hQ : Q.IsCoded)
    (hnew : ∀ s ∉ Set.range φ, ∀ t, R.row s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) :
    R.IsCoded := by
  intro s t
  by_cases hs : s ∈ Set.range φ
  · obtain ⟨s, rfl⟩ := hs
    obtain ⟨t', -, ht'⟩ := exists_row_eq_of_isLowerEmbedding hφ hRQ s t
    exact ht' ▸ hQ s t'
  · exact hnew s hs t

/-- **Appending strongly coded cells keeps coding**: if the rows `R` pull back to coded rows along
`φ` and every new cell is strongly coded, then `R` is coded.  Only the new rows are asked to be
strongly coded; the inherited rows need only be coded. -/
theorem isCoded_of_isLowerEmbedding_of_isStronglyCodedAt (hφ : E.IsLowerEmbedding D φ)
    (hRQ : R.comap hφ = Q) (hQ : Q.IsCoded) (hnew : ∀ s ∉ Set.range φ, R.IsStronglyCodedAt s) :
    R.IsCoded :=
  isCoded_of_isLowerEmbedding hφ hRQ hQ fun s hs ↦ (hnew s hs).lt_omega0_sq

/-! ### Consistency over appended cells -/

/-- **Appending cells keeps consistency**: if the rows `R` pull back to consistent rows along the
lower embedding `φ` and the row of every new cell is lawful below the graded index of its cell,
then `R` is consistent.  The extended rows are then orderly, by `IsConsistent.isOrderly`. -/
theorem isConsistent_of_isLowerEmbedding (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    (hQ : Q.IsConsistent)
    (hnew : ∀ s ∉ Set.range φ, R.IsLawfulBelow (D.gradedIndex s) (R.row s)) :
    R.IsConsistent := by
  intro s
  by_cases hs : s ∈ Set.range φ
  · obtain ⟨s, rfl⟩ := hs
    refine (isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    subst hRQ
    convert hQ s using 1
    funext t
    exact R.row_congr rfl rfl
  · exact hnew s hs

end CellScheme.Rows

/-! ### Coded schemes -/

namespace Scheme

variable {n m : ℕ}

/-- A scheme is coded exactly when its rows are. -/
theorem isCoded_iff {S : Scheme.{u} n} : S.IsCoded ↔ S.rows.IsCoded := Iff.rfl

/-- **Coding of a scheme with appended cells.**  Let `φ` be a lower embedding of the cells of a
coded scheme `S` into those of `T` along which the rows of `T` pull back to those of `S`.  If the
row of every cell of `T` outside the range of `φ` takes values below `ω ^ 2`, then `T` is coded;
no strong coding of `S` is assumed. -/
theorem isCoded_of_isLowerEmbedding {S : Scheme.{u} m} {T : Scheme.{u} n}
    {φ : Fin S.card → Fin T.card} (hφ : S.toCellScheme.IsLowerEmbedding T.toCellScheme φ)
    (hrows : T.rows.comap hφ = S.rows) (hS : S.IsCoded)
    (hnew : ∀ s ∉ Set.range φ, ∀ t, T.rows.row s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) :
    T.IsCoded :=
  CellScheme.Rows.isCoded_of_isLowerEmbedding hφ hrows hS hnew

/-- **Coding of a scheme with strongly coded appended cells**: as `isCoded_of_isLowerEmbedding`,
with every new cell strongly coded. -/
theorem isCoded_of_isLowerEmbedding_of_isStronglyCodedAt {S : Scheme.{u} m} {T : Scheme.{u} n}
    {φ : Fin S.card → Fin T.card} (hφ : S.toCellScheme.IsLowerEmbedding T.toCellScheme φ)
    (hrows : T.rows.comap hφ = S.rows) (hS : S.IsCoded)
    (hnew : ∀ s ∉ Set.range φ, T.rows.IsStronglyCodedAt s) : T.IsCoded :=
  isCoded_of_isLowerEmbedding hφ hrows hS fun s hs ↦ (hnew s hs).lt_omega0_sq

end Scheme

end VaughtConjecture

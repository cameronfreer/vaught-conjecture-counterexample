/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Finite.Lattice
import VaughtConjecture.Extension.CoatomScheme

/-!
# Coding transport under the range normalization

Roadmap, Library conventions (legality imposes coding as the range normalization only) and
Layer 3 (the coatom extension construction: the completion of the amalgam by cells of full
scope, its coding, and the finiteness of its catalogue); semantic contract, item 3.

The rows of a legal scheme are **coded** (`Scheme.IsCoded`): every row value lies below `ω ^ 2`,
that is, it is bottom or an ordinal `ω · i + j` (`Label.lt_omega0_sq_iff`).  The bound `j ≤ k + 1`
at a row of grade `k`, the offset bound of [Kni26, Lemma 2.5.13], is not correct as stated and is
not part of legality.  This file records the coding facts that the completion of the amalgam
([Kni26, Definition 4.3.14]) needs, stated under the range normalization alone, and shows that the
offset bound is needed of no input: it holds of the rows that the completion constructs, and is
imposed on them there.

**Coding of labels.**

* `Label.IsStronglyCoded k x`: `x` is bottom or `ω · i + j` with `j ≤ k + 1`, the range of a row
  of grade `k` in [Kni26, Lemma 2.5.13].  A strongly coded label lies below `ω ^ 2`
  (`Label.IsStronglyCoded.lt_omega0_sq`), and a label below `ω ^ 2` is strongly coded at some
  grade (`Label.lt_omega0_sq_iff_exists_isStronglyCoded`), so the range normalization is exactly
  strong coding with no bound on the offset in terms of the grade.  On the natural numbers,
  `IsStronglyCoded k n ↔ n ≤ k + 1` (`Label.isStronglyCoded_natCast`), and on `ω · i + j`,
  `IsStronglyCoded k (ω · i + j) ↔ j ≤ k + 1` (`Label.isStronglyCoded_coe_omega0_mul_add`).
* The **coded alphabet** `Label.codedAlphabet i j`, the finite set of `⊥` and the ordinals
  `ω · a + b` with `a ≤ i` and `b ≤ j`.  The labels below `ω ^ 2` form an infinite set
  (`Label.infinite_setOf_lt_omega0_sq`), so the finiteness of a catalogue needs a finite alphabet;
  the strongly coded labels below a given `ω · i + j` lie in one
  (`Label.finite_setOf_isStronglyCoded_le`).

**Coding of rows.**  For rows `R` of a cell scheme (`CellScheme.Rows.IsCoded`, of which
`Scheme.IsCoded` is the instance for the rows of a scheme, `Scheme.isCoded_iff`) and a lower
embedding `φ` of a cell scheme with rows `Q` whose rows pull back to `Q`, the cells outside the
range of `φ` being the new cells:

* (a) the amalgam of two coded schemes is coded: `Coatom.isCoded_amalgam`, in
  `VaughtConjecture.Extension.CoatomAmalgam`;
* (b) **appending cells** keeps coding: `R` is coded when `Q` is and every new row takes values
  below `ω ^ 2` (`CellScheme.Rows.isCoded_of_isLowerEmbedding`), in particular in a set of labels
  below `ω ^ 2`, such as a coded alphabet (`CellScheme.Rows.isCoded_of_isLowerEmbedding_of_mem`);
* (c) **the apex**: a new cell whose row is bottom is strongly coded
  (`CellScheme.Rows.isStronglyCodedAt_of_forall_eq_bot`), so it keeps coding;
* (e) **strong coding of the new rows**: a cell is strongly coded
  (`CellScheme.Rows.IsStronglyCodedAt`) when its row is strongly coded at its grade; if every new
  cell is, then `R` is coded when `Q` is
  (`CellScheme.Rows.isCoded_of_isLowerEmbedding_of_isStronglyCodedAt`, and
  `Scheme.isCoded_of_isLowerEmbedding` for schemes).  Strongly coded rows are coded
  (`CellScheme.Rows.IsStronglyCoded.isCoded`), and strong coding pulls back along lower
  embeddings (`CellScheme.Rows.IsStronglyCoded.comap`).
* (d) **finiteness of catalogues**: over a finite set of cells, the lawful labellings with values
  in a finite set of labels form a finite set (`CellScheme.Rows.finite_setOf_isLawful_forall_mem`,
  and below a pair `CellScheme.Rows.finite_setOf_isLawfulBelow_forall_mem`), and so do the
  labellings strongly coded at given grades and bounded by `ω · i + j`
  (`Label.finite_setOf_forall_isStronglyCoded_le`,
  `Scheme.finite_setOf_isLawful_isStronglyCoded_le`).

**Orderliness from consistency.**  Orderliness of rows is not a law of its own: consistent rows
are orderly (`CellScheme.Rows.IsConsistent.isOrderly`).  A labelling lawful below a pair takes
values self-visible at the grades of their cells (`CellScheme.Rows.IsLawfulBelow.isSelfVisible`),
so a new row that is lawful below the graded index of its cell is orderly.  Consistency and
orderliness transport over appended cells in the same way as coding
(`CellScheme.Rows.isConsistent_of_isLowerEmbedding`,
`CellScheme.Rows.isOrderly_of_isLowerEmbedding`): the inherited cells keep their laws, and the
new rows need theirs.

**Universes.**  Every statement is universe polymorphic: labels are `Label.{u}`, rows
`CellScheme.Rows.{u}`, and schemes `Scheme.{u}`, for an arbitrary universe `u`.

## Verdict

The completion needs no coding of its inputs beyond the range normalization `Scheme.IsCoded`,
and its output is coded with its new rows strongly coded.  In the completion of
[Kni26, Definition 4.3.14], coding of the inputs enters only to conclude coding of the output:
the inherited rows are copied literally (so their values are the values of the input rows, and
(b) applies with the input's `IsCoded`), the amalgam of the two inputs is coded by (a), the apex
row is bottom (c), and every other new row takes its values in a coded alphabet fixed by its
grade (grid values `ω · b + k`, normal forms, and their visibility replacements at grades `≤ k`),
so it is strongly coded (e) by its construction, not by the coding of the inputs.  Consistency,
capped lifting, lawful sections, normalization, decoding, and the finiteness of the catalogue
never use the coding of the inputs; the catalogue is finite because its vectors take values in a
coded alphabet (d).  `VaughtConjecture.Extension.CodingExamples` exhibits a legal scheme with a
row value `3` at a cell of grade `1`, so not strongly coded, to which the transport lemmas
apply.

## Placement

`Ordinal.lt_omega0_sq_iff`, `Ordinal.omega0_mul_add_natCast_lt`,
`Ordinal.omega0_mul_add_natCast_mod_omega0`, and `Ordinal.le_of_omega0_mul_add_natCast_le` belong
in `Mathlib.SetTheory.Ordinal.Arithmetic`, and are declared in the root `Ordinal` namespace;
the label statements in `VaughtConjecture.Label.Basic`; `CellScheme.Rows.IsCoded` with its
transport and `CellScheme.Rows.IsLawfulBelow.isSelfVisible` in `VaughtConjecture.Scheme.Row`; and
`Scheme.isCoded_iff` in `VaughtConjecture.Stage.Scheme`.  They are stated here so that those files
are unchanged.

## References

The coding of rows is the range normalization of [Kni26, Lemma 2.5.13], whose offset bound is not
used; the amalgam is [Kni26, Definition 4.3.1] and its completion [Kni26, Definition 4.3.14];
consistency is [Kni26, Definition 2.5.12].
-/

universe u

open Ordinal

/-! ### Ordinals below `ω ^ 2` -/

namespace Ordinal

/-- `ω · i + j < ω · (i + 1)` for natural numbers `i` and `j`. -/
theorem omega0_mul_add_natCast_lt (i j : ℕ) :
    ω * i + j < ω * ((i + 1 : ℕ) : Ordinal.{u}) :=
  calc ω * i + j < ω * i + ω := add_lt_add_right (natCast_lt_omega0 j) _
    _ = ω * ((i + 1 : ℕ) : Ordinal.{u}) := by push_cast; rw [mul_add_one]

/-- The finite part of `ω · i + j` is `j`. -/
theorem omega0_mul_add_natCast_mod_omega0 (i j : ℕ) :
    (ω * i + j : Ordinal.{u}) % ω = j := by
  rw [mul_add_mod_self, natCast_mod_omega0]

/-- The ordinals below `ω ^ 2` are the ordinals `ω · i + j` with `i` and `j` natural numbers. -/
theorem lt_omega0_sq_iff {o : Ordinal.{u}} : o < ω ^ 2 ↔ ∃ i j : ℕ, o = ω * i + j := by
  rw [pow_two]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := lt_omega0.mp ((lt_mul_iff_div_lt omega0_ne_zero).mp h)
    obtain ⟨j, hj⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
    exact ⟨i, j, by rw [← hi, ← hj, div_add_mod]⟩
  · rintro ⟨i, j, rfl⟩
    exact (omega0_mul_add_natCast_lt i j).trans_le
      (mul_le_mul_right (natCast_lt_omega0 _).le _)

/-- `ω · a + b ≤ ω · i + j` for natural numbers forces `a ≤ i`. -/
theorem le_of_omega0_mul_add_natCast_le {a b i j : ℕ}
    (h : (ω * a + b : Ordinal.{u}) ≤ ω * i + j) : a ≤ i := by
  by_contra hai
  have ha : ((i + 1 : ℕ) : Ordinal.{u}) ≤ a := by exact_mod_cast Nat.succ_le_of_lt (not_le.mp hai)
  exact (h.trans_lt (omega0_mul_add_natCast_lt i j)).not_ge
    ((mul_le_mul_right ha _).trans le_self_add)

end Ordinal

namespace VaughtConjecture

open Finset

namespace Label

variable {k k' : ℕ} {x : Label.{u}}

/-! ### Labels below `ω ^ 2` -/

/-- The labels below `ω ^ 2` are bottom and the ordinals `ω · i + j`: the range normalization of
[Kni26, Lemma 2.5.13], without its offset bound. -/
theorem lt_omega0_sq_iff :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) ↔
      x = ⊥ ∨ ∃ i j : ℕ, x = ((ω * i + j : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o =>
    simp only [WithBot.coe_lt_coe, WithTop.coe_lt_coe, Ordinal.lt_omega0_sq_iff,
      WithBot.coe_ne_bot, false_or, WithBot.coe_inj, WithTop.coe_inj]
  | top =>
    simp only [not_top_lt, false_iff, not_or]
    exact ⟨WithBot.coe_ne_bot, fun ⟨_, _, h⟩ ↦ WithTop.top_ne_coe (WithBot.coe_injective h)⟩

/-- Bottom lies below `ω ^ 2`. -/
theorem bot_lt_omega0_sq : (⊥ : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  WithBot.bot_lt_coe _

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
`j ≤ k + 1`.  This is the range of a row of grade `k` displayed in [Kni26, Lemma 2.5.13]; it is
not part of legality, and a construction that needs it imposes it on the rows it builds. -/
def IsStronglyCoded (k : ℕ) (x : Label.{u}) : Prop :=
  x = ⊥ ∨ ∃ i j : ℕ, j ≤ k + 1 ∧ x = ((ω * i + j : Ordinal.{u}) : Label.{u})

/-- Bottom is strongly coded at every grade. -/
@[simp] theorem isStronglyCoded_bot (k : ℕ) : IsStronglyCoded k (⊥ : Label.{u}) := .inl rfl

/-- The formal top is not strongly coded. -/
@[simp] theorem not_isStronglyCoded_top (k : ℕ) : ¬ IsStronglyCoded k (⊤ : Label.{u}) := by
  rintro (h | ⟨_, _, _, h⟩)
  · exact WithBot.coe_ne_bot h
  · exact WithTop.top_ne_coe (WithBot.coe_injective h)

/-- `ω · i + j` is strongly coded at grade `k` exactly when `j ≤ k + 1`. -/
theorem isStronglyCoded_coe_omega0_mul_add (k i j : ℕ) :
    IsStronglyCoded k ((ω * i + j : Ordinal.{u}) : Label.{u}) ↔ j ≤ k + 1 := by
  refine ⟨?_, fun h ↦ .inr ⟨i, j, h, rfl⟩⟩
  rintro (h | ⟨a, b, hb, h⟩)
  · exact absurd h WithBot.coe_ne_bot
  · have h' : (ω * i + j : Ordinal.{u}) = ω * a + b :=
      WithTop.coe_injective (WithBot.coe_injective h)
    have hmod := congrArg (· % ω) h'
    simp only [Ordinal.omega0_mul_add_natCast_mod_omega0, Nat.cast_inj] at hmod
    exact hmod ▸ hb

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

/-- Strong coding is monotone in the grade. -/
theorem IsStronglyCoded.mono (h : IsStronglyCoded k x) (hk : k ≤ k') : IsStronglyCoded k' x := by
  rcases h with h | ⟨i, j, hj, h⟩
  · exact .inl h
  · exact .inr ⟨i, j, by omega, h⟩

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
ordinals `ω · a + b` for `a ≤ i` and `b ≤ j`.  It is a finite set of labels below `ω ^ 2`. -/
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

/-- Every label of the coded alphabet lies below `ω ^ 2`. -/
theorem lt_omega0_sq_of_mem_codedAlphabet {i j : ℕ} (h : x ∈ codedAlphabet i j) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_codedAlphabet.mp h with h | ⟨a, -, b, -, h⟩
  · exact lt_omega0_sq_iff.mpr (.inl h)
  · exact lt_omega0_sq_iff.mpr (.inr ⟨a, b, h⟩)

/-- Every label of the coded alphabet with offset bound `j ≤ k + 1` is strongly coded at `k`. -/
theorem isStronglyCoded_of_mem_codedAlphabet {i j : ℕ} (h : x ∈ codedAlphabet i j)
    (hj : j ≤ k + 1) : IsStronglyCoded k x := by
  rcases mem_codedAlphabet.mp h with h | ⟨a, -, b, hb, h⟩
  · exact .inl h
  · exact .inr ⟨a, b, hb.trans hj, h⟩

/-- A label strongly coded at `k` and at most `ω · i + j` lies in the coded alphabet with block
bound `i` and offset bound `k + 1`. -/
theorem mem_codedAlphabet_of_isStronglyCoded_of_le {i j : ℕ} (h : IsStronglyCoded k x)
    (hle : x ≤ ((ω * i + j : Ordinal.{u}) : Label.{u})) : x ∈ codedAlphabet i (k + 1) := by
  rcases h with h | ⟨a, b, hb, rfl⟩
  · exact mem_codedAlphabet.mpr (.inl h)
  · refine mem_codedAlphabet.mpr (.inr ⟨a, ?_, b, hb, rfl⟩)
    exact Ordinal.le_of_omega0_mul_add_natCast_le
      (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hle))

/-- **Finitely many strongly coded labels lie below a given `ω · i + j`**: the labels strongly
coded at `k` and at most `ω · i + j` form a finite set.  The labels at most `ω · i + j` alone do
not, for `i ≥ 1`. -/
theorem finite_setOf_isStronglyCoded_le (k i j : ℕ) :
    {x : Label.{u} | IsStronglyCoded k x ∧ x ≤ ((ω * i + j : Ordinal.{u}) : Label.{u})}.Finite :=
  (codedAlphabet i (k + 1)).finite_toSet.subset fun _ hx ↦
    mem_codedAlphabet_of_isStronglyCoded_of_le hx.1 hx.2

/-! ### Finitely many labellings -/

section Labellings

variable {ι : Type*} [Finite ι]

/-- Over a finite set of cells, the labellings taking at each cell `d` a value in a finite set
`V d` form a finite set. -/
theorem finite_setOf_forall_mem {V : ι → Set Label.{u}} (hV : ∀ d, (V d).Finite) :
    {p : ι → Label.{u} | ∀ d, p d ∈ V d}.Finite := by
  convert Set.Finite.pi hV using 1
  ext p
  simp [Set.mem_pi]

/-- Over a finite set of cells, the labellings with values in the coded alphabet form a finite
set. -/
theorem finite_setOf_forall_mem_codedAlphabet (i j : ℕ) :
    {p : ι → Label.{u} | ∀ d, p d ∈ codedAlphabet i j}.Finite :=
  finite_setOf_forall_mem fun _ ↦ (codedAlphabet i j).finite_toSet

/-- Over a finite set of cells, the labellings strongly coded at the grades `k d` of their cells
and bounded by `ω · i + j` form a finite set. -/
theorem finite_setOf_forall_isStronglyCoded_le (k : ι → ℕ) (i j : ℕ) :
    {p : ι → Label.{u} | ∀ d, IsStronglyCoded (k d) (p d) ∧
      p d ≤ ((ω * i + j : Ordinal.{u}) : Label.{u})}.Finite :=
  finite_setOf_forall_mem (V := fun d ↦ {x | IsStronglyCoded (k d) x ∧
    x ≤ ((ω * i + j : Ordinal.{u}) : Label.{u})}) fun _ ↦ finite_setOf_isStronglyCoded_le _ _ _

end Labellings

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

/-- A row that is constantly bottom (an apex row) is strongly coded. -/
theorem isStronglyCodedAt_of_forall_eq_bot {s : ι} (h : ∀ t, R.row s t = ⊥) :
    R.IsStronglyCodedAt s :=
  fun t ↦ h t ▸ Label.isStronglyCoded_bot _

/-- Mute rows are strongly coded. -/
theorem isStronglyCoded_mute : (mute D : D.Rows.{u}).IsStronglyCoded :=
  fun _ ↦ isStronglyCodedAt_of_forall_eq_bot fun _ ↦ rfl

/-- Coded rows pull back to coded rows along a lower embedding. -/
theorem IsCoded.comap (h : R.IsCoded) (hφ : E.IsLowerEmbedding D φ) : (R.comap hφ).IsCoded :=
  fun _ _ ↦ h _ _

/-- Strongly coded rows pull back to strongly coded rows along a lower embedding, which preserves
grades. -/
theorem IsStronglyCoded.comap (h : R.IsStronglyCoded) (hφ : E.IsLowerEmbedding D φ) :
    (R.comap hφ).IsStronglyCoded :=
  fun s _ ↦ hφ.grade_eq s ▸ h (φ s) _

/-- The values of the row of an inherited cell `φ s` are values of the row of `s`, when the rows
pull back to `Q` along the lower embedding `φ`. -/
theorem exists_row_eq_of_isLowerEmbedding (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    (s : κ) (t : D.below (D.gradedIndex (φ s))) :
    ∃ t' : E.below (E.gradedIndex s), R.row (φ s) t = Q.row s t' := by
  obtain ⟨t', ht'⟩ := hφ.mem_range s t.1 t.2
  refine ⟨⟨t', (hφ.le_iff t' s).mp (ht' ▸ t.2)⟩, ?_⟩
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
    obtain ⟨t', ht'⟩ := exists_row_eq_of_isLowerEmbedding hφ hRQ s t
    exact ht' ▸ hQ s t'
  · exact hnew s hs t

/-- **Appending cells with rows in a set of coded labels keeps coding**: as
`isCoded_of_isLowerEmbedding`, with the new rows taking values in a set `V` of labels below
`ω ^ 2`, such as a coded alphabet. -/
theorem isCoded_of_isLowerEmbedding_of_mem (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    (hQ : Q.IsCoded) {V : Set Label.{u}}
    (hV : ∀ x ∈ V, x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}))
    (hnew : ∀ s ∉ Set.range φ, ∀ t, R.row s t ∈ V) : R.IsCoded :=
  isCoded_of_isLowerEmbedding hφ hRQ hQ fun s hs t ↦ hV _ (hnew s hs t)

/-- **Appending strongly coded cells keeps coding**: if the rows `R` pull back to coded rows along
`φ` and every new cell is strongly coded, then `R` is coded.  Only the new rows are asked to be
strongly coded; the inherited rows need only be coded. -/
theorem isCoded_of_isLowerEmbedding_of_isStronglyCodedAt (hφ : E.IsLowerEmbedding D φ)
    (hRQ : R.comap hφ = Q) (hQ : Q.IsCoded) (hnew : ∀ s ∉ Set.range φ, R.IsStronglyCodedAt s) :
    R.IsCoded :=
  isCoded_of_isLowerEmbedding hφ hRQ hQ fun s hs ↦ (hnew s hs).lt_omega0_sq

/-- **Appending apex cells keeps coding**: if the rows `R` pull back to coded rows along `φ` and
the row of every new cell is bottom, then `R` is coded. -/
theorem isCoded_of_isLowerEmbedding_of_eq_bot (hφ : E.IsLowerEmbedding D φ)
    (hRQ : R.comap hφ = Q) (hQ : Q.IsCoded) (hnew : ∀ s ∉ Set.range φ, ∀ t, R.row s t = ⊥) :
    R.IsCoded :=
  isCoded_of_isLowerEmbedding_of_isStronglyCodedAt hφ hRQ hQ fun s hs ↦
    isStronglyCodedAt_of_forall_eq_bot (hnew s hs)

/-! ### Orderliness and consistency over appended cells -/

/-- **Orderliness of a lawful labelling**: a labelling lawful below a pair takes values
self-visible at the grades of their cells. -/
theorem IsLawfulBelow.isSelfVisible {X : Finset α × ℕ} {r : D.below X → Label.{u}}
    (h : R.IsLawfulBelow X r) (t : D.below X) : Label.IsSelfVisible (D.grade t) (r t) :=
  (isLawfulBelow_iff.mp h).orderly t

/-- A row lawful below the graded index of its cell is orderly: its values are self-visible at
the grades of their cells. -/
theorem isSelfVisible_row_of_isLawfulBelow {s : ι} (h : R.IsLawfulBelow (D.gradedIndex s) (R.row s))
    (t : D.below (D.gradedIndex s)) : Label.IsSelfVisible (D.grade t) (R.row s t) :=
  h.isSelfVisible t

/-- **Appending cells keeps consistency**: if the rows `R` pull back to consistent rows along the
lower embedding `φ` and the row of every new cell is lawful below the graded index of its cell,
then `R` is consistent. -/
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

/-- **Appending cells keeps orderliness**: if the rows `R` pull back to orderly rows along the
lower embedding `φ` and the row of every new cell is orderly, then `R` is orderly.  By
`isSelfVisible_row_of_isLawfulBelow`, a new row lawful below the graded index of its cell is
orderly. -/
theorem isOrderly_of_isLowerEmbedding (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    (hQ : Q.IsOrderly)
    (hnew : ∀ s ∉ Set.range φ, ∀ t : D.below (D.gradedIndex s),
      Label.IsSelfVisible (D.grade t) (R.row s t)) :
    R.IsOrderly := by
  intro s t
  by_cases hs : s ∈ Set.range φ
  · obtain ⟨s, rfl⟩ := hs
    obtain ⟨t', ht'⟩ := hφ.mem_range s t.1 t.2
    have ht : Q.row s ⟨t', (hφ.le_iff t' s).mp (ht' ▸ t.2)⟩ = R.row (φ s) t := by
      subst hRQ
      exact R.row_congr rfl ht'
    have hg : D.grade t = E.grade t' := by rw [← ht', hφ.grade_eq]
    rw [← ht, hg]
    exact hQ s _
  · exact hnew s hs t

/-! ### Finitely many lawful labellings -/

/-- **Finiteness of a catalogue**: over a finite set of cells, the lawful labellings with values
in a finite set of labels form a finite set. -/
theorem finite_setOf_isLawful_forall_mem [Finite ι] (R : D.Rows.{u}) {V : Set Label.{u}}
    (hV : V.Finite) : {p : ι → Label.{u} | R.IsLawful p ∧ ∀ d, p d ∈ V}.Finite :=
  (Label.finite_setOf_forall_mem fun _ ↦ hV).subset fun _ hp ↦ hp.2

/-- Over a finite set of cells, the labellings lawful below a pair with values in a finite set
of labels form a finite set. -/
theorem finite_setOf_isLawfulBelow_forall_mem [Finite ι] (R : D.Rows.{u}) (X : Finset α × ℕ)
    {V : Set Label.{u}} (hV : V.Finite) :
    {r : D.below X → Label.{u} | R.IsLawfulBelow X r ∧ ∀ d, r d ∈ V}.Finite :=
  (Label.finite_setOf_forall_mem fun _ ↦ hV).subset fun _ hr ↦ hr.2

end CellScheme.Rows

/-! ### Coded schemes -/

namespace Scheme

variable {n m : ℕ}

/-- A scheme is coded exactly when its rows are. -/
theorem isCoded_iff {S : Scheme.{u} n} : S.IsCoded ↔ S.rows.IsCoded := Iff.rfl

/-- The rows of a scheme are **strongly coded**: the row of every cell is strongly coded at the
grade of the cell. -/
def IsStronglyCoded (S : Scheme.{u} n) : Prop := S.rows.IsStronglyCoded

/-- A strongly coded scheme is coded. -/
theorem IsStronglyCoded.isCoded {S : Scheme.{u} n} (h : S.IsStronglyCoded) : S.IsCoded :=
  CellScheme.Rows.IsStronglyCoded.isCoded h

/-- **Coding of a scheme with appended cells.**  Let `φ` be a lower embedding of the cells of a
coded scheme `S` into those of `T` along which the rows of `T` pull back to those of `S`.  If the
row of every cell of `T` outside the range of `φ` is strongly coded, then `T` is coded; no strong
coding of `S` is assumed. -/
theorem isCoded_of_isLowerEmbedding {S : Scheme.{u} m} {T : Scheme.{u} n}
    {φ : Fin S.card → Fin T.card} (hφ : S.toCellScheme.IsLowerEmbedding T.toCellScheme φ)
    (hrows : T.rows.comap hφ = S.rows) (hS : S.IsCoded)
    (hnew : ∀ s ∉ Set.range φ, T.rows.IsStronglyCodedAt s) : T.IsCoded :=
  CellScheme.Rows.isCoded_of_isLowerEmbedding_of_isStronglyCodedAt hφ hrows hS hnew

/-- **Finiteness of a catalogue on a scheme**: the lawful labellings of a scheme whose labels are
strongly coded at the grades of their cells and bounded by `ω · i + j` form a finite set. -/
theorem finite_setOf_isLawful_isStronglyCoded_le (S : Scheme.{u} n) (i j : ℕ) :
    {p : Fin S.card → Label.{u} | S.rows.IsLawful p ∧ ∀ d,
      Label.IsStronglyCoded (S.toCellScheme.grade d) (p d) ∧
        p d ≤ ((ω * i + j : Ordinal.{u}) : Label.{u})}.Finite :=
  (Label.finite_setOf_forall_isStronglyCoded_le _ i j).subset fun _ hp ↦ hp.2

end Scheme

end VaughtConjecture

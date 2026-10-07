/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Extension.GatedExtensionCounterexample
import VaughtConjecture.Label.StepWitness

/-!
# The capped reading of a donor through the reference cells of a private context

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the reading of the donor through the
private context) and 3.3 (the recovery statements); the private context of
`VaughtConjecture.Realization.PrivateContext`.  This file proves the **capped-donor lemma**, for a
private context and a donor given as data: no scheme over them, no display, and no completion
hypothesis.

**The data** (`CappedDonorReading.PrivateReference`, with its laws
`PrivateReference.HasMargin`).  Rows `R` of a cell scheme of private cells with actual labels `w`;
a **private cap** `C` of grade `N` (the full grade) below which every cell lies; a finite set of
requested **blocks**, by their indices `b` (the block of index `b` is `[ω * b, ω * b + ω)`); and
for each block a **reference cell** `ref b` labelled `ω * b + off b` with `off b < N`.  The
**margin** asks the cap to be labelled at least every `ω * b + N` (the private context of
[Kni26, Lemma 8.1.1], with the cap above the reference cells by the full grade).

* **The cut** of a labelling `v` of the private cells (`PrivateReference.cut`) is
  `min (v C) (max_b vr_N(N, v (ref b)))`, `vr_N` being visibility replacement at the threshold
  `N`.  At the actual labels, with the margin, it is `max_b (ω * b + N)`
  (`PrivateReference.HasMargin.cut_eq`).
* `v` is **active** (`PrivateReference.IsActive`) when it is not `⊥` at the cap nor at any
  reference cell.
* **The capped reading** (`PrivateReference.reading v`) sends `⊥` to `⊥`, a point `ω * b + n` to
  `min (vr_N(n, v (ref b))) (cut v)`, and `⊤` to `cut v`.  A donor labelling `ℓ` **reads in the
  blocks** (`PrivateReference.ReadsInBlocks`) when each of its ordinal labels lies in a requested
  block with finite part at most `N`.

**The capped-donor lemma** (`PrivateReference.HasMargin.isLawful_reading`).  With the margin, for
every active lawful labelling `v` of the private cells and every lawful donor labelling `ℓ`, for
any rows on donor cells of grade at most `N`, that reads in the blocks, the capped reading
`reading v ∘ ℓ` is lawful for the donor's rows.  The proof uses of activity only the reference
cells (`PrivateReference.HasMargin.isLawful_reading_of_ne_bot`): at a cap `⊥` the cut is `⊥` and
the reading is constantly `⊥`.

* *The codes* (`PrivateReference.HasMargin.exists_code`).  The capped witness of the actual labels
  at the cap (`Label.TransformsTo.exists_isWitness_capped`) reads the entry of the row of the cap
  at `ref b` as `ω * b + off b`.  So that entry is a point `ω * r b + j b` with `j b < N` (a
  self-visible entry would make `ω * b + off b` self-visible at `N`), and the code blocks `r b` are
  strictly increasing in `b` (two reference cells read in one code block would be read in one
  block).
* *The block pieces* (`CappedDonorReading.piece`, `CappedDonorReading.isWitness_piece`).  The piece
  from the block `b` to the block `r` is `⊥` below `ω * b`, sends `o ≥ ω * b` to
  `ω * r + min (o - ω * b) N`, and fixes `⊤`; it is a witness bounded by grade `N` (a witness
  whose suppressor is `⊤` at the grades `≤ N` and `⊥` above).  The supremum of the pieces of the
  requested blocks (`Label.IsWitness.finsetSup`) moves each requested block onto the code block of
  its reference cell, since the code blocks increase.
* *The reading as a witness.*  With `τ` the capped witness of `v` at the cap, the composite of the
  pieces and `τ` agrees, at the labels whose finite parts are at most `N`, with a witness bounded
  by grade `N` (`Label.IsWitness.exists_eq_comp_of_isShort`), and capping it by the cut keeps it
  one (`Label.IsWitness.min_const_of_isSelfVisible`).  This witness `ν` gives the reading:
  `reading v ∘ ℓ = ν ∘ ℓ`.
* *The criterion for maps that need not reflect `⊥`.*  `ν` sends to `⊥` every label below the
  lowest requested block, so `CellScheme.Rows.IsLawful.map_of_bot_reflecting` does not apply, and
  the donor's rows need not be short, so the short branch of
  `CellScheme.Rows.IsLawful.map_of_isShort_or` does not either.  The criterion used is
  `CellScheme.Rows.IsLawful.map_of_apply_eq_bot` (`VaughtConjecture.Extension.CapTransport`): `ν`
  sends no label of `ℓ` other than `⊥` to `⊥`, by activity of the reference cells and since the
  cut is not `⊥`.  No coding of rows
  (`VaughtConjecture.Extension.Coding`, `VaughtConjecture.Extension.OrbitCode`) is used: the codes
  are the entries of the row of the cap itself.

**The reading at the actual labels** (`PrivateReference.HasMargin.reading_eq_min`,
`PrivateReference.HasMargin.reading_eq_self`): it is the donor label capped by the cut, so it
recovers every donor label other than `⊤` and reads `⊤` as the cut.  This is where the margin
enters; the capped-donor lemma uses of it only that every reference label lies below the cap.

**Three inputs.**

* *A proper anchor* (`CappedDonorReading.AnchorInput`).  A **proper anchor** is a private cell
  labelled by an ordinal that is not self-visible at the full grade, through which a donor label
  below the cap is read by visibility replacement.  The two-point private type with the dead cells
  `{0}`, `{1}`, the cells `z₁`, `z₂` of graded index `(univ, 1)` labelled `1` and `⊤`, and the cap
  of graded index `(univ, 2)` labelled `⊤`, has the proper anchor `z₁` (`1` is not self-visible at
  `2`).  Its one-point donor `1, ⊤` has rows reading both donor cells in the block `[0, ω)`, so no
  lawful donor labelling is `⊥` at the first donor cell and not at the second
  (`AnchorInput.eq_bot_of_isLawful_donor`); the private type has the lawful labelling
  `⊥, ⊥, ⊥, ω + 1, ω + 2`, which keeps the cap and drops `z₁`
  (`AnchorInput.isLawful_lab_bot_omegaAdd`).  A design that transports the bottom pattern of every
  lawful private labelling at the anchors to the donor fails at this input (argued, not compiled
  here).  Here the margin holds with the
  block `[0, ω)` and the reference cell `z₁` (`AnchorInput.hasMargin`), so every active lawful
  labelling reads the donor lawfully (`AnchorInput.isLawful_reading`); the actual labels read
  `1, 2` (`AnchorInput.reading_lab_one_top_top`); the labelling that drops `z₁` is lawful, keeps
  the cap, and is inactive (`AnchorInput.not_isActive_lab_bot_omegaAdd`), so no reading is
  prescribed for it; and no labelling of the private cells, active or not, produces the forbidden
  pattern (`AnchorInput.reading_eq_bot_of_reading_eq_bot`).  With one block, a labelling `⊥` at
  `z₁` has the cut `⊥`.
* *Opposite full cells* (`CappedDonorReading.OppositeCellsInput`), at
  `GatedExtensionCounterexample.P α`, whose two full cells are ordered oppositely by the lawful
  labellings `⊤, 2` and `2, ⊤`.  Both are active (`OppositeCellsInput.isActive_labelling`), and
  for both the capped reading of every lawful donor labelled `⊥` and `⊤` is lawful
  (`OppositeCellsInput.isLawful_reading`).  This holds vacuously: no cell of `P α` carries an
  ordinal label, so there is no reference cell and no requested block, the cut is `⊥`
  (`OppositeCellsInput.cut_eq_bot`), and both readings are constantly `⊥`.
* *Two blocks* (`CappedDonorReading.TwoBlockInput`).  A private type with three cells, reference
  cells labelled `1` and `ω + 1` (blocks `[0, ω)` and `[ω, ω * 2)`) and a cap of grade `2` labelled
  `⊤`, with the one-point donor `1, ω + 1` whose second row reads both donor cells in their two
  blocks.  The margin holds (`TwoBlockInput.hasMargin`), so every active lawful labelling reads the
  donor lawfully (`TwoBlockInput.isLawful_reading`); the actual labels read the donor itself
  (`TwoBlockInput.reading_actual`); and the active lawful labelling `1, ω + 1, 2`, whose cut is `2`,
  reads it as `1, 2`, a lawful donor labelling not `⊥` anywhere and other than the donor's labels
  (`TwoBlockInput.reading_lab_one_omegaAdd_two`, `TwoBlockInput.isLawful_donorLab_one_two`).

**What is not claimed.**  The lemma is stated for given reference data with the margin.  Its
acquisition from modelhood is prospective: `Realization.IsModel.exists_privateContext` gives
reference cells below the cap, not the margin, and no block for the cutoff.  The clause of the
reading at the root (the reading is `v` capped by the cut there) and its commutation with caps are
prospective, as are a scheme over the private type and the donor that carries the readings as
lawful sections, the gate reading capped by the cut, and their assembly.  (R1), finite-cut
receiving for all models, and the attached gated extension over the private contexts that models
acquire are open; nothing here implies them.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.  The generic statements are stated here so
that the files where they belong are unchanged: `Label.IsWitness.min_const_of_isSelfVisible`
belongs in `VaughtConjecture.Extension.WitnessAlgebra`, beside `Label.IsWitness.max`, and the block
pieces (`CappedDonorReading.piece` and its lemmas) beside its block arithmetic;
`Label.exists_eq_of_not_isSelfVisible`, `CappedDonorReading.finitePart` and its lemmas,
`CappedDonorReading.isSuccPrelimit_omega0_mul`, `CappedDonorReading.coe_omega0_mul_add_le_coe_iff`
and `CappedDonorReading.min_visibilityReplace_natCast` belong beside the blocks of
`VaughtConjecture.Label.Visibility`.
-/

universe u

namespace VaughtConjecture

open Finset Label Ordinal

namespace CappedDonorReading

/-! ### Finite parts and block pieces -/

/-- The **finite part** `o % ω` of an ordinal `o`, as a natural number. -/
noncomputable def finitePart (o : Ordinal.{u}) : ℕ :=
  (lt_omega0.mp (mod_lt o omega0_ne_zero)).choose

/-- The finite part, cast back to an ordinal, is `o % ω`. -/
theorem natCast_finitePart (o : Ordinal.{u}) : (finitePart o : Ordinal.{u}) = o % ω :=
  (lt_omega0.mp (mod_lt o omega0_ne_zero)).choose_spec.symm

/-- The finite part of `ω * b + n` is `n`. -/
@[simp] theorem finitePart_omega0_mul_add (b : Ordinal.{u}) (n : ℕ) :
    finitePart (ω * b + n) = n := by
  have h := natCast_finitePart (ω * b + n)
  rw [omega0_mul_add_natCast_mod] at h
  exact_mod_cast h

/-- An ordinal is `ω * (o / ω) + finitePart o`. -/
theorem omega0_mul_div_add_finitePart (o : Ordinal.{u}) : ω * (o / ω) + finitePart o = o := by
  rw [natCast_finitePart, div_add_mod]

/-- A multiple of `ω` is zero or a limit. -/
theorem isSuccPrelimit_omega0_mul (b : Ordinal.{u}) : Order.IsSuccPrelimit (ω * b) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

/-- The labels `ω * a + m` and `ω * b + n` compare lexicographically in block and finite part. -/
theorem coe_omega0_mul_add_le_coe_iff {a b : Ordinal.{u}} {m n : ℕ} :
    ((ω * a + m : Ordinal.{u}) : Label.{u}) ≤ ((ω * b + n : Ordinal.{u}) : Label.{u}) ↔
      a < b ∨ a = b ∧ m ≤ n := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff]

/-- Capping a finite part at `N` commutes with visibility replacement at a threshold `k ≤ N` with
a value `i ≤ k`. -/
theorem min_visibilityReplace_natCast {N k i : ℕ} (hk : k ≤ N) (hi : i ≤ k) (δ : Ordinal.{u}) :
    min (Ordinal.visibilityReplace k i δ) (N : Ordinal.{u}) =
      Ordinal.visibilityReplace k i (min δ (N : Ordinal.{u})) := by
  rcases lt_or_ge δ ω with hδ | hδ
  · obtain ⟨n, rfl⟩ := lt_omega0.mp hδ
    rw [← Nat.mono_cast.map_min, Ordinal.visibilityReplace_natCast,
      Ordinal.visibilityReplace_natCast]
    by_cases hnk : n < k
    · have : min n N < k := (min_le_left n N).trans_lt hnk
      simp only [hnk, this, ↓reduceIte, ← Nat.mono_cast.map_min,
        min_eq_left (hi.trans hk)]
    · have : ¬ min n N < k := by omega
      simp only [hnk, this, ↓reduceIte, ← Nat.mono_cast.map_min]
  · have hN : (N : Ordinal.{u}) < ω := natCast_lt_omega0 N
    have hvr : ω ≤ Ordinal.visibilityReplace k i δ :=
      not_lt.mp fun h ↦ (not_lt.mpr hδ)
        ((Ordinal.visibilityReplace_lt_iff isSuccLimit_omega0.isSuccPrelimit k i).mp h)
    rw [min_eq_right (hN.le.trans hvr), min_eq_right (hN.le.trans hδ),
      Ordinal.visibilityReplace_natCast, ite_eq_right (by omega)]

/-- The **block piece** at threshold `N` from the block `b` to the block `r`: `⊥` below the block
`b` (that is, below `ω * b`), the ordinal `ω * r + min (o - ω * b) N` at an ordinal `o ≥ ω * b`,
and `⊤` at `⊤`.  On the block `b` it moves `ω * b + n` to `ω * r + min n N`, and above that block
it is the constant `ω * r + N`. -/
noncomputable def piece (N : ℕ) (b r : Ordinal.{u}) : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (fun o ↦ if o < ω * b then ⊥ else
    ((ω * r + min (o - ω * b) (N : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) ⊤

/-- The block piece fixes `⊥`. -/
@[simp] theorem piece_bot (N : ℕ) (b r : Ordinal.{u}) : piece N b r ⊥ = ⊥ := rfl

/-- The block piece fixes `⊤`. -/
@[simp] theorem piece_top (N : ℕ) (b r : Ordinal.{u}) : piece N b r ⊤ = ⊤ := rfl

/-- The block piece at an ordinal. -/
theorem piece_coe (N : ℕ) (b r o : Ordinal.{u}) : piece N b r (o : Label.{u}) =
    if o < ω * b then ⊥ else
      ((ω * r + min (o - ω * b) (N : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := rfl

/-- The block piece at a point `ω * b + n` of its own block with `n ≤ N`. -/
theorem piece_omega0_mul_add {N n : ℕ} (hn : n ≤ N) (b r : Ordinal.{u}) :
    piece N b r ((ω * b + n : Ordinal.{u}) : Label.{u}) =
      ((ω * r + n : Ordinal.{u}) : Label.{u}) := by
  rw [piece_coe, ite_eq_right (not_lt.mpr le_self_add), Ordinal.add_sub_cancel,
    min_eq_left (by exact_mod_cast hn)]

/-- The block piece at a point `ω * b' + n` of a higher block `b' > b` is `ω * r + N`. -/
theorem piece_omega0_mul_add_of_lt {N : ℕ} {b b' : Ordinal.{u}} (h : b < b') (r : Ordinal.{u})
    (n : ℕ) : piece N b r ((ω * b' + n : Ordinal.{u}) : Label.{u}) =
      ((ω * r + N : Ordinal.{u}) : Label.{u}) := by
  have hlt : ω * b + N < ω * b' + n := omega0_mul_add_natCast_lt h N n
  rw [piece_coe, ite_eq_right (not_lt.mpr (le_self_add.trans hlt.le)), min_eq_right
    (Ordinal.le_sub_of_add_le hlt.le)]

/-- The block piece is monotone. -/
theorem monotone_piece (N : ℕ) (b r : Ordinal.{u}) : Monotone (piece N b r) := by
  intro x y hxy
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top => rw [top_le_iff.mp hxy]
  | coe o =>
    induction y using recBotCoeTop with
    | bot => exact absurd hxy (not_le.mpr (WithBot.bot_lt_coe _))
    | top => exact le_top
    | coe o' =>
      have hoo : o ≤ o' := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hxy)
      rw [piece_coe, piece_coe]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact bot_le
      · exact absurd (hoo.trans_lt h2) h1
      · refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
        have hsub : o - ω * b ≤ o' - ω * b := by
          rw [Ordinal.sub_le, Ordinal.add_sub_cancel_of_le (not_lt.mp h2)]
          exact hoo
        gcongr

/-- The block piece commutes with visibility replacement at every threshold `k ≤ N` and every
value `i ≤ k`. -/
theorem piece_visibilityReplace {N k i : ℕ} (hk : k ≤ N) (hi : i ≤ k) (b r : Ordinal.{u})
    (x : Label.{u}) :
    piece N b r (visibilityReplace k i x) = visibilityReplace k i (piece N b r x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    have hb := isSuccPrelimit_omega0_mul b
    rw [visibilityReplace_coe, piece_coe, piece_coe]
    by_cases ho : o < ω * b
    · rw [ite_eq_left ((Ordinal.visibilityReplace_lt_iff hb k i).mpr ho), ite_eq_left ho,
        visibilityReplace_bot]
    · rw [ite_eq_right (mt (Ordinal.visibilityReplace_lt_iff hb k i).mp ho), ite_eq_right ho,
        visibilityReplace_coe]
      obtain ⟨δ, rfl⟩ : ∃ δ, o = ω * b + δ :=
        ⟨o - ω * b, (Ordinal.add_sub_cancel_of_le (not_lt.mp ho)).symm⟩
      rw [Ordinal.visibilityReplace_add hb, Ordinal.add_sub_cancel, Ordinal.add_sub_cancel,
        Ordinal.visibilityReplace_add (isSuccPrelimit_omega0_mul r),
        min_visibilityReplace_natCast hk hi]

/-- **The block piece is a witness bounded by grade `N`.**  Above `N` the guard holds only where
the piece is `⊥`, below the block `b`, and visibility replacement stays below that block. -/
theorem isWitness_piece (N : ℕ) (b r : Ordinal.{u}) :
    IsWitness (stepSuppressor.{u} N) (piece N b r) where
  antitone := (IsWitness.id_step N).antitone
  isSelfVisible := (IsWitness.id_step N).isSelfVisible
  map_bot := rfl
  monotone := monotone_piece N b r
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ N
    · exact piece_visibilityReplace hk hi b r x
    rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
    induction x using recBotCoeTop with
    | bot => rfl
    | top => exact absurd hx (by simp)
    | coe o =>
      have ho : o < ω * b := by
        by_contra h
        rw [piece_coe, ite_eq_right h] at hx
        exact WithBot.coe_ne_bot hx
      rw [visibilityReplace_coe, piece_coe, piece_coe, ite_eq_left ho,
        ite_eq_left ((Ordinal.visibilityReplace_lt_iff (isSuccPrelimit_omega0_mul b) k i).mpr ho),
        visibilityReplace_bot]

/-- **Capping a witness bounded by grade `N`** at a label `c` self-visible at `N` gives a witness
bounded by grade `N`. -/
theorem _root_.VaughtConjecture.Label.IsWitness.min_const_of_isSelfVisible {N : ℕ}
    {σ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor.{u} N) σ) {c : Label.{u}}
    (hc : IsSelfVisible N c) : IsWitness (stepSuppressor.{u} N) fun x ↦ min (σ x) c where
  antitone := hσ.antitone
  isSelfVisible := hσ.isSelfVisible
  map_bot := by simp [hσ.map_bot]
  monotone _ _ h := min_le_min_right _ (hσ.monotone h)
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ N
    · rw [hσ.visibilityReplace_comm x k (by simp [hk]) i hi,
        visibilityReplace_min_of_isSelfVisible hi (hc.mono hk)]
    rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, min_eq_bot] at hx
    rcases hx with hx | hx
    · rw [hσ.apply_visibilityReplace_eq_bot hx k hi, hx]; simp
    · simp [hx]

/-! ### Reference data, the cut, activity, and the capped reading -/

/-- **Reference data of a private context**: a cell `cap` (the private cap), its grade
`fullGrade` (written `N`), a finite set `blocks` of block indices (the block of index `b` is the
interval `[ω * b, ω * b + ω)`), a reference cell `ref b` for each block, and the finite part
`off b` of its label.  The laws, with the margin, are `PrivateReference.HasMargin`. -/
structure PrivateReference (ι : Type*) where
  /-- The private cap. -/
  cap : ι
  /-- The full grade `N`: the grade of the cap and the threshold of the readings. -/
  fullGrade : ℕ
  /-- The indices of the requested blocks. -/
  blocks : Finset Ordinal.{u}
  /-- The reference cell of each block. -/
  ref : Ordinal.{u} → ι
  /-- The finite part of the label of each reference cell. -/
  off : Ordinal.{u} → ℕ

namespace PrivateReference

variable {ι α : Type*} (P : PrivateReference.{u} ι) {D : CellScheme ι α} {R : D.Rows.{u}}
  {w v : ι → Label.{u}}

/-- **The cut** of a labelling `v` of the private cells: the smaller of `v` at the cap and the
largest of the replacements `vr_N(N, v (ref b))` of the reference labels at the threshold and value
`N`.  At the actual labels, with the margin, it is the largest of the `ω * b + N`
(`HasMargin.cut_eq`). -/
noncomputable def cut (v : ι → Label.{u}) : Label.{u} :=
  min (v P.cap) (P.blocks.sup fun b ↦ visibilityReplace P.fullGrade P.fullGrade (v (P.ref b)))

/-- A labelling `v` of the private cells is **active** when it is not `⊥` at the cap nor at any
reference cell. -/
def IsActive (v : ι → Label.{u}) : Prop :=
  v P.cap ≠ ⊥ ∧ ∀ b ∈ P.blocks, v (P.ref b) ≠ ⊥

/-- **The capped reading** of a donor label through a labelling `v` of the private cells: `⊥` at
`⊥`; at an ordinal `o` of the block `b = o / ω` with finite part `n`, the replacement
`vr_N(n, v (ref b))` of the reference label capped by the cut; and the cut at `⊤`. -/
noncomputable def reading (v : ι → Label.{u}) : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (fun o ↦ min (visibilityReplace P.fullGrade (finitePart o) (v (P.ref (o / ω))))
    (P.cut v)) (P.cut v)

/-- A labelling `ℓ` of donor cells **reads in the blocks** of `P` when each of its ordinal labels
lies in a requested block with finite part at most `N`. -/
def ReadsInBlocks {κ : Type*} (ℓ : κ → Label.{u}) : Prop :=
  ∀ t (o : Ordinal.{u}), ℓ t = o → o / ω ∈ P.blocks ∧ o % ω ≤ P.fullGrade

/-- **The laws of reference data with the margin**, for rows `R` of a cell scheme `D` and a
labelling `w` (the actual labels of the private cells): `w` is lawful, every cell lies below the
cap, the cap has grade `N`, each reference cell `ref b` is labelled `ω * b + off b` with
`off b < N`, and the **margin**: the cap is labelled at least every `ω * b + N`
([Kni26, Lemma 8.1.1], clauses 3 and 4). -/
structure HasMargin (R : D.Rows.{u}) (w : ι → Label.{u}) : Prop where
  /-- The actual labels are lawful. -/
  isLawful : R.IsLawful w
  /-- Every cell lies below the cap. -/
  mem_below (x : ι) : x ∈ D.below (D.gradedIndex P.cap)
  /-- The cap has the full grade. -/
  grade_cap : D.grade P.cap = P.fullGrade
  /-- The finite part of a reference label lies below the full grade. -/
  off_lt (b : Ordinal.{u}) : b ∈ P.blocks → P.off b < P.fullGrade
  /-- The label of a reference cell. -/
  label_ref (b : Ordinal.{u}) : b ∈ P.blocks →
    w (P.ref b) = ((ω * b + P.off b : Ordinal.{u}) : Label.{u})
  /-- The margin: the cap is labelled at least every `ω * b + N`. -/
  margin (b : Ordinal.{u}) : b ∈ P.blocks →
    ((ω * b + P.fullGrade : Ordinal.{u}) : Label.{u}) ≤ w P.cap

/-- The capped reading fixes `⊥`. -/
@[simp] theorem reading_bot : P.reading v ⊥ = ⊥ := rfl

/-- The capped reading sends `⊤` to the cut. -/
@[simp] theorem reading_top : P.reading v ⊤ = P.cut v := rfl

/-- The capped reading at an ordinal. -/
theorem reading_coe (o : Ordinal.{u}) : P.reading v (o : Label.{u}) =
    min (visibilityReplace P.fullGrade (finitePart o) (v (P.ref (o / ω)))) (P.cut v) := rfl

/-- The capped reading at a point `ω * b + n` of the block `b`. -/
theorem reading_omega0_mul_add (b : Ordinal.{u}) (n : ℕ) :
    P.reading v ((ω * b + n : Ordinal.{u}) : Label.{u}) =
      min (visibilityReplace P.fullGrade n (v (P.ref b))) (P.cut v) := by
  rw [reading_coe, finitePart_omega0_mul_add, omega0_mul_add_natCast_div]

/-- When the cut is `⊥`, the capped reading is constantly `⊥`. -/
theorem reading_of_cut_eq_bot (h : P.cut v = ⊥) (x : Label.{u}) : P.reading v x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => exact h
  | coe o => rw [reading_coe, h, min_bot_right]

/-- The cut is self-visible at `N` when the label of the cap is. -/
theorem isSelfVisible_cut (hC : IsSelfVisible P.fullGrade (v P.cap)) :
    IsSelfVisible P.fullGrade (P.cut v) :=
  hC.min (Finset.sup_induction (isSelfVisible_bot _) (fun _ ha _ hb ↦ ha.max hb)
    fun _ _ ↦ isSelfVisible_visibilityReplace_self _ _)

/-- An ordinal label of a donor that reads in the blocks is a point `ω * b + n` of a requested
block with `n ≤ N`. -/
theorem exists_eq_of_readsInBlocks {o : Ordinal.{u}}
    (h : o / ω ∈ P.blocks ∧ o % ω ≤ P.fullGrade) :
    ∃ b ∈ P.blocks, ∃ n ≤ P.fullGrade, o = ω * b + n := by
  refine ⟨o / ω, h.1, finitePart o, ?_, (omega0_mul_div_add_finitePart o).symm⟩
  have := h.2
  rw [← natCast_finitePart] at this
  exact_mod_cast this

/-! ### The codes of the reference cells in the row of the cap -/

variable {P}

/-- **The capped witness at the cap** of a lawful labelling `v`: a witness `τ` bounded by grade
`N`, with values at most `v` at the cap, that reads each entry of the row of the cap as the label
of its cell capped at the cap (`Label.TransformsTo.exists_isWitness_capped`). -/
theorem HasMargin.exists_isWitness_capped (hP : P.HasMargin R w) (hv : R.IsLawful v) :
    ∃ τ, IsWitness (stepSuppressor.{u} P.fullGrade) τ ∧ (∀ x, τ x ≤ v P.cap) ∧
      ∀ x, τ (R.row P.cap ⟨x, hP.mem_below x⟩) = min (v x) (v P.cap) := by
  obtain ⟨τ, hτ, hτC, hτrow⟩ := (hv.locality P.cap).exists_isWitness_capped
    (grade := fun d : D.below (D.gradedIndex P.cap) ↦ D.grade d) (p := fun d ↦ v d)
    (c := ⟨P.cap, D.mem_below_gradedIndex P.cap⟩) (fun d ↦ d.2.2) (hv.orderly P.cap)
  -- The grade of the cap, read through the subtype of the cells below it.
  change IsWitness (stepSuppressor (D.grade P.cap)) τ at hτ
  rw [hP.grade_cap] at hτ
  exact ⟨τ, hτ, hτC, fun x ↦ hτrow ⟨x, hP.mem_below x⟩⟩

/-- A label that is not self-visible at `N` is a point `ω * r + j` with `j < N`. -/
theorem _root_.VaughtConjecture.Label.exists_eq_of_not_isSelfVisible {N : ℕ} {c : Label.{u}}
    (hc : ¬ IsSelfVisible N c) :
    ∃ (r : Ordinal.{u}) (j : ℕ), j < N ∧ c = ((ω * r + j : Ordinal.{u}) : Label.{u}) := by
  induction c using recBotCoeTop with
  | bot => exact absurd (isSelfVisible_bot N) hc
  | top => exact absurd (isSelfVisible_top N) hc
  | coe o =>
    refine ⟨o / ω, finitePart o, ?_, by rw [omega0_mul_div_add_finitePart]⟩
    rw [isSelfVisible_coe, ← natCast_finitePart, Nat.cast_le] at hc
    omega

/-- **The codes of the reference cells.**  With the margin, the row of the cap reads each
reference cell `ref b` at a point `ω * r b + j b` with `j b < N`, and the code blocks `r b` are
strictly increasing in `b`.  The capped witness of the actual labels at the cap reads the code as
`ω * b + off b`; a self-visible code would make that label self-visible at `N`, and two reference
cells of different blocks read in one code block would be read in one block. -/
theorem HasMargin.exists_code (hP : P.HasMargin R w) :
    ∃ (r : Ordinal.{u} → Ordinal.{u}) (j : Ordinal.{u} → ℕ),
      (∀ b ∈ P.blocks, j b < P.fullGrade ∧ R.row P.cap ⟨P.ref b, hP.mem_below _⟩ =
        ((ω * r b + j b : Ordinal.{u}) : Label.{u})) ∧
      ∀ b ∈ P.blocks, ∀ b' ∈ P.blocks, b < b' → r b < r b' := by
  obtain ⟨τ, hτ, -, hrow⟩ := hP.exists_isWitness_capped hP.isLawful
  have hτref (b : Ordinal.{u}) (hb : b ∈ P.blocks) :
      τ (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) =
        ((ω * b + P.off b : Ordinal.{u}) : Label.{u}) := by
    rw [hrow, hP.label_ref b hb, min_eq_left (le_trans ?_ (hP.margin b hb))]
    exact coe_omega0_mul_add_le_coe_iff.mpr (.inr ⟨rfl, (hP.off_lt b hb).le⟩)
  have hcode (b : Ordinal.{u}) (hb : b ∈ P.blocks) : ∃ (r : Ordinal.{u}) (j : ℕ),
      j < P.fullGrade ∧ R.row P.cap ⟨P.ref b, hP.mem_below _⟩ =
        ((ω * r + j : Ordinal.{u}) : Label.{u}) := by
    refine exists_eq_of_not_isSelfVisible fun hc ↦ ?_
    have h := hτ.visibilityReplace_comm (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) P.fullGrade
      (by simp) P.fullGrade le_rfl
    rw [hc, hτref b hb] at h
    have hsv : IsSelfVisible P.fullGrade ((ω * b + P.off b : Ordinal.{u}) : Label.{u}) := h.symm
    rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le] at hsv
    exact absurd (hP.off_lt b hb) (not_lt.mpr hsv)
  choose! r j hj hrj using hcode
  refine ⟨r, j, fun b hb ↦ ⟨hj b hb, hrj b hb⟩, fun b hb b' hb' hbb' ↦ ?_⟩
  by_contra hr
  rcases (not_lt.mp hr).lt_or_eq with hlt | heq
  · -- The code of `ref b'` lies below that of `ref b`, so its label does too.
    have hle := hτ.monotone (show R.row P.cap ⟨P.ref b', hP.mem_below _⟩ ≤
        R.row P.cap ⟨P.ref b, hP.mem_below _⟩ by
      rw [hrj b' hb', hrj b hb]; exact coe_omega0_mul_add_le_coe_iff.mpr (.inl hlt))
    rw [hτref b' hb', hτref b hb, coe_omega0_mul_add_le_coe_iff] at hle
    rcases hle with h | ⟨h, -⟩
    · exact absurd h (not_lt.mpr hbb'.le)
    · exact absurd h hbb'.ne'
  · -- One code block: the code of `ref b'` is a replacement of the code of `ref b`.
    have hvr : R.row P.cap ⟨P.ref b', hP.mem_below _⟩ =
        visibilityReplace P.fullGrade (j b') (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) := by
      rw [hrj b' hb', hrj b hb, heq, visibilityReplace_coe,
        Ordinal.visibilityReplace_omega0_mul_add_natCast, ite_eq_left (hj b hb)]
    have h := congrArg τ hvr
    rw [hτ.visibilityReplace_comm _ _ (by simp) _ (hj b' hb').le, hτref b' hb', hτref b hb,
      visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
      ite_eq_left (hP.off_lt b hb), WithBot.coe_inj, WithTop.coe_inj] at h
    have hdiv := congrArg (· / ω) h
    simp only [omega0_mul_add_natCast_div] at hdiv
    exact hbb'.ne' hdiv

/-! ### The capped-donor lemma -/

/-- The capped reading sends to `⊥` only `⊥`, at the labels that read in the blocks, when the cut
is not `⊥` and no reference cell is `⊥`. -/
theorem eq_bot_of_reading_eq_bot (hcut : P.cut v ≠ ⊥) (href : ∀ b ∈ P.blocks, v (P.ref b) ≠ ⊥)
    {x : Label.{u}} (hx : ∀ o : Ordinal.{u}, x = o → o / ω ∈ P.blocks ∧ o % ω ≤ P.fullGrade)
    (h : P.reading v x = ⊥) : x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => exact absurd h hcut
  | coe o =>
    obtain ⟨b, hb, n, -, rfl⟩ := P.exists_eq_of_readsInBlocks (hx o rfl)
    rw [reading_omega0_mul_add, min_eq_bot, visibilityReplace_eq_bot_iff] at h
    exact (h.resolve_right hcut |> href b hb).elim

/-- **The capped-donor lemma** (lawfulness of the capped reading).  Let `P` be reference data
with the margin for rows `R` and actual labels `w` (`HasMargin`), let `v` be a lawful labelling of
the private cells that is not `⊥` at any reference cell, and let `ℓ` be a lawful labelling, for
rows `Q`, of donor cells of grade at most `N` whose labels read in the blocks of `P`.  Then the
capped reading `P.reading v ∘ ℓ` is lawful for `Q`.

If the cut is `⊥` the reading is constantly `⊥`.  Otherwise the reading is `ν ∘ ℓ` for a witness
`ν` bounded by grade `N` that sends to `⊥` only the labels `⊥` of `ℓ`
(`CellScheme.Rows.IsLawful.map_of_apply_eq_bot`): `ν` is the capped witness `τ` of `v` at the cap
(`HasMargin.exists_isWitness_capped`), after the block pieces that move each requested block onto
the code block of its reference cell in the row of the cap (`HasMargin.exists_code`), capped by the
cut.  The cap clause of activity is not used here: when `v` is `⊥` at the cap the cut is `⊥`. -/
theorem HasMargin.isLawful_reading_of_ne_bot (hP : P.HasMargin R w) (hv : R.IsLawful v)
    (href : ∀ b ∈ P.blocks, v (P.ref b) ≠ ⊥) {κ β : Type*} {E : CellScheme κ β}
    {Q : E.Rows.{u}} {ℓ : κ → Label.{u}} (hℓ : Q.IsLawful ℓ) (hK : ∀ t, E.grade t ≤ P.fullGrade)
    (hblk : P.ReadsInBlocks ℓ) : Q.IsLawful (P.reading v ∘ ℓ) := by
  by_cases hcut : P.cut v = ⊥
  · have h : P.reading v ∘ ℓ = fun _ ↦ ⊥ := funext fun t ↦ P.reading_of_cut_eq_bot hcut (ℓ t)
    rw [h]
    exact CellScheme.Rows.isLawful_const_bot
  have hS : P.blocks.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro hS
    exact hcut (by simp [cut, hS])
  obtain ⟨r, j, hcode, hmono⟩ := hP.exists_code
  obtain ⟨τ, hτ, -, hτrow⟩ := hP.exists_isWitness_capped hv
  have hvC : IsSelfVisible P.fullGrade (v P.cap) := hP.grade_cap ▸ hv.orderly P.cap
  -- The block pieces, one per requested block, and their supremum `φ`.
  have hφ : IsWitness (stepSuppressor.{u} P.fullGrade)
      (fun x ↦ P.blocks.sup fun b ↦ piece P.fullGrade b (r b) x) :=
    IsWitness.finsetSup hS fun b _ ↦ isWitness_piece P.fullGrade b (r b)
  obtain ⟨ρ, hρ, hρφ⟩ := hφ.exists_eq_comp_of_isShort hτ le_rfl
  have hν := hρ.min_const_of_isSelfVisible (P.isSelfVisible_cut hvC)
  -- `φ` fixes `⊤` and moves each point `ω * b + n`, `n ≤ N`, of a requested block to the code
  -- block of `ref b`.
  have hφtop : (P.blocks.sup fun b ↦ piece P.fullGrade b (r b) ⊤) = ⊤ := by
    obtain ⟨b, hb⟩ := hS
    exact top_le_iff.mp (le_sup_of_le hb (piece_top _ _ _).ge)
  have hφpt (b : Ordinal.{u}) (hb : b ∈ P.blocks) (n : ℕ) (hn : n ≤ P.fullGrade) :
      (P.blocks.sup fun b' ↦ piece P.fullGrade b' (r b') ((ω * b + n : Ordinal.{u}) : Label.{u}))
        = ((ω * r b + n : Ordinal.{u}) : Label.{u}) := by
    refine le_antisymm (Finset.sup_le fun b' hb' ↦ ?_)
      (le_sup_of_le hb (piece_omega0_mul_add hn b (r b)).ge)
    rw [piece_coe]
    split_ifs with h
    · exact bot_le
    have hb'b : b' ≤ b := not_lt.mp fun hlt ↦ h (by
      simpa using omega0_mul_add_natCast_lt hlt n 0)
    rcases hb'b.lt_or_eq with hlt | rfl
    · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (omega0_mul_add_lt
        ((min_le_right _ _).trans_lt (natCast_lt_omega0 _)) (hmono b' hb' b hb hlt) _).le)
    · rw [Ordinal.add_sub_cancel, min_eq_left (by exact_mod_cast hn)]
  -- `τ` reads the code block of `ref b` through the label of `ref b` capped at the cap.
  have hτpt (b : Ordinal.{u}) (hb : b ∈ P.blocks) (n : ℕ) (hn : n ≤ P.fullGrade) :
      τ ((ω * r b + n : Ordinal.{u}) : Label.{u}) =
        min (visibilityReplace P.fullGrade n (v (P.ref b))) (v P.cap) := by
    have hc : ((ω * r b + n : Ordinal.{u}) : Label.{u}) = visibilityReplace P.fullGrade n
        (R.row P.cap ⟨P.ref b, hP.mem_below _⟩) := by
      rw [(hcode b hb).2, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
        ite_eq_left (hcode b hb).1]
    rw [hc, hτ.visibilityReplace_comm _ _ (by simp) n hn, hτrow,
      visibilityReplace_min_of_isSelfVisible hn hvC]
  have hcutC : P.cut v ≤ v P.cap := min_le_left _ _
  have key (x : Label.{u})
      (hx : ∀ o : Ordinal.{u}, x = o → o / ω ∈ P.blocks ∧ o % ω ≤ P.fullGrade) :
      P.reading v x = min (ρ x) (P.cut v) := by
    induction x using recBotCoeTop with
    | bot => simp [hρ.map_bot]
    | top =>
      rw [reading_top, hρφ ⊤ (isShort_top _), hφtop, eq_comm, min_eq_right]
      calc P.cut v ≤ v P.cap := hcutC
        _ = τ (R.row P.cap ⟨P.cap, hP.mem_below _⟩) := by rw [hτrow, min_self]
        _ ≤ τ ⊤ := hτ.monotone le_top
    | coe o =>
      obtain ⟨b, hb, n, hn, rfl⟩ := P.exists_eq_of_readsInBlocks (hx o rfl)
      rw [reading_omega0_mul_add, hρφ _ (isShort_coe.mpr (by
          rw [omega0_mul_add_natCast_mod]; exact_mod_cast hn)), hφpt b hb n hn, hτpt b hb n hn,
        min_assoc, min_eq_right hcutC]
  have hcomp : P.reading v ∘ ℓ = (fun x ↦ min (ρ x) (P.cut v)) ∘ ℓ :=
    funext fun t ↦ key (ℓ t) (hblk t)
  rw [hcomp]
  refine hℓ.map_of_apply_eq_bot hK hν fun t ht ↦ ?_
  rw [← key (ℓ t) (hblk t)] at ht
  exact eq_bot_of_reading_eq_bot hcut href (hblk t) ht

/-- **The capped-donor lemma for active labellings.**  For reference data with the margin, every
active lawful labelling `v` of the private cells gives a lawful capped reading `P.reading v ∘ ℓ`
of every lawful donor labelling `ℓ` of grades at most `N` that reads in the blocks
(`HasMargin.isLawful_reading_of_ne_bot`). -/
theorem HasMargin.isLawful_reading (hP : P.HasMargin R w) (hv : R.IsLawful v)
    (hact : P.IsActive v) {κ β : Type*} {E : CellScheme κ β} {Q : E.Rows.{u}}
    {ℓ : κ → Label.{u}} (hℓ : Q.IsLawful ℓ) (hK : ∀ t, E.grade t ≤ P.fullGrade)
    (hblk : P.ReadsInBlocks ℓ) : Q.IsLawful (P.reading v ∘ ℓ) :=
  hP.isLawful_reading_of_ne_bot hv hact.2 hℓ hK hblk

/-! ### The reading at the actual labels -/

/-- **The cut at the actual labels** is the largest of the `ω * b + N`: the replacement of
`ω * b + off b` at the threshold and value `N` is `ω * b + N`, and the margin puts the cap at least
all of them. -/
theorem HasMargin.cut_eq (hP : P.HasMargin R w) :
    P.cut w = P.blocks.sup fun b ↦ ((ω * b + P.fullGrade : Ordinal.{u}) : Label.{u}) := by
  have hsup : (P.blocks.sup fun b ↦ visibilityReplace P.fullGrade P.fullGrade (w (P.ref b))) =
      P.blocks.sup fun b ↦ ((ω * b + P.fullGrade : Ordinal.{u}) : Label.{u}) :=
    Finset.sup_congr rfl fun b hb ↦ by
      rw [hP.label_ref b hb, visibilityReplace_coe,
        Ordinal.visibilityReplace_omega0_mul_add_natCast, ite_eq_left (hP.off_lt b hb)]
  rw [cut, hsup, min_eq_right (Finset.sup_le fun b hb ↦ hP.margin b hb)]

/-- **The reading at the actual labels** is the label capped by the cut, at every label that
reads in the blocks. -/
theorem HasMargin.reading_eq_min (hP : P.HasMargin R w) {x : Label.{u}}
    (hx : ∀ o : Ordinal.{u}, x = o → o / ω ∈ P.blocks ∧ o % ω ≤ P.fullGrade) :
    P.reading w x = min x (P.cut w) := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨b, hb, n, -, rfl⟩ := P.exists_eq_of_readsInBlocks (hx o rfl)
    rw [reading_omega0_mul_add, hP.label_ref b hb, visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, ite_eq_left (hP.off_lt b hb)]

/-- **The reading at the actual labels recovers the donor below `⊤`**: at a label other than `⊤`
that reads in the blocks, the reading is the label itself, since the cut lies above every
`ω * b + n` with `n ≤ N`. -/
theorem HasMargin.reading_eq_self (hP : P.HasMargin R w) {x : Label.{u}}
    (hx : ∀ o : Ordinal.{u}, x = o → o / ω ∈ P.blocks ∧ o % ω ≤ P.fullGrade) (hxt : x ≠ ⊤) :
    P.reading w x = x := by
  rw [hP.reading_eq_min hx, min_eq_left]
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top => exact absurd rfl hxt
  | coe o =>
    obtain ⟨b, hb, n, hn, rfl⟩ := P.exists_eq_of_readsInBlocks (hx o rfl)
    rw [hP.cut_eq]
    exact le_sup_of_le hb (coe_omega0_mul_add_le_coe_iff.mpr (.inr ⟨rfl, hn⟩))

end PrivateReference

/-! ### The two-point private type with a proper anchor -/

namespace AnchorInput

open CellScheme

/-- The scopes of the five private cells: `{0}`, `{1}` (dead), `univ` (the cells `z₁ = 2` and
`z₂ = 3` of grade `1`) and `univ` (the cap `4`, of grade `2`). -/
def cellScope : Fin 5 → Finset (Fin 2) := ![{0}, {1}, univ, univ, univ]

/-- The grades of the five private cells. -/
def cellGrade : Fin 5 → ℕ := ![1, 1, 1, 1, 2]

/-- The private cell scheme on two points with the interval plan. -/
def cells : CellScheme (Fin 5) (Fin 2) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The label `ω + j`. -/
noncomputable def omegaAdd (j : ℕ) : Label.{u} := ((ω + j : Ordinal.{u}) : Label.{u})

/-- The codes `1`, `ω + 1`, `ω + 2` at the cells `2`, `3`, `4`, and `⊥` at the dead cells. -/
noncomputable def code : Fin 5 → Label.{u} :=
  ![⊥, ⊥, ((1 : ℕ) : Label.{u}), omegaAdd 1, omegaAdd 2]

/-- The row values: the row of `z₁ = 2` reads `z₁` and `z₂` at `1`; the rows of `z₂ = 3` and of
the cap read the codes; the dead cells read `⊥`. -/
noncomputable def rowValue (s t : Fin 5) : Label.{u} :=
  if s = 2 then (if t = 2 ∨ t = 3 then ((1 : ℕ) : Label.{u}) else ⊥)
  else if s = 3 ∨ s = 4 then code t else ⊥

/-- The rows of the private type. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The labelling `⊥, ⊥, x, y, c` of the private cells. -/
noncomputable def lab (x y c : Label.{u}) : Fin 5 → Label.{u} := ![⊥, ⊥, x, y, c]

private theorem availability_cases : ∀ s t : Fin 5, cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → (s = 0 ∨ s = 1) ∨ (cellScope t = cellScope s ∧
      cellGrade t = cellGrade s) := by
  decide

/-- The labellings `lab x y c` are lawful once the localities at the three live cells hold. -/
private theorem isLawful_lab_of {x y c : Label.{u}} (hx : IsSelfVisible 1 x)
    (hy : IsSelfVisible 1 y) (hc : IsSelfVisible 2 c)
    (h2 : TransformsTo (fun d : cells.below (cells.gradedIndex 2) ↦ cells.grade d) (rows.row 2)
      (fun d ↦ min (lab x y c d) x))
    (h3 : TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.row 3)
      (fun d ↦ min (lab x y c d) y))
    (h4 : TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.row 4)
      (fun d ↦ min (lab x y c d) c)) : rows.{u}.IsLawful (lab x y c) where
  orderly d := by
    fin_cases d
    exacts [isSelfVisible_bot _, isSelfVisible_bot _, hx, hy, hc]
  locality s := by
    fin_cases s
    · simpa [lab] using TransformsTo.bot _ (rows.row 0)
    · simpa [lab] using TransformsTo.bot _ (rows.row 1)
    · exact h2
    · exact h3
    · exact h4
  availability s t hst hg := by
    rcases availability_cases s t hst hg with hs | ⟨h1, h2⟩
    · refine ⟨t, rfl, ?_⟩
      rcases hs with rfl | rfl <;> exact bot_le
    · exact ⟨s, Prod.ext h1.symm h2.symm, le_rfl⟩

/-- A locality of the private type from a witness, checked cell by cell. -/
private theorem transformsTo_of (s : Fin 5) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {F : Fin 5 → Label.{u}}
    (h : ∀ d : Fin 5, cells.gradedIndex d ≤ cells.gradedIndex s →
      F d = min (σ (rowValue s d)) (g (cellGrade d))) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.row s)
      (fun d ↦ F d) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

private theorem natCast_lt_omegaAdd (n j : ℕ) : ((n : ℕ) : Label.{u}) < omegaAdd j := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, omegaAdd, WithBot.coe_lt_coe,
    WithTop.coe_lt_coe]
  exact (natCast_lt_omega0 n).trans_le le_self_add

private theorem omegaAdd_ne_bot (j : ℕ) : omegaAdd.{u} j ≠ ⊥ := WithBot.coe_ne_bot

private theorem omegaAdd_le_omegaAdd {i j : ℕ} (h : i ≤ j) : omegaAdd.{u} i ≤ omegaAdd j :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (add_le_add_right (Nat.cast_le.mpr h) _))

private theorem isSelfVisible_omegaAdd {k j : ℕ} (h : k ≤ j) :
    IsSelfVisible k (omegaAdd.{u} j) :=
  isSelfVisible_coe_add isSuccLimit_omega0.isSuccPrelimit h

private theorem raise_one : raise (3 : Label.{u}) 1 = 1 := by
  have h : ¬ (3 : Label.{u}) ≤ 1 := by simp
  simp only [raise, ite_eq_right h]

private theorem raise_omegaAdd (j : ℕ) : raise (3 : Label.{u}) (omegaAdd j) = ⊤ := by
  have h : (3 : Label.{u}) ≤ omegaAdd j := by simpa using (natCast_lt_omegaAdd.{u} 3 j).le
  simp only [raise, ite_eq_left h]

private theorem raise_bot' : raise (3 : Label.{u}) ⊥ = ⊥ :=
  raise_bot (bot_lt_iff_ne_bot.mpr (by simp))

private theorem isWitness_raise_three {K : ℕ} (hK : K ≤ 2) :
    IsWitness (stepSuppressor.{u} K) (raise (3 : Label.{u})) :=
  isWitness_raise (by simp; omega) (bot_lt_iff_ne_bot.mpr (by simp))

/-- **The actual labels of the private type**, `⊥, ⊥, 1, ⊤, ⊤`, are lawful: the codes at `3`
and above are raised to `⊤`. -/
theorem isLawful_lab_one_top_top : rows.{u}.IsLawful (lab (1 : Label.{u}) ⊤ ⊤) := by
  refine isLawful_lab_of (by simp) (isSelfVisible_top 1) (isSelfVisible_top 2) ?_ ?_ ?_
  · refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) | simp [lab, rowValue]
  · refine transformsTo_of 3 (F := fun d ↦ min (lab _ _ _ d) _)
      (isWitness_raise_three (K := 1) (by omega)) fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) |
      simp [lab, rowValue, code, cellGrade, raise_one, raise_omegaAdd, raise_bot']
  · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _)
      (isWitness_raise_three (K := 2) le_rfl) fun d _ ↦ ?_
    fin_cases d <;> simp [lab, rowValue, code, cellGrade, raise_one, raise_omegaAdd, raise_bot']

/-- The labels below `ω` (the finite ones and `⊥`) go to `⊥`; the others are kept. -/
private noncomputable def dropFinite (x : Label.{u}) : Label.{u} :=
  if x < ((ω : Ordinal.{u}) : Label.{u}) then ⊥ else x

private theorem lt_omega_visibilityReplace {x : Label.{u}}
    (hx : x < ((ω : Ordinal.{u}) : Label.{u})) (k i : ℕ) :
    visibilityReplace k i x < ((ω : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o =>
    rw [visibilityReplace_coe, WithBot.coe_lt_coe, WithTop.coe_lt_coe,
      Ordinal.visibilityReplace_lt_iff isSuccLimit_omega0.isSuccPrelimit]
    exact WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hx)
  | top => exact absurd hx (not_lt.mpr le_top)

/-- Sending the labels below `ω` to `⊥` is a witness with the suppressor `⊤`. -/
private theorem isWitness_dropFinite : IsWitness (fun _ ↦ (⊤ : Label.{u})) dropFinite where
  antitone := fun _ _ _ ↦ le_rfl
  isSelfVisible := fun n ↦ isSelfVisible_top n
  map_bot := by simp [dropFinite, WithBot.bot_lt_coe]
  monotone := by
    intro x y hxy
    unfold dropFinite
    split_ifs with hx hy hy
    · exact le_rfl
    · exact bot_le
    · exact absurd (hxy.trans_lt hy) hx
    · exact hxy
  visibilityReplace_comm x k _ i _ := by
    unfold dropFinite
    by_cases hx : x < ((ω : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (lt_omega_visibilityReplace hx k i), ite_eq_left hx, visibilityReplace_bot]
    · have hx0 : x ≠ ⊥ := fun h ↦ hx (h ▸ WithBot.bot_lt_coe _)
      rw [ite_eq_right (not_lt_omega_visibilityReplace hx0 hx k i), ite_eq_right hx]

private theorem dropFinite_one : dropFinite (1 : Label.{u}) = ⊥ := by
  have h : (1 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by simp
  simp only [dropFinite, ite_eq_left h]

private theorem dropFinite_omegaAdd (j : ℕ) : dropFinite (omegaAdd.{u} j) = omegaAdd j := by
  have h : ¬ omegaAdd.{u} j < ((ω : Ordinal.{u}) : Label.{u}) := by
    rw [omegaAdd, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    exact not_lt.mpr le_self_add
  simp only [dropFinite, ite_eq_right h]

private theorem dropFinite_bot : dropFinite (⊥ : Label.{u}) = ⊥ := isWitness_dropFinite.map_bot

/-- **A lawful labelling that drops the reference cell `z₁` and keeps the cap**:
`⊥, ⊥, ⊥, ω + 1, ω + 2`, the codes with the finite labels sent to `⊥`. -/
theorem isLawful_lab_bot_omegaAdd : rows.{u}.IsLawful (lab ⊥ (omegaAdd 1) (omegaAdd 2)) := by
  refine isLawful_lab_of (isSelfVisible_bot 1) (isSelfVisible_omegaAdd (by omega))
    (isSelfVisible_omegaAdd le_rfl) ?_ ?_ ?_
  · refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.bot_top fun d _ ↦ ?_
    fin_cases d <;> simp [lab]
  · refine transformsTo_of 3 (F := fun d ↦ min (lab _ _ _ d) _) isWitness_dropFinite
      fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) |
      simp [lab, rowValue, code, dropFinite_bot, dropFinite_one, dropFinite_omegaAdd]
  · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _) isWitness_dropFinite
      fun d _ ↦ ?_
    fin_cases d <;> simp [lab, rowValue, code, dropFinite_bot, dropFinite_one,
      dropFinite_omegaAdd, omegaAdd_le_omegaAdd]

/-! ### The one-point donor `1, ⊤` -/

/-- The donor cells: two cells of graded index `(univ, 1)` on one point. -/
def donorCells : CellScheme (Fin 2) (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The donor row values: the row of `e₁ = 0` reads `(1, 1)`, the row of `e₂ = 1` reads
`(1, 2)`, both in the block `[0, ω)`. -/
noncomputable def donorRowValue (s t : Fin 2) : Label.{u} :=
  if s = 0 then 1 else if t = 0 then 1 else 2

/-- The rows of the donor. -/
noncomputable def donorRows : donorCells.Rows.{u} := ⟨fun s t ↦ donorRowValue s t.1⟩

/-- The labelling `x₀, x₁` of the donor cells. -/
noncomputable def donorLab (x₀ x₁ : Label.{u}) : Fin 2 → Label.{u} := ![x₀, x₁]

private theorem raise_two_one : raise (2 : Label.{u}) 1 = 1 := by
  have h : ¬ (2 : Label.{u}) ≤ 1 := by simp
  simp only [raise, ite_eq_right h]

private theorem raise_two_two : raise (2 : Label.{u}) 2 = ⊤ := by
  simp only [raise, ite_eq_left le_rfl]

/-- **The donor labelling** `1, ⊤` is lawful: the row of `e₂` raised at `2`. -/
theorem isLawful_donorLab_one_top : donorRows.{u}.IsLawful (donorLab 1 ⊤) where
  orderly d := by fin_cases d <;> simp [donorLab, donorCells]
  locality s := by
    fin_cases s
    · exact ⟨_, _, IsWitness.id_top, fun d ↦ by
        obtain ⟨d, -⟩ := d; fin_cases d <;> simp [donorLab, donorRows, donorRowValue]⟩
    · exact ⟨_, _, isWitness_raise (K := 1) (h := (2 : Label.{u})) (by simp)
        (bot_lt_iff_ne_bot.mpr (by simp)), fun d ↦ by
        obtain ⟨d, -⟩ := d
        fin_cases d <;> simp [donorLab, donorRows, donorRowValue, raise_two_one, raise_two_two,
          donorCells]⟩
  availability s _ _ _ := ⟨s, rfl, le_rfl⟩

/-- **The donor's rows forbid `⊥` at `e₁` with a label other than `⊥` at `e₂`**: locality at
`e₂` reads `e₁` and `e₂` at `1` and `2 = vr_2(1, 2)`, and a shifter sending `1` to `⊥` sends
`2` to `⊥`. -/
theorem eq_bot_of_isLawful_donor {ρ : Fin 2 → Label.{u}} (hρ : donorRows.IsLawful ρ)
    (h₀ : ρ 0 = ⊥) : ρ 1 = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := hρ.locality 1
  have h0 := heq ⟨0, (le_rfl : donorCells.gradedIndex 0 ≤ donorCells.gradedIndex 1)⟩
  have h1 := heq ⟨1, (le_rfl : donorCells.gradedIndex 1 ≤ donorCells.gradedIndex 1)⟩
  -- The row of `e₂` reads `1` at `e₁` and `2` at `e₂` (`donorRows`, by definition).
  change min (ρ 0) (ρ 1) = min (σ 1) (g 1) at h0
  -- The same row, at `e₂`.
  change min (ρ 1) (ρ 1) = min (σ 2) (g 1) at h1
  rw [h₀, min_eq_left bot_le] at h0
  rw [min_self] at h1
  by_contra hne
  have hg : g 1 ≠ ⊥ := fun hg ↦ hne (by rw [h1, hg, min_eq_right bot_le])
  have hσ1 : σ 1 = ⊥ := (min_eq_bot.mp h0.symm).resolve_right hg
  have hσ2 : σ 2 = ⊥ := by
    have h := hw.visibilityReplace_comm 1 2 (by rw [hσ1]; exact bot_le) 2 le_rfl
    have hvr : visibilityReplace 2 2 (1 : Label.{u}) = 2 := by simp
    rw [hvr, hσ1, visibilityReplace_bot] at h
    exact h
  exact hne (by rw [h1, hσ2, min_eq_left bot_le])

/-! ### The reference data and the capped reading at this input -/

/-- **The reference data**: the cap `4`, the full grade `2`, the one block `[0, ω)`, its reference
cell `z₁ = 2`, labelled `1 = ω * 0 + 1`. -/
def reference : PrivateReference.{u} (Fin 5) := ⟨4, 2, {0}, fun _ ↦ 2, fun _ ↦ 1⟩

/-- **The margin holds** at the actual labels `⊥, ⊥, 1, ⊤, ⊤`: the cap is labelled `⊤`, at least
`ω * 0 + 2`. -/
theorem hasMargin : reference.{u}.HasMargin rows (lab (1 : Label.{u}) ⊤ ⊤) where
  isLawful := isLawful_lab_one_top_top
  mem_below x := by
    -- Membership below the cap is the comparison of graded indices (`CellScheme.mem_below`).
    change cells.gradedIndex x ≤ cells.gradedIndex 4
    revert x; decide
  grade_cap := rfl
  off_lt b _ := by simp [reference]
  label_ref b hb := by
    rw [show b = 0 from mem_singleton.mp hb]
    simp [reference, lab]
  margin b _ := le_top

/-- The donor labelling `1, ⊤` reads in the block `[0, ω)`, with finite part `1 ≤ 2`. -/
theorem readsInBlocks_donorLab : reference.{u}.ReadsInBlocks (donorLab (1 : Label.{u}) ⊤) := by
  intro t o ho
  fin_cases t
  · have h1 : o = 1 := by
      have h : ((1 : Ordinal.{u}) : Label.{u}) = (o : Label.{u}) := by simpa [donorLab] using ho
      exact (WithTop.coe_injective (WithBot.coe_injective h)).symm
    subst h1
    refine ⟨by simp [reference, Ordinal.div_eq_zero_of_lt one_lt_omega0], ?_⟩
    rw [Ordinal.mod_eq_of_lt one_lt_omega0]
    exact Nat.one_le_cast.mpr (by decide)
  · exact absurd ho (by simp [donorLab])

private theorem one_ne_top : (1 : Label.{u}) ≠ ⊤ := by
  rw [← WithBot.coe_one, ← WithTop.coe_one]
  exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne

/-- **The capped-donor lemma at this input**: every active lawful labelling of the private type
reads the donor `1, ⊤` lawfully. -/
theorem isLawful_reading {v : Fin 5 → Label.{u}} (hv : rows.IsLawful v)
    (hact : reference.IsActive v) : donorRows.IsLawful (reference.reading v ∘ donorLab 1 ⊤) :=
  hasMargin.isLawful_reading hv hact isLawful_donorLab_one_top
    (fun _ ↦ by simp [donorCells, reference])
    readsInBlocks_donorLab

/-- **The reading at the actual labels** is the donor `1, ⊤` capped by the cut `2`: the
labelling `1, 2`. -/
theorem reading_lab_one_top_top :
    reference.reading (lab (1 : Label.{u}) ⊤ ⊤) ∘ donorLab 1 ⊤ = donorLab 1 2 := by
  have hcut : reference.cut (lab (1 : Label.{u}) ⊤ ⊤) = 2 := by
    rw [hasMargin.cut_eq]
    simp [reference]
  funext t
  fin_cases t
  · have := hasMargin.reading_eq_self (x := (1 : Label.{u}))
      (fun o ho ↦ readsInBlocks_donorLab 0 o (by simpa [donorLab] using ho)) one_ne_top
    simpa [donorLab] using this
  · simp [donorLab, hcut]

/-- **The labelling that drops `z₁` is inactive**: `⊥, ⊥, ⊥, ω + 1, ω + 2` is lawful and not
`⊥` at the cap, but `⊥` at the reference cell. -/
theorem not_isActive_lab_bot_omegaAdd :
    rows.IsLawful (lab ⊥ (omegaAdd 1) (omegaAdd 2)) ∧ lab ⊥ (omegaAdd 1) (omegaAdd 2) 4 ≠ ⊥ ∧
      ¬ reference.{u}.IsActive (lab ⊥ (omegaAdd 1) (omegaAdd 2)) :=
  ⟨isLawful_lab_bot_omegaAdd, omegaAdd_ne_bot 2, fun h ↦ h.2 0 (mem_singleton_self 0) rfl⟩

/-- **The reading never produces the bottom pattern of the donor's rows**: for every labelling
`v` of the private cells, if the reading is `⊥` at `e₁` then it is `⊥` at `e₂`.  A reading `⊥` at
`e₁` makes `v` or the cut `⊥` there, and `v (z₁) = ⊥` makes the cut `⊥`.  The donor's rows forbid
the opposite pattern in every lawful labelling (`eq_bot_of_isLawful_donor`). -/
theorem reading_eq_bot_of_reading_eq_bot (v : Fin 5 → Label.{u})
    (h : reference.reading v (donorLab 1 ⊤ 0) = ⊥) :
    reference.reading v (donorLab 1 ⊤ 1) = ⊥ := by
  have h1 : ((1 : Label.{u})) = ((ω * 0 + (1 : ℕ) : Ordinal.{u}) : Label.{u}) := by simp
  -- The donor labels are `1` and `⊤` (`donorLab`, by definition).
  change reference.reading v 1 = ⊥ at h
  -- The reading at `e₂`, labelled `⊤`, is the cut (`donorLab` and `reading`, by definition).
  change reference.cut v = ⊥
  rw [h1, PrivateReference.reading_omega0_mul_add, min_eq_bot, visibilityReplace_eq_bot_iff] at h
  rcases h with h | h
  · simp only [PrivateReference.cut, reference, sup_singleton] at h ⊢
    rw [h, visibilityReplace_bot, min_bot_right]
  · exact h

end AnchorInput

/-! ### The private type whose full cells lawful labellings order either way -/

namespace OppositeCellsInput

open GatedExtensionCounterexample

/-- **The reference data** at the private type `GatedExtensionCounterexample.P α`: the cap `3`
(one of the two full cells), the full grade `2`, and no block, since no cell of that type carries
an ordinal label. -/
def reference : PrivateReference.{u} (Fin 5) := ⟨3, 2, ∅, fun _ ↦ 3, fun _ ↦ 0⟩

/-- **The margin holds** (vacuously in its block clauses) at the actual labels `⊥, ⊥, ⊥, ⊤, ⊤` of
`P α`. -/
theorem hasMargin (α : Ordinal.{u}) : reference.{u}.HasMargin (P α).rows (P α).label where
  isLawful := (P α).isLawful
  mem_below x := by
    -- The cells of `P α` are those of `GatedExtensionCounterexample.cells` (`P`, by definition),
    -- and membership below the cap is the comparison of graded indices (`CellScheme.mem_below`).
    change cells.gradedIndex x ≤ cells.gradedIndex 3
    revert x; decide
  grade_cap := rfl
  off_lt b hb := absurd hb (Finset.notMem_empty b)
  label_ref b hb := absurd hb (Finset.notMem_empty b)
  margin b hb := absurd hb (Finset.notMem_empty b)

/-- With no block the cut is `⊥` for every labelling. -/
theorem cut_eq_bot (v : Fin 5 → Label.{u}) : reference.cut v = ⊥ := by
  simp [PrivateReference.cut, reference]

/-- **Both oppositely ordered labellings are active**: `⊤, 2` and `2, ⊤` at the full cells are
not `⊥` at the cap. -/
theorem isActive_labelling :
    reference.{u}.IsActive (labelling ⊤ ((2 : ℕ) : Label.{u})) ∧
      reference.{u}.IsActive (labelling ((2 : ℕ) : Label.{u}) ⊤) :=
  ⟨⟨by simp [reference, labelling], by simp [reference]⟩,
    ⟨by simp [reference, labelling], by simp [reference]⟩⟩

/-- A donor labelled only `⊥` and `⊤` reads in the (empty) blocks. -/
theorem readsInBlocks_of_bot_or_top {κ : Type*} {ℓ : κ → Label.{u}}
    (hℓ : ∀ t, ℓ t = ⊥ ∨ ℓ t = ⊤) : reference.{u}.ReadsInBlocks ℓ := by
  intro t o ho
  rcases hℓ t with h | h <;> rw [h] at ho <;> simp at ho

/-- **The capped-donor lemma at `P α`**: for both oppositely ordered lawful labellings
`⊤, 2` and `2, ⊤` of the full cells, the capped reading of every lawful donor labelling of grades
at most `2` labelled `⊥` and `⊤` is lawful.  The cut is `⊥` (`cut_eq_bot`): the readings are
constantly `⊥`. -/
theorem isLawful_reading {κ β : Type*} {E : CellScheme κ β} {Q : E.Rows.{u}}
    {ℓ : κ → Label.{u}} (hℓ : Q.IsLawful ℓ) (hK : ∀ t, E.grade t ≤ 2)
    (hbt : ∀ t, ℓ t = ⊥ ∨ ℓ t = ⊤) :
    Q.IsLawful (reference.reading (labelling ⊤ ((2 : ℕ) : Label.{u})) ∘ ℓ) ∧
      Q.IsLawful (reference.reading (labelling ((2 : ℕ) : Label.{u}) ⊤) ∘ ℓ) :=
  ⟨(hasMargin 0).isLawful_reading isLawful_labelling_top_two isActive_labelling.1 hℓ hK
      (readsInBlocks_of_bot_or_top hbt),
    (hasMargin 0).isLawful_reading isLawful_labelling_two_top isActive_labelling.2 hℓ hK
      (readsInBlocks_of_bot_or_top hbt)⟩

end OppositeCellsInput

/-! ### Two requested blocks -/

namespace TwoBlockInput

open CellScheme

/-- The point `ω * b + n` of the block `b`, as a label. -/
noncomputable def pt (b : Ordinal.{u}) (n : ℕ) : Label.{u} :=
  ((ω * b + n : Ordinal.{u}) : Label.{u})

/-- Points compare lexicographically in block and finite part. -/
theorem pt_le_pt_iff {a b : Ordinal.{u}} {m n : ℕ} : pt a m ≤ pt b n ↔ a < b ∨ a = b ∧ m ≤ n :=
  coe_omega0_mul_add_le_coe_iff

/-- A point is self-visible at `k` exactly when its finite part is at least `k`. -/
theorem isSelfVisible_pt {k n : ℕ} {b : Ordinal.{u}} : IsSelfVisible k (pt b n) ↔ k ≤ n := by
  rw [pt, isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- Visibility replacement of a point replaces its finite part. -/
theorem visibilityReplace_pt (k i n : ℕ) (b : Ordinal.{u}) :
    visibilityReplace k i (pt b n) = pt b (if n < k then i else n) := by
  rw [pt, pt, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

/-- A point is not `⊥`. -/
theorem pt_ne_bot (b : Ordinal.{u}) (n : ℕ) : pt b n ≠ ⊥ := WithBot.coe_ne_bot

/-- A point is not `⊤`. -/
theorem pt_ne_top (b : Ordinal.{u}) (n : ℕ) : pt b n ≠ ⊤ := fun h ↦
  WithTop.coe_ne_top (WithBot.coe_injective h)

/-- The three private cells, on two points: the reference cells `0` and `1` of grade `1`, and the
cap `2` of grade `2`, all of full scope. -/
def cells : CellScheme (Fin 3) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, ![1, 1, 2]⟩

/-- The row values: the cap reads the codes `1`, `ω + 1`, `ω + 3`; the cell `0` reads `1` at both
cells of grade `1`; the cell `1` reads `1`, `ω + 1`. -/
noncomputable def rowValue (s t : Fin 3) : Label.{u} :=
  if s = 2 then ![pt 0 1, pt 1 1, pt 1 3] t
  else if s = 0 then pt 0 1 else ![pt 0 1, pt 1 1, ⊥] t

/-- The rows of the private type. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The labelling `x, y, c` of the private cells. -/
noncomputable def lab (x y c : Label.{u}) : Fin 3 → Label.{u} := ![x, y, c]

/-- The labellings `lab x y c` are lawful once the three localities hold. -/
private theorem isLawful_lab_of {x y c : Label.{u}} (hx : IsSelfVisible 1 x)
    (hy : IsSelfVisible 1 y) (hc : IsSelfVisible 2 c)
    (h0 : TransformsTo (fun d : cells.below (cells.gradedIndex 0) ↦ cells.grade d) (rows.row 0)
      (fun d ↦ min (lab x y c d) x))
    (h1 : TransformsTo (fun d : cells.below (cells.gradedIndex 1) ↦ cells.grade d) (rows.row 1)
      (fun d ↦ min (lab x y c d) y))
    (h2 : TransformsTo (fun d : cells.below (cells.gradedIndex 2) ↦ cells.grade d) (rows.row 2)
      (fun d ↦ min (lab x y c d) c)) : rows.{u}.IsLawful (lab x y c) where
  orderly d := by
    fin_cases d
    exacts [hx, hy, hc]
  locality s := by
    fin_cases s
    exacts [h0, h1, h2]
  availability s _ _ hg := ⟨s, Prod.ext rfl hg, le_rfl⟩

/-- A locality of the private type from a witness, checked cell by cell. -/
private theorem transformsTo_of (s : Fin 3) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {F : Fin 3 → Label.{u}}
    (h : ∀ d : Fin 3, cells.gradedIndex d ≤ cells.gradedIndex s →
      F d = min (σ (rowValue s d)) (g (cells.grade d))) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.row s)
      (fun d ↦ F d) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

private theorem pt01_le_pt11 : pt.{u} 0 1 ≤ pt 1 1 := pt_le_pt_iff.mpr (.inl zero_lt_one)

private theorem pt02_le_pt11 : pt.{u} 0 2 ≤ pt 1 1 := pt_le_pt_iff.mpr (.inl zero_lt_one)

private theorem pt01_le_pt02 : pt.{u} 0 1 ≤ pt 0 2 := pt_le_pt_iff.mpr (.inr ⟨rfl, by omega⟩)

/-- The locality at the reference cell `0`, labelled `1`. -/
private theorem locality_zero (c : Label.{u}) :
    TransformsTo (fun d : cells.below (cells.gradedIndex 0) ↦ cells.grade d) (rows.row 0)
      (fun d ↦ min (lab (pt 0 1) (pt 1 1) c d) (pt 0 1)) := by
  refine transformsTo_of 0 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
  fin_cases d
  · simp [lab, rowValue]
  · simp [lab, rowValue, min_eq_right pt01_le_pt11]
  · exact absurd hd (by decide)

/-- The locality at the reference cell `1`, labelled `ω + 1`. -/
private theorem locality_one (c : Label.{u}) :
    TransformsTo (fun d : cells.below (cells.gradedIndex 1) ↦ cells.grade d) (rows.row 1)
      (fun d ↦ min (lab (pt 0 1) (pt 1 1) c d) (pt 1 1)) := by
  refine transformsTo_of 1 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
  fin_cases d
  · simp [lab, rowValue, min_eq_left pt01_le_pt11]
  · simp [lab, rowValue]
  · exact absurd hd (by decide)

/-- **The actual labels** `1, ω + 1, ⊤` are lawful: the codes at `ω + 3` and above raised to `⊤`. -/
theorem isLawful_lab_top : rows.{u}.IsLawful (lab (pt 0 1) (pt 1 1) ⊤) := by
  have hraise : IsWitness (stepSuppressor.{u} 2) (raise (pt 1 3)) :=
    isWitness_raise (isSelfVisible_pt.mpr le_rfl) (bot_lt_iff_ne_bot.mpr (pt_ne_bot 1 3))
  have h1 : ¬ pt.{u} 1 3 ≤ pt 0 1 := fun h ↦ by
    rcases pt_le_pt_iff.mp h with h | ⟨h, -⟩
    · exact absurd h (not_lt.mpr zero_le_one)
    · exact one_ne_zero h
  have h2 : ¬ pt.{u} 1 3 ≤ pt 1 1 := fun h ↦ by
    rcases pt_le_pt_iff.mp h with h | ⟨-, h⟩
    · exact lt_irrefl _ h
    · omega
  refine isLawful_lab_of (isSelfVisible_pt.mpr le_rfl) (isSelfVisible_pt.mpr le_rfl)
    (isSelfVisible_top 2) (locality_zero ⊤) (locality_one ⊤) ?_
  refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) hraise fun d _ ↦ ?_
  fin_cases d <;> simp [lab, rowValue, cells, raise, h1, h2]

/-- **An active lawful labelling with a lower cut**: `1, ω + 1, 2`, the codes read by the block
piece that keeps the block `[0, ω)` with finite parts capped at `2` and sends every higher block
to `2`. -/
theorem isLawful_lab_two : rows.{u}.IsLawful (lab (pt 0 1) (pt 1 1) (pt 0 2)) := by
  refine isLawful_lab_of (isSelfVisible_pt.mpr le_rfl) (isSelfVisible_pt.mpr le_rfl)
    (isSelfVisible_pt.mpr le_rfl) (locality_zero _) (locality_one _) ?_
  have hp1 : piece 2 0 0 (pt.{u} 0 1) = pt 0 1 := piece_omega0_mul_add (by omega) 0 0
  have hp2 (n : ℕ) : piece 2 0 0 (pt.{u} 1 n) = pt 0 2 :=
    piece_omega0_mul_add_of_lt zero_lt_one 0 n
  refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) (isWitness_piece 2 0 0)
    fun d _ ↦ ?_
  fin_cases d <;> simp [lab, rowValue, cells, hp1, hp2, min_eq_left pt01_le_pt02,
    min_eq_right pt02_le_pt11]

/-! The donor `1, ω + 1` on one point. -/

/-- The donor cells: two cells of graded index `(univ, 1)` on one point. -/
def donorCells : CellScheme (Fin 2) (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The donor row values: the row of `e₁ = 0` reads `1, 1`, the row of `e₂ = 1` reads
`1, ω + 1`, in two blocks. -/
noncomputable def donorRowValue (s t : Fin 2) : Label.{u} :=
  if s = 0 then pt 0 1 else ![pt 0 1, pt 1 1] t

/-- The rows of the donor. -/
noncomputable def donorRows : donorCells.Rows.{u} := ⟨fun s t ↦ donorRowValue s t.1⟩

/-- The labelling `x₀, x₁` of the donor cells. -/
noncomputable def donorLab (x₀ x₁ : Label.{u}) : Fin 2 → Label.{u} := ![x₀, x₁]

/-- **The donor labelling** `1, ω + 1` is lawful: each row is read by the identity. -/
theorem isLawful_donorLab : donorRows.{u}.IsLawful (donorLab (pt 0 1) (pt 1 1)) where
  orderly d := by fin_cases d <;> exact isSelfVisible_pt.mpr le_rfl
  locality s := by
    refine ⟨_, _, IsWitness.id_top, fun d ↦ ?_⟩
    obtain ⟨d, -⟩ := d
    fin_cases s <;> fin_cases d <;>
      simp [donorLab, donorRows, donorRowValue, min_eq_left pt01_le_pt11,
        min_eq_right pt01_le_pt11]
  availability s _ _ _ := ⟨s, rfl, le_rfl⟩

/-! The reference data and the readings. -/

/-- **The reference data**: the cap `2`, the full grade `2`, the blocks `[0, ω)` and `[ω, ω * 2)`
with the reference cells `0` and `1`, both labelled with finite part `1`. -/
noncomputable def reference : PrivateReference.{u} (Fin 3) :=
  ⟨2, 2, {0, 1}, fun b ↦ if b = 0 then 0 else 1, fun _ ↦ 1⟩

private theorem ref_zero : reference.{u}.ref 0 = 0 := by simp [reference]

private theorem ref_one : reference.{u}.ref 1 = 1 := by simp [reference]

private theorem lab_zero (x y c : Label.{u}) : lab x y c 0 = x := rfl

private theorem lab_one (x y c : Label.{u}) : lab x y c 1 = y := rfl

/-- The capped reading at a point. -/
private theorem reading_pt (v : Fin 3 → Label.{u}) (b : Ordinal.{u}) (n : ℕ) :
    reference.reading v (pt b n) =
      min (visibilityReplace reference.{u}.fullGrade n (v (reference.ref b))) (reference.cut v) :=
  reference.reading_omega0_mul_add b n

/-- **The margin holds** at the actual labels `1, ω + 1, ⊤`. -/
theorem hasMargin : reference.{u}.HasMargin rows (lab (pt 0 1) (pt 1 1) ⊤) where
  isLawful := isLawful_lab_top
  mem_below x := by
    -- Membership below the cap is the comparison of graded indices (`CellScheme.mem_below`).
    change cells.gradedIndex x ≤ cells.gradedIndex 2
    revert x; decide
  grade_cap := rfl
  off_lt _ _ := Nat.one_lt_two
  label_ref b hb := by
    rcases mem_insert.mp hb with rfl | hb
    · rw [ref_zero]; rfl
    · rw [mem_singleton.mp hb, ref_one]; rfl
  margin _ _ := le_top

/-- The donor `1, ω + 1` reads in the two blocks. -/
theorem readsInBlocks_donorLab : reference.{u}.ReadsInBlocks (donorLab (pt 0 1) (pt 1 1)) := by
  intro t o ho
  have key (b : Ordinal.{u}) (hb : b ∈ reference.{u}.blocks) (h : pt b 1 = (o : Label.{u})) :
      o / ω ∈ reference.{u}.blocks ∧ o % ω ≤ reference.{u}.fullGrade := by
    obtain rfl := WithTop.coe_injective (WithBot.coe_injective h)
    rw [omega0_mul_add_natCast_div, omega0_mul_add_natCast_mod]
    exact ⟨hb, Nat.cast_le.mpr Nat.one_lt_two.le⟩
  fin_cases t
  · exact key 0 (by simp [reference]) ho
  · exact key 1 (by simp [reference]) ho

/-- **The capped-donor lemma at two blocks**: every active lawful labelling of the private type
reads the donor `1, ω + 1` lawfully. -/
theorem isLawful_reading {v : Fin 3 → Label.{u}} (hv : rows.IsLawful v)
    (hact : reference.IsActive v) :
    donorRows.IsLawful (reference.reading v ∘ donorLab (pt 0 1) (pt 1 1)) :=
  hasMargin.isLawful_reading hv hact isLawful_donorLab (fun _ ↦ Nat.one_lt_two.le)
    readsInBlocks_donorLab

/-- **The reading at the actual labels** is the donor `1, ω + 1` itself. -/
theorem reading_actual : reference.reading (lab (pt 0 1) (pt 1 1) ⊤) ∘
    donorLab (pt 0 1) (pt 1 1) = donorLab.{u} (pt 0 1) (pt 1 1) := by
  funext t
  refine hasMargin.reading_eq_self (readsInBlocks_donorLab t) ?_
  fin_cases t
  exacts [pt_ne_top 0 1, pt_ne_top 1 1]

/-- The labelling `1, ω + 1, 2` is active. -/
theorem isActive_lab_two : reference.{u}.IsActive (lab (pt 0 1) (pt 1 1) (pt 0 2)) := by
  have h (i : Fin 3) : lab (pt.{u} 0 1) (pt 1 1) (pt 0 2) i ≠ ⊥ := by
    fin_cases i
    exacts [pt_ne_bot 0 1, pt_ne_bot 1 1, pt_ne_bot 0 2]
  exact ⟨h _, fun _ _ ↦ h _⟩

/-- **The cut of `1, ω + 1, 2` is `2`**: the replacement `2` of the first reference label is
already the label of the cap. -/
theorem cut_lab_two : reference.cut (lab (pt 0 1) (pt 1 1) (pt 0 2)) = pt.{u} 0 2 := by
  refine le_antisymm (min_le_left _ _) (le_min le_rfl (le_sup_of_le (b := 0) (by
    simp [reference]) ?_))
  rw [ref_zero, lab_zero, visibilityReplace_pt]
  exact le_rfl

/-- **The reading of `1, ω + 1, 2`** is the donor labelling `1, 2`: the first donor label is read
through its reference cell below the cut, the second is capped by the cut `2`. -/
theorem reading_lab_two : reference.reading (lab (pt 0 1) (pt 1 1) (pt 0 2)) ∘
    donorLab (pt 0 1) (pt 1 1) = donorLab.{u} (pt 0 1) (pt 0 2) := by
  funext t
  fin_cases t
  · -- The first donor label is `pt 0 1` (`donorLab`, by definition).
    change reference.reading _ (pt 0 1) = pt 0 1
    rw [reading_pt, cut_lab_two, ref_zero, lab_zero, visibilityReplace_pt]
    exact min_eq_left pt01_le_pt02
  · -- The second donor label is `pt 1 1` (`donorLab`, by definition).
    change reference.reading _ (pt 1 1) = pt 0 2
    rw [reading_pt, cut_lab_two, ref_one, lab_one, visibilityReplace_pt]
    exact min_eq_right pt02_le_pt11

/-- **A lawful reading that is neither the donor nor `⊥`**: the reading `1, 2` of the active
labelling `1, ω + 1, 2` is lawful for the donor's rows (`isLawful_reading`), and not `⊥` at either
donor cell. -/
theorem isLawful_donorLab_one_two : donorRows.IsLawful (donorLab (pt 0 1) (pt.{u} 0 2)) ∧
    ∀ t, donorLab (pt 0 1) (pt.{u} 0 2) t ≠ ⊥ := by
  refine ⟨reading_lab_two ▸ isLawful_reading isLawful_lab_two isActive_lab_two, fun t ↦ ?_⟩
  fin_cases t
  exacts [pt_ne_bot 0 1, pt_ne_bot 0 2]

end TwoBlockInput

end CappedDonorReading

end VaughtConjecture

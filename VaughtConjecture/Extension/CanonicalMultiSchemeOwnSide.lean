/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalMultiScheme
import VaughtConjecture.Extension.OrderedLayerObstruction
import VaughtConjecture.Extension.Coding
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Own-side copy rows, and the orientations forced on the copies

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: a
choice of copy rows for the canonical multi-layer scheme defined for every seed, and a necessary
condition that every step of the scheme meets); semantic contract, items 2–4.

Let `I` be a seed on five points with coatoms `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}`.  The
canonical multi-layer scheme `canonicalMultiScheme I R`
(`VaughtConjecture.Extension.CanonicalMultiScheme`) has, at each `(univ, k + 1)`, a copy of the
original at `(C, k + 1)` and a copy of the original at `(D, k + 1)`, the `i`-th copy reading every
cell through its base by the copy rows `R k i`.

**The own-side rows** (`OrderedLayer.ownSideRows I`).  The copy of `(B, k + 1)`, `B` its coatom
(`copyCoatom i`) and `B'` the other coatom, reads

* a cell `d` below `(B, k + 1)` (its own side, the common face included) as its original reads `d`
  in the amalgam, shifted into a higher block: `blockShift N x = ω · N + x` for an ordinal `x`, `⊥`
  and `⊤` fixed (`Label.blockShift`);
* a cell `d` below `(B', k + 1)` and not below `(B, k + 1)` (the other side) as the original of the
  other copy of its grade reads `d`, unshifted;
* every other cell at `⊥`.

Here `N = rowBound I` is a number with every row value of the amalgam below `ω · N`
(`OrderedLayer.exists_rowBound`, from the coding of the rows), so every value read on the own side,
other than `⊥`, is above every value read on the other side (`OrderedLayer.ownSideRows_lt`), and
the values stay below `ω ^ 2` (`Label.blockShift_lt_omega0_sq`).  The rows depend only on the
amalgam, that is, on the two coatom types.  **The own-side step** (`Seed.OwnSideStep I`) is the
multi-layer step of the canonical multi-layer scheme with these rows; it gives a step of the
family (`Seed.OwnSideStep.hasCanonicalMultiStep`).

**Comparison with the rows of the crossed-coupling seed.**  The copy rows `CanonicalHG.rowsHG` of
`seedHG` read, at `(univ, 1)`, the parameter of the own coatom at `ω + 2` and the other's at `1`:
own side above, the orientation of the own-side rows at the grade `1`, which read the own
parameter at `ω · N + 1` instead (`OrderedLayer.ownSideRows_zero_lt_of_TH`,
`OrderedLayer.CanonicalHG.rowsHG_zero_lt`); the two rows share the orientation there, not the
values.  At `(univ, 2)` and `(univ, 3)` the rows `rowsHG` read both copies alike, oriented toward
`C` at the grade `2` and toward `D` at the grade `3`; the own-side rows do not, and that is where
they fail at `seedHG` (below).

**The orientations forced on the copies** (`Seed.MultiLayerStep.copyRows_lt_of_forcesTop`, for
every copy rows `R`).  Let `P` be lawful below `(B, k)`, `B` the coatom of the copy `(j, i)` with
`j + 1 ≤ k`, prescribing `⊤` at its original, let `P` force `⊤` (`Seed.ForcesTop`) at a cell `d₂`
below `(B', j + 1)`, and let `d₁` be a cell below `(B, j + 1)` with `P d₁ ≠ ⊤` and grade at most
that of `d₂`.  Then every step of the family with copy rows `R` has `R j i d₁ < R j i d₂`: the
capped lift of `P` into `(univ, k)` is `⊤` at `d₂` by the forcing, `⊤` at the copy by forcedness
(`OrderedLayer.eq_copyOrig_of_isLawfulBelow`), and locality at the copy excludes reading `d₂` at
most `d₁`.  This is the argument of the forced separation
(`CompletionBelowFullGrade.exists_separating_of_forcesTop`), at a copy of any grade instead of a
cell reached by availability; it is a necessary condition on the copy rows of every step, not a
refutation of the family.

**Where the own-side rows fail** (`Seed.not_ownSideStep_of_forcesTop`).  Under such a forcing the
own-side rows read the own cell `d₁` above the other side's cell `d₂`, when `P d₁ ≠ ⊥` (then the
original reads `d₁` at a value other than `⊥`, by locality of `P` at it) and `d₂` is not below the
coatom of the copy, against the forced orientation.  So a seed with such a forcing and a cell `d₁`
with `P d₁ ∉ {⊥, ⊤}` (and `d₂` off the own side) has no own-side step; with `P d₁ = ⊥` the own-side
rows may read `d₁` at `⊥`, below `d₂`.  The instances `seedHG`, `seedL` and `seedLM` are in
`VaughtConjecture.Extension.CanonicalMultiSchemeOwnSideExamples`.  This refutes the own-side rows,
not the family and not a completion.

**The direction of the shift, and the mirror rows.**  The direction here is a choice.  The rows
first specified for this checkpoint were the *mirror rows*: the copy reads its own coatom's cells
at their own values and the other coatom's cells shifted into a higher block.  The direction was
reversed here to match `rowsHG` at the grade `1` (own side above, as above).  The necessary
condition always concludes that the own cell `d₁` is read below the other side's cell `d₂`, so
through a cell `d₂` off the own side that the other original reads at a value other than `⊥` it
can refute only rows with the own side above, never the mirror rows (argued, not formalized):
under the mirror rows `d₁` is read below `ω · N` and such a `d₂` at least `ω · N`.  At `seedHG`,
`seedL` and `seedLM` this holds at `({3}, 1)` and `({4}, 1)`, so the mirror rows meet every
orientation compiled there (argued, not formalized); at the grade `1` of `seedHG` they also give
the two copies opposite orientations.  The condition also allows `d₂` on the common face
(`Seed.MultiLayerStep.copyRows_lt_of_forcesTop` does not place `d₂` off the own side); there the
mirror rows read both cells unshifted, as the own original does, so it is a condition on that
original's row, which this argument does not exclude.  Whether the mirror rows give a step is the
next test.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope, several at one graded face); its rows are not those of that definition, and neither
printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture

open Finset CellScheme
open Ordinal hiding univ

namespace Label

/-- **Shifting into a higher block**: `⊥` and `⊤` are fixed, and an ordinal `x` goes to
`ω · N + x`, the same finite part in the block `N` places higher. -/
noncomputable def blockShift (N : ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun o ↦ ω * (N : Ordinal.{u}) + o)

/-- The block shift fixes `⊥`. -/
@[simp] theorem blockShift_bot (N : ℕ) : blockShift N (⊥ : Label.{u}) = ⊥ := rfl

/-- The block shift of an ordinal. -/
theorem blockShift_coe (N : ℕ) (o : Ordinal.{u}) :
    blockShift N (o : Label.{u}) = ((ω * (N : Ordinal.{u}) + o : Ordinal.{u}) : Label.{u}) := rfl

/-- **A shifted label other than `⊥` is at least `ω · N`.** -/
theorem le_blockShift {N : ℕ} {x : Label.{u}} (hx : x ≠ ⊥) :
    ((ω * (N : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ blockShift N x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | coe o =>
    rw [blockShift_coe]
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
  | top => exact le_top

/-- **The block shift keeps coded labels coded**: below `ω ^ 2`. -/
theorem blockShift_lt_omega0_sq {N : ℕ} {x : Label.{u}}
    (hx : x < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) :
    blockShift N x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases lt_omega0_sq_iff.mp hx with rfl | ⟨i, j, rfl⟩
  · exact hx
  · rw [blockShift_coe]
    refine lt_omega0_sq_iff.mpr (.inr ⟨N + i, j, ?_⟩)
    rw [← add_assoc, ← mul_add, Nat.cast_add]

/-- A coded label lies below `ω · N` for every large `N`. -/
theorem eventually_lt_omega0_mul {x : Label.{u}} (hx : x < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) :
    ∀ᶠ N : ℕ in Filter.atTop, x < ((ω * (N : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  rcases lt_omega0_sq_iff.mp hx with rfl | ⟨i, j, rfl⟩
  · exact Filter.Eventually.of_forall fun _ ↦ WithBot.bot_lt_coe _
  · refine Filter.eventually_atTop.mpr ⟨i + 1, fun N hN ↦ ?_⟩
    refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
    calc ω * (i : Ordinal.{u}) + j < ω * i + ω :=
        (add_lt_add_iff_left _).mpr (natCast_lt_omega0 j)
      _ = ω * ((i + 1 : ℕ) : Ordinal.{u}) := by rw [Nat.cast_succ, mul_add_one]
      _ ≤ ω * N := by gcongr

end Label

namespace OrderedLayer

open Label

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-! ### The own-side rows -/

/-- **A bound on the blocks of the rows of the amalgam**: some `N` has every row value below
`ω · N`, since the rows are coded and there are finitely many cells. -/
theorem exists_rowBound : ∃ N : ℕ, ∀ s (t : I.amalgam.toCellScheme.below
    (I.amalgam.toCellScheme.gradedIndex s)),
      I.amalgam.rows.row s t < ((ω * (N : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) :=
  (Filter.eventually_all.mpr fun s ↦ Filter.eventually_all.mpr fun t ↦
    eventually_lt_omega0_mul (I.amalgam.isCoded s t)).exists

/-- The bound on the blocks of the rows of the amalgam used by the own-side rows. -/
noncomputable def rowBound : ℕ := (exists_rowBound I).choose

/-- Every row value of the amalgam is below `ω · rowBound I`. -/
theorem row_lt_rowBound (s : Fin I.amalgam.card)
    (t : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    I.amalgam.rows.row s t < ((ω * (rowBound I : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) :=
  (exists_rowBound I).choose_spec s t

/-- The coatom of the first copy is `C`. -/
@[simp] theorem copyCoatom_zero : copyCoatom 0 = coatomC := rfl

/-- The coatom of the second copy is `D`. -/
@[simp] theorem copyCoatom_one : copyCoatom 1 = coatomD := rfl

variable {I}

/-- A cell below `(copyCoatom i, k + 1)` is below the original of the copy `(k, i)`. -/
theorem mem_below_copyOrig {k : Fin 4} {i : Fin 2} {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (copyCoatom i, (k : ℕ) + 1)) :
    d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex (copyOrig I k i)) := by
  rw [gradedIndex_copyOrig]; exact hd

variable (I) in
open Classical in
/-- **The own-side rows**: the copy `(k, i)` reads a cell below its own coatom at the grade `k + 1`
as its original does, shifted into the block `rowBound I`; a cell below the other coatom only as
the original of the other copy of its grade does; every other cell at `⊥`. -/
noncomputable def ownSideRows : CopyRows I := fun k i d ↦
  if hd : d ∈ I.amalgam.toCellScheme.below (copyCoatom i, (k : ℕ) + 1) then
    blockShift (rowBound I) (I.amalgam.rows.row (copyOrig I k i) ⟨d, mem_below_copyOrig hd⟩)
  else if hd' : d ∈ I.amalgam.toCellScheme.below (copyCoatom i.rev, (k : ℕ) + 1) then
    I.amalgam.rows.row (copyOrig I k i.rev) ⟨d, mem_below_copyOrig hd'⟩
  else ⊥

/-- On its own side, the copy reads as its original, shifted. -/
theorem ownSideRows_of_mem {k : Fin 4} {i : Fin 2} {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (copyCoatom i, (k : ℕ) + 1)) :
    ownSideRows I k i d =
      blockShift (rowBound I) (I.amalgam.rows.row (copyOrig I k i) ⟨d, mem_below_copyOrig hd⟩) :=
  dite_eq_left hd

/-- Off its own side, the copy reads below `ω · rowBound I`. -/
theorem ownSideRows_lt_of_not_mem {k : Fin 4} {i : Fin 2} {d : Fin I.amalgam.card}
    (hd : d ∉ I.amalgam.toCellScheme.below (copyCoatom i, (k : ℕ) + 1)) :
    ownSideRows I k i d < ((ω * (rowBound I : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  rw [ownSideRows, dite_eq_right hd]
  split_ifs with hd'
  · exact row_lt_rowBound I _ _
  · exact WithBot.bot_lt_coe _

/-- **Own side above**: the copy `(k, i)` reads a cell `e` off its own side strictly below a cell
`d` on its own side, when its original reads `d` at a value other than `⊥`. -/
theorem ownSideRows_lt {k : Fin 4} {i : Fin 2} {d e : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (copyCoatom i, (k : ℕ) + 1))
    (he : e ∉ I.amalgam.toCellScheme.below (copyCoatom i, (k : ℕ) + 1))
    (hne : ∀ h, I.amalgam.rows.row (copyOrig I k i) ⟨d, h⟩ ≠ ⊥) :
    ownSideRows I k i e < ownSideRows I k i d := by
  rw [ownSideRows_of_mem hd]
  exact (ownSideRows_lt_of_not_mem he).trans_le (le_blockShift (hne _))

/-- The own-side rows are coded. -/
theorem ownSideRows_lt_omega0_sq (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card) :
    ownSideRows I k i d < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  unfold ownSideRows
  split_ifs
  · exact blockShift_lt_omega0_sq (I.amalgam.isCoded _ _)
  · exact I.amalgam.isCoded _ _
  · exact WithBot.bot_lt_coe _

/-- **A row read at a value other than `⊥`**: if `P` is lawful below `X`, the cell `s` lies below
`X`, and `min (P d) (P s) ≠ ⊥` at a cell `d` below `s`, the row of `s` reads `d` at a value other
than `⊥` (locality at `s`). -/
theorem row_ne_bot_of_isLawfulBelow {X : Finset (Fin 5) × ℕ} {P : Fin I.amalgam.card → Label.{u}}
    (hP : I.amalgam.rows.IsLawfulBelow X fun d ↦ P d) {s d : Fin I.amalgam.card}
    (hs : s ∈ I.amalgam.toCellScheme.below X) (hPd : min (P d) (P s) ≠ ⊥)
    (h : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    I.amalgam.rows.row s ⟨d, h⟩ ≠ ⊥ := by
  intro hbot
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hP
  exact hPd ((hloc s hs).eq_bot (d := ⟨d, h⟩) hbot)

end OrderedLayer

namespace Seed

open Label OrderedLayer

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- **The own-side step**: the multi-layer step of the canonical multi-layer scheme with the
own-side rows. -/
def OwnSideStep : Prop := I.MultiLayerStep canonicalMult (canonicalRows I (ownSideRows I))

variable {I}

/-- The own-side step is a step of the canonical multi-layer scheme. -/
theorem OwnSideStep.hasCanonicalMultiStep (h : I.OwnSideStep) : I.HasCanonicalMultiStep :=
  ⟨ownSideRows I, h⟩

/-- A multi-layer step lifts capped from each full coatom graded face `(copyCoatom i, k)` into
`(univ, k)`. -/
theorem MultiLayerStep.cappedLift_copyCoatom {M : Fin 4 → ℕ} {r : MultiRows I M}
    (h : I.MultiLayerStep M r) (i : Fin 2) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (multiLayerScheme I M r).rows.CappedLift (X := (copyCoatom i, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ := by
  have key : ∀ B : Finset (Fin 5), B = coatomC ∨ B = coatomD →
      (multiLayerScheme I M r).rows.CappedLift (X := (B, k))
        (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ := by
    rintro B (rfl | rfl)
    exacts [h.cappedLift_left k hk1 hk4, h.cappedLift_right k hk1 hk4]
  exact key _ (copyCoatom_eq i)

/-- **The orientation forced on a copy.**  Let `P` be lawful below `(B, k)`, `B` the coatom of the
copy `(j, i)` with `j + 1 ≤ k ≤ 4`, with `P` equal to `⊤` at the original of the copy, and let
`P` force `⊤` at a cell `d₂` below the other coatom at the grade `j + 1`.  If `d₁` is a cell below
`(B, j + 1)` with `P d₁ ≠ ⊤` and grade at most that of `d₂`, every step of the canonical
multi-layer scheme with copy rows `R` has the copy read `d₁` strictly below `d₂`.

The capped lift at the cap `⊥` from `(B, k)` into `(univ, k)` of `P` read through the bases is
`⊤` at `d₂` (the forcing) and at the copy (forcedness: the copy carries its original's label), and
locality at the copy with `P d₁ < ⊤` excludes reading `d₂` at most `d₁`. -/
theorem MultiLayerStep.copyRows_lt_of_forcesTop {R : CopyRows I}
    (h : I.MultiLayerStep canonicalMult (canonicalRows I R)) {j : Fin 4} {i : Fin 2} {k : ℕ}
    (hjk : (j : ℕ) + 1 ≤ k) (hk4 : k ≤ 4) {P : Fin I.amalgam.card → Label.{u}}
    (hP : I.amalgam.rows.IsLawfulBelow (copyCoatom i, k) fun d ↦ P d)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (copyCoatom i, (j : ℕ) + 1))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (copyCoatom i.rev, (j : ℕ) + 1))
    (hg : I.amalgam.toCellScheme.grade d₁ ≤ I.amalgam.toCellScheme.grade d₂)
    (hP₁ : P d₁ ≠ ⊤) (hPo : P (copyOrig I j i) = ⊤)
    (hforce : I.ForcesTop (copyCoatom i, k) (copyCoatom i.rev, k) P d₂) :
    R j i d₁ < R j i d₂ := by
  classical
  -- Step 0: the pairs `X = (B, k)` and `Y = (univ, k)`.
  have hXY : ((copyCoatom i, k) : Finset (Fin 5) × ℕ) ≤ ((univ : Finset (Fin 5)), k) :=
    ⟨subset_univ _, le_rfl⟩
  have hk1 : 1 ≤ k := by omega
  -- Step 1: the prescription read through the bases is lawful below `X`.
  set w₀ : Fin (canonicalMultiScheme I R).card → Label.{u} := fun z ↦ P (copyBase I z) with hw₀
  have hw₀X : (canonicalMultiScheme I R).rows.IsLawfulBelow (copyCoatom i, k) fun z ↦ w₀ z := by
    refine (isLawfulBelow_multiOldCell_iff (copyCoatom_ne_univ i)).mpr ?_
    simpa only [hw₀, copyBase_multiOldCell] using hP
  -- Step 2: the capped lift at the cap `⊥` with the ambient `⊥`, extended by `⊥`.
  obtain ⟨x', hx'law, -, hx'p⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (h.cappedLift_copyCoatom i hk1 hk4) ⊥ (isSelfVisible_bot _) (fun z ↦ w₀ z) (fun _ ↦ ⊥)
    hw₀X (Rows.isLawfulBelow_const_bot _) fun _ ↦ by simp
  set x := Rows.extendBot ((univ : Finset (Fin 5)), k) x' with hx_def
  have hx : (canonicalMultiScheme I R).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ x z :=
    Rows.isLawfulBelow_extendBot.mpr hx'law
  have hxX (z : Fin (canonicalMultiScheme I R).card)
      (hz : z ∈ (canonicalMultiScheme I R).toCellScheme.below (copyCoatom i, k)) :
      x z = w₀ z := by
    rw [hx_def,
      Rows.extendBot_of_mem x' ((canonicalMultiScheme I R).toCellScheme.below_mono hXY hz)]
    exact hx'p ⟨z, hz⟩
  have hold (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (copyCoatom i, k)) :
      x (multiOldCell I canonicalMult d) = P d := by
    rw [hxX _ (multiOldCell_mem_below hd)]
    simp only [hw₀, copyBase_multiOldCell]
  -- Step 3: on the other coatom the lift is lawful and equals `P` on the common cells; the
  -- forcing gives `⊤` at `d₂`.
  have hx₂ : x (multiOldCell I canonicalMult d₂) = ⊤ :=
    hforce (fun d ↦ x (multiOldCell I canonicalMult d))
      (isLawfulBelow_coatom_of_isLawfulBelow_univ R hx (copyCoatom_ne_univ i.rev))
      fun d hd _ ↦ hold d hd
  have hmono : I.amalgam.toCellScheme.below (copyCoatom i, (j : ℕ) + 1) ⊆
      I.amalgam.toCellScheme.below (copyCoatom i, k) :=
    I.amalgam.toCellScheme.below_mono ⟨subset_rfl, hjk⟩
  have hx₁ : x (multiOldCell I canonicalMult d₁) = P d₁ := hold d₁ (hmono hd₁)
  -- Step 4: forcedness: the copy carries the label `⊤` of its original.
  have horig : copyOrig I j i ∈ I.amalgam.toCellScheme.below (copyCoatom i, k) := by
    rw [CellScheme.mem_below, gradedIndex_copyOrig]; exact ⟨subset_rfl, hjk⟩
  have hxκ : x (multiNewCell I canonicalMult j i) = ⊤ := by
    rw [eq_copyOrig_of_isLawfulBelow R hx hjk i, hold _ horig, hPo]
  -- Step 5: locality at the copy: reading `d₂` at most `d₁` would give `⊤ ≤ P d₁`.
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  have hκ : multiNewCell I canonicalMult j i ∈
      (canonicalMultiScheme I R).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
    multiNewCell_mem_below (r := canonicalRows I R) i hjk
  -- The cells below the copy, and the row of the copy at an old cell.
  set U := (canonicalMultiScheme I R).toCellScheme.below
    ((canonicalMultiScheme I R).toCellScheme.gradedIndex (multiNewCell I canonicalMult j i))
    with hU
  have hmem (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ (j : ℕ) + 1) :
      multiOldCell I canonicalMult d ∈ U := by
    rw [hU, gradedIndex_multiNewCell]
    exact multiOldCell_mem_below ⟨subset_univ _, hd⟩
  have h₁ := hmem d₁ hd₁.2
  have h₂ := hmem d₂ hd₂.2
  by_contra hcon
  rw [not_lt] at hcon
  have hrow (d : Fin I.amalgam.card) (hd : multiOldCell I canonicalMult d ∈ U) :
      (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult j i) ⟨_, hd⟩ =
        R j i d := by
    rw [row_canonical, copyBase_multiOldCell]
  have h21 := (hloc _ hκ).le_of_le (d := ⟨_, h₂⟩) (d' := ⟨_, h₁⟩)
    (by rw [hrow, hrow]; exact hcon)
    ((grade_multiOldCell (r := canonicalRows I R) d₁).trans_le
      (hg.trans_eq (grade_multiOldCell d₂).symm))
  simp only at h21
  rw [hx₂, hx₁, hxκ, min_top_right, min_top_right] at h21
  exact hP₁ (top_le_iff.mp h21)

/-- **Own-side rows fail under a forcing from the own coatom.**  Under the hypotheses of
`Seed.MultiLayerStep.copyRows_lt_of_forcesTop`, with `P d₁ ≠ ⊥` and `d₂` off the own side of the
copy, the seed has no own-side step: the own-side rows read the own cell `d₁` above `d₂` (its
original reads `d₁` at a value other than `⊥`, by locality of `P` at the original), against the
orientation forced on the copy. -/
theorem not_ownSideStep_of_forcesTop {j : Fin 4} {i : Fin 2} {k : ℕ} (hjk : (j : ℕ) + 1 ≤ k)
    (hk4 : k ≤ 4) {P : Fin I.amalgam.card → Label.{u}}
    (hP : I.amalgam.rows.IsLawfulBelow (copyCoatom i, k) fun d ↦ P d)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (copyCoatom i, (j : ℕ) + 1))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (copyCoatom i.rev, (j : ℕ) + 1))
    (hd₂' : d₂ ∉ I.amalgam.toCellScheme.below (copyCoatom i, (j : ℕ) + 1))
    (hg : I.amalgam.toCellScheme.grade d₁ ≤ I.amalgam.toCellScheme.grade d₂)
    (hP₁ : P d₁ ≠ ⊤) (hP₁' : P d₁ ≠ ⊥) (hPo : P (copyOrig I j i) = ⊤)
    (hforce : I.ForcesTop (copyCoatom i, k) (copyCoatom i.rev, k) P d₂) : ¬ I.OwnSideStep := by
  intro h
  have horig : copyOrig I j i ∈ I.amalgam.toCellScheme.below (copyCoatom i, k) := by
    rw [CellScheme.mem_below, gradedIndex_copyOrig]; exact ⟨subset_rfl, hjk⟩
  exact lt_asymm (h.copyRows_lt_of_forcesTop hjk hk4 hP hd₁ hd₂ hg hP₁ hPo hforce)
    (ownSideRows_lt hd₁ hd₂'
      (row_ne_bot_of_isLawfulBelow hP horig (by rw [hPo, min_top_right]; exact hP₁')))

end Seed

end VaughtConjecture

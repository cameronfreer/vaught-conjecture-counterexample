/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Extension.Encoders

/-!
# The flattened source

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (owner alignment: the source section of an owner,
short at the grade of the owner); semantic contract, item 3.

The owner alignment of the completion aligns a lawful prescription `p` below the graded index of
an owner `o` of grade `m` with a lawful **coded source section** `s` below `o`, which must be
**short at `m`** (`Label.IsShort m`: every finite part at most `m`) and never the formal top.  The
normal forms are not short: the codes of the strongly coded encoder `strongEncode V m` are
**strongly coded at `m`** (finite parts at most `m + 1`, `Label.IsStronglyCoded m`), and a label
whose finite part exceeds `m` gets the finite part `m + 1` (the code of `3` at grade `1`,
`VaughtConjecture.Extension.TransformationExamples`).
Strongly coded at `m` and short at `m` are different conditions; this file produces the second
from the first by flattening.

**The flattened source** (`Label.flattenedSource V m w`) of a labelling `w` with values in a
finite set `V` of labels is `flatten m ∘ (strongEncode V m ∘ w)`: the flattening of finite parts
at `m` (`Label.flatten`) of the normal form `strongEncode V m ∘ w`, which is strongly coded at `m`.

* **Lawful** (`CellScheme.Rows.IsLawful.flattenedSource`,
  `CellScheme.Rows.IsLawfulBelow.flattenedSource`): flattening is a witness bounded by grade `m`
  (`Label.isWitness_flatten`, from `Label.isWitness_comp_flatten`) that sends only bottom to bottom,
  so it maps the lawful normal form to a lawful section on the cells of grade at most `m`.
* **Short at `m`, strongly coded at `m`, never the formal top** (`Label.isShort_flattenedSource`,
  `Label.isStronglyCoded_flattenedSource`, `Label.flattenedSource_ne_top`).
* **Read literally by the decoder** (`Label.strongDecode_flattenedSource`):
  `strongDecode V m (flattenedSource V m w d) = w d` whenever `w d ∈ V`.

**Non-merging.**  Flattening is not injective: `flatten m` identifies the finite parts `≥ m` of a
block.  It merges no two labels that the decoder separates: for a coding grade `K ≤ m`,
`strongDecode V K ∘ flatten m = strongDecode V K` (`Label.strongDecode_flatten`, so
`Label.strongDecode_eq_of_flatten_eq`).  The block decoding keeps finite parts and commutes with
flattening (`Label.blockDecode_flatten`), and unspreading at `K` reads a finite part only up to
`K` on the blocks of the labels of finite part `≤ K` and not at all on the blocks of their own
that spreading gives to the other labels (`Label.unspread_flatten`).  So the flattened codes of
the labels of `V` are distinct (`Label.injOn_flatten_strongEncode`).  The hypothesis `K ≤ m` is
necessary: for `K > m` flattening at `m` merges the finite parts `m, …, K` of one value block,
which unspreading at `K` separates (`Label.strongDecode_flatten_strongEncode_eq`; the code of `2` at
`K = 2`, flattened at `m = 1`, decodes to `1`, `VaughtConjecture.Extension.FlatteningExamples`).
The decoder must be the decoder of the encoder: an arbitrary strongly coded normal form with an
arbitrary decoder bounded by `m` (as in `CellScheme.Rows.IsLawful.exists_stronglyCoded`) may be
merged by flattening (the identity decoder of the label `2` at grade `1`, in the same file).

**The flattening step preserves the prescribed face and every cap.**  Through the encoder's own
decoder, the flattened source of a labelling `w` reads what `w` reads, cell by cell: the
prescription `min p (p o)` below `(C, j + 1)` literally
(`CellScheme.Rows.strongDecode_flattenedSource_inclusion`), and the observation at every cap `c`
at every cell (`CellScheme.Rows.min_strongDecode_flattenedSource`).  These are statements about
the flattening step and the decoder `strongDecode V m`, not about the decoder `ρ` of the owner
alignment.  For `ρ`, the reading capped at a cap `γ` transfers from the agreement of `ρ` with the
capped decoder on the labels short at `m`, at every cell that carries a flattened code
(`Label.min_apply_flattenedSource_of_agree`).  The transfer holds at the cap `γ`; it is
the ambient condition of the lift only when `γ` is the cap `c` of the lift.  The reading above
`γ`, up to the owner label, is the content of the alignment itself.

**The source of the alignment** (`CellScheme.Rows.IsLawfulBelow.flattenedSource_prescription`).
For a prescription `p` lawful below a pair `X` with values in `V`, its flattened source at the
grade of `X` is lawful below `X`, short at that grade, strongly coded there, never the formal top,
read literally by `strongDecode V X.2`, and decoded to `min p γ` by a witness `τ` bounded by that
grade with values at most `γ`, for every cap `γ` self-visible at that grade
(`Label.exists_isWitness_flattenedSource`).

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Witnesses are [Kni26, Definition 2.3.9]; the range normalization of rows below `ω ^ 2` is that of
[Kni26, Lemma 2.5.13], and the strong coding, flattening, and literal reading of the codes are
proved in this library.
-/

universe u

namespace VaughtConjecture.Label

open Finset Ordinal

variable {V : Finset Label.{u}} {K m : ℕ} {x y γ : Label.{u}}

/-! ### Flattening -/

/-- The flattened finite part is finite. -/
private theorem min_mod_lt_omega0 (m : ℕ) (o : Ordinal.{u}) : min (o % ω) (m : Ordinal.{u}) < ω :=
  (min_le_left _ _).trans_lt (mod_lt _ omega0_ne_zero)

/-- The block of a flattened ordinal. -/
private theorem flattenOrd_div (m : ℕ) (o : Ordinal.{u}) : flattenOrd m o / ω = o / ω := by
  rw [flattenOrd, omega0_mul_add_div (min_mod_lt_omega0 m o)]

/-- The finite part of a flattened ordinal. -/
private theorem flattenOrd_mod (m : ℕ) (o : Ordinal.{u}) :
    flattenOrd m o % ω = min (o % ω) (m : Ordinal.{u}) := by
  rw [flattenOrd, omega0_mul_add_mod (min_mod_lt_omega0 m o)]

/-- **Flattening of finite parts at `m` is a witness bounded by grade `m`**, sending only bottom
to bottom.  It makes the flattened source of a lawful section lawful
(`CellScheme.Rows.IsLawful.flattenedSource`). -/
theorem isWitness_flatten (m : ℕ) : IsWitness (stepSuppressor.{u} m) (flatten m) :=
  isWitness_comp_flatten (f := id) rfl monotone_id fun _ _ _ _ _ ↦ rfl

/-- **Every flattened label is short at `m`.** -/
theorem isShort_flatten (m : ℕ) (x : Label.{u}) : IsShort m (flatten m x) := by
  induction x using recBotCoeTop with
  | bot => exact isShort_bot m
  | top => exact isShort_top m
  | coe o => rw [flatten_coe, isShort_coe, flattenOrd_mod]; exact min_le_right _ _

/-- Flattening sends a label to the formal top only if it is the formal top. -/
@[simp] theorem flatten_eq_top_iff : flatten m x = ⊤ ↔ x = ⊤ := by
  induction x using recBotCoeTop <;> simp

/-- Flattening keeps strong coding at every grade `k`: it keeps the block and lowers the finite
part. -/
theorem IsStronglyCoded.flatten {k : ℕ} (h : IsStronglyCoded k x) (m : ℕ) :
    IsStronglyCoded k (Label.flatten m x) := by
  induction x using recBotCoeTop with
  | bot => exact isStronglyCoded_bot k
  | top => exact absurd h (not_isStronglyCoded_top k)
  | coe o =>
    obtain ⟨ho, hk⟩ := isStronglyCoded_coe.mp h
    rw [flatten_coe, isStronglyCoded_coe, flattenOrd_mod]
    refine ⟨lt_of_le_of_lt ?_ ho, (min_le_left _ _).trans hk⟩
    calc flattenOrd m o = ω * (o / ω) + min (o % ω) (m : Ordinal.{u}) := rfl
      _ ≤ ω * (o / ω) + o % ω := add_le_add_right (min_le_left _ _) _
      _ = o := div_add_mod o ω

/-- The block decoding keeps finite parts, so it commutes with flattening. -/
theorem blockDecode_flatten (V : Finset Label.{u}) (m : ℕ) (z : Label.{u}) :
    blockDecode V (flatten m z) = flatten m (blockDecode V z) := by
  induction z using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    rw [flatten_coe, blockDecode_coe, blockDecode_coe]
    by_cases hex : ∃ i : Fin #(codeBlocks V), o / ω = ((i + 1 : ℕ) : Ordinal.{u})
    · obtain ⟨i, hi⟩ := hex
      rw [blockDecodeOrd_of_eq i ((flattenOrd_div m o).trans hi), blockDecodeOrd_of_eq i hi,
        flatten_coe, flattenOrd_mod]
      rw [flattenOrd, omega0_mul_add_div (mod_lt _ omega0_ne_zero),
        omega0_mul_add_mod (mod_lt _ omega0_ne_zero)]
    · have hex' : ¬ ∃ i : Fin #(codeBlocks V), flattenOrd m o / ω = ((i + 1 : ℕ) : Ordinal.{u}) :=
        by rwa [flattenOrd_div]
      by_cases h0 : o / ω = 0
      · rw [blockDecodeOrd_of_eq_zero h0, blockDecodeOrd_of_eq_zero ((flattenOrd_div m o).trans h0)]
        rfl
      · rw [blockDecodeOrd, dite_eq_right hex', ite_eq_right (by rwa [flattenOrd_div]),
          blockDecodeOrd, dite_eq_right hex, ite_eq_right h0]
        rfl

/-- **Unspreading at `K` ignores flattening at every `m ≥ K`**: on the blocks of the labels of
finite part `≤ K` it reads the finite part only up to `K`, and on the other blocks not at all. -/
theorem unspread_flatten (hKm : K ≤ m) (z : Label.{u}) :
    unspread K (flatten m z) = unspread K z := by
  induction z using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    rw [flatten_coe, unspread_coe, unspread_coe, unspreadOrd, unspreadOrd, flattenOrd_div,
      flattenOrd_mod, min_assoc,
      min_eq_right (show (K : Ordinal.{u}) ≤ m by exact_mod_cast hKm)]

/-- **The decoder factors through flattening** at every `m` at least the coding grade `K`. -/
theorem strongDecode_flatten (hKm : K ≤ m) (z : Label.{u}) :
    strongDecode V K (flatten m z) = strongDecode V K z := by
  rw [strongDecode_apply, strongDecode_apply, blockDecode_flatten, unspread_flatten hKm]

/-- **Non-merging for the encoder's own decoder.**  For a coding grade `K ≤ m`, flattening at
`m` identifies only labels that `strongDecode V K` identifies.  It is specific to this decoder:
another witness bounded by the grade may separate labels that flattening merges (the identity
decoder in `VaughtConjecture.Extension.FlatteningExamples`). -/
theorem strongDecode_eq_of_flatten_eq (hKm : K ≤ m) (h : flatten m x = flatten m y) :
    strongDecode V K x = strongDecode V K y := by
  rw [← strongDecode_flatten hKm x, h, strongDecode_flatten hKm y]

/-- The decoded flattened code of a label of `V`, at every coding grade `K` and every flattening
grade `m`: unspreading at `K` of the flattened spread label.  For `K ≤ m` it is the label
(`strongDecode_flatten_strongEncode`); for `K > m` it may differ
(`VaughtConjecture.Extension.FlatteningExamples`). -/
theorem strongDecode_flatten_strongEncode_eq {z : Label.{u}} (hz : z ∈ V) :
    strongDecode V K (flatten m (strongEncode V K z)) = unspread K (flatten m (spread K z)) := by
  rw [strongDecode_apply, blockDecode_flatten, strongEncode_apply,
    blockDecode_blockEncode (mem_image_of_mem _ hz)]

/-- **The decoder reads the flattened codes of the labels of `V` literally**, for `K ≤ m`. -/
theorem strongDecode_flatten_strongEncode (hKm : K ≤ m) {z : Label.{u}} (hz : z ∈ V) :
    strongDecode V K (flatten m (strongEncode V K z)) = z := by
  rw [strongDecode_flatten hKm, strongDecode_strongEncode hz]

/-- **The flattened codes of the labels of `V` are distinct**, for `K ≤ m`. -/
theorem injOn_flatten_strongEncode (hKm : K ≤ m) :
    Set.InjOn (flatten m ∘ strongEncode V K) V := fun _ hx _ hy h ↦ by
  rw [← strongDecode_flatten_strongEncode hKm hx, ← strongDecode_flatten_strongEncode hKm hy]
  exact congrArg _ h

/-- The decoder reads a flattened code of a label of `V` as bottom only if the code is bottom,
for `K ≤ m`: the decoded label is the label itself.  So the decoder sends no non-bottom value of a
labelling of flattened codes to bottom (`CellScheme.Rows.IsLawful.map_of_apply_eq_bot`). -/
theorem eq_bot_of_strongDecode_flatten_strongEncode_eq_bot (hKm : K ≤ m) {x : Label.{u}}
    (hx : x ∈ V) (h : strongDecode V K (flatten m (strongEncode V K x)) = ⊥) :
    flatten m (strongEncode V K x) = ⊥ := by
  rw [strongDecode_flatten_strongEncode hKm hx] at h
  rw [h, strongEncode_eq_bot_iff.mpr rfl, flatten_bot]

/-- **Capping a witness bounded by grade `m`** at a label `γ` self-visible at `m` gives a witness
bounded by grade `m` with values at most `γ`.  It gives the capped decoder of the flattened source
(`exists_isWitness_flattenedSource`). -/
theorem IsWitness.min_const {σ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor m) σ)
    (hγ : IsSelfVisible m γ) : IsWitness (stepSuppressor.{u} m) fun x ↦ min (σ x) γ where
  antitone := hσ.antitone
  isSelfVisible := hσ.isSelfVisible
  map_bot := by simp [hσ.map_bot]
  monotone _ _ h := min_le_min_right _ (hσ.monotone h)
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ m
    · rw [hσ.visibilityReplace_comm x k (by simp [hk]) i hi,
        visibilityReplace_min_of_isSelfVisible hi (hγ.mono hk)]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, min_eq_bot] at hx
      rcases hx with hx | hx
      · rw [hσ.apply_visibilityReplace_eq_bot hx k hi, hx, min_eq_left bot_le,
          visibilityReplace_bot]
      · rw [hx, min_eq_right bot_le, min_eq_right bot_le, visibilityReplace_bot]

/-! ### The flattened source -/

variable {ι : Type*} {w : ι → Label.{u}}

/-- The **flattened source** of a labelling `w` relative to a finite set `V` of labels at the grade
`m` (the grade of an owner): the flattening of finite parts at `m` of the normal form
`strongEncode V m ∘ w`.  The normal form is strongly coded at `m`; the flattened source is short at
`m` and never the formal top, and the decoder `strongDecode V m` reads it literally on the labels
of `V`. -/
noncomputable def flattenedSource (V : Finset Label.{u}) (m : ℕ) (w : ι → Label.{u}) :
    ι → Label.{u} :=
  flatten m ∘ (strongEncode V m ∘ w)

/-- The flattened source, applied. -/
theorem flattenedSource_apply (d : ι) :
    flattenedSource V m w d = flatten m (strongEncode V m (w d)) := rfl

/-- **The flattened source is short at `m`.** -/
theorem isShort_flattenedSource (d : ι) : IsShort m (flattenedSource V m w d) :=
  isShort_flatten m _

/-- **The flattened source is strongly coded at `m`**, as the normal form is. -/
theorem isStronglyCoded_flattenedSource (d : ι) : IsStronglyCoded m (flattenedSource V m w d) :=
  (isStronglyCoded_strongEncode _).flatten m

/-- **The flattened source is never the formal top**: no code of the encoder is. -/
theorem flattenedSource_ne_top (d : ι) : flattenedSource V m w d ≠ ⊤ := by
  rw [flattenedSource_apply, Ne, flatten_eq_top_iff]
  exact fun h ↦ not_isStronglyCoded_top m (h ▸ isStronglyCoded_strongEncode (V := V) (w d))

/-- **The decoder reads the flattened source literally** at every cell whose label lies in `V`. -/
theorem strongDecode_flattenedSource {d : ι} (hd : w d ∈ V) :
    strongDecode V m (flattenedSource V m w d) = w d :=
  strongDecode_flatten_strongEncode le_rfl hd

/-- **The flattened source is bottom exactly where the labelling is**: encoding and flattening
send only bottom to bottom.  So an owner label above a positive cap has a code above bottom. -/
@[simp] theorem flattenedSource_eq_bot_iff {d : ι} : flattenedSource V m w d = ⊥ ↔ w d = ⊥ := by
  rw [flattenedSource_apply, flatten_eq_bot_iff, strongEncode_eq_bot_iff]

/-- **Agreement with the decoder on short labels reads the flattened source.**  If a value map
`ρ` agrees with the decoder `strongDecode V m` capped at `γ` at every label short at `m`, then
`ρ` reads `w` capped at `γ` at every cell whose label lies in `V`.  The hypothesis is the last
conclusion of the owner-local alignment with the capped decoder
`τ := fun z ↦ min (strongDecode V m z) γ` of `exists_isWitness_flattenedSource`, since
`min (τ z) γ = min (strongDecode V m z) γ`; so the decoder `ρ` of the alignment keeps the
observation at the cap `γ` at every cell that carries a flattened code.  This is the
ambient condition of the lift only when `γ` is the cap `c` of the lift. -/
theorem min_apply_flattenedSource_of_agree {ρ : Label.{u} → Label.{u}}
    (hagree : ∀ z, IsShort m z → min (ρ z) γ = min (strongDecode V m z) γ) {d : ι}
    (hd : w d ∈ V) : min (ρ (flattenedSource V m w d)) γ = min (w d) γ := by
  rw [hagree _ (isShort_flattenedSource d), strongDecode_flattenedSource hd]

/-- **The capped decoder of the flattened source.**  For a cap `γ` self-visible at `m`, some
witness `τ` bounded by grade `m`, with values at most `γ`, decodes the flattened source of `w`
to `w` capped at `γ` at every cell whose label lies in `V`.  These are the source hypotheses of
the owner-local alignment: a witness `τ` bounded by the grade of the owner, `τ ≤ γ`,
`τ ∘ s = min w γ`, on a source `s` short at that grade and never the formal top. -/
theorem exists_isWitness_flattenedSource (hγ : IsSelfVisible m γ) :
    ∃ τ, IsWitness (stepSuppressor.{u} m) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ d, w d ∈ V → τ (flattenedSource V m w d) = min (w d) γ :=
  ⟨_, isWitness_strongDecode.min_const hγ, fun _ ↦ min_le_right _ _,
    fun _ hd ↦ by rw [strongDecode_flattenedSource hd]⟩

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {V : Finset Label.{u}} {m : ℕ}

/-- **The flattened source of a lawful section is lawful** on cells of grade at most `m`: the
normal form is lawful, and flattening is a witness bounded by grade `m` that sends only bottom to
bottom. -/
theorem IsLawful.flattenedSource {w : ι → Label.{u}} (hw : R.IsLawful w)
    (hm : ∀ d, D.grade d ≤ m) : R.IsLawful (Label.flattenedSource V m w) :=
  (hw.strongEncode hm).map_of_bot_reflecting hm (isWitness_flatten m)
    fun _ ↦ flatten_eq_bot_iff.mp

/-- **The flattened source of a labelling lawful below a pair `X` is lawful below `X`**, at every
grade `m` at least that of `X`. -/
theorem IsLawfulBelow.flattenedSource {X : Finset α × ℕ} {w : D.below X → Label.{u}}
    (hw : R.IsLawfulBelow X w) (hm : X.2 ≤ m) :
    R.IsLawfulBelow X (Label.flattenedSource V m w) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hw).flattenedSource fun d ↦ d.2.2.trans hm)

variable {C B : Finset α} {j : ℕ}

/-- **The flattening step keeps the prescribed face literally.**  If a labelling `w` below
`(B, j + 1)` reads `min p (p o)` below `(C, j + 1)`, with values there in `V`, the decoder
`strongDecode V (j + 1)` reads `min p (p o)` from its flattened source there; restoration
(`VaughtConjecture.Extension.Restoration`) then gives `p` itself.  It is a statement about the
flattening step and the encoder's own decoder, not about the decoder of the owner alignment. -/
theorem strongDecode_flattenedSource_inclusion (hCB : C ⊆ B) {p : D.below (C, j + 1) → Label.{u}}
    {o : D.below (C, j + 1)} {w : D.below (B, j + 1) → Label.{u}}
    (hV : ∀ e, w (Set.inclusion (D.below_mono
      (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) e) ∈ V)
    (hread : ∀ e, w (Set.inclusion (D.below_mono
      (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) e) = min (p e) (p o))
    (e : D.below (C, j + 1)) :
    strongDecode V (j + 1) (Label.flattenedSource V (j + 1) w (Set.inclusion (D.below_mono
      (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) e)) =
      min (p e) (p o) := by
  rw [strongDecode_flattenedSource (hV e), hread]

/-- **The flattening step keeps the observation at every cap `c`** at every cell below the target
pair, the auxiliary cells (the new cells of full scope and the cells of the other coatom)
included, when read by the encoder's own decoder `strongDecode V m`. -/
theorem min_strongDecode_flattenedSource {Y : Finset α × ℕ} {w q : D.below Y → Label.{u}}
    {c : Label.{u}} (hV : ∀ d, w d ∈ V) (hamb : ∀ d, min (w d) c = min (q d) c)
    (d : D.below Y) : min (strongDecode V m (Label.flattenedSource V m w d)) c = min (q d) c := by
  rw [strongDecode_flattenedSource (hV d), hamb]

/-- **The flattened source of a prescription.**  Let `p` be lawful below a pair `X` (in the owner
alignment, the prescription below the graded index `(C, j + 1)` of an owner), with values in `V`.
Its flattened source `s` at the grade of `X` is a coded source section for the owner-local
alignment: lawful below `X`, short at the grade of `X`, strongly coded there, never the formal
top, bottom exactly where `p` is, read literally by `strongDecode V X.2`, and, at every cap `γ`
self-visible at the grade of `X`, decoded to `min p γ` by a witness `τ` bounded by that grade with
values at most `γ`. -/
theorem IsLawfulBelow.flattenedSource_prescription {X : Finset α × ℕ}
    {p : D.below X → Label.{u}} (hp : R.IsLawfulBelow X p) (hV : ∀ e, p e ∈ V) :
    R.IsLawfulBelow X (Label.flattenedSource V X.2 p) ∧
      (∀ e, IsShort X.2 (Label.flattenedSource V X.2 p e)) ∧
      (∀ e, Label.IsStronglyCoded X.2 (Label.flattenedSource V X.2 p e)) ∧
      (∀ e, Label.flattenedSource V X.2 p e ≠ ⊤) ∧
      (∀ e, Label.flattenedSource V X.2 p e = ⊥ ↔ p e = ⊥) ∧
      strongDecode V X.2 ∘ Label.flattenedSource V X.2 p = p ∧
      ∀ γ, IsSelfVisible X.2 γ → ∃ τ, IsWitness (stepSuppressor.{u} X.2) τ ∧ (∀ x, τ x ≤ γ) ∧
        ∀ e, τ (Label.flattenedSource V X.2 p e) = min (p e) γ :=
  ⟨hp.flattenedSource le_rfl, isShort_flattenedSource, isStronglyCoded_flattenedSource,
    flattenedSource_ne_top, fun _ ↦ flattenedSource_eq_bot_iff,
    funext fun e ↦ strongDecode_flattenedSource (hV e), fun _ hγ ↦
      (exists_isWitness_flattenedSource hγ).imp fun _ ⟨hτ, hle, h⟩ ↦ ⟨hτ, hle, fun e ↦ h e (hV e)⟩⟩

end VaughtConjecture.CellScheme.Rows

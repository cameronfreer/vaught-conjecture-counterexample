/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OwnerAlignment

/-!
# The aligned encoding and its literal reading

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (the alignment of owners: an encoding of the
prescription below the owner, lawful under the alignment, that the alignment decoder reads
literally); Layer 1 (guarded composition retains its guards); semantic contract, item 3.

Let `s` and `p` be lawful labellings of the cells of a scheme of grades at most `m`, let `h` and `δ`
be labels self-visible at `m` with `h ≠ ⊥`, and suppose the **alignment**: every cell with
`δ < p d` has `h ≤ s d`.  (In the application `s` is the source below an owner `o`, `p` the
prescription capped at the owner label, and `h`, `δ` the source cap and the reading cap of the
owner-local alignment, `Label.exists_ownerAlignment`.)  Let `μ` be zero or a limit with `h < μ`,
and `V` a finite set of labels containing every value of `p` above `δ`.

* **Tail codes** (`Label.tailEncode μ V m`): a label `y` is coded by `μ + strongEncode V m y`, the
  translation by `μ` of its strongly coded code; the formal top has a proper code.  The **tail
  decoder** (`Label.tailDecode μ V m`) is bottom below `μ` and reads `x ≥ μ` as
  `strongDecode V m (x - μ)`; it is a witness bounded by grade `m`
  (`Label.isWitness_tailDecode`) and recovers every label of `V` other than bottom from its tail
  code (`Label.tailDecode_tailEncode`).
* **The aligned encoding** (`Label.alignedEncode μ V m h δ s p`): at a cell `d`,
  `max (min (s d) h) (highCode (p d))`, where `highCode` is bottom at the labels `≤ δ` and the tail
  code above `δ` (`Label.highCode`).  The cells with `p d ≤ δ` keep their source capped at `h`;
  the others carry the tail code of `p d`, which lies above `μ > h`.
  - It agrees with `s` capped at `h` at every cell (`Label.min_alignedEncode`), by the alignment.
  - It is lawful (`CellScheme.Rows.IsLawful.alignedEncode`): orderliness and availability come from
    `s` and `p`; at every cell `c` the locality is read off the capped witnesses of `s` and `p` at
    `c` by the map `x ↦ max (min (σs x) h) (highCode (σp x))`, which commutes with visibility
    replacement at the thresholds at most the grade of `c` but need not satisfy the guard above it;
    the guard is repaired with `s` as the lawful companion (`Label.TransformsTo.of_read`), since the
    aligned encoding is bottom exactly where `s` is.
  - It is never the formal top when `h` is not (`Label.alignedEncode_ne_top`).
* **The extended decoder** (`Label.alignedDecode μ V m ρ δ`): `x ↦ max (min (ρ x) δ) (tailDecode x)`
  for a witness `ρ` bounded by grade `m` (the alignment decoder).  It is a witness bounded by grade
  `m` (`Label.isWitness_alignedDecode`), and:
  - **literal reading** (`Label.alignedDecode_alignedEncode`): if `δ ≤ ρ h` and
    `min (p d) δ = min (ρ (s d)) δ` at a cell, it reads the aligned encoding as `p d` there, at the
    cells below `δ` through `ρ` and the others through the tail decoder;
  - **the cap observation transfers** (`Label.min_alignedDecode_eq`): for `γ ≤ δ ≤ ρ h`, two labels
    that agree capped at `h` are read by the extended decoder and by `ρ` as labels that agree capped
    at `γ`.  This is the cap observation at every cell whose code agrees with a short source value
    capped at `h`, whether or not that cell carries a flattened code.

**The package below an owner** (`CellScheme.Rows.IsLawfulBelow.exists_alignedEncoding`).  From the
data of the owner-local alignment it produces a source cap `h`, a decoder `ρ` bounded by the
grade, and a lawful labelling `f` of codes below the owner, never the formal top, agreeing with `s`
capped at `h`, read by `ρ` literally as `p` capped at the owner label, and such that `ρ` reads every
label that agrees capped at `h` with a short label `z` as `τ z` capped at `γ`.  These are the two
readings the flattening step of `VaughtConjecture.Extension.FlattenedSource` left to the alignment
decoder: the literal reading of the prescribed face above the cap `γ`, and the cap
observation at the cells that need not carry flattened codes.  In the one-grade step the package is
decoded to an owner-capped lift (`VaughtConjecture.Extension.OwnerCappedLift`).

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Witnesses are [Kni26, Definition 2.3.9] and visibility replacement is [Kni26, Definition 2.2.3];
lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal Order

variable {μ : Ordinal.{u}} {V : Finset Label.{u}} {m k i : ℕ} {h δ γ x y z : Label.{u}}
  {ρ σ : Label.{u} → Label.{u}} {g : ℕ → Label.{u}}

/-! ### Precomposition with a map commuting with every replacement -/

/-- **Precomposition with a map commuting with every replacement.**  If `σ` fixes bottom, is
monotone, and commutes with visibility replacement at every threshold and value `i ≤ k`, then
`ν ∘ σ` is a witness for every witness `ν` with the same suppressor.  It makes the tail decoder a
witness bounded by grade `m`. -/
theorem IsWitness.comp_of_commute {ν : Label.{u} → Label.{u}} (hν : IsWitness g ν)
    (hbot : σ ⊥ = ⊥) (hmono : Monotone σ)
    (hcomm : ∀ x k i, i ≤ k → σ (visibilityReplace k i x) = visibilityReplace k i (σ x)) :
    IsWitness g (ν ∘ σ) where
  antitone := hν.antitone
  isSelfVisible := hν.isSelfVisible
  map_bot := by simp [hbot, hν.map_bot]
  monotone := hν.monotone.comp hmono
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    rw [hcomm x k i hi, hν.visibilityReplace_comm _ k hx i hi]

/-! ### Tail codes -/

/-- Removal of the offset `μ`: bottom below `μ`, and `x - μ` at the labels `x ≥ μ` (the formal top
is fixed). -/
noncomputable def unshift (μ : Ordinal.{u}) (x : Label.{u}) : Label.{u} :=
  open Classical in if x < (μ : Label.{u}) then ⊥ else translate 0 μ x

/-- Below `μ` the removal of the offset is bottom. -/
theorem unshift_of_lt (hx : x < (μ : Label.{u})) : unshift μ x = ⊥ := ite_eq_left hx

/-- From `μ` on, the removal of the offset is translation from `μ` to `0`. -/
theorem unshift_of_le (hx : (μ : Label.{u}) ≤ x) : unshift μ x = translate 0 μ x :=
  ite_eq_right (not_lt.mpr hx)

/-- The removal of the offset is monotone. -/
theorem monotone_unshift (μ : Ordinal.{u}) : Monotone (unshift μ) := by
  intro x y hxy
  by_cases hx : x < (μ : Label.{u})
  · rw [unshift_of_lt hx]; exact bot_le
  · rw [unshift_of_le (not_lt.mp hx), unshift_of_le ((not_lt.mp hx).trans hxy)]
    exact monotone_translate 0 μ hxy

/-- At an offset `μ` that is zero or a limit, removal of the offset commutes with every visibility
replacement. -/
theorem unshift_visibilityReplace (hμ : IsSuccPrelimit μ) (k i : ℕ) (x : Label.{u}) :
    unshift μ (visibilityReplace k i x) = visibilityReplace k i (unshift μ x) := by
  by_cases hx : x < (μ : Label.{u})
  · rw [unshift_of_lt hx, unshift_of_lt ((visibilityReplace_lt_iff hμ).mpr hx),
      visibilityReplace_bot]
  · rw [unshift_of_le (not_lt.mp hx),
      unshift_of_le (not_lt.mp (mt (visibilityReplace_lt_iff hμ).mp hx)),
      translate_visibilityReplace (isSuccPrelimit_iff_omega0_dvd.mpr (dvd_zero ω)) hμ
        (not_lt.mp hx)]

/-- Removal of the offset undoes translation by it, at every label other than bottom. -/
theorem unshift_translate (hz : z ≠ ⊥) : unshift μ (translate μ 0 z) = z := by
  rw [unshift_of_le (coe_le_translate hz)]
  induction z using recBotCoeTop with
  | bot => exact absurd rfl hz
  | coe o => rw [translate_coe, translate_coe, Ordinal.sub_zero, Ordinal.add_sub_cancel, zero_add]
  | top => rfl

/-- The **tail code** of a label: the translation by `μ` of its strongly coded code. -/
noncomputable def tailEncode (μ : Ordinal.{u}) (V : Finset Label.{u}) (m : ℕ) (y : Label.{u}) :
    Label.{u} :=
  translate μ 0 (strongEncode V m y)

/-- The **tail decoder**: the strongly coded decoder after removal of the offset `μ`. -/
noncomputable def tailDecode (μ : Ordinal.{u}) (V : Finset Label.{u}) (m : ℕ) :
    Label.{u} → Label.{u} :=
  strongDecode V m ∘ unshift μ

/-- The tail code is monotone. -/
theorem monotone_tailEncode : Monotone (tailEncode μ V m) :=
  (monotone_translate μ 0).comp monotone_strongEncode

/-- A tail code is never the formal top. -/
theorem tailEncode_ne_top (y : Label.{u}) : tailEncode μ V m y ≠ ⊤ := by
  have h := isStronglyCoded_strongEncode (V := V) (K := m) y
  induction hy : strongEncode V m y using recBotCoeTop with
  | bot => simp [tailEncode, hy]
  | coe o =>
    rw [tailEncode, hy, translate_coe]
    exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
  | top => exact absurd (hy ▸ h) (not_isStronglyCoded_top m)

/-- The tail code of a label other than bottom is at least `μ`. -/
theorem coe_le_tailEncode (hy : y ≠ ⊥) : (μ : Label.{u}) ≤ tailEncode μ V m y :=
  coe_le_translate (by rwa [Ne, strongEncode_eq_bot_iff])

/-- **The tail decoder is a witness bounded by grade `m`**, at an offset `μ` that is zero or a
limit. -/
theorem isWitness_tailDecode (hμ : IsSuccPrelimit μ) :
    IsWitness (stepSuppressor.{u} m) (tailDecode μ V m) :=
  isWitness_strongDecode.comp_of_commute (unshift_of_lt (WithBot.bot_lt_coe _))
    (monotone_unshift μ) fun x k i _ ↦ unshift_visibilityReplace hμ k i x

/-- The tail decoder is bottom below `μ`. -/
theorem tailDecode_of_lt (hx : x < (μ : Label.{u})) : tailDecode μ V m x = ⊥ := by
  rw [tailDecode, Function.comp_apply, unshift_of_lt hx]
  exact (isWitness_strongDecode (K := m)).map_bot

/-- **The tail decoder reads tail codes literally**, at the labels of `V` other than bottom. -/
theorem tailDecode_tailEncode (hy : y ∈ V) (hyb : y ≠ ⊥) :
    tailDecode μ V m (tailEncode μ V m y) = y := by
  rw [tailDecode, Function.comp_apply, tailEncode,
    unshift_translate (by rwa [Ne, strongEncode_eq_bot_iff]), strongDecode_strongEncode hy]

/-! ### The high code and the aligned encoding -/

/-- The **high code** above `δ`: bottom at the labels `≤ δ`, the tail code above `δ`. -/
noncomputable def highCode (μ : Ordinal.{u}) (V : Finset Label.{u}) (m : ℕ) (δ y : Label.{u}) :
    Label.{u} :=
  open Classical in if y ≤ δ then ⊥ else tailEncode μ V m y

/-- At the labels at most `δ` the high code is bottom. -/
theorem highCode_of_le (hy : y ≤ δ) : highCode μ V m δ y = ⊥ := ite_eq_left hy

/-- Above `δ` the high code is the tail code. -/
theorem highCode_of_lt (hy : δ < y) : highCode μ V m δ y = tailEncode μ V m y :=
  ite_eq_right (not_le.mpr hy)

/-- The high code fixes bottom. -/
theorem highCode_bot : highCode μ V m δ ⊥ = ⊥ := highCode_of_le bot_le

/-- The high code is monotone. -/
theorem monotone_highCode : Monotone (highCode μ V m δ) := by
  intro y y' hyy
  by_cases hy : y ≤ δ
  · rw [highCode_of_le hy]; exact bot_le
  · rw [highCode_of_lt (not_le.mp hy), highCode_of_lt ((not_le.mp hy).trans_le hyy)]
    exact monotone_tailEncode hyy

/-- Above `δ` the high code is at least `μ`. -/
theorem coe_le_highCode (hy : δ < y) : (μ : Label.{u}) ≤ highCode μ V m δ y := by
  rw [highCode_of_lt hy]
  exact coe_le_tailEncode (ne_bot_of_gt hy)

/-- A label above a bound self-visible at `k` stays above it after visibility replacement at `k`
with any value `i ≤ k`. -/
theorem lt_visibilityReplace_of_lt (hi : i ≤ k) (hδ : IsSelfVisible k δ) (hy : δ < y) :
    δ < visibilityReplace k i y := by
  by_contra hle
  rw [not_lt] at hle
  have h := visibilityReplace_le_of_le le_rfl hδ hle
  rw [visibilityReplace_self_visibilityReplace hi] at h
  exact hy.not_ge ((le_visibilityReplace (by omega) y).trans h)

/-- Every label other than bottom is at least ordinal zero. -/
private theorem coe_zero_le (hx : x ≠ ⊥) : ((0 : Ordinal.{u}) : Label.{u}) ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | coe o => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (zero_le (a := o)))
  | top => exact le_top

/-- Ordinal zero is zero or a limit. -/
private theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal.{u}) :=
  isSuccPrelimit_iff_omega0_dvd.mpr (dvd_zero ω)

/-- **The tail code commutes with visibility replacement** at every threshold `k ≤ m`, at an
offset `μ` that is zero or a limit. -/
theorem tailEncode_visibilityReplace (hμ : IsSuccPrelimit μ) (hk : k ≤ m) (hi : i ≤ k)
    {y : Label.{u}} (hy : y ≠ ⊥) :
    tailEncode μ V m (visibilityReplace k i y) = visibilityReplace k i (tailEncode μ V m y) := by
  rw [tailEncode, tailEncode, isWitness_strongEncode.visibilityReplace_comm y k (by simp [hk]) i hi,
    translate_visibilityReplace hμ isSuccPrelimit_zero
      (coe_zero_le (by rwa [Ne, strongEncode_eq_bot_iff]))]

/-- **The high code commutes with visibility replacement** at every threshold `k ≤ m`, when `δ` is
self-visible at `m` and `μ` is zero or a limit. -/
theorem highCode_visibilityReplace (hμ : IsSuccPrelimit μ) (hδ : IsSelfVisible m δ) (hk : k ≤ m)
    (hi : i ≤ k) (y : Label.{u}) :
    highCode μ V m δ (visibilityReplace k i y) = visibilityReplace k i (highCode μ V m δ y) := by
  by_cases hy : y ≤ δ
  · rw [highCode_of_le hy, highCode_of_le (visibilityReplace_le_of_le hi (hδ.mono hk) hy),
      visibilityReplace_bot]
  · have hy' := not_le.mp hy
    rw [highCode_of_lt hy', highCode_of_lt (lt_visibilityReplace_of_lt hi (hδ.mono hk) hy'),
      tailEncode_visibilityReplace hμ hk hi (ne_bot_of_gt hy')]

/-- The **aligned encoding**: at a cell `d`, the source capped at `h`, joined with the high code of
the prescription above `δ`. -/
noncomputable def alignedEncode {ι : Type*} (μ : Ordinal.{u}) (V : Finset Label.{u}) (m : ℕ)
    (h δ : Label.{u}) (s p : ι → Label.{u}) (d : ι) : Label.{u} :=
  max (min (s d) h) (highCode μ V m δ (p d))

section Encoding

variable {ι : Type*} {s p : ι → Label.{u}} {d c : ι}

/-- At a cell whose prescription is at most `δ`, the aligned encoding is the source capped at
`h`. -/
theorem alignedEncode_of_le (hd : p d ≤ δ) : alignedEncode μ V m h δ s p d = min (s d) h := by
  rw [alignedEncode, highCode_of_le hd, max_bot_right]

/-- At a cell whose prescription exceeds `δ`, the aligned encoding is the tail code of the
prescription, when `h < μ`. -/
theorem alignedEncode_of_lt (hhμ : h < (μ : Label.{u})) (hd : δ < p d) :
    alignedEncode μ V m h δ s p d = tailEncode μ V m (p d) := by
  rw [alignedEncode, max_eq_right ((min_le_right _ _).trans (hhμ.le.trans (coe_le_highCode hd))),
    highCode_of_lt hd]

/-- **The aligned encoding agrees with the source capped at `h`**, under the alignment at the
cell. -/
theorem min_alignedEncode (hhμ : h < (μ : Label.{u})) (halign : δ < p d → h ≤ s d) :
    min (alignedEncode μ V m h δ s p d) h = min (s d) h := by
  by_cases hd : p d ≤ δ
  · rw [alignedEncode_of_le hd, min_assoc, min_self]
  · have hd' := not_le.mp hd
    rw [alignedEncode_of_lt hhμ hd', min_eq_right (hhμ.le.trans (coe_le_tailEncode
      (ne_bot_of_gt hd'))), min_eq_right (halign hd')]

/-- The aligned encoding is never the formal top when `h` is not. -/
theorem alignedEncode_ne_top (hh : h ≠ ⊤) : alignedEncode μ V m h δ s p d ≠ ⊤ := by
  rw [alignedEncode, Ne, max_eq_top, not_or]
  refine ⟨ne_top_of_le_ne_top hh (min_le_right _ _), ?_⟩
  by_cases hd : p d ≤ δ
  · rw [highCode_of_le hd]; exact bot_ne_top
  · rw [highCode_of_lt (not_le.mp hd)]; exact tailEncode_ne_top _

/-- **The read identity of the aligned encoding**: the capped values at two cells `d` and `c`
combine to the aligned encoding at `d` capped at its value at `c`, under the alignment at both
cells.  It is the reading of the locality of the aligned encoding. -/
theorem max_min_highCode_min (hhμ : h < (μ : Label.{u})) (halignd : δ < p d → h ≤ s d)
    (halignc : δ < p c → h ≤ s c) :
    max (min (min (s d) (s c)) h) (highCode μ V m δ (min (p d) (p c))) =
      min (alignedEncode μ V m h δ s p d) (alignedEncode μ V m h δ s p c) := by
  rw [monotone_highCode.map_min]
  by_cases hd : p d ≤ δ <;> by_cases hc : p c ≤ δ
  · rw [highCode_of_le hd, highCode_of_le hc, min_self, max_bot_right, alignedEncode_of_le hd,
      alignedEncode_of_le hc, min_min_min_comm, min_self]
  · have hc' := not_le.mp hc
    rw [highCode_of_le hd, min_bot_left, max_bot_right, alignedEncode_of_le hd,
      alignedEncode_of_lt hhμ hc', min_eq_left ((min_le_right _ _).trans
        (hhμ.le.trans (coe_le_tailEncode (ne_bot_of_gt hc')))), min_assoc,
      min_eq_right (halignc hc')]
  · have hd' := not_le.mp hd
    rw [highCode_of_le hc, min_bot_right, max_bot_right, alignedEncode_of_lt hhμ hd',
      alignedEncode_of_le hc, min_eq_right ((min_le_right _ _).trans
        (hhμ.le.trans (coe_le_tailEncode (ne_bot_of_gt hd')))), min_comm (s d) (s c), min_assoc,
      min_eq_right (halignd hd')]
  · have hd' := not_le.mp hd
    have hc' := not_le.mp hc
    rw [alignedEncode_of_lt hhμ hd', alignedEncode_of_lt hhμ hc', highCode_of_lt hd',
      highCode_of_lt hc']
    exact max_eq_right ((min_le_right _ _).trans (hhμ.le.trans (le_min
      (coe_le_tailEncode (ne_bot_of_gt hd')) (coe_le_tailEncode (ne_bot_of_gt hc')))))

end Encoding

/-! ### The extended decoder -/

/-- The **extended decoder** of an alignment decoder `ρ`: `ρ` capped at `δ`, joined with the tail
decoder. -/
noncomputable def alignedDecode (μ : Ordinal.{u}) (V : Finset Label.{u}) (m : ℕ)
    (ρ : Label.{u} → Label.{u}) (δ x : Label.{u}) : Label.{u} :=
  max (min (ρ x) δ) (tailDecode μ V m x)

/-- **The extended decoder is a witness bounded by grade `m`**, for a witness `ρ` bounded by grade
`m`, `δ` self-visible at `m`, and `μ` zero or a limit. -/
theorem isWitness_alignedDecode (hμ : IsSuccPrelimit μ) (hρ : IsWitness (stepSuppressor m) ρ)
    (hδ : IsSelfVisible m δ) : IsWitness (stepSuppressor.{u} m) (alignedDecode μ V m ρ δ) :=
  (hρ.min_const hδ).max (isWitness_tailDecode hμ)

/-- Below `μ` the extended decoder is `ρ` capped at `δ`. -/
theorem alignedDecode_of_lt (hx : x < (μ : Label.{u})) :
    alignedDecode μ V m ρ δ x = min (ρ x) δ := by
  rw [alignedDecode, tailDecode_of_lt hx, max_bot_right]

/-- **Literal reading of the aligned encoding.**  If `ρ` is monotone, `δ ≤ ρ h`, `h < μ`,
`min (p d) δ = min (ρ (s d)) δ`, and `p d ∈ V` when `p d > δ`, the extended decoder reads the
aligned encoding at `d` as `p d`. -/
theorem alignedDecode_alignedEncode {ι : Type*} {s p : ι → Label.{u}} {d : ι}
    (hρ : Monotone ρ) (hhμ : h < (μ : Label.{u})) (hδρ : δ ≤ ρ h)
    (hread : min (p d) δ = min (ρ (s d)) δ) (hV : δ < p d → p d ∈ V) :
    alignedDecode μ V m ρ δ (alignedEncode μ V m h δ s p d) = p d := by
  by_cases hd : p d ≤ δ
  · rw [alignedEncode_of_le hd, alignedDecode_of_lt ((min_le_right _ _).trans_lt hhμ),
      hρ.map_min, min_assoc, min_eq_right hδρ, ← hread, min_eq_left hd]
  · have hd' := not_le.mp hd
    rw [alignedEncode_of_lt hhμ hd', alignedDecode,
      tailDecode_tailEncode (hV hd') (ne_bot_of_gt hd')]
    exact max_eq_right ((min_le_right _ _).trans hd'.le)

/-- **The cap observation transfers through the extended decoder.**  For a monotone `ρ`,
`γ ≤ δ ≤ ρ h`, and `h < μ`, two labels `x` and `y` that agree capped at `h` satisfy
`min (alignedDecode x) γ = min (ρ y) γ`. -/
theorem min_alignedDecode_eq (hρ : Monotone ρ) (hγδ : γ ≤ δ) (hδρ : δ ≤ ρ h)
    (hhμ : h < (μ : Label.{u})) (hxy : min x h = min y h) :
    min (alignedDecode μ V m ρ δ x) γ = min (ρ y) γ := by
  by_cases hx : x < h
  · have hyx : y = x := by
      rw [min_eq_left hx.le] at hxy
      by_contra hne
      rcases lt_or_ge y h with hy | hy
      · rw [min_eq_left hy.le] at hxy
        exact hne hxy.symm
      · rw [min_eq_right hy] at hxy
        exact hx.ne hxy
    rw [hyx, alignedDecode_of_lt (hx.trans hhμ), min_assoc, min_eq_right hγδ]
  · have hy : h ≤ y := by
      rw [min_eq_right (not_lt.mp hx)] at hxy
      by_contra hy
      rw [min_eq_left (not_le.mp hy).le] at hxy
      exact (not_le.mp hy).ne hxy.symm
    have hdec : γ ≤ alignedDecode μ V m ρ δ x :=
      (le_min (hγδ.trans hδρ) hγδ).trans ((min_le_min_right δ (hρ (not_lt.mp hx))).trans
        (le_max_left _ _))
    rw [min_eq_right hdec, min_eq_right (hγδ.trans (hδρ.trans (hρ hy)))]

/-! ### Locality from a read map with a lawful companion -/

/-- **Locality from a read map with a lawful companion.**  Let `c` be a cell of maximal grade, `q`
a labelling with `q c` self-visible at the grade of `c` and `E ⇒ (d ↦ min (q d) (q c))`, and `F` a
monotone map fixing bottom that commutes with visibility replacement at the thresholds `≤` the
grade of `c`.  If `F` reads the target from the row, `F (E d) = t d`, and `t` is bottom exactly
where `q` capped at `q c` is, then `E ⇒ t`.  The map `F` need not satisfy the guard above the
grade of `c`; it is repaired off the zero set of the capped witness of `q`
(`Label.exists_isWitness_interpolation`).  It proves the locality of the aligned encoding
(`CellScheme.Rows.IsLawful.alignedEncode`). -/
theorem TransformsTo.of_read {D : Type*} {grade : D → ℕ} {E q t : D → Label.{u}} {c : D}
    {F : Label.{u} → Label.{u}} (hmax : ∀ d, grade d ≤ grade c)
    (hvisq : IsSelfVisible (grade c) (q c)) (hlocq : TransformsTo grade E fun d ↦ min (q d) (q c))
    (hFbot : F ⊥ = ⊥) (hFmono : Monotone F)
    (hFcomm : ∀ x, ∀ k ≤ grade c, ∀ i ≤ k,
      F (visibilityReplace k i x) = visibilityReplace k i (F x))
    (hread : ∀ d, F (E d) = t d) (hbot : ∀ d, t d = ⊥ ↔ min (q d) (q c) = ⊥) :
    TransformsTo grade E t := by
  obtain ⟨τq, hτq, -, hcapq⟩ := hlocq.exists_isWitness_capped hmax hvisq
  obtain ⟨ρ, hρ, hS, hf⟩ := exists_isWitness_interpolation (f := F) (m := grade c)
    (S := {x | τq x = ⊥}) hFbot hFmono hFcomm
    (fun x y hxy hy ↦ le_bot_iff.mp ((show τq y = ⊥ from hy) ▸ hτq.monotone hxy))
    (fun x hx k i hi ↦ hτq.apply_visibilityReplace_eq_bot hx k hi)
  refine ⟨_, ρ, hρ, fun d ↦ ?_⟩
  rw [stepSuppressor_of_le (hmax d), min_top_right]
  by_cases hd : τq (E d) = ⊥
  · rw [hS _ hd]
    rw [hcapq] at hd
    exact (hbot d).mpr hd
  · have hne : F (E d) ≠ ⊥ := by
      rw [hread]
      exact fun h ↦ hd (by rw [hcapq]; exact (hbot d).mp h)
    rw [hf _ hd hne, hread]

/-! ### Room above the source cap -/

/-- Above every label other than the formal top lies an ordinal that is zero or a limit. -/
theorem exists_isSuccPrelimit_lt (hh : h ≠ ⊤) :
    ∃ μ : Ordinal.{u}, IsSuccPrelimit μ ∧ h < (μ : Label.{u}) := by
  induction h using recBotCoeTop with
  | bot => exact ⟨0, isSuccPrelimit_zero, WithBot.bot_lt_coe _⟩
  | coe o =>
    refine ⟨ω * succ (o / ω), isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right ω _), ?_⟩
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, mul_succ]
    exact lt_mul_div_add o omega0_ne_zero
  | top => exact absurd rfl hh

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label Order

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {μ : Ordinal.{u}}
  {V : Finset Label.{u}} {m : ℕ} {h δ γ : Label.{u}} {τ : Label.{u} → Label.{u}}

/-- **The aligned encoding is lawful.**  Let `s` and `p` be lawful, the grades at most `m`, `h ≠ ⊥`
and `δ` self-visible at `m`, `μ` zero or a limit with `h < μ`, and suppose the alignment: every cell
with `δ < p d` has `h ≤ s d`.  Then `alignedEncode μ V m h δ s p` is lawful.  Its locality at a cell
is read off the capped witnesses of `s` and `p` there, with `s` as the lawful companion
(`Label.TransformsTo.of_read`). -/
theorem IsLawful.alignedEncode {s p : ι → Label.{u}} (hs : R.IsLawful s) (hp : R.IsLawful p)
    (hK : ∀ d, D.grade d ≤ m) (hh : IsSelfVisible m h) (hhb : h ≠ ⊥) (hδ : IsSelfVisible m δ)
    (hμ : IsSuccPrelimit μ) (hhμ : h < (μ : Label.{u})) (halign : ∀ d, δ < p d → h ≤ s d) :
    R.IsLawful (Label.alignedEncode μ V m h δ s p) where
  orderly d := by
    have hH : IsSelfVisible (D.grade d) (highCode μ V m δ (p d)) := by
      have h' := highCode_visibilityReplace (V := V) hμ hδ (hK d) le_rfl (p d)
      rw [hp.orderly d] at h'
      exact h'.symm
    exact ((hs.orderly d).min (hh.mono (hK d))).max hH
  locality c := by
    have hfbot (e : ι) : Label.alignedEncode μ V m h δ s p e = ⊥ ↔ s e = ⊥ :=
      eq_bot_iff_of_min_eq (min_alignedEncode hhμ (halign e)) hhb
    obtain ⟨σs, hσs, -, hσsr⟩ := TransformsTo.exists_isWitness_capped
      (grade := fun d : D.below (D.gradedIndex c) ↦ D.grade d) (E := R.row c)
      (p := fun d ↦ s d) (c := ⟨c, D.mem_below_gradedIndex c⟩) (fun d ↦ d.2.2) (hs.orderly c)
      (hs.locality c)
    obtain ⟨σp, hσp, -, hσpr⟩ := TransformsTo.exists_isWitness_capped
      (grade := fun d : D.below (D.gradedIndex c) ↦ D.grade d) (E := R.row c)
      (p := fun d ↦ p d) (c := ⟨c, D.mem_below_gradedIndex c⟩) (fun d ↦ d.2.2) (hp.orderly c)
      (hp.locality c)
    refine TransformsTo.of_read (grade := fun d : D.below (D.gradedIndex c) ↦ D.grade d)
      (E := R.row c) (q := fun d ↦ s d) (c := ⟨c, D.mem_below_gradedIndex c⟩)
      (F := fun x ↦ max (min (σs x) h) (highCode μ V m δ (σp x))) (fun d ↦ d.2.2) (hs.orderly c)
      (hs.locality c) (by simp [hσs.map_bot, hσp.map_bot, highCode_bot])
      (fun x y hxy ↦ max_le_max (min_le_min_right h (hσs.monotone hxy))
        (monotone_highCode (hσp.monotone hxy))) (fun x k hk i hi ↦ ?_) (fun d ↦ ?_)
      (fun d ↦ ?_)
    · have hkm : k ≤ m := hk.trans (hK c)
      rw [hσs.visibilityReplace_comm x k (by simp [hk]) i hi,
        hσp.visibilityReplace_comm x k (by simp [hk]) i hi,
        highCode_visibilityReplace hμ hδ hkm hi, visibilityReplace_max hi,
        visibilityReplace_min_of_isSelfVisible hi (hh.mono hkm)]
    · rw [hσsr d, hσpr d]
      exact max_min_highCode_min hhμ (halign d) (halign c)
    · rw [min_eq_bot, min_eq_bot, hfbot, hfbot]
  availability c t hct hg := by
    by_cases hle : highCode μ V m δ (p c) ≤ min (s c) h
    · obtain ⟨u, hu, hcu⟩ := hs.availability c t hct hg
      refine ⟨u, hu, ?_⟩
      rw [Label.alignedEncode, Label.alignedEncode, max_eq_left hle]
      exact (min_le_min_right h hcu).trans (le_max_left _ _)
    · obtain ⟨u, hu, hcu⟩ := hp.availability c t hct hg
      refine ⟨u, hu, ?_⟩
      rw [Label.alignedEncode, Label.alignedEncode, max_eq_right (not_le.mp hle).le]
      exact (monotone_highCode hcu).trans (le_max_right _ _)

/-- **The aligned encoding is lawful below a pair** (`CellScheme.Rows.IsLawful.alignedEncode`). -/
theorem IsLawfulBelow.alignedEncode {X : Finset α × ℕ} {s p : D.below X → Label.{u}}
    (hs : R.IsLawfulBelow X s) (hp : R.IsLawfulBelow X p) (hK : ∀ d : D.below X, D.grade d ≤ m)
    (hh : IsSelfVisible m h) (hhb : h ≠ ⊥) (hδ : IsSelfVisible m δ) (hμ : IsSuccPrelimit μ)
    (hhμ : h < (μ : Label.{u})) (halign : ∀ d, δ < p d → h ≤ s d) :
    R.IsLawfulBelow X (Label.alignedEncode μ V m h δ s p) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hs).alignedEncode (isLawfulBelow_iff.mp hp) hK hh
    hhb hδ hμ hhμ halign)

/-- **The aligned encoding below an owner, with its decoder.**  Let `o` be a cell of graded index
`X` below `X`, on finitely many cells, let `s` and `p` be lawful below `X`, `s` short at the grade
of `X` with `s o ≠ ⊤`, and let `τ` be a witness bounded by the grade of `X` with `τ ≤ γ` and
`τ ∘ s = min p γ`, where `⊥ < γ < p o` and `γ` is self-visible at the grade of `X`.  Then there are
a source cap `h` (`⊥ < h ≤ s o`, self-visible at the grade of `X`), a witness `ρ` bounded by the
grade of `X`, and a labelling `f` of codes lawful below `X`, such that

* `f` is never the formal top and agrees with `s` capped at `h`;
* **(i)** `ρ` reads `f` literally as the prescription capped at the owner label:
  `ρ (f e) = min (p e) (p o)`;
* **(ii)** `ρ` reads every label `x` that agrees capped at `h` with a label `z` short at the grade
  of `X` as `τ z` capped at `γ`: `min (ρ x) γ = min (τ z) γ`.

The decoder is the extended decoder of the alignment decoder of
`CellScheme.Rows.IsLawfulBelow.exists_ownerAlignment`, and `f` its aligned encoding.  In the
one-grade step, (ii) gives the ambient observation at the cap `γ` at every cell of a labelling of
codes that agrees with the source of the serving cell capped at `h`, and (i) the literal reading of
the prescribed face; with positive-cap transport the decoded labelling is an owner-capped lift
(`CellScheme.Rows.hasOwnerCappedLifts_of_source`). -/
theorem IsLawfulBelow.exists_alignedEncoding {X : Finset α × ℕ} [Finite (D.below X)]
    {s p : D.below X → Label.{u}} (hs : R.IsLawfulBelow X s) (hp : R.IsLawfulBelow X p)
    {o : D.below X} (ho : D.gradedIndex o = X) (hshort : ∀ e, IsShort X.2 (s e))
    (htop : s o ≠ ⊤) (hτ : IsWitness (stepSuppressor X.2) τ) (hτγ : ∀ x, τ x ≤ γ)
    (hface : ∀ e, τ (s e) = min (p e) γ) (hγ : IsSelfVisible X.2 γ) (hγbot : ⊥ < γ)
    (hγo : γ < p o) :
    ∃ h ρ f, ⊥ < h ∧ IsSelfVisible X.2 h ∧ h ≤ s o ∧ IsWitness (stepSuppressor.{u} X.2) ρ ∧
      R.IsLawfulBelow X f ∧ (∀ e, f e ≠ ⊤) ∧ (∀ e, min (f e) h = min (s e) h) ∧
      (∀ e, ρ (f e) = min (p e) (p o)) ∧
      ∀ x z, IsShort X.2 z → min x h = min z h → min (ρ x) γ = min (τ z) γ := by
  classical
  have := Fintype.ofFinite (D.below X)
  obtain ⟨h, δ, ρ, hhbot, hhtop, hhvis, hho, hρ, hγδ, hδo, hδvis, hρh, hread, halign, hcap⟩ :=
    hs.exists_ownerAlignment hp ho hshort htop hτ hτγ hface hγ hγbot hγo
  obtain ⟨μ, hμ, hhμ⟩ := exists_isSuccPrelimit_lt hhtop
  set p₀ : D.below X → Label.{u} := fun e ↦ min (p e) (p o) with hp₀_def
  have hp₀ : R.IsLawfulBelow X p₀ :=
    hp.min_const_of_isSelfVisible (hp.isSelfVisible_of_gradedIndex_eq ho)
  set V : Finset Label.{u} := Finset.univ.image p₀
  refine ⟨h, alignedDecode μ V X.2 ρ δ, Label.alignedEncode μ V X.2 h δ s p₀, hhbot, hhvis, hho,
    isWitness_alignedDecode hμ hρ hδvis,
    hs.alignedEncode hp₀ (fun d ↦ d.2.2) hhvis hhbot.ne' hδvis hμ hhμ halign,
    fun e ↦ alignedEncode_ne_top hhtop, fun e ↦ min_alignedEncode hhμ (halign e), fun e ↦ ?_,
    fun x z hz hxz ↦ (min_alignedDecode_eq hρ.monotone hγδ hρh.ge hhμ hxz).trans (hcap z hz)⟩
  refine alignedDecode_alignedEncode hρ.monotone hhμ hρh.ge ?_
    fun _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ e)
  rw [hp₀_def, min_assoc, min_eq_right hδo]
  exact hread e

end VaughtConjecture.CellScheme.Rows

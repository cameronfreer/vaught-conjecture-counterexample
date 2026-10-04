/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OwnerCappedLift
import VaughtConjecture.Extension.TransformationExamples
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples: owner-local alignment, aligned encoding, and owner-capped lifts

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (the alignment of owners); semantic contract, item 3.

* **The reading cap must exceed the cap.**  Two cells `d`, `o` of grades `1` and `2`, with the
  row of `o` equal to the source `s = (ω * 6 + 1, ω * 6 + 2)`, the prescription
  `p = (ω * 9 + 1, ω * 9 + 2)`, the cap `γ = ω * 3 + 2`, and the witness `τ` bounded by grade `2`
  that is bottom below `ω * 6` and `γ` from there on.  The hypotheses of the owner-local
  alignment hold (`exists_alignment_strip`).  Both cells are saturated, and the source of `d` lies
  in the strip `[ω * 6, ω * 6 + 2]` below its end: every source cap `h` self-visible at `2` and at
  most `s d` lies below `ω * 6`.  With the reading cap `δ = γ` the alignment would force
  `h ≤ s d`, and the alignment decoder would send `h` to bottom, although `ρ h = δ` is not bottom.
  So no alignment has the reading cap `δ = γ`: every alignment has `γ < δ` (`cap_lt_readingCap`),
  so `ρ h = δ > γ ≥ τ h` and the alignment decoder is not `τ`.  This is the owner label above the
  cap at a grade with a saturated strip.
* **The one-face case** `C = B`, on a scheme whose cells all have the full scope of one point and
  grade `1` with rows constantly `1` (short at `1`, never the formal top): with `U = V = O = Y`,
  every cell lies on the boundary (`CellScheme.Rows.extendsFromBoundary_self`), and the rows have
  owner-capped lifts at every cap self-visible at `1` (`hasOwnerCappedLifts_oneFace`), by the
  alignment, the aligned encoding, and the decoding at the positive caps.
  - *One coordinate*: one cell.
  - *Repeated coordinates*: two cells of one graded index, both serving cells.
  - *The owner label above a positive cap*: the prescription `ω + 1` and the cap `1`.
  - *The cap `⊥`, with literal top*: the prescription `⊤` is read literally.
* **The owner label at most the cap** needs no owner-capped lift: the one-grade lift
  (`CellScheme.Rows.cappedLift_of_ownerCappedLift`) takes the lift below the cap
  (`CellScheme.Rows.exists_lift_of_le_cap`) there, and no example is given here.
* **Grade `0`.**  The owner-local alignment applies to a single cell of grade `0`, where every
  label is self-visible and no source lies in a strip below its end.
* **A label at `K + 1`.**  The tail code of `3` relative to `{3}` at grade `1` has finite part
  `2 = 1 + 1`: it is not short at `1`, and the tail decoder reads it literally.  The aligned
  encoding is lawful whether or not its tail codes are short.

## References

Witnesses are [Kni26, Definition 2.3.9]; lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset CellScheme Label
open scoped Ordinal

namespace AlignmentExamples

/-! ### The reading cap must exceed the cap -/

/-- The point `ω * b + n`, for natural numbers `b` and `n`. -/
noncomputable abbrev pt (b n : ℕ) : Label.{u} :=
  ((ω * (b : Ordinal.{u}) + (n : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

/-- Points of blocks compare lexicographically. -/
private theorem pt_le_pt {b b' n n' : ℕ} (h : b < b' ∨ b = b' ∧ n ≤ n') :
    pt.{u} b n ≤ pt b' n' :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (omega0_mul_add_natCast_le_iff.mpr
    (h.imp (fun h ↦ by exact_mod_cast h) fun h ↦ ⟨by rw [h.1], h.2⟩)))

/-- A point of a lower block lies below every point of a higher block. -/
private theorem pt_lt_pt {b b' n n' : ℕ} (h : b < b') : pt.{u} b n < pt b' n' :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (omega0_mul_add_natCast_lt
    (by exact_mod_cast h) n _))

/-- A point of a block is self-visible at `k` exactly when its finite part is at least `k`. -/
private theorem isSelfVisible_pt {k b n : ℕ} : IsSelfVisible k (pt.{u} b n) ↔ k ≤ n := by
  rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- A point of a block is short at `k` exactly when its finite part is at most `k`. -/
private theorem isShort_pt {k b n : ℕ} : IsShort k (pt.{u} b n) ↔ n ≤ k := by
  rw [isShort_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- The start `ω * b` of the block `b` is zero or a limit. -/
private theorem isSuccPrelimit_block (b : ℕ) : Order.IsSuccPrelimit (ω * (b : Ordinal.{u})) :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

/-- The start of the block `6`, as a label. -/
noncomputable abbrev six : Label.{u} := ((ω * (6 : ℕ) : Ordinal.{u}) : Label.{u})

/-- Every point of the block `6` is at least its start. -/
private theorem six_le_pt {n : ℕ} : six.{u} ≤ pt 6 n :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

/-- The grades: `d = false` has grade `1`, the owner `o = true` grade `2`. -/
def stripGrade : Bool → ℕ := fun e ↦ if e then 2 else 1

/-- The source, also the row of the owner: `(ω * 6 + 1, ω * 6 + 2)`. -/
noncomputable def stripSource : Bool → Label.{u} := fun e ↦ if e then pt 6 2 else pt 6 1

/-- The prescription: `(ω * 9 + 1, ω * 9 + 2)`. -/
noncomputable def stripPrescription : Bool → Label.{u} :=
  fun e ↦ if e then pt 9 2 else pt 9 1

/-- The cap `ω * 3 + 2`. -/
noncomputable abbrev stripCap : Label.{u} := pt 3 2

/-- The witness of the ambient: bottom below `ω * 6`, the cap from there on. -/
noncomputable def stripAmbient (x : Label.{u}) : Label.{u} :=
  open Classical in if x < six then ⊥ else stripCap

/-- The shifter of the prescription: bottom below `ω * 6`, translation from `ω * 6` to `ω * 9`
above. -/
private noncomputable def stripShift (x : Label.{u}) : Label.{u} :=
  open Classical in if x < six then ⊥ else translate (ω * (9 : ℕ)) (ω * (6 : ℕ)) x

/-- The cap is not bottom. -/
private theorem stripCap_ne_bot : stripCap.{u} ≠ ⊥ := WithBot.coe_ne_bot

/-- The witness of the ambient is a witness bounded by grade `2`. -/
private theorem isWitness_stripAmbient : IsWitness (stepSuppressor.{u} 2) stripAmbient where
  antitone := (IsWitness.id_step 2).antitone
  isSelfVisible := (IsWitness.id_step 2).isSelfVisible
  map_bot := ite_eq_left (WithBot.bot_lt_coe _)
  monotone x y hxy := by
    unfold stripAmbient
    by_cases hy : y < six
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
    by_cases hx : x < six
    · rw [ite_eq_left hx]; exact bot_le
    rw [ite_eq_right hx, ite_eq_right hy]
  visibilityReplace_comm x k hx i hi := by
    have hlt := visibilityReplace_lt_iff (k := k) (i := i) (x := x) (isSuccPrelimit_block.{u} 6)
    unfold stripAmbient at hx ⊢
    by_cases hxs : x < six
    · rw [ite_eq_left hxs, ite_eq_left (hlt.mpr hxs), visibilityReplace_bot]
    · rw [ite_eq_right hxs, ite_eq_right (mt hlt.mp hxs)] at *
      by_cases hk : k ≤ 2
      · exact ((isSelfVisible_pt.mpr le_rfl).mono hk).visibilityReplace_eq i |>.symm
      · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
        exact absurd hx stripCap_ne_bot

/-- The shifter of the prescription is a witness. -/
private theorem isWitness_stripShift : IsWitness (fun _ ↦ (⊤ : Label.{u})) stripShift where
  antitone := antitone_const
  isSelfVisible _ := isSelfVisible_top _
  map_bot := ite_eq_left (WithBot.bot_lt_coe _)
  monotone x y hxy := by
    unfold stripShift
    by_cases hy : y < six
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
    by_cases hx : x < six
    · rw [ite_eq_left hx]; exact bot_le
    rw [ite_eq_right hx, ite_eq_right hy]
    exact monotone_translate _ _ hxy
  visibilityReplace_comm x k _ i _ := by
    have hlt := visibilityReplace_lt_iff (k := k) (i := i) (x := x) (isSuccPrelimit_block.{u} 6)
    unfold stripShift
    by_cases hxs : x < six
    · rw [ite_eq_left hxs, ite_eq_left (hlt.mpr hxs), visibilityReplace_bot]
    · rw [ite_eq_right hxs, ite_eq_right (mt hlt.mp hxs), translate_visibilityReplace
        (isSuccPrelimit_block 9) (isSuccPrelimit_block 6) (not_lt.mp hxs)]

/-- The source is at most its value at the owner. -/
private theorem stripSource_le (e : Bool) : stripSource.{u} e ≤ stripSource true := by
  cases e
  · exact pt_le_pt (.inr ⟨rfl, by omega⟩)
  · exact le_rfl

/-- The prescription is at most its value at the owner. -/
private theorem stripPrescription_le (e : Bool) :
    stripPrescription.{u} e ≤ stripPrescription true := by
  cases e
  · exact pt_le_pt (.inr ⟨rfl, by omega⟩)
  · exact le_rfl

/-- The shifter of the prescription sends the source to the prescription. -/
private theorem stripShift_source (e : Bool) :
    stripShift.{u} (stripSource e) = stripPrescription e := by
  have key (n : ℕ) : stripShift.{u} (pt 6 n) = pt 9 n := by
    rw [stripShift, ite_eq_right (not_lt.mpr six_le_pt), translate_coe, Ordinal.add_sub_cancel]
  cases e
  · exact key 1
  · exact key 2

/-- The witness of the ambient decodes the source to the prescription capped at the cap. -/
private theorem stripAmbient_source (e : Bool) :
    stripAmbient.{u} (stripSource e) = min (stripPrescription e) stripCap := by
  have hs : ¬ stripSource.{u} e < six := by
    cases e <;> exact not_lt.mpr six_le_pt
  have hp : stripCap.{u} ≤ stripPrescription e := by
    cases e <;> exact (pt_lt_pt (by omega)).le
  rw [stripAmbient, ite_eq_right hs, min_eq_right hp]

/-- **The owner-local alignment on the strip example**: its hypotheses hold there, so some source
cap, reading cap, and alignment decoder have its conclusions. -/
theorem exists_alignment_strip :
    ∃ h δ ρ, ⊥ < h ∧ h ≠ ⊤ ∧ IsSelfVisible 2 h ∧ IsShort 2 h ∧ h ≤ stripSource.{u} true ∧
      IsWitness (stepSuppressor.{u} 2) ρ ∧ stripCap ≤ δ ∧ δ ≤ stripPrescription true ∧
      IsSelfVisible 2 δ ∧ ρ h = δ ∧
      (∀ e, min (stripPrescription e) δ = min (ρ (stripSource e)) δ) ∧
      (∀ e, δ < min (stripPrescription e) (stripPrescription true) → h ≤ stripSource e) ∧
      ∀ z, IsShort 2 z → min (ρ z) stripCap = min (stripAmbient z) stripCap := by
  refine exists_ownerAlignment (grade := stripGrade) (E := stripSource) (o := true)
    (fun e ↦ by cases e <;> simp [stripGrade]) rfl (isSelfVisible_pt.mpr le_rfl)
    ⟨fun _ ↦ ⊤, id, IsWitness.id_top, fun e ↦ ?_⟩ (isSelfVisible_pt.mpr le_rfl)
    ⟨fun _ ↦ ⊤, stripShift, isWitness_stripShift, fun e ↦ ?_⟩
    (fun e ↦ by cases e <;> exact isShort_pt.mpr (by omega))
    (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
    isWitness_stripAmbient (fun x ↦ by unfold stripAmbient; split_ifs <;> simp)
    stripAmbient_source (isSelfVisible_pt.mpr le_rfl) (WithBot.bot_lt_coe _) (pt_lt_pt (by omega))
  · dsimp only
    rw [min_eq_left (stripSource_le e), min_top_right, id]
  · dsimp only
    rw [min_eq_left (stripPrescription_le e), min_top_right, stripShift_source]

/-- **The reading cap must exceed the cap.**  On the strip example, every source cap, reading
cap, and alignment decoder with the conclusions of the owner-local alignment have the reading cap
strictly above the cap.  Suppose the reading cap were the cap.  Then the alignment at `d` would
bound the source cap by `ω * 6 + 1`, so the source cap, being self-visible at `2`, would be
`ω * b + n` with `b < 6` and `n ≥ 2`, below `ω * 6`, where the ambient witness is bottom.  By the
cap observation at the short label `ω * b + 2`, of which the source cap is a visibility
replacement, the alignment decoder would send the source cap to bottom, contradicting `ρ h = δ`.
So the alignment decoder is retuned (it is not `τ` and reads the strip above the cap,
`VaughtConjecture.Extension.OwnerAlignment`). -/
theorem cap_lt_readingCap {h δ : Label.{u}} {ρ : Label.{u} → Label.{u}} (hhbot : ⊥ < h)
    (hhvis : IsSelfVisible 2 h) (hρ : IsWitness (stepSuppressor.{u} 2) ρ) (hγδ : stripCap ≤ δ)
    (hρh : ρ h = δ)
    (halign : ∀ e, δ < min (stripPrescription e) (stripPrescription true) → h ≤ stripSource e)
    (hcap : ∀ z, IsShort 2 z → min (ρ z) stripCap = min (stripAmbient z) stripCap) :
    stripCap < δ := by
  by_contra hδ
  have hδeq : δ = stripCap := le_antisymm (not_lt.mp hδ) hγδ
  -- The alignment at `d` puts the source cap at most `ω * 6 + 1`.
  have hhd : h ≤ pt 6 1 := halign false (by
    rw [hδeq, min_eq_left (stripPrescription_le false)]
    exact pt_lt_pt (by omega))
  -- So the source cap is `ω * b + n` with `n ≥ 2` and `b < 6`.
  induction h using recBotCoeTop with
  | bot => exact absurd hhbot (lt_irrefl _)
  | top => exact absurd hhd (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)))
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    have hn : 2 ≤ n := by
      have := isSelfVisible_coe.mp hhvis
      rwa [omega0_mul_add_natCast_mod, Nat.cast_le] at this
    have hb : b < ((6 : ℕ) : Ordinal.{u}) := by
      have := omega0_mul_add_natCast_le_iff.mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hhd))
      rcases this with h | ⟨-, h⟩
      · exact h
      · omega
    -- The short label `ω * b + 2` lies below `ω * 6`, so `ρ` sends it to bottom.
    set z : Label.{u} := ((ω * b + (2 : ℕ) : Ordinal.{u}) : Label.{u}) with hz
    have hzshort : IsShort 2 z := by
      rw [hz, isShort_coe, omega0_mul_add_natCast_mod]
    have hzsix : z < six := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by
      simpa using omega0_mul_add_natCast_lt hb 2 0))
    have hρz : ρ z = ⊥ := by
      have h' := hcap z hzshort
      rw [stripAmbient, ite_eq_left hzsix, min_bot_left, min_eq_bot] at h'
      exact h'.resolve_right stripCap_ne_bot
    -- The source cap is a replacement of `z` at the threshold `n`, so `ρ` sends it to bottom.
    have hvr : visibilityReplace n n z = ((ω * b + n : Ordinal.{u}) : Label.{u}) := by
      rw [hz, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]
      congr 4
      split_ifs <;> omega
    have hρh' := hρ.visibilityReplace_comm z n (by rw [hρz]; exact bot_le) n le_rfl
    rw [hvr, hρz, visibilityReplace_bot, hρh] at hρh'
    exact absurd (hρh' ▸ hγδ) (not_le.mpr (WithBot.bot_lt_coe _))

/-! ### The one-face case -/

/-- A scheme whose cells all have the full scope of one point and grade `1`. -/
def oneFace (ι : Type*) : CellScheme ι (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The rows of `oneFace ι` that are constantly `1`. -/
def oneRows (ι : Type*) : (oneFace ι).Rows.{u} := ⟨fun _ _ ↦ 1⟩

/-- The constant labelling `1` is lawful below every pair for the rows constantly `1`. -/
private theorem isLawfulBelow_one {ι : Type*} (X : Finset (Fin 1) × ℕ) :
    (oneRows.{u} ι).IsLawfulBelow X fun _ ↦ 1 :=
  Rows.isLawfulBelow_iff.mpr ⟨fun _ ↦ (isSelfVisible_one.mpr le_rfl : IsSelfVisible 1 (1 : Label)),
    fun _ ↦ ⟨_, id, IsWitness.id_top, fun _ ↦ by simp [oneRows]⟩,
    fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩⟩

/-- The label `1` is the point `ω * 0 + 1`. -/
private theorem one_eq_pt : (1 : Label.{u}) = pt 0 1 := by simp [pt]

/-- **The one-face case**: on `oneFace ι` with the rows constantly `1`, for a finite nonempty
family of cells, the rows have owner-capped lifts from `(univ, 1)` to itself at every cap
self-visible at `1`, from the boundary and the serving cells
(`CellScheme.Rows.hasOwnerCappedLifts_of_boundary`). -/
theorem hasOwnerCappedLifts_oneFace {ι : Type*} [Finite ι] [Nonempty ι] (c : Label.{u})
    (hc : IsSelfVisible 1 c) :
    (oneRows.{u} ι).HasOwnerCappedLifts (subset_refl (univ : Finset (Fin 1))) 0 c := by
  have : Finite ((oneFace ι).below ((univ : Finset (Fin 1)), 0 + 1)) := Subtype.finite
  set Y : Finset (Fin 1) × ℕ := ((univ : Finset (Fin 1)), 0 + 1) with hY
  have hrefl : (oneRows.{u} ι).CappedLift (le_refl Y) := Rows.cappedLift_refl Y
  refine Rows.hasOwnerCappedLifts_of_boundary (C := univ) (B := univ) (j := 0) (U := Y) (V := Y)
    (O := Y) subset_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (fun _ hd _ ↦ hd) hrefl hrefl
    (Rows.extendsFromBoundary_self _ _ _) ⟨Classical.arbitrary ι, rfl⟩ (fun u hu ↦ ?_) c hc
  refine ⟨isLawfulBelow_one _, fun _ ↦ ?_, fun _ ↦ ?_,
    fun _ _ _ ↦ Rows.extendsFromBoundary_self _ _ _⟩
  · change IsShort (0 + 1) ((1 : Ordinal.{u}) : Label.{u})
    exact isShort_coe.mpr (by simpa using Ordinal.mod_le (1 : Ordinal.{u}) ω)
  · change ((1 : Ordinal.{u}) : Label.{u}) ≠ ⊤
    exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne

/-- *One coordinate*: one cell. -/
example (c : Label.{u}) (hc : IsSelfVisible 1 c) :
    (oneRows.{u} (Fin 1)).HasOwnerCappedLifts (subset_refl (univ : Finset (Fin 1))) 0 c :=
  hasOwnerCappedLifts_oneFace c hc

/-- *Repeated coordinates*: two cells of one graded index, both serving cells. -/
example (c : Label.{u}) (hc : IsSelfVisible 1 c) :
    (oneRows.{u} Bool).HasOwnerCappedLifts (subset_refl (univ : Finset (Fin 1))) 0 c :=
  hasOwnerCappedLifts_oneFace c hc

/-- The shifter sending every label other than bottom to the formal top. -/
private noncomputable def toTop (x : Label.{u}) : Label.{u} :=
  open Classical in if x = ⊥ then ⊥ else ⊤

/-- The shifter sending every label other than bottom to the formal top is a witness. -/
private theorem isWitness_toTop : IsWitness (fun _ ↦ (⊤ : Label.{u})) toTop where
  antitone := antitone_const
  isSelfVisible _ := isSelfVisible_top _
  map_bot := ite_eq_left rfl
  monotone x y hxy := by
    unfold toTop
    by_cases hx : x = ⊥
    · rw [ite_eq_left hx]; exact bot_le
    have hy : ¬ y = ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
    rw [ite_eq_right hx, ite_eq_right hy]
  visibilityReplace_comm x k _ i _ := by
    unfold toTop
    by_cases hx : x = ⊥
    · rw [ite_eq_left hx, ite_eq_left (by rw [hx, visibilityReplace_bot]), visibilityReplace_bot]
    · rw [ite_eq_right hx, ite_eq_right (mt visibilityReplace_eq_bot_iff.mp hx),
        visibilityReplace_top]

/-- The literal top is lawful below `(univ, 1)` for the rows constantly `1`. -/
private theorem isLawfulBelow_top :
    (oneRows.{u} (Fin 1)).IsLawfulBelow ((univ : Finset (Fin 1)), 0 + 1) fun _ ↦ ⊤ :=
  Rows.isLawfulBelow_iff.mpr ⟨fun _ ↦ isSelfVisible_top _, fun _ ↦ ⟨_, toTop, isWitness_toTop,
    fun _ ↦ by simp [toTop, oneRows]⟩, fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩⟩

/-- The cell of `oneFace (Fin 1)`, below `(univ, 1)`. -/
private def oneCell : (oneFace (Fin 1)).below ((univ : Finset (Fin 1)), 0 + 1) :=
  ⟨0, show (oneFace (Fin 1)).gradedIndex 0 ≤ (univ, 0 + 1) from le_rfl⟩

/-- *The cap `⊥`, with literal top*: the owner-capped lift at the cap `⊥` reads the prescription
`⊤` literally. -/
example : ∃ w : (oneFace (Fin 1)).below ((univ : Finset (Fin 1)), 0 + 1) → Label.{u},
    (oneRows.{u} (Fin 1)).IsLawfulBelow (univ, 0 + 1) w ∧ ∀ d, w d = ⊤ := by
  obtain ⟨w, hw, hwp, -⟩ := hasOwnerCappedLifts_oneFace.{u} (ι := Fin 1) ⊥ (isSelfVisible_bot 1)
    (fun _ ↦ ⊤) (fun _ ↦ ⊤) isLawfulBelow_top isLawfulBelow_top (fun _ ↦ rfl) oneCell rfl
    (fun _ _ ↦ le_rfl) (WithBot.bot_lt_coe _)
  refine ⟨w, hw, fun d ↦ ?_⟩
  have := hwp d
  rwa [min_self] at this

/-- The translation by `ω`. -/
private theorem isWitness_translate_omega0 :
    IsWitness (fun _ ↦ (⊤ : Label.{u})) (translate ω 0) where
  antitone := antitone_const
  isSelfVisible _ := isSelfVisible_top _
  map_bot := rfl
  monotone := monotone_translate _ _
  visibilityReplace_comm x k _ i _ := by
    induction x using recBotCoeTop with
    | bot => rfl
    | coe o =>
      exact translate_visibilityReplace Ordinal.isSuccLimit_omega0.isSuccPrelimit
        (Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_zero _))
        (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (zero_le (a := o)))) k i
    | top => rfl

/-- The label `ω + 1`, lawful below `(univ, 1)` for the rows constantly `1`. -/
private theorem isLawfulBelow_omega0_add_one :
    (oneRows.{u} (Fin 1)).IsLawfulBelow ((univ : Finset (Fin 1)), 0 + 1) fun _ ↦ pt 1 1 :=
  Rows.isLawfulBelow_iff.mpr ⟨fun _ ↦ isSelfVisible_pt.mpr le_rfl, fun _ ↦ ⟨_, translate ω 0,
    isWitness_translate_omega0, fun _ ↦ by
      rw [min_self, min_top_right]
      change pt 1 1 = translate ω 0 ((1 : Ordinal.{u}) : Label.{u})
      rw [translate_coe]
      simp [pt]⟩,
    fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩⟩

/-- *The owner label above a positive cap*: at the cap `1`, the prescription `ω + 1` has an
owner-capped lift reading it literally, with the observation of the ambient `ω + 1` at `1`. -/
example : ∃ w : (oneFace (Fin 1)).below ((univ : Finset (Fin 1)), 0 + 1) → Label.{u},
    (oneRows.{u} (Fin 1)).IsLawfulBelow (univ, 0 + 1) w ∧ (∀ d, w d = pt 1 1) ∧
      ∀ d, min (w d) 1 = 1 := by
  have h1 : (1 : Label.{u}) < pt 1 1 := one_eq_pt ▸ pt_lt_pt (by omega)
  obtain ⟨w, hw, hwp, hwc⟩ := hasOwnerCappedLifts_oneFace.{u} (ι := Fin 1) 1 (by simp)
    (fun _ ↦ pt 1 1) (fun _ ↦ pt 1 1) isLawfulBelow_omega0_add_one isLawfulBelow_omega0_add_one
    (fun _ ↦ rfl) oneCell rfl (fun _ _ ↦ le_rfl) h1
  refine ⟨w, hw, fun d ↦ ?_, fun d ↦ ?_⟩
  · have := hwp d
    rwa [min_self] at this
  · rw [hwc d]
    exact min_eq_right h1.le

/-! ### Grade `0` -/

/-- *Grade `0`*: on a single cell of grade `0`, with row `⊤`, source `ω`, prescription `⊤`, cap
`1`, and the witness `x ↦ min x 1`, the owner-local alignment applies. -/
example : ∃ h δ ρ, ⊥ < h ∧ h ≠ ⊤ ∧ IsSelfVisible 0 h ∧ IsShort 0 h ∧ h ≤ pt.{u} 1 0 ∧
    IsWitness (stepSuppressor.{u} 0) ρ ∧ 1 ≤ δ ∧ δ ≤ ⊤ ∧ IsSelfVisible 0 δ ∧ ρ h = δ ∧
    (∀ _ : Unit, min ⊤ δ = min (ρ (pt 1 0)) δ) ∧
    (∀ _ : Unit, δ < min (⊤ : Label.{u}) ⊤ → h ≤ pt 1 0) ∧
    ∀ z, IsShort 0 z → min (ρ z) 1 = min (min z 1) 1 := by
  have hvis0 (x : Label.{u}) : IsSelfVisible 0 x := by
    induction x using recBotCoeTop with
    | bot => exact isSelfVisible_bot 0
    | coe o => exact isSelfVisible_coe.mpr (by simp)
    | top => exact isSelfVisible_top 0
  have h1top : (1 : Label.{u}) < ⊤ := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  have hω1 : (1 : Label.{u}) ≤ pt 1 0 := one_eq_pt ▸ (pt_lt_pt (by omega)).le
  exact exists_ownerAlignment (I := Unit) (grade := fun _ ↦ 0) (E := fun _ ↦ ⊤)
    (s := fun _ ↦ pt 1 0) (p := fun _ ↦ ⊤) (o := ()) (fun _ ↦ le_rfl) rfl (hvis0 _)
    ⟨_, fun x ↦ min (id x) (pt 1 0), (IsWitness.id_step 0).min_const (hvis0 _), fun _ ↦ by simp⟩
    (hvis0 _) (by simpa using TransformsTo.refl (fun _ : Unit ↦ 0) fun _ ↦ (⊤ : Label.{u}))
    (fun _ ↦ isShort_pt.mpr le_rfl) (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
    ((IsWitness.id_step 0).min_const (hvis0 1)) (fun _ ↦ min_le_right _ _)
    (fun _ ↦ by simp [min_eq_right hω1]) (hvis0 _) (WithBot.bot_lt_coe _)
    h1top

/-! ### A label at `K + 1` -/

/-- *A label at `K + 1`*: the tail code of `3` relative to `{3}` at grade `1`, above `ω`, has
finite part `2 = 1 + 1`, so it is not short at `1`; the tail decoder reads it literally. -/
example : ¬ IsShort 1 (tailEncode ω ({3} : Finset Label.{u}) 1 3) ∧
    tailDecode ω ({3} : Finset Label.{u}) 1 (tailEncode ω {3} 1 3) = 3 := by
  refine ⟨fun h ↦ TransformationExamples.isStronglyCoded_and_not_isShort_strongEncode.2 ?_,
    tailDecode_tailEncode (mem_singleton_self _) (WithBot.coe_ne_bot)⟩
  rw [tailEncode] at h
  induction hx : strongEncode ({3} : Finset Label.{u}) 1 3 using recBotCoeTop with
  | bot => exact isShort_bot 1
  | top => exact isShort_top 1
  | coe o =>
    rw [hx, translate_coe, isShort_coe, Ordinal.sub_zero] at h
    rw [isShort_coe]
    rwa [show ω + o = ω * 1 + o by rw [mul_one], Ordinal.mul_add_mod_self] at h

end AlignmentExamples

end VaughtConjecture

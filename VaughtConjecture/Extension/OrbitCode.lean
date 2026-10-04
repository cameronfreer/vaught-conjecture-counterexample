/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalCode

/-!
# The orbit code

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities: the catalogue of the field
layer at a grade with cells of lower grades); semantic contract, item 3.

The canonical code of `VaughtConjecture.Extension.CanonicalCode` ranks a label `x` by its
replacement `vr k k x`, so it sends the labels `ω * c + 1` and `ω * c + 2` to one canonical point
at grade `2`.  A field layer at grade `2` over a scheme with cells of grade `1` must read both: a
new cell above a grade-`1` cell labelled `ω * 3 + 1` and a grade-`2` cell labelled `ω * 3 + 2`
needs a witness reading one code as `ω * 3 + 1` at grade `1` and as `ω * 3 + 2` at grade `2`, which
no antitone suppressor allows (`VaughtConjecture.Extension.SmallArityOneExamples`, R5).  The
**orbit code** keeps the finite parts below `k`.

**Keys and strips.**  The **key** of a label `x` at grade `k` is `vr k k x`; the labels with the
key `ω * b + k` form the **strip** `[ω * b, ω * b + k]` of the block `b`.  A key of a labelling `w`
is the key of one of its values other than bottom.  It is an **orbit key** (`Label.IsOrbitKey`)
when some value of `w` with that key is not self-visible at `k`, i.e. has finite part below `k`;
its strip then carries the values of `w` with their finite parts, the *orbit* of the key.  Every
other key of `w` carries exactly one value, the key itself.  The **key rank** of `x`
(`Label.keyRank`) is the number of keys of `w` at most the key of `x`.

**The code block** (`Label.codeBlock`) of a label `x` other than bottom, with `r` the key rank of
`x`, is the block in which the orbit code places it: `0` if the key of `x` is the orbit key `k`
(the **natural strip** `[0, k]`); `2 r - 1` if the key of `x` is a key of `w` and not an orbit key;
and `2 r` otherwise, that is, if the key of `x` is any other orbit key or not a key of `w` at all.

**The orbit code** (`Label.orbitMap`, `Label.orbitCode`).  Bottom is fixed.  A label whose key is
an orbit key keeps its finite part and moves to its code block (`Label.moveToBlock`, the **block
move** to the block of a label); every other label goes to the grid point `ω * b + k` of its code
block `b`.  So a key of rank `r` that is not an orbit key is coded by the canonical point
`ω * (2 r - 1) + k`, the orbit of an orbit key of rank `r` lies in the block `2 r` above it, the
natural strip stays in the block `0`, and a label whose key is not a key of `w` goes to the top
`ω * 2 r + k` of the block `2 r`.

* **N0**: the orbit map is a witness bounded by grade `k` (`Label.isWitness_orbitMap`), sends only
  bottom to bottom, is never the formal top, is short at `k`, and takes values in the **code grid**
  (`Label.codeGrid k B`: bottom and the points `ω * b + f`, `b ≤ B`, `f ≤ k`) for `B` at least
  twice the number of cells.  On a labelling whose values are self-visible at `k` the orbit code is
  the canonical code (`Label.orbitCode_eq_canonicalCode`).
* **N1, idempotence** (`Label.orbitCode_orbitCode`), with no hypothesis on the values.
* **N2, prefix stability** (`Label.orbitCode_eq_of_min_eq`): labellings that agree capped at a cap
  `h` self-visible at `k` have the same code at every cell whose value lies below `h`.
* **N3, relative room** (`Label.min_orbitCode_eq`): if `w` agrees with an orbit-canonical `a`
  (`orbitCode k a = a`) capped at a cap `h` self-visible and **short** at `k` (finite part exactly
  `k`, or the formal top), so does the orbit code of `w`.  It fails at caps that are not short:
  `a = (ω * 2 + 1)`, `w = (ω * 5 + 3)` and `h = ω + 7` at `k = 2`
  (`VaughtConjecture.Extension.SmallArityOneExamples`, R6).
* **The orbit decoder** (`Label.orbitDecoder k w h`, N4): a label `x` goes to the larger of
  `min x h` and the **readings** of the cells `d` whose code has key at least `h`
  (`Label.cellReading`): bottom below the key of the code of `d`, the block move back to the
  block of `w d` on its strip when its key is an orbit key, and the key of `w d` otherwise.  For a
  cap `h` self-visible at `k` other than bottom it is a witness bounded by grade `k`
  (`Label.isWitness_orbitDecoder`); it reads the orbit code literally as `w`, the formal top
  included, when the code agrees with `w` capped at `h` (`Label.orbitDecoder_orbitCode`); and it
  keeps the cap at every label self-visible at `k` (`Label.min_orbitDecoder_eq`).
* **The natural strip** (`Label.min_orbitCode_gridPoint_zero`): the orbit code agrees with `w`
  capped at the least grid point `k`.  Were the natural strip moved, a decoder reading it would
  send the grid points below the moved strip to bottom.

Capped agreements of labellings with values in the code grid pass to agreement heights in the grid
of the same bound at short caps (`Label.min_agreementHeight_eq_of_isShort`): such a cap is in the
grid or above every value.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Witnesses are [Kni26, Definition 2.3.9] and visibility replacement is [Kni26, Definition 2.2.3];
lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.Label

open Finset Ordinal

variable {k : ℕ} {x y z h : Label.{u}}

/-! ### Points of a block -/

/-- The point `ω * b + n` of the block `b`, as a label. -/
private abbrev pt (b : Ordinal.{u}) (n : ℕ) : Label.{u} :=
  ((ω * b + n : Ordinal.{u}) : Label.{u})

/-- Visibility replacement of a point of a block replaces its finite part. -/
private theorem pt_visibilityReplace (b : Ordinal.{u}) (j i n : ℕ) :
    visibilityReplace j i (pt b n) = pt b (if n < j then i else n) := by
  rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

/-- Points of blocks compare lexicographically in block and finite part. -/
private theorem pt_le_pt_iff {b b' : Ordinal.{u}} {n n' : ℕ} :
    pt b n ≤ pt b' n' ↔ b < b' ∨ b = b' ∧ n ≤ n' := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff]

/-- A point of a block determines its block and its finite part. -/
private theorem pt_inj {b b' : Ordinal.{u}} {n n' : ℕ} (h : pt b n = pt b' n') :
    b = b' ∧ n = n' := by
  rcases pt_le_pt_iff.mp h.le with hb | ⟨rfl, hn⟩
  · rcases pt_le_pt_iff.mp h.ge with hb' | ⟨rfl, -⟩
    · exact absurd (hb.trans hb') (lt_irrefl _)
    · exact absurd hb (lt_irrefl _)
  · rcases pt_le_pt_iff.mp h.ge with hb' | ⟨-, hn'⟩
    · exact absurd hb' (lt_irrefl _)
    · exact ⟨rfl, le_antisymm hn hn'⟩

/-- A point of a lower block lies below every point of a higher block. -/
private theorem pt_lt_pt_of_lt {b b' : Ordinal.{u}} (hb : b < b') (n n' : ℕ) :
    pt b n < pt b' n' :=
  lt_of_le_of_ne (pt_le_pt_iff.mpr (.inl hb)) fun h ↦ absurd (pt_inj h).1 hb.ne

/-- A point of a block is self-visible at `k` exactly when its finite part is at least `k`. -/
private theorem isSelfVisible_pt {b : Ordinal.{u}} {n : ℕ} :
    IsSelfVisible k (pt b n) ↔ k ≤ n := by
  rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- A point of a block is short at `k` exactly when its finite part is at most `k`. -/
private theorem isShort_pt {b : Ordinal.{u}} {n : ℕ} : IsShort k (pt b n) ↔ n ≤ k := by
  rw [isShort_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- Every label is bottom, the formal top, or a point of a block. -/
private theorem eq_bot_or_eq_top_or_eq_pt (x : Label.{u}) :
    x = ⊥ ∨ x = ⊤ ∨ ∃ b n, x = pt b n := by
  induction x using recBotCoeTop with
  | bot => exact .inl rfl
  | top => exact .inr (.inl rfl)
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    exact .inr (.inr ⟨b, n, rfl⟩)

/-- A point of a block is not bottom. -/
private theorem pt_ne_bot (b : Ordinal.{u}) (n : ℕ) : pt b n ≠ ⊥ := WithBot.coe_ne_bot

/-- A point of a block is not the formal top. -/
private theorem pt_ne_top (b : Ordinal.{u}) (n : ℕ) : pt b n ≠ ⊤ := fun h ↦
  WithTop.coe_ne_top (WithBot.coe_injective h)

/-- A grid point is the point of its block with finite part `k`. -/
private theorem gridPoint_eq_pt (k b : ℕ) : gridPoint.{u} k b = pt (b : Ordinal.{u}) k := rfl

/-- The key of a point of a block: its finite part is raised to `k`. -/
private theorem visibilityReplace_self_pt (b : Ordinal.{u}) (n : ℕ) :
    visibilityReplace k k (pt b n) = pt b (max n k) := by
  rw [pt_visibilityReplace]
  congr 1
  split_ifs with hn <;> omega

/-! ### The block move -/

/-- The block index `o / ω` of an ordinal label `o` (zero at bottom and the formal top). -/
noncomputable def blockIndex (y : Label.{u}) : Ordinal.{u} :=
  WithTop.untopD 0 (WithBot.unbotD 0 y) / ω

/-- The **block move** to the block of `y`: an ordinal label `o` goes to the point of the block of
`y` with the finite part of `o`; bottom and the formal top are fixed. -/
noncomputable def moveToBlock (y : Label.{u}) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun o ↦ ω * blockIndex y + o % ω)

/-- The block index of a point is its block. -/
private theorem blockIndex_pt (b : Ordinal.{u}) (n : ℕ) : blockIndex (pt b n) = b :=
  omega0_mul_add_natCast_div b n

/-- The block move of a point keeps its finite part. -/
private theorem moveToBlock_pt (y : Label.{u}) (b : Ordinal.{u}) (n : ℕ) :
    moveToBlock y (pt b n) = pt (blockIndex y) n := by
  -- The block move of an ordinal label is the ordinal formula.
  change (((ω * blockIndex y + (ω * b + n) % ω : Ordinal.{u}) : WithTop Ordinal.{u}) :
    Label.{u}) = _
  rw [omega0_mul_add_natCast_mod]

/-- The block move of a point keeps its finite part, as ordinals. -/
theorem moveToBlock_omega0_mul_add (b b' : Ordinal.{u}) (n n' : ℕ) :
    moveToBlock ((ω * b + n : Ordinal.{u}) : Label.{u}) ((ω * b' + n' : Ordinal.{u}) : Label.{u}) =
      ((ω * b + n' : Ordinal.{u}) : Label.{u}) := by
  rw [moveToBlock_pt, blockIndex_pt]

/-- The block move fixes bottom. -/
@[simp] theorem moveToBlock_bot (y : Label.{u}) : moveToBlock y ⊥ = ⊥ := rfl

/-- The block move fixes the formal top. -/
@[simp] theorem moveToBlock_top (y : Label.{u}) : moveToBlock y ⊤ = ⊤ := rfl

/-- **The block move commutes with every visibility replacement.** -/
theorem moveToBlock_visibilityReplace (y x : Label.{u}) (j i : ℕ) :
    moveToBlock y (visibilityReplace j i x) = visibilityReplace j i (moveToBlock y x) := by
  rcases eq_bot_or_eq_top_or_eq_pt x with rfl | rfl | ⟨b, n, rfl⟩
  · rfl
  · rfl
  · rw [pt_visibilityReplace, moveToBlock_pt, moveToBlock_pt, pt_visibilityReplace]

/-- Shifting a shifted label: only the last block counts. -/
theorem moveToBlock_moveToBlock (y y' x : Label.{u}) :
    moveToBlock y (moveToBlock y' x) = moveToBlock y x := by
  rcases eq_bot_or_eq_top_or_eq_pt x with rfl | rfl | ⟨b, n, rfl⟩
  · rfl
  · rfl
  · rw [moveToBlock_pt, moveToBlock_pt, moveToBlock_pt]

/-- Two labels of one strip lie in one block. -/
private theorem blockIndex_eq_of_visibilityReplace_eq {b b' : Ordinal.{u}} {n n' : ℕ}
    (h : visibilityReplace k k (pt b n) = visibilityReplace k k (pt b' n')) : b = b' := by
  rw [visibilityReplace_self_pt, visibilityReplace_self_pt] at h
  exact (pt_inj h).1

/-- A label is fixed by the block move to the block of a label with the same key. -/
theorem moveToBlock_eq_self (hxy : visibilityReplace k k y = visibilityReplace k k x) :
    moveToBlock y x = x := by
  rcases eq_bot_or_eq_top_or_eq_pt x with rfl | rfl | ⟨b, n, rfl⟩
  · rfl
  · rfl
  · rcases eq_bot_or_eq_top_or_eq_pt y with rfl | rfl | ⟨b', n', rfl⟩
    · rw [visibilityReplace_bot, eq_comm, visibilityReplace_eq_bot_iff] at hxy
      exact absurd hxy (pt_ne_bot _ _)
    · rw [visibilityReplace_top, eq_comm, visibilityReplace_eq_top_iff] at hxy
      exact absurd hxy (pt_ne_top _ _)
    · rw [moveToBlock_pt, blockIndex_pt, blockIndex_eq_of_visibilityReplace_eq hxy]

/-- The block move is monotone on a strip. -/
private theorem moveToBlock_le_moveToBlock (hxy : x ≤ y)
    (hk : visibilityReplace k k x = visibilityReplace k k y) :
    moveToBlock z x ≤ moveToBlock z y := by
  rcases eq_bot_or_eq_top_or_eq_pt x with rfl | rfl | ⟨b, n, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases eq_bot_or_eq_top_or_eq_pt y with rfl | rfl | ⟨b', n', rfl⟩
    · exact absurd (le_bot_iff.mp hxy) (pt_ne_bot _ _)
    · exact le_top
    · have hb := blockIndex_eq_of_visibilityReplace_eq hk
      subst hb
      rw [moveToBlock_pt, moveToBlock_pt]
      rcases pt_le_pt_iff.mp hxy with h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · exact pt_le_pt_iff.mpr (.inr ⟨rfl, h⟩)

/-! ### Keys and the code block -/

variable {ι : Type*} {w w' a : ι → Label.{u}}

/-- The key of `x` is a **key** of `w` at grade `k`: some value of `w` other than bottom has the
key of `x`. -/
def IsKey (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Prop :=
  ∃ d, w d ≠ ⊥ ∧ visibilityReplace k k (w d) = visibilityReplace k k x

/-- The key of `x` is an **orbit key** of `w` at grade `k`: some value of `w` with the key of `x`
is not self-visible at `k`. -/
def IsOrbitKey (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Prop :=
  ∃ d, visibilityReplace k k (w d) = visibilityReplace k k x ∧ ¬ IsSelfVisible k (w d)

/-- Being a key depends only on the key. -/
theorem isKey_congr (hxy : visibilityReplace k k x = visibilityReplace k k y) :
    IsKey k w x ↔ IsKey k w y := by
  rw [IsKey, IsKey, hxy]

/-- Being an orbit key depends only on the key. -/
theorem isOrbitKey_congr (hxy : visibilityReplace k k x = visibilityReplace k k y) :
    IsOrbitKey k w x ↔ IsOrbitKey k w y := by
  rw [IsOrbitKey, IsOrbitKey, hxy]

/-- The value of `w` at a cell has a key of `w` exactly when it is not bottom. -/
theorem isKey_apply_iff {d : ι} : IsKey k w (w d) ↔ w d ≠ ⊥ := by
  refine ⟨fun ⟨e, he, hed⟩ hd ↦ he ?_, fun hd ↦ ⟨d, hd, rfl⟩⟩
  rwa [hd, visibilityReplace_bot, visibilityReplace_eq_bot_iff] at hed

/-- A label whose key is a key of `w` is not bottom. -/
theorem IsKey.ne_bot (hx : IsKey k w x) : x ≠ ⊥ := by
  obtain ⟨d, hd, hdx⟩ := hx
  rintro rfl
  rw [visibilityReplace_bot, visibilityReplace_eq_bot_iff] at hdx
  exact hd hdx

/-- An orbit key is a key. -/
theorem IsOrbitKey.isKey (hx : IsOrbitKey k w x) : IsKey k w x := by
  obtain ⟨d, hdx, hd⟩ := hx
  exact ⟨d, fun h ↦ hd (h ▸ isSelfVisible_bot k), hdx⟩

/-- A value of `w` that is not self-visible at `k` has an orbit key. -/
theorem isOrbitKey_of_not_isSelfVisible {d : ι} (hd : ¬ IsSelfVisible k (w d)) :
    IsOrbitKey k w (w d) :=
  ⟨d, rfl, hd⟩

/-- A label whose key is an orbit key is a point `ω * b + n` with `n ≤ k`, of key `ω * b + k`. -/
private theorem IsOrbitKey.eq_pt (hx : IsOrbitKey k w x) :
    ∃ b n, n ≤ k ∧ x = pt b n ∧ visibilityReplace k k x = pt b k := by
  have hne := hx.isKey.ne_bot
  obtain ⟨d, hdx, hd⟩ := hx
  rcases eq_bot_or_eq_top_or_eq_pt (w d) with hw | hw | ⟨b', n', hw⟩
  · exact absurd (hw ▸ isSelfVisible_bot k) hd
  · exact absurd (hw ▸ isSelfVisible_top k) hd
  rw [hw, isSelfVisible_pt, not_le] at hd
  rw [hw, visibilityReplace_self_pt, max_eq_right hd.le] at hdx
  rcases eq_bot_or_eq_top_or_eq_pt x with rfl | rfl | ⟨b, n, rfl⟩
  · exact absurd rfl hne
  · rw [visibilityReplace_top] at hdx
    exact absurd hdx (pt_ne_top _ _)
  · rw [visibilityReplace_self_pt] at hdx ⊢
    obtain ⟨rfl, hn⟩ := pt_inj hdx
    exact ⟨b', n, by omega, rfl, by rw [← hn]⟩

/-- A label whose key is an orbit key is not the formal top. -/
theorem IsOrbitKey.ne_top (hx : IsOrbitKey k w x) : x ≠ ⊤ := by
  obtain ⟨b, n, -, rfl, -⟩ := hx.eq_pt
  exact pt_ne_top _ _

variable [Fintype ι]

/-- The **key rank** of `x` for `w` at grade `k`: the number of distinct keys `vr k k (w d)` of the
values of `w` other than bottom that are at most the key `vr k k x` of `x`. -/
noncomputable def keyRank (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : ℕ :=
  valueRank (fun d ↦ visibilityReplace k k (w d)) (visibilityReplace k k x)

open Classical in
/-- The **code block** of `x` for `w` at grade `k`, with `r` the key rank of `x`: the block `0` of
the natural strip when the key of `x` is the orbit key `k`; the block `2 r` when it is any other
orbit key or not a key of `w`; and the block `2 r - 1` of the canonical point of rank `r` when it
is a key of `w` and not an orbit key. -/
noncomputable def codeBlock (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : ℕ :=
  if IsOrbitKey k w x ∧ visibilityReplace k k x = gridPoint k 0 then 0
  else 2 * keyRank k w x - if IsKey k w x ∧ ¬ IsOrbitKey k w x then 1 else 0

open Classical in
/-- The **orbit map** of a labelling `w` at grade `k`: bottom is fixed; a label whose key is an
orbit key of `w` moves to its code block with its finite part (the block move); every other label
goes to the grid point `ω * b + k` of its code block `b`. -/
noncomputable def orbitMap (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥
  else if IsOrbitKey k w x then moveToBlock (gridPoint k (codeBlock k w x)) x
  else gridPoint k (codeBlock k w x)

/-- The **orbit code** of a labelling `w` at grade `k`: the orbit map applied to its values. -/
noncomputable def orbitCode (k : ℕ) (w : ι → Label.{u}) : ι → Label.{u} :=
  orbitMap k w ∘ w

/-- The orbit code at a cell. -/
theorem orbitCode_apply (d : ι) : orbitCode k w d = orbitMap k w (w d) := rfl

/-- The key rank depends only on the key. -/
theorem keyRank_congr (hxy : visibilityReplace k k x = visibilityReplace k k y) :
    keyRank k w x = keyRank k w y := by
  rw [keyRank, keyRank, hxy]

/-- The code block depends only on the key. -/
theorem codeBlock_congr (hxy : visibilityReplace k k x = visibilityReplace k k y) :
    codeBlock k w x = codeBlock k w y := by
  unfold codeBlock
  rw [keyRank_congr hxy, propext (isKey_congr (w := w) hxy),
    propext (isOrbitKey_congr (w := w) hxy), hxy]

/-- The key rank is monotone in the key. -/
theorem keyRank_le_keyRank (hxy : visibilityReplace k k x ≤ visibilityReplace k k y) :
    keyRank k w x ≤ keyRank k w y :=
  monotone_valueRank _ hxy

/-- The key rank grows strictly up to a key of `w`. -/
theorem keyRank_lt_keyRank (hy : IsKey k w y)
    (hxy : visibilityReplace k k x < visibilityReplace k k y) :
    keyRank k w x < keyRank k w y := by
  obtain ⟨d, hd, hdy⟩ := hy
  rw [keyRank, keyRank, ← hdy]
  exact valueRank_lt_valueRank (w := fun d ↦ visibilityReplace k k (w d))
    (by rwa [Ne, visibilityReplace_eq_bot_iff]) (hdy ▸ hxy)

/-- The key rank is at most the number of cells. -/
theorem keyRank_le_card (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) :
    keyRank k w x ≤ Fintype.card ι :=
  valueRank_le_card _ _

/-- A key of `w` has positive key rank. -/
theorem one_le_keyRank (hx : IsKey k w x) : 1 ≤ keyRank k w x := by
  have h := keyRank_lt_keyRank (x := ⊥) hx (by
    rw [visibilityReplace_bot]
    exact bot_lt_iff_ne_bot.mpr (by rw [Ne, visibilityReplace_eq_bot_iff]; exact hx.ne_bot))
  omega

/-- The code block is at most twice the key rank. -/
theorem codeBlock_le (k : ℕ) (w : ι → Label.{u}) (x : Label.{u}) :
    codeBlock k w x ≤ 2 * keyRank k w x := by
  unfold codeBlock
  split_ifs <;> omega

/-- Off the natural strip, the code block is at least `2 r - 1`, for the key rank `r`. -/
theorem le_codeBlock (hx : ¬ (IsOrbitKey k w x ∧ visibilityReplace k k x = gridPoint k 0)) :
    2 * keyRank k w x - 1 ≤ codeBlock k w x := by
  unfold codeBlock
  rw [ite_eq_right hx]
  split_ifs <;> omega

/-- The code block of an orbit key off the natural strip is twice its key rank. -/
theorem codeBlock_of_isOrbitKey (hx : IsOrbitKey k w x)
    (hn : visibilityReplace k k x ≠ gridPoint k 0) :
    codeBlock k w x = 2 * keyRank k w x := by
  unfold codeBlock
  rw [ite_eq_right fun h ↦ hn h.2, ite_eq_right fun h ↦ h.2 hx]
  omega

/-- The code block of a key that is not an orbit key is `2 r - 1`, for its key rank `r`. -/
theorem codeBlock_of_not_isOrbitKey (hk : IsKey k w x) (hx : ¬ IsOrbitKey k w x) :
    codeBlock k w x = 2 * keyRank k w x - 1 := by
  unfold codeBlock
  rw [ite_eq_right fun h ↦ hx h.1, ite_eq_left ⟨hk, hx⟩]

/-- The natural strip has code block `0`. -/
theorem codeBlock_of_natural (hx : IsOrbitKey k w x)
    (hn : visibilityReplace k k x = gridPoint k 0) : codeBlock k w x = 0 := by
  unfold codeBlock
  rw [ite_eq_left ⟨hx, hn⟩]

/-- A label other than bottom has a key at least the least grid point. -/
theorem gridPoint_zero_le_visibilityReplace (hx : x ≠ ⊥) :
    gridPoint.{u} k 0 ≤ visibilityReplace k k x :=
  gridPoint_zero_le (isSelfVisible_visibilityReplace_self k x)
    (by rwa [Ne, visibilityReplace_eq_bot_iff])

/-- **The code block grows strictly up to a key of `w`.** -/
theorem codeBlock_lt_codeBlock (hx : x ≠ ⊥) (hy : IsKey k w y)
    (hxy : visibilityReplace k k x < visibilityReplace k k y) :
    codeBlock k w x < codeBlock k w y := by
  have hr := keyRank_lt_keyRank hy hxy
  have h1 := codeBlock_le k w x
  have hn : ¬ (IsOrbitKey k w y ∧ visibilityReplace k k y = gridPoint k 0) := fun h ↦
    absurd ((gridPoint_zero_le_visibilityReplace hx).trans_lt hxy) (by rw [h.2]; exact lt_irrefl _)
  have h2 := le_codeBlock hn
  omega

/-- **On the keys of `w` the code block is an order embedding.** -/
theorem codeBlock_le_codeBlock_iff (hx : IsKey k w x) (hy : IsKey k w y) :
    codeBlock k w x ≤ codeBlock k w y ↔ visibilityReplace k k x ≤ visibilityReplace k k y := by
  refine ⟨fun h ↦ not_lt.mp fun hlt ↦ ?_, fun h ↦ ?_⟩
  · exact absurd h (not_le.mpr (codeBlock_lt_codeBlock hy.ne_bot hx hlt))
  · rcases h.lt_or_eq with h | h
    · exact (codeBlock_lt_codeBlock hx.ne_bot hy h).le
    · exact (codeBlock_congr h).le

/-- On the keys of `w`, equal code blocks are equal keys. -/
theorem visibilityReplace_eq_of_codeBlock_eq (hx : IsKey k w x) (hy : IsKey k w y)
    (h : codeBlock k w x = codeBlock k w y) :
    visibilityReplace k k x = visibilityReplace k k y :=
  le_antisymm ((codeBlock_le_codeBlock_iff hx hy).mp h.le)
    ((codeBlock_le_codeBlock_iff hy hx).mp h.ge)

/-! ### The orbit map -/

/-- The orbit map fixes bottom. -/
@[simp] theorem orbitMap_bot : orbitMap k w ⊥ = ⊥ := ite_eq_left rfl

/-- The orbit map at a label whose key is an orbit key. -/
theorem orbitMap_of_isOrbitKey (hx : IsOrbitKey k w x) :
    orbitMap k w x = moveToBlock (gridPoint k (codeBlock k w x)) x := by
  rw [orbitMap, ite_eq_right hx.isKey.ne_bot, ite_eq_left hx]

/-- The orbit map at a label other than bottom whose key is not an orbit key. -/
theorem orbitMap_of_not_isOrbitKey (hx0 : x ≠ ⊥) (hx : ¬ IsOrbitKey k w x) :
    orbitMap k w x = gridPoint k (codeBlock k w x) := by
  rw [orbitMap, ite_eq_right hx0, ite_eq_right hx]

/-- **The shape of the orbit map**: a label other than bottom goes to a point of its code block
with finite part at most `k`, exactly `k` off the orbit keys, and the finite part of the label on
an orbit key. -/
private theorem orbitMap_eq_pt (hx0 : x ≠ ⊥) :
    ∃ n ≤ k, orbitMap k w x = pt (codeBlock k w x : Ordinal.{u}) n ∧
      (IsOrbitKey k w x → ∃ b, x = pt b n) ∧ (¬ IsOrbitKey k w x → n = k) := by
  by_cases hx : IsOrbitKey k w x
  · obtain ⟨b, n, hn, rfl, -⟩ := hx.eq_pt
    refine ⟨n, hn, ?_, fun _ ↦ ⟨b, rfl⟩, fun h ↦ absurd hx h⟩
    rw [orbitMap_of_isOrbitKey hx, moveToBlock_pt, gridPoint_eq_pt, blockIndex_pt]
  · exact ⟨k, le_rfl, orbitMap_of_not_isOrbitKey hx0 hx, fun h ↦ absurd h hx, fun _ ↦ rfl⟩

/-- The orbit map sends a label to bottom exactly when it is bottom. -/
@[simp] theorem orbitMap_eq_bot_iff : orbitMap k w x = ⊥ ↔ x = ⊥ := by
  refine ⟨fun h ↦ by_contra fun hx0 ↦ ?_, by rintro rfl; exact orbitMap_bot⟩
  obtain ⟨n, -, he, -⟩ := orbitMap_eq_pt (w := w) hx0
  exact pt_ne_bot _ _ (he ▸ h)

/-- **The orbit map is never the formal top.** -/
theorem orbitMap_ne_top (x : Label.{u}) : orbitMap k w x ≠ ⊤ := by
  by_cases hx0 : x = ⊥
  · rw [hx0, orbitMap_bot]
    exact bot_ne_top
  · obtain ⟨n, -, he, -⟩ := orbitMap_eq_pt (w := w) hx0
    rw [he]
    exact pt_ne_top _ _

/-- **The orbit map is short at `k`.** -/
theorem isShort_orbitMap (x : Label.{u}) : IsShort k (orbitMap k w x) := by
  by_cases hx0 : x = ⊥
  · rw [hx0, orbitMap_bot]
    exact isShort_bot k
  · obtain ⟨n, hn, he, -⟩ := orbitMap_eq_pt (w := w) hx0
    rw [he]
    exact isShort_pt.mpr hn

/-- **The key of the orbit map is the grid point of the code block.** -/
theorem visibilityReplace_orbitMap (hx0 : x ≠ ⊥) :
    visibilityReplace k k (orbitMap k w x) = gridPoint k (codeBlock k w x) := by
  obtain ⟨n, hn, he, -⟩ := orbitMap_eq_pt (w := w) hx0
  rw [he, visibilityReplace_self_pt, max_eq_right hn, gridPoint_eq_pt]

/-- The orbit map lies at or above the start of its code block. -/
private theorem pt_zero_le_orbitMap (hx0 : x ≠ ⊥) :
    pt (codeBlock k w x : Ordinal.{u}) 0 ≤ orbitMap k w x := by
  obtain ⟨n, -, he, -⟩ := orbitMap_eq_pt (w := w) hx0
  rw [he]
  exact pt_le_pt_iff.mpr (.inr ⟨rfl, Nat.zero_le n⟩)

/-- The orbit map lies at or below the grid point of its code block. -/
theorem orbitMap_le_gridPoint (x : Label.{u}) :
    orbitMap k w x ≤ gridPoint k (codeBlock k w x) := by
  by_cases hx0 : x = ⊥
  · rw [hx0, orbitMap_bot]
    exact bot_le
  · obtain ⟨n, hn, he, -⟩ := orbitMap_eq_pt (w := w) hx0
    rw [he, gridPoint_eq_pt]
    exact pt_le_pt_iff.mpr (.inr ⟨rfl, hn⟩)

/-- The orbit map keeps self-visibility at `k`, and keeps the lack of it on the orbit keys. -/
theorem isSelfVisible_orbitMap_iff (hx0 : x ≠ ⊥) :
    IsSelfVisible k (orbitMap k w x) ↔ ¬ IsOrbitKey k w x ∨ IsSelfVisible k x := by
  obtain ⟨n, -, he, hor, hnor⟩ := orbitMap_eq_pt (w := w) hx0
  rw [he, isSelfVisible_pt]
  by_cases hx : IsOrbitKey k w x
  · obtain ⟨b, rfl⟩ := hor hx
    rw [isSelfVisible_pt]
    exact ⟨fun h ↦ .inr h, fun h ↦ h.resolve_left (not_not.mpr hx)⟩
  · exact ⟨fun _ ↦ .inl hx, fun _ ↦ (hnor hx).ge⟩

/-- **The orbit map is monotone.** -/
theorem monotone_orbitMap (k : ℕ) (w : ι → Label.{u}) : Monotone (orbitMap k w) := by
  intro x y hxy
  by_cases hx0 : x = ⊥
  · rw [hx0, orbitMap_bot]
    exact bot_le
  have hy0 : y ≠ ⊥ := fun hy ↦ hx0 (le_bot_iff.mp (hy ▸ hxy))
  have hv := monotone_visibilityReplace (k := k) le_rfl hxy
  rcases hv.lt_or_eq with hlt | heq
  · -- A larger key: a larger code block, or the same block with the grid point.
    have hblock : codeBlock k w x < codeBlock k w y ∨
        codeBlock k w x = codeBlock k w y ∧ ¬ IsOrbitKey k w y := by
      by_cases hy : IsKey k w y
      · exact .inl (codeBlock_lt_codeBlock hx0 hy hlt)
      · have hyo : ¬ IsOrbitKey k w y := fun h ↦ hy h.isKey
        have hcy : codeBlock k w y = 2 * keyRank k w y := by
          unfold codeBlock
          rw [ite_eq_right fun h ↦ hyo h.1, ite_eq_right fun h ↦ hy h.1]
          omega
        have := keyRank_le_keyRank (w := w) hlt.le
        have := codeBlock_le k w x
        rcases (show codeBlock k w x ≤ codeBlock k w y by omega).lt_or_eq with h | h
        exacts [.inl h, .inr ⟨h, hyo⟩]
    rcases hblock with hb | ⟨hb, hyo⟩
    · refine (orbitMap_le_gridPoint x).trans (le_trans ?_ (pt_zero_le_orbitMap hy0))
      rw [gridPoint_eq_pt]
      exact (pt_lt_pt_of_lt (by exact_mod_cast hb) _ _).le
    · rw [orbitMap_of_not_isOrbitKey hy0 hyo, ← hb]
      exact orbitMap_le_gridPoint x
  · -- The same key: the same block, and the block move is monotone on a strip.
    by_cases hx : IsOrbitKey k w x
    · have hy : IsOrbitKey k w y := (isOrbitKey_congr heq).mp hx
      rw [orbitMap_of_isOrbitKey hx, orbitMap_of_isOrbitKey hy, codeBlock_congr heq]
      exact moveToBlock_le_moveToBlock hxy heq
    · have hy : ¬ IsOrbitKey k w y := fun h ↦ hx ((isOrbitKey_congr heq).mpr h)
      rw [orbitMap_of_not_isOrbitKey hx0 hx, orbitMap_of_not_isOrbitKey hy0 hy,
        codeBlock_congr heq]

/-- **N0: the orbit map is a witness bounded by grade `k`.** -/
theorem isWitness_orbitMap (k : ℕ) (w : ι → Label.{u}) :
    IsWitness (stepSuppressor.{u} k) (orbitMap k w) where
  antitone := (IsWitness.id_step k).antitone
  isSelfVisible := (IsWitness.id_step k).isSelfVisible
  map_bot := orbitMap_bot
  monotone := monotone_orbitMap k w
  visibilityReplace_comm x j hx i hi := by
    by_cases hj : j ≤ k
    · have hkey : visibilityReplace k k (visibilityReplace j i x) = visibilityReplace k k x :=
        visibilityReplace_self_visibilityReplace_of_le hi hj x
      by_cases hx0 : x = ⊥
      · simp [hx0]
      have hx0' : visibilityReplace j i x ≠ ⊥ := by rwa [Ne, visibilityReplace_eq_bot_iff]
      by_cases ho : IsOrbitKey k w x
      · rw [orbitMap_of_isOrbitKey ho, orbitMap_of_isOrbitKey ((isOrbitKey_congr hkey).mpr ho),
          codeBlock_congr hkey, moveToBlock_visibilityReplace]
      · rw [orbitMap_of_not_isOrbitKey hx0 ho,
          orbitMap_of_not_isOrbitKey hx0' fun h ↦ ho ((isOrbitKey_congr hkey).mp h),
          codeBlock_congr hkey]
        exact (((isSelfVisible_gridPoint k _).mono hj).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (not_le.mp hj), le_bot_iff, orbitMap_eq_bot_iff] at hx
      simp [hx]

/-! ### The orbit code -/

/-- **The orbit code is bottom exactly where the labelling is.** -/
@[simp] theorem orbitCode_eq_bot_iff {d : ι} : orbitCode k w d = ⊥ ↔ w d = ⊥ :=
  orbitMap_eq_bot_iff

/-- **The orbit code is never the formal top.** -/
theorem orbitCode_ne_top (d : ι) : orbitCode k w d ≠ ⊤ := orbitMap_ne_top _

/-- **The orbit code is short at `k`.** -/
theorem isShort_orbitCode (d : ι) : IsShort k (orbitCode k w d) := isShort_orbitMap _

/-- **On the values of `w`, the keys of the orbit code are ordered as the keys of `w`.** -/
theorem visibilityReplace_orbitCode_le_iff {d e : ι} (hd : w d ≠ ⊥) (he : w e ≠ ⊥) :
    visibilityReplace k k (orbitCode k w e) ≤ visibilityReplace k k (orbitCode k w d) ↔
      visibilityReplace k k (w e) ≤ visibilityReplace k k (w d) := by
  rw [orbitCode_apply, orbitCode_apply, visibilityReplace_orbitMap he,
    visibilityReplace_orbitMap hd, gridPoint_le_gridPoint]
  exact codeBlock_le_codeBlock_iff (isKey_apply_iff.mpr he) (isKey_apply_iff.mpr hd)

/-- Grid points of one grade are equal exactly when their blocks are. -/
private theorem gridPoint_inj {b b' : ℕ} : gridPoint.{u} k b = gridPoint k b' ↔ b = b' :=
  ⟨fun h ↦ le_antisymm (gridPoint_le_gridPoint.mp h.le) (gridPoint_le_gridPoint.mp h.ge),
    fun h ↦ h ▸ rfl⟩

/-- The key of the orbit code at a cell. -/
private theorem visibilityReplace_orbitCode_eq (d : ι) :
    visibilityReplace k k (orbitCode k w d) =
      if w d = ⊥ then ⊥ else gridPoint k (codeBlock k w (w d)) := by
  by_cases hd : w d = ⊥
  · rw [ite_eq_left hd, orbitCode_eq_bot_iff.mpr hd, visibilityReplace_bot]
  · rw [ite_eq_right hd]
    exact visibilityReplace_orbitMap hd

/-- **The orbit code keeps the key ranks.** -/
theorem keyRank_orbitCode {d : ι} (hd : w d ≠ ⊥) :
    keyRank k (orbitCode k w) (orbitCode k w d) = keyRank k w (w d) := by
  classical
  have hvv (x : Label.{u}) :
      visibilityReplace k k (visibilityReplace k k x) = visibilityReplace k k x :=
    visibilityReplace_self_visibilityReplace le_rfl x
  set φ : Label.{u} → Label.{u} := fun K ↦ if K = ⊥ then ⊥ else gridPoint k (codeBlock k w K)
    with hφ_def
  have hφ (e : ι) :
      visibilityReplace k k (orbitCode k w e) = φ (visibilityReplace k k (w e)) := by
    rw [visibilityReplace_orbitCode_eq, hφ_def]
    simp only [visibilityReplace_eq_bot_iff]
    split_ifs
    · rfl
    · rw [codeBlock_congr (hvv (w e)).symm]
  -- A key of `w` has a key of `w`, and the grid point of its code block.
  have hkey {K : Label.{u}} (hK : K ∈ univ.image fun e ↦ visibilityReplace k k (w e))
      (hK0 : K ≠ ⊥) : IsKey k w K ∧ visibilityReplace k k K = K := by
    obtain ⟨e, -, rfl⟩ := mem_image.mp hK
    refine ⟨⟨e, fun he ↦ hK0 (by rw [he, visibilityReplace_bot]), (hvv _).symm⟩, hvv _⟩
  have hφne {K : Label.{u}} (hK0 : K ≠ ⊥) : φ K = gridPoint k (codeBlock k w K) := ite_eq_right hK0
  have hd' : visibilityReplace k k (w d) ≠ ⊥ := by rwa [Ne, visibilityReplace_eq_bot_iff]
  have hdkey := hkey (mem_image_of_mem _ (mem_univ d)) hd'
  have himage : (univ.image fun e ↦ visibilityReplace k k (orbitCode k w e)) =
      (univ.image fun e ↦ visibilityReplace k k (w e)).image φ := by
    rw [image_image]
    exact image_congr fun e _ ↦ hφ e
  rw [keyRank, keyRank, valueRank, valueRank, himage, filter_image, hφ d, card_image_of_injOn]
  · refine congrArg Finset.card (filter_congr fun K hK ↦ ?_)
    by_cases hK0 : K = ⊥
    · simp [hK0, φ]
    obtain ⟨hKk, hKv⟩ := hkey hK hK0
    rw [hφne hK0, hφne hd', gridPoint_le_gridPoint, codeBlock_le_codeBlock_iff hKk hdkey.1, hKv,
      hdkey.2]
    exact ⟨fun h ↦ ⟨hK0, h.2⟩, fun h ↦ ⟨gridPoint_ne_bot _ _, h.2⟩⟩
  · intro K hK K' hK' hKK'
    have hK0 : K ≠ ⊥ := fun h ↦ (mem_filter.mp hK).2.1 (by rw [h]; rfl)
    have hK0' : K' ≠ ⊥ := fun h ↦ (mem_filter.mp hK').2.1 (by rw [h]; rfl)
    obtain ⟨hKk, hKv⟩ := hkey (mem_filter.mp hK).1 hK0
    obtain ⟨hKk', hKv'⟩ := hkey (mem_filter.mp hK').1 hK0'
    have h := visibilityReplace_eq_of_codeBlock_eq hKk hKk'
      (gridPoint_inj.mp ((hφne hK0).symm.trans (hKK'.trans (hφne hK0'))))
    rwa [hKv, hKv'] at h

/-- **N1, idempotence**: the orbit code of an orbit code is itself. -/
theorem orbitCode_orbitCode : orbitCode k (orbitCode k w) = orbitCode k w := by
  funext d
  by_cases hd : w d = ⊥
  · have hc : orbitCode k w d = ⊥ := orbitCode_eq_bot_iff.mpr hd
    rw [hc, orbitCode_eq_bot_iff, hc]
  have hc : orbitCode k w d ≠ ⊥ := by rwa [Ne, orbitCode_eq_bot_iff]
  have hkey : IsKey k (orbitCode k w) (orbitCode k w d) := isKey_apply_iff.mpr hc
  have hdkey : IsKey k w (w d) := isKey_apply_iff.mpr hd
  have hvc : visibilityReplace k k (orbitCode k w d) = gridPoint k (codeBlock k w (w d)) :=
    visibilityReplace_orbitMap hd
  -- The codes with the key of the code of `d` are the codes of the values with the key of `w d`.
  have hsame {e : ι} (he : w e ≠ ⊥) :
      visibilityReplace k k (orbitCode k w e) = visibilityReplace k k (orbitCode k w d) ↔
        visibilityReplace k k (w e) = visibilityReplace k k (w d) := by
    rw [le_antisymm_iff, le_antisymm_iff, visibilityReplace_orbitCode_le_iff hd he,
      visibilityReplace_orbitCode_le_iff he hd]
  have horb : IsOrbitKey k (orbitCode k w) (orbitCode k w d) ↔ IsOrbitKey k w (w d) := by
    constructor
    · rintro ⟨e, hek, hesv⟩
      have he : w e ≠ ⊥ := fun he ↦ hesv (orbitCode_eq_bot_iff.mpr he ▸ isSelfVisible_bot k)
      have := (not_iff_not.mpr (isSelfVisible_orbitMap_iff he)).mp hesv
      push Not at this
      exact ⟨e, (hsame he).mp hek, this.2⟩
    · rintro ⟨e, hek, hesv⟩
      have he : w e ≠ ⊥ := fun he ↦ hesv (he ▸ isSelfVisible_bot k)
      refine ⟨e, (hsame he).mpr hek, fun h ↦ ?_⟩
      rcases (isSelfVisible_orbitMap_iff he).mp h with h | h
      · exact h (isOrbitKey_of_not_isSelfVisible hesv)
      · exact hesv h
  have hcb : codeBlock k (orbitCode k w) (orbitCode k w d) = codeBlock k w (w d) := by
    by_cases ho : IsOrbitKey k w (w d)
    · by_cases hn : visibilityReplace k k (w d) = gridPoint k 0
      · rw [codeBlock_of_natural ho hn, codeBlock_of_natural (horb.mpr ho)]
        rw [hvc, codeBlock_of_natural ho hn]
      · rw [codeBlock_of_isOrbitKey ho hn, codeBlock_of_isOrbitKey (horb.mpr ho),
          keyRank_orbitCode hd]
        rw [hvc, Ne, gridPoint_inj, codeBlock_of_isOrbitKey ho hn]
        have := one_le_keyRank hdkey
        omega
    · rw [codeBlock_of_not_isOrbitKey hdkey ho,
        codeBlock_of_not_isOrbitKey hkey (mt horb.mp ho), keyRank_orbitCode hd]
  -- Unfold both orbit codes at `d` to the orbit maps of the values.
  change orbitMap k (orbitCode k w) (orbitCode k w d) = orbitMap k w (w d)
  by_cases ho : IsOrbitKey k w (w d)
  · rw [orbitMap_of_isOrbitKey (horb.mpr ho), hcb, orbitCode_apply, orbitMap_of_isOrbitKey ho,
      moveToBlock_moveToBlock]
  · rw [orbitMap_of_not_isOrbitKey hc (mt horb.mp ho), hcb, orbitMap_of_not_isOrbitKey hd ho]

/-- The orbit map at `x` depends only on the key rank of `x` and on whether it is a key and an
orbit key. -/
theorem orbitMap_congr (hrank : keyRank k w x = keyRank k w' x) (hkey : IsKey k w x ↔ IsKey k w' x)
    (horb : IsOrbitKey k w x ↔ IsOrbitKey k w' x) : orbitMap k w x = orbitMap k w' x := by
  unfold orbitMap codeBlock
  rw [hrank, propext hkey, propext horb]

omit [Fintype ι] in
/-- Below a cap self-visible at `k`, a key at most the key of a value below the cap is a key of
every labelling agreeing capped at the cap. -/
private theorem exists_visibilityReplace_eq (hh : IsSelfVisible k h)
    (hag : ∀ d, min (w d) h = min (w' d) h) {d : ι} (hd : w d < h) {e : ι}
    (he : visibilityReplace k k (w e) ≤ visibilityReplace k k (w d)) :
    ∃ e', visibilityReplace k k (w' e') = visibilityReplace k k (w e) := by
  have hdh : visibilityReplace k k (w d) ≤ h :=
    (monotone_visibilityReplace le_rfl hd.le).trans_eq hh
  rcases lt_or_ge (w e) h with heh | heh
  · exact ⟨e, by rw [eq_of_min_eq_of_lt (hag e) heh]⟩
  · refine ⟨d, ?_⟩
    rw [eq_of_min_eq_of_lt (hag d) hd]
    exact (le_antisymm he (hdh.trans (heh.trans (le_visibilityReplace (Nat.le_succ k) _)))).symm

/-- **N2, prefix stability**: two labellings that agree capped at a cap `h` self-visible at `k`
have the same orbit code at every cell whose value lies below `h`. -/
theorem orbitCode_eq_of_min_eq (hh : IsSelfVisible k h) (hag : ∀ d, min (w d) h = min (w' d) h)
    {d : ι} (hd : w d < h) : orbitCode k w d = orbitCode k w' d := by
  have hwd : w' d = w d := eq_of_min_eq_of_lt (hag d) hd
  have hd' : w' d < h := hwd ▸ hd
  have hag' : ∀ e, min (w' e) h = min (w e) h := fun e ↦ (hag e).symm
  rw [orbitCode_apply, orbitCode_apply, hwd]
  by_cases hd0 : w d = ⊥
  · rw [hd0, orbitMap_bot, orbitMap_bot]
  have hdh : visibilityReplace k k (w d) ≤ h :=
    (monotone_visibilityReplace le_rfl hd.le).trans_eq hh
  refine orbitMap_congr ?_ ?_ ?_
  · rw [keyRank, keyRank, valueRank, valueRank]
    congr 1
    ext K
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨e, rfl⟩, hK0, hKd⟩
      exact ⟨exists_visibilityReplace_eq hh hag hd hKd, hK0, hKd⟩
    · rintro ⟨⟨e, rfl⟩, hK0, hKd⟩
      have hKd' : visibilityReplace k k (w' e) ≤ visibilityReplace k k (w' d) := hwd ▸ hKd
      obtain ⟨e', he'⟩ := exists_visibilityReplace_eq hh hag' hd' hKd'
      exact ⟨⟨e', he'⟩, hK0, hKd⟩
  · rw [isKey_apply_iff]
    exact ⟨fun _ ↦ ⟨d, hwd ▸ hd0, by rw [hwd]⟩, fun _ ↦ hd0⟩
  · -- An orbit witness lies below `h`, where the two labellings agree.
    have hlow {v v' : ι → Label.{u}} (hagv : ∀ e, min (v e) h = min (v' e) h) {e : ι}
        (hek : visibilityReplace k k (v e) = visibilityReplace k k (w d))
        (hesv : ¬ IsSelfVisible k (v e)) : v' e = v e := by
      refine eq_of_min_eq_of_lt (hagv e) (lt_of_le_of_ne ?_ fun h' ↦ hesv (h' ▸ hh))
      exact (le_visibilityReplace (Nat.le_succ k) _).trans (hek.trans_le hdh)
    constructor
    · rintro ⟨e, hek, hesv⟩
      exact ⟨e, by rw [hlow hag hek hesv, hek], by rwa [hlow hag hek hesv]⟩
    · rintro ⟨e, hek, hesv⟩
      exact ⟨e, by rw [hlow hag' hek hesv, hek], by rwa [hlow hag' hek hesv]⟩

/-- A cap self-visible and short at `k`, other than bottom and the formal top, is a grid point
`ω * c + k`. -/
private theorem exists_eq_pt_of_isShort (hh : IsSelfVisible k h) (hs : IsShort k h)
    (h0 : h ≠ ⊥) (htop : h ≠ ⊤) : ∃ c, h = pt c k := by
  rcases eq_bot_or_eq_top_or_eq_pt h with rfl | rfl | ⟨c, n, rfl⟩
  · exact absurd rfl h0
  · exact absurd rfl htop
  · exact ⟨c, by rw [le_antisymm (isShort_pt.mp hs) (isSelfVisible_pt.mp hh)]⟩

/-- **N3, relative room.**  Let `a` be orbit-canonical (`orbitCode k a = a`) and let `w` agree
with `a` capped at a cap `h` self-visible and short at `k`.  Then the orbit code of `w` agrees with
`a` capped at `h`.  Below `h` this is prefix stability.  At a cell where `w` is at least `h`, write
`h = ω * c + k` and let `R` be the number of keys of `w` below `h`, shared with `a`.  If some value
below `h` has the key `h`, it is a value of `a`, and canonical in `a`, so the orbit of `h` is in the
block `c`; the value `h` itself is coded by `h`, and any larger key by a larger code block.
Otherwise the least value of `a` at least `h` has key rank `R + 1` in `a`, so `c ≤ 2 R + 1`, while
every value of `w` at least `h` has code block at least `2 R + 1`, and exactly `2 R + 1` only off
the orbit keys, where its code is `ω * c + k`. -/
theorem min_orbitCode_eq (hh : IsSelfVisible k h) (hs : IsShort k h) (ha : orbitCode k a = a)
    (hag : ∀ d, min (w d) h = min (a d) h) (d : ι) :
    min (orbitCode k w d) h = min (a d) h := by
  classical
  have haa (e : ι) : orbitMap k a (a e) = a e := congrFun ha e
  rcases lt_or_ge (w d) h with hd | hd
  · rw [orbitCode_eq_of_min_eq hh hag hd, orbitCode_apply, haa]
  have had : h ≤ a d := le_of_min_eq_of_le (hag d) hd
  rw [min_eq_right had]
  refine min_eq_right ?_
  rw [orbitCode_apply]
  by_cases h0 : h = ⊥
  · rw [h0]
    exact bot_le
  by_cases htop : h = ⊤
  · -- At the formal top the two labellings are equal.
    have hwa : w = a := funext fun e ↦ by simpa [htop] using hag e
    subst hwa
    rw [haa]
    exact had
  obtain ⟨c, rfl⟩ := exists_eq_pt_of_isShort hh hs h0 htop
  have hx0 : w d ≠ ⊥ := ne_bot_of_le_ne_bot (pt_ne_bot _ _) hd
  have hxkey : IsKey k w (w d) := isKey_apply_iff.mpr hx0
  have hxh : pt c k ≤ visibilityReplace k k (w d) :=
    hd.trans (le_visibilityReplace (Nat.le_succ k) _)
  have hshare' (e : ι) (he : a e < pt c k) : w e = a e := eq_of_min_eq_of_lt (hag e).symm he
  by_cases hS : ∃ e, w e < pt c k ∧ visibilityReplace k k (w e) = pt c k
  · -- The orbit of the key `h`: its block is `c`.
    obtain ⟨e, he, hek⟩ := hS
    have he0 : w e ≠ ⊥ := fun h ↦ pt_ne_bot c k (by rw [← hek, h, visibilityReplace_bot])
    have hcode : orbitMap k w (w e) = w e := by
      have h' := orbitCode_eq_of_min_eq hh hag he
      rwa [orbitCode_apply, orbitCode_apply, haa, eq_of_min_eq_of_lt (hag e) he] at h'
    obtain ⟨m, hm, hwe⟩ : ∃ m, m < k ∧ w e = pt c m := by
      rcases eq_bot_or_eq_top_or_eq_pt (w e) with h' | h' | ⟨b, m, h'⟩
      · exact absurd h' he0
      · exact absurd (h' ▸ he) (not_lt.mpr le_top)
      · rw [h', visibilityReplace_self_pt] at hek
        obtain ⟨rfl, hmk⟩ := pt_inj hek
        refine ⟨m, lt_of_le_of_ne (by omega) fun hmk' ↦ ?_, h'⟩
        rw [h', hmk'] at he
        exact lt_irrefl _ he
    have heo : IsOrbitKey k w (w e) :=
      isOrbitKey_of_not_isSelfVisible (by rw [hwe, isSelfVisible_pt]; omega)
    have hcb : ((codeBlock k w (w e) : ℕ) : Ordinal.{u}) = c := by
      obtain ⟨n', -, hpt, -, -⟩ := orbitMap_eq_pt (w := w) he0
      exact (pt_inj (hwe.symm.trans (hcode.symm.trans hpt))).1.symm
    rcases (hek.trans_le hxh).lt_or_eq with hlt | heq
    · have hlt' := codeBlock_lt_codeBlock he0 hxkey hlt
      refine (pt_lt_pt_of_lt ?_ k 0).le.trans (pt_zero_le_orbitMap hx0)
      rw [← hcb]
      exact_mod_cast hlt'
    · have hxeq : w d = pt c k :=
        le_antisymm ((le_visibilityReplace (Nat.le_succ k) _).trans (heq.symm.trans hek).le) hd
      rw [orbitMap_of_isOrbitKey ((isOrbitKey_congr heq).mp heo), ← codeBlock_congr heq, hxeq,
        moveToBlock_pt, gridPoint_eq_pt, blockIndex_pt, hcb]
  · push Not at hS
    -- The keys of `w` below `h`, which are the keys of `a` below `h`.
    set L : Finset Label.{u} :=
      {y ∈ univ.image (fun e ↦ visibilityReplace k k (w e)) | y ≠ ⊥ ∧ y < pt c k} with hL
    have hxr : #L + 1 ≤ keyRank k w (w d) := by
      have hnot : visibilityReplace k k (w d) ∉ L := fun hm ↦
        not_lt.mpr hxh (mem_filter.mp hm).2.2
      have hsub : insert (visibilityReplace k k (w d)) L ⊆
          {y ∈ univ.image fun e ↦ visibilityReplace k k (w e) |
            y ≠ ⊥ ∧ y ≤ visibilityReplace k k (w d)} := by
        intro y hy
        rcases mem_insert.mp hy with rfl | hy
        · exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ d),
            by rwa [Ne, visibilityReplace_eq_bot_iff], le_rfl⟩
        · obtain ⟨hyimg, hy0, hylt⟩ := mem_filter.mp hy
          exact mem_filter.mpr ⟨hyimg, hy0, (hylt.trans_le hxh).le⟩
      calc #L + 1 = #(insert (visibilityReplace k k (w d)) L) := (card_insert_of_notMem hnot).symm
        _ ≤ keyRank k w (w d) := card_le_card hsub
    -- The least value of `a` at least `h` has key rank at most `#L + 1` in `a`.
    obtain ⟨e₀, he₀, hmin⟩ := exists_min_image ({e | pt c k ≤ a e} : Finset ι) a
      ⟨d, mem_filter.mpr ⟨mem_univ d, had⟩⟩
    have he₀h : pt c k ≤ a e₀ := (mem_filter.mp he₀).2
    have hv0 : a e₀ ≠ ⊥ := ne_bot_of_le_ne_bot (pt_ne_bot _ _) he₀h
    have hvr : keyRank k a (a e₀) ≤ #L + 1 := by
      have hsub : {y ∈ univ.image fun e ↦ visibilityReplace k k (a e) |
          y ≠ ⊥ ∧ y ≤ visibilityReplace k k (a e₀)} ⊆ insert (visibilityReplace k k (a e₀)) L := by
        intro y hy
        obtain ⟨hyimg, hy0, hyle⟩ := mem_filter.mp hy
        obtain ⟨e', -, rfl⟩ := mem_image.mp hyimg
        rcases lt_or_ge (a e') (pt c k) with hlt | hge
        · have hw' := hshare' e' hlt
          have hle : visibilityReplace k k (a e') ≤ pt c k :=
            (monotone_visibilityReplace le_rfl hlt.le).trans_eq hh
          have hne : visibilityReplace k k (a e') ≠ pt c k := by
            rw [← hw']
            exact hS e' (hw' ▸ hlt)
          exact mem_insert_of_mem (mem_filter.mpr ⟨mem_image.mpr ⟨e', mem_univ _, by rw [hw']⟩,
            hy0, lt_of_le_of_ne hle hne⟩)
        · exact mem_insert.mpr (.inl (le_antisymm hyle
            (monotone_visibilityReplace le_rfl (hmin e' (mem_filter.mpr ⟨mem_univ _, hge⟩)))))
      exact (card_le_card hsub).trans (card_insert_le _ _)
    -- Hence `c ≤ 2 #L + 1`.
    obtain ⟨n₀, -, hpt₀, -, -⟩ := orbitMap_eq_pt (w := a) hv0
    rw [haa] at hpt₀
    have hcb₀ := codeBlock_le k a (a e₀)
    have hcle : c ≤ ((2 * #L + 1 : ℕ) : Ordinal.{u}) := by
      have hle := he₀h
      rw [hpt₀] at hle
      by_cases hcb : codeBlock k a (a e₀) ≤ 2 * #L + 1
      · rcases pt_le_pt_iff.mp hle with hlt | ⟨heq, -⟩
        · exact hlt.le.trans (by exact_mod_cast hcb)
        · exact heq.le.trans (by exact_mod_cast hcb)
      · -- The code block `2 #L + 2` is that of an orbit key, which cannot be the key `h`.
        have ho : IsOrbitKey k a (a e₀) := by
          by_contra ho
          rw [codeBlock_of_not_isOrbitKey (isKey_apply_iff.mpr hv0) ho] at hcb
          omega
        rcases pt_le_pt_iff.mp hle with hlt | ⟨heq, hkn⟩
        · have : codeBlock k a (a e₀) = 2 * #L + 1 + 1 := by omega
          rw [this, Nat.cast_add, Nat.cast_one] at hlt
          exact Order.lt_add_one_iff.mp hlt
        · exfalso
          obtain ⟨b₀, n₁, hn₁, ha₀, hvk⟩ := ho.eq_pt
          rw [hpt₀] at ha₀
          obtain ⟨hb₀, hn₀⟩ := pt_inj ha₀
          have hvr₀ : visibilityReplace k k (a e₀) = pt c k := by
            rw [hvk, ← hb₀, heq]
          obtain ⟨e', he'k, he'sv⟩ := ho
          have hae' : a e' < pt c k := lt_of_le_of_ne
            ((le_visibilityReplace (Nat.le_succ k) _).trans (he'k.trans hvr₀).le)
            fun h' ↦ he'sv (h' ▸ hh)
          exact hS e' (by rw [hshare' e' hae']; exact hae') (by rw [hshare' e' hae', he'k, hvr₀])
    obtain ⟨c', rfl⟩ : ∃ c' : ℕ, c = c' :=
      Ordinal.lt_omega0.mp (hcle.trans_lt (Ordinal.natCast_lt_omega0 _))
    have hcle' : c' ≤ 2 * #L + 1 := by exact_mod_cast hcle
    -- The code block of `w d` is at least `2 #L + 1`, and exactly that only off the orbit keys.
    have hnx : ¬ (IsOrbitKey k w (w d) ∧ visibilityReplace k k (w d) = gridPoint k 0) := by
      rintro ⟨⟨e, hek, hesv⟩, hn⟩
      have hc0 : c' = 0 := by
        have := hxh.trans_eq hn
        rw [gridPoint_eq_pt] at this
        rcases pt_le_pt_iff.mp this with h' | ⟨h', -⟩
        · exact absurd h' (by exact_mod_cast Nat.not_lt_zero c')
        · exact_mod_cast h'
      subst hc0
      have hwe : w e < pt ((0 : ℕ) : Ordinal.{u}) k := lt_of_le_of_ne
        ((le_visibilityReplace (Nat.le_succ k) _).trans (hek.trans hn).le)
        fun h' ↦ hesv (h' ▸ hh)
      exact hS e hwe (by rw [hek, hn]; rfl)
    have hxb := le_codeBlock hnx
    rcases (show c' ≤ codeBlock k w (w d) by omega).lt_or_eq with hlt | heq
    · exact (pt_lt_pt_of_lt (by exact_mod_cast hlt) k 0).le.trans (pt_zero_le_orbitMap hx0)
    · have hxo : ¬ IsOrbitKey k w (w d) := fun ho ↦ by
        have := codeBlock_of_isOrbitKey ho fun hn ↦ hnx ⟨ho, hn⟩
        omega
      rw [orbitMap_of_not_isOrbitKey hx0 hxo, ← heq]
      exact le_rfl

/-- **On values self-visible at `k`, the orbit code is the canonical code.** -/
theorem orbitCode_eq_canonicalCode (hv : ∀ d, IsSelfVisible k (w d)) :
    orbitCode k w = canonicalCode k w := by
  funext d
  by_cases hd : w d = ⊥
  · rw [orbitCode_eq_bot_iff.mpr hd, canonicalCode_eq_bot_iff.mpr hd]
  have ho : ¬ IsOrbitKey k w (w d) := fun ⟨e, _, he⟩ ↦ he (hv e)
  have hvw : (fun e ↦ visibilityReplace k k (w e)) = w := funext hv
  rw [orbitCode_apply, orbitMap_of_not_isOrbitKey hd ho,
    codeBlock_of_not_isOrbitKey (isKey_apply_iff.mpr hd) ho, canonicalCode_of_ne_bot (hv d) hd,
    canonicalPoint, keyRank, hvw, hv d]

/-- **The natural strip is kept**: the orbit code agrees with the labelling capped at the least
grid point `ω * 0 + k`.  It gives the literal reading at the cap `⊥`. -/
theorem min_orbitCode_gridPoint_zero (d : ι) :
    min (orbitCode k w d) (gridPoint k 0) = min (w d) (gridPoint k 0) := by
  by_cases hd : w d = ⊥
  · rw [orbitCode_eq_bot_iff.mpr hd, hd]
  by_cases hn : IsOrbitKey k w (w d) ∧ visibilityReplace k k (w d) = gridPoint k 0
  · rw [orbitCode_apply, orbitMap_of_isOrbitKey hn.1, codeBlock_of_natural hn.1 hn.2,
      moveToBlock_eq_self (by rw [hn.2]; exact isSelfVisible_gridPoint k 0)]
  -- Off the natural strip both are at least the least grid point.
  have h1 : 1 ≤ codeBlock k w (w d) := by
    have := le_codeBlock hn
    have := one_le_keyRank (k := k) (isKey_apply_iff.mpr hd)
    omega
  have hcode : gridPoint k 0 ≤ orbitCode k w d := by
    refine le_trans ?_ (pt_zero_le_orbitMap hd)
    rw [gridPoint_eq_pt]
    exact (pt_lt_pt_of_lt (by exact_mod_cast h1) _ _).le
  have hw : gridPoint k 0 ≤ w d := by
    by_contra hlt
    rw [not_le, gridPoint_eq_pt] at hlt
    rcases eq_bot_or_eq_top_or_eq_pt (w d) with h' | h' | ⟨b, m, h'⟩
    · exact hd h'
    · exact absurd (h' ▸ hlt) (not_lt.mpr le_top)
    rw [h'] at hlt
    rcases (pt_le_pt_iff.mp hlt.le) with hb | ⟨hb, hm⟩
    · exact absurd hb (by simp)
    have hm' : m < k := by
      rcases Nat.lt_or_ge m k with h'' | h''
      · exact h''
      · exact absurd hlt (not_lt.mpr (pt_le_pt_iff.mpr (.inr ⟨hb.symm, h''⟩)))
    refine hn ⟨isOrbitKey_of_not_isSelfVisible (by rw [h', isSelfVisible_pt]; omega), ?_⟩
    rw [h', visibilityReplace_self_pt, max_eq_right hm'.le, hb, gridPoint_eq_pt]
  rw [min_eq_right hcode, min_eq_right hw]

/-! ### The code grid -/

/-- The **code grid** at grade `k` with block bound `B`: bottom and the points `ω * b + f` with
`b ≤ B` and `f ≤ k`.  It contains the grid of the same bound and the orbit codes. -/
noncomputable def codeGrid (k B : ℕ) : Finset Label.{u} :=
  insert ⊥ (((range (B + 1)) ×ˢ (range (k + 1))).image fun p ↦
    ((ω * (p.1 : Ordinal.{u}) + (p.2 : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))

/-- Membership in the code grid. -/
theorem mem_codeGrid {B : ℕ} :
    x ∈ codeGrid k B ↔ x = ⊥ ∨ ∃ b ≤ B, ∃ f ≤ k,
      x = ((ω * (b : Ordinal.{u}) + (f : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  simp only [codeGrid, mem_insert, mem_image, mem_product, mem_range, Nat.lt_succ_iff,
    Prod.exists]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨b, f, ⟨hb, hf⟩, rfl⟩
    exact ⟨b, hb, f, hf, rfl⟩
  · rintro ⟨b, hb, f, hf, rfl⟩
    exact ⟨b, f, ⟨hb, hf⟩, rfl⟩

/-- The grid lies in the code grid of the same bound. -/
theorem grid_subset_codeGrid (k B : ℕ) : grid.{u} k B ⊆ codeGrid k B := fun x hx ↦ by
  rcases mem_grid.mp hx with rfl | ⟨b, hb, rfl⟩
  · exact mem_insert_self _ _
  · exact mem_codeGrid.mpr (.inr ⟨b, hb, k, le_rfl, rfl⟩)

/-- The code grid grows with its bound. -/
theorem codeGrid_mono {B B' : ℕ} (hB : B ≤ B') : codeGrid.{u} k B ⊆ codeGrid k B' := fun x hx ↦ by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, hb, f, hf, rfl⟩
  · exact mem_insert_self _ _
  · exact mem_codeGrid.mpr (.inr ⟨b, hb.trans hB, f, hf, rfl⟩)

/-- The members of the code grid are short at `k`. -/
theorem isShort_of_mem_codeGrid {B : ℕ} (hx : x ∈ codeGrid k B) : IsShort k x := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, -, f, hf, rfl⟩
  exacts [isShort_bot k, isShort_pt.mpr hf]

/-- The members of the code grid are not the formal top. -/
theorem ne_top_of_mem_codeGrid {B : ℕ} (hx : x ∈ codeGrid k B) : x ≠ ⊤ := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, -, f, -, rfl⟩
  exacts [bot_ne_top, pt_ne_top _ _]

/-- The members of the code grid lie below `ω ^ 2`. -/
theorem lt_omega0_sq_of_mem_codeGrid {B : ℕ} (hx : x ∈ codeGrid k B) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, -, f, -, rfl⟩
  exacts [lt_omega0_sq_iff.mpr (.inl rfl), lt_omega0_sq_iff.mpr (.inr ⟨b, f, rfl⟩)]

/-- The members of the code grid with block bound `B` are at most the grid point `ω * B + k`. -/
theorem le_gridPoint_of_mem_codeGrid {B : ℕ} (hx : x ∈ codeGrid k B) : x ≤ gridPoint k B := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, hb, f, hf, rfl⟩
  · exact bot_le
  · rw [gridPoint_eq_pt]
    rcases hb.lt_or_eq with hb | rfl
    · exact (pt_lt_pt_of_lt (by exact_mod_cast hb) _ _).le
    · exact pt_le_pt_iff.mpr (.inr ⟨rfl, hf⟩)

/-- **The orbit map takes values in the code grid** whose bound is at least twice the number of
cells. -/
theorem orbitMap_mem_codeGrid {B : ℕ} (hB : 2 * Fintype.card ι ≤ B) (x : Label.{u}) :
    orbitMap k w x ∈ codeGrid k B := by
  by_cases hx0 : x = ⊥
  · rw [hx0, orbitMap_bot]
    exact mem_insert_self _ _
  obtain ⟨n, hn, he, -⟩ := orbitMap_eq_pt (w := w) hx0
  have := codeBlock_le k w x
  have := keyRank_le_card k w x
  exact mem_codeGrid.mpr (.inr ⟨_, by omega, n, hn, he⟩)

/-- **Capped agreements pass to agreement heights at short caps.**  Let two labellings with values
in the code grid of bound `B` agree capped at a cap `h` self-visible and short at `k`.  Then, for
every third labelling, their agreement heights with it in the grid of bound `B` agree capped at
`h`: either `h` is a member of the grid, at which the two labellings agree, or `h` lies above every
value and the two labellings are equal. -/
theorem min_agreementHeight_eq_of_isShort {B : ℕ} {v v' : ι → Label.{u}}
    (hh : IsSelfVisible k h) (hs : IsShort k h)
    (hval : ∀ d, v d ∈ codeGrid k B ∧ v' d ∈ codeGrid k B)
    (hag : ∀ d, min (v d) h = min (v' d) h) (c : ι → Label.{u}) :
    min (agreementHeight (grid k B) v c) h = min (agreementHeight (grid k B) v' c) h := by
  have hG : ⊥ ∈ grid.{u} k B := bot_mem_grid k B
  have key : v = v' ∨ h ≤ agreementHeight (grid k B) v v' := by
    rcases eq_bot_or_eq_top_or_eq_pt h with rfl | rfl | ⟨c', n, rfl⟩
    · exact .inr bot_le
    · exact .inl (funext fun d ↦ by simpa using hag d)
    obtain rfl : k = n := le_antisymm (isSelfVisible_pt.mp hh) (isShort_pt.mp hs)
    by_cases hc : c' ≤ (B : Ordinal.{u})
    · obtain ⟨c'', rfl⟩ : ∃ c'' : ℕ, c' = c'' :=
        Ordinal.lt_omega0.mp (hc.trans_lt (Ordinal.natCast_lt_omega0 _))
      exact .inr (le_agreementHeight (gridPoint_mem_grid (by exact_mod_cast hc)) hag)
    · -- Above the code grid the two labellings are equal.
      refine .inl (funext fun d ↦ ?_)
      have hlt (y : Label.{u}) (hy : y ∈ codeGrid k B) : y < pt c' k :=
        (le_gridPoint_of_mem_codeGrid hy).trans_lt (pt_lt_pt_of_lt (not_le.mp hc) _ _)
      have h' := hag d
      rwa [min_eq_left (hlt _ (hval d).1).le, min_eq_left (hlt _ (hval d).2).le] at h'
  rcases key with rfl | hle
  · rfl
  calc min (agreementHeight (grid k B) v c) h
      = min (min (agreementHeight (grid k B) v c) (agreementHeight (grid k B) v v')) h := by
        rw [min_assoc, min_eq_right hle]
    _ = min (min (agreementHeight (grid k B) v' c) (agreementHeight (grid k B) v v')) h := by
        rw [agreementHeight_tri hG]
    _ = min (agreementHeight (grid k B) v' c) h := by rw [min_assoc, min_eq_right hle]

/-! ### The orbit decoder -/

open Classical in
/-- The **reading of the cell `d`** of a labelling `w` at grade `k`: bottom at the labels whose key
lies below the key of the orbit code of `d`; on the strip of that key, the block move back to the
block of `w d` when the key of `w d` is an orbit key; and the key of `w d` otherwise. -/
noncomputable def cellReading (k : ℕ) (w : ι → Label.{u}) (d : ι) (x : Label.{u}) : Label.{u} :=
  if visibilityReplace k k x < visibilityReplace k k (orbitCode k w d) then ⊥
  else if visibilityReplace k k x = visibilityReplace k k (orbitCode k w d) ∧
      IsOrbitKey k w (w d) then moveToBlock (w d) x
  else visibilityReplace k k (w d)

/-- The **orbit decoder** of a labelling `w` at grade `k` and cap `h`: a label `x` goes to the
larger of `min x h` and the readings at `x` of the cells whose orbit code has key at least `h`. -/
noncomputable def orbitDecoder (k : ℕ) (w : ι → Label.{u}) (h x : Label.{u}) : Label.{u} :=
  max (min x h)
    (({d | h ≤ visibilityReplace k k (orbitCode k w d)} : Finset ι).sup
      fun d ↦ cellReading k w d x)

/-- A label of the strip of a grid point is a point of its block with finite part at most `k`. -/
private theorem eq_pt_of_visibilityReplace_eq {c : Ordinal.{u}}
    (hx : visibilityReplace k k x = pt c k) : ∃ n ≤ k, x = pt c n := by
  rcases eq_bot_or_eq_top_or_eq_pt x with rfl | rfl | ⟨b, n, rfl⟩
  · exact absurd hx.symm (by rw [visibilityReplace_bot]; exact pt_ne_bot _ _)
  · exact absurd hx.symm (by rw [visibilityReplace_top]; exact pt_ne_top _ _)
  · rw [visibilityReplace_self_pt] at hx
    obtain ⟨rfl, hn⟩ := pt_inj hx
    exact ⟨n, by omega, rfl⟩

/-- On the strip of the code of a cell whose value has an orbit key, the block move back stays
at most the key of the value. -/
private theorem moveToBlock_le_visibilityReplace {d : ι} (hd : IsOrbitKey k w (w d))
    (hx : visibilityReplace k k x = visibilityReplace k k (orbitCode k w d)) :
    moveToBlock (w d) x ≤ visibilityReplace k k (w d) := by
  obtain ⟨b, n₀, -, hwd, hvd⟩ := hd.eq_pt
  rw [visibilityReplace_orbitCode_eq, ite_eq_right hd.isKey.ne_bot, gridPoint_eq_pt] at hx
  obtain ⟨n, hn, rfl⟩ := eq_pt_of_visibilityReplace_eq hx
  rw [moveToBlock_pt, hvd, hwd, blockIndex_pt]
  exact pt_le_pt_iff.mpr (.inr ⟨rfl, hn⟩)

/-- The reading of a cell is monotone. -/
theorem monotone_cellReading (k : ℕ) (w : ι → Label.{u}) (d : ι) :
    Monotone (cellReading k w d) := by
  intro x y hxy
  have hv := monotone_visibilityReplace (k := k) le_rfl hxy
  by_cases hx1 : visibilityReplace k k x < visibilityReplace k k (orbitCode k w d)
  · rw [cellReading, ite_eq_left hx1]
    exact bot_le
  have hy1 : ¬ visibilityReplace k k y < visibilityReplace k k (orbitCode k w d) :=
    fun h ↦ hx1 (hv.trans_lt h)
  by_cases hx2 : visibilityReplace k k x = visibilityReplace k k (orbitCode k w d) ∧
      IsOrbitKey k w (w d)
  · by_cases hy2 : visibilityReplace k k y = visibilityReplace k k (orbitCode k w d) ∧
        IsOrbitKey k w (w d)
    · rw [cellReading, cellReading, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hy1,
        ite_eq_left hy2]
      exact moveToBlock_le_moveToBlock hxy (hx2.1.trans hy2.1.symm)
    · rw [cellReading, cellReading, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hy1,
        ite_eq_right hy2]
      exact moveToBlock_le_visibilityReplace hx2.2 hx2.1
  · have hy2 : ¬ (visibilityReplace k k y = visibilityReplace k k (orbitCode k w d) ∧
        IsOrbitKey k w (w d)) := fun h ↦
      hx2 ⟨le_antisymm (hv.trans_eq h.1) (not_lt.mp hx1), h.2⟩
    rw [cellReading, cellReading, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hy1,
      ite_eq_right hy2]

/-- The reading of a cell commutes with the visibility replacements at the thresholds at most
`k`. -/
theorem cellReading_visibilityReplace {j i : ℕ} (hi : i ≤ j) (hj : j ≤ k) (d : ι)
    (x : Label.{u}) :
    cellReading k w d (visibilityReplace j i x) = visibilityReplace j i (cellReading k w d x) := by
  have hkey : visibilityReplace k k (visibilityReplace j i x) = visibilityReplace k k x :=
    visibilityReplace_self_visibilityReplace_of_le hi hj x
  unfold cellReading
  rw [hkey]
  split_ifs
  · rfl
  · exact moveToBlock_visibilityReplace _ _ _ _
  · exact (((isSelfVisible_visibilityReplace_self k _).mono hj).visibilityReplace_eq i).symm

/-- The reading of a cell fixes bottom. -/
theorem cellReading_bot (d : ι) : cellReading k w d ⊥ = ⊥ := by
  by_cases hd : w d = ⊥
  · have ho : ¬ IsOrbitKey k w (w d) := fun h ↦ h.isKey.ne_bot hd
    rw [cellReading, ite_eq_right (by simp [hd]), ite_eq_right fun h ↦ ho h.2, hd,
      visibilityReplace_bot]
  · rw [cellReading, ite_eq_left]
    rw [visibilityReplace_bot, bot_lt_iff_ne_bot, Ne, visibilityReplace_eq_bot_iff,
      orbitCode_eq_bot_iff]
    exact hd

/-- The orbit decoder fixes bottom. -/
theorem orbitDecoder_bot : orbitDecoder k w h ⊥ = ⊥ := by
  rw [orbitDecoder, min_eq_left bot_le,
    (Finset.sup_eq_bot_iff _ _).mpr fun d _ ↦ cellReading_bot d, max_self]

/-- The orbit decoder sends only bottom to bottom, at a cap other than bottom. -/
theorem eq_bot_of_orbitDecoder_eq_bot (hbot : h ≠ ⊥) (hx : orbitDecoder k w h x = ⊥) :
    x = ⊥ := by
  have := le_bot_iff.mp ((le_max_left _ _).trans hx.le)
  rwa [min_eq_bot, or_iff_left hbot] at this

/-- **The orbit decoder is a witness bounded by grade `k`**, for a cap `h` self-visible at `k`
other than bottom. -/
theorem isWitness_orbitDecoder (hh : IsSelfVisible k h) (hbot : h ≠ ⊥) :
    IsWitness (stepSuppressor.{u} k) (orbitDecoder k w h) where
  antitone := (IsWitness.id_step k).antitone
  isSelfVisible := (IsWitness.id_step k).isSelfVisible
  map_bot := orbitDecoder_bot
  monotone x y hxy := max_le_max (min_le_min_right _ hxy)
    (Finset.sup_mono_fun fun d _ ↦ monotone_cellReading k w d hxy)
  visibilityReplace_comm x j hx i hi := by
    by_cases hj : j ≤ k
    · rw [orbitDecoder, orbitDecoder, visibilityReplace_max hi,
        visibilityReplace_min_of_isSelfVisible hi (hh.mono hj),
        Finset.apply_sup_eq_sup_comp (visibilityReplace j i) (visibilityReplace_max hi)
          (visibilityReplace_bot j i)]
      congr 1
      exact Finset.sup_congr rfl fun d _ ↦ cellReading_visibilityReplace hi hj d x
    · rw [stepSuppressor_of_lt (not_le.mp hj), le_bot_iff] at hx
      rw [eq_bot_of_orbitDecoder_eq_bot hbot hx, visibilityReplace_bot, orbitDecoder_bot,
        visibilityReplace_bot]

/-- The reading of a cell at the orbit code of a cell whose value has the same key is that value.
-/
private theorem cellReading_orbitCode_of_eq {d e : ι} (hd : w d ≠ ⊥) (he : w e ≠ ⊥)
    (heq : visibilityReplace k k (w e) = visibilityReplace k k (w d)) :
    cellReading k w e (orbitCode k w d) = w d := by
  have hc : visibilityReplace k k (orbitCode k w d) = visibilityReplace k k (orbitCode k w e) :=
    le_antisymm ((visibilityReplace_orbitCode_le_iff he hd).mpr heq.ge)
      ((visibilityReplace_orbitCode_le_iff hd he).mpr heq.le)
  rw [cellReading, ite_eq_right (not_lt.mpr hc.ge)]
  by_cases ho : IsOrbitKey k w (w d)
  · have hoe : IsOrbitKey k w (w e) := (isOrbitKey_congr heq).mpr ho
    rw [ite_eq_left ⟨hc, hoe⟩, orbitCode_apply, orbitMap_of_isOrbitKey ho, moveToBlock_moveToBlock,
      moveToBlock_eq_self heq]
  · have hoe : ¬ IsOrbitKey k w (w e) := fun h ↦ ho ((isOrbitKey_congr heq).mp h)
    rw [ite_eq_right fun h ↦ hoe h.2, heq]
    by_contra hnsv
    exact ho (isOrbitKey_of_not_isSelfVisible hnsv)

/-- The reading of a cell at the orbit code of a cell is at most the value there. -/
private theorem cellReading_orbitCode_le (d e : ι) :
    cellReading k w e (orbitCode k w d) ≤ w d := by
  by_cases h1 : visibilityReplace k k (orbitCode k w d) < visibilityReplace k k (orbitCode k w e)
  · rw [cellReading, ite_eq_left h1]
    exact bot_le
  by_cases he : w e = ⊥
  · have ho : ¬ IsOrbitKey k w (w e) := fun h ↦ h.isKey.ne_bot he
    rw [cellReading, ite_eq_right h1, ite_eq_right fun h ↦ ho h.2, he, visibilityReplace_bot]
    exact bot_le
  by_cases hd : w d = ⊥
  · refine absurd ?_ h1
    rw [orbitCode_eq_bot_iff.mpr hd, visibilityReplace_bot, bot_lt_iff_ne_bot, Ne,
      visibilityReplace_eq_bot_iff, orbitCode_eq_bot_iff]
    exact he
  have hkey := (visibilityReplace_orbitCode_le_iff hd he).mp (not_lt.mp h1)
  rcases hkey.lt_or_eq with hlt | heq
  · have h2 : ¬ (visibilityReplace k k (orbitCode k w d) =
        visibilityReplace k k (orbitCode k w e) ∧ IsOrbitKey k w (w e)) := fun h ↦
      (not_le.mpr hlt) ((visibilityReplace_orbitCode_le_iff he hd).mp h.1.le)
    rw [cellReading, ite_eq_right h1, ite_eq_right h2]
    by_contra hc
    exact (not_le.mpr hlt) (visibilityReplace_le_of_le le_rfl
      (isSelfVisible_visibilityReplace_self k _) (not_le.mp hc).le)
  · exact (cellReading_orbitCode_of_eq hd he heq).le

/-- **N4, the literal reading**: when the orbit code of `w` agrees with `w` capped at `h`, the orbit
decoder reads it literally as `w`, the formal top included. -/
theorem orbitDecoder_orbitCode (hag : ∀ d, min (orbitCode k w d) h = min (w d) h) (d : ι) :
    orbitDecoder k w h (orbitCode k w d) = w d := by
  have hsup : (({e | h ≤ visibilityReplace k k (orbitCode k w e)} : Finset ι).sup
      fun e ↦ cellReading k w e (orbitCode k w d)) ≤ w d :=
    Finset.sup_le fun e _ ↦ cellReading_orbitCode_le d e
  rcases le_or_gt h (orbitCode k w d) with hc | hc
  · have hwd : h ≤ w d := le_of_min_eq_of_le (hag d) hc
    by_cases hd : w d = ⊥
    · rw [hd] at hsup
      rw [orbitDecoder, le_bot_iff.mp hsup, max_bot_right, orbitCode_eq_bot_iff.mpr hd, hd]
      exact min_eq_left bot_le
    have hmem : d ∈ ({e | h ≤ visibilityReplace k k (orbitCode k w e)} : Finset ι) :=
      mem_filter.mpr ⟨mem_univ d, hc.trans (le_visibilityReplace (Nat.le_succ k) _)⟩
    have hge : w d ≤ ({e | h ≤ visibilityReplace k k (orbitCode k w e)} : Finset ι).sup
        fun e ↦ cellReading k w e (orbitCode k w d) :=
      (cellReading_orbitCode_of_eq hd hd rfl).symm.le.trans (le_sup (f := fun e ↦
        cellReading k w e (orbitCode k w d)) hmem)
    rw [orbitDecoder, le_antisymm hsup hge, min_eq_right hc]
    exact max_eq_right hwd
  · have hw : w d = orbitCode k w d := eq_of_min_eq_of_lt (hag d) hc
    rw [orbitDecoder, min_eq_left hc.le, max_eq_left (hsup.trans hw.le)]
    exact hw.symm

/-- **The cap is kept**: at a label self-visible at `k` the orbit decoder agrees with the identity
capped at `h`. -/
theorem min_orbitDecoder_eq (hx : IsSelfVisible k x) :
    min (orbitDecoder k w h x) h = min x h := by
  rcases lt_or_ge x h with hxh | hxh
  · have hsup : (({d | h ≤ visibilityReplace k k (orbitCode k w d)} : Finset ι).sup
        fun d ↦ cellReading k w d x) = ⊥ := (Finset.sup_eq_bot_iff _ _).mpr fun d hd ↦ by
      rw [cellReading, ite_eq_left]
      rw [hx]
      exact hxh.trans_le (mem_filter.mp hd).2
    rw [orbitDecoder, hsup, max_bot_right, min_eq_left hxh.le, min_eq_left hxh.le]
  · rw [min_eq_right hxh]
    exact min_eq_right ((min_eq_right hxh).ge.trans (le_max_left _ _))

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} [Fintype ι] {D : CellScheme ι α} {R : D.Rows.{u}} {k : ℕ}

/-- **The orbit code of a labelling lawful below a pair is lawful below it**, when the cells
below the pair have grade at most `k`: the orbit map is a witness bounded by grade `k` that sends
only bottom to bottom. -/
theorem IsLawfulBelow.orbitCode {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) (hk : ∀ d : D.below X, D.grade d ≤ k) :
    R.IsLawfulBelow X fun d ↦ Label.orbitCode k w d :=
  hw.map_of_apply_eq_bot hk (isWitness_orbitMap k w) fun _ ↦ orbitMap_eq_bot_iff.mp

end VaughtConjecture.CellScheme.Rows

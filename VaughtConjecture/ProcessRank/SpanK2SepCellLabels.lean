/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeThreeLabels

/-!
# The grade-two and grade-three labels at the controller of the separated admitted state

Process rank `ω₁`, the finite span of mutual rigidity: the labels of the test with `K = 2` on the
grade-two scheme (`ProcessRank.k2Grade2Label`) and on the grade-three scheme
(`ProcessRank.k2Grade3Label`) differ at the controller of the separated admitted state
(`ProcessRank.k2SepCell`), an old cell of the grade-three scheme.  Compiled here (theorem named):
* the grade-two label there is `3` (`ProcessRank.k2Grade2Label_k2SepCell`): the code of the
  attachment labels reads the controller as `ω + 2` (`ProcessRank.agreementHeight_eq_blockPt_one`),
  below the key of every code, and the upper decoder at the cap grade three reads the least
  admissible label `3` below the value `ω + 1` at the cell `1`
  (`ProcessRank.upperDecoderAt_eq_of_lt`, `ProcessRank.admissibleBelowAt_eq_blockPt`);
* the grade-three label there is `4` (`ProcessRank.k2Grade3Label_k2SepCell`): the code at the grade
  two of `k2Code3` reads the controller as `ω + 2`, the decoder over `k2Code3` reads that as
  `ω + 3`, and the decoder at the cap grade four over the attachment labels reads `ω + 3` as `4`;
* hence the grade-three labels do not extend the grade-two labels
  (`ProcessRank.k2Grade3Label_k2SepCell_ne`).
The orbit codes are bounded through their code blocks (`ProcessRank.blockPt_le_orbitMap`,
`ProcessRank.blockPt_le_orbitMap_of_isOrbitKey`) and computed exactly only where needed: the value
`ω + 1` of least key goes to `ω * 2 + 1` (`ProcessRank.orbitMap_blockPt_one_one`).

Open: the classification of the grade-two controllers at which the two labels agree, the mirror
conditions at the grade three, the grade four, legality of the completed scheme, the four-point
span of mutual rigidity of the test pair, and the countable upper bound on the Scott classes.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-! ### Points of blocks -/

/-- The point `ω * b + n` of the block `b`, for natural numbers `b` and `n`. -/
noncomputable abbrev blockPt (b n : ℕ) : Label.{u} :=
  ((ω * (b : Ordinal.{u}) + (n : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

theorem blockPt_le_blockPt_iff {b b' n n' : ℕ} :
    blockPt.{u} b n ≤ blockPt b' n' ↔ b < b' ∨ b = b' ∧ n ≤ n' := by
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff]
  constructor
  · rintro (h | ⟨h, hn⟩)
    · exact .inl (by exact_mod_cast h)
    · exact .inr ⟨by exact_mod_cast h, hn⟩
  · rintro (h | ⟨rfl, hn⟩)
    · exact .inl (by exact_mod_cast h)
    · exact .inr ⟨rfl, hn⟩

theorem blockPt_lt_blockPt_iff {b b' n n' : ℕ} :
    blockPt.{u} b n < blockPt b' n' ↔ b < b' ∨ b = b' ∧ n < n' := by
  rw [lt_iff_le_not_ge, blockPt_le_blockPt_iff, blockPt_le_blockPt_iff]
  omega

theorem blockPt_lt_top (b n : ℕ) : blockPt.{u} b n < ⊤ :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

theorem blockPt_ne_bot (b n : ℕ) : blockPt.{u} b n ≠ ⊥ := WithBot.coe_ne_bot

theorem visibilityReplace_blockPt (k i b n : ℕ) :
    visibilityReplace k i (blockPt.{u} b n) = blockPt b (if n < k then i else n) := by
  rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

theorem isSelfVisible_blockPt {k b n : ℕ} : IsSelfVisible k (blockPt.{u} b n) ↔ k ≤ n := by
  rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

theorem moveToBlock_blockPt (b n b' n' : ℕ) :
    moveToBlock (blockPt.{u} b n) (blockPt b' n') = blockPt b n' :=
  moveToBlock_omega0_mul_add _ _ _ _

theorem gridPoint_eq_blockPt (k b : ℕ) : gridPoint.{u} k b = blockPt b k := rfl

theorem blockPt_mem_codeGrid {K B b f : ℕ} (hb : b ≤ B) (hf : f ≤ K) :
    blockPt.{u} b f ∈ codeGrid K B :=
  mem_codeGrid.mpr (.inr ⟨b, hb, f, hf, rfl⟩)

/-! ### Key ranks, orbit maps and upper decoders at concrete labellings -/

section Generic

variable {ι : Type*} [Fintype ι] {k K B : ℕ} {w : ι → Label.{u}} {x y z v : Label.{u}}

/-- A key whose key is below every key of `w` has key rank one. -/
theorem keyRank_eq_one (hx : IsKey k w x)
    (hmin : ∀ d, w d ≠ ⊥ → visibilityReplace k k x ≤ visibilityReplace k k (w d)) :
    keyRank k w x = 1 := by
  classical
  refine le_antisymm ?_ (one_le_keyRank hx)
  unfold keyRank valueRank
  refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
  have key (c : Label.{u}) (hc : c ∈ ({y ∈ univ.image fun d ↦ visibilityReplace k k (w d) |
      y ≠ ⊥ ∧ y ≤ visibilityReplace k k x} : Finset Label.{u})) :
      c = visibilityReplace k k x := by
    obtain ⟨hcimg, hc0, hcx⟩ := mem_filter.mp hc
    obtain ⟨d, -, rfl⟩ := mem_image.mp hcimg
    have hd : w d ≠ ⊥ := fun h ↦ hc0 (by rw [h, visibilityReplace_bot])
    exact le_antisymm hcx (hmin d hd)
  rw [key a ha, key b hb]

/-- A key above another key of `w` has key rank at least two. -/
theorem two_le_keyRank (hy : IsKey k w y) (hz : IsKey k w z)
    (h : visibilityReplace k k z < visibilityReplace k k y) : 2 ≤ keyRank k w y := by
  have h1 := one_le_keyRank hz
  have h2 := keyRank_lt_keyRank hy h
  omega

/-- The orbit map of a label other than bottom lies at least at the start of its code block. -/
theorem blockPt_codeBlock_le_orbitMap (hx : x ≠ ⊥) :
    blockPt.{u} (codeBlock k w x) 0 ≤ orbitMap k w x := by
  by_cases ho : IsOrbitKey k w x
  · rw [orbitMap_of_isOrbitKey ho]
    induction x using recBotCoeTop with
    | bot => exact absurd rfl hx
    | top => exact absurd rfl ho.ne_top
    | coe o =>
      obtain ⟨b', n', rfl⟩ := exists_eq_omega0_mul_add_natCast o
      rw [gridPoint, moveToBlock_omega0_mul_add]
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (omega0_mul_add_natCast_le_iff.mpr (.inr ⟨rfl, Nat.zero_le _⟩)))
  · rw [orbitMap_of_not_isOrbitKey hx ho, gridPoint_eq_blockPt]
    exact blockPt_le_blockPt_iff.mpr (.inr ⟨rfl, Nat.zero_le _⟩)

/-- The orbit map at an orbit key off the natural strip, of key rank at least `r`, lies at least
at the start of the block `2 r`. -/
theorem blockPt_le_orbitMap_of_isOrbitKey {r : ℕ} (hx : IsOrbitKey k w x)
    (hn : visibilityReplace k k x ≠ gridPoint k 0) (hr : r ≤ keyRank k w x) :
    blockPt.{u} (2 * r) 0 ≤ orbitMap k w x := by
  refine le_trans ?_ (blockPt_codeBlock_le_orbitMap hx.isKey.ne_bot)
  rw [codeBlock_of_isOrbitKey hx hn]
  exact blockPt_le_blockPt_iff.mpr (by omega)

/-- The orbit map at a label other than bottom off the natural strip, of key rank at least `r`,
lies at least at the start of the block `2 r - 1`. -/
theorem blockPt_le_orbitMap {r : ℕ} (hx : x ≠ ⊥)
    (hn : ¬ (IsOrbitKey k w x ∧ visibilityReplace k k x = gridPoint k 0))
    (hr : r ≤ keyRank k w x) : blockPt.{u} (2 * r - 1) 0 ≤ orbitMap k w x := by
  refine le_trans ?_ (blockPt_codeBlock_le_orbitMap hx)
  have := le_codeBlock hn
  exact blockPt_le_blockPt_iff.mpr (by omega)

/-- **The upper decoder at a label read by no cell**: if every orbit code has key above the key of
`x`, the decoder is the larger of `min x (gridPoint k 0)` and the least admissible label below a
value; here it is the admissible label `v` attained at a cell `d₀` and below the others. -/
theorem upperDecoderAt_eq_of_lt (hx : x ≠ ⊥)
    (hread : ∀ d, visibilityReplace k k x < visibilityReplace k k (orbitCode k w d))
    (hmin : min x (gridPoint k 0) ≤ v) (hlow : ∀ d, v ≤ admissibleBelowAt K B (w d)) (d₀ : ι)
    (hd₀ : admissibleBelowAt K B (w d₀) = v) (hvB : v ≤ gridPoint K B) :
    upperDecoderAt k K B w x = v := by
  classical
  have hod : orbitDecoder k w (gridPoint k 0) x = min x (gridPoint k 0) := by
    unfold orbitDecoder
    rw [(Finset.sup_eq_bot_iff _ _).mpr (fun d _ ↦ ?_), max_bot_right]
    unfold cellReading
    exact ite_eq_left (hread d)
  have hgap : gapValueAt k K B w x = v := by
    rw [gapValueAt_of_ne_bot hx]
    have hinf : ({d | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w d)} :
        Finset ι).inf (fun d ↦ admissibleBelowAt K B (w d)) = v :=
      le_antisymm ((Finset.inf_le (mem_filter.mpr ⟨mem_univ d₀, (hread d₀).le⟩)).trans_eq hd₀)
        (Finset.le_inf fun d _ ↦ hlow d)
    rw [hinf, min_eq_right hvB]
  unfold upperDecoderAt
  rw [hod, hgap, max_eq_right hmin]

end Generic

/-- The admissible label below a label of the block `b` from `ω * b + K` on is `ω * b + K`. -/
theorem admissibleBelowAt_eq_blockPt {K B b : ℕ} {v : Label.{u}} (hb : b ≤ B)
    (hle : blockPt b K ≤ v) (hlt : v < blockPt (b + 1) K) :
    admissibleBelowAt K B v = blockPt b K := by
  refine le_antisymm ?_ (le_admissibleBelowAt (blockPt_mem_codeGrid hb le_rfl)
    (isSelfVisible_blockPt.mpr le_rfl) hle)
  have hm := admissibleBelowAt_mem_codeGrid K B v
  have hs := isSelfVisible_admissibleBelowAt K B v
  have hv := (admissibleBelowAt_le K B v).trans_lt hlt
  rcases mem_codeGrid.mp hm with h0 | ⟨b', -, f, hf, he⟩
  · rw [h0]; exact bot_le
  · change admissibleBelowAt K B v = blockPt b' f at he
    rw [he] at hs hv ⊢
    have hfK : f = K := le_antisymm hf (isSelfVisible_blockPt.mp hs)
    subst hfK
    have := blockPt_lt_blockPt_iff.mp hv
    exact blockPt_le_blockPt_iff.mpr (by omega)

/-- A point `ω * b + K` at most `v`, with `b ≤ B`, is at most the admissible label below `v`. -/
theorem blockPt_le_admissibleBelowAt {K B b : ℕ} {v : Label.{u}} (hb : b ≤ B)
    (hle : blockPt b K ≤ v) : blockPt b K ≤ admissibleBelowAt K B v :=
  le_admissibleBelowAt (blockPt_mem_codeGrid hb le_rfl) (isSelfVisible_blockPt.mpr le_rfl) hle

/-- **The agreement height at the first grid point**: two labellings at least `ω + 2` agree capped
at `ω + 2`; if at a cell one is below `ω * 2 + 2` and the other at least `ω * 2 + 2`, they agree
capped at no larger grid point. -/
theorem agreementHeight_eq_blockPt_one {ι : Type*} [Fintype ι] {a c : ι → Label.{u}}
    (ha : ∀ d, blockPt 1 2 ≤ a d) (hc : ∀ d, blockPt 1 2 ≤ c d) (e : ι)
    (hce : c e < blockPt 2 2) (hae : blockPt 2 2 ≤ a e) :
    agreementHeight (grid 2 16) a c = blockPt 1 2 := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨hm, hag⟩ := agreementHeight_spec (bot_mem_grid 2 16) a c
    rcases mem_grid.mp hm with h0 | ⟨b, -, hb⟩
    · rw [h0]; exact bot_le
    · by_contra hlt
      rw [hb, gridPoint_eq_blockPt, blockPt_le_blockPt_iff] at hlt
      have h22 : blockPt.{u} 2 2 ≤ agreementHeight (grid 2 16) a c := by
        rw [hb, gridPoint_eq_blockPt]; exact blockPt_le_blockPt_iff.mpr (by omega)
      have he := hag e
      rw [min_eq_left (hce.le.trans h22)] at he
      exact absurd (he ▸ le_min hae h22) (not_le.mpr hce)
  · unfold agreementHeight
    exact le_sup (f := id) (mem_filter.mpr ⟨gridPoint_mem_grid (by decide : 1 ≤ 16), fun d ↦
      (min_eq_right (ha d)).trans (min_eq_right (hc d)).symm⟩)

theorem visibilityReplace_blockPt_of_lt {k i b n : ℕ} (h : n < k) :
    visibilityReplace k i (blockPt.{u} b n) = blockPt b i := by
  rw [visibilityReplace_blockPt, ite_eq_left h]

theorem visibilityReplace_blockPt_of_le {k i b n : ℕ} (h : k ≤ n) :
    visibilityReplace k i (blockPt.{u} b n) = blockPt b n := by
  rw [visibilityReplace_blockPt, ite_eq_right (not_lt.mpr h)]

section Generic2

variable {ι : Type*} [Fintype ι] {k : ℕ} {w : ι → Label.{u}} {x : Label.{u}}

/-- A value `ω * b + 1` with `1 ≤ b` is, at a grade `k ≥ 2`, an orbit key off the natural strip;
with key rank at least `r`, its orbit map lies at least at the start of the block `2 r`. -/
theorem blockPt_le_orbitMap_blockPt_one {b r : ℕ} (hb : 1 ≤ b) (hk : 2 ≤ k) {d : ι}
    (hd : w d = blockPt b 1) (hr : r ≤ keyRank k w (blockPt b 1)) :
    blockPt.{u} (2 * r) 0 ≤ orbitMap k w (blockPt b 1) := by
  have ho : IsOrbitKey k w (blockPt b 1) := by
    rw [← hd]
    exact isOrbitKey_of_not_isSelfVisible (by rw [hd, isSelfVisible_blockPt]; omega)
  refine blockPt_le_orbitMap_of_isOrbitKey ho ?_ hr
  rw [visibilityReplace_blockPt_of_lt (by omega), gridPoint_eq_blockPt]
  intro h
  have := blockPt_le_blockPt_iff.mp h.le
  omega

/-- **The orbit map at the least key `ω + 1`**: at a grade `k ≥ 2`, if `ω + 1` is a value of `w`
and every key of `w` is at least its key `ω + k`, the orbit map sends `ω + 1` to `ω * 2 + 1`. -/
theorem orbitMap_blockPt_one_one {d : ι} (hk : 2 ≤ k) (hd : w d = blockPt 1 1)
    (hmin : ∀ e, w e ≠ ⊥ → blockPt 1 k ≤ visibilityReplace k k (w e)) :
    orbitMap k w (blockPt 1 1) = blockPt.{u} 2 1 := by
  have ho : IsOrbitKey k w (blockPt 1 1) := by
    rw [← hd]
    exact isOrbitKey_of_not_isSelfVisible (by rw [hd, isSelfVisible_blockPt]; omega)
  have hr : keyRank k w (blockPt 1 1) = 1 :=
    keyRank_eq_one ho.isKey fun e he ↦ by
      rw [visibilityReplace_blockPt_of_lt (by omega)]; exact hmin e he
  rw [orbitMap_of_isOrbitKey ho, codeBlock_of_isOrbitKey ho (by
      rw [visibilityReplace_blockPt_of_lt (by omega), gridPoint_eq_blockPt]
      intro h
      have := blockPt_le_blockPt_iff.mp h.le
      omega), hr, gridPoint_eq_blockPt, moveToBlock_blockPt]

/-- **The orbit map at an orbit key `ω * b + 1`** of key rank at least two, at a grade `k ≥ 2`, is
`ω * m + 1` for a block `m ≥ 4`. -/
theorem orbitMap_blockPt_one_of_two_le {b : ℕ} {d : ι} (hb : 1 ≤ b) (hk : 2 ≤ k)
    (hd : w d = blockPt b 1) (hr : 2 ≤ keyRank k w (blockPt b 1)) :
    ∃ m, 4 ≤ m ∧ orbitMap k w (blockPt b 1) = blockPt.{u} m 1 := by
  have ho : IsOrbitKey k w (blockPt b 1) := by
    rw [← hd]
    exact isOrbitKey_of_not_isSelfVisible (by rw [hd, isSelfVisible_blockPt]; omega)
  refine ⟨codeBlock k w (blockPt b 1), ?_, ?_⟩
  · rw [codeBlock_of_isOrbitKey ho (by
      rw [visibilityReplace_blockPt_of_lt (by omega), gridPoint_eq_blockPt]
      intro h
      have := blockPt_le_blockPt_iff.mp h.le
      omega)]
    omega
  · rw [orbitMap_of_isOrbitKey ho, gridPoint_eq_blockPt, moveToBlock_blockPt]

/-- **The orbit map at a non-orbit key** of key rank at least two, at a grade `k`, is
`ω * m + k` for a block `m ≥ 3`. -/
theorem orbitMap_of_not_isOrbitKey_of_two_le (hx0 : x ≠ ⊥) (hk : IsKey k w x)
    (ho : ¬ IsOrbitKey k w x) (hr : 2 ≤ keyRank k w x) :
    ∃ m, 3 ≤ m ∧ orbitMap k w x = blockPt.{u} m k := by
  refine ⟨codeBlock k w x, ?_, ?_⟩
  · rw [codeBlock_of_not_isOrbitKey hk ho]; omega
  · rw [orbitMap_of_not_isOrbitKey hx0 ho, gridPoint_eq_blockPt]

omit [Fintype ι] in
/-- A value of `w` is a key of `w`. -/
theorem isKey_of_apply_eq {d : ι} {x : Label.{u}} (hd : w d = x) (hx : x ≠ ⊥) : IsKey k w x :=
  hd ▸ isKey_apply_iff.mpr (hd ▸ hx)

end Generic2

/-! ### The concrete labellings -/

theorem k2AttLabel_one : k2AttLabel.{u} 1 = blockPt 1 1 := by
  simp [k2AttLabel, attCell, k2Left, blockPt]

theorem k2AttLabel_five : k2AttLabel.{u} 5 = blockPt 2 1 := by
  simp [k2AttLabel, attCell, k2Right, blockPt]

theorem k2AttLabel_cases (d : Fin 8) :
    k2AttLabel.{u} d = ⊤ ∨ k2AttLabel d = blockPt 1 1 ∨ k2AttLabel d = blockPt 2 1 := by
  fin_cases d <;> simp [k2AttLabel, attCell, k2Left, k2Right, blockPt]

theorem attRow_five : attRow.{u} 5 = blockPt 1 1 := by
  simp [attRow, attCell, testRow, blockPt]

theorem attRow_cases (d : Fin 8) :
    attRow.{u} d = blockPt 2 1 ∨ attRow d = blockPt 1 1 ∨ attRow d = blockPt 2 2 := by
  fin_cases d <;> simp [attRow, attCell, testRow, blockPt]

/-! ### The codes -/

/-- The attachment labels as a labelling of the cells of the attachment. -/
noncomputable abbrev k2P : Fin k2AttachmentBase.{u}.S.card → Label.{u} := fun e ↦ k2AttLabel e

theorem k2P_one_isKey (k : ℕ) : IsKey k k2P.{u} (blockPt 1 1) :=
  isKey_of_apply_eq (d := (1 : Fin 8)) k2AttLabel_one (blockPt_ne_bot 1 1)

/-- Every orbit code at a grade `k ≥ 2` of the attachment labels lies at least at `ω * 2`. -/
theorem blockPt_le_orbitCode_k2P {k : ℕ} (hk : 2 ≤ k) (d : Fin k2AttachmentBase.{u}.S.card) :
    blockPt 2 0 ≤ orbitCode k k2P.{u} d := by
  rw [orbitCode_apply]
  change blockPt 2 0 ≤ orbitMap k k2P (k2AttLabel d)
  rcases k2AttLabel_cases d with h | h | h <;> rw [h]
  · have hy : IsKey k k2P.{u} ⊤ := isKey_of_apply_eq (d := d) h top_ne_bot
    have hr := two_le_keyRank hy (k2P_one_isKey k) (by
      rw [visibilityReplace_top, visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_lt_top _ _)
    refine le_trans ?_ (blockPt_le_orbitMap (r := 2) top_ne_bot (fun h ↦ h.1.ne_top rfl) hr)
    exact blockPt_le_blockPt_iff.mpr (by omega)
  · exact blockPt_le_orbitMap_blockPt_one (r := 1) le_rfl hk h
      (one_le_keyRank (k2P_one_isKey k))
  · exact blockPt_le_orbitMap_blockPt_one (r := 1) one_le_two hk h
      (one_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot 2 1)))

/-- The orbit code at a grade `k ≥ 2` of the attachment labels at the cell `5` lies at least at
`ω * 4`. -/
theorem blockPt_le_orbitCode_k2P_five {k : ℕ} (hk : 2 ≤ k) :
    blockPt 4 0 ≤ orbitCode k k2P.{u} (5 : Fin 8) := by
  change blockPt 4 0 ≤ orbitMap k k2P (k2AttLabel 5)
  rw [k2AttLabel_five]
  have hr := two_le_keyRank (isKey_of_apply_eq (d := (5 : Fin 8)) k2AttLabel_five
    (blockPt_ne_bot 2 1)) (k2P_one_isKey k) (by
      rw [visibilityReplace_blockPt_of_lt (by omega), visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_lt_blockPt_iff.mpr (.inl one_lt_two))
  exact blockPt_le_orbitMap_blockPt_one (r := 2) one_le_two hk k2AttLabel_five hr

/-- The attachment labels at the cell `1` have key rank one at every grade `k ≥ 2`. -/
theorem keyRank_k2P_one {k : ℕ} (hk : 2 ≤ k) : keyRank k k2P.{u} (blockPt 1 1) = 1 := by
  refine keyRank_eq_one (k2P_one_isKey k) fun d _ ↦ ?_
  change visibilityReplace k k (blockPt 1 1) ≤ visibilityReplace k k (k2AttLabel d)
  rw [visibilityReplace_blockPt_of_lt (by omega)]
  rcases k2AttLabel_cases d with h | h | h <;> rw [h]
  · exact le_top
  · rw [visibilityReplace_blockPt_of_lt (by omega)]
  · rw [visibilityReplace_blockPt_of_lt (by omega)]
    exact blockPt_le_blockPt_iff.mpr (.inl one_lt_two)

/-- The orbit code at a grade `k ≥ 2` of the attachment labels at the cell `1` is `ω * 2 + 1`. -/
theorem orbitCode_k2P_one {k : ℕ} (hk : 2 ≤ k) : orbitCode k k2P.{u} (1 : Fin 8) = blockPt 2 1 := by
  change orbitMap k k2P (k2AttLabel 1) = blockPt 2 1
  rw [k2AttLabel_one]
  have ho : IsOrbitKey k k2P.{u} (blockPt 1 1) :=
    ⟨(1 : Fin 8), by change visibilityReplace k k (k2AttLabel 1) = _; rw [k2AttLabel_one], by
      change ¬ IsSelfVisible k (k2AttLabel 1)
      rw [k2AttLabel_one, isSelfVisible_blockPt]; omega⟩
  rw [orbitMap_of_isOrbitKey ho, codeBlock_of_isOrbitKey ho (by
      rw [visibilityReplace_blockPt_of_lt (by omega), gridPoint_eq_blockPt]
      intro h
      have := blockPt_le_blockPt_iff.mp h.le
      omega), keyRank_k2P_one hk, gridPoint_eq_blockPt, moveToBlock_blockPt]

/-- The shapes of the orbit code at the grade three of the attachment labels: `ω * 2 + 1`, a point
`ω * m + 1` with `m ≥ 4`, or a point `ω * m + 3` with `m ≥ 3`. -/
theorem k2Code3_cases (d : Fin k2AttachmentBase.{u}.S.card) :
    k2Code3 d = blockPt 2 1 ∨ (∃ m, 4 ≤ m ∧ k2Code3 d = blockPt m 1) ∨
      (∃ m, 3 ≤ m ∧ k2Code3 d = blockPt m 3) := by
  change orbitMap 3 k2P (k2AttLabel d) = _ ∨ (∃ m, 4 ≤ m ∧ orbitMap 3 k2P (k2AttLabel d) = _) ∨
    (∃ m, 3 ≤ m ∧ orbitMap 3 k2P (k2AttLabel d) = _)
  rcases k2AttLabel_cases d with h | h | h <;> rw [h]
  · have hy : IsKey 3 k2P.{u} ⊤ := isKey_of_apply_eq (d := d) h top_ne_bot
    have hr := two_le_keyRank hy (k2P_one_isKey 3) (by
      rw [visibilityReplace_top, visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_lt_top _ _)
    exact .inr (.inr (orbitMap_of_not_isOrbitKey_of_two_le top_ne_bot hy
      (fun h ↦ h.ne_top rfl) hr))
  · refine .inl (orbitMap_blockPt_one_one (by omega) h fun e _ ↦ ?_)
    change blockPt 1 3 ≤ visibilityReplace 3 3 (k2AttLabel e)
    rcases k2AttLabel_cases e with h' | h' | h' <;> rw [h']
    · exact le_top
    · rw [visibilityReplace_blockPt_of_lt (by omega)]
    · rw [visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_le_blockPt_iff.mpr (.inl one_lt_two)
  · have hr := two_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot 2 1)) (k2P_one_isKey 3) (by
      rw [visibilityReplace_blockPt_of_lt (by omega), visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_lt_blockPt_iff.mpr (.inl one_lt_two))
    exact .inr (.inl (orbitMap_blockPt_one_of_two_le one_le_two (by omega) h hr))

theorem k2Code3_one : k2Code3.{u} (1 : Fin 8) = blockPt 2 1 := orbitCode_k2P_one (by omega)

theorem k2Code3_five : ∃ m, 4 ≤ m ∧ k2Code3.{u} (5 : Fin 8) = blockPt m 1 := by
  change ∃ m, 4 ≤ m ∧ orbitMap 3 k2P (k2AttLabel 5) = _
  rw [k2AttLabel_five]
  have hr := two_le_keyRank (isKey_of_apply_eq (d := (5 : Fin 8)) k2AttLabel_five
    (blockPt_ne_bot 2 1)) (k2P_one_isKey 3) (by
      rw [visibilityReplace_blockPt_of_lt (by omega), visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_lt_blockPt_iff.mpr (.inl one_lt_two))
  exact orbitMap_blockPt_one_of_two_le one_le_two (by omega) k2AttLabel_five hr

theorem k2Code3_one_isKey : IsKey 2 k2Code3.{u} (blockPt 2 1) :=
  isKey_of_apply_eq (d := (1 : Fin 8)) k2Code3_one (blockPt_ne_bot 2 1)

/-- Every orbit code at the grade two of `k2Code3` lies at least at `ω * 2`. -/
theorem blockPt_le_orbitCode_k2Code3 (d : Fin k2AttachmentBase.{u}.S.card) :
    blockPt 2 0 ≤ orbitCode 2 k2Code3.{u} d := by
  change blockPt 2 0 ≤ orbitMap 2 k2Code3 (k2Code3 d)
  rcases k2Code3_cases d with h | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ <;> rw [h]
  · exact blockPt_le_orbitMap_blockPt_one (r := 1) one_le_two le_rfl h
      (one_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot 2 1)))
  · exact blockPt_le_orbitMap_blockPt_one (r := 1) (by omega) le_rfl h
      (one_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot m 1)))
  · have hr := two_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot m 3)) k2Code3_one_isKey (by
      rw [visibilityReplace_blockPt_of_lt (by omega), visibilityReplace_blockPt_of_le (by omega)]
      exact blockPt_lt_blockPt_iff.mpr (.inl (by omega)))
    refine le_trans ?_ (blockPt_le_orbitMap (r := 2) (blockPt_ne_bot m 3) (fun h ↦ ?_) hr)
    · exact blockPt_le_blockPt_iff.mpr (by omega)
    · rw [visibilityReplace_blockPt_of_le (by omega), gridPoint_eq_blockPt] at h
      have := blockPt_le_blockPt_iff.mp h.2.le
      omega

theorem blockPt_le_orbitCode_k2Code3_five :
    blockPt 4 0 ≤ orbitCode 2 k2Code3.{u} (5 : Fin 8) := by
  obtain ⟨m, hm, h⟩ := k2Code3_five.{u}
  change blockPt 4 0 ≤ orbitMap 2 k2Code3 (k2Code3 (5 : Fin 8))
  rw [h]
  have hr := two_le_keyRank (isKey_of_apply_eq (d := (5 : Fin 8)) h (blockPt_ne_bot m 1))
    k2Code3_one_isKey (by
      rw [visibilityReplace_blockPt_of_lt (by omega), visibilityReplace_blockPt_of_lt (by omega)]
      exact blockPt_lt_blockPt_iff.mpr (.inl (by omega)))
  exact blockPt_le_orbitMap_blockPt_one (r := 2) (by omega) le_rfl h hr

/-! ### The separated admitted state -/

/-- The attachment row as a labelling of the cells of the attachment. -/
noncomputable abbrev k2A : Fin k2AttachmentBase.{u}.S.card → Label.{u} := fun e ↦ attRow e

theorem k2A_five_isKey : IsKey 2 k2A.{u} (blockPt 1 1) :=
  isKey_of_apply_eq (d := (5 : Fin 8)) attRow_five (blockPt_ne_bot 1 1)

/-- Every value of the separated admitted state lies at least at `ω * 2`. -/
theorem blockPt_le_k2SepState (d : Fin k2AttachmentBase.{u}.S.card) :
    blockPt 2 0 ≤ k2SepState.{u} d := by
  change blockPt 2 0 ≤ orbitMap 2 k2A (attRow d)
  rcases attRow_cases d with h | h | h <;> rw [h]
  · exact blockPt_le_orbitMap_blockPt_one (r := 1) one_le_two le_rfl h
      (one_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot 2 1)))
  · exact blockPt_le_orbitMap_blockPt_one (r := 1) le_rfl le_rfl h
      (one_le_keyRank k2A_five_isKey)
  · have hr := two_le_keyRank (isKey_of_apply_eq h (blockPt_ne_bot 2 2)) k2A_five_isKey (by
      rw [visibilityReplace_blockPt_of_lt (by omega), visibilityReplace_blockPt_of_le le_rfl]
      exact blockPt_lt_blockPt_iff.mpr (.inl one_lt_two))
    refine le_trans ?_ (blockPt_le_orbitMap (r := 2) (blockPt_ne_bot 2 2) (fun h ↦ ?_) hr)
    · exact blockPt_le_blockPt_iff.mpr (by omega)
    · rw [visibilityReplace_blockPt_of_le le_rfl, gridPoint_eq_blockPt] at h
      have := blockPt_le_blockPt_iff.mp h.2.le
      omega

/-- The separated admitted state at the cell `5` is `ω * 2 + 1`. -/
theorem k2SepState_five : k2SepState.{u} (5 : Fin 8) = blockPt 2 1 := by
  change orbitMap 2 k2A (attRow 5) = _
  rw [attRow_five]
  refine orbitMap_blockPt_one_one le_rfl attRow_five fun e _ ↦ ?_
  change blockPt 1 2 ≤ visibilityReplace 2 2 (attRow e)
  rcases attRow_cases e with h | h | h <;> rw [h]
  · rw [visibilityReplace_blockPt_of_lt (by omega)]
    exact blockPt_le_blockPt_iff.mpr (.inl one_lt_two)
  · rw [visibilityReplace_blockPt_of_lt (by omega)]
  · rw [visibilityReplace_blockPt_of_le le_rfl]
    exact blockPt_le_blockPt_iff.mpr (.inl one_lt_two)

/-! ### The two labels -/

/-- Every attachment label lies at least at `ω + 1`. -/
theorem blockPt_le_k2P (d : Fin k2AttachmentBase.{u}.S.card) : blockPt 1 1 ≤ k2P.{u} d := by
  change blockPt 1 1 ≤ k2AttLabel d
  rcases k2AttLabel_cases d with h | h | h <;> rw [h]
  · exact le_top
  · exact blockPt_le_blockPt_iff.mpr (.inl one_lt_two)

/-- **The grade-two label at the controller of the separated admitted state is `3`.**  The code of
the attachment labels reads the controller as `ω + 2`, below the key of every code, so the
decoder reads the least admissible label, `3`, below the value `ω + 1` of the cell `1`. -/
theorem k2Grade2Label_k2SepCell_eq_blockPt : k2Grade2Label.{u} k2SepCell = blockPt 0 3 := by
  unfold k2Grade2Label k2SepCell
  rw [k2Phi_natAdd, Equiv.symm_apply_apply]
  have hbase := blockPt_le_orbitCode_k2P.{u} (k := 2) le_rfl
  have haH : agreementHeight (grid 2 16) k2Code.{u} k2SepState = blockPt 1 2 :=
    agreementHeight_eq_blockPt_one
      (fun d ↦ (blockPt_le_blockPt_iff.mpr (.inl one_lt_two)).trans (hbase d))
      (fun d ↦ (blockPt_le_blockPt_iff.mpr (.inl one_lt_two)).trans (blockPt_le_k2SepState d))
      (5 : Fin 8)
      (by rw [k2SepState_five]; exact blockPt_lt_blockPt_iff.mpr (.inr ⟨rfl, one_lt_two⟩))
      ((blockPt_le_blockPt_iff.mpr (.inl (by omega))).trans (blockPt_le_orbitCode_k2P_five le_rfl))
  rw [haH]
  refine upperDecoderAt_eq_of_lt (blockPt_ne_bot 1 2) (fun d ↦ ?_) ?_ (fun d ↦ ?_) (1 : Fin 8) ?_ ?_
  · rw [visibilityReplace_blockPt_of_le le_rfl]
    exact (blockPt_lt_blockPt_iff.mpr (.inl one_lt_two)).trans_le
      ((hbase d).trans (le_visibilityReplace (by omega) _))
  · exact (min_le_right _ _).trans (blockPt_le_blockPt_iff.mpr (.inr ⟨rfl, by omega⟩))
  · exact blockPt_le_admissibleBelowAt (Nat.zero_le _)
      ((blockPt_le_blockPt_iff.mpr (.inl Nat.zero_lt_one)).trans (blockPt_le_k2P d))
  · rw [k2AttLabel_one]
    exact admissibleBelowAt_eq_blockPt (Nat.zero_le _)
      (blockPt_le_blockPt_iff.mpr (.inl Nat.zero_lt_one))
      (blockPt_lt_blockPt_iff.mpr (.inr ⟨rfl, by omega⟩))
  · exact blockPt_le_blockPt_iff.mpr (.inl (by omega))

/-- **The grade-three label at the controller of the separated admitted state is `4`.**  The code
at the grade two of `k2Code3` reads the controller as `ω + 2`; the decoder at the grade two over
`k2Code3` reads it as `ω + 3`, the least admissible label below the value `ω * 2 + 1` of the cell
`1`, and the decoder at the grade three over the attachment labels reads that as `4`, the least
admissible label at the cap grade four below the value `ω + 1` of the cell `1`. -/
theorem k2Grade3Label_k2SepCell_eq_blockPt :
    k2Grade3Label.{u} (Fin.castAdd _ k2SepCell) = blockPt 0 4 := by
  unfold k2Grade3Label
  rw [k2Phi3_castAdd]
  unfold k2Sec3 k2SepCell
  rw [k2Phi_natAdd, Equiv.symm_apply_apply]
  have hbase := blockPt_le_orbitCode_k2Code3.{u}
  have hbase3 := blockPt_le_orbitCode_k2P.{u} (k := 3) (by omega)
  have haH : agreementHeight (grid 2 16) (orbitCode 2 k2Code3.{u}) k2SepState = blockPt 1 2 :=
    agreementHeight_eq_blockPt_one
      (fun d ↦ (blockPt_le_blockPt_iff.mpr (.inl one_lt_two)).trans (hbase d))
      (fun d ↦ (blockPt_le_blockPt_iff.mpr (.inl one_lt_two)).trans (blockPt_le_k2SepState d))
      (5 : Fin 8)
      (by rw [k2SepState_five]; exact blockPt_lt_blockPt_iff.mpr (.inr ⟨rfl, one_lt_two⟩))
      ((blockPt_le_blockPt_iff.mpr (.inl (by omega))).trans blockPt_le_orbitCode_k2Code3_five)
  rw [haH]
  have hinner : upperDecoderAt 2 3 16 k2Code3.{u} (blockPt 1 2) = blockPt 1 3 := by
    refine upperDecoderAt_eq_of_lt (blockPt_ne_bot 1 2) (fun d ↦ ?_) ?_ (fun d ↦ ?_) (1 : Fin 8)
      ?_ ?_
    · rw [visibilityReplace_blockPt_of_le le_rfl]
      exact (blockPt_lt_blockPt_iff.mpr (.inl one_lt_two)).trans_le
        ((hbase d).trans (le_visibilityReplace (by omega) _))
    · exact (min_le_right _ _).trans (blockPt_le_blockPt_iff.mpr (.inl Nat.zero_lt_one))
    · exact blockPt_le_admissibleBelowAt (by omega)
        ((blockPt_le_blockPt_iff.mpr (.inl one_lt_two)).trans (hbase3 d))
    · rw [k2Code3_one]
      exact admissibleBelowAt_eq_blockPt (by omega)
        (blockPt_le_blockPt_iff.mpr (.inl one_lt_two))
        (blockPt_lt_blockPt_iff.mpr (.inr ⟨rfl, by omega⟩))
    · exact blockPt_le_blockPt_iff.mpr (.inl (by omega))
  rw [hinner]
  refine upperDecoderAt_eq_of_lt (blockPt_ne_bot 1 3) (fun d ↦ ?_) ?_ (fun d ↦ ?_) (1 : Fin 8) ?_ ?_
  · rw [visibilityReplace_blockPt_of_le le_rfl]
    exact (blockPt_lt_blockPt_iff.mpr (.inl one_lt_two)).trans_le
      ((hbase3 d).trans (le_visibilityReplace (by omega) _))
  · exact (min_le_right _ _).trans (blockPt_le_blockPt_iff.mpr (.inr ⟨rfl, by omega⟩))
  · exact blockPt_le_admissibleBelowAt (Nat.zero_le _)
      ((blockPt_le_blockPt_iff.mpr (.inl Nat.zero_lt_one)).trans (blockPt_le_k2P d))
  · rw [k2AttLabel_one]
    exact admissibleBelowAt_eq_blockPt (Nat.zero_le _)
      (blockPt_le_blockPt_iff.mpr (.inl Nat.zero_lt_one))
      (blockPt_lt_blockPt_iff.mpr (.inr ⟨rfl, by omega⟩))
  · exact blockPt_le_blockPt_iff.mpr (.inl (by omega))

/-- **The grade-two label at the controller of the separated admitted state is `3`.** -/
theorem k2Grade2Label_k2SepCell : k2Grade2Label.{u} k2SepCell = 3 :=
  k2Grade2Label_k2SepCell_eq_blockPt.trans (by simp [blockPt])

/-- **The grade-three label at the controller of the separated admitted state is `4`.** -/
theorem k2Grade3Label_k2SepCell : k2Grade3Label.{u} (Fin.castAdd _ k2SepCell) = 4 :=
  k2Grade3Label_k2SepCell_eq_blockPt.trans (by simp [blockPt])

/-- **The grade-three labels do not extend the grade-two labels**: they differ at the controller of
the separated admitted state. -/
theorem k2Grade3Label_k2SepCell_ne :
    k2Grade3Label.{u} (Fin.castAdd _ k2SepCell) ≠ k2Grade2Label k2SepCell := by
  rw [k2Grade3Label_k2SepCell_eq_blockPt, k2Grade2Label_k2SepCell_eq_blockPt]
  intro h
  have := blockPt_le_blockPt_iff.mp h.le
  omega

end VaughtConjecture.ProcessRank

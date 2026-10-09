/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeThreeDecoder

/-!
# Recovery of the ladder base through the upper decoder

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

A level of grade `k` renders a state `P` through the upper decoder of `P` applied to the row
labelling of its orbit code `orbitCode k P`.  On the ladder base (the cells of the attachment and
the ladder points) the row labelling of a code is its extension with a rank member
(`Scheme.LadderBaseData.stateExtOf`).  **Decoding the ladder base of the code gives the ladder base
of the state** (`Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode`), ranks included:

* the orbit map is injective and order-reflecting on the values of the state
  (`Label.orbitCode_eq_iff`, `Label.orbitCode_le_iff`), so the code has the value ranks of the state
  (`Label.valueRank_orbitCode`, `Label.rankVector_orbitCode`) and its value table is the orbit map
  of the value table of the state (`Label.valueTable_orbitCode`);
* the rank member read from the grade one of the code is that of the state
  (`Scheme.LadderBaseData.ofLawfulBelowOne_orbitCode`);
* the upper decoder reads the positive table of the code as the positive table of the state, for a
  state with values self-visible at `1` and some value other than `⊥`
  (`Label.upperDecoderAt_posTable_orbitCode`).  For the bottom state the ladder value `1` is read as
  the gap value `ω * B + K` (no cell has a positive code), so a positive value is assumed.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset
open scoped Ordinal

namespace Label

variable {ι : Type*} [Fintype ι] {k : ℕ} {w : ι → Label.{u}}

/-- **The orbit code is injective on the values**: two cells have the same code exactly when they
have the same value. -/
theorem orbitCode_eq_iff {d e : ι} : orbitCode k w d = orbitCode k w e ↔ w d = w e := by
  refine ⟨fun hc ↦ ?_, fun h ↦ by rw [orbitCode_apply, orbitCode_apply, h]⟩
  by_cases hd : w d = ⊥
  · rw [hd]; exact (orbitCode_eq_bot_iff.mp (hc.symm.trans (orbitCode_eq_bot_iff.mpr hd))).symm
  have he : w e ≠ ⊥ := fun h0 ↦
    hd (orbitCode_eq_bot_iff.mp (hc.trans (orbitCode_eq_bot_iff.mpr h0)))
  have hkey : visibilityReplace k k (w d) = visibilityReplace k k (w e) := le_antisymm
    ((visibilityReplace_orbitCode_le_iff he hd).mp (by rw [hc]))
    ((visibilityReplace_orbitCode_le_iff hd he).mp (by rw [hc]))
  by_cases hok : IsOrbitKey k w (w d)
  · have hok' : IsOrbitKey k w (w e) := (isOrbitKey_congr hkey).mp hok
    rw [orbitCode_apply, orbitCode_apply, orbitMap_of_isOrbitKey hok, orbitMap_of_isOrbitKey hok',
      codeBlock_congr hkey] at hc
    have h1 := congrArg (moveToBlock (w d)) hc
    rwa [moveToBlock_moveToBlock, moveToBlock_moveToBlock, moveToBlock_eq_self rfl,
      moveToBlock_eq_self hkey] at h1
  · have hok' : ¬ IsOrbitKey k w (w e) := fun h ↦ hok ((isOrbitKey_congr hkey).mpr h)
    have hvd : IsSelfVisible k (w d) := by_contra fun hn ↦ hok ⟨d, rfl, hn⟩
    have hve : IsSelfVisible k (w e) := by_contra fun hn ↦ hok' ⟨e, rfl, hn⟩
    exact hvd.symm.trans (hkey.trans hve)

/-- **The orbit code reflects the order of the values.** -/
theorem orbitCode_le_iff {d e : ι} : orbitCode k w d ≤ orbitCode k w e ↔ w d ≤ w e := by
  refine ⟨fun h ↦ ?_, fun h ↦ monotone_orbitMap k w h⟩
  by_contra hlt
  have h' := monotone_orbitMap k w (not_le.mp hlt).le
  have heq : orbitCode k w d = orbitCode k w e := le_antisymm h h'
  exact hlt (orbitCode_eq_iff.mp heq).le

/-- **The orbit code keeps the value ranks.** -/
theorem valueRank_orbitCode (d : ι) :
    valueRank (orbitCode k w) (orbitCode k w d) = valueRank w (w d) := by
  classical
  unfold valueRank
  symm
  refine Finset.card_bij (fun y _ ↦ orbitMap k w y) (fun y hy ↦ ?_) (fun y hy y' hy' h ↦ ?_)
    fun z hz ↦ ?_
  · simp only [mem_filter, mem_image, mem_univ, true_and] at hy ⊢
    obtain ⟨⟨e, rfl⟩, h0, hle⟩ := hy
    exact ⟨⟨e, rfl⟩, fun h ↦ h0 (orbitMap_eq_bot_iff.mp h), monotone_orbitMap k w hle⟩
  · simp only [mem_filter, mem_image, mem_univ, true_and] at hy hy'
    obtain ⟨⟨e, rfl⟩, -⟩ := hy
    obtain ⟨⟨e', rfl⟩, -⟩ := hy'
    exact orbitCode_eq_iff.mp h
  · simp only [mem_filter, mem_image, mem_univ, true_and] at hz
    obtain ⟨⟨e, rfl⟩, h0, hle⟩ := hz
    refine ⟨w e, ?_, rfl⟩
    simp only [mem_filter, mem_image, mem_univ, true_and]
    exact ⟨⟨e, rfl⟩, fun h ↦ h0 (orbitCode_eq_bot_iff.mpr h), orbitCode_le_iff.mp hle⟩

/-- **The orbit code keeps the rank vector.** -/
theorem rankVector_orbitCode (d : ι) : rankVector (orbitCode k w) d = rankVector w d :=
  valueRank_orbitCode d

/-- **The value table of the code is the orbit map of the value table of the state.** -/
theorem valueTable_orbitCode (i : ℕ) :
    valueTable (orbitCode k w) i = orbitMap k w (valueTable w i) := by
  classical
  unfold valueTable
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder _ (monotone_orbitMap k w) orbitMap_bot]
  refine Finset.sup_congr (Finset.filter_congr fun e _ ↦ ?_) fun _ _ ↦ rfl
  rw [valueRank_orbitCode]

/-- A value of a state self-visible at `1` has its code self-visible at `1`, for `1 ≤ k`. -/
theorem isSelfVisible_one_orbitCode (hk : 1 ≤ k) {d : ι} (hd : IsSelfVisible 1 (w d)) :
    IsSelfVisible 1 (orbitCode k w d) :=
  (isWitness_orbitMap k w).isSelfVisible_apply hd (by rw [stepSuppressor_of_le hk]; exact le_top)

/-- **The upper decoder reads the positive table of the code as the positive table of the state**,
at a grade `k ≥ 2`, for a state with values self-visible at `1` and some value other than `⊥`. -/
theorem upperDecoderAt_posTable_orbitCode (hk : 2 ≤ k) {K B : ℕ}
    (hv1 : ∀ d, IsSelfVisible 1 (w d)) (hpos : ∃ d, w d ≠ ⊥) (i : ℕ) :
    upperDecoderAt k K B w (posTable (orbitCode k w) i) = posTable w i := by
  classical
  unfold posTable
  by_cases hi : i = 0
  · simp only [hi, ite_true, upperDecoderAt_bot]
  simp only [hi, ite_false]
  rw [valueTable_orbitCode]
  -- the value table at a positive rank is a positive value of the state
  obtain ⟨d₀, hd₀⟩ := hpos
  have hV : 1 ≤ #((univ.image w).filter (· ≠ ⊥)) :=
    card_pos.mpr ⟨w d₀, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), hd₀⟩⟩
  obtain ⟨e₁, he₁0, he₁⟩ := exists_valueRank_eq (Z := w) Nat.one_pos hV
  have hmem : e₁ ∈ univ.filter fun e ↦ valueRank w (w e) ≤ i :=
    mem_filter.mpr ⟨mem_univ _, by omega⟩
  obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_sup _ ⟨e₁, hmem⟩ w
  have hve : valueTable w i = w e := he
  have hle1 : w e₁ ≤ w e := by rw [← hve]; exact Finset.le_sup (f := w) hmem
  have he0 : w e ≠ ⊥ := fun h0 ↦ he₁0 (le_bot_iff.mp (h0 ▸ hle1))
  have h1 : (1 : Label.{u}) ≤ w e := one_le_of_isSelfVisible (hv1 e) he0
  have h1' : (1 : Label.{u}) ≤ orbitCode k w e :=
    one_le_of_isSelfVisible (isSelfVisible_one_orbitCode (by omega) (hv1 e))
      (fun h ↦ he0 (orbitCode_eq_bot_iff.mp h))
  rw [hve, max_eq_left h1, ← orbitCode_apply, max_eq_left h1']
  exact upperDecoderAt_orbitCode e

end Label

namespace Scheme.LadderBaseData

open Label

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ}

/-- **The rank member of the code is the rank member of the state**: the rank member read from
the grade one depends only on the rank vector, which the orbit code keeps. -/
theorem ofLawfulBelowOne_orbitCode (hcard : B.S.card ≤ H) {k : ℕ} {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d)
    (hC : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ orbitCode k R d) :
    RankMember.ofLawfulBelowOne B.wf hcard hC = RankMember.ofLawfulBelowOne B.wf hcard hR :=
  Subtype.ext (funext fun d ↦ Fin.ext (Label.rankVector_orbitCode d))

/-- **Decoding the ladder base of the code gives the ladder base of the state**: for a rank
member `a`, at a grade `k ≥ 2`, a state with values self-visible at `1` and some value other than
`⊥`, the upper decoder of the state reads the extension of its orbit code as the extension of the
state, on the cells of the attachment (the code read literally) and on the ladder (the positive
tables, `Label.upperDecoderAt_posTable_orbitCode`). -/
theorem upperDecoderAt_stateExtOf_orbitCode {k K B' : ℕ} (hk : 2 ≤ k)
    {R : Fin B.S.card → Label.{u}} (hv1 : ∀ d, IsSelfVisible 1 (R d)) (hpos : ∃ d, R d ≠ ⊥)
    (a : RankMember B.S H) (t : Fin (B.ladderBase H).card) :
    upperDecoderAt k K B' R (B.stateExtOf (orbitCode k R) a t) = B.stateExtOf R a t := by
  induction t using Fin.addCases with
  | left d =>
    change upperDecoderAt k K B' R (Fin.append _ _ (Fin.castAdd _ d)) = Fin.append _ _ _
    rw [Fin.append_left, Fin.append_left]
    exact upperDecoderAt_orbitCode d
  | right j =>
    change upperDecoderAt k K B' R (Fin.append _ _ (Fin.natAdd _ j)) = Fin.append _ _ _
    rw [Fin.append_right, Fin.append_right]
    exact Label.upperDecoderAt_posTable_orbitCode hk hv1 hpos _

/-- **The ladder base, ranks included, is recovered from the code**: with the rank members read
from the grade one, the upper decoder of the state reads the extension of its code as the
extension of the state. -/
theorem upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne (hcard : B.S.card ≤ H) {k K B' : ℕ}
    (hk : 2 ≤ k) {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d)
    (hC : B.S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ orbitCode k R d)
    (hv1 : ∀ d, IsSelfVisible 1 (R d)) (hpos : ∃ d, R d ≠ ⊥) (t : Fin (B.ladderBase H).card) :
    upperDecoderAt k K B' R
        (B.stateExtOf (orbitCode k R) (RankMember.ofLawfulBelowOne B.wf hcard hC) t) =
      B.stateExtOf R (RankMember.ofLawfulBelowOne B.wf hcard hR) t := by
  rw [ofLawfulBelowOne_orbitCode hcard hR hC]
  exact upperDecoderAt_stateExtOf_orbitCode hk hv1 hpos _ t

end Scheme.LadderBaseData

end VaughtConjecture

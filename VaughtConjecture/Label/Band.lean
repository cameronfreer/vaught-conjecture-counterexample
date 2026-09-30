/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Cap
import VaughtConjecture.Label.Transform

/-!
# The band map and the band rule

Roadmap, Layer 1 (the bounded transformations used by the construction: the band rule; guarded
composition retains its guards); semantic contract, item 3.

Fix ordinals `α` and `β` and a natural number `K`.  The *translation* `translate α β` sends an
ordinal `ν` to `α + (ν - β)` and fixes bottom and the formal top; it carries the band of `β` onto
the band of `α`, and every ordinal below `β` to `α`.  The *band map* `bandMap α β K` is the
translation capped at `α + K`:

* bottom goes to bottom, and the formal top to `α + K` (`bandMap_bot`, `bandMap_top`);
* an ordinal `ν ≤ β` goes to `α` (`bandMap_coe_of_le`);
* `β + j` goes to `α + min j K` for a natural number `j` (`bandMap_coe_add_natCast`);
* every label at least `β + K` goes to `α + K` (`bandMap_of_le`).

The band map is monotone, lies between `α` and `α + K` off bottom, and, when `α` and `β` are zero
or limits, commutes on the labels `≥ β` with visibility replacement at every threshold `k ≤ K`
(`bandMap_visibilityReplace`).

**The band rule** (`IsWitness.transformsTo_bandMap`).  Let `σ` be a shifter normalized at `K`,
`α` a limit, and `β` zero or a limit, on a finite family of cells of grades `≤ K`.  If the
source labelling `p` is sent by `σ` below `α` or to the formal top, and to the formal top only
from labels `≥ β`, then `p` transforms to the labelling that keeps the values of `σ ∘ p` below
`α` and replaces each formal top by the band map of its source label.  The shifter
(`IsWitness.band`) keeps the values of `σ` below `α` capped at a permitted cutoff `c`, self-visible
at `K`, that bounds the finitely many values used; it applies the band map to the labels `≥ β`
sent to `α` or above, and sends the remaining labels to `c`.

## References

The band rule is the post-composition of the top-witness row in the proof of
[Kni26, Lemma 5.3.5], and the band map is the map it composes with; the remaining rows of that
proof need a splice of two witnesses, not stated here.  The transformation relation is
[Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture.Label

open Order

variable {D : Type*} {grade : D → ℕ} {p q : D → Label.{u}}
  {σ : Label.{u} → Label.{u}} {α β ν : Ordinal.{u}} {K k i : ℕ} {x c : Label.{u}}

/-! ### Translation -/

/-- Translation of labels from `β` to `α`: an ordinal `ν` goes to `α + (ν - β)` (so every
ordinal `≤ β` goes to `α`), and bottom and the formal top are fixed. -/
noncomputable def translate (α β : Ordinal.{u}) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun ν ↦ α + (ν - β))

/-- Translation fixes bottom. -/
@[simp] theorem translate_bot (α β : Ordinal.{u}) : translate α β (⊥ : Label.{u}) = ⊥ := rfl

/-- Translation fixes the formal top. -/
@[simp] theorem translate_top (α β : Ordinal.{u}) : translate α β (⊤ : Label.{u}) = ⊤ := rfl

/-- Translation of an ordinal label. -/
@[simp] theorem translate_coe (α β ν : Ordinal.{u}) :
    translate α β (ν : Label.{u}) = ((α + (ν - β) : Ordinal.{u}) : Label.{u}) := rfl

/-- Translation is monotone. -/
theorem monotone_translate (α β : Ordinal.{u}) : Monotone (translate α β) := by
  have h : Monotone fun ν : Ordinal.{u} ↦ α + (ν - β) := fun a b h ↦
    (add_le_add_iff_left α).mpr (Ordinal.sub_le.mpr (h.trans (Ordinal.le_add_sub b β)))
  exact h.withTop_map.withBot_map

/-- Translation sends every label other than bottom to a label at least `α`. -/
theorem coe_le_translate (hx : x ≠ ⊥) : (α : Label.{u}) ≤ translate α β x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | coe ν => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
  | top => exact le_top

/-- When `α` and `β` are zero or limits, translation from `β` to `α` commutes with visibility
replacement on the labels `≥ β`. -/
theorem translate_visibilityReplace (hα : IsSuccPrelimit α) (hβ : IsSuccPrelimit β)
    (hx : (β : Label.{u}) ≤ x) (k i : ℕ) :
    translate α β (visibilityReplace k i x) = visibilityReplace k i (translate α β x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe ν =>
    obtain ⟨δ, rfl⟩ : ∃ δ, ν = β + δ :=
      ⟨ν - β,
        (Ordinal.add_sub_cancel_of_le (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hx))).symm⟩
    simp only [visibilityReplace_coe, translate_coe]
    rw [Ordinal.visibilityReplace_add hβ, Ordinal.add_sub_cancel, Ordinal.add_sub_cancel,
      Ordinal.visibilityReplace_add hα]
  | top => rfl

/-! ### The band map -/

/-- The band map from `β` to `α` truncated at `K`: the translation from `β` to `α` capped at
`α + K`.  It sends bottom to bottom, an ordinal `ν ≤ β` to `α`, `β + j` to `α + min j K`, and
every label at least `β + K`, including the formal top, to `α + K`. -/
noncomputable def bandMap (α β : Ordinal.{u}) (K : ℕ) (x : Label.{u}) : Label.{u} :=
  min (translate α β x) ((α + K : Ordinal.{u}) : Label.{u})

/-- The band map fixes bottom. -/
@[simp] theorem bandMap_bot (α β : Ordinal.{u}) (K : ℕ) : bandMap α β K ⊥ = ⊥ := by
  simp [bandMap]

/-- The band map sends the formal top to `α + K`. -/
@[simp] theorem bandMap_top (α β : Ordinal.{u}) (K : ℕ) :
    bandMap α β K ⊤ = ((α + K : Ordinal.{u}) : Label.{u}) := by
  simp only [bandMap, translate_top, min_eq_right le_top]

/-- The band map sends an ordinal `ν` to `α + min (ν - β) K`. -/
@[simp] theorem bandMap_coe (α β : Ordinal.{u}) (K : ℕ) (ν : Ordinal.{u}) :
    bandMap α β K ν = ((α + min (ν - β) K : Ordinal.{u}) : Label.{u}) := by
  rw [bandMap, translate_coe, ← min_add_add_left, WithTop.coe_min, WithBot.coe_min]

/-- The band map sends every ordinal `ν ≤ β` to `α`. -/
theorem bandMap_coe_of_le (h : ν ≤ β) (K : ℕ) : bandMap α β K ν = α := by
  rw [bandMap_coe, Ordinal.sub_eq_zero_iff_le.mpr h, min_eq_left (by simp), add_zero]

/-- The band map sends `β + j` to `α + min j K`. -/
theorem bandMap_coe_add_natCast (K j : ℕ) :
    bandMap α β K ((β + j : Ordinal.{u}) : Label.{u}) =
      ((α + (min j K : ℕ) : Ordinal.{u}) : Label.{u}) := by
  rw [bandMap_coe, Ordinal.add_sub_cancel, Nat.mono_cast.map_min]

/-- The band map sends every label at least `β + K` to `α + K`. -/
theorem bandMap_of_le (h : ((β + K : Ordinal.{u}) : Label.{u}) ≤ x) :
    bandMap α β K x = ((α + K : Ordinal.{u}) : Label.{u}) := by
  refine min_eq_right ((monotone_translate α β h).trans' ?_)
  rw [translate_coe, Ordinal.add_sub_cancel]

/-- The band map is monotone. -/
theorem monotone_bandMap (α β : Ordinal.{u}) (K : ℕ) : Monotone (bandMap α β K) :=
  (monotone_translate α β).min monotone_const

/-- The band map sends every label other than bottom to a label at least `α`. -/
theorem coe_le_bandMap (hx : x ≠ ⊥) : (α : Label.{u}) ≤ bandMap α β K x :=
  le_min (coe_le_translate hx) (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add))

/-- The band map is at most `α + K`. -/
theorem bandMap_le (x : Label.{u}) : bandMap α β K x ≤ ((α + K : Ordinal.{u}) : Label.{u}) :=
  min_le_right _ _

/-- When `α` and `β` are zero or limits, the band map commutes on the labels `≥ β` with
visibility replacement at every threshold `k ≤ K` and every value `i ≤ k`. -/
theorem bandMap_visibilityReplace (hα : IsSuccPrelimit α) (hβ : IsSuccPrelimit β) (hk : k ≤ K)
    (hi : i ≤ k) (hx : (β : Label.{u}) ≤ x) :
    bandMap α β K (visibilityReplace k i x) = visibilityReplace k i (bandMap α β K x) := by
  rw [bandMap, bandMap, translate_visibilityReplace hα hβ hx,
    visibilityReplace_min_of_isSelfVisible hi (isSelfVisible_coe_add hα hk)]

/-! ### The band rule -/

/-- **The band shifter.**  Let `σ` be a shifter normalized at `K`, let `α` and `β` be zero or
limits, and let `c` be a permitted cutoff at stage `α` that is self-visible at `K`.  The shifter
that caps the values of `σ` below `α` at `c`, applies the band map from `β` to `α` truncated at
`K` to the labels `≥ β` that `σ` sends to `α` or above, and sends the remaining labels to `c`, is
normalized at `K`. -/
theorem IsWitness.band (hσ : IsWitness (stepSuppressor K) σ) (hα : IsSuccPrelimit α)
    (hβ : IsSuccPrelimit β) (hc : IsPermittedCutoff α c) (hcK : IsSelfVisible K c) :
    IsWitness (stepSuppressor K) fun x ↦
      if σ x < α then min (σ x) c else if (β : Label.{u}) ≤ x then bandMap α β K x else c := by
  set τ : Label.{u} → Label.{u} := fun x ↦
    if σ x < α then min (σ x) c else if (β : Label.{u}) ≤ x then bandMap α β K x else c
  have hge (x : Label.{u}) (hx : ¬ σ x < α) : c ≤ τ x := by
    simp only [τ, ite_eq_right hx]
    split_ifs with hβx
    · exact hc.2.le.trans (coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le hβx).ne')
    · exact le_rfl
  refine ⟨hσ.antitone, hσ.isSelfVisible, ?_, fun x y hxy ↦ ?_, fun x k hx i hi ↦ ?_⟩
  · simp [τ, hσ.map_bot]
  · by_cases hy : σ y < α
    · have hx : σ x < α := (hσ.monotone hxy).trans_lt hy
      simp only [τ, ite_eq_left hx, ite_eq_left hy]
      exact min_le_min_right _ (hσ.monotone hxy)
    by_cases hx : σ x < α
    · exact (by simp only [τ, ite_eq_left hx]; exact min_le_right _ _ : τ x ≤ c).trans (hge y hy)
    simp only [τ, ite_eq_right hx, ite_eq_right hy]
    split_ifs with hβx hβy hβy
    · exact monotone_bandMap α β K hxy
    · exact absurd (hβx.trans hxy) hβy
    · exact hc.2.le.trans (coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le hβy).ne')
    · exact le_rfl
  · rcases le_or_gt k K with hk | hk
    · have hcomm := hσ.visibilityReplace_comm x k (by simp [hk]) i hi
      have hlt : σ (visibilityReplace k i x) < α ↔ σ x < α := by
        rw [hcomm, visibilityReplace_lt_iff hα]
      have hβ' : (β : Label.{u}) ≤ visibilityReplace k i x ↔ (β : Label.{u}) ≤ x := by
        simpa only [not_lt] using (visibilityReplace_lt_iff hβ (k := k) (i := i) (x := x)).not
      simp only [τ]
      by_cases hσx : σ x < α
      · rw [ite_eq_left (hlt.mpr hσx), ite_eq_left hσx, hcomm,
          visibilityReplace_min_of_isSelfVisible hi (hcK.mono hk)]
      rw [ite_eq_right (mt hlt.mp hσx), ite_eq_right hσx]
      by_cases hβx : (β : Label.{u}) ≤ x
      · rw [ite_eq_left (hβ'.mpr hβx), ite_eq_left hβx, bandMap_visibilityReplace hα hβ hk hi hβx]
      · rw [ite_eq_right (mt hβ'.mp hβx), ite_eq_right hβx, (hcK.mono hk).visibilityReplace_eq]
    · rw [stepSuppressor_of_lt hk, le_bot_iff] at hx
      have hσx : σ x < α := by_contra fun h ↦ (hc.1.trans_le (hge x h)).ne' hx
      have hσx' : σ x = ⊥ := by
        simp only [τ, ite_eq_left hσx] at hx
        exact (min_eq_bot.mp hx).resolve_right hc.1.ne'
      have hvr := hσ.visibilityReplace_comm x k (hσx' ▸ bot_le) i hi
      rw [hσx', visibilityReplace_bot] at hvr
      rw [hx, visibilityReplace_bot]
      simp only [τ, hvr, ite_eq_left (WithBot.bot_lt_coe _), min_eq_left bot_le]

/-- **The band rule.**  Let `σ` be a shifter normalized at `K`, let `α` be a limit and `β` zero
or a limit, and let the family of cells be finite with all grades `≤ K`.  Suppose that `σ` sends
each source label `p d` below `α` or to the formal top, and to the formal top only when
`β ≤ p d`.  Then `p` transforms to any labelling `q` that agrees with `σ ∘ p` where it is below
`α` and is the band map of the source label where `σ ∘ p` is the formal top.  This is the
post-composition of the top-witness row in the proof of [Kni26, Lemma 5.3.5]; the other rows of
that proof need a two-witness splice (the band map applied to a row `r` with `p ⇒ r`, at grades
`≤ J ≤ K`), which is left to Layer 3. -/
theorem IsWitness.transformsTo_bandMap [Finite D] (hσ : IsWitness (stepSuppressor K) σ)
    (hα : IsSuccLimit α) (hβ : IsSuccPrelimit β) (hgr : ∀ d, grade d ≤ K)
    (hbound : ∀ d, σ (p d) < α ∨ σ (p d) = ⊤) (hlow : ∀ d, σ (p d) < α → q d = σ (p d))
    (htop : ∀ d, σ (p d) = ⊤ → (β : Label.{u}) ≤ p d ∧ q d = bandMap α β K (p d)) :
    TransformsTo grade p q := by
  obtain ⟨c, h0c, hcα, hcK, hbd⟩ := exists_isSelfVisible_bound hα.isSuccPrelimit K
    (b := ((0 : Ordinal.{u}) : Label.{u}))
    (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hα.pos)) (σ ∘ p)
  refine ⟨_, _, hσ.band hα.isSuccPrelimit hβ ⟨(WithBot.bot_lt_coe _).trans_le h0c, hcα⟩ hcK,
    fun d ↦ ?_⟩
  rw [stepSuppressor_of_le (hgr d), min_top_right]
  rcases hbound d with hd | hd
  · rw [ite_eq_left hd, hlow d hd]
    exact (min_eq_left (hbd d hd)).symm
  · obtain ⟨hβd, hqd⟩ := htop d hd
    rw [ite_eq_right (hd ▸ not_top_lt), ite_eq_left hβd, hqd]

end VaughtConjecture.Label

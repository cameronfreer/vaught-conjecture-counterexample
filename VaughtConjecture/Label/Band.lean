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
ordinal `ν` to `α + (ν - β)` and fixes bottom and the formal top; it carries the band
`[β, β + K]` onto the band `[α, α + K]`, and every ordinal below `β` to `α`.  The *band map*
`bandMap α β K` is the translation capped at `α + K`:

* bottom goes to bottom, and the formal top to `α + K` (`bandMap_bot`, `bandMap_top`);
* an ordinal `ν ≤ β` goes to `α` (`bandMap_coe_of_le`);
* `β + j` goes to `α + min j K` for a natural number `j` (`bandMap_coe_add_natCast`);
* every label at least `β + K` goes to `α + K` (`bandMap_of_le`).

The band map is monotone, lies between `α` and `α + K` off bottom, and, when `α` and `β` are zero
or limits, commutes on the labels `≥ β` with visibility replacement at every threshold `k ≤ K`
(`bandMap_visibilityReplace`).

**The band rule** (`IsWitness.transformsTo_bandMap`).  Let `σ` be a witness bounded by grade `K`
(`VaughtConjecture.Label.Transform`: `(stepSuppressor K, σ)` is a witness), `α` a limit, and `β`
zero or a limit, on a finite family of cells of grades `≤ K`.  If the source labelling `p` is sent
by `σ` below `α` or to the formal top, and to the formal top only from labels `≥ β`, then `p`
transforms to the labelling that keeps the values of `σ ∘ p` below `α` and replaces each formal top
by the band map of its source label.  The shifter (`IsWitness.band`) keeps the values of `σ` below
`α` capped at a permitted cutoff `c`, self-visible at `K`, that bounds the finitely many values
used; it applies the band map to the labels `≥ β` sent to `α` or above, and sends the remaining
labels to `c`.

**The splice of two witnesses** (`TransformsTo.splice_bandMap`).  On a finite family of cells of
grades at most `K`, if a source transforms to `q`, with values below a limit `β` or the formal top,
and to `r`, at least `μ` (zero or a limit) where `q` is the formal top, then it transforms to the
labelling equal to `q` where `q` is below `β` and to the band map from `μ` to `β` at `K` of `r`
where `q` is the formal top.  The band map keeps self-visibility at the grades at most `K` on the
labels at least `μ` (`isSelfVisible_bandMap`) and is strictly increasing below `μ + K`
(`bandMap_lt_bandMap`).

## References

The band rule is the post-composition, in the proof of [Kni26, Lemma 5.3.5], for the row of the
*top-witness cell* (the cell of full scope and grade `K` labelled by the formal top), and the band
map is the map it composes with; the rows of the other cells labelled by the formal top need a
splice of two witnesses with the same source (roadmap, Layer 3, 3.1), stated here in a general
form (`TransformsTo.splice_bandMap`).  The transformation relation is [Kni26, Definition 2.3.9].
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

/-- The band map from `β` to `α` at `K`: the translation from `β` to `α` capped at
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
  le_min (coe_le_translate hx) (coe_le_coe_add α K)

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

/-- **The band shifter.**  Let `σ` be a witness bounded by grade `K`, let `α` and `β` be zero or
limits, and let `c` be a permitted cutoff at stage `α` that is self-visible at `K`.
The shifter that caps the values of `σ` below `α` at `c`, applies the band map from `β` to `α` at
`K` to the labels `≥ β` that `σ` sends to `α` or above, and sends the remaining labels to `c`, is
a witness bounded by grade `K`. -/
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

/-- **The band rule.**  Let `σ` be a witness bounded by grade `K`, let `α` be a limit and `β`
zero or a limit, and let the family of cells be finite with all grades `≤ K`.
Suppose that `σ` sends each source label `p d` below `α` or to the formal top, and to the formal
top only when `β ≤ p d`.  Then `p` transforms to any labelling `q` that agrees with `σ ∘ p` where
it is below `α` and is the band map of the source label where `σ ∘ p` is the formal top.  This is
the post-composition for the row of the top-witness cell in the proof of [Kni26, Lemma 5.3.5]; the
rows of the other cells labelled by the formal top need a splice of two witnesses (the band map
applied to a row `r` with `p ⇒ r`, at grades `≤ J ≤ K`), `TransformsTo.splice_bandMap`. -/
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

/-! ### The splice of two witnesses -/

section Splice

variable {D : Type*} {grade : D → ℕ} {e q r T : D → Label.{u}} {β μ : Ordinal.{u}} {K : ℕ}

/-- A label between an ordinal and a stage is an ordinal below the stage. -/
private theorem exists_coe_eq_of_le_of_lt {x : Label.{u}} {o : Ordinal.{u}}
    (h₀ : (o : Label.{u}) ≤ x) (h : x < β) : ∃ ν : Ordinal.{u}, x = ν ∧ ν < β := by
  induction x using recBotCoeTop with
  | bot => exact absurd h₀ (not_le.mpr (WithBot.bot_lt_coe _))
  | coe ν => exact ⟨ν, rfl, WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)⟩
  | top => exact absurd h (not_lt.mpr le_top)

/-- On the labels at least `μ`, the band map at `K` keeps self-visibility at every `n ≤ K`. -/
theorem isSelfVisible_bandMap (hβ : IsSuccPrelimit β) (hμ : IsSuccPrelimit μ) {n : ℕ}
    (hn : n ≤ K) {y : Label.{u}} (hy : (μ : Label.{u}) ≤ y) (hv : IsSelfVisible n y) :
    IsSelfVisible n (bandMap β μ K y) := by
  unfold IsSelfVisible
  rw [← bandMap_visibilityReplace hβ hμ hn le_rfl hy, hv.visibilityReplace_eq]

/-- **The band map is strictly increasing below `μ + K`**: if `μ ≤ z < μ + K` and `z < y`, then
the band map at `K` is larger at `y` than at `z`. -/
theorem bandMap_lt_bandMap {y z : Label.{u}} (hz : (μ : Label.{u}) ≤ z)
    (hzK : z < ((μ + K : Ordinal.{u}) : Label.{u})) (hzy : z < y) :
    bandMap β μ K z < bandMap β μ K y := by
  obtain ⟨ν, rfl, -⟩ := exists_coe_eq_of_le_of_lt hz hzK
  have hν₁ : μ ≤ ν := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hz)
  have hν₂ : ν < μ + K := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hzK)
  obtain ⟨j, rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hν₁
    (hν₂.trans (add_lt_add_right (Ordinal.natCast_lt_omega0 K) μ))
  have hjK : j < K := by
    have := (add_lt_add_iff_left μ).mp hν₂
    exact_mod_cast this
  have hy : ((μ + (j + 1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤ y := by
    rw [Nat.cast_add_one, ← add_assoc]
    exact not_lt.mp fun h ↦ hzy.not_ge (lt_coe_add_one_iff.mp h)
  refine lt_of_lt_of_le ?_ (monotone_bandMap β μ K hy)
  rw [bandMap_coe_add_natCast, bandMap_coe_add_natCast, min_eq_left hjK.le,
    min_eq_left (Nat.succ_le_of_lt hjK)]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ((add_lt_add_iff_left β).mpr
    (by exact_mod_cast j.lt_succ_self)))

/-- **The splice of two witnesses with the same source.**  Let `β` be a limit and `μ` zero or a
limit, and let the family of cells be finite with all grades at most `K`.  Let the source `e`
transform to `q`, whose values are below `β` or the formal top, and to `r`, which is at least `μ`
at every cell where `q` is the formal top.  Then `e` transforms to every labelling `T` that agrees
with `q` where `q` is below `β` and is the band map of `r` (from `μ` to `β` at `K`) where `q` is
the formal top. -/
theorem TransformsTo.splice_bandMap [Finite D] (hβ : IsSuccLimit β) (hμ : IsSuccPrelimit μ)
    (hgr : ∀ d, grade d ≤ K) (h₁ : TransformsTo grade e q) (h₂ : TransformsTo grade e r)
    (hq : ∀ d, q d < β ∨ q d = ⊤) (hr : ∀ d, q d = ⊤ → (μ : Label.{u}) ≤ r d)
    (hlow : ∀ d, q d < β → T d = q d) (htop : ∀ d, q d = ⊤ → T d = bandMap β μ K (r d)) :
    TransformsTo grade e T := by
  classical
  obtain ⟨g₁, σ₁, hw₁, heq₁⟩ := h₁
  obtain ⟨g₂, σ₂, hw₂, heq₂⟩ := h₂
  have hβ' := hβ.isSuccPrelimit
  have h0β : ((0 : Ordinal.{u}) : Label.{u}) < β :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hβ.pos)
  -- two cutoffs `c₀ < c` below `β`, self-visible at `K`, with `c₀` above the values of `q` below
  -- `β`
  obtain ⟨c₀', h0c₀, hc₀β, hc₀K, hbd⟩ := exists_isSelfVisible_bound hβ' K h0β q
  obtain ⟨ν₀, rfl, hν₀β⟩ := exists_coe_eq_of_le_of_lt h0c₀ hc₀β
  obtain ⟨ν, hν₀ν, hνβ, hνK⟩ := exists_lt_lt_isSelfVisible hβ' hν₀β K
  have hc₀c : (ν₀ : Label.{u}) < ν := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hν₀ν)
  have hcβ : (ν : Label.{u}) < β := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hνβ)
  have hcband (y : Label.{u}) (hy : (μ : Label.{u}) ≤ y) : (ν : Label.{u}) < bandMap β μ K y :=
    hcβ.trans_le (coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le hy).ne')
  set σ : Label.{u} → Label.{u} := fun x ↦
    if σ₁ x < β then min (σ₁ x) ν
    else if (μ : Label.{u}) ≤ σ₂ x then bandMap β μ K (σ₂ x) else ν with hσdef
  set g : ℕ → Label.{u} := fun n ↦
    if K < n then ⊥
    else if g₁ n = ⊤ then (if (μ : Label.{u}) ≤ g₂ n then bandMap β μ K (g₂ n) else ν₀)
    else min (g₁ n) ν₀ with hgdef
  -- the three values of the shifter
  have hσlow (x : Label.{u}) (hx : σ₁ x < β) : σ x = min (σ₁ x) ν := ite_eq_left hx
  have hσband (x : Label.{u}) (hx : ¬ σ₁ x < β) (h2 : (μ : Label.{u}) ≤ σ₂ x) :
      σ x = bandMap β μ K (σ₂ x) :=
    (ite_eq_right hx).trans (ite_eq_left h2)
  have hσc (x : Label.{u}) (hx : ¬ σ₁ x < β) (h2 : ¬ (μ : Label.{u}) ≤ σ₂ x) : σ x = ν :=
    (ite_eq_right hx).trans (ite_eq_right h2)
  -- the four values of the suppressor
  have hgK (n : ℕ) (hn : K < n) : g n = ⊥ := ite_eq_left hn
  have hgB (n : ℕ) (hn : n ≤ K) (h1 : g₁ n = ⊤) (h2 : (μ : Label.{u}) ≤ g₂ n) :
      g n = bandMap β μ K (g₂ n) :=
    (ite_eq_right (not_lt.mpr hn)).trans ((ite_eq_left h1).trans (ite_eq_left h2))
  have hgC (n : ℕ) (hn : n ≤ K) (h1 : g₁ n = ⊤) (h2 : ¬ (μ : Label.{u}) ≤ g₂ n) : g n = ν₀ :=
    (ite_eq_right (not_lt.mpr hn)).trans ((ite_eq_left h1).trans (ite_eq_right h2))
  have hgA (n : ℕ) (hn : n ≤ K) (h1 : g₁ n ≠ ⊤) : g n = min (g₁ n) ν₀ :=
    (ite_eq_right (not_lt.mpr hn)).trans (ite_eq_right h1)
  have hσge (x : Label.{u}) (hx : ¬ σ₁ x < β) : (ν : Label.{u}) ≤ σ x := by
    by_cases h2 : (μ : Label.{u}) ≤ σ₂ x
    · rw [hσband x hx h2]
      exact (hcband _ h2).le
    · rw [hσc x hx h2]
  have hgge (n : ℕ) (hn : n ≤ K) (h1 : g₁ n = ⊤) : (ν₀ : Label.{u}) ≤ g n := by
    by_cases h2 : (μ : Label.{u}) ≤ g₂ n
    · rw [hgB n hn h1 h2]
      exact (hc₀c.trans (hcband _ h2)).le
    · rw [hgC n hn h1 h2]
  have hw : IsWitness g σ := by
    refine ⟨fun n n' hnn' ↦ ?_, fun n ↦ ?_, ?_, fun x y hxy ↦ ?_, fun x k hx i hi ↦ ?_⟩
    · -- the suppressor is antitone
      by_cases hn' : K < n'
      · rw [hgK n' hn']
        exact bot_le
      have hn'K : n' ≤ K := not_lt.mp hn'
      have hn : n ≤ K := hnn'.trans hn'K
      by_cases h1' : g₁ n' = ⊤
      · have h1 : g₁ n = ⊤ := top_le_iff.mp (h1' ▸ hw₁.antitone hnn')
        by_cases h2' : (μ : Label.{u}) ≤ g₂ n'
        · rw [hgB n' hn'K h1' h2', hgB n hn h1 (h2'.trans (hw₂.antitone hnn'))]
          exact monotone_bandMap β μ K (hw₂.antitone hnn')
        · rw [hgC n' hn'K h1' h2']
          exact hgge n hn h1
      · have hle : g n' ≤ ν₀ := by
          rw [hgA n' hn'K h1']
          exact min_le_right _ _
        by_cases h1 : g₁ n = ⊤
        · exact hle.trans (hgge n hn h1)
        · rw [hgA n' hn'K h1', hgA n hn h1]
          exact min_le_min_right _ (hw₁.antitone hnn')
    · -- every value of the suppressor is self-visible at its grade
      by_cases hn : K < n
      · rw [hgK n hn]
        exact isSelfVisible_bot n
      have hnK : n ≤ K := not_lt.mp hn
      by_cases h1 : g₁ n = ⊤
      · by_cases h2 : (μ : Label.{u}) ≤ g₂ n
        · rw [hgB n hnK h1 h2]
          exact isSelfVisible_bandMap hβ' hμ hnK h2 (hw₂.isSelfVisible n)
        · rw [hgC n hnK h1 h2]
          exact hc₀K.mono hnK
      · rw [hgA n hnK h1]
        exact (hw₁.isSelfVisible n).min (hc₀K.mono hnK)
    · -- the shifter fixes bottom
      rw [hσlow ⊥ (by rw [hw₁.map_bot]; exact WithBot.bot_lt_coe _), hw₁.map_bot]
      exact min_eq_left bot_le
    · -- the shifter is monotone
      by_cases hy : σ₁ y < β
      · have hx : σ₁ x < β := (hw₁.monotone hxy).trans_lt hy
        rw [hσlow x hx, hσlow y hy]
        exact min_le_min_right _ (hw₁.monotone hxy)
      by_cases hx : σ₁ x < β
      · exact (hσlow x hx ▸ min_le_right _ _).trans (hσge y hy)
      by_cases h2x : (μ : Label.{u}) ≤ σ₂ x
      · have h2y : (μ : Label.{u}) ≤ σ₂ y := h2x.trans (hw₂.monotone hxy)
        rw [hσband x hx h2x, hσband y hy h2y]
        exact monotone_bandMap β μ K (hw₂.monotone hxy)
      · rw [hσc x hx h2x]
        exact hσge y hy
    · -- the shifter commutes with visibility replacement under the guard
      rcases lt_or_ge K k with hk | hk
      · -- above `K` the suppressor is bottom, so `σ x = ⊥`, hence `σ₁ x = ⊥`
        rw [hgK k hk, le_bot_iff] at hx
        have hx1 : σ₁ x < β := by
          by_contra h
          exact (WithBot.bot_lt_coe _).ne' (le_bot_iff.mp (hx ▸ hσge x h))
        rw [hσlow x hx1] at hx
        have hx1' : σ₁ x = ⊥ :=
          (min_eq_bot.mp hx).resolve_right (WithBot.bot_lt_coe _).ne'
        have hc := hw₁.visibilityReplace_comm x k (hx1' ▸ bot_le) i hi
        rw [hx1', visibilityReplace_bot] at hc
        rw [hσlow _ (hc ▸ WithBot.bot_lt_coe _), hc, hσlow x hx1, hx1', min_eq_left bot_le,
          visibilityReplace_bot]
      have hsub (y : Label.{u}) (hy : σ₁ y < β) (hyg : σ₁ y ≤ g₁ k) :
          σ (visibilityReplace k i y) = visibilityReplace k i (σ y) := by
        have hc := hw₁.visibilityReplace_comm y k hyg i hi
        have hlt : σ₁ (visibilityReplace k i y) < β := by
          rw [hc, visibilityReplace_lt_iff hβ']
          exact hy
        rw [hσlow _ hlt, hσlow y hy, hc]
        exact (visibilityReplace_min_of_isSelfVisible hi (hνK.mono hk) _).symm
      by_cases hx1 : σ₁ x < β
      · refine hsub x hx1 ?_
        by_cases hg1 : g₁ k = ⊤
        · rw [hg1]
          exact le_top
        rw [hgA k hk hg1, hσlow x hx1] at hx
        have hxc : σ₁ x < ν := by
          by_contra h
          rw [min_eq_right (not_lt.mp h)] at hx
          exact (hx.trans (min_le_right _ _)).not_gt hc₀c
        rw [min_eq_left hxc.le] at hx
        exact hx.trans (min_le_left _ _)
      -- here `σ₁ x ≥ β`, so the guard forces `g₁ k = ⊤` and `μ ≤ g₂ k`
      have hcx : (ν : Label.{u}) ≤ σ x := hσge x hx1
      have hg1 : g₁ k = ⊤ := by
        by_contra hg1
        rw [hgA k hk hg1] at hx
        exact (hcx.trans (hx.trans (min_le_right _ _))).not_gt hc₀c
      have hg2 : (μ : Label.{u}) ≤ g₂ k := by
        by_contra hg2
        rw [hgC k hk hg1 hg2] at hx
        exact (hcx.trans hx).not_gt hc₀c
      rw [hgB k hk hg1 hg2] at hx
      have hc1 := hw₁.visibilityReplace_comm x k (hg1 ▸ le_top) i hi
      have hx1' : ¬ σ₁ (visibilityReplace k i x) < β := by
        rw [hc1, visibilityReplace_lt_iff hβ']
        exact hx1
      by_cases hx2 : (μ : Label.{u}) ≤ σ₂ x
      · rw [hσband x hx1 hx2] at hx ⊢
        rcases le_or_gt (σ₂ x) (g₂ k) with h22 | h22
        · have hc2 := hw₂.visibilityReplace_comm x k h22 i hi
          have hx2' : (μ : Label.{u}) ≤ σ₂ (visibilityReplace k i x) := by
            rw [hc2]
            exact not_lt.mp fun h ↦ not_lt.mpr hx2 ((visibilityReplace_lt_iff hμ).mp h)
          rw [hσband _ hx1' hx2', hc2]
          exact bandMap_visibilityReplace hβ' hμ hk hi hx2
        · have h22' := hw₂.lt_apply_visibilityReplace h22 hi
          by_cases hK : ((μ + K : Ordinal.{u}) : Label.{u}) ≤ g₂ k
          · rw [hσband _ hx1' (hg2.trans h22'.le), bandMap_of_le (hK.trans h22'.le),
              bandMap_of_le (hK.trans h22.le), (isSelfVisible_coe_add hβ' hk).visibilityReplace_eq]
          · exact absurd hx (not_le.mpr (bandMap_lt_bandMap hg2 (not_le.mp hK) h22))
      · have h22 : σ₂ x ≤ g₂ k := (not_le.mp hx2).le.trans hg2
        have hc2 := hw₂.visibilityReplace_comm x k h22 i hi
        have hx2' : ¬ (μ : Label.{u}) ≤ σ₂ (visibilityReplace k i x) := by
          rw [hc2, not_le, visibilityReplace_lt_iff hμ]
          exact not_le.mp hx2
        rw [hσc _ hx1' hx2', hσc x hx1 hx2]
        exact ((hνK.mono hk).visibilityReplace_eq i).symm
  refine ⟨g, σ, hw, fun d ↦ ?_⟩
  have hdK := hgr d
  rcases hq d with hqd | hqd
  · -- a cell where `q` is below `β`
    have hqc₀ : q d ≤ ν₀ := hbd d hqd
    rw [hlow d hqd]
    rw [heq₁ d] at hqd hqc₀ ⊢
    by_cases hb : g₁ (grade d) = ⊤
    · rw [hb, min_top_right] at hqd hqc₀ ⊢
      rw [hσlow _ hqd, min_eq_left (hqc₀.trans hc₀c.le)]
      exact (min_eq_left (hqc₀.trans (hgge _ hdK hb))).symm
    rw [hgA _ hdK hb]
    by_cases ha : σ₁ (e d) < β
    · rw [hσlow _ ha, min_min_min_comm, min_eq_right hc₀c.le]
      exact (min_eq_left hqc₀).symm
    · have hmin : min (σ₁ (e d)) (g₁ (grade d)) = g₁ (grade d) :=
        min_eq_right (not_lt.mp fun h ↦ ha (lt_of_eq_of_lt (min_eq_left h.le).symm hqd))
      rw [hmin] at hqc₀ ⊢
      rw [min_eq_left hqc₀]
      exact (min_eq_right (hqc₀.trans (hc₀c.le.trans (hσge _ ha)))).symm
  · -- a cell where `q` is the formal top
    have hμr := hr d hqd
    rw [htop d hqd, heq₂ d]
    rw [heq₂ d] at hμr
    rw [heq₁ d] at hqd
    obtain ⟨ha, hb⟩ := min_eq_top.mp hqd
    have hμa : (μ : Label.{u}) ≤ σ₂ (e d) := hμr.trans (min_le_left _ _)
    have hμb : (μ : Label.{u}) ≤ g₂ (grade d) := hμr.trans (min_le_right _ _)
    rw [hσband _ (by rw [ha]; exact not_top_lt) hμa, hgB _ hdK hb hμb]
    exact (monotone_bandMap β μ K).map_min

end Splice

end VaughtConjecture.Label

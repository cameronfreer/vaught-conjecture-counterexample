/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStep
import VaughtConjecture.Continuation.GrowthCappedDecoder

/-!
# The tie case of the LOW step through a top cell of the donor

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW step from the
private coatom at the tie); semantic contract, items 3, 4 and 8.

At the tie of donor raising no witness image of a capped lift raises a donor top: a witness fixing
the donor maximum fixes its replacement.  The donor is read instead through the row of a cell `Z`
labelled `⊤` of graded index `(univ, K)`, the **template** `V = row_Z`: it reads every top above
the replacements of its readings of the proper cells (`StageType.visibilityReplace_rowAt_lt_of_top`,
the donor-side source gap), so a threshold `θ_b`, the largest such replacement, separates the tops
from the proper cells in `V`.

**The raise map** (`Label.raiseMap`, `Label.isWitness_raiseMap`, compiled in this repository).
For a map `θ` fixing `⊥`, monotone, commuting with visibility replacement at every threshold
`k ≤ K` with no guard and keeping its bottom under every replacement, a threshold `θ_b` and a cap
`c`, both self-visible at `K`, the map `ρ` equal to `θ` at and below `θ_b`, to `max (θ v) c` above,
and `⊥` where `θ` is `⊥`, is a witness bounded by `K`.

**The raise through the template** (`StageType.exists_raised_of_dominated`, compiled in this
repository).  Let `W₁` be a section of the donor lawful at `K` (bottom above `K`) dominated at `Z`:
every cell of grade at most `K` is read by `W₁` at most at `Z`, and `W₁ Z ≠ ⊥`.  With `θ` the
capped decoder of `W₁` at `Z` (`Scheme.exists_cappedDecoder`, from the locality of `W₁` at `Z`:
`θ (row_Z d) = min (W₁ d) (W₁ Z)`, exact by domination), the section `ρ ∘ V`, spliced with `⊥`
above `K`, is lawful at `K` (transport with `W₁` as lawful companion of the same bottom pattern,
`CellScheme.Rows.IsLawfulBelow.map_of_bot_iff`), equals `W₁` at every proper cell and every cell
`W₁` reads as `⊥`, and reads every other top `d` as `max (W₁ d) c`.

**The tie case from donor domination** (`StageType.lowStepTie_of_donorDomination`, compiled in this
repository).  If every capped lift of the donor from the root, literal on the root and agreeing
with the ambient donor face capped at the cap, can be chosen dominated at a top cell of graded index
`(univ, K)` (`StageType.DonorDomination`), the tie case `StageType.LowStepTie` holds: the raise
through the template keeps the root (proper root cells are kept, root tops are at least the
frontier already), keeps the capped agreement (the raised tops are at least the cap), and puts every
donor top off the root, at the tie or determined by the root included, at least at the frontier.
So the open part of the tie case is donor domination, the donor-side counterpart of the domination
by the owner on the private side.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

variable {K : ℕ}

open Classical in
/-- The **raise map**: `⊥` where `θ` is `⊥`, `θ` at and below the threshold `θb`, and `max (θ v) c`
above it. -/
noncomputable def raiseMap (θ : Label.{u} → Label.{u}) (θb c : Label.{u}) (v : Label.{u}) :
    Label.{u} :=
  if θ v = ⊥ then ⊥ else if v ≤ θb then θ v else max (θ v) c

variable {θ : Label.{u} → Label.{u}} {θb c : Label.{u}}

theorem raiseMap_of_bot {v : Label.{u}} (h : θ v = ⊥) : raiseMap θ θb c v = ⊥ := by
  simp [raiseMap, h]

theorem raiseMap_of_le {v : Label.{u}} (h0 : θ v ≠ ⊥) (h : v ≤ θb) : raiseMap θ θb c v = θ v := by
  simp [raiseMap, h0, h]

theorem raiseMap_of_lt {v : Label.{u}} (h0 : θ v ≠ ⊥) (h : θb < v) :
    raiseMap θ θb c v = max (θ v) c := by
  simp [raiseMap, h0, not_le.mpr h]

theorem le_raiseMap (v : Label.{u}) : θ v ≤ raiseMap θ θb c v := by
  by_cases h0 : θ v = ⊥
  · rw [h0]; exact bot_le
  by_cases h : v ≤ θb
  · rw [raiseMap_of_le h0 h]
  · rw [raiseMap_of_lt h0 (not_le.mp h)]; exact le_max_left _ _

theorem raiseMap_eq_bot_iff {v : Label.{u}} : raiseMap θ θb c v = ⊥ ↔ θ v = ⊥ :=
  ⟨fun h ↦ le_bot_iff.mp (h ▸ le_raiseMap v), raiseMap_of_bot⟩

/-- **The raise map is a witness bounded by `K`.** -/
theorem isWitness_raiseMap (hθm : Monotone θ) (hθ0 : θ ⊥ = ⊥)
    (hθc : ∀ k ≤ K, ∀ i ≤ k, ∀ x, θ (visibilityReplace k i x) = visibilityReplace k i (θ x))
    (hθb0 : ∀ x, θ x = ⊥ → ∀ k i, i ≤ k → θ (visibilityReplace k i x) = ⊥)
    (hb : IsSelfVisible K θb) (hc : IsSelfVisible K c) :
    IsWitness (stepSuppressor K) (raiseMap θ θb c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := raiseMap_of_bot hθ0
  monotone x y hxy := by
    by_cases hx0 : θ x = ⊥
    · rw [raiseMap_of_bot hx0]; exact bot_le
    have hy0 : θ y ≠ ⊥ := fun h ↦ hx0 (le_bot_iff.mp (h ▸ hθm hxy))
    by_cases hy : y ≤ θb
    · rw [raiseMap_of_le hx0 (hxy.trans hy), raiseMap_of_le hy0 hy]; exact hθm hxy
    · rw [raiseMap_of_lt hy0 (not_le.mp hy)]
      by_cases hx : x ≤ θb
      · rw [raiseMap_of_le hx0 hx]; exact (hθm hxy).trans (le_max_left _ _)
      · rw [raiseMap_of_lt hx0 (not_le.mp hx)]; exact max_le_max (hθm hxy) le_rfl
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · by_cases hx0 : θ x = ⊥
      · rw [raiseMap_of_bot hx0, raiseMap_of_bot (hθb0 x hx0 k i hi), visibilityReplace_bot]
      have hR0 : θ (visibilityReplace k i x) ≠ ⊥ := by
        rw [hθc k hk i hi x, Ne, visibilityReplace_eq_bot_iff]; exact hx0
      by_cases hxb : x ≤ θb
      · have hRb : visibilityReplace k i x ≤ θb :=
          (monotone_visibilityReplace hi hxb).trans_eq ((hb.mono hk).visibilityReplace_eq i)
        rw [raiseMap_of_le hR0 hRb, raiseMap_of_le hx0 hxb, hθc k hk i hi x]
      · have hlt := not_le.mp hxb
        rw [raiseMap_of_lt hR0 (lt_visibilityReplace_of_lt hi (hb.mono hk) hlt),
          raiseMap_of_lt hx0 hlt, hθc k hk i hi x,
          (monotone_visibilityReplace hi).map_max, (hc.mono hk).visibilityReplace_eq i]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, raiseMap_eq_bot_iff] at hx
      rw [raiseMap_of_bot (hθb0 x hx k i hi), raiseMap_of_bot hx, visibilityReplace_bot]

end VaughtConjecture.Label

/-! ### The raise through the template -/

namespace VaughtConjecture.StageType

open Finset Label H2

variable {α : Ordinal.{u}} {n K : ℕ}

/-- **The raise through the template.**  In a legal stage type `tb` on `n` points, let `Z` be a
cell labelled `⊤` of graded index `(univ, K)`, `0 < K ≤ n`, `W₁` lawful at `K` and dominated at
`Z` (`W₁ d ≤ W₁ Z` at every cell of grade at most `K`, `W₁ Z ≠ ⊥`), and `c` self-visible at `K`.
Some `W` lawful at `K` equals `W₁` at every proper cell and every cell `W₁` reads as `⊥`, and
reads every other top `d` of grade at most `K` as `max (W₁ d) c`: the raise map of the capped
decoder of `W₁` at `Z` above the largest replaced reading of a proper cell, applied to the row of
`Z`. -/
theorem exists_raised_of_dominated {tb : StageType.{u} α n} (htb : tb.IsLegal) (hK0 : 0 < K)
    (hKn : K ≤ n) {Z : Fin tb.card} (hZ : tb.label Z = ⊤)
    (hZi : tb.toCellScheme.gradedIndex Z = (univ, K)) {W₁ : Fin tb.card → Label.{u}}
    (hW₁ : LawfulAt tb K W₁) (hdom : ∀ d, tb.toCellScheme.grade d ≤ K → W₁ d ≤ W₁ Z)
    (hZ0 : W₁ Z ≠ ⊥) {c : Label.{u}} (hc : IsSelfVisible K c) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧
      (∀ d, tb.toCellScheme.grade d ≤ K → tb.label d ≠ ⊤ → W d = W₁ d) ∧
      (∀ d, tb.toCellScheme.grade d ≤ K → W₁ d = ⊥ → W d = ⊥) ∧
      ∀ d, tb.toCellScheme.grade d ≤ K → tb.label d = ⊤ → W₁ d ≠ ⊥ → W d = max (W₁ d) c := by
  classical
  obtain ⟨W', hW', hW'W⟩ := exists_ext_bot_at htb hK0 hKn hW₁
  have hgZ : tb.toCellScheme.grade Z = K := congrArg Prod.snd hZi
  obtain ⟨θ, hθm, hθ0, -, hθc, hθb0, hθrow⟩ := Scheme.exists_cappedDecoder (S := tb.toScheme) hW' hgZ
  have hbelow (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      d ∈ tb.toCellScheme.below (tb.toCellScheme.gradedIndex Z) := by
    rw [hZi]; exact ⟨subset_univ _, hd⟩
  have hθV (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      θ (tb.rowAt Z d) = W₁ d := by
    rw [hθrow d (hbelow d hd), hW'W d hd, hW'W Z hgZ.le]
    exact min_eq_left (hdom d hd)
  -- the threshold separating the tops from the proper cells in the template
  set Lo := univ.filter fun y ↦ tb.label y ≠ ⊤ ∧ tb.toCellScheme.grade y ≤ K with hLo
  set θb := Lo.sup fun y ↦ visibilityReplace K K (tb.rowAt Z y) with hθb_def
  have hθb : IsSelfVisible K θb := by
    refine Finset.sup_induction (p := IsSelfVisible K) (isSelfVisible_bot K) ?_ ?_
    · intro a ha b hb
      rcases max_choice a b with h1 | h1
      · change IsSelfVisible K (max a b); rw [h1]; exact ha
      · change IsSelfVisible K (max a b); rw [h1]; exact hb
    · intro y _
      exact visibilityReplace_self_visibilityReplace le_rfl _
  have hprop (y : Fin tb.card) (hy : tb.toCellScheme.grade y ≤ K) (hyt : tb.label y ≠ ⊤) :
      tb.rowAt Z y ≤ θb :=
    (le_visibilityReplace (by omega) _).trans
      (Finset.le_sup (f := fun y ↦ visibilityReplace K K (tb.rowAt Z y))
        (mem_filter.mpr ⟨mem_univ _, hyt, hy⟩))
  have htop (x : Fin tb.card) (hx : tb.toCellScheme.grade x ≤ K) (hxt : tb.label x = ⊤)
      (hx0 : tb.rowAt Z x ≠ ⊥) : θb < tb.rowAt Z x := by
    refine (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr hx0)).mpr fun y hy ↦ ?_
    obtain ⟨-, hyt, hyK⟩ := mem_filter.mp hy
    have := visibilityReplace_rowAt_lt_of_top hZ (hbelow x hx) (hbelow y hyK) hxt hyt
    rwa [hgZ] at this
  have hρ : IsWitness (stepSuppressor K) (raiseMap θ θb c) :=
    isWitness_raiseMap hθm hθ0 hθc hθb0 hθb hc
  have hlawρ : tb.rows.IsLawfulBelow ((univ : Finset (Fin n)), K)
      (raiseMap θ θb c ∘ fun e ↦ tb.rowAt Z e.1) :=
    (Scheme.isLawfulBelow_rowAt htb.isConsistent hZi).map_of_bot_iff hW₁.1 (fun d ↦ d.2.2) hρ
      fun d ↦ by
        change raiseMap θ θb c (tb.rowAt Z d.1) = ⊥ ↔ W₁ d.1 = ⊥
        rw [raiseMap_eq_bot_iff, hθV d.1 d.2.2]
  set W : Fin tb.card → Label.{u} :=
    tb.toCellScheme.splice K (fun _ ↦ ⊥) fun d ↦ raiseMap θ θb c (tb.rowAt Z d) with hW
  have hWle (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) : W d = raiseMap θ θb c (tb.rowAt Z d) :=
    CellScheme.splice_of_le hd
  refine ⟨W, ⟨(CellScheme.Rows.isLawfulBelow_congr (R := tb.rows)
      (X := ((univ : Finset (Fin n)), K)) (w := fun d ↦ raiseMap θ θb c (tb.rowAt Z d))
      (w' := W) fun d hd ↦ (hWle d (show tb.toCellScheme.grade d ≤ K from hd.2)).symm).mp hlawρ,
      fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩,
    fun d hd hdt ↦ ?_, fun d hd h0 ↦ ?_, fun d hd hdt h0 ↦ ?_⟩
  · rw [hWle d hd]
    by_cases h0 : θ (tb.rowAt Z d) = ⊥
    · rw [raiseMap_of_bot h0, ← hθV d hd, h0]
    · rw [raiseMap_of_le h0 (hprop d hd hdt), hθV d hd]
  · rw [hWle d hd]
    exact raiseMap_of_bot (by rw [hθV d hd]; exact h0)
  · rw [hWle d hd]
    have hθ0' : θ (tb.rowAt Z d) ≠ ⊥ := by rw [hθV d hd]; exact h0
    have hV0 : tb.rowAt Z d ≠ ⊥ := fun h ↦ hθ0' (by rw [h, hθ0])
    rw [raiseMap_of_lt hθ0' (htop d hd hdt hV0), hθV d hd]

end VaughtConjecture.StageType

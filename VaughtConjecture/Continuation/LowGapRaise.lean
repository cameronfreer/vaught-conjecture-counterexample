/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplay
import VaughtConjecture.Continuation.H2GeneralRaise
import VaughtConjecture.Extension.CappedDecoder

/-!
# The raise of the donor tops below a gap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the donor face of the LOW
step from the private coatom); semantic contract, items 3, 4 and 8.

The donor face asked by the LOW step from the private coatom (literal on the root, agreeing with
the ambient donor face capped at the cap, reading every donor top off the root at least at the
prescribed private frontier) is built at every LOW family, with no tie premise.  A LOW family
bounds the top grade of the donor by the grade `K` (`StageType.IsLowFamily.topGrade_donor`); that
bound is used here.

**The donor-side source gap** (`StageType.visibilityReplace_rowAt_lt_of_top`).  The row of a cell
`Z` labelled `⊤` reads every top below `Z` above the replacements, at the grade of `Z`, of its
readings of the proper cells below `Z`.  A top of grade `j` gives a top cell of graded index
`(univ, j)` (`StageType.exists_top_cell_univ`, by completeness and availability).

**The raise map** (`Label.raiseMap`, `Label.isWitness_raiseMap`).  For a map `θ` fixing `⊥`,
monotone, commuting with visibility replacement at every threshold `k ≤ K` unconditionally and
keeping its bottom under every replacement, a threshold `θ_b` and a cap `c`, both self-visible at
`K`, the map `ρ` equal to `θ` at and below `θ_b`, to `max (θ v) c` above, and `⊥` where `θ` is
`⊥`, is a witness bounded by `K`.

**The raise through a top cell** (`StageType.exists_raised_at_top`).  For `W₁` lawful at `K` with
`W₁ Z ≠ ⊥` at a top cell `Z` of graded index `(univ, K)`, the raise map of the capped decoder of
`W₁` at `Z`, above the largest replaced reading of a proper cell, applied to the row of `Z`, reads
every proper cell `d` as `min (W₁ d) (W₁ Z)` and every other top `d` as
`max (min (W₁ d) (W₁ Z)) c`.

**Raising below a gap** (`H2.lawfulAt_raise_below`).  Let `R` be lawful at `K`, `j ≤ K`, and `h`
a label with every cell of grade in `(j, K]` read by `R` below `h`.  A labelling `W` lawful at
`j`, equal to `R` at the cells of grade at most `j` that `R` reads below `h`, and at least `h` at
those `R` reads at least at `h`, spliced with `R` above `j`, is lawful at `K`.

**The raise of the tops** (`StageType.exists_raised_tops`).  In a legal stage type of top grade at
most `K`, let `R` be lawful at `K` with a gap at a positive label `h`: every top read at least at
`h`, every proper cell of grade at most `K` below `h`.  For every `c` self-visible at `K`, some `W`
lawful at `K` equals `R` at every proper cell and reads every top at least at `c`: without tops
`W = R`; otherwise, with `j` the largest grade of a top, `R` truncated above `j` is raised through a
top cell of graded index `(univ, j)` and spliced with `R` above `j`.

**The donor face at every LOW family** (`StageType.IsLowFamily.exists_raised_of_gap`).  The
ambient donor face `R` has the gap at the cap `h` (the root tops are at least `h` through the
private face, which reads them at least at the frontier `c > h`).  Its raise at `c` agrees with
`R` capped at `h` and with the private face on the root capped at `c`, and the capped lift at `c`
from the root of the private face with this ambient (bountifulness of the donor) is literal on the
root, agrees with `R` capped at `h` at every donor cell, and reads every donor top off the root at
least at `c`.  The tie premise of `StageType.LowStepTie`, the self-visibility of the cap and a top
cell of graded index `(univ, K)` are not used; `StageType.IsLowFamily.exists_raised` (in
`VaughtConjecture.Continuation.LowStep`) and `StageType.lowStepTie_of_top` (in
`VaughtConjecture.Continuation.LowStepTie`) are this theorem.

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

/-! ### The donor-side source gap and a top cell of full scope -/

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The source gap at a top cell**: in a stage type `t`, the row of a cell `Z` labelled `⊤`
reads every cell `x` below `Z` labelled `⊤` strictly above the replacement, at the grade of `Z`,
of its reading of every cell `y` below `Z` with a proper label.  The labels below `Z` are the
images of the row of `Z` under the witness of the locality of the labels at `Z`, which commutes
with the replacement; a proper label has a proper replacement.  At a top cell of the donor of
graded index `(univ, K)` this is the source gap through which a raising of the donor tops at the
tie can read them apart from the proper donor cells. -/
theorem visibilityReplace_rowAt_lt_of_top {t : StageType.{u} α n} {Z : Fin t.card}
    (hZ : t.label Z = ⊤) {x y : Fin t.card}
    (hx : x ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z))
    (hy : y ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z)) (hxt : t.label x = ⊤)
    (hyt : t.label y ≠ ⊤) :
    visibilityReplace (t.toCellScheme.grade Z) (t.toCellScheme.grade Z) (t.rowAt Z y) <
      t.rowAt Z x := by
  obtain ⟨g, σ, hσ, heq⟩ := t.isLawful.locality Z
  have hread (d : Fin t.card) (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z)) :
      min (t.label d) (t.label Z) = min (σ (t.rowAt Z d)) (g (t.toCellScheme.grade d)) := by
    rw [Scheme.rowAt_of_mem hd]
    exact heq ⟨d, hd⟩
  have hgZ : g (t.toCellScheme.grade Z) = ⊤ := by
    have h := (hread Z (t.toCellScheme.mem_below_gradedIndex Z)).symm
    rw [hZ, min_self] at h
    exact (_root_.min_eq_top.mp h).2
  have hlab (d : Fin t.card) (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex Z)) :
      t.label d = σ (t.rowAt Z d) := by
    have h := hread d hd
    have hgd : g (t.toCellScheme.grade d) = ⊤ :=
      top_le_iff.mp (hgZ ▸ hσ.antitone (show t.toCellScheme.grade d ≤ t.toCellScheme.grade Z
        from hd.2))
    rwa [hZ, min_top_right, hgd, min_top_right] at h
  refine lt_of_not_ge fun hle ↦ hyt ?_
  have h1 : σ (t.rowAt Z x) ≤ σ (visibilityReplace (t.toCellScheme.grade Z)
      (t.toCellScheme.grade Z) (t.rowAt Z y)) := hσ.monotone hle
  rw [← hlab x hx, hxt, hσ.visibilityReplace_comm _ _ (by rw [hgZ]; exact le_top) _ le_rfl,
    ← hlab y hy, top_le_iff, visibilityReplace_eq_top_iff] at h1
  exact h1

/-- **A top of grade `K` gives a top cell of graded index `(univ, K)`**, in a legal stage type:
completeness gives a cell of that graded index, and availability of the labels one labelled `⊤`. -/
theorem exists_top_cell_univ {t : StageType.{u} α n} (ht : t.IsLegal) {x : Fin t.card}
    (hx : t.label x = ⊤) :
    ∃ Z, t.label Z = ⊤ ∧ t.toCellScheme.gradedIndex Z = (univ, t.toCellScheme.grade x) := by
  have hg : t.toCellScheme.grade x ≤ #(univ : Finset (Fin n)) := by
    rw [card_univ, Fintype.card_fin]
    exact t.grade_le x
  obtain ⟨u₀, hu₀⟩ := (isLegal_iff.mp ht).2.2 (univ, t.toCellScheme.grade x)
    ⟨t.univ_mem_faces, t.isWellFormed.isWellFormed.grade_pos x, hg⟩
  have hsc : t.toCellScheme.scope x ⊆ t.toCellScheme.scope u₀ := by
    rw [show t.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
    exact subset_univ _
  obtain ⟨Z, hZ, hxZ⟩ := t.isLawful.availability x u₀ hsc (congrArg Prod.snd hu₀).symm
  rw [hx, top_le_iff] at hxZ
  exact ⟨Z, hxZ, hZ.trans hu₀⟩

end VaughtConjecture.StageType

/-! ### The raise through a top cell -/

namespace VaughtConjecture.StageType

open Finset Label H2

variable {α : Ordinal.{u}} {n K : ℕ}

/-- **The raise through the template, capped at the top cell.**  As
`StageType.exists_raised_of_dominated`, without domination but with `W₁ Z ≠ ⊥`: the raised face
reads every proper cell `d` as `min (W₁ d) (W₁ Z)`, every cell `W₁` reads as `⊥` as `⊥`, and every
other top `d` as `max (min (W₁ d) (W₁ Z)) c`. -/
theorem exists_raised_at_top {tb : StageType.{u} α n} (htb : tb.IsLegal) (hK0 : 0 < K)
    (hKn : K ≤ n) {Z : Fin tb.card} (hZ : tb.label Z = ⊤)
    (hZi : tb.toCellScheme.gradedIndex Z = (univ, K)) {W₁ : Fin tb.card → Label.{u}}
    (hW₁ : LawfulAt tb K W₁) (hZ0 : W₁ Z ≠ ⊥) {c : Label.{u}} (hc : IsSelfVisible K c) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧
      (∀ d, tb.toCellScheme.grade d ≤ K → tb.label d ≠ ⊤ → W d = min (W₁ d) (W₁ Z)) ∧
      (∀ d, tb.toCellScheme.grade d ≤ K → W₁ d = ⊥ → W d = ⊥) ∧
      ∀ d, tb.toCellScheme.grade d ≤ K → tb.label d = ⊤ → W₁ d ≠ ⊥ →
        W d = max (min (W₁ d) (W₁ Z)) c := by
  classical
  obtain ⟨W', hW', hW'W⟩ := exists_ext_bot_at htb hK0 hKn hW₁
  have hgZ : tb.toCellScheme.grade Z = K := congrArg Prod.snd hZi
  obtain ⟨θ, hθm, hθ0, -, hθc, hθb0, hθrow⟩ :=
    Scheme.exists_cappedDecoder (S := tb.toScheme) hW' hgZ
  have hbelow (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      d ∈ tb.toCellScheme.below (tb.toCellScheme.gradedIndex Z) := by
    rw [hZi]; exact ⟨subset_univ _, hd⟩
  have hθV (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      θ (tb.rowAt Z d) = min (W₁ d) (W₁ Z) := by
    rw [hθrow d (hbelow d hd), hW'W d hd, hW'W Z hgZ.le]
  have hθV0 (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      θ (tb.rowAt Z d) = ⊥ ↔ W₁ d = ⊥ := by
    rw [hθV d hd, min_eq_bot]
    exact ⟨fun h ↦ h.resolve_right hZ0, .inl⟩
  set Lo := univ.filter fun y ↦ tb.label y ≠ ⊤ ∧ tb.toCellScheme.grade y ≤ K with hLo
  set θb := Lo.sup fun y ↦ visibilityReplace K K (tb.rowAt Z y) with hθb_def
  have hθb : IsSelfVisible K θb := by
    refine Finset.sup_induction (p := IsSelfVisible K) (isSelfVisible_bot K) ?_ ?_
    · intro a ha b hb
      rcases max_choice a b with h1 | h1
      · rw [h1]; exact ha
      · rw [h1]; exact hb
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
        rw [raiseMap_eq_bot_iff, hθV0 d.1 d.2.2]
  set W : Fin tb.card → Label.{u} :=
    tb.toCellScheme.splice K (fun _ ↦ ⊥) fun d ↦ raiseMap θ θb c (tb.rowAt Z d) with hW
  have hWle (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ K) :
      W d = raiseMap θ θb c (tb.rowAt Z d) :=
    CellScheme.splice_of_le hd
  refine ⟨W, ⟨(CellScheme.Rows.isLawfulBelow_congr (R := tb.rows)
      (X := ((univ : Finset (Fin n)), K)) (w := fun d ↦ raiseMap θ θb c (tb.rowAt Z d))
      (w' := W) fun d hd ↦
        (hWle d (show tb.toCellScheme.grade d ≤ K from hd.2)).symm).mp hlawρ,
      fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩,
    fun d hd hdt ↦ ?_, fun d hd h0 ↦ ?_, fun d hd hdt h0 ↦ ?_⟩
  · rw [hWle d hd]
    by_cases h0 : θ (tb.rowAt Z d) = ⊥
    · rw [raiseMap_of_bot h0, ← hθV d hd, h0]
    · rw [raiseMap_of_le h0 (hprop d hd hdt), hθV d hd]
  · rw [hWle d hd]
    exact raiseMap_of_bot ((hθV0 d hd).mpr h0)
  · rw [hWle d hd]
    have hθ0' : θ (tb.rowAt Z d) ≠ ⊥ := fun h ↦ h0 ((hθV0 d hd).mp h)
    have hV0 : tb.rowAt Z d ≠ ⊥ := fun h ↦ hθ0' (by rw [h, hθ0])
    rw [raiseMap_of_lt hθ0' (htop d hd hdt hV0), hθV d hd]

end VaughtConjecture.StageType

/-! ### Raising below a gap, and the donor face at every LOW family -/

namespace VaughtConjecture.H2

open Finset Label StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **Raising below a gap.**  Let `R` be lawful at `K`, `j ≤ K`, and `h` a label such that `R`
reads every cell of grade in `(j, K]` below `h` (`hmid`).  If `W` is lawful at `j`, equals `R` at
every cell of grade at most `j` read by `R` below `h` (`hlo`), and is at least `h` at every cell of
grade at most `j` read by `R` at least at `h` (`hhi`), then `V`, equal to `W` at the cells of grade
at most `j` and to `R` at the others, is lawful at `K`.

*Which cells change.*  `V` differs from `R` only at cells of grade at most `j` that `R` reads at
least at `h` (by `hlo`), and there `V` is at least `h` (by `hhi`).  Above `K`, `V = R = ⊥`.

*The three laws* (checked pointwise, `CellScheme.Rows.isLawfulBelow_iff_forall`).  Order: at a cell
of grade at most `j` it is the order law of `W`, at the others that of `R`.  Availability: the
cells compared have equal grades, so both lie at most `j` (availability of `W`, the cell found has
the same grade) or both above (availability of `R`).  Locality at a cell `s`: if the grade of `s`
is at most `j`, so is that of every cell below `s`, and the target `d ↦ min (V d) (V s)` is
`d ↦ min (W d) (W s)` (locality of `W`).  If the grade of `s` is in `(j, K]`, then `V s = R s < h`
by `hmid`, and the target is `d ↦ min (R d) (R s)` (locality of `R`): at a cell `d` with `R d < h`,
`V d = R d`; at a cell `d` with `R d ≥ h`, both `V d` and `R d` are at least `h > R s`, so both
minima are `R s`.  The capping by the label `R s < h` of the reader erases the change.  This is the
only place `hmid` is used. -/
theorem lawfulAt_raise_below {t : StageType.{u} α n} {j K : ℕ} (hjK : j ≤ K) {h : Label.{u}}
    {R W : Fin t.card → Label.{u}} (hR : LawfulAt t K R) (hW : LawfulAt t j W)
    (hmid : ∀ d, j < t.toCellScheme.grade d → t.toCellScheme.grade d ≤ K → R d < h)
    (hlo : ∀ d, t.toCellScheme.grade d ≤ j → R d < h → W d = R d)
    (hhi : ∀ d, t.toCellScheme.grade d ≤ j → h ≤ R d → h ≤ W d) :
    LawfulAt t K fun d ↦ if t.toCellScheme.grade d ≤ j then W d else R d := by
  classical
  obtain ⟨hRo, hRl, hRa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hR.1
  obtain ⟨hWo, hWl, hWa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hW.1
  refine ⟨(CellScheme.Rows.isLawfulBelow_iff_forall
    (w := fun d ↦ if t.toCellScheme.grade d ≤ j then W d else R d)).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s u hu hsu hg ↦ ?_⟩, fun d hd ↦ ?_⟩
  · -- order
    split_ifs with hdj
    · exact hWo d ⟨subset_univ _, hdj⟩
    · exact hRo d hd
  · -- locality
    by_cases hsj : t.toCellScheme.grade s ≤ j
    · have he : (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
          min (if t.toCellScheme.grade d.1 ≤ j then W d.1 else R d.1)
            (if t.toCellScheme.grade s ≤ j then W s else R s)) =
          fun d ↦ min (W d.1) (W s) := by
        funext d
        have hdj : t.toCellScheme.grade d.1 ≤ j := d.2.2.trans hsj
        rw [ite_eq_left hdj, ite_eq_left hsj]
      rw [he]
      exact hWl s ⟨subset_univ _, hsj⟩
    · have hRs : R s < h := hmid s (not_le.mp hsj) hs.2
      have he : (fun d : t.toCellScheme.below (t.toCellScheme.gradedIndex s) ↦
          min (if t.toCellScheme.grade d.1 ≤ j then W d.1 else R d.1)
            (if t.toCellScheme.grade s ≤ j then W s else R s)) =
          fun d ↦ min (R d.1) (R s) := by
        funext d
        rw [ite_eq_right hsj]
        split_ifs with hdj
        · rcases lt_or_ge (R d.1) h with hd | hd
          · rw [hlo d.1 hdj hd]
          · rw [min_eq_right (hRs.le.trans (hhi d.1 hdj hd)), min_eq_right (hRs.le.trans hd)]
        · rfl
      rw [he]
      exact hRl s hs
  · -- availability
    have hgu (v : Fin t.card) (hv : t.toCellScheme.gradedIndex v = t.toCellScheme.gradedIndex u) :
        t.toCellScheme.grade v = t.toCellScheme.grade u := congrArg Prod.snd hv
    by_cases huj : t.toCellScheme.grade u ≤ j
    · obtain ⟨v, hv, hle⟩ := hWa s u ⟨subset_univ _, huj⟩ hsu hg
      refine ⟨v, hv, ?_⟩
      rw [ite_eq_left (hg ▸ huj), ite_eq_left ((hgu v hv).trans_le huj)]
      exact hle
    · obtain ⟨v, hv, hle⟩ := hRa s u hu hsu hg
      refine ⟨v, hv, ?_⟩
      rw [ite_eq_right (hg ▸ huj), ite_eq_right (by rw [hgu v hv]; exact huj)]
      exact hle
  · -- above `K`
    exact (ite_eq_right fun (h' : t.toCellScheme.grade d ≤ j) ↦ hd (h'.trans hjK)).trans
      (hR.2 d hd)

end VaughtConjecture.H2

namespace VaughtConjecture.StageType

open Finset Label H2

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The raise of the tops.**  In a legal stage type `tb` on `n` points of top grade at most
`K ≤ n` (`htg`), let `R` be lawful at `K` with a gap at a positive label `h`: every cell labelled
`⊤` read at least at `h` (`htop`), every other cell of grade at most `K` below `h` (`hlow`).  For
every `c` self-visible at `K`, some `W` lawful at `K` equals `R` at every cell not labelled `⊤`
and reads every cell labelled `⊤` at least at `c`.

*Construction.*  Without tops, `W = R`.  Otherwise `j` is the largest grade of a top (so every top
has grade at most `j`, and `j ≤ K` by `htg`), `Z` a cell labelled `⊤` of graded index `(univ, j)`
(`StageType.exists_top_cell_univ`).  `W'` is the raise of `R` truncated above `j` through the row
of `Z` at the grade `j` (`StageType.exists_raised_at_top`, with `c` self-visible at `j ≤ K`): it
reads a proper cell `d` of grade at most `j` as `min (R d) (R Z)`, which is `R d` since
`R d < h ≤ R Z` (`hlow` and `htop` at `Z`), and every top `d` as `max (min (R d) (R Z)) c ≥ c`
(`R d ≠ ⊥` by `htop` and `⊥ < h`).  Then `W` is `W'` at the cells of grade at most `j` and `R`
above (`H2.lawfulAt_raise_below`).

*Which cells change.*  Only the tops, all of grade at most `j`: every proper cell keeps `R`.

*Hypotheses of the splice.*  `hmid`: a cell of grade in `(j, K]` is not a top (maximality of `j`),
so `R` reads it below `h` by `hlow`.  `hlo`: a cell of grade at most `j` read below `h` is not a
top (`htop`), so it keeps `R`.  `hhi`: a cell of grade at most `j` read at least at `h` is a top
(`hlow`), read by `W'` at least at `min (R d) (R Z) ≥ h`.

Capped agreement with `R` at `h` and literalness on a root are not claimed here; they are
established in `StageType.IsLowFamily.lowStepTie`. -/
theorem exists_raised_tops {tb : StageType.{u} α n} (htb : tb.IsLegal) {K : ℕ} (hKn : K ≤ n)
    (htg : tb.topGrade ≤ K) {R : Fin tb.card → Label.{u}} (hR : LawfulAt tb K R)
    {h c : Label.{u}} (hb : ⊥ < h) (hc : IsSelfVisible K c)
    (htop : ∀ d, tb.label d = ⊤ → h ≤ R d)
    (hlow : ∀ d, tb.label d ≠ ⊤ → tb.toCellScheme.grade d ≤ K → R d < h) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧ (∀ d, tb.label d ≠ ⊤ → W d = R d) ∧
      ∀ d, tb.label d = ⊤ → c ≤ W d := by
  classical
  by_cases hT : (univ.filter fun x : Fin tb.card ↦ tb.label x = ⊤).Nonempty
  swap
  · refine ⟨R, hR, fun _ _ ↦ rfl, fun d hd ↦ absurd ⟨d, mem_filter.mpr ⟨mem_univ _, hd⟩⟩ hT⟩
  obtain ⟨x, hxT, hxmax⟩ := Finset.exists_max_image _ tb.toCellScheme.grade hT
  have hx : tb.label x = ⊤ := (mem_filter.mp hxT).2
  set j := tb.toCellScheme.grade x with hj
  have hmax (y : Fin tb.card) (hy : tb.label y = ⊤) : tb.toCellScheme.grade y ≤ j :=
    hxmax y (mem_filter.mpr ⟨mem_univ _, hy⟩)
  have hj0 : 0 < j := tb.isWellFormed.isWellFormed.grade_pos x
  have hjK : j ≤ K := topGrade_le_iff.mp htg x hx
  obtain ⟨Z, hZ, hZi⟩ := exists_top_cell_univ htb hx
  have hgZ : tb.toCellScheme.grade Z = j := congrArg Prod.snd hZi
  set W₁ : Fin tb.card → Label.{u} := fun d ↦ if tb.toCellScheme.grade d ≤ j then R d else ⊥
    with hW₁_def
  have hW₁ : LawfulAt tb j W₁ := lawfulAt_trunc hR.1 hjK
  have hW₁le (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) : W₁ d = R d :=
    ite_eq_left hd
  have hRZ : h ≤ R Z := htop Z hZ
  have hZ0 : W₁ Z ≠ ⊥ := by rw [hW₁le Z hgZ.le]; exact ne_bot_of_gt (hb.trans_le hRZ)
  obtain ⟨W', hW', hW'p, -, hW't⟩ :=
    exists_raised_at_top htb hj0 (hjK.trans hKn) hZ hZi hW₁ hZ0 (hc.mono hjK)
  -- the raise keeps every proper cell of grade at most `j`
  have hp' (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) (hdt : tb.label d ≠ ⊤) :
      W' d = R d := by
    rw [hW'p d hd hdt, hW₁le d hd, hW₁le Z hgZ.le]
    exact min_eq_left ((hlow d hdt (hd.trans hjK)).le.trans hRZ)
  -- and reads every top at least at `c`
  have ht' (d : Fin tb.card) (hdt : tb.label d = ⊤) : c ≤ W' d := by
    have hd := hmax d hdt
    have h0 : W₁ d ≠ ⊥ := by rw [hW₁le d hd]; exact ne_bot_of_gt (hb.trans_le (htop d hdt))
    rw [hW't d hd hdt h0]
    exact le_max_right _ _
  have hmid (d : Fin tb.card) (hjd : j < tb.toCellScheme.grade d)
      (hdK : tb.toCellScheme.grade d ≤ K) : R d < h :=
    hlow d (fun hdt ↦ absurd (hmax d hdt) (not_le.mpr hjd)) hdK
  have hlo (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) (hRd : R d < h) : W' d = R d :=
    hp' d hd fun hdt ↦ absurd (htop d hdt) (not_le.mpr hRd)
  have hhi (d : Fin tb.card) (hd : tb.toCellScheme.grade d ≤ j) (hRd : h ≤ R d) : h ≤ W' d := by
    by_cases hdt : tb.label d = ⊤
    · rw [hW't d hd hdt (by rw [hW₁le d hd]; exact ne_bot_of_gt (hb.trans_le hRd)),
        hW₁le d hd, hW₁le Z hgZ.le]
      exact (le_min hRd hRZ).trans (le_max_left _ _)
    · exact absurd (hlow d hdt (hd.trans hjK)) (not_lt.mpr hRd)
  refine ⟨_, lawfulAt_raise_below hjK hR hW' hmid hlo hhi, fun d hdt ↦ ?_, fun d hdt ↦ ?_⟩
  · split_ifs with hd
    · exact hp' d hd hdt
    · rfl
  · rw [ite_eq_left (hmax d hdt)]
    exact ht' d hdt

variable {k K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The donor face from the private coatom, at every LOW family, with no tie premise.**  For a
private face `f` and a donor face `R`, lawful at `K`, agreeing on the root capped at a label
`⊥ < h` below the frontier `c` of `f`, with every donor top off the root read by `R` at least at
`h` and every proper donor cell of grade at most `K` read below `h`, some donor face lawful at `K`,
literal on the root and agreeing with `R` capped at `h`, reads every donor top off the root at least
at `c`.  This is the conclusion of `StageType.IsLowFamily.exists_raised` without its premises
`StageType.LowStepTie` and `IsSelfVisible K h`, and the conclusion of `StageType.LowStepTie`
without its premise that the cap is the replaced low maximum of `R` or that some donor top off the
root is determined by the root, nor its self-visibility of the cap: none of these is used (the
frontier `c`, not the cap, is the label the capped lift needs self-visible).

*The gap.*  Every top `d` of the donor has `h ≤ R d`: off the root by `htop`, on the root because
the private face reads its copy at least at the frontier `c > h` (strict source gaps,
`H2.frontier_le_lawfulAt`) and agrees there with `R` capped at `h`.  Every proper cell of grade at
most `K` has `R d < h` (`hlow`).  So `StageType.exists_raised_tops`
gives `W'` lawful at `K`, equal to `R` at every proper cell, at least `c` at every top.

*Capped agreement at `h`* (`W'` with `R`): at proper cells `W' = R`; at tops both are at least `h`
(`W' ≥ c > h`).

*Agreement on the root capped at `c`* (`W'` with the private face `f`): at a root top both are at
least `c`; at a proper root cell of grade at most `K`, `R < h` and `f` agrees with `R` capped at
`h`, so `f = R = W'`; above `K` both are `⊥`.

*Literal root.*  The capped lift at `c` from the root of `f` with the ambient `W'`
(`H2.hasCappedLifts_lawfulAt'`, bountifulness of the donor) gives `W` lawful at `K`, equal to `f`
at every root cell, and agreeing with `W'` capped at `c`.  The root cells that `W'` moved are the
root tops (to at least `c`), and `W` puts them back to `f` exactly; no other root cell moved.
From the capped agreement at `c`: `W` agrees with `R` capped at `h` (since `h < c`), and reads
every top off the root at least at `c`. -/
theorem IsLowFamily.exists_raised_of_gap (hF : IsLowFamily K t' tb p o r) {h c : Label.{u}}
    (hb : ⊥ < h) (hhc : h < c) {R : Fin tb.card → Label.{u}}
    {f : Fin t'.card → Label.{u}} (hR : LawfulAt tb K R) (hf : LawfulAt t' K f)
    (hag : ∀ x, min (f (faceCell hF.face_private x)) h = min (R (faceCell hF.face_donor x)) h)
    (hlow : ∀ x, tb.label x ≠ ⊤ → tb.toCellScheme.grade x ≤ K → R x < h)
    (hc : c = min (f o) (visibilityReplace K K (f r)))
    (htop : ∀ t, tb.label t = ⊤ → tb.toCellScheme.grade t ≤ K →
      t ∉ tb.toScheme.visibleCells Fin.castSuccEmb → h ≤ R t) :
    ∃ W : Fin tb.card → Label.{u}, LawfulAt tb K W ∧
      (∀ x, W (faceCell hF.face_donor x) = f (faceCell hF.face_private x)) ∧
      (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t, tb.label t = ⊤ → tb.toCellScheme.grade t ≤ K →
        t ∉ tb.toScheme.visibleCells Fin.castSuccEmb → c ≤ W t := by
  classical
  have hs := hF.isSourceGapContextAt
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  have hfo := frontier_le_lawfulAt hF.isLegal_private hs hf
  have hcv : IsSelfVisible K c := by
    rw [hc]
    rcases min_choice (f o) (visibilityReplace K K (f r)) with h1 | h1 <;> rw [h1]
    · exact hfo.1
    · exact visibilityReplace_self_visibilityReplace le_rfl _
  -- the root tops of `f` are at least `c`
  have hroot_top (x : Fin p.card) (hx : tb.label (faceCell hF.face_donor x) = ⊤) :
      c ≤ f (faceCell hF.face_private x) := by
    rw [hc]
    refine hfo.2 _ ?_ (last_notMem_scope_faceCell hF.face_private x)
    rw [label_faceCell, ← label_faceCell hF.face_donor x]
    exact hx
  -- every top of `R` is at least `h`
  have hRh (d : Fin tb.card) (hd : tb.label d = ⊤) : h ≤ R d := by
    by_cases hv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨x, rfl⟩ := exists_faceCell_eq hF.face_donor hv
      have h1 := hag x
      have h2 : h ≤ f (faceCell hF.face_private x) := hhc.le.trans (hroot_top x hd)
      rw [min_eq_right h2] at h1
      exact min_eq_right_iff.mp h1.symm
    · exact htop d hd (hF.grade_le hd) hv
  obtain ⟨W', hW', hW'p, hW't⟩ :=
    exists_raised_tops hF.isLegal_donor hKk hF.topGrade_donor hR hb hcv hRh hlow
  -- `W'` agrees with `R` capped at `h`
  have hW'R (d : Fin tb.card) : min (W' d) h = min (R d) h := by
    by_cases hdt : tb.label d = ⊤
    · rw [min_eq_right (hhc.le.trans (hW't d hdt)), min_eq_right (hRh d hdt)]
    · rw [hW'p d hdt]
  -- the root of `f` agrees with `W'` capped at `c`
  have hagc (x : Fin p.card) :
      min (f (faceCell hF.face_private x)) c = min (W' (faceCell hF.face_donor x)) c := by
    set d := faceCell hF.face_donor x
    have hgd : tb.toCellScheme.grade d = t'.toCellScheme.grade (faceCell hF.face_private x) := by
      rw [grade_faceCell, grade_faceCell]
    by_cases hdt : tb.label d = ⊤
    · rw [min_eq_right (hroot_top x hdt), min_eq_right (hW't d hdt)]
    · rw [hW'p d hdt]
      by_cases hdK : tb.toCellScheme.grade d ≤ K
      · have hRd := hlow d hdt hdK
        have hfx : f (faceCell hF.face_private x) = R d := eq_of_min_eq_of_lt (hag x).symm hRd
        rw [hfx]
      · rw [hR.2 d hdK, hf.2 _ (hgd ▸ hdK)]
  obtain ⟨W, hW, hWr, hWc⟩ := hasCappedLifts_lawfulAt' hK0 hKk hF.isLegal_private
    hF.face_private hF.isLegal_donor hF.face_donor hcv hW' hf hagc
  refine ⟨W, hW, hWr, fun d ↦ ?_, fun d hd _ _ ↦ ?_⟩
  · calc min (W d) h = min (min (W d) c) h := by rw [min_assoc, min_eq_right hhc.le]
      _ = min (min (W' d) c) h := by rw [hWc d]
      _ = min (W' d) h := by rw [min_assoc, min_eq_right hhc.le]
      _ = min (R d) h := hW'R d
  · have h2 := hWc d
    rw [min_eq_right (hW't d hd)] at h2
    exact min_eq_right_iff.mp h2

end VaughtConjecture.StageType

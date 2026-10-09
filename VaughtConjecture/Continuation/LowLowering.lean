/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapContext
import VaughtConjecture.Extension.AlignedEncoding
import VaughtConjecture.Extension.SectionTheorem

/-!
# Lowering the lost top below a cap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the private
installation); semantic contract, items 4 and 8.

In a LOW lift the private side must be chosen so that the frontier `min (v o) (R_K (v r))` of the
private section `v` is at most the cap `c`: the owner `o` cannot be lowered (availability keeps it
at least the root tops of its grade), so the **lost top** `r` is lowered to the cap.  The strict
source gaps of the context make this possible: the owner's row reads `r` at or below the
threshold `θ = R_K (row_o r)`, and the owner and every top avoiding the lost point strictly above
it.

**The lowering map** (`Label.lowerMap θ c`): `⊥` at `⊥`, the cap `c` on `(⊥, θ]`, `⊤` above `θ`.
For `θ` and `c` self-visible at `K` and `c ≠ ⊥` it is a witness bounded by grade `K` that sends
only `⊥` to `⊥` (`Label.isWitness_lowerMap`): visibility replacement at a threshold `k ≤ K` keeps
`(⊥, θ]` and its complement (`Label.lt_visibilityReplace_of_lt`, in
`VaughtConjecture.Extension.AlignedEncoding`).  So the lowering map of a
lawful row is lawful (`CellScheme.Rows.IsLawful.map_of_bot_reflecting`).

**The lowering** (`StageType.IsSourceGapContextAt.exists_lowering`, compiled in this repository).
Let `t'` be a legal source-gap context of grade `K` with owner `o` and lost top `r`, `u` lawful
below `(univ, K)`, `c` self-visible at `K` with `⊥ < c ≤ u o`, and `u` **dominated by the owner
where the owner reads high** (`u d ≤ u o` at the cells of grade at most `K` that the owner reads
above `θ`).  Then `v = min u (lowerMap θ c ∘ row_o)` is lawful
below `(univ, K)`, agrees with `u` capped at `c`, reads the lost top at most `c`, and equals `u`
at every cell the owner reads above `θ` (the owner and every top of `t'` avoiding the lost point,
by the strict source gaps) and at every cell where `u` is at most `c`.  Locality of `v` is the
minimum of two localities (`Label.TransformsTo.inf`); availability passes through the owner's
row: capped at `u o`, `u` is a witness image of that row, and below the threshold the lowered
section is at most `c ≤ u o`, while above it domination applies.

**The private installation** (`StageType.IsSourceGapContextAt.exists_installation`, compiled in
this repository).  With the root prescribed by `u` (the root cells of `t'` avoid the lost point),
the lowering keeps the root literally when every root cell that is not a top of `t'` is
prescribed at most `c`: in the LOW construction these are proper donor fields, below the donor
maximum and so below the cap.  The remaining condition is on the lift: a section lawful below
`(univ, K)`, equal to the root prescription and agreeing with the given private section capped at
`c`, at most its owner's label at every cell the owner reads above `R_K (row_o r)`.  A capped lift
of the prescription (bountifulness of `t'`) gives the first two.  Capping the lift at its owner
gives the domination and keeps the root when no root cell is prescribed above the owner's label
(`StageType.IsSourceGapContextAt.exists_installation_of_le_owner`); the root tops are read above
the threshold (`gap_retained`), so a root top prescribed above the owner's label is the remaining
case, open here.

**After donor raising** (`Label.le_or_eq_of_raise`, `Label.max_le_of_raise`,
`Label.le_of_raise_of_lt`): a designated donor top at least the cap `h` that donor raising with the
gap leaves at least the frontier `c` or at most `R_K M` (`M` the donor maximum) is at least `c`
unless `h = R_K M` (the tie, at the cutoff cut of the donor), where it is exactly `h`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace Label

variable {k i K : ℕ} {θ c x : Label.{u}}

/-- The **lowering map**: `⊥` at `⊥`, `c` on `(⊥, θ]`, and `⊤` above `θ`. -/
noncomputable def lowerMap (θ c : Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else if x ≤ θ then c else ⊤

theorem lowerMap_bot : lowerMap θ c ⊥ = ⊥ := by simp [lowerMap]

theorem lowerMap_of_le (hx : x ≠ ⊥) (h : x ≤ θ) : lowerMap θ c x = c := by
  simp [lowerMap, hx, h]

theorem lowerMap_of_lt (h : θ < x) : lowerMap θ c x = ⊤ := by
  simp [lowerMap, ne_bot_of_gt h, not_le.mpr h]

theorem lowerMap_le (h : x ≤ θ) : lowerMap θ c x ≤ c := by
  by_cases hx : x = ⊥
  · rw [hx, lowerMap_bot]; exact bot_le
  · rw [lowerMap_of_le hx h]

theorem lowerMap_eq_bot_iff (hc : ⊥ < c) : lowerMap θ c x = ⊥ ↔ x = ⊥ := by
  constructor
  · intro h
    by_contra hx
    by_cases hxθ : x ≤ θ
    · rw [lowerMap_of_le hx hxθ] at h; exact hc.ne' h
    · rw [lowerMap_of_lt (not_le.mp hxθ)] at h; exact top_ne_bot h
  · rintro rfl; exact lowerMap_bot

theorem monotone_lowerMap : Monotone (lowerMap θ c) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, lowerMap_bot]; exact bot_le
  have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
  by_cases hyθ : y ≤ θ
  · rw [lowerMap_of_le hx (hxy.trans hyθ), lowerMap_of_le hy hyθ]
  · rw [lowerMap_of_lt (not_le.mp hyθ)]; exact le_top

/-- **The lowering map is a witness bounded by grade `K`.** -/
theorem isWitness_lowerMap (hθ : IsSelfVisible K θ) (hcv : IsSelfVisible K c) (hc : ⊥ < c) :
    IsWitness (stepSuppressor.{u} K) (lowerMap θ c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := lowerMap_bot
  monotone := monotone_lowerMap
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · have hθk := hθ.mono hk
      by_cases hx0 : x = ⊥
      · rw [hx0, visibilityReplace_bot, lowerMap_bot, visibilityReplace_bot]
      have hv0 : visibilityReplace k i x ≠ ⊥ := fun h ↦ hx0 (visibilityReplace_eq_bot_iff.mp h)
      by_cases hxθ : x ≤ θ
      · have hvθ : visibilityReplace k i x ≤ θ :=
          (monotone_visibilityReplace hi hxθ).trans_eq (hθk.visibilityReplace_eq i)
        rw [lowerMap_of_le hv0 hvθ, lowerMap_of_le hx0 hxθ, (hcv.mono hk).visibilityReplace_eq]
      · have hlt := not_le.mp hxθ
        rw [lowerMap_of_lt (lt_visibilityReplace_of_lt hi hθk hlt), lowerMap_of_lt hlt,
          visibilityReplace_top]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, lowerMap_eq_bot_iff hc] at hx
      rw [hx, visibilityReplace_bot, lowerMap_bot, visibilityReplace_bot]

/-- **A raised donor top above the cap**: if a donor top `W` is at least the cap `h` (self-visible
at `K`, above the donor maximum `M`), and donor raising with the gap leaves it at least `c` or at
most `R_K M`, then it is at least `c` or exactly `h`.  So the LOW clause at cutoff `h` and frontier
`c` holds at it exactly when `c ≤ W` or `c ≤ h`. -/
theorem le_or_eq_of_raise {M h c W : Label.{u}} (hh : IsSelfVisible K h) (hM : M < h)
    (hW : h ≤ W) (hraise : c ≤ W ∨ W ≤ visibilityReplace K K M) : c ≤ W ∨ W = h := by
  rcases hraise with h1 | h1
  · exact .inl h1
  · exact .inr (le_antisymm (h1.trans (visibilityReplace_le_of_le le_rfl hh hM.le)) hW)

/-- **The LOW clause after raising**: under `Label.le_or_eq_of_raise`, `max h c ≤ W` whenever
`c ≤ h` or the raise lands at `c`. -/
theorem max_le_of_raise {M h c W : Label.{u}} (hh : IsSelfVisible K h) (hM : M < h)
    (hW : h ≤ W) (hraise : c ≤ W ∨ W ≤ visibilityReplace K K M) (hc : c ≤ h ∨ c ≤ W) :
    max h c ≤ W := by
  rcases le_or_eq_of_raise hh hM hW hraise with h1 | h1
  · exact max_le hW h1
  · rcases hc with h2 | h2
    · exact max_le hW (h2.trans hW)
    · exact max_le hW h2

/-- **No tie, no cap outcome**: if the replacement at `K` of the donor maximum `M` is strictly
below the cap `h`, a donor top at least `h` that donor raising with the gap leaves at least `c` or
at most `R_K M` is at least `c`.  So the second outcome of donor raising occurs only at the tie
`h = R_K M`, the cutoff cut of the donor (`Label.le_or_eq_of_raise`). -/
theorem le_of_raise_of_lt {M h c W : Label.{u}} (hlt : visibilityReplace K K M < h)
    (hW : h ≤ W) (hraise : c ≤ W ∨ W ≤ visibilityReplace K K M) : c ≤ W :=
  hraise.resolve_right fun h1 ↦ (h1.trans_lt hlt).not_ge hW

end Label

namespace StageType

open Label

variable {α : Ordinal.{u}} {n k K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
  {l : Fin k} {o r : Fin t'.card}

/-- The row of the owner, read at every cell, is lawful below `(univ, K)` in a legal source-gap
context of grade `K`: consistency at the owner, whose graded index is `(univ, K)`. -/
theorem IsSourceGapContextAt.isLawfulBelow_rowAt (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) :
    t'.rows.IsLawfulBelow (univ, K) fun d ↦ t'.rowAt o d := by
  have hgi : t'.toCellScheme.gradedIndex o = (univ, K) :=
    Prod.ext hs.scope_owner hs.grade_owner
  have h' : t'.rows.IsLawfulBelow (t'.toCellScheme.gradedIndex o) fun d ↦ t'.rowAt o d := by
    convert ht'.isConsistent o using 1
    funext d
    rw [Scheme.rowAt_of_mem d.2]
  rw [hgi] at h'
  exact h'

/-- **The lowering below a cap** in a legal source-gap context of grade `K`: a section `u`
lawful below `(univ, K)`, a cap `c` self-visible at `K` with `⊥ < c ≤ u o`, and the serving
premise (`hserve`: for cells `s`, `t` of equal grades at most `K` with the scope of `s` inside that
of `t`, if the owner reads `s` above `R_K (row_o r)` and `u` reads `s` above `u o`, some cell `w`
of the graded index of `t` with `u s ≤ u w` is read by the owner above `R_K (row_o r)`), give a
section
`v` lawful below `(univ, K)` agreeing with `u` capped at `c`, reading the lost top at most `c`,
and equal to `u` at every cell the owner reads above `R_K (row_o r)` and at every cell where `u`
is at most `c`.  Domination by the owner where the owner reads high gives the serving premise
(`IsSourceGapContextAt.serve_of_dom`, `IsSourceGapContextAt.exists_lowering`). -/
theorem IsSourceGapContextAt.exists_lowering' (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    {c : Label.{u}} (hcv : IsSelfVisible K c) (hc : ⊥ < c) (hco : c ≤ u o)
    (hserve : ∀ s t, t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t →
      t'.toCellScheme.grade s = t'.toCellScheme.grade t → t'.toCellScheme.grade t ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o s → u o < u s →
      ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
        visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧ v r ≤ c ∧
      ∀ d, t'.toCellScheme.grade d ≤ K →
        (visibilityReplace K K (t'.rowAt o r) < t'.rowAt o d ∨ u d ≤ c) → v d = u d := by
  set θ := visibilityReplace K K (t'.rowAt o r) with hθdef
  have hθ : IsSelfVisible K θ := visibilityReplace_self_visibilityReplace le_rfl _
  set E : Fin t'.card → Label.{u} := fun d ↦ t'.rowAt o d with hE
  have hEl := hs.isLawfulBelow_rowAt ht'
  set lam : Fin t'.card → Label.{u} := fun d ↦ lowerMap θ c (E d) with hlam
  -- the lowered row is lawful below `(univ, K)`
  have hlaml : t'.rows.IsLawfulBelow (univ, K) fun d ↦ lam d :=
    hEl.map_of_bot_reflecting (K := K) (fun d ↦ d.2.2) (isWitness_lowerMap hθ hcv hc)
      fun _ ↦ (lowerMap_eq_bot_iff hc).mp
  -- `u` is a witness image of the owner's row, by domination
  have hgi : t'.toCellScheme.gradedIndex o = (univ, K) :=
    Prod.ext hs.scope_owner hs.grade_owner
  have hob : o ∈ t'.toCellScheme.below (univ, K) := hgi.le
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hu
  obtain ⟨g, σ, hσ, heq⟩ := hloc o hob
  have hmem (d : Fin t'.card) (hd : d ∈ t'.toCellScheme.below (univ, K)) :
      d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) := by rw [hgi]; exact hd
  -- capped at its owner, `u` is a witness image of the owner's row
  have hgK : u o ≤ g K := by
    have := heq ⟨o, hmem o hob⟩
    simp only [min_self] at this
    rw [this, show t'.toCellScheme.grade o = K from hs.grade_owner]
    exact min_le_right _ _
  have hrep (d : Fin t'.card) (hd : d ∈ t'.toCellScheme.below (univ, K)) :
      min (u d) (u o) = min (σ (E d)) (u o) := by
    have h1 := heq ⟨d, hmem d hd⟩
    simp only at h1
    have hgd : u o ≤ g (t'.toCellScheme.grade d) := hgK.trans (hσ.antitone hd.2)
    have h2 := congrArg (fun x ↦ min x (u o)) h1
    simp only [min_assoc, min_self] at h2
    rw [h2, min_eq_right hgd]
    simp only [hE]
    rw [Scheme.rowAt_of_mem (hmem d hd)]
  have hU : ⊥ < u o := hc.trans_le hco
  set v : Fin t'.card → Label.{u} := fun d ↦ min (u d) (lam d) with hv
  have hbel (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) :
      d ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, hd⟩
  have hbot (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) (hE0 : E d = ⊥) :
      u d = ⊥ ∧ lam d = ⊥ := by
    refine ⟨?_, by simp only [hlam, hE0, lowerMap_bot]⟩
    have h1 := hrep d (hbel d hd)
    rw [hE0, hσ.map_bot, min_bot_left] at h1
    rcases min_eq_bot.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hU.ne'
  have hlc (d : Fin t'.card) (hE0 : E d ≠ ⊥) : c ≤ lam d := by
    by_cases hEθ : E d ≤ θ
    · simp only [hlam]; rw [lowerMap_of_le hE0 hEθ]
    · simp only [hlam]; rw [lowerMap_of_lt (not_le.mp hEθ)]; exact le_top
  refine ⟨v, ?_, fun d hdK ↦ ?_, ?_, fun d hdK hd ↦ ?_⟩
  · -- lawfulness: orderly and locality by minima, availability through the owner's row
    obtain ⟨huo, hul, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hu
    obtain ⟨hlo, hll, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hlaml
    obtain ⟨-, -, hEa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hEl
    obtain ⟨-, -, hua⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hu
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ (huo d hd).min (hlo d hd),
      fun s hs' ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · convert (hul s hs').inf (hll s hs') using 1
      funext d
      simp only [Pi.inf_apply, hv]
      exact min_min_min_comm _ _ _ _
    · have hsb : s ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, hg.trans_le ht.2⟩
      by_cases hcase : E s ≤ θ ∨ u s ≤ u o
      swap
      · -- a cell read above the threshold and above the owner: served by a cell read above the
        -- threshold
        obtain ⟨hEθ, hso⟩ := not_or.mp hcase
        obtain ⟨w, hw, huw, hEw⟩ := hserve s t hst hg ht.2 (not_le.mp hEθ) (not_le.mp hso)
        refine ⟨w, hw, min_le_min huw ?_⟩
        simp only [hlam]
        rw [lowerMap_of_lt hEw]
        exact le_top
      obtain ⟨w, hw, hEw⟩ := hEa s t ht hst hg
      have hwb : w ∈ t'.toCellScheme.below (univ, K) := by
        rw [CellScheme.mem_below, hw]; exact ht
      have hgw : t'.toCellScheme.grade w = t'.toCellScheme.grade s :=
        (congrArg Prod.snd hw).trans hg.symm
      refine ⟨w, hw, le_min ?_ ((min_le_right _ _).trans (monotone_lowerMap hEw))⟩
      have hsU : min (u s) (lam s) ≤ min (u s) (u o) := by
        rcases hcase with hEθ | hso
        · exact min_le_min le_rfl ((lowerMap_le hEθ).trans hco)
        · exact (min_le_left _ _).trans (le_min le_rfl hso)
      refine hsU.trans ?_
      rw [hrep s hsb]
      refine (min_le_min (hσ.monotone hEw) le_rfl).trans ?_
      rw [← hrep w hwb]
      exact min_le_left _ _
  · -- agreement capped at `c`
    simp only [hv]
    by_cases hE0 : E d = ⊥
    · obtain ⟨hu0, hl0⟩ := hbot d hdK hE0
      rw [hu0, hl0, min_bot_left]
    · rw [min_assoc, min_eq_right (hlc d hE0)]
  · -- the lost top is read at most `c`
    exact (min_le_right _ _).trans (lowerMap_le (le_visibilityReplace (by omega) _))
  · -- cells read above `θ`, or with `u` at most `c`, are kept
    simp only [hv]
    rcases hd with hd | hd
    · simp only [hlam, hE]; rw [lowerMap_of_lt hd, min_top_right]
    · by_cases hE0 : E d = ⊥
      · obtain ⟨hu0, hl0⟩ := hbot d hdK hE0
        rw [hu0, hl0, min_self]
      · exact min_eq_left (hd.trans (hlc d hE0))

/-- **Availability above the owner is served above the threshold** when the replaced lost top is
below the owner: in a legal source-gap context of grade `K`, for `u` lawful below `(univ, K)` with
`R_K (u r) < u o`, a cell `s` read by the owner above the threshold `θ = R_K (row_o r)` and by `u`
above the owner has, at every graded index `t` it is available to, a cell read by `u` at least as
`s` and by the owner above `θ`.  The cell serving `s` for `u` will do: the witness `σ` of the
locality of `u` at the owner sends its row value to at least `u o`, while it sends `θ` to
`R_K (u r) < u o`. -/
theorem IsSourceGapContextAt.serve_of_lt (hs : t'.IsSourceGapContextAt K h l o r)
    {u : Fin t'.card → Label.{u}} (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    (hlt : visibilityReplace K K (u r) < u o) :
    ∀ s t, t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t →
      t'.toCellScheme.grade s = t'.toCellScheme.grade t → t'.toCellScheme.grade t ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o s → u o < u s →
      ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
        visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w := by
  intro s t hst hg htK _ hso
  set θ := visibilityReplace K K (t'.rowAt o r) with hθdef
  set E : Fin t'.card → Label.{u} := fun d ↦ t'.rowAt o d with hE
  have hgi : t'.toCellScheme.gradedIndex o = (univ, K) :=
    Prod.ext hs.scope_owner hs.grade_owner
  have hob : o ∈ t'.toCellScheme.below (univ, K) := hgi.le
  obtain ⟨-, hloc, hua⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hu
  obtain ⟨g, σ, hσ, heq⟩ := hloc o hob
  have hmem (d : Fin t'.card) (hd : d ∈ t'.toCellScheme.below (univ, K)) :
      d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) := by rw [hgi]; exact hd
  have hgK : u o ≤ g K := by
    have := heq ⟨o, hmem o hob⟩
    simp only [min_self] at this
    rw [this, show t'.toCellScheme.grade o = K from hs.grade_owner]
    exact min_le_right _ _
  have hrep (d : Fin t'.card) (hd : d ∈ t'.toCellScheme.below (univ, K)) :
      min (u d) (u o) = min (σ (E d)) (u o) := by
    have h1 := heq ⟨d, hmem d hd⟩
    simp only at h1
    have hgd : u o ≤ g (t'.toCellScheme.grade d) := hgK.trans (hσ.antitone hd.2)
    have h2 := congrArg (fun x ↦ min x (u o)) h1
    simp only [min_assoc, min_self] at h2
    rw [h2, min_eq_right hgd]
    simp only [hE]
    rw [Scheme.rowAt_of_mem (hmem d hd)]
  have htb : t ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, htK⟩
  obtain ⟨w, hw, huw⟩ := hua s t htb hst hg
  have hwb : w ∈ t'.toCellScheme.below (univ, K) := by
    rw [CellScheme.mem_below, hw]; exact htb
  have hrb : r ∈ t'.toCellScheme.below (univ, K) :=
    ⟨subset_univ _, hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost⟩
  have hur : u r < u o := (le_visibilityReplace (by omega) _).trans_lt hlt
  refine ⟨w, hw, huw, lt_of_not_ge fun hle ↦ ?_⟩
  have h1 : u o ≤ σ (E w) := by
    have h' := hrep w hwb
    rw [min_eq_right (hso.le.trans huw)] at h'
    rw [h']
    exact min_le_left _ _
  have h2 : σ (E r) = u r := by
    have h' := hrep r hrb
    rw [min_eq_left hur.le] at h'
    rcases le_total (σ (E r)) (u o) with h3 | h3
    · rw [min_eq_left h3] at h'; exact h'.symm
    · rw [min_eq_right h3] at h'; exact absurd h' hur.ne
  have h3 : σ θ = visibilityReplace K K (u r) := by
    rw [hθdef, hσ.visibilityReplace_comm _ K (by rw [h2]; exact hur.le.trans hgK) K le_rfl, h2]
  exact (h1.trans (hσ.monotone hle)).not_gt (h3 ▸ hlt)

/-- **A section dominated by its owner where the owner reads high is served**: no cell read above
the threshold is read above the owner, so the serving hypothesis of
`IsSourceGapContextAt.exists_lowering'` holds vacuously.  So the unserved case
(`StageType.LowStepUnserved`) arises only for lifts not dominated at the owner, the private-side
counterpart of `StageType.DonorDomination`. -/
theorem IsSourceGapContextAt.serve_of_dom {u : Fin t'.card → Label.{u}}
    (hdom : ∀ d, t'.toCellScheme.grade d ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o d → u d ≤ u o) :
    ∀ s t, t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t →
      t'.toCellScheme.grade s = t'.toCellScheme.grade t → t'.toCellScheme.grade t ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o s → u o < u s →
      ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
        visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w :=
  fun s _ _ hg ht hEs hso ↦ absurd (hdom s (hg ▸ ht) hEs) (not_le.mpr hso)

/-- **The lowering below a cap** in a legal source-gap context of grade `K`, for a section `u`
dominated by its owner where the owner reads high (`IsSourceGapContextAt.exists_lowering'`). -/
theorem IsSourceGapContextAt.exists_lowering (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    {c : Label.{u}} (hcv : IsSelfVisible K c) (hc : ⊥ < c) (hco : c ≤ u o)
    (hdom : ∀ d, t'.toCellScheme.grade d ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o d → u d ≤ u o) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧ v r ≤ c ∧
      ∀ d, t'.toCellScheme.grade d ≤ K →
        (visibilityReplace K K (t'.rowAt o r) < t'.rowAt o d ∨ u d ≤ c) → v d = u d :=
  hs.exists_lowering' ht' hu hcv hc hco fun s _ _ hg ht hEs hso ↦
    absurd (hdom s (hg ▸ ht) hEs) (not_le.mpr hso)

/-- **The lowering below a cap without domination**, when the replaced lost top is below the
owner, `R_K (u r) < u o`.  Availability at a cell `s` that the owner reads above the threshold and
that `u` reads above the owner is served by the cell `w` serving it for `u`, which the owner reads
above the threshold too: otherwise the witness of the locality at the owner would send the row at
`w`, at most the threshold, to at least `u o`, while it sends the threshold to `R_K (u r)`. -/
theorem IsSourceGapContextAt.exists_lowering_of_lt (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    {c : Label.{u}} (hcv : IsSelfVisible K c) (hc : ⊥ < c) (hco : c ≤ u o)
    (hlt : visibilityReplace K K (u r) < u o) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧ v r ≤ c ∧
      ∀ d, t'.toCellScheme.grade d ≤ K →
        (visibilityReplace K K (t'.rowAt o r) < t'.rowAt o d ∨ u d ≤ c) → v d = u d :=
  hs.exists_lowering' ht' hu hcv hc hco (hs.serve_of_lt hu hlt)

/-- **The private installation from a lift dominated by the owner where the owner reads high.**
In a legal source-gap context of grade `K` with lost point `l`, owner `o` and lost top `r`, let `u`
be lawful below `(univ, K)`, `c` self-visible at `K` with `⊥ < c ≤ u o`, and `u` at most `u o` at
every cell of grade at most `K` that the owner reads above `R_K (row_o r)`.  If `u` is at
most `c` at every cell of grade at most `K` avoiding `l` that is not a top of `t'` (in the LOW
construction: the proper root cells, proper donor fields below the cap), then some `v` lawful
below `(univ, K)` agrees with `u` capped at `c`, reads the lost top at most `c`, and equals `u`
at the owner and at every cell of grade at most `K` avoiding `l` (the root, kept literally).  The
tops avoiding `l` are read by the owner above the threshold (`gap_retained`), and the owner too
(`gap_owner`). -/
theorem IsSourceGapContextAt.exists_installation (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    {c : Label.{u}} (hcv : IsSelfVisible K c) (hc : ⊥ < c) (hco : c ≤ u o)
    (hdom : ∀ d, t'.toCellScheme.grade d ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o d → u d ≤ u o)
    (hroot : ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → t'.label d ≠ ⊤ →
      u d ≤ c) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧ v r ≤ c ∧ v o = u o ∧
      ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → v d = u d := by
  obtain ⟨v, hv, hcap, hr, hkeep⟩ := hs.exists_lowering ht' hu hcv hc hco hdom
  refine ⟨v, hv, hcap, hr, hkeep o hs.grade_owner.le (.inl hs.gap_owner), fun d hd hl ↦ ?_⟩
  refine hkeep d hd ?_
  by_cases htop : t'.label d = ⊤
  · exact .inl (hs.gap_retained d htop hl)
  · exact .inr (hroot d hd hl htop)

/-- **The private installation from a lift capped at its owner.**  In a legal source-gap context
of grade `K` with lost point `l`, owner `o` and lost top `r`, let `u` be lawful below `(univ, K)`
(for instance a capped lift of the root prescription, by bountifulness), `c` self-visible at `K`
with `⊥ < c ≤ u o`.  If every cell of grade at most `K` avoiding `l` is at most `u o` (the
**residual condition**: no root cell is prescribed above the owner), and every such cell that is
not a top of `t'` is at most `c`, then some `v` lawful below `(univ, K)` agrees with `u` capped at
`c`, reads the lost top at most `c`, and equals `u` at the owner and at every cell of grade at
most `K` avoiding `l`.  The lift is first capped at its owner's label (lawful, dominated by the
owner, unchanged on the root by the residual condition, unchanged at `c` since `c ≤ u o`), then
lowered (`StageType.IsSourceGapContextAt.exists_installation`). -/
theorem IsSourceGapContextAt.exists_installation_of_le_owner (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d) {c : Label.{u}}
    (hcv : IsSelfVisible K c) (hc : ⊥ < c) (hco : c ≤ u o)
    (hres : ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → u d ≤ u o)
    (hroot : ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → t'.label d ≠ ⊤ →
      u d ≤ c) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧ v r ≤ c ∧ v o = u o ∧
      ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → v d = u d := by
  -- the owner's label is self-visible at `K`
  have hgo : t'.toCellScheme.grade o = K := hs.grade_owner
  have hob : o ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, hgo.le⟩
  have hUv : IsSelfVisible K (u o) := by
    have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hu).1 o hob
    rwa [hgo] at this
  -- cap the lift at its owner
  set u₁ : Fin t'.card → Label.{u} := fun d ↦ min (u d) (u o) with hu₁
  have hu₁l : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u₁ d :=
    hu.min_const_of_isSelfVisible (c := u o) hUv
  have hu₁o : u₁ o = u o := min_self _
  obtain ⟨v, hv, hcap, hr, hvo, hroot'⟩ := hs.exists_installation ht' hu₁l hcv hc
    (by rw [hu₁o]; exact hco) (fun d _ _ ↦ by rw [hu₁o]; exact min_le_right _ _)
    (fun d hd hl ht ↦ (min_le_left _ _).trans (hroot d hd hl ht))
  refine ⟨v, hv, fun d hd ↦ ?_, hr, hvo.trans hu₁o, fun d hd hl ↦ ?_⟩
  · rw [hcap d hd, hu₁, min_assoc, min_eq_right hco]
  · rw [hroot' d hd hl, hu₁]
    exact min_eq_left (hres d hd hl)

/-- **The private frontier at most the cap.**  In a legal source-gap context of grade `K` with lost
point `l`, owner `o` and lost top `r`, let `u` be lawful below `(univ, K)` and `h` self-visible at
`K` with `⊥ < h`, every cell of grade at most `K` avoiding `l` that is not a top of `t'` read by `u`
at most `h` (in a LOW lift with an active serving profile: the proper root cells, below the donor
maximum).  Suppose the frontier `min (u o) (R_K (u r))` is already at most `h`, or availability at
the cells read above the threshold and above the owner is served above the threshold (for
instance when `R_K (u r) < u o`, `IsSourceGapContextAt.serve_of_lt`).  Then some `v` lawful below
`(univ, K)` agrees with `u` capped at `h`, equals `u` at every cell of grade at most `K` avoiding
`l` (the root, kept literally), and has frontier at most `h`.  The remaining case is
`h < u o ≤ R_K (u r)` with a cell read above the threshold and above the owner served only by
cells read at most the threshold. -/
theorem IsSourceGapContextAt.exists_frontier_le (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d) {c : Label.{u}}
    (hcv : IsSelfVisible K c) (hc : ⊥ < c)
    (hroot : ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → t'.label d ≠ ⊤ →
      u d ≤ c)
    (hres : min (u o) (visibilityReplace K K (u r)) ≤ c ∨
      ∀ s t, t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t →
        t'.toCellScheme.grade s = t'.toCellScheme.grade t → t'.toCellScheme.grade t ≤ K →
        visibilityReplace K K (t'.rowAt o r) < t'.rowAt o s → u o < u s →
        ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
          visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → v d = u d) ∧
      min (v o) (visibilityReplace K K (v r)) ≤ c := by
  by_cases hfr : min (u o) (visibilityReplace K K (u r)) ≤ c
  · exact ⟨u, hu, fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, hfr⟩
  have hco : c ≤ u o := (not_le.mp hfr).le.trans (min_le_left _ _)
  obtain ⟨v, hv, hcap, hr, hkeep⟩ := hs.exists_lowering' ht' hu hcv hc hco (hres.resolve_left hfr)
  refine ⟨v, hv, hcap, fun d hd hl ↦ hkeep d hd ?_, ?_⟩
  · by_cases htop : t'.label d = ⊤
    · exact .inl (hs.gap_retained d htop hl)
    · exact .inr (hroot d hd hl htop)
  · exact (min_le_right _ _).trans
      ((monotone_visibilityReplace le_rfl hr).trans_eq (hcv.visibilityReplace_eq K))

/-- **Serving is necessary for a lowering**: if `v` is lawful below `(univ, K)`, at most `u`, at
most `c` at every cell the owner reads at most the threshold `θ = R_K (row_o r)`, and keeps a cell
`s` with `c < u s`, then at every graded index `t` that `s` is available to some cell is read by
`u` at least as `s` and by the owner above `θ`.  So the serving hypothesis of
`IsSourceGapContextAt.exists_lowering'` is exact for the lowerings that keep the cells read above
`θ`. -/
theorem IsSourceGapContextAt.serve_of_lowered {u v : Fin t'.card → Label.{u}}
    (hv : t'.rows.IsLawfulBelow (univ, K) fun d ↦ v d) (hvu : ∀ d, v d ≤ u d) {c : Label.{u}}
    (hlow : ∀ d, t'.toCellScheme.grade d ≤ K →
      t'.rowAt o d ≤ visibilityReplace K K (t'.rowAt o r) → v d ≤ c)
    {s t : Fin t'.card} (hst : t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t)
    (hg : t'.toCellScheme.grade s = t'.toCellScheme.grade t) (htK : t'.toCellScheme.grade t ≤ K)
    (hvs : v s = u s) (hcs : c < u s) :
    ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w := by
  obtain ⟨-, -, hva⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hv
  have htb : t ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, htK⟩
  obtain ⟨w, hw, hsw⟩ := hva s t htb hst hg
  have hwK : t'.toCellScheme.grade w ≤ K := by
    rw [show t'.toCellScheme.grade w = t'.toCellScheme.grade t from congrArg Prod.snd hw]
    exact htK
  refine ⟨w, hw, hvs ▸ hsw.trans (hvu w), lt_of_not_ge fun hle ↦ ?_⟩
  exact (hcs.trans_le (hvs ▸ hsw)).not_ge (hlow w hwK hle)

variable (t' K l o r) in
/-- **The unserved case of the private frontier** (proved with the lost point last,
`StageType.lowStepUnserved`, in `VaughtConjecture.Continuation.LowFullGradeUnserved`, and below
the full grade `StageType.lowStepUnserved_of_le`): in a legal source-gap context of grade `K`
with lost point `l`, owner `o` and lost top `r`, every section `u` lawful below `(univ, K)` with the
proper cells avoiding `l` at most a cap `c` (self-visible at `K`, `⊥ < c`), with
`c < u o ≤ R_K (u r)`, and with a cell read by the owner above the threshold and by `u` above the
owner that is served only by cells read at most the threshold, has a section `v` lawful below
`(univ, K)` agreeing with `u` capped at `c`, equal to `u` at the cells of grade at most `K`
avoiding `l`, with frontier at most `c`. -/
def LowStepUnserved : Prop :=
  ∀ u : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ u d) →
    ∀ c : Label.{u}, IsSelfVisible K c → ⊥ < c →
    (∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → t'.label d ≠ ⊤ →
      u d ≤ c) →
    c < u o → u o ≤ visibilityReplace K K (u r) →
    ¬ (∀ s t, t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t →
        t'.toCellScheme.grade s = t'.toCellScheme.grade t → t'.toCellScheme.grade t ≤ K →
        visibilityReplace K K (t'.rowAt o r) < t'.rowAt o s → u o < u s →
        ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
          visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w) →
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → v d = u d) ∧
      min (v o) (visibilityReplace K K (v r)) ≤ c

/-- **The private frontier at most the cap, from the unserved case**: the conclusion of
`IsSourceGapContextAt.exists_frontier_le` for every section, given `LowStepUnserved`: a frontier
above the cap with `R_K (u r) < u o` is served (`IsSourceGapContextAt.serve_of_lt`). -/
theorem IsSourceGapContextAt.exists_frontier_le_of_unserved (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) (hU : LowStepUnserved K t' l o r)
    {u : Fin t'.card → Label.{u}} (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    {c : Label.{u}} (hcv : IsSelfVisible K c) (hc : ⊥ < c)
    (hroot : ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → t'.label d ≠ ⊤ →
      u d ≤ c) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → v d = u d) ∧
      min (v o) (visibilityReplace K K (v r)) ≤ c := by
  by_cases hfr : min (u o) (visibilityReplace K K (u r)) ≤ c
  · exact hs.exists_frontier_le ht' hu hcv hc hroot (.inl hfr)
  by_cases hserve : ∀ s t, t'.toCellScheme.scope s ⊆ t'.toCellScheme.scope t →
      t'.toCellScheme.grade s = t'.toCellScheme.grade t → t'.toCellScheme.grade t ≤ K →
      visibilityReplace K K (t'.rowAt o r) < t'.rowAt o s → u o < u s →
      ∃ w, t'.toCellScheme.gradedIndex w = t'.toCellScheme.gradedIndex t ∧ u s ≤ u w ∧
        visibilityReplace K K (t'.rowAt o r) < t'.rowAt o w
  · exact hs.exists_frontier_le ht' hu hcv hc hroot (.inr hserve)
  have hco : c < u o := (not_le.mp hfr).trans_le (min_le_left _ _)
  have hor : u o ≤ visibilityReplace K K (u r) := not_lt.mp fun hlt ↦ hserve (hs.serve_of_lt hu hlt)
  exact hU u hu c hcv hc hroot hco hor hserve

end StageType

end VaughtConjecture

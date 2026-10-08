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
below `(univ, K)` and **dominated by the owner** (`u d ≤ u o` at the cells of grade at most `K`),
and `c` self-visible at `K` with `⊥ < c`.  Then `v = min u (lowerMap θ c ∘ row_o)` is lawful
below `(univ, K)`, agrees with `u` capped at `c`, reads the lost top at most `c`, and equals `u`
at every cell the owner reads above `θ` (the owner and every top of `t'` avoiding the lost point,
by the strict source gaps) and at every cell where `u` is at most `c`.  Locality of `v` is the
minimum of two localities (`Label.TransformsTo.inf`); availability passes through the owner's
row, of which `u` is a witness image by domination.

**The private installation** (`StageType.IsSourceGapContextAt.exists_installation`, compiled in
this repository).  With the root prescribed by `u` (the root cells of `t'` avoid the lost point),
the lowering keeps the root literally when every root cell that is not a top of `t'` is
prescribed at most `c`: in the LOW construction these are proper donor fields, below the donor
maximum and so below the cap.  The remaining condition is the domination of the lift by the
owner: a section lawful below `(univ, K)`, equal to the root prescription, agreeing with the given
private section capped at `c`, and at most its owner's label at every cell of grade at most `K`.
A capped lift of the prescription (bountifulness of `t'`) gives the first three; the domination
is not proved here.

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
lawful below `(univ, K)` and dominated by the owner, and a cap `c` self-visible at `K` with
`⊥ < c`, give a section `v` lawful below `(univ, K)` agreeing with `u` capped at `c`,
reading the lost top at most `c`, and equal to `u` at every cell the owner reads above
`R_K (row_o r)` and at every cell where `u` is at most `c`. -/
theorem IsSourceGapContextAt.exists_lowering (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    (hdom : ∀ d, t'.toCellScheme.grade d ≤ K → u d ≤ u o) {c : Label.{u}}
    (hcv : IsSelfVisible K c) (hc : ⊥ < c) :
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
  have hrep (d : Fin t'.card) (hd : d ∈ t'.toCellScheme.below (univ, K)) :
      u d = min (σ (E d)) (g (t'.toCellScheme.grade d)) := by
    have := heq ⟨d, hmem d hd⟩
    simp only at this
    rw [min_eq_left (hdom d hd.2)] at this
    rw [this, hE]
    simp only
    rw [Scheme.rowAt_of_mem (hmem d hd)]
  set v : Fin t'.card → Label.{u} := fun d ↦ min (u d) (lam d) with hv
  have hbel (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) :
      d ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, hd⟩
  have hbot (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) (hE0 : E d = ⊥) :
      u d = ⊥ ∧ lam d = ⊥ := by
    refine ⟨?_, by simp only [hlam, hE0, lowerMap_bot]⟩
    rw [hrep d (hbel d hd), hE0, hσ.map_bot, min_bot_left]
  have hlc (d : Fin t'.card) (hE0 : E d ≠ ⊥) : c ≤ lam d := by
    by_cases hEθ : E d ≤ θ
    · simp only [hlam]; rw [lowerMap_of_le hE0 hEθ]
    · simp only [hlam]; rw [lowerMap_of_lt (not_le.mp hEθ)]; exact le_top
  refine ⟨v, ?_, fun d hdK ↦ ?_, ?_, fun d hdK hd ↦ ?_⟩
  · -- lawfulness: orderly and locality by minima, availability through the owner's row
    obtain ⟨huo, hul, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hu
    obtain ⟨hlo, hll, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hlaml
    obtain ⟨-, -, hEa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hEl
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ (huo d hd).min (hlo d hd),
      fun s hs' ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · convert (hul s hs').inf (hll s hs') using 1
      funext d
      simp only [Pi.inf_apply, hv]
      exact min_min_min_comm _ _ _ _
    · obtain ⟨w, hw, hEw⟩ := hEa s t ht hst hg
      have hsb : s ∈ t'.toCellScheme.below (univ, K) := ⟨subset_univ _, hg.trans_le ht.2⟩
      have hwb : w ∈ t'.toCellScheme.below (univ, K) := by
        rw [CellScheme.mem_below, hw]; exact ht
      have hgw : t'.toCellScheme.grade w = t'.toCellScheme.grade s :=
        (congrArg Prod.snd hw).trans hg.symm
      refine ⟨w, hw, min_le_min ?_ ?_⟩
      · rw [hrep s hsb, hrep w hwb, hgw]
        exact min_le_min (hσ.monotone hEw) le_rfl
      · exact monotone_lowerMap hEw
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

/-- **The private installation from a lift dominated by the owner.**  In a legal source-gap
context of grade `K` with lost point `l`, owner `o` and lost top `r`, let `u` be lawful below
`(univ, K)` and dominated by the owner, and `c` self-visible at `K` with `⊥ < c`.  If `u` is at
most `c` at every cell of grade at most `K` avoiding `l` that is not a top of `t'` (in the LOW
construction: the proper root cells, proper donor fields below the cap), then some `v` lawful
below `(univ, K)` agrees with `u` capped at `c`, reads the lost top at most `c`, and equals `u`
at the owner and at every cell of grade at most `K` avoiding `l` (the root, kept literally).  The
tops avoiding `l` are read by the owner above the threshold (`gap_retained`), and the owner too
(`gap_owner`). -/
theorem IsSourceGapContextAt.exists_installation (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) {u : Fin t'.card → Label.{u}}
    (hu : t'.rows.IsLawfulBelow (univ, K) fun d ↦ u d)
    (hdom : ∀ d, t'.toCellScheme.grade d ≤ K → u d ≤ u o) {c : Label.{u}}
    (hcv : IsSelfVisible K c) (hc : ⊥ < c)
    (hroot : ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → t'.label d ≠ ⊤ →
      u d ≤ c) :
    ∃ v : Fin t'.card → Label.{u}, t'.rows.IsLawfulBelow (univ, K) (fun d ↦ v d) ∧
      (∀ d, t'.toCellScheme.grade d ≤ K → min (v d) c = min (u d) c) ∧ v r ≤ c ∧ v o = u o ∧
      ∀ d, t'.toCellScheme.grade d ≤ K → l ∉ t'.toCellScheme.scope d → v d = u d := by
  obtain ⟨v, hv, hcap, hr, hkeep⟩ := hs.exists_lowering ht' hu hdom hcv hc
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
  obtain ⟨v, hv, hcap, hr, hvo, hroot'⟩ := hs.exists_installation ht' hu₁l
    (fun d _ ↦ by rw [hu₁o]; exact min_le_right _ _) hcv hc
    (fun d hd hl ht ↦ (min_le_left _ _).trans (hroot d hd hl ht))
  refine ⟨v, hv, fun d hd ↦ ?_, hr, hvo.trans hu₁o, fun d hd hl ↦ ?_⟩
  · rw [hcap d hd, hu₁, min_assoc, min_eq_right hco]
  · rw [hroot' d hd hl, hu₁]
    exact min_eq_left (hres d hd hl)

end StageType

end VaughtConjecture

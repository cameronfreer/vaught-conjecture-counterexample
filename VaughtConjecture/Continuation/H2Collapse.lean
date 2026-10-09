/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2ArityOne
import VaughtConjecture.Extension.CapTransport

/-!
# h2: donor raising by a band raise (work file)

WORK FILE (branch `research/work-h2`).  Every declaration here is proved.

**The band raise** (`H2.bandRaise B h c`): the label `c` on the band of labels above `B`, at least
`h` and below `c`; the identity elsewhere.  For `B` and `c` self-visible at `K` and either `h ≤ B`
or `h` self-visible at `K + 1`, it is a witness bounded by the grade `K` (`H2.isWitness_bandRaise`).

**Refined donor raising from capped lifts** (`H2.donorRaisingV_of_cappedLift`), at any grade `K`:
from a capped lift `W₁` of the served face with the root of the context face, the band raise with
`B` the replaced low maximum of `W₁` and `c` the frontier cap fixes the root (every root cell is a
low cell or a designated root top, at least `c`), keeps the agreement capped at `h`, and sends
every designated top at least `h` to at least `c` or keeps it at most `B`.  For a cap `h` above
`B` not self-visible at `K + 1`, the band raise above `h` itself leaves only the tops at exactly
`h`; that case is a separate hypothesis (`H2.TieAtCap`).

**Donor raising with the gap, no tie** (`H2.donorRaisingGap_of_cappedLift`): at a state of the
clause every designated top above the replaced low maximum is at least `min c h`
(`H2.DonorRaisingGap`).  If every cell is low, designated, a root cell, or determined by the root
(`H2.IsRootDet`), then at a cap `h = μ + K` and a frontier cap `c > h` no cell of the capped lift
has a label in `[μ, h)`, and the band raise of `[μ, c)` to `c` (a witness: replacement does not
cross `μ`, `H2.coe_le_visibilityReplace_iff`) finishes; at `c ≤ h` the capped lift finishes.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label

/-! ### The band raise -/

/-- Replacement at `k ≤ K` with value `i ≤ k` does not cross a label self-visible at `K` from
above. -/
theorem visibilityReplace_le_iff_of_isSelfVisible {K k i : ℕ} {B : Label.{u}}
    (hB : IsSelfVisible K B) (hk : k ≤ K) (hi : i ≤ k) (x : Label.{u}) :
    visibilityReplace k i x ≤ B ↔ x ≤ B := by
  refine ⟨fun hle ↦ (le_visibilityReplace (k := k) (i := k) (by omega) x).trans ?_,
    fun hle ↦ visibilityReplace_le_of_le hi (hB.mono hk) hle⟩
  have := visibilityReplace_le_of_le le_rfl (hB.mono hk) hle
  rw [visibilityReplace_visibilityReplace_of_le le_rfl] at this
  split_ifs at this with hik
  · exact this
  · obtain rfl : i = k := by omega
    exact this

/-- **The band raise**: `c` at the labels above `B`, at least `h` and below `c`. -/
noncomputable def bandRaise (B h c x : Label.{u}) : Label.{u} :=
  if B < x ∧ h ≤ x ∧ x < c then c else x

variable {B h c x : Label.{u}}

theorem le_bandRaise (B h c x : Label.{u}) : x ≤ bandRaise B h c x := by
  unfold bandRaise
  split_ifs with hx
  exacts [hx.2.2.le, le_rfl]

theorem bandRaise_of_mem (hx : B < x ∧ h ≤ x ∧ x < c) : bandRaise B h c x = c := ite_eq_left hx

theorem bandRaise_of_not_mem (hx : ¬ (B < x ∧ h ≤ x ∧ x < c)) : bandRaise B h c x = x :=
  ite_eq_right hx

theorem bandRaise_of_le (hx : x ≤ B) : bandRaise B h c x = x :=
  bandRaise_of_not_mem fun h' ↦ h'.1.not_ge hx

theorem bandRaise_of_ge (hx : c ≤ x) : bandRaise B h c x = x :=
  bandRaise_of_not_mem fun h' ↦ h'.2.2.not_ge hx

/-- The band raise does not change a label capped at `h`. -/
theorem min_bandRaise (B h c x : Label.{u}) : min (bandRaise B h c x) h = min x h := by
  unfold bandRaise
  split_ifs with hx
  · rw [min_eq_right (hx.2.1.trans hx.2.2.le), min_eq_right hx.2.1]
  · rfl

/-- **The band raise is a witness bounded by the grade `K`**, for `B` and `c` self-visible at `K`
and either `h ≤ B` or `h` not crossed by replacement at thresholds `k ≤ K`. -/
theorem isWitness_bandRaise_of_stable {K : ℕ} (hB : IsSelfVisible K B) (hc : IsSelfVisible K c)
    (hh : h ≤ B ∨ ∀ k ≤ K, ∀ i ≤ k, ∀ x : Label.{u}, h ≤ visibilityReplace k i x ↔ h ≤ x) :
    IsWitness (stepSuppressor K) (bandRaise B h c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := bandRaise_of_not_mem fun h' ↦ not_lt_bot h'.1
  monotone := by
    intro x y hxy
    unfold bandRaise
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact not_lt.mp fun hyc ↦ h2 ⟨h1.1.trans_le hxy, h1.2.1.trans hxy, hyc⟩
    · exact hxy.trans h2.2.2.le
    · exact hxy
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · have hlow : ∀ y, (B < visibilityReplace k i y ∧ h ≤ visibilityReplace k i y) ↔
          (B < y ∧ h ≤ y) := by
        intro y
        have e1 : B < visibilityReplace k i y ↔ B < y := by
          rw [← not_le, ← not_le, visibilityReplace_le_iff_of_isSelfVisible hB hk hi]
        rcases hh with hhB | hh3
        · constructor
          · rintro ⟨h1, -⟩
            exact ⟨e1.mp h1, hhB.trans (e1.mp h1).le⟩
          · rintro ⟨h1, -⟩
            exact ⟨e1.mpr h1, hhB.trans (e1.mpr h1).le⟩
        · rw [e1, hh3 k hk i hi]
      have hcc : visibilityReplace k i c = c := (hc.mono hk).visibilityReplace_eq i
      by_cases hJ : B < x ∧ h ≤ x ∧ x < c
      · rw [bandRaise_of_mem hJ, hcc]
        have hle : visibilityReplace k i x ≤ c :=
          visibilityReplace_le_of_le hi (hc.mono hk) hJ.2.2.le
        obtain ⟨h1, h2⟩ := (hlow x).mpr ⟨hJ.1, hJ.2.1⟩
        rcases hle.lt_or_eq with hlt | heq
        · exact bandRaise_of_mem ⟨h1, h2, hlt⟩
        · rw [heq]
          exact bandRaise_of_ge le_rfl
      · rw [bandRaise_of_not_mem hJ]
        refine bandRaise_of_not_mem fun ⟨h1, h2, h3⟩ ↦ ?_
        obtain ⟨h1', h2'⟩ := (hlow x).mp ⟨h1, h2⟩
        have hxc : c ≤ x := not_lt.mp fun hxc ↦ hJ ⟨h1', h2', hxc⟩
        exact h3.not_ge (hcc ▸ monotone_visibilityReplace hi hxc)
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hx0 : x = ⊥ := le_bot_iff.mp (hx ▸ le_bandRaise B h c x)
      subst hx0
      rw [visibilityReplace_bot, hx, visibilityReplace_bot]

/-- **The band raise is a witness bounded by the grade `K`**, for `B` and `c` self-visible at `K`
and either `h ≤ B` or `h` self-visible at `K + 1`. -/
theorem isWitness_bandRaise {K : ℕ} (hB : IsSelfVisible K B) (hc : IsSelfVisible K c)
    (hh : h ≤ B ∨ IsSelfVisible (K + 1) h) : IsWitness (stepSuppressor K) (bandRaise B h c) :=
  isWitness_bandRaise_of_stable hB hc
    (hh.imp id fun hh3 _ hk _ hi x ↦ hh3.le_visibilityReplace_iff hk hi x)

/-- Replacement does not cross an ordinal that is zero or a limit. -/
theorem coe_le_visibilityReplace_iff {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (k i : ℕ)
    (x : Label.{u}) : (μ : Label.{u}) ≤ visibilityReplace k i x ↔ (μ : Label.{u}) ≤ x := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    rw [visibilityReplace_coe, WithBot.coe_le_coe, WithTop.coe_le_coe, WithBot.coe_le_coe,
      WithTop.coe_le_coe, ← not_lt, ← not_lt, Ordinal.visibilityReplace_lt_iff hμ]

/-! ### Refined donor raising from capped lifts -/

section Raising

variable {ιC ιD ιR : Type*} {rc : ιR → ιC} {rd : ιR → ιD} {K : ℕ}

/-- **The capped-lift provision**: a lawful served face `R` and a lawful context face `f` agreeing
on the root capped at `h` (self-visible at `K`) have a lawful served face with the root of `f`,
agreeing with `R` capped at `h`. -/
def HasCappedLifts (rc : ιR → ιC) (rd : ιR → ιD) (K : ℕ) (C : (ιC → Label.{u}) → Prop)
    (D : (ιD → Label.{u}) → Prop) : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible K h → ∀ {R : ιD → Label.{u}} {f : ιC → Label.{u}}, D R → C f →
    (∀ x, min (f (rc x)) h = min (R (rd x)) h) →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ ∀ d, min (W d) h = min (R d) h

/-- **The tie at a cap not self-visible at `K + 1`**: the refined donor raising at a cap `h` not
self-visible at `K + 1`, given a capped lift `W₁` whose replaced low maximum is below `h` and whose
designated tops at least `h` are at least `c` or exactly `h` (the case the band raise leaves
open). -/
def TieAtCap (rc : ιR → ιC) (rd : ιR → ιD) (K : ℕ) (C : (ιC → Label.{u}) → Prop)
    (D : (ιD → Label.{u}) → Prop) (A : Set ιR) (Lo Tops : Finset ιD) : Prop :=
  ∀ {h c : Label.{u}}, IsSelfVisible K h → ¬ IsSelfVisible (K + 1) h → IsSelfVisible K c →
    ∀ {R : ιD → Label.{u}} {f : ιC → Label.{u}} {W₁ : ιD → Label.{u}}, D R → C f →
    (∀ x, min (f (rc x)) h = min (R (rd x)) h) → (∀ a ∈ A, c ≤ f (rc a)) →
    D W₁ → (∀ x, W₁ (rd x) = f (rc x)) → (∀ d, min (W₁ d) h = min (R d) h) →
    (∀ t ∈ Tops, h ≤ R t → c ≤ W₁ t ∨ W₁ t = h) → visibilityReplace K K (Lo.sup W₁) < h →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t ∈ Tops, h ≤ R t → c ≤ W t ∨ W t ≤ visibilityReplace K K (Lo.sup W)

/-- **Refined donor raising from capped lifts and the band raise**, at any grade `K`: every root
cell is a low cell or a designated root top, the served faces are closed under witnesses bounded by
`K` above the identity, and the tie at caps not self-visible at `K + 1` holds. -/
theorem donorRaisingV_of_cappedLift {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {A : Set ιR} {Lo Tops : Finset ιD}
    (hlift : HasCappedLifts rc rd K C D)
    (hmap : ∀ {ν : Label.{u} → Label.{u}}, IsWitness (stepSuppressor K) ν → (∀ x, x ≤ ν x) →
      ∀ {W : ιD → Label.{u}}, D W → D fun d ↦ ν (W d))
    (hroot : ∀ x, rd x ∈ Lo ∨ x ∈ A) (htie : TieAtCap rc rd K C D A Lo Tops) :
    DonorRaisingV rc rd K C D A Lo Tops := by
  intro h c hh hc R f hR hf hagr hA
  obtain ⟨W₁, hW₁, hW₁r, hW₁R⟩ := hlift hh hR hf hagr
  set B := visibilityReplace K K (Lo.sup W₁) with hBdef
  have hW₁t : ∀ t, h ≤ R t → h ≤ W₁ t := fun t hRt ↦ by
    have e := hW₁R t
    rw [min_eq_right hRt] at e
    exact min_eq_right_iff.mp e
  by_cases hgood : h ≤ B ∨ IsSelfVisible (K + 1) h
  swap
  · -- the band raise above `h` itself, leaving the tops at exactly `h`
    push Not at hgood
    obtain ⟨hBh, hh3⟩ := hgood
    have hlo : ∀ d ∈ Lo, W₁ d < h := fun d hd ↦
      ((Finset.le_sup (f := W₁) hd).trans (le_visibilityReplace (by omega) _)).trans_lt hBh
    refine htie hh hh3 hc hR hf hagr hA
      (hmap (isWitness_bandRaise hh hc (.inl le_rfl)) (le_bandRaise h h c) hW₁) (fun x ↦ ?_)
      (fun d ↦ ?_) (fun t _ hRt ↦ ?_) ?_
    · rw [hW₁r]
      rcases hroot x with hx | hx
      · refine bandRaise_of_le ?_
        rw [← hW₁r]
        exact (hlo _ hx).le
      · exact bandRaise_of_ge (hA x hx)
    · rw [min_bandRaise, hW₁R]
    · by_cases hJ : h < W₁ t ∧ h ≤ W₁ t ∧ W₁ t < c
      · exact .inl (bandRaise_of_mem hJ).ge
      · rw [bandRaise_of_not_mem hJ]
        rcases (hW₁t t hRt).lt_or_eq with hlt | heq
        · exact .inl (not_lt.mp fun hc' ↦ hJ ⟨hlt, hlt.le, hc'⟩)
        · exact .inr heq.symm
    · rw [Finset.sup_congr rfl fun d hd ↦ bandRaise_of_le (B := h) (h := h) (c := c) (hlo d hd).le]
      exact hBh
  have hB : IsSelfVisible K B := visibilityReplace_self_visibilityReplace le_rfl _
  have hν := isWitness_bandRaise hB hc hgood
  refine ⟨fun d ↦ bandRaise B h c (W₁ d), hmap hν (le_bandRaise B h c) hW₁, fun x ↦ ?_,
    fun d ↦ ?_, fun t _ hRt ↦ ?_⟩
  · change bandRaise B h c (W₁ (rd x)) = f (rc x)
    rw [hW₁r]
    rcases hroot x with hx | hx
    · refine bandRaise_of_le ?_
      rw [← hW₁r]
      exact (Finset.le_sup (f := W₁) hx).trans (le_visibilityReplace (by omega) _)
    · exact bandRaise_of_ge (hA x hx)
  · change min (bandRaise B h c (W₁ d)) h = min (R d) h
    rw [min_bandRaise, hW₁R]
  · have hsup : B ≤ visibilityReplace K K (Lo.sup fun d ↦ bandRaise B h c (W₁ d)) :=
      monotone_visibilityReplace le_rfl
        (Finset.sup_mono_fun fun d _ ↦ le_bandRaise B h c (W₁ d))
    by_cases hJ : B < W₁ t ∧ h ≤ W₁ t ∧ W₁ t < c
    · left
      change c ≤ bandRaise B h c (W₁ t)
      rw [bandRaise_of_mem hJ]
    · by_cases hle : W₁ t ≤ B
      · right
        change bandRaise B h c (W₁ t) ≤ _
        rw [bandRaise_of_le hle]
        exact hle.trans hsup
      · left
        have : c ≤ W₁ t := not_lt.mp fun hlt ↦ hJ ⟨not_le.mp hle, hW₁t t hRt, hlt⟩
        exact this.trans (le_bandRaise _ _ _ _)

/-- A cell of the served face is **determined by the root** when lawful served faces agreeing on
the root agree at it. -/
def IsRootDet (rd : ιR → ιD) (D : (ιD → Label.{u}) → Prop) (d : ιD) : Prop :=
  ∀ W W' : ιD → Label.{u}, D W → D W' → (∀ x, W (rd x) = W' (rd x)) → W d = W' d

/-- **Donor raising with the gap from capped lifts**, at any grade `K`, with no tie hypothesis:
every root cell is a low cell or a designated root top, every cell of the served face is a low
cell, a designated top, a root cell, or determined by the root, and the served faces are closed
under witnesses bounded by `K` above the identity.

At a cap `h = μ + K` (`μ` zero or a limit) above the replaced low maximum `B` of the capped lift
`W₁`, with the frontier cap `c` above `h`: the band raise of `[μ, c)` to `c` is a witness, and no
cell of `W₁` has a label in `[μ, h)` (a low cell is at most `B < μ`; a designated top there is at
least `min c h = h` by the gap; a root cell is low or at least `c`; a cell determined by the root
is fixed by the band raise, which fixes the root).  So the band raise of `W₁` keeps the agreement
capped at `h` and raises every designated top at least `h` to at least `c`. -/
theorem donorRaisingGap_of_cappedLift {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {A : Set ιR} {Lo Tops : Finset ιD}
    (hlift : HasCappedLifts rc rd K C D)
    (hmap : ∀ {ν : Label.{u} → Label.{u}}, IsWitness (stepSuppressor K) ν → (∀ x, x ≤ ν x) →
      ∀ {W : ιD → Label.{u}}, D W → D fun d ↦ ν (W d))
    (hroot : ∀ x, rd x ∈ Lo ∨ x ∈ A)
    (hcls : ∀ d, d ∈ Lo ∨ d ∈ Tops ∨ (∃ x, rd x = d) ∨ IsRootDet rd D d) :
    DonorRaisingGap rc rd K C D A Lo Tops := by
  intro h c hh hc R f hR hf hagr hA hgap
  obtain ⟨W₁, hW₁, hW₁r, hW₁R⟩ := hlift hh hR hf hagr
  set B := visibilityReplace K K (Lo.sup W₁) with hBdef
  have hB : IsSelfVisible K B := visibilityReplace_self_visibilityReplace le_rfl _
  have hW₁t : ∀ t, h ≤ R t → h ≤ W₁ t := fun t hRt ↦ by
    have e := hW₁R t
    rw [min_eq_right hRt] at e
    exact min_eq_right_iff.mp e
  have hloB : ∀ d ∈ Lo, W₁ d ≤ B := fun d hd ↦
    (Finset.le_sup (f := W₁) hd).trans (le_visibilityReplace (by omega) _)
  by_cases hgood : h ≤ B ∨ IsSelfVisible (K + 1) h
  · -- the band raise of `(B, c) ∩ [h, c)`
    have hν := isWitness_bandRaise hB hc hgood
    refine ⟨fun d ↦ bandRaise B h c (W₁ d), hmap hν (le_bandRaise B h c) hW₁, fun x ↦ ?_,
      fun d ↦ ?_, fun t _ hRt ↦ ?_⟩
    · change bandRaise B h c (W₁ (rd x)) = f (rc x)
      rw [hW₁r]
      rcases hroot x with hx | hx
      · refine bandRaise_of_le ?_
        rw [← hW₁r]
        exact hloB _ hx
      · exact bandRaise_of_ge (hA x hx)
    · change min (bandRaise B h c (W₁ d)) h = min (R d) h
      rw [min_bandRaise, hW₁R]
    · have hsup : B ≤ visibilityReplace K K (Lo.sup fun d ↦ bandRaise B h c (W₁ d)) :=
        monotone_visibilityReplace le_rfl
          (Finset.sup_mono_fun fun d _ ↦ le_bandRaise B h c (W₁ d))
      by_cases hJ : B < W₁ t ∧ h ≤ W₁ t ∧ W₁ t < c
      · left
        change c ≤ bandRaise B h c (W₁ t)
        rw [bandRaise_of_mem hJ]
      · by_cases hle : W₁ t ≤ B
        · right
          change bandRaise B h c (W₁ t) ≤ _
          rw [bandRaise_of_le hle]
          exact hle.trans hsup
        · left
          have : c ≤ W₁ t := not_lt.mp fun hlt ↦ hJ ⟨not_le.mp hle, hW₁t t hRt, hlt⟩
          exact this.trans (le_bandRaise _ _ _ _)
  push Not at hgood
  obtain ⟨hBh, hh3⟩ := hgood
  -- a frontier cap at most `h`: the capped lift itself
  by_cases hch : c ≤ h
  · exact ⟨W₁, hW₁, hW₁r, hW₁R, fun t _ hRt ↦ .inl (hch.trans (hW₁t t hRt))⟩
  have hhc : h < c := not_le.mp hch
  -- the cap is `μ + K` with `μ` zero or a limit
  have hhbot : h ≠ ⊥ := ne_bot_of_gt hBh
  have hhtop : h ≠ ⊤ := fun e ↦ hh3 (e ▸ isSelfVisible_top _)
  obtain ⟨o, rfl⟩ : ∃ o : Ordinal.{u}, h = (o : Label.{u}) := by
    induction h using recBotCoeTop with
    | bot => exact absurd rfl hhbot
    | top => exact absurd rfl hhtop
    | coe o => exact ⟨o, rfl⟩
  obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
  have hjK : j = K := by
    have h1 := (isSelfVisible_coe_add_natCast_iff hμ).mp hh
    have h2 : ¬ K + 1 ≤ j := fun h' ↦ hh3 ((isSelfVisible_coe_add_natCast_iff hμ).mpr h')
    omega
  subst j
  set a : Label.{u} := (μ : Label.{u}) with ha
  have hah : a ≤ ((μ + K : Ordinal.{u}) : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
  have hBa : B < a := by
    refine not_le.mp fun haB ↦ hBh.not_ge ?_
    have e : visibilityReplace K K a = ((μ + K : Ordinal.{u}) : Label.{u}) := by
      have := visibilityReplace_coe_add hμ K K 0
      simp only [Nat.cast_zero, add_zero] at this
      rcases Nat.eq_zero_or_pos K with hK0 | hK0
      · subst hK0
        rw [ha, visibilityReplace_coe, Ordinal.visibilityReplace_of_le (by simp)]
        simp
      · simpa only [hK0, ↓reduceIte] using this
    rw [← e, ← hB.visibilityReplace_eq K]
    exact monotone_visibilityReplace le_rfl haB
  have hν := isWitness_bandRaise_of_stable (h := a) hB hc
    (.inr fun k _ i _ x ↦ coe_le_visibilityReplace_iff hμ k i x)
  set ψ := bandRaise B a c with hψ
  have hψD : D fun d ↦ ψ (W₁ d) := hmap hν (le_bandRaise B a c) hW₁
  have hrootfix : ∀ x, ψ (W₁ (rd x)) = W₁ (rd x) := fun x ↦ by
    rcases hroot x with hx | hx
    · exact bandRaise_of_le (hloB _ hx)
    · exact bandRaise_of_ge ((hA x hx).trans (hW₁r x).ge)
  -- no label of the capped lift in `[μ, h)`
  have hwin : ∀ d, a ≤ W₁ d → ((μ + K : Ordinal.{u}) : Label.{u}) ≤ W₁ d := by
    intro d had
    by_contra hdh
    push Not at hdh
    have hRd : R d = W₁ d := Label.eq_of_min_eq_of_lt (hW₁R d) hdh
    rcases hcls d with hd | hd | ⟨x, rfl⟩ | hd
    · exact (hloB d hd).not_gt (hBa.trans_le had)
    · have hsupR : Lo.sup R = Lo.sup W₁ := Finset.sup_congr rfl fun e he ↦
        Label.eq_of_min_eq_of_lt (hW₁R e) (((hloB e he).trans_lt hBa).trans_le hah)
      have := hgap d hd (by rw [hsupR, hRd]; exact hBa.trans_le had)
      rw [min_eq_right hhc.le, hRd] at this
      exact hdh.not_ge this
    · rcases hroot x with hx | hx
      · exact (hloB _ hx).not_gt (hBa.trans_le had)
      · exact hdh.not_ge (hhc.le.trans ((hA x hx).trans (hW₁r x).ge))
    · have e := hd _ _ hψD hW₁ hrootfix
      rw [show ψ (W₁ d) = c from bandRaise_of_mem ⟨hBa.trans_le had, had, hdh.trans hhc⟩] at e
      exact (hdh.trans hhc).ne' e
  refine ⟨fun d ↦ ψ (W₁ d), hψD, fun x ↦ (hrootfix x).trans (hW₁r x), fun d ↦ ?_,
    fun t _ hRt ↦ .inl ?_⟩
  · change min (ψ (W₁ d)) _ = min (R d) _
    by_cases had : a ≤ W₁ d
    · have h1 := hwin d had
      rw [← hW₁R d, min_eq_right h1, min_eq_right (h1.trans (le_bandRaise B a c (W₁ d)))]
    · rw [show ψ (W₁ d) = W₁ d from bandRaise_of_not_mem fun h' ↦ had h'.2.1, hW₁R]
  · change c ≤ ψ (W₁ t)
    have h1 := hW₁t t hRt
    by_cases htc : W₁ t < c
    · rw [show ψ (W₁ t) = c from bandRaise_of_mem ⟨hBa.trans_le (hah.trans h1), hah.trans h1, htc⟩]
    · exact (not_lt.mp htc).trans (le_bandRaise B a c (W₁ t))

end Raising

/-! ### Capped lifts at a legal stage type from a face -/

/-- **Capped lifts from a face of a legal stage type**: for a face on `n > 0` points, `n < K ≤ k`,
every cell of grade at most `K`, and a cap `h` self-visible at `K`, a lawful labelling `L` and a
lawful labelling `y` of the face agreeing with `L` capped at `h` have a lawful labelling with face
`y`, agreeing with `L` capped at `h` (bountifulness). -/
theorem exists_isLawful_cappedLift_face {α : Ordinal.{u}} {k n K : ℕ} {t : StageType.{u} α k}
    (hleg : t.IsLegal) {g : Fin n ↪ Fin k} {s : StageType.{u} α n}
    (ht : StageType.restrictFace g t = some s) (hn : 0 < n) (hnK : n < K) (hKk : K ≤ k)
    (hK : ∀ d, t.toCellScheme.grade d ≤ K) {h : Label.{u}} (hh : IsSelfVisible K h)
    {L : Fin t.card → Label.{u}} (hL : t.rows.IsLawful L) {y : Fin s.card → Label.{u}}
    (hy : s.rows.IsLawful y) (hroot : ∀ i, min (y i) h = min (L (StageType.faceCell ht i)) h) :
    ∃ W : Fin t.card → Label.{u}, t.rows.IsLawful W ∧ (∀ i, W (StageType.faceCell ht i) = y i) ∧
      ∀ d, min (W d) h = min (L d) h := by
  classical
  obtain ⟨hf, -⟩ := (StageType.restrictFace_eq_some_iff (t := t) (f := g)).mp ht
  have he := StageType.comap_toScheme_of_restrictFace ht
  have hinj : Function.Injective (StageType.faceCell ht) := by
    intro i j hij
    have := (t.toScheme.cellMap g).injective hij
    exact Fin.cast_injective _ this
  set x : Fin t.card → Label.{u} := Function.extend (StageType.faceCell ht) y (fun _ ↦ ⊥)
  have hx (i : Fin s.card) : x (StageType.faceCell ht i) = y i := hinj.extend_apply _ _ i
  have hpX : t.rows.IsLawfulBelow (Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n))
      (fun d ↦ x d) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ x).mp ?_
    convert hy.isLawfulBelow ((univ : Finset (Fin n)), n) using 2 with i
    exact hx i.1
  have hXY : Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n) ≤
      ((univ : Finset (Fin k)), K) := ⟨subset_univ _, hnK.le⟩
  have hX : Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n) ∈
      t.toCellScheme.gradedFaces := ⟨hf, hn, by simp⟩
  have hY : ((univ : Finset (Fin k)), K) ∈ t.toCellScheme.gradedFaces :=
    ⟨t.univ_mem_faces, hn.trans hnK, by simpa using hKk⟩
  have hlift := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (hleg.isBountiful hX hY hXY) h hh (fun d ↦ x d) (fun d ↦ L d) hpX
    (hL.isLawfulBelow _) (fun d ↦ ?_)
  rotate_left
  · have hvis : d.1 ∈ t.toScheme.visibleCells g := by
      refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
      have hy' : y ∈ (univ : Finset (Fin n)).map g := d.2.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hvis
    change min (L d.1) h = min (x d.1) h
    rw [← hi]
    change min (L (StageType.faceCell ht i)) h = min (x (StageType.faceCell ht i)) h
    rw [hx]
    exact (hroot i).symm
  obtain ⟨q', hq', hq'L, hq'p⟩ := hlift
  have hmem (d : Fin t.card) : d ∈ t.toCellScheme.below ((univ : Finset (Fin k)), K) :=
    ⟨subset_univ _, hK d⟩
  refine ⟨fun d ↦ q' ⟨d, hmem d⟩, hq'.isLawful fun d ↦ hmem d, fun i ↦ ?_, fun d ↦ ?_⟩
  · have hvX : StageType.faceCell ht i ∈ t.toCellScheme.below
        (Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n)) :=
      (CellScheme.mem_below _).mpr
        ⟨show t.toCellScheme.scope (StageType.faceCell ht i) ⊆ (univ : Finset (Fin n)).map g by
          rw [StageType.scope_faceCell]; exact map_subset_map.mpr (subset_univ _),
        show t.toCellScheme.grade (StageType.faceCell ht i) ≤ n by
          rw [StageType.grade_faceCell]; exact s.grade_le i⟩
    have := hq'p ⟨_, hvX⟩
    change q' ⟨StageType.faceCell ht i, _⟩ = x (StageType.faceCell ht i) at this
    exact this.trans (hx i)
  · exact hq'L ⟨d, hmem d⟩

/-- **Capped lifts between two legal stage types sharing a face** (`H2.HasCappedLifts`), lifting
into the second. -/
theorem hasCappedLifts_of_isLegal {α : Ordinal.{u}} {k n K : ℕ} {t' : StageType.{u} α k}
    {g : Fin n ↪ Fin k} {s : StageType.{u} α n} (ht : StageType.restrictFace g t' = some s)
    {tb : StageType.{u} α k} (htbleg : tb.IsLegal) (htb : StageType.restrictFace g tb = some s)
    (hn : 0 < n) (hnK : n < K) (hKk : K ≤ k) (hK : ∀ d, tb.toCellScheme.grade d ≤ K) :
    HasCappedLifts (StageType.faceCell ht) (StageType.faceCell htb) K t'.rows.IsLawful
      tb.rows.IsLawful := fun hh _ _ hR hf hagr ↦
  exists_isLawful_cappedLift_face htbleg htb hn hnK hKk hK hh hR
    (StageType.isLawful_comp_faceCell ht hf) hagr

end VaughtConjecture.H2

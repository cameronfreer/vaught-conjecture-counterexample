/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsCode
import VaughtConjecture.Extension.SourceGapRequests

/-!
# The orbit-literal premise

Roadmap, Layer 3 (3.1: the catalogue at a grade; 3.3: the admissions of (R2), (R3) and (R4)).

Let `ι` be a family of cells with grades `grade`, `lab : ι → Label` the literal labels, and `priv`
a set of cells (the private cells).  A state `s` is **orbit-literal**
(`IsOrbitLiteral grade lab priv s`) when on the private cells it is a capped transformation image of
the literal labels: for some witness `(g, σ)`, `s d = min (σ (lab d)) (g (grade d))` for every
`d ∈ priv`.

## Results

Each item below is compiled in this file (theorem named).

* **The literal labels** are orbit-literal (`isOrbitLiteral_self`), and so is every
  transformation image of them (`IsOrbitLiteral.of_transformsTo`).
* **Capping** at a label `h` self-visible at `K` keeps the premise when the private cells have
  grade at most `K` (`IsOrbitLiteral.cap`), and capping by the step suppressor at a grade `k` (the
  splice of a profile at `k`, `⊥` above `k`) keeps it with no condition
  (`IsOrbitLiteral.min_stepSuppressor`, and `IsOrbitLiteral.hat` for `ProfileTower.hat`).
* **Plain images** `τ ∘ s` under a witness bounded by a grade `K'` keep the premise when `τ` is
  strictly monotone and the private cells have grade at most `K'` (`IsOrbitLiteral.comp`): the
  composite `(τ ∘ g, τ ∘ σ)` is a witness, since a strictly monotone `τ` reflects the comparison
  of the shifter with the suppressor under which the shifter commutes with replacement.
  **Without strict monotonicity they do not** (`not_forall_isOrbitLiteral_comp`): this is the
  nontransitivity of the transformation relation.  The labels `(1, 2)` at grade `1` give the
  orbit-literal state `(1, ⊤)`, and its image `(⊥, ⊤)` under the witness sending every label other
  than `⊤` to `⊥` is not orbit-literal.  The orbit map of a profile is not strictly monotone, so
  closure under the orbit code is not given by this argument; it is not decided here.
* **Tie inversion** (`not_isOrbitLiteral_of_tie_inversion`): if two private cells carry one literal
  label and `s` reads them at `1` and `2`, the second of grade at least `1`, then `s` is not
  orbit-literal.  At equal grades a capped image keeps the tie; at a larger grade of the first cell,
  the value `1` would be the suppressor at a grade at least `2`, where it is not self-visible.

## Admission with the orbit-literal premise

`CapRequests.AdmitsOrbit r grade lab priv s` asks that an orbit-literal state be correct.  An
admission of the form "premise implies correctness" is kept by a map only if the map **reflects**
the premise (the premise of the image gives the premise of the source); forward closure of the
premise, as above, does not help.  The orbit-literal premise is not reflected by capping:
`CapRequests.not_forall_admitsOrbit_cap` exhibits a state admitted vacuously (it inverts a tie, so
it is not orbit-literal) whose cap at the self-visible label `1` is orbit-literal and not correct.
So `AdmitsOrbit` is not closed under capping.  What the closures above give is the closure of the
**conjunction**, orbit-literal and correct, under capping, splicing and strictly monotone plain
images (`CapRequests.IsCorrect.cap_isOrbitLiteral`, `CapRequests.IsCorrect.comp_isOrbitLiteral`).
The same holds for the partner-form low admission of source-gap requests
(`SourceGapRequests.AdmitsOrbitVia`, `SourceGapRequests.AdmitsLowVia.cap_isOrbitLiteral`,
`SourceGapRequests.AdmitsLowVia.comp_isOrbitLiteral`).
-/

universe u

namespace VaughtConjecture

open Label

variable {ι : Type*} {grade : ι → ℕ} {lab s : ι → Label.{u}} {priv : Set ι}

/-- A state is **orbit-literal**: on the private cells it is a capped transformation image of the
literal labels. -/
def IsOrbitLiteral (grade : ι → ℕ) (lab : ι → Label.{u}) (priv : Set ι) (s : ι → Label.{u}) :
    Prop :=
  ∃ g σ, IsWitness g σ ∧ ∀ d ∈ priv, s d = min (σ (lab d)) (g (grade d))

/-- **The literal labels are orbit-literal.** -/
theorem isOrbitLiteral_self : IsOrbitLiteral grade lab priv lab :=
  ⟨_, _, IsWitness.id_top, fun _ _ ↦ (min_top_right _).symm⟩

/-- A transformation image of the literal labels is orbit-literal. -/
theorem IsOrbitLiteral.of_transformsTo (h : TransformsTo grade lab s) :
    IsOrbitLiteral grade lab priv s :=
  let ⟨g, σ, hw, heq⟩ := h
  ⟨g, σ, hw, fun d _ ↦ heq d⟩

/-- **Capping keeps the premise**, at a label `h` self-visible at a bound `K` on the grades of the
private cells. -/
theorem IsOrbitLiteral.cap (hs : IsOrbitLiteral grade lab priv s) {K : ℕ} {h : Label.{u}}
    (hh : IsSelfVisible K h) (hK : ∀ d ∈ priv, grade d ≤ K) :
    IsOrbitLiteral grade lab priv fun d ↦ min (s d) h := by
  obtain ⟨g, σ, hw, heq⟩ := hs
  refine ⟨_, σ, hw.cap hh, fun d hd ↦ ?_⟩
  simp only [heq d hd, hK d hd, ↓reduceIte, min_assoc]

/-- **Capping by the step suppressor keeps the premise** (the splice of a profile at `k`). -/
theorem IsOrbitLiteral.min_stepSuppressor (hs : IsOrbitLiteral grade lab priv s) (k : ℕ) :
    IsOrbitLiteral grade lab priv fun d ↦ min (s d) (stepSuppressor k (grade d)) := by
  obtain ⟨g, σ, hw, heq⟩ := hs
  refine ⟨_, σ, hw.truncate k, fun d hd ↦ ?_⟩
  change min (s d) (stepSuppressor k (grade d)) = _
  rw [heq d hd]
  by_cases hk : grade d ≤ k
  · simp only [stepSuppressor_of_le hk, hk, ↓reduceIte, min_top_right]
  · simp only [stepSuppressor_of_lt (not_le.mp hk), hk, ↓reduceIte, min_bot_right]

/-- **Strictly monotone plain images keep the premise**: for a witness `τ` bounded by a grade `K'`
that is strictly monotone, and private cells of grade at most `K'`, the image `τ ∘ s` is
orbit-literal when `s` is. -/
theorem IsOrbitLiteral.comp (hs : IsOrbitLiteral grade lab priv s) {K' : ℕ}
    {τ : Label.{u} → Label.{u}} (hτ : IsWitness (stepSuppressor K') τ) (hmono : StrictMono τ)
    (hK : ∀ d ∈ priv, grade d ≤ K') : IsOrbitLiteral grade lab priv (τ ∘ s) := by
  obtain ⟨g, σ, hw, heq⟩ := hs
  have hw₁ := hw.truncate K'
  set g₁ : ℕ → Label.{u} := fun n ↦ if n ≤ K' then g n else ⊥ with hg₁
  have hτc (n : ℕ) (hn : n ≤ K') (x : Label.{u}) (i : ℕ) (hi : i ≤ n) :
      τ (visibilityReplace n i x) = visibilityReplace n i (τ x) :=
    hτ.visibilityReplace_comm x n (by rw [stepSuppressor_of_le hn]; exact le_top) i hi
  refine ⟨fun n ↦ τ (g₁ n), τ ∘ σ, ⟨fun a b hab ↦ hτ.monotone (hw₁.antitone hab), fun n ↦ ?_,
    by simp [hw.map_bot, hτ.map_bot], hτ.monotone.comp hw.monotone, ?_⟩, fun d hd ↦ ?_⟩
  · by_cases hn : n ≤ K'
    · exact ((hτc n hn _ n le_rfl).symm.trans (congrArg τ (hw₁.isSelfVisible n)) :)
    · simp only [hg₁, hn, ↓reduceIte, hτ.map_bot]
      exact isSelfVisible_bot n
  · intro x k hx i hi
    simp only [Function.comp_apply] at hx ⊢
    have hσ : σ x ≤ g₁ k := hmono.le_iff_le.mp hx
    rw [hw₁.visibilityReplace_comm x k hσ i hi]
    by_cases hk : k ≤ K'
    · exact hτc k hk _ i hi
    · have hb : σ x = ⊥ := le_bot_iff.mp (by simpa [hg₁, hk] using hσ)
      rw [hb, visibilityReplace_bot, hτ.map_bot, visibilityReplace_bot]
  · simp only [Function.comp_apply, heq d hd, hτ.monotone.map_min, hg₁, hK d hd, ↓reduceIte]

/-- **Tie inversion**: if two private cells carry one literal label, `s` reads the first at `1`
and the second at `2`, and the second has grade at least `1`, then `s` is not orbit-literal. -/
theorem not_isOrbitLiteral_of_tie_inversion {d₁ d₂ : ι} (h₁ : d₁ ∈ priv) (h₂ : d₂ ∈ priv)
    (hlab : lab d₁ = lab d₂) (hs₁ : s d₁ = ((1 : ℕ) : Label.{u}))
    (hs₂ : s d₂ = ((2 : ℕ) : Label.{u})) (hg : 1 ≤ grade d₂) :
    ¬ IsOrbitLiteral grade lab priv s := by
  rintro ⟨g, σ, hw, heq⟩
  have e₁ := heq d₁ h₁
  have e₂ := heq d₂ h₂
  rw [hs₁] at e₁
  rw [hs₂, ← hlab] at e₂
  have h12 : ((1 : ℕ) : Label.{u}) < ((2 : ℕ) : Label.{u}) := natCast_label_lt.mpr (by omega)
  rcases le_or_gt (grade d₁) (grade d₂) with hle | hlt
  · have : min (σ (lab d₁)) (g (grade d₂)) ≤ min (σ (lab d₁)) (g (grade d₁)) :=
      min_le_min_left _ (hw.antitone hle)
    rw [← e₁, ← e₂] at this
    exact absurd this (not_le.mpr h12)
  · have hσ : ((2 : ℕ) : Label.{u}) ≤ σ (lab d₁) := e₂ ▸ min_le_left _ _
    have hg₁ : g (grade d₁) = ((1 : ℕ) : Label.{u}) := by
      rcases le_total (σ (lab d₁)) (g (grade d₁)) with h | h
      · rw [min_eq_left h] at e₁
        exact absurd (e₁ ▸ hσ) (not_le.mpr h12)
      · rw [min_eq_right h] at e₁
        exact e₁.symm
    have hv := hw.isSelfVisible (grade d₁)
    rw [hg₁, isSelfVisible_natCast] at hv
    omega

/-! ### Plain images that are not strictly monotone -/

section Nontransitive

open Ordinal

/-- The labels `(1, 2)` at grade one transform to `(1, ⊤)` (as in `Label.TransformsTo`, the
nontransitivity example). -/
private theorem transformsTo_one_two_one_top :
    TransformsTo (fun _ : Bool ↦ 1)
      (fun b ↦ ((if b then 2 else 1 : Ordinal.{u}) : Label.{u}))
      (fun b ↦ if b then ⊤ else ((1 : Ordinal.{u}) : Label.{u})) := by
  refine ⟨stepSuppressor 1, Label.reduce 2, ⟨(IsWitness.id_step 1).antitone,
    (IsWitness.id_step 1).isSelfVisible, reduce_bot, monotone_reduce 2, ?_⟩, ?_⟩
  · intro x k hx i hi
    rcases le_or_gt k 1 with hk | hk
    · by_cases h2 : ((2 : Ordinal.{u}) : Label.{u}) ≤ x
      · rw [reduce_of_le h2, visibilityReplace_top,
          reduce_of_le (h2.trans (le_visibilityReplace (by omega) x))]
      rw [not_le] at h2
      rw [reduce_of_lt h2]
      refine reduce_of_lt ?_
      induction x using recBotCoeTop with
      | bot => exact h2
      | coe o =>
        have ho : o < 2 := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h2)
        have hω : o < ω := ho.trans (by exact_mod_cast natCast_lt_omega0 2)
        have hi2 : (i : Ordinal.{u}) < 2 := by exact_mod_cast (hi.trans hk).trans_lt one_lt_two
        simp only [visibilityReplace_coe, Ordinal.visibilityReplace_of_lt_omega0 hω,
          WithBot.coe_lt_coe, WithTop.coe_lt_coe]
        split_ifs <;> assumption
      | top => simp at h2
    · rw [stepSuppressor_of_lt hk, le_bot_iff, reduce_eq_bot_iff] at hx
      simp [hx, reduce_bot]
  · have h12 : ((1 : Ordinal.{u}) : Label.{u}) < ((2 : Ordinal.{u}) : Label.{u}) :=
      WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr one_lt_two)
    intro b
    cases b
    · rw [stepSuppressor_of_le le_rfl, min_top_right]
      exact (reduce_of_lt h12).symm
    · rw [stepSuppressor_of_le le_rfl, min_top_right]
      exact (reduce_of_le le_rfl).symm

/-- The labels `(1, 2)` at grade one do not transform to `(⊥, ⊤)` (as in `Label.TransformsTo`,
the nontransitivity example). -/
private theorem not_transformsTo_one_two_bot_top :
    ¬ TransformsTo (fun _ : Bool ↦ 1)
      (fun b ↦ ((if b then 2 else 1 : Ordinal.{u}) : Label.{u}))
      (fun b ↦ if b then ⊤ else ⊥) := by
  rintro ⟨g, τ, hw, heq⟩
  have h₁ := heq false
  have h₂ := heq true
  simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
  have hg : g 1 = ⊤ := top_le_iff.mp (h₂.le.trans (min_le_right _ _))
  rw [hg, min_top_right] at h₁ h₂
  have h := hw.visibilityReplace_comm _ 2 (h₁ ▸ bot_le) 2 le_rfl
  have h12 : Ordinal.visibilityReplace 2 2 (1 : Ordinal.{u}) = 2 := by simp
  rw [visibilityReplace_coe, h12, ← h₁, visibilityReplace_bot, ← h₂] at h
  exact top_ne_bot h

open Classical in
/-- The shifter sending every label other than `⊤` to `⊥` is a witness bounded by grade `1`. -/
private theorem isWitness_topIndicator :
    IsWitness (stepSuppressor.{u} 1) fun x : Label.{u} ↦ if x = ⊤ then ⊤ else ⊥ := by
  have hw : IsWitness (fun _ ↦ (⊤ : Label.{u})) fun x : Label.{u} ↦ if x = ⊤ then ⊤ else ⊥ :=
    ⟨antitone_const, fun _ ↦ isSelfVisible_top _, by simp, fun x y hxy ↦ by
      split_ifs with hx hy <;> simp_all, fun x k _ i _ ↦ by by_cases hx : x = ⊤ <;> simp [hx]⟩
  exact hw.of_le (fun _ ↦ le_top) (IsWitness.id_step 1).antitone
    (IsWitness.id_step 1).isSelfVisible

/-- **Plain images do not keep the premise**: the labels `(1, 2)` at grade `1` give the
orbit-literal state `(1, ⊤)`, whose image `(⊥, ⊤)` under a witness bounded by grade `1` is not
orbit-literal. -/
theorem not_forall_isOrbitLiteral_comp :
    ¬ ∀ (lab s : Bool → Label.{u}) (τ : Label.{u} → Label.{u}),
      IsOrbitLiteral (fun _ ↦ 1) lab Set.univ s → IsWitness (stepSuppressor 1) τ →
        IsOrbitLiteral (fun _ ↦ 1) lab Set.univ (τ ∘ s) := by
  classical
  intro h
  have hs := IsOrbitLiteral.of_transformsTo (priv := Set.univ) transformsTo_one_two_one_top.{u}
  obtain ⟨g, σ, hw, heq⟩ := h _ _ _ hs isWitness_topIndicator
  refine not_transformsTo_one_two_bot_top.{u} ⟨g, σ, hw, fun b ↦ ?_⟩
  rw [← heq b (Set.mem_univ b)]
  have h1 : ((1 : Ordinal.{u}) : Label.{u}) ≠ ⊤ :=
    (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (1 : Ordinal.{u}))).ne
  cases b
  · simpa using h1
  · simp

end Nontransitive

/-! ### Admission with the orbit-literal premise -/

namespace CapRequests

variable {r : CapRequests ι}

variable (r) in
/-- **Admission with the orbit-literal premise**: an orbit-literal state is correct. -/
def AdmitsOrbit (grade : ι → ℕ) (lab : ι → Label.{u}) (priv : Set ι) (s : ι → Label.{u}) :
    Prop :=
  IsOrbitLiteral grade lab priv s → r.IsCorrect s

/-- A correct state is admitted. -/
theorem IsCorrect.admitsOrbit (hs : r.IsCorrect s) : r.AdmitsOrbit grade lab priv s :=
  fun _ ↦ hs

/-- **The conjunction is kept by capping**: an orbit-literal correct state, capped at a label
self-visible at `N`, with offsets of `F` at most `N` and private cells of grade at most `N`, is
orbit-literal and correct. -/
theorem IsCorrect.cap_isOrbitLiteral (hs : r.IsCorrect s) (ho : IsOrbitLiteral grade lab priv s)
    (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) {h : Label.{u}} (hh : IsSelfVisible r.N h)
    (hK : ∀ d ∈ priv, grade d ≤ r.N) :
    r.IsCorrect (fun d ↦ min (s d) h) ∧ IsOrbitLiteral grade lab priv fun d ↦ min (s d) h :=
  ⟨hs.cap hoff hh, ho.cap hh hK⟩

/-- **The conjunction is kept by strictly monotone plain images** bounded by a grade `K' ≥ N`. -/
theorem IsCorrect.comp_isOrbitLiteral (hs : r.IsCorrect s) (ho : IsOrbitLiteral grade lab priv s)
    {K' : ℕ} {τ : Label.{u} → Label.{u}} (hτ : IsWitness (stepSuppressor K') τ)
    (hmono : StrictMono τ) (hNK : r.N ≤ K') (hoff : ∀ f ∈ r.F, r.off f ≤ r.N)
    (hK : ∀ d ∈ priv, grade d ≤ K') :
    r.IsCorrect (τ ∘ s) ∧ IsOrbitLiteral grade lab priv (τ ∘ s) :=
  ⟨hs.comp hτ hNK hoff, ho.comp hτ hmono hK⟩

end CapRequests

/-- **The splice of a profile keeps the premise**: `hat I k P` is the profile capped by the step
suppressor at `k`. -/
theorem IsOrbitLiteral.hat {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}
    {lab' : Fin I.amalgam.card → Label.{u}} {priv' : Set (Fin I.amalgam.card)}
    {P : ProfileTower.Prof I}
    (hP : IsOrbitLiteral I.amalgam.toCellScheme.grade lab' priv' P) (k : ℕ) :
    IsOrbitLiteral I.amalgam.toCellScheme.grade lab' priv' (ProfileTower.hat I k P) := by
  rw [CapRequests.hat_eq_min]
  exact hP.min_stepSuppressor k

namespace SourceGapRequests

variable {r : SourceGapRequests ι}

variable (r) in
/-- **The partner-form low admission with the orbit-literal premise**: an orbit-literal state
satisfies the low clause at its value at the partner `π`. -/
def AdmitsOrbitVia (π : ι) (grade : ι → ℕ) (lab : ι → Label.{u}) (priv : Set ι)
    (s : ι → Label.{u}) : Prop :=
  IsOrbitLiteral grade lab priv s → r.AdmitsLowVia π s

/-- A state satisfying the partner form is admitted. -/
theorem AdmitsLowVia.admitsOrbitVia {π : ι} (hs : r.AdmitsLowVia π s) :
    r.AdmitsOrbitVia π grade lab priv s :=
  fun _ ↦ hs

/-- **The conjunction is kept by capping** at a label self-visible at `K`, for private cells of
grade at most `K`. -/
theorem AdmitsLowVia.cap_isOrbitLiteral {π : ι} (hs : r.AdmitsLowVia π s)
    (ho : IsOrbitLiteral grade lab priv s) {h : Label.{u}} (hh : IsSelfVisible r.K h)
    (hK : ∀ d ∈ priv, grade d ≤ r.K) :
    r.AdmitsLowVia π (fun d ↦ min (s d) h) ∧ IsOrbitLiteral grade lab priv fun d ↦ min (s d) h :=
  ⟨hs.cap hh, ho.cap hh hK⟩

/-- **The conjunction is kept by strictly monotone plain images** bounded by a grade `K' ≥ K`. -/
theorem AdmitsLowVia.comp_isOrbitLiteral {π : ι} (hs : r.AdmitsLowVia π s)
    (ho : IsOrbitLiteral grade lab priv s) {K' : ℕ} {τ : Label.{u} → Label.{u}}
    (hτ : IsWitness (stepSuppressor K') τ) (hmono : StrictMono τ) (hK : r.K ≤ K')
    (hpriv : ∀ d ∈ priv, grade d ≤ K') :
    r.AdmitsLowVia π (τ ∘ s) ∧ IsOrbitLiteral grade lab priv (τ ∘ s) :=
  ⟨hs.comp hτ hK, ho.comp hτ hmono hpriv⟩

end SourceGapRequests

/-- The requests of the capping counterexample: the cap `2` with threshold `1`, `Z = {0}`. -/
private def capCounterReq : CapRequests (Fin 3) where
  cap := 2
  N := 1
  R := 0
  R_lt_N := Nat.one_pos
  Z := {0}
  F := ∅
  T := ∅
  ref := id
  off _ := 0
  marker := 2

/-- **Admission with the orbit-literal premise is not kept by capping**: on three cells of grade
`1`, with literal labels `3` at the private cells `0`, `1`, the state `(1, 2, ⊤)` inverts the tie
and is admitted vacuously, while its cap at `1` is orbit-literal (the literal labels capped at
`1`) and not correct (`⊥` is requested at the cell `0` under the cap `1`). -/
theorem CapRequests.not_forall_admitsOrbit_cap :
    ¬ ∀ (r : CapRequests (Fin 3)) (s : Fin 3 → Label.{u}) (h : Label.{u}),
      IsSelfVisible 1 h → r.AdmitsOrbit (fun _ ↦ 1) (fun _ ↦ ((3 : ℕ) : Label.{u})) {0, 1} s →
        r.AdmitsOrbit (fun _ ↦ 1) (fun _ ↦ ((3 : ℕ) : Label.{u})) {0, 1}
          fun d ↦ min (s d) h := by
  intro H
  set s : Fin 3 → Label.{u} := ![((1 : ℕ) : Label.{u}), ((2 : ℕ) : Label.{u}), ⊤] with hs
  have hadm : capCounterReq.AdmitsOrbit (fun _ ↦ 1) (fun _ ↦ ((3 : ℕ) : Label.{u})) {0, 1} s :=
    fun ho ↦ absurd ho (not_isOrbitLiteral_of_tie_inversion (d₁ := 0) (d₂ := 1) (by simp)
      (by simp) rfl rfl rfl le_rfl)
  have hcap :=
    H capCounterReq s ((1 : ℕ) : Label.{u}) ((isSelfVisible_natCast 1).mpr le_rfl) hadm
  -- the cap is orbit-literal: the literal labels capped at `1`
  have ho : IsOrbitLiteral (fun _ ↦ 1) (fun _ ↦ ((3 : ℕ) : Label.{u})) {0, 1}
      fun d ↦ min (s d) ((1 : ℕ) : Label.{u}) := by
    have h₀ := (isOrbitLiteral_self (grade := fun _ : Fin 3 ↦ 1)
      (lab := fun _ ↦ ((3 : ℕ) : Label.{u})) (priv := {0, 1})).cap
        ((isSelfVisible_natCast 1).mpr le_rfl) (K := 1) (fun _ _ ↦ le_rfl)
    obtain ⟨g, σ, hw, heq⟩ := h₀
    refine ⟨g, σ, hw, fun d hd ↦ ?_⟩
    rw [← heq d hd]
    have h13 : ((1 : ℕ) : Label.{u}) ≤ ((3 : ℕ) : Label.{u}) := natCast_label_le.mpr (by omega)
    have h12 : ((1 : ℕ) : Label.{u}) ≤ ((2 : ℕ) : Label.{u}) := natCast_label_le.mpr (by omega)
    rcases hd with rfl | rfl
    · simp [hs]
    · simp [hs]
  have hbot : min (min ((1 : ℕ) : Label.{u}) ((1 : ℕ) : Label.{u}))
      (min ⊤ ((1 : ℕ) : Label.{u})) = ⊥ := (hcap ho).eq_bot 0 rfl
  rw [min_self, min_top_left, min_self] at hbot
  exact natCast_label_ne_bot 1 hbot

end VaughtConjecture

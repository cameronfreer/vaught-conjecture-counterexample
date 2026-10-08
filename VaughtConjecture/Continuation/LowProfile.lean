/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalCode
import VaughtConjecture.Extension.NormalForm

/-!
# LOW profiles: the LOW clause, the partner, and activation by a strict comparison

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3); semantic contract,
items 4 and 8.

The scalar part of the LOW construction [Kni26, §3.3].  A **profile** is a labelling `a : X → Label`
of a finite type of **fields**: in the construction, the cells of the donor and of the private
context, and one more field, the **cutoff** `β`.  The fields carry four designations:

* `N`, the **proper donor fields** (the donor cells whose donor label is not `⊤`);
* `T`, the **donor tops** (the donor cells whose donor label is `⊤`);
* `o` and `r`, the **owner** and the **lost top** of the private context.

**Scalars** (`Label.donorMax`, `Label.cutoffCut`, `Label.frontier`).  The **donor maximum**
`M(a)` is the supremum of `a` over `N`; the **cutoff cut** is `R_K(M(a))`, the visibility
replacement of `M(a)` at `K`, self-visible at `K` and at least `M(a)`; the **frontier** is
`e(a) = min (a o) (R_K(a r))`.

**The LOW clause** (`Label.IsLowAt K N T o r β a`): if `M(a) < a β`, every donor top is at least
`max (a β) e(a)`.  It holds at the actual profile (donor labels, private labels, any cutoff),
whose donor tops are `⊤` (`Label.isLowAt_of_forall_top`).

**The partner** (`Label.partner`): lower the cutoff field of `s` to its cutoff cut `h`.  When
`h < s β`, the partner agrees with `s` capped at `h` (`Label.min_partner`), has cutoff `h`
(`Label.partner_cutoff`), and keeps the LOW clause (`Label.IsLowAt.partner`).

**Activation by a strict comparison** (`Label.lt_of_agreementHeight_lt`, compiled in this
repository).  Let `G` be a finite set of labels containing `⊥` and `h`, let `s` have donor maximum
at most `h < s β`, and let `t` agree with `s` capped at `h` with `t β = h`.  For every profile `a`,
if the agreement height of `a` and `t` in `G` is below that of `a` and `s`, then `M(a) < a β`: the
ultrametric inequality (`Label.min_agreementHeight_le`) puts the agreement height of `a` and `s`
above `h`, where `a` and `s` agree on the proper donor fields and on the cutoff.

**The reading of the donor tops** (`Label.eq_top_of_isLowAt`, compiled in this repository).  For
a witness `(g, σ)` with `g K = ⊤`, if the LOW clause is active at `a` and `σ` reads the owner and
the lost top of `a` as `⊤`, then `σ` reads every donor top of `a` as `⊤`: `σ` is monotone and
commutes with the visibility replacement at `K`, so it reads the frontier as `⊤`.  With
activation (`Label.eq_top_of_agreementHeight_lt`): a monotone `σ` reading the agreement height of
`a` and the partner strictly below that of `a` and `s` reads every donor top of `a` as `⊤`.  This
is the per-controller argument of the LOW display: the controller of `a` reads the cell of a
profile `x` at the agreement height of `a` and `x`.

**Anchors** (`Label.lowAnchors`, compiled in this repository).  A witness `(g, σ)` with
`g K = ⊤` maps LOW profiles to LOW profiles (`Label.IsLowAt.map`).  So the normal form
`strongEncode V K ∘ a` of a LOW profile (`VaughtConjecture.Extension.NormalForm`, `V` its set of
values) is a **LOW anchor**: a LOW profile with values in the coded alphabet with block bound
`2 · #X + 1` and offset bound `K + 1`, from which the decoder recovers `a`
(`Label.exists_mem_lowAnchors`).  The LOW anchors with a given block bound are finitely many
(`Label.finite_lowAnchors`): they index the controllers of a LOW layer.  The coding is that of
the normal form; no bound on the values of `a` or on the rows is assumed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

open Finset

variable {X : Type*} (K : ℕ) (N : Finset X) (T : Set X) (o r β : X)

/-! ### Scalars -/

/-- The **donor maximum** of a profile: its supremum over the proper donor fields. -/
noncomputable def donorMax (a : X → Label.{u}) : Label.{u} := N.sup a

/-- The **cutoff cut** of a profile: the visibility replacement of its donor maximum at `K`. -/
noncomputable def cutoffCut (a : X → Label.{u}) : Label.{u} :=
  visibilityReplace K K (donorMax N a)

/-- The **frontier** of a profile: the owner, capped by the visibility replacement of the lost
top at `K`. -/
noncomputable def frontier (a : X → Label.{u}) : Label.{u} :=
  min (a o) (visibilityReplace K K (a r))

/-- The **LOW clause** at `K`: if the donor maximum is below the cutoff, every donor top is at
least the cutoff and the frontier. -/
def IsLowAt (a : X → Label.{u}) : Prop :=
  donorMax N a < a β → ∀ x ∈ T, max (a β) (frontier K o r a) ≤ a x

variable {K N T o r β}

theorem le_donorMax {a : X → Label.{u}} {f : X} (hf : f ∈ N) : a f ≤ donorMax N a :=
  le_sup hf

theorem donorMax_le_cutoffCut (a : X → Label.{u}) : donorMax N a ≤ cutoffCut K N a :=
  le_visibilityReplace (by omega) _

theorem isSelfVisible_cutoffCut (a : X → Label.{u}) : IsSelfVisible K (cutoffCut K N a) :=
  visibilityReplace_self_visibilityReplace le_rfl _

/-- Profiles agreeing on the proper donor fields have the same donor maximum. -/
theorem donorMax_congr {a b : X → Label.{u}} (h : ∀ f ∈ N, a f = b f) :
    donorMax N a = donorMax N b :=
  sup_congr rfl h

/-- **The actual profile is LOW**: if every donor top is `⊤`, the LOW clause holds. -/
theorem isLowAt_of_forall_top {a : X → Label.{u}} (h : ∀ x ∈ T, a x = ⊤) :
    IsLowAt K N T o r β a := fun _ x hx ↦ by
  rw [h x hx]
  exact le_top

/-! ### The partner -/

variable [DecidableEq X]

variable (K N β) in
/-- The **partner** of a profile: its cutoff field lowered to its cutoff cut. -/
noncomputable def partner (s : X → Label.{u}) : X → Label.{u} :=
  Function.update s β (cutoffCut K N s)

/-- The partner has cutoff the cutoff cut. -/
@[simp] theorem partner_cutoff (s : X → Label.{u}) : partner K N β s β = cutoffCut K N s :=
  Function.update_self _ _ _

/-- The partner agrees with the profile off the cutoff field. -/
theorem partner_of_ne (s : X → Label.{u}) {f : X} (hf : f ≠ β) : partner K N β s f = s f :=
  Function.update_of_ne hf _ _

/-- **The partner agrees with the profile capped at the cutoff cut**, when the cutoff is at least
the cutoff cut. -/
theorem min_partner {s : X → Label.{u}} (hs : cutoffCut K N s ≤ s β) (f : X) :
    min (partner K N β s f) (cutoffCut K N s) = min (s f) (cutoffCut K N s) := by
  by_cases hf : f = β
  · subst hf
    rw [partner_cutoff, min_self, min_eq_right hs]
  · rw [partner_of_ne s hf]

/-- **The partner keeps the LOW clause**, when the cutoff field is not a proper donor field: its
donor maximum is that of `s`, at most its cutoff, and when it is below, the donor maximum of `s` is
below the cutoff of `s`, so the donor tops of `s` are at least the cutoff of `s`, above that of the
partner. -/
theorem IsLowAt.partner {s : X → Label.{u}} (hs : IsLowAt K N T o r β s) (hβN : β ∉ N)
    (hβT : β ∉ T) (hβo : β ≠ o) (hβr : β ≠ r) (hlt : cutoffCut K N s < s β) :
    IsLowAt K N T o r β (Label.partner K N β s) := by
  have hM : donorMax N (Label.partner K N β s) = donorMax N s :=
    donorMax_congr fun f hf ↦ partner_of_ne s fun h ↦ hβN (h ▸ hf)
  have hfr : frontier K o r (Label.partner K N β s) = frontier K o r s := by
    unfold frontier
    rw [partner_of_ne s (Ne.symm hβo), partner_of_ne s (Ne.symm hβr)]
  intro _ x hx
  have hxs := hs ((donorMax_le_cutoffCut s).trans_lt hlt) x hx
  have hxβ : x ≠ β := fun h ↦ hβT (h ▸ hx)
  rw [hfr, partner_cutoff, partner_of_ne s hxβ]
  exact max_le (hlt.le.trans (le_max_left _ _) |>.trans hxs) ((le_max_right _ _).trans hxs)

/-! ### Activation by a strict comparison -/

variable [Fintype X] {G : Finset Label.{u}}

omit [DecidableEq X] in
/-- **Activation by a strict comparison of agreement heights.**  Let `⊥, h ∈ G`, let `s` have
donor maximum at most `h < s β`, and let `t` agree with `s` capped at `h` and have cutoff `h`.  If
the agreement height of `a` and `t` is below that of `a` and `s`, then the donor maximum of `a` is
below its cutoff. -/
theorem lt_of_agreementHeight_lt (hG : ⊥ ∈ G) {h : Label.{u}} (hh : h ∈ G)
    {s t a : X → Label.{u}} (hsM : donorMax N s ≤ h) (hsβ : h < s β)
    (hst : ∀ f, min (t f) h = min (s f) h)
    (hlt : agreementHeight G a t < agreementHeight G a s) : donorMax N a < a β := by
  set κ := agreementHeight G a s with hκ
  -- the agreement height of `s` and `t` is at least `h`
  have hst' : h ≤ agreementHeight G s t := le_agreementHeight hh fun f ↦ (hst f).symm
  -- the agreement height of `a` and `s` is above `h`
  have hκh : h < κ := by
    by_contra hle
    have := min_agreementHeight_le hG a s t
    rw [min_eq_left ((not_lt.mp hle).trans hst')] at this
    exact hlt.not_ge this
  have hag := (agreementHeight_spec hG a s).2
  -- `a` is `s` on the proper donor fields
  have hN : ∀ f ∈ N, a f = s f := fun f hf ↦
    eq_of_min_eq_of_lt (hag f).symm (((le_donorMax hf).trans hsM).trans_lt hκh)
  rw [donorMax_congr hN]
  -- the cutoff of `a` is above `h`
  refine hsM.trans_lt (lt_of_not_ge fun hle ↦ ?_)
  have h1 := hag β
  rw [min_eq_left (hle.trans hκh.le)] at h1
  have h2 : h < min (s β) κ := lt_min hsβ hκh
  rw [← h1] at h2
  exact h2.not_ge hle

/-! ### The reading of the donor tops -/

omit [DecidableEq X] [Fintype X] in
/-- **The reading of the donor tops**: for a witness `(g, σ)` with `g K = ⊤`, if the LOW clause
is active at `a` and `σ` reads the owner and the lost top of `a` as `⊤`, then `σ` reads every
donor top of `a` as `⊤`. -/
theorem eq_top_of_isLowAt {a : X → Label.{u}} (hlow : IsLowAt K N T o r β a)
    (hact : donorMax N a < a β) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hσ : IsWitness g σ) (hgK : g K = ⊤) (ho : σ (a o) = ⊤) (hr : σ (a r) = ⊤) :
    ∀ x ∈ T, σ (a x) = ⊤ := by
  intro x hx
  have hfx : frontier K o r a ≤ a x := (le_max_right _ _).trans (hlow hact x hx)
  have hσr : σ (visibilityReplace K K (a r)) = ⊤ := by
    rw [hσ.visibilityReplace_comm (a r) K (by rw [hgK]; exact le_top) K le_rfl, hr,
      visibilityReplace_top]
  have hσf : σ (frontier K o r a) = ⊤ := by
    unfold frontier
    rw [hσ.monotone.map_min, ho, hσr, min_self]
  exact top_le_iff.mp (hσf ▸ hσ.monotone hfx)

omit [DecidableEq X] in
/-- **Activation and reading**: under the hypotheses of `lt_of_agreementHeight_lt`, a witness
`(g, σ)` with `g K = ⊤` reading the agreement height of `a` and `t` strictly below that of `a`
and `s`, and the owner and the lost top of a LOW profile `a` as `⊤`, reads every donor top of
`a` as `⊤`. -/
theorem eq_top_of_agreementHeight_lt (hG : ⊥ ∈ G) {h : Label.{u}} (hh : h ∈ G)
    {s t a : X → Label.{u}} (hsM : donorMax N s ≤ h) (hsβ : h < s β)
    (hst : ∀ f, min (t f) h = min (s f) h) (hlow : IsLowAt K N T o r β a)
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hσ : IsWitness g σ) (hgK : g K = ⊤)
    (hlt : σ (agreementHeight G a t) < σ (agreementHeight G a s))
    (ho : σ (a o) = ⊤) (hr : σ (a r) = ⊤) : ∀ x ∈ T, σ (a x) = ⊤ :=
  eq_top_of_isLowAt hlow (lt_of_agreementHeight_lt hG hh hsM hsβ hst
    (lt_of_not_ge fun hle ↦ hlt.not_ge (hσ.monotone hle))) hσ hgK ho hr

/-- **The partner activates**: `eq_top_of_agreementHeight_lt` with `t` the partner of `s` and `h`
its cutoff cut. -/
theorem eq_top_of_agreementHeight_partner_lt {s a : X → Label.{u}} (hG : ⊥ ∈ G)
    (hh : cutoffCut K N s ∈ G) (hsβ : cutoffCut K N s < s β) (hlow : IsLowAt K N T o r β a)
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hσ : IsWitness g σ) (hgK : g K = ⊤)
    (hlt : σ (agreementHeight G a (partner K N β s)) < σ (agreementHeight G a s))
    (ho : σ (a o) = ⊤) (hr : σ (a r) = ⊤) : ∀ x ∈ T, σ (a x) = ⊤ :=
  eq_top_of_agreementHeight_lt hG hh (donorMax_le_cutoffCut s) hsβ (min_partner hsβ.le) hlow hσ
    hgK hlt ho hr

/-! ### Anchors -/

omit [DecidableEq X] [Fintype X] in
/-- **Witness images of LOW profiles are LOW**: for a witness `(g, σ)` with `g K = ⊤`, if `a` is
LOW so is `σ ∘ a`.  The donor maximum of `σ ∘ a` is attained at a proper donor field or is `⊥`,
so a strict comparison for `σ ∘ a` gives one for `a`; `σ` is monotone and commutes with the
frontier. -/
theorem IsLowAt.map {a : X → Label.{u}} (hlow : IsLowAt K N T o r β a) {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hσ : IsWitness g σ) (hgK : g K = ⊤) :
    IsLowAt K N T o r β (σ ∘ a) := by
  intro hlt x hx
  have hact : donorMax N a < a β := by
    refine lt_of_not_ge fun hle ↦ ?_
    rcases N.eq_empty_or_nonempty with hN | hN
    · rw [donorMax, hN, sup_empty, le_bot_iff] at hle
      rw [Function.comp_apply, hle, hσ.map_bot] at hlt
      exact not_lt_bot hlt
    · obtain ⟨f, hf, hfa⟩ := exists_mem_eq_sup N hN a
      have h1 : σ (a β) ≤ σ (a f) := hσ.monotone (hfa ▸ hle)
      exact hlt.not_ge (h1.trans (le_donorMax (a := σ ∘ a) hf))
  have hfr : frontier K o r (σ ∘ a) = σ (frontier K o r a) := by
    unfold frontier
    rw [hσ.monotone.map_min, Function.comp_apply, Function.comp_apply,
      hσ.visibilityReplace_comm (a r) K (by rw [hgK]; exact le_top) K le_rfl]
  rw [hfr, Function.comp_apply, Function.comp_apply, ← hσ.monotone.map_max]
  exact hσ.monotone (hlow hact x hx)

variable (K N T o r β) in
/-- The **LOW anchors** at `K` with block bound `B`: the LOW profiles with values in the coded
alphabet with block bound `B` and offset bound `K + 1`.  A finite set
(`Label.finite_lowAnchors`). -/
def lowAnchors (B : ℕ) : Set (X → Label.{u}) :=
  {a | IsLowAt K N T o r β a ∧ ∀ f, a f ∈ codedAlphabet B (K + 1)}

omit [DecidableEq X] [Fintype X] in
/-- **The LOW anchors are finitely many.** -/
theorem finite_lowAnchors [Finite X] (B : ℕ) :
    (lowAnchors K N T o r β B : Set (X → Label.{u})).Finite := by
  refine (Set.finite_range fun c : X → (codedAlphabet B (K + 1) : Finset Label.{u}) ↦
    fun f ↦ (c f : Label.{u})).subset fun a ha ↦ ⟨fun f ↦ ⟨a f, ha.2 f⟩, rfl⟩

omit [DecidableEq X] in
/-- **Every LOW profile has a LOW anchor**: its normal form `strongEncode V K ∘ a`, for `V` its
set of values, is a LOW anchor with block bound `2 · #X + 1`, from which the decoder recovers
`a` (`Label.strongDecode_strongEncode`). -/
theorem exists_mem_lowAnchors {a : X → Label.{u}} (hlow : IsLowAt K N T o r β a) :
    ∃ a' ∈ lowAnchors K N T o r β (2 * Fintype.card X + 1),
      ∀ f, strongDecode (univ.image a) K (a' f) = a f := by
  refine ⟨strongEncode (univ.image a) K ∘ a,
    ⟨hlow.map isWitness_strongEncode (stepSuppressor_of_le le_rfl), fun f ↦ ?_⟩,
    fun f ↦ strongDecode_strongEncode (mem_image_of_mem a (mem_univ f))⟩
  have hV : #(univ.image a) ≤ Fintype.card X := card_image_le.trans_eq card_univ
  have h := strongEncode_mem_codedAlphabet (V := univ.image a) (K := K) (a f)
  rw [mem_codedAlphabet] at h ⊢
  rcases h with h | ⟨i, hi, j, hj, h⟩
  · exact .inl h
  · exact .inr ⟨i, by omega, j, hj, h⟩

end VaughtConjecture.Label

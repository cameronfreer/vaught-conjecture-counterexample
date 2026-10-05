/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.PrivateContext

/-!
# Examples for the private context

Special cases of `VaughtConjecture.Realization.PrivateContext`:

* **the empty root**: over an occurrence on no points the literal-face equation holds for every
  embedding, and the private context, also in its anchored form, has arity at least `2`;
* **the anchoring condition of the gated extension**: every non-bottom label of a new donor cell
  (a cell whose scope contains the new point) below the private cap is `vr_n(i, label z)` for
  some cell `z` of the private type and some `i ≤ n`, with no condition on `z`.  It holds for
  every private type and cap when every new donor label is bottom or the formal top; and the
  reference cells of `IsModel.exists_privateContext` give it in general;
* **the stronger form**, with `z` not self-visible at the threshold, labelled at most the cap, and
  `i < n`, also follows from the reference cells of `IsModel.exists_privateContext`;
* **the block of the cutoff**: the cutoff `ω + 1` lies in the block of the donor label `ω + 3`.  At
  the threshold `n = 4` the reference cell labelled `ω` gives the donor label, and the actual cut
  of the block, `ω + 4`, lies above the cutoff, so no separate reference cell for the block of the
  cutoff is used;
* **the smallest case** `m = 0`, `n = 2`: `vr_2(1, ω) = ω + 1` and `vr_2(2, ω + 1) = ω + 2`;
* **padding is needed**: a cell whose finite part is at least the threshold is self-visible and is
  fixed, `vr_2(1, ω + 5) = ω + 5 ≠ ω + 1`;
* **the finite part `k = n` gives no reference cell**: `vr_n(i, μ + n) = μ + n` for every value `i`;
* **full grade means full scope** on a member of a dominance family.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Realization

open Finset Label StageType
open scoped Ordinal

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-! ### The empty root -/

/-- Over the empty root the literal-face equation is automatic. -/
example (x : R.Occurrence) (hx : x.arity = 0) (y : R.Occurrence)
    (f : Fin x.arity ↪ Fin y.arity) : f.trans y.tuple = x.tuple := by
  ext i
  exact (Fin.cast hx i).elim0

/-- **The empty root**: a model at a positive stage has an occurrence on no points, and over it a
private context of arity at least `2` with a private cap above any `γ < α`. -/
example (hR : R.IsModel) {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ (x y : R.Occurrence) (C : Fin y.type.card), x.arity = 0 ∧ 2 ≤ y.arity ∧
      y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧ (γ : Label.{u}) < y.type.label C := by
  obtain ⟨x, hx⟩ := hR.exists_arity_eq (zero_le.trans_lt hγ) 0
  obtain ⟨-, -, d, -, -⟩ := hR.dominance x γ hγ
  obtain ⟨y, -, C, -, hy, -, hC, hγC, -⟩ := hR.exists_privateContext x d hγ 0
  exact ⟨x, y, C, hx, by omega, hC, hγC⟩

/-- **The empty root, anchored**: over an occurrence on no points, the anchored private context
(`IsModel.exists_privateContext_isAnchored`) has arity at least `2`. -/
example (hR : R.IsModel) (x : R.Occurrence) (hx : x.arity = 0) (d : StageType.{u} α (x.arity + 1))
    {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ (y : R.Occurrence) (C : Fin y.type.card), 2 ≤ y.arity ∧ IsAnchored y.type C d := by
  obtain ⟨y, -, C, -, -, hn, -, -, hanc⟩ := hR.exists_privateContext_isAnchored x d hγ
  exact ⟨y, C, by omega, hanc⟩

/-! ### The anchoring condition of the gated extension -/

section Anchoring

variable {n m : ℕ} (P : StageType.{u} α n) (C : Fin P.card) (d : StageType.{u} α (m + 1))

/-- **Donors without proper new labels**: if every label of a new cell of the donor (a cell whose
scope contains the new point) is bottom or the formal top, the anchoring condition of the gated
extension holds for every private type `P` and cell `C`, vacuously. -/
example (hd : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j = ⊥ ∨ d.label j = ⊤) :
    ∀ j : Fin d.card, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
      d.label j < P.label C →
        ∃ z : Fin P.card, ∃ i ≤ n, d.label j = visibilityReplace n i (P.label z) := by
  intro j hj hbot hlt
  rcases hd j hj with h | h
  · exact absurd h hbot
  · exact absurd (h ▸ hlt) not_top_lt

/-- **The reference cells give the anchoring condition**: the conclusion of
`IsModel.exists_privateContext` about proper donor labels (a cell `z` and `i < n`) gives the
anchoring condition of the gated extension (`i ≤ n`, no condition on `z`); a non-bottom label
below the cap is not the formal top, hence proper. -/
example (h : ∀ (j : Fin d.card) (o : Ordinal.{u}), d.label j = o →
      ∃ z, ∃ i < n, d.label j = visibilityReplace n i (P.label z) ∧
        ¬ IsSelfVisible n (P.label z) ∧ P.label z < P.label C) :
    ∀ j : Fin d.card, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
      d.label j < P.label C →
        ∃ z : Fin P.card, ∃ i ≤ n, d.label j = visibilityReplace n i (P.label z) := by
  intro j _ hbot hlt
  induction hj : d.label j using recBotCoeTop with
  | bot => exact absurd hj hbot
  | coe o =>
    obtain ⟨z, i, hi, he, -, -⟩ := h j o hj
    exact ⟨z, i, hi.le, hj ▸ he⟩
  | top => exact absurd (hj ▸ hlt) not_top_lt

/-- **The stronger form**: the same reference cells give, for every non-bottom new donor label
below the cap, a cell `z` that is not self-visible at the threshold and is labelled at most the
cap, with `i < n`. -/
example (h : ∀ (j : Fin d.card) (o : Ordinal.{u}), d.label j = o →
      ∃ z, ∃ i < n, d.label j = visibilityReplace n i (P.label z) ∧
        ¬ IsSelfVisible n (P.label z) ∧ P.label z < P.label C) :
    ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
      ∃ z, ¬ IsSelfVisible n (P.label z) ∧ P.label z ≤ P.label C ∧
        ∃ i < n, d.label j = visibilityReplace n i (P.label z) := by
  intro j _ hbot hlt
  induction hj : d.label j using recBotCoeTop with
  | bot => exact absurd hj hbot
  | coe o =>
    obtain ⟨z, i, hi, he, hsv, hzC⟩ := h j o hj
    exact ⟨z, hsv, hzC.le, i, hi, hj ▸ he⟩
  | top => exact absurd (hj ▸ hlt) not_top_lt

end Anchoring

/-! ### Block arithmetic -/

/-- `ω` is a limit, so its block is `[ω, ω + ω)`. -/
private theorem isSuccPrelimit_omega0 : Order.IsSuccPrelimit (ω : Ordinal.{u}) :=
  Ordinal.isSuccLimit_omega0.isSuccPrelimit

/-- **The block of the cutoff**: the cutoff `ω + 1` lies in the block `[ω, ω + ω)` of the donor
label `ω + 3`.  At the threshold `4` the reference cell labelled `ω` (finite part `0 < 4`) gives
the donor label, `vr_4(3, ω) = ω + 3`, and is not self-visible; the actual cut of the block,
`vr_4(4, ω) = ω + 4`, lies above the cutoff.  So the reference cell of the donor's block also
serves the cutoff, and no separate reference cell for the block of the cutoff is used. -/
example : visibilityReplace 4 3 ((ω : Ordinal.{u}) : Label.{u}) = ((ω + 3 : Ordinal.{u}) : Label) ∧
    ¬ IsSelfVisible 4 ((ω : Ordinal.{u}) : Label.{u}) ∧
    ((ω + 1 : Ordinal.{u}) : Label.{u}) < visibilityReplace 4 4 ((ω : Ordinal.{u}) : Label) := by
  have h3 := visibilityReplace_coe_add_natCast (n := 4) (k := 0) isSuccPrelimit_omega0
    (by omega) 3
  have h4 := visibilityReplace_coe_add_natCast (n := 4) (k := 0) isSuccPrelimit_omega0
    (by omega) 4
  have hsv := not_isSelfVisible_coe_add_natCast (n := 4) (k := 0) isSuccPrelimit_omega0
    (by omega)
  simp only [Nat.cast_zero, add_zero, Nat.cast_ofNat] at h3 h4 hsv
  refine ⟨h3, hsv, ?_⟩
  rw [h4]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left ω).mpr (by exact_mod_cast (by omega : 1 < 4))))

/-- **The smallest case**, root on `m = 0` points and threshold `n = 2`: `vr_2(1, ω) = ω + 1`, and
the actual cut of the block of `ω + 1` is `vr_2(2, ω + 1) = ω + 2`. -/
example : visibilityReplace 2 1 ((ω : Ordinal.{u}) : Label.{u}) = ((ω + 1 : Ordinal.{u}) : Label) ∧
    visibilityReplace 2 2 ((ω + 1 : Ordinal.{u}) : Label.{u}) =
      ((ω + 2 : Ordinal.{u}) : Label) := by
  have h1 := visibilityReplace_coe_add_natCast (n := 2) (k := 0) isSuccPrelimit_omega0
    (by omega) 1
  have h2 := visibilityReplace_coe_add_natCast (n := 2) (k := 1) isSuccPrelimit_omega0
    (by omega) 2
  simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- **Padding is needed**: at the threshold `2` the label `ω + 5` is self-visible, so it is fixed by
visibility replacement and gives no reference cell for the donor label `ω + 1`. -/
example : visibilityReplace 2 1 ((ω + 5 : Ordinal.{u}) : Label.{u}) =
      ((ω + 5 : Ordinal.{u}) : Label) ∧
    visibilityReplace 2 1 ((ω + 5 : Ordinal.{u}) : Label.{u}) ≠
      ((ω + 1 : Ordinal.{u}) : Label) := by
  have h : visibilityReplace 2 1 ((ω + 5 : Ordinal.{u}) : Label.{u}) =
      ((ω + 5 : Ordinal.{u}) : Label) := by
    simpa using (isSelfVisible_coe_add (K := 5) isSuccPrelimit_omega0 (k := 2)
      (by omega)).visibilityReplace_eq 1
  refine ⟨h, fun h' ↦ ?_⟩
  have h51 : (ω + 5 : Ordinal.{u}) = ω + 1 :=
    WithTop.coe_injective (WithBot.coe_injective (h.symm.trans h'))
  simp at h51

/-- **The finite part `k = n` gives no reference cell**: `μ + n` is self-visible at the threshold
`n`, so every replacement at `n` fixes it. -/
example {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (n i : ℕ) :
    visibilityReplace n i ((μ + n : Ordinal.{u}) : Label.{u}) = ((μ + n : Ordinal.{u}) : Label) :=
  (isSelfVisible_coe_add hμ le_rfl).visibilityReplace_eq i

/-! ### Full grade means full scope -/

/-- **Full grade means full scope** on a dominance member: the cell of grade `n + 1` labelled above
`γ` has graded index `(univ, n + 1)`. -/
example {n : ℕ} {γ : Ordinal.{u}} {q : StageType.{u} α (n + 1)} (hq : q ∈ dominanceFamily γ) :
    ∃ C, q.toCellScheme.gradedIndex C = (univ, n + 1) ∧ (γ : Label.{u}) < q.label C := by
  obtain ⟨C, hC, hγC⟩ := hq
  exact ⟨C, q.gradedIndex_eq_univ_of_grade_eq hC, hγC⟩

end VaughtConjecture.Realization

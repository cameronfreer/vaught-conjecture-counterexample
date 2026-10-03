/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.WitnessAlgebra
import VaughtConjecture.Scheme.Row

/-!
# Positive-cap transport of lawfulness

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (owner alignment: the transport of lawfulness through
a decoder that agrees with a lawful labelling at a positive cap); Layer 1 (guarded composition
retains its guards); semantic contract, item 3.

A witness `ν` bounded by grade `K` (a value map with `IsWitness (stepSuppressor K) ν`: the guard
is vacuous at the grades `≤ K`, whatever the values of `ν`) need not send lawful sections to
lawful sections, because it may send a label that is not bottom to bottom
(`VaughtConjecture.Extension.TransformationExamples`: the rows `(1, 1)`, `(1, 2)` and the section
`(1, ω * 5 + 1)` decode to `(⊥, ⊤)`).  The statements here show that the **bottom pattern** is the
only obstruction: if `ν ∘ r` is bottom exactly where some lawful labelling `q` is bottom (a
**lawful companion**), then `ν ∘ r` is lawful; conversely, a lawful `ν ∘ r` is its own companion
(`CellScheme.Rows.isLawful_comp_iff_exists_bot_iff`).  Agreement of `ν ∘ r` with a lawful `q`
capped at a label `γ ≠ ⊥` gives the same bottom pattern, hence the **positive-cap transport**
(`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`); at `γ = ⊥` the agreement is automatic and the
conclusion can fail (`VaughtConjecture.Extension.FlatteningExamples`).  When `ν` sends no
non-bottom value of `r` to bottom, `r` is its own companion
(`CellScheme.Rows.IsLawful.map_of_apply_eq_bot`), which generalizes the transport through a
witness that reflects bottom everywhere (`CellScheme.Rows.IsLawful.map_of_bot_reflecting`).

* **The zero set of a witness** (`Label.IsWitness.apply_visibilityReplace_eq_bot`): the labels a
  shifter sends to bottom form a lower set closed under every visibility replacement, at every
  threshold, since the guard `σ x ≤ g k` holds at such a label.
* **Witness interpolation** (`Label.exists_isWitness_interpolation`).  Let `f` be monotone, fix
  bottom, and commute with visibility replacement at every threshold `≤ m` (such as the composite
  `ν ∘ τ` of witnesses bounded by grades `K ≥ m` and `m`, which may fail the guard above `m`).
  Let `S` be a lower set of labels closed under every visibility replacement.  Then some witness
  `ρ` bounded by grade `m` is bottom on `S` and equals `f` at every label outside `S` that `f`
  does not send to bottom.  The interpolant is bottom on `S` and on the blocks that `f` sends
  entirely to bottom; elsewhere it is the maximum of `f` and the finite part of the label capped
  at `m`, which is at most `f` wherever `f` is not bottom and keeps the interpolant away from
  bottom in a block that `f` sends to bottom only in part.
* **Mapped locality with a lawful companion** (`Label.TransformsTo.map_of_bot_iff`).  For a cell
  `c` of maximal grade, if `E ⇒ (d ↦ min (p d) (p c))` and `E ⇒ (d ↦ min (q d) (q c))` with
  labels at `c` self-visible at its grade, and `ν (p d) = ⊥ ↔ q d = ⊥`, then
  `E ⇒ (d ↦ min (ν (p d)) (ν (p c)))`: interpolate `ν ∘ τ` (`τ` the capped witness of `p`) off the
  zero set of the capped witness of `q`.
* **Transport of lawfulness** (`CellScheme.Rows.IsLawful.map_of_bot_iff`,
  `CellScheme.Rows.IsLawful.map_of_min_eq`, `CellScheme.Rows.IsLawful.map_of_apply_eq_bot`, and
  their forms below a pair).

The hypothesis `γ ≠ ⊥` is the only condition on the cap: `γ` need not be self-visible, and only the
grades of the cells below the pair, at most `K`, enter.  The application is to the owner
alignment of the completion (`VaughtConjecture.Extension.OwnerCappedLift`): there, a labelling `r`
lawful below the target pair of a lift, extending the aligned encoding, is decoded by the alignment
decoder `ν`, and the decoded labelling `ν ∘ r`, agreeing at the positive cap of the lift with the
lawful ambient labelling, is lawful by the transport here
(`CellScheme.Rows.hasOwnerCappedLifts_of_source`).  The cap `⊥` is treated separately, by the
boundary lift of the prescription capped at the owner label
(`CellScheme.Rows.hasOwnerCappedLifts_bot_of_boundary`).

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Witnesses are [Kni26, Definition 2.3.9] and visibility replacement is [Kni26, Definition 2.2.3];
lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {f σ ν : Label.{u} → Label.{u}} {g : ℕ → Label.{u}} {m n k i N M K : ℕ}
  {x y γ : Label.{u}}

/-! ### Replacement rules -/

/-- Replacing at a threshold `M ≥ k` with value `M` forgets an earlier replacement at `k` with a
value `i ≤ k`. -/
theorem _root_.Ordinal.visibilityReplace_self_visibilityReplace_of_le (hi : i ≤ k) (hkM : k ≤ M)
    (o : Ordinal.{u}) :
    Ordinal.visibilityReplace M M (Ordinal.visibilityReplace k i o) =
      Ordinal.visibilityReplace M M o := by
  have hik : (i : Ordinal.{u}) ≤ k := by exact_mod_cast hi
  have hkM' : (k : Ordinal.{u}) ≤ M := by exact_mod_cast hkM
  conv_lhs => rw [Ordinal.visibilityReplace, Ordinal.visibilityReplace_div,
    Ordinal.visibilityReplace_mod]
  rw [Ordinal.visibilityReplace]
  by_cases hm : o % ω < k
  · rw [ite_eq_left hm, ite_eq_left (hm.trans_le hkM')]
    by_cases hiM : (i : Ordinal.{u}) < M
    · rw [ite_eq_left hiM]
    · rw [ite_eq_right hiM, le_antisymm (hik.trans hkM') (not_lt.mp hiM)]
  · rw [ite_eq_right hm]

/-- Replacing at a threshold `M ≥ k` with value `M` forgets an earlier replacement at `k` with a
value `i ≤ k`. -/
theorem visibilityReplace_self_visibilityReplace_of_le (hi : i ≤ k) (hkM : k ≤ M)
    (x : Label.{u}) :
    visibilityReplace M M (visibilityReplace k i x) = visibilityReplace M M x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => simp [Ordinal.visibilityReplace_self_visibilityReplace_of_le hi hkM]
  | top => rfl

/-- A replacement at threshold `M` with value `M` is self-visible at `M`. -/
theorem isSelfVisible_visibilityReplace_self (M : ℕ) (x : Label.{u}) :
    IsSelfVisible M (visibilityReplace M M x) :=
  visibilityReplace_self_visibilityReplace le_rfl x

/-- A label that is not bottom and is self-visible at `n` is at least the ordinal `n`. -/
theorem natCast_le_of_isSelfVisible (h : IsSelfVisible n y) (hy : y ≠ ⊥) :
    ((n : Ordinal.{u}) : Label.{u}) ≤ y := by
  induction y using recBotCoeTop with
  | bot => exact absurd rfl hy
  | coe o => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      ((isSelfVisible_coe.mp h).trans (Ordinal.mod_le o ω)))
  | top => exact le_top

/-- **The zero set of a shifter is closed under every visibility replacement**, at every
threshold: at a label sent to bottom the guard holds. -/
theorem IsWitness.apply_visibilityReplace_eq_bot (hw : IsWitness g σ) (hx : σ x = ⊥) (k : ℕ)
    (hi : i ≤ k) : σ (visibilityReplace k i x) = ⊥ := by
  rw [hw.visibilityReplace_comm x k (hx ▸ bot_le) i hi, hx, visibilityReplace_bot]

/-- A map commuting with the replacements at the thresholds `≤ m` keeps self-visibility at every
threshold `n ≤ m`. -/
private theorem isSelfVisible_apply
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x))
    (hn : n ≤ m) (hx : IsSelfVisible n x) : IsSelfVisible n (f x) := by
  have h := hcomm x n hn n le_rfl
  rw [hx] at h
  exact h.symm

/-! ### The finite part capped at a grade -/

/-- The finite part of a label capped at `m`, as an ordinal label: bottom for bottom, the ordinal
`min (o % ω) m` for an ordinal `o`, and `m` for the formal top.  It is the lower bound that keeps
the interpolant of `exists_isWitness_interpolation` away from bottom. -/
private noncomputable def finitePartCap (m : ℕ) : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (fun o ↦ ((min (o % ω) (m : Ordinal.{u}) : Ordinal.{u}) : Label.{u}))
    ((m : Ordinal.{u}) : Label.{u})

private theorem finitePartCap_bot : finitePartCap m (⊥ : Label.{u}) = ⊥ := rfl

private theorem finitePartCap_top : finitePartCap m (⊤ : Label.{u}) = ((m : Ordinal.{u}) : Label) :=
  rfl

private theorem finitePartCap_coe (o : Ordinal.{u}) :
    finitePartCap m (o : Label.{u}) = ((min (o % ω) (m : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) :=
  rfl

/-- The finite part of an ordinal is a natural number. -/
private theorem exists_mod_eq (o : Ordinal.{u}) : ∃ n : ℕ, o % ω = n :=
  lt_omega0.mp (mod_lt o omega0_ne_zero)

private theorem finitePartCap_ne_bot (hx : x ≠ ⊥) : finitePartCap m x ≠ ⊥ := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | coe o => simp [finitePartCap_coe]
  | top => simp [finitePartCap_top]

private theorem finitePartCap_le (m : ℕ) (x : Label.{u}) :
    finitePartCap m x ≤ ((m : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | coe o => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (min_le_right _ _))
  | top => exact le_rfl

/-- The finite part capped at `m` commutes with visibility replacement at the thresholds `≤ m`. -/
private theorem finitePartCap_visibilityReplace (hk : k ≤ m) (hi : i ≤ k) (x : Label.{u}) :
    finitePartCap m (visibilityReplace k i x) = visibilityReplace k i (finitePartCap m x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o =>
    obtain ⟨n, hn⟩ := exists_mod_eq o
    rw [visibilityReplace_coe, finitePartCap_coe, finitePartCap_coe, visibilityReplace_coe,
      Ordinal.visibilityReplace_mod, hn, ← Nat.mono_cast.map_min, Ordinal.visibilityReplace_natCast]
    by_cases hnk : n < k
    · have : min n m < k := (min_le_left n m).trans_lt hnk
      simp only [Nat.cast_lt, hnk, this, ↓reduceIte, ← Nat.mono_cast.map_min,
        min_eq_left (hi.trans hk)]
    · have : ¬ min n m < k := by omega
      simp only [Nat.cast_lt, hnk, this, ↓reduceIte, ← Nat.mono_cast.map_min]
  | top =>
    rw [visibilityReplace_top, finitePartCap_top, visibilityReplace_coe,
      Ordinal.visibilityReplace_natCast, ite_eq_right (by omega)]

/-- **The finite part capped at `m` lies below a map commuting with the replacements at the
thresholds `≤ m`** at every label that the map does not send to bottom: such a value is
self-visible at the capped finite part. -/
private theorem finitePartCap_le_apply
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x))
    (hx : f x ≠ ⊥) : finitePartCap m x ≤ f x := by
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | coe o =>
    obtain ⟨n, hn⟩ := exists_mod_eq o
    rw [finitePartCap_coe, hn, ← Nat.mono_cast.map_min]
    refine natCast_le_of_isSelfVisible (isSelfVisible_apply hcomm (min_le_right n m) ?_) hx
    exact isSelfVisible_coe.mpr (by rw [hn]; exact_mod_cast min_le_left n m)
  | top =>
    rw [finitePartCap_top]
    exact natCast_le_of_isSelfVisible (isSelfVisible_apply hcomm le_rfl (isSelfVisible_top m)) hx

/-- In one block, the finite part capped at `m` is monotone: `x ≤ y ≤ vr M M x`. -/
private theorem finitePartCap_mono_of_le_visibilityReplace (hxy : x ≤ y)
    (hy : y ≤ visibilityReplace M M x) : finitePartCap m x ≤ finitePartCap m y := by
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top => rw [top_le_iff.mp hxy]
  | coe o =>
    induction y using recBotCoeTop with
    | bot => exact absurd hxy (not_le.mpr (WithBot.bot_lt_coe _))
    | top => exact absurd hy (by simp [visibilityReplace_coe])
    | coe o' =>
      have h₁ : o ≤ o' := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hxy)
      have h₂ : o' ≤ Ordinal.visibilityReplace M M o := by
        rw [visibilityReplace_coe] at hy
        exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hy)
      have hdiv : o / ω = o' / ω := by
        refine le_antisymm (Ordinal.div_le_left h₁ ω) (Order.lt_succ_iff.mp ?_)
        rw [← lt_mul_iff_div_lt omega0_ne_zero, Ordinal.mul_succ]
        exact h₂.trans_lt (Ordinal.visibilityReplace_lt M M o)
      rw [finitePartCap_coe, finitePartCap_coe]
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (min_le_min_right _ (mod_le_mod_of_div_eq h₁ hdiv)))

/-! ### Witness interpolation -/

/-- The labels sent to bottom by the interpolant: those of `S`, and those whose replacements
`vr N N x`, for every `N`, are sent to bottom by `f` (the blocks that `f` sends entirely to
bottom). -/
private def IsInterpolantZero (f : Label.{u} → Label.{u}) (S : Set Label.{u}) (x : Label.{u}) :
    Prop :=
  x ∈ S ∨ ∀ N : ℕ, f (visibilityReplace N N x) = ⊥

open Classical in
/-- The interpolant of `exists_isWitness_interpolation`. -/
private noncomputable def interpolant (f : Label.{u} → Label.{u}) (S : Set Label.{u}) (m : ℕ)
    (x : Label.{u}) : Label.{u} :=
  if IsInterpolantZero f S x then ⊥ else max (f x) (finitePartCap m x)

/-- **Witness interpolation.**  Let `f` fix bottom, be monotone, and commute with visibility
replacement at every threshold `≤ m`, and let `S` be a lower set of labels closed under every
visibility replacement.  Then some witness `ρ` bounded by grade `m` is bottom on `S` and equals
`f` at every label outside `S` that `f` does not send to bottom.  It repairs the guard of a
composite of witnesses above `m` without bottom reflection, when the labels it must send to
bottom form such a set `S` (`TransformsTo.map_of_bot_iff`). -/
theorem exists_isWitness_interpolation (hbot : f ⊥ = ⊥) (hmono : Monotone f)
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x))
    {S : Set Label.{u}} (hdown : ∀ ⦃x y : Label.{u}⦄, x ≤ y → y ∈ S → x ∈ S)
    (hvr : ∀ x ∈ S, ∀ k, ∀ i ≤ k, visibilityReplace k i x ∈ S) :
    ∃ ρ, IsWitness (stepSuppressor.{u} m) ρ ∧ (∀ x ∈ S, ρ x = ⊥) ∧
      ∀ x ∉ S, f x ≠ ⊥ → ρ x = f x := by
  classical
  set Z := IsInterpolantZero f S
  -- The zero set is a lower set closed under every replacement, and reflected by them.
  have hZdown {x y : Label.{u}} (hxy : x ≤ y) (hy : Z y) : Z x := by
    rcases (hy : y ∈ S ∨ ∀ N : ℕ, f (visibilityReplace N N y) = ⊥) with h | h
    · exact Or.inl (hdown hxy h)
    · exact Or.inr fun N ↦ le_bot_iff.mp ((h N) ▸ hmono (monotone_visibilityReplace le_rfl hxy))
  have hZvr {x : Label.{u}} (hx : Z x) (k : ℕ) {i : ℕ} (hi : i ≤ k) :
      Z (visibilityReplace k i x) := by
    rcases (hx : x ∈ S ∨ ∀ N : ℕ, f (visibilityReplace N N x) = ⊥) with h | h
    · exact Or.inl (hvr x h k i hi)
    refine Or.inr fun N ↦ le_bot_iff.mp ?_
    have hM : IsSelfVisible N (visibilityReplace (max N k) (max N k) x) :=
      (isSelfVisible_visibilityReplace_self _ x).mono (le_max_left N k)
    calc f (visibilityReplace N N (visibilityReplace k i x))
        ≤ f (visibilityReplace N N (visibilityReplace (max N k) (max N k)
            (visibilityReplace k i x))) :=
          hmono (monotone_visibilityReplace le_rfl (le_visibilityReplace (by omega) _))
      _ = f (visibilityReplace (max N k) (max N k) x) := by
          rw [visibilityReplace_self_visibilityReplace_of_le hi (le_max_right N k),
            hM.visibilityReplace_eq]
      _ = ⊥ := h _
  have hZback {x : Label.{u}} {k i : ℕ} (hi : i ≤ k) (hx : Z (visibilityReplace k i x)) :
      Z x := by
    have h := hZvr hx k le_rfl
    rw [visibilityReplace_self_visibilityReplace hi] at h
    exact hZdown (le_visibilityReplace (by omega) x) h
  have hZbot : Z ⊥ := Or.inr fun N ↦ by rw [visibilityReplace_bot, hbot]
  have hρZ {x : Label.{u}} (hx : Z x) : interpolant f S m x = ⊥ := ite_eq_left hx
  have hρnZ {x : Label.{u}} (hx : ¬ Z x) :
      interpolant f S m x = max (f x) (finitePartCap m x) := ite_eq_right hx
  have hρne {x : Label.{u}} (hx : ¬ Z x) : interpolant f S m x ≠ ⊥ := by
    rw [hρnZ hx]
    exact ne_bot_of_le_ne_bot (finitePartCap_ne_bot fun (h : x = ⊥) ↦ hx (h ▸ hZbot))
      (le_max_right _ _)
  refine ⟨interpolant f S m, ⟨(IsWitness.id_step m).antitone, (IsWitness.id_step m).isSelfVisible,
    hρZ hZbot, fun x y hxy ↦ ?_, fun x k hx i hi ↦ ?_⟩, fun x hx ↦ hρZ (.inl hx),
    fun x hxS hfx ↦ ?_⟩
  · -- Monotonicity.
    by_cases hy : Z y
    · rw [hρZ (hZdown hxy hy)]
      exact bot_le
    by_cases hx : Z x
    · rw [hρZ hx]
      exact bot_le
    rw [hρnZ hx, hρnZ hy]
    refine max_le (le_max_of_le_left (hmono hxy)) ?_
    obtain ⟨N, hN⟩ : ∃ N, f (visibilityReplace N N x) ≠ ⊥ := by
      by_contra h
      exact hx (Or.inr fun N ↦ by_contra fun hN ↦ h ⟨N, hN⟩)
    set M := max N m
    set z := visibilityReplace M M x
    have hz : f z ≠ ⊥ := ne_bot_of_le_ne_bot hN (hmono (by
      calc visibilityReplace N N x ≤ visibilityReplace M M (visibilityReplace N N x) :=
            le_visibilityReplace (by omega) _
        _ = z := visibilityReplace_self_visibilityReplace_of_le le_rfl (le_max_left N m) x))
    rcases le_or_gt z y with hzy | hyz
    · refine le_max_of_le_left ((finitePartCap_le m x).trans ?_)
      refine (natCast_le_of_isSelfVisible (isSelfVisible_apply hcomm le_rfl ?_) hz).trans
        (hmono hzy)
      exact (isSelfVisible_visibilityReplace_self M x).mono (le_max_right N m)
    · exact le_max_of_le_right (finitePartCap_mono_of_le_visibilityReplace hxy hyz.le)
  · -- Commutation with visibility replacement, and the guard above `m`.
    by_cases hk : k ≤ m
    · by_cases hZ : Z x
      · rw [hρZ hZ, hρZ (hZvr hZ k hi), visibilityReplace_bot]
      · rw [hρnZ hZ, hρnZ fun h ↦ hZ (hZback hi h), hcomm x k hk i hi,
          finitePartCap_visibilityReplace hk hi, visibilityReplace_max hi]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hZ : Z x := by
        by_contra h
        exact hρne h hx
      rw [hρZ hZ, hρZ (hZvr hZ k hi), visibilityReplace_bot]
  · -- Agreement with `f` off `S` where `f` is not bottom.
    have hZ : ¬ Z x := by
      rintro (h | h : x ∈ S ∨ ∀ N : ℕ, f (visibilityReplace N N x) = ⊥)
      · exact hxS h
      · exact hfx (le_bot_iff.mp ((h 0) ▸ hmono (le_visibilityReplace (by omega) x)))
    rw [hρnZ hZ, max_eq_left (finitePartCap_le_apply hcomm hfx)]

/-! ### Mapped locality with a lawful companion -/

variable {D : Type*} {grade : D → ℕ}

/-- **Mapped locality with a lawful companion.**  Let `c` be a cell of maximal grade, at most `K`,
let `E ⇒ (d ↦ min (p d) (p c))` and `E ⇒ (d ↦ min (q d) (q c))` with `p c` and `q c` self-visible
at the grade of `c`, and let `ν` be a witness bounded by grade `K` that sends `p d` to bottom
exactly when `q d` is bottom.  Then `E ⇒ (d ↦ min (ν (p d)) (ν (p c)))`.  No bottom reflection of
`ν` and no shortness of `E` is assumed.  It proves the locality in the transport of lawfulness
(`CellScheme.Rows.IsLawful.map_of_bot_iff`). -/
theorem TransformsTo.map_of_bot_iff {E p q : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K)
    (hvis : IsSelfVisible (grade c) (p c)) (hloc : TransformsTo grade E fun d ↦ min (p d) (p c))
    (hvisq : IsSelfVisible (grade c) (q c))
    (hlocq : TransformsTo grade E fun d ↦ min (q d) (q c))
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ d, ν (p d) = ⊥ ↔ q d = ⊥) :
    TransformsTo grade E fun d ↦ min (ν (p d)) (ν (p c)) := by
  obtain ⟨τ, hτ, -, hcap⟩ := hloc.exists_isWitness_capped hmax hvis
  obtain ⟨τq, hτq, -, hcapq⟩ := hlocq.exists_isWitness_capped hmax hvisq
  have hcomm : ∀ x, ∀ k ≤ grade c, ∀ i ≤ k,
      (ν ∘ τ) (visibilityReplace k i x) = visibilityReplace k i ((ν ∘ τ) x) := by
    intro x k hk i hi
    simp only [Function.comp_apply]
    rw [hτ.visibilityReplace_comm x k (by simp [hk]) i hi,
      hν.visibilityReplace_comm _ k (by simp [hk.trans hcK]) i hi]
  obtain ⟨ρ, hρ, hS, hf⟩ := exists_isWitness_interpolation (f := ν ∘ τ) (m := grade c)
    (S := {x | τq x = ⊥}) (by simp [hτ.map_bot, hν.map_bot]) (hν.monotone.comp hτ.monotone)
    hcomm (fun x y hxy hy ↦ le_bot_iff.mp ((show τq y = ⊥ from hy) ▸ hτq.monotone hxy))
    (fun x hx k i hi ↦ hτq.apply_visibilityReplace_eq_bot hx k hi)
  refine ⟨_, ρ, hρ, fun d ↦ ?_⟩
  -- Beta-reduce the target and expose the step suppressor at the grade of `d`.
  change min (ν (p d)) (ν (p c)) = min (ρ (E d)) (stepSuppressor (grade c) (grade d))
  rw [stepSuppressor_of_le (hmax d), min_top_right]
  by_cases hd : τq (E d) = ⊥
  · rw [hS _ hd]
    rw [hcapq, min_eq_bot] at hd
    rcases hd with h | h
    · rw [(hbot d).mpr h, min_eq_left bot_le]
    · rw [(hbot c).mpr h, min_eq_right bot_le]
  · have hne : (ν ∘ τ) (E d) ≠ ⊥ := by
      rw [hcapq, min_eq_bot, not_or] at hd
      rw [Function.comp_apply, hcap, hν.monotone.map_min, Ne, min_eq_bot, not_or,
        hbot d, hbot c]
      exact hd
    rw [hf _ hd hne, Function.comp_apply, hcap, hν.monotone.map_min]

/-- Two labels that agree capped at a label `γ ≠ ⊥` are bottom together. -/
theorem eq_bot_iff_of_min_eq (h : min x γ = min y γ) (hγ : γ ≠ ⊥) : x = ⊥ ↔ y = ⊥ := by
  have key : ∀ z, z = ⊥ ↔ min z γ = ⊥ := fun z ↦ by rw [min_eq_bot, or_iff_left hγ]
  rw [key x, key y, h]

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {K : ℕ}
  {ν : Label.{u} → Label.{u}} {γ : Label.{u}}

namespace IsLawful

variable {r q : ι → Label.{u}}

/-- **Transport of lawfulness through a witness with a lawful companion.**  Let `r` and `q` be
lawful, the grades at most `K`, and `ν` a witness bounded by grade `K` that sends `r d` to bottom
exactly when `q d` is bottom.  Then `ν ∘ r` is lawful.  It proves the positive-cap transport
(`IsLawful.map_of_min_eq`), by which a labelling of codes is to decode to a lawful lift in the
owner alignment of the completion, which is not constructed here. -/
theorem map_of_bot_iff (hr : R.IsLawful r) (hq : R.IsLawful q) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ d, ν (r d) = ⊥ ↔ q d = ⊥) :
    R.IsLawful (ν ∘ r) where
  orderly d := hν.isSelfVisible_apply (hr.orderly d) (by simp [hK d])
  locality s := TransformsTo.map_of_bot_iff
    (grade := fun d : D.below (D.gradedIndex s) ↦ D.grade d) (E := R.row s)
    (p := fun d ↦ r d) (q := fun d ↦ q d) (c := ⟨s, D.mem_below_gradedIndex s⟩)
    (fun d ↦ d.2.2) (hK s) (hr.orderly s) (hr.locality s) (hq.orderly s) (hq.locality s) hν
    fun d ↦ hbot d
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hr.availability s t hst hg
    exact ⟨u, hu, hν.monotone hle⟩

/-- **Positive-cap transport of lawfulness.**  Let `r` and `q` be lawful, the grades at most `K`,
`ν` a witness bounded by grade `K`, and `γ ≠ ⊥` a label at which `ν ∘ r` agrees with `q` capped:
`min (ν (r d)) γ = min (q d) γ`.  Then `ν ∘ r` is lawful.  The cap need not be self-visible. -/
theorem map_of_min_eq (hr : R.IsLawful r) (hq : R.IsLawful q) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hγ : γ ≠ ⊥)
    (hag : ∀ d, min (ν (r d)) γ = min (q d) γ) : R.IsLawful (ν ∘ r) :=
  hr.map_of_bot_iff hq hK hν fun d ↦ eq_bot_iff_of_min_eq (hag d) hγ

/-- **Transport of lawfulness without global bottom reflection.**  If `ν` sends no non-bottom
value of the lawful section `r` to bottom, then `ν ∘ r` is lawful: `r` is its own lawful companion
(`IsLawful.map_of_bot_iff`).  It generalizes `IsLawful.map_of_bot_reflecting`, which asks bottom
reflection at every label; in the completion, which is not constructed here, it is to decode a
labelling of codes whose non-bottom codes the decoder reads as non-bottom, such as the flattened
codes of `VaughtConjecture.Extension.FlattenedSource`. -/
theorem map_of_apply_eq_bot (hr : R.IsLawful r) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ d, ν (r d) = ⊥ → r d = ⊥) :
    R.IsLawful (ν ∘ r) :=
  hr.map_of_bot_iff hr hK hν fun d ↦ ⟨hbot d, fun h ↦ by rw [h, hν.map_bot]⟩

end IsLawful

/-- **The bottom pattern is the only obstruction.**  For a lawful section `r` on grades at most
`K` and a witness `ν` bounded by grade `K`, the section `ν ∘ r` is lawful exactly when some lawful
section is bottom at the same cells as `ν ∘ r`. -/
theorem isLawful_comp_iff_exists_bot_iff {r : ι → Label.{u}} (hr : R.IsLawful r)
    (hK : ∀ d, D.grade d ≤ K) (hν : IsWitness (stepSuppressor K) ν) :
    R.IsLawful (ν ∘ r) ↔ ∃ q, R.IsLawful q ∧ ∀ d, ν (r d) = ⊥ ↔ q d = ⊥ :=
  ⟨fun h ↦ ⟨ν ∘ r, h, fun _ ↦ Iff.rfl⟩, fun ⟨_, hq, hbot⟩ ↦ hr.map_of_bot_iff hq hK hν hbot⟩

namespace IsLawfulBelow

variable {X : Finset α × ℕ} {r q : D.below X → Label.{u}}

/-- **Transport of lawfulness through a witness with a lawful companion**, below a pair `X`
(`IsLawful.map_of_bot_iff`). -/
theorem map_of_bot_iff (hr : R.IsLawfulBelow X r) (hq : R.IsLawfulBelow X q)
    (hK : ∀ d : D.below X, D.grade d ≤ K) (hν : IsWitness (stepSuppressor K) ν)
    (hbot : ∀ d, ν (r d) = ⊥ ↔ q d = ⊥) : R.IsLawfulBelow X (ν ∘ r) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).map_of_bot_iff (isLawfulBelow_iff.mp hq) hK hν
    hbot)

/-- **Positive-cap transport of lawfulness**, below a pair `X` (`IsLawful.map_of_min_eq`).  Let
`r` and `q` be lawful below `X`, the grades of the cells below `X` at most `K`, `ν` a witness
bounded by grade `K`, and `γ ≠ ⊥` with `min (ν (r d)) γ = min (q d) γ`.  Then `ν ∘ r` is lawful
below `X`.  In the owner alignment of the completion
(`CellScheme.Rows.hasOwnerCappedLifts_of_source`), `r` is a labelling lawful below the target pair
of a lift, `ν` the alignment decoder, and `q` the ambient labelling at the positive cap of the
lift, so that the decoded labelling is lawful. -/
theorem map_of_min_eq (hr : R.IsLawfulBelow X r) (hq : R.IsLawfulBelow X q)
    (hK : ∀ d : D.below X, D.grade d ≤ K) (hν : IsWitness (stepSuppressor K) ν) (hγ : γ ≠ ⊥)
    (hag : ∀ d, min (ν (r d)) γ = min (q d) γ) : R.IsLawfulBelow X (ν ∘ r) :=
  hr.map_of_bot_iff hq hK hν fun d ↦ eq_bot_iff_of_min_eq (hag d) hγ

/-- **Transport of lawfulness without global bottom reflection**, below a pair `X`
(`IsLawful.map_of_apply_eq_bot`). -/
theorem map_of_apply_eq_bot (hr : R.IsLawfulBelow X r) (hK : ∀ d : D.below X, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ d, ν (r d) = ⊥ → r d = ⊥) :
    R.IsLawfulBelow X (ν ∘ r) :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).map_of_apply_eq_bot hK hν hbot)

end IsLawfulBelow

end VaughtConjecture.CellScheme.Rows

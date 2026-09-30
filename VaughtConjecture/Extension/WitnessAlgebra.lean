/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# The witness algebra of the coatom completion

Roadmap, Layer 3, 3.1 (the section theorem and the witnesses bounded by a grade) and 3.1, row 6,
checkpoint 2.3 (transformation algebra); Layer 1 (guarded composition retains its guards, and no
transitivity is declared); semantic contract, item 3.

A value map `ν` is a **witness bounded by grade `K`** when `(stepSuppressor K, ν)` is a witness
([Kni26, Definition 2.3.9]): it fixes bottom, is monotone, commutes with visibility replacement at
every threshold `k ≤ K` without a guard, and above `K` sends the replacements of a label to
bottom whenever it sends the label to bottom.  This file proves the rules for such witnesses that
the seed constructions of checkpoints 2.5 and 2.6 use, each named with its use.

* **Short labels** (`IsShort m x`): bottom, the formal top, or an ordinal whose finite part is
  at most `m` (`isShort_coe`).  The **flattening** `trim m` replaces a finite part above `m` by
  `m` (`trim_coe`); it is monotone (`monotone_trim`), fixes the short labels
  (`IsShort.trim_eq`), and commutes with visibility replacement at thresholds `k ≤ m`
  (`trim_visibilityReplace`).
* **Repair of the bottom guard** (`isWitness_comp_trim`): a monotone map fixing bottom that
  commutes with visibility replacement at the thresholds `≤ m` becomes a witness bounded by `m`
  after flattening at `m`, because a map commuting with the replacements at `m` sends the whole
  flattened band to bottom once it sends one point of it to bottom.
* **Composition without bottom reflection on short labels**
  (`IsWitness.exists_eq_comp_of_isShort`): for witnesses `τ` bounded by `m` and `ν` bounded by
  `K ≥ m`, some witness bounded by `m` agrees with `ν ∘ τ` at every label short at `m`.  The
  composite `ν ∘ τ` itself need not be a witness, and the library's guarded composition
  `IsWitness.comp_of_bot_reflecting` needs bottom reflection for it
  (`VaughtConjecture.Extension.TransformationExamples`).
* **The capped witness** (`TransformsTo.exists_isWitness_capped`): the locality at a cell `c`
  of maximal grade, with a label `p c` self-visible at that grade, has a witness bounded by the
  grade of `c` whose values are at most `p c` and which sends each source label exactly to its
  capped target.  The key step is `IsWitness.le_apply_visibilityReplace`: past a self-visible
  cap below the suppressor, a shifter stays past it at every replacement.
* **Mapped locality** (`TransformsTo.map_of_isShort`, `TransformsTo.map_of_bot_reflecting`): a
  locality `E ⇒ (d ↦ min (p d) (p c))` gives `E ⇒ (d ↦ min (ν (p d)) (ν (p c)))` for a witness
  `ν` bounded by `K ≥` the grade of `c`, when the source row `E` is short at the grade of `c`, or
  when `ν` reflects bottom.
* **Maximum of shifters** (`IsWitness.max`) and **postcomposition**
  (`IsWitness.transformsTo_comp`): a witness bounded by `K` transforms every labelling of cells
  of grade `≤ K` to its image.

Two rules the seeds use are already in the library: capping the target at a self-visible label
is `TransformsTo.min_const` (a related target-capping variant of [Kni26, Lemma 2.3.12]), and a
transformation does not reverse two sources of the same grade (the fixed-grade case of
`TransformsTo.le_of_le`).

## Placement

These statements belong in `VaughtConjecture.Label.Transform`, after the guarded composition, with
`IsShort` and `trim` beside the self-visible labels of `VaughtConjecture.Label.Visibility`.  They
are stated here so that those files are unchanged.

## References

Witnesses are [Kni26, Definition 2.3.9] and visibility replacement is [Kni26, Definition 2.2.3].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {D : Type*} {grade : D → ℕ} {g : ℕ → Label.{u}} {σ τ ν f : Label.{u} → Label.{u}}
  {m K k i : ℕ} {x c : Label.{u}}

/-! ### Short labels and flattening -/

/-- A label is **short** at grade `m`: it is bottom, the formal top, or an ordinal whose finite
part is at most `m`.  Used by 2.5 and 2.6: an owner of a seed construction is short when every
entry of its row is short at its grade, as the new rows are by their support; the section theorem
(`CellScheme.Rows.IsLawful.map_of_isShort_or`) needs no other condition at such an owner. -/
def IsShort (m : ℕ) (x : Label.{u}) : Prop := ∀ o : Ordinal.{u}, (o : Label.{u}) = x → o % ω ≤ m

/-- Bottom is short at every grade. -/
@[simp] theorem isShort_bot (m : ℕ) : IsShort m (⊥ : Label.{u}) := fun _ h ↦ absurd h (by simp)

/-- The formal top is short at every grade. -/
@[simp] theorem isShort_top (m : ℕ) : IsShort m (⊤ : Label.{u}) := fun _ h ↦ absurd h (by simp)

/-- An ordinal is short at `m` exactly when its finite part is at most `m`. -/
@[simp] theorem isShort_coe {o : Ordinal.{u}} : IsShort m (o : Label.{u}) ↔ o % ω ≤ m :=
  ⟨fun h ↦ h o rfl, fun h _ he ↦ by rwa [WithTop.coe_injective (WithBot.coe_injective he)]⟩

/-- The flattening of an ordinal at `m`: its finite part is replaced by the smaller of it and
`m`, in the same band. -/
noncomputable def trimOrd (m : ℕ) (o : Ordinal.{u}) : Ordinal.{u} :=
  ω * (o / ω) + min (o % ω) m

/-- The **flattening** of labels at `m`: bottom and the formal top are fixed, and an ordinal
`ω * b + n` (`n < ω`) goes to `ω * b + min n m`. -/
noncomputable def trim (m : ℕ) : Label.{u} → Label.{u} := WithBot.map (WithTop.map (trimOrd m))

/-- Flattening fixes bottom. -/
@[simp] theorem trim_bot (m : ℕ) : trim m (⊥ : Label.{u}) = ⊥ := rfl

/-- Flattening fixes the formal top. -/
@[simp] theorem trim_top (m : ℕ) : trim m (⊤ : Label.{u}) = ⊤ := rfl

/-- Flattening of an ordinal label. -/
@[simp] theorem trim_coe (m : ℕ) (o : Ordinal.{u}) :
    trim m (o : Label.{u}) = (trimOrd m o : Label.{u}) := rfl

/-- The flattened finite part is finite. -/
private theorem min_mod_lt (m : ℕ) (o : Ordinal.{u}) : min (o % ω) (m : Ordinal.{u}) < ω :=
  (min_le_left _ _).trans_lt (mod_lt _ omega0_ne_zero)

/-- Flattening keeps the band. -/
private theorem trimOrd_div (m : ℕ) (o : Ordinal.{u}) : trimOrd m o / ω = o / ω := by
  rw [trimOrd, mul_add_div _ omega0_ne_zero, div_eq_zero_of_lt (min_mod_lt m o), add_zero]

/-- The finite part after flattening. -/
private theorem trimOrd_mod (m : ℕ) (o : Ordinal.{u}) :
    trimOrd m o % ω = min (o % ω) (m : Ordinal.{u}) := by
  rw [trimOrd, mul_add_mod_self, mod_eq_of_lt (min_mod_lt m o)]

/-- In one band, ordinals compare as their finite parts. -/
private theorem mod_le_mod_of_le_of_div_eq {o o' : Ordinal.{u}} (h : o ≤ o')
    (he : o / ω = o' / ω) : o % ω ≤ o' % ω := by
  have := div_add_mod o ω ▸ div_add_mod o' ω ▸ h
  rwa [he, add_le_add_iff_left] at this

/-- An ordinal of a lower band lies below every ordinal of a higher band. -/
private theorem lt_of_div_lt {a b x y : Ordinal.{u}} (hx : x < ω) (h : a < b) :
    ω * a + x < ω * b + y :=
  calc ω * a + x < ω * a + ω := add_lt_add_right hx _
    _ = ω * Order.succ a := (mul_succ _ _).symm
    _ ≤ ω * b := by gcongr; exact Order.succ_le_of_lt h
    _ ≤ ω * b + y := le_self_add

/-- Flattening of ordinals is monotone. -/
private theorem trimOrd_mono (m : ℕ) {o o' : Ordinal.{u}} (h : o ≤ o') :
    trimOrd m o ≤ trimOrd m o' := by
  rcases (div_le_left h ω).lt_or_eq with hlt | he
  · exact (lt_of_div_lt (min_mod_lt m o) hlt).le
  · rw [trimOrd, trimOrd, he]
    exact add_le_add_right (min_le_min_right _ (mod_le_mod_of_le_of_div_eq h he)) _

/-- **Flattening is monotone.** -/
theorem monotone_trim (m : ℕ) : Monotone (trim m : Label.{u} → Label.{u}) :=
  (Monotone.withTop_map fun _ _ ↦ trimOrd_mono m).withBot_map

/-- Flattening sends a label to bottom only if it is bottom. -/
@[simp] theorem trim_eq_bot_iff : trim m x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- **Flattening fixes the short labels.** -/
theorem IsShort.trim_eq (h : IsShort m x) : trim m x = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    rw [trim_coe, trimOrd, min_eq_left (isShort_coe.mp h), div_add_mod]

/-- **Flattening commutes with visibility replacement** at every threshold `k ≤ m` and every
value `i ≤ k`. -/
theorem trim_visibilityReplace (hk : k ≤ m) (hi : i ≤ k) (x : Label.{u}) :
    trim m (visibilityReplace k i x) = visibilityReplace k i (trim m x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    have hkm : (k : Ordinal.{u}) ≤ m := by exact_mod_cast hk
    have him : (i : Ordinal.{u}) ≤ m := by exact_mod_cast hi.trans hk
    simp only [visibilityReplace_coe, trim_coe, WithBot.coe_inj, WithTop.coe_inj]
    rw [trimOrd, Ordinal.visibilityReplace_div, Ordinal.visibilityReplace_mod,
      Ordinal.visibilityReplace, trimOrd_div, trimOrd_mod]
    by_cases ho : o % ω < k
    · rw [ite_eq_left ho, ite_eq_left ((min_le_left _ _).trans_lt ho), min_eq_left him]
    · rw [ite_eq_right ho, ite_eq_right (not_lt.mpr (le_min (not_lt.mp ho) hkm))]

/-! ### Repair of the bottom guard -/

/-- A map commuting with visibility replacement at `m` that sends one flattened point of a band
to bottom sends every flattened point of that band to bottom. -/
private theorem apply_trim_eq_bot (hmono : Monotone f)
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x))
    {o o' : Ordinal.{u}} (he : o / ω = o' / ω) (ho : f (trim m (o : Label.{u})) = ⊥) :
    f (trim m (o' : Label.{u})) = ⊥ := by
  -- The start `ω * (o / ω)` of the band is sent to bottom.
  have h0 : f ((ω * (o / ω) : Ordinal.{u}) : Label.{u}) = ⊥ :=
    le_bot_iff.mp (ho ▸ hmono (show ((ω * (o / ω) : Ordinal.{u}) : Label.{u}) ≤ trim m o from
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)))
  obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o' omega0_ne_zero)
  have htrim : trimOrd m o' = ω * (o / ω) + (min n m : ℕ) := by
    rw [trimOrd, hn, he, Nat.mono_cast.map_min]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [trim_coe, htrim, Nat.min_zero, Nat.cast_zero, add_zero, h0]
  · -- Otherwise the flattened point is a replacement of the band start at threshold `m`.
    have hvr : Ordinal.visibilityReplace m (min n m) (ω * (o / ω)) = trimOrd m o' := by
      rw [htrim, Ordinal.visibilityReplace_of_lt (by rw [mul_mod]; exact_mod_cast hm),
        mul_div_cancel _ omega0_ne_zero]
    rw [trim_coe, ← hvr, ← visibilityReplace_coe, hcomm _ m le_rfl _ (min_le_right n m), h0,
      visibilityReplace_bot]

/-- **Repair of the bottom guard.**  A monotone map `f` fixing bottom and commuting with
visibility replacement at every threshold `≤ m` gives the witness `f ∘ trim m` bounded by `m`.
Used by 2.5 and 2.6 through `IsWitness.exists_eq_comp_of_isShort`. -/
theorem isWitness_comp_trim (hbot : f ⊥ = ⊥) (hmono : Monotone f)
    (hcomm : ∀ x, ∀ k ≤ m, ∀ i ≤ k, f (visibilityReplace k i x) = visibilityReplace k i (f x)) :
    IsWitness (stepSuppressor.{u} m) (f ∘ trim m) where
  antitone := (IsWitness.id_step m).antitone
  isSelfVisible := (IsWitness.id_step m).isSelfVisible
  map_bot := by simp [hbot]
  monotone := hmono.comp (monotone_trim m)
  visibilityReplace_comm x k hx i hi := by
    simp only [Function.comp_apply] at hx ⊢
    by_cases hk : k ≤ m
    · rw [trim_visibilityReplace hk hi, hcomm _ k hk i hi]
    rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
    rw [hx, visibilityReplace_bot]
    induction x using recBotCoeTop with
    | bot => simpa using hbot
    | top => exact hx
    | coe o =>
      rw [visibilityReplace_coe]
      exact apply_trim_eq_bot hmono hcomm (Ordinal.visibilityReplace_div k i o).symm hx

/-! ### Composition on short labels -/

/-- **Composition without bottom reflection on short labels.**  For a witness `τ` bounded by `m`
and a witness `ν` bounded by `K ≥ m`, some witness bounded by `m` agrees with `ν ∘ τ` at every
label short at `m`: the composite flattened at `m`.  Used by 2.5 and 2.6: through
`TransformsTo.map_of_isShort`, it gives the locality of the new owners, whose rows are short, in
the section theorem of the seed constructions. -/
theorem IsWitness.exists_eq_comp_of_isShort (hτ : IsWitness (stepSuppressor m) τ)
    (hν : IsWitness (stepSuppressor K) ν) (hmK : m ≤ K) :
    ∃ ρ, IsWitness (stepSuppressor.{u} m) ρ ∧ ∀ x, IsShort m x → ρ x = ν (τ x) := by
  refine ⟨(ν ∘ τ) ∘ trim m, isWitness_comp_trim (by simp [hτ.map_bot, hν.map_bot])
    (hν.monotone.comp hτ.monotone) fun x k hk i hi ↦ ?_, fun x hx ↦ by simp [hx.trim_eq]⟩
  simp only [Function.comp_apply]
  rw [hτ.visibilityReplace_comm x k (by simp [hk]) i hi,
    hν.visibilityReplace_comm _ k (by simp [hk.trans hmK]) i hi]

/-! ### The capped witness -/

/-- **Past a self-visible cap below the suppressor, a shifter stays past it at every
replacement.**  If `c` is self-visible at `k`, `c ≤ g k`, and `c < σ x`, then
`c ≤ σ (visibilityReplace k i x)` for every `i ≤ k`.  Used by 2.5 and 2.6 through
`TransformsTo.exists_isWitness_capped`. -/
theorem IsWitness.le_apply_visibilityReplace (hw : IsWitness g σ) (hc : IsSelfVisible k c)
    (hcg : c ≤ g k) (hx : c < σ x) (hi : i ≤ k) : c ≤ σ (visibilityReplace k i x) := by
  by_contra hlt
  rw [not_le] at hlt
  rcases hi.lt_or_eq with hi | rfl
  · -- The label is recovered by a second replacement, with which the shifter commutes.
    obtain ⟨j, hj, hx'⟩ := exists_visibilityReplace_visibilityReplace hi x
    have h := hw.visibilityReplace_comm _ k (hlt.le.trans hcg) j hj.le
    rw [hx'] at h
    exact hx.not_ge (h ▸ visibilityReplace_le_of_le hj.le hc hlt.le)
  · exact hx.not_ge ((hw.monotone (le_visibilityReplace (by omega) x)).trans hlt.le)

/-- **The capped witness.**  Let `c` be a cell of maximal grade whose label `p c` is
self-visible at its grade, and suppose `E ⇒ (d ↦ min (p d) (p c))`.  Then some witness `τ`
bounded by the grade of `c` has all its values at most `p c` and sends each source label exactly
to its capped target, `τ (E d) = min (p d) (p c)`.  Used by 2.5 and 2.6: it is the first step of
the locality of a short owner in the section theorem (`TransformsTo.map_of_isShort`). -/
theorem TransformsTo.exists_isWitness_capped {E p : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hvis : IsSelfVisible (grade c) (p c))
    (hloc : TransformsTo grade E fun d ↦ min (p d) (p c)) :
    ∃ τ, IsWitness (stepSuppressor.{u} (grade c)) τ ∧ (∀ x, τ x ≤ p c) ∧
      ∀ d, τ (E d) = min (p d) (p c) := by
  by_cases hb : p c = ⊥
  · refine ⟨fun _ ↦ ⊥, IsWitness.bot_top.of_le (fun _ ↦ le_top)
      (IsWitness.id_step _).antitone (IsWitness.id_step _).isSelfVisible, fun _ ↦ bot_le,
      fun d ↦ by simp [hb]⟩
  obtain ⟨g, σ, hw, heq⟩ := hloc
  -- The cap lies below the suppressor at every grade up to that of `c`.
  have hcg (k : ℕ) (hk : k ≤ grade c) : p c ≤ g k := by
    have h := heq c
    simp only [min_self] at h
    exact h.le.trans ((min_le_right _ _).trans (hw.antitone hk))
  refine ⟨fun x ↦ min (σ x) (p c), ⟨(IsWitness.id_step _).antitone,
    (IsWitness.id_step _).isSelfVisible, by simp [hw.map_bot],
    fun _ _ h ↦ min_le_min_right _ (hw.monotone h), fun x k hx i hi ↦ ?_⟩,
    fun _ ↦ min_le_right _ _, fun d ↦ ?_⟩
  · by_cases hk : k ≤ grade c
    · have hck : IsSelfVisible k (p c) := hvis.mono hk
      rcases le_or_gt (σ x) (p c) with hle | hlt
      · rw [min_eq_left hle, hw.visibilityReplace_comm x k (hle.trans (hcg k hk)) i hi,
          min_eq_left (visibilityReplace_le_of_le hi hck hle)]
      · rw [min_eq_right hlt.le, hck.visibilityReplace_eq,
          min_eq_right (hw.le_apply_visibilityReplace hck (hcg k hk) hlt hi)]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, min_eq_bot] at hx
      have hσ : σ x = ⊥ := hx.resolve_right hb
      rw [hw.visibilityReplace_comm x k (hσ ▸ bot_le) i hi, hσ]
      simp
  · have h := heq d
    simp only at h
    calc min (σ (E d)) (p c) = min (min (σ (E d)) (g (grade d))) (p c) := by
          rw [min_assoc, min_eq_right (hcg _ (hmax d))]
      _ = min (p d) (p c) := by rw [← h, min_assoc, min_self]

/-! ### Mapped locality -/

/-- **Mapped locality of a short row.**  Let `c` be a cell of maximal grade, at most `K`, whose
label is self-visible at its grade, let the source row `E` be short at the grade of `c`, and let
`ν` be a witness bounded by `K`.  A locality `E ⇒ (d ↦ min (p d) (p c))` gives
`E ⇒ (d ↦ min (ν (p d)) (ν (p c)))`; no bottom reflection of `ν` is needed.  Used by 2.5 and
2.6: the locality of the new owners in the section theorem. -/
theorem TransformsTo.map_of_isShort {E p : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K) (hshort : ∀ d, IsShort (grade c) (E d))
    (hvis : IsSelfVisible (grade c) (p c)) (hloc : TransformsTo grade E fun d ↦ min (p d) (p c))
    (hν : IsWitness (stepSuppressor K) ν) :
    TransformsTo grade E fun d ↦ min (ν (p d)) (ν (p c)) := by
  obtain ⟨τ, hτ, -, hread⟩ := hloc.exists_isWitness_capped hmax hvis
  obtain ⟨ρ, hρ, hρτ⟩ := hτ.exists_eq_comp_of_isShort hν hcK
  refine ⟨_, ρ, hρ, fun d ↦ ?_⟩
  rw [stepSuppressor_of_le (hmax d), min_top_right, hρτ _ (hshort d), hread,
    hν.monotone.map_min]

/-- **Mapped locality through a bottom-reflecting witness.**  As `TransformsTo.map_of_isShort`,
with no condition on the source row and a witness `ν` bounded by `K` that sends a label to bottom
only if it is bottom.  Used by 2.5 and 2.6: through
`CellScheme.Rows.IsLawful.map_of_bot_reflecting`, it makes the strongly coded representative of
the boundary labels lawful. -/
theorem TransformsTo.map_of_bot_reflecting {E p : D → Label.{u}} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K) (hvis : IsSelfVisible (grade c) (p c))
    (hloc : TransformsTo grade E fun d ↦ min (p d) (p c)) (hν : IsWitness (stepSuppressor K) ν)
    (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    TransformsTo grade E fun d ↦ min (ν (p d)) (ν (p c)) := by
  obtain ⟨τ, hτ, -, hread⟩ := hloc.exists_isWitness_capped hmax hvis
  refine ⟨_, _, hτ.comp_of_bot_reflecting (hν.of_le_stepSuppressor hcK) fun x ↦ hbot (τ x),
    fun d ↦ ?_⟩
  rw [stepSuppressor_of_le (hmax d), min_top_right, Function.comp_apply, hread,
    hν.monotone.map_min]

/-! ### Maximum and postcomposition -/

/-- **The maximum of two shifters** with the same suppressor is a shifter for it: the guard of
the maximum implies the guards of both.  Used by 2.6: the row of a new full-scope cell on a free
diagonal is the maximum of the capped witness of an owner (`TransformsTo.exists_isWitness_capped`)
and a step witness at a fresh band. -/
theorem IsWitness.max (hσ : IsWitness g σ) (hτ : IsWitness g τ) :
    IsWitness g fun x ↦ max (σ x) (τ x) where
  antitone := hσ.antitone
  isSelfVisible := hσ.isSelfVisible
  map_bot := by simp [hσ.map_bot, hτ.map_bot]
  monotone _ _ h := max_le_max (hσ.monotone h) (hτ.monotone h)
  visibilityReplace_comm x k hx i hi := by
    rw [hσ.visibilityReplace_comm x k ((le_max_left _ _).trans hx) i hi,
      hτ.visibilityReplace_comm x k ((le_max_right _ _).trans hx) i hi,
      visibilityReplace_max hi]

/-- **Postcomposition.**  On cells of grade at most `K`, every labelling transforms to its image
under a witness bounded by `K`.  Used by 2.5 and 2.6: the boundary labels transform to their
strongly coded representative, and it transforms back to them. -/
theorem IsWitness.transformsTo_comp (hν : IsWitness (stepSuppressor K) ν)
    (hK : ∀ d, grade d ≤ K) (p : D → Label.{u}) : TransformsTo grade p (ν ∘ p) :=
  ⟨_, ν, hν, fun d ↦ by rw [stepSuppressor_of_le (hK d), min_top_right, Function.comp_apply]⟩

end VaughtConjecture.Label

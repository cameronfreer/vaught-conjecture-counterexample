/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedContextGap
import VaughtConjecture.MainTheorem.ReplicatedTieInstance

/-!
# Cuts at a grade and codes above them in the values of the seed

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme at an arbitrary grade
`2 ≤ k ≤ m + 1`, the top grade `m + 1` included).

A context-only lift at a cap `c` above a lawful ambient reads the ambient through the row of a cell
of full scope at `(univ, k)` (its capped decoder), and the context cell of the gap analysis
(`Seed.not_gap_of_context_cell`) gives a **cut**: a value of that row at a cell of the attachment,
self-visible at `k` (the context cell's value, or the tied value).  The cut needs **headroom**: the
prescription's values above the cap must be coded strictly above the cut by a state of the
catalogue, and read back by one decoder bounded by `k`.

* **Reachable cuts** (`Seed.ReachableCut`, `Seed.reachableCut_mem`): a value of the row of a
  cell of full scope at `(univ, k)` at a cell of the attachment of grade at most `k`, self-visible
  at `k`.
  The definition does not mention a lift, an ambient or a cap.  Every reachable cut is a value of
  `Γ` (the row reads a state of the catalogue) and a height at `k`.  So with one set of values
  `Γ` at every grade, the reachable cuts range over the values of `Γ` self-visible at `k`: the
  values that would be codes are themselves reachable cuts.
* **No headroom at the top block of the values of the seed**
  (`Seed.lt_omega0_mul_of_mem_seedValues`, `Seed.isSelfVisible_witness_of_mem_seedValues`,
  `Seed.not_exists_code_above_top`): every value of `Seed.seedValues` lies below `ω * (C + 1)`
  (`C` the number of cells of the attachment); above a label `ω * C + k` every value of
  `Seed.seedValues` is self-visible at `k`, and
  every witness bounded by `k` sends it to a label self-visible at `k`.  So above a cut in the block
  `ω * C` no code in `Seed.seedValues` reads a prescription value not self-visible at `k` (a value
  at a context cell of grade below `k`).

**The gate at the input** (`TieInstance.gradeGate_fails`, at the grade `2 = m + 1`, the top
grade).  The state `twoLevel (ω * C + 3) (ω * C + 4) ∘ P₀` of the catalogue (`P₀` the admitted
completion of `sep`) has the reachable cut `ω * C + 4`, the only label in its interval
`(ω * C + 3, ω * C + 4]` between a cell below the cap `ω * C + 4` and a cell at it; the lawful
context section `TieInstance.topSection C` agrees with it capped at the cap and carries
`ω * (C + 1) + 1`, not self-visible at `2`, at the cell `y` of grade `1`; and no value of
`Seed.seedValues` above the cut is read as that label by a witness bounded by `2`.  A serving
state agreeing with the ambient's state capped at the cut is at least the cut at `y` (the ambient's
state is `ω * C + 4` there), so it would need such a code: the fresh codes above a reachable cut
fail for the single set of values at this input.

**The single set of values and a set per grade.** The replicated scheme takes the states of its
catalogue at every grade from one set `Γ`, here `Seed.seedValues`; the reachable cuts at the grade
`k` lie in the values of `Γ` self-visible at `k` (`Seed.reachableCut_mem`), the codes above a cut
must lie in `Γ` too, and at the input a reachable cut lies in the top block of `Γ`, above which `Γ`
has only labels self-visible at `k`. A set `Γ_k` per grade, with codes in blocks above the values
reachable at the grades below `k`, would avoid this; it is a change of the catalogue of the tower,
not made here. The single decoder of the gate (agreement with the ambient's decoder below the cut,
the codes read above it, the capped agreement at every class of cells) is not attempted, the fresh
codes failing first.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9]; agreement heights are
those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

/-- **A witness bounded by `k` keeps self-visibility at `k`.** -/
theorem isSelfVisible_witness {k : ℕ} {θ : Label.{u} → Label.{u}}
    (hθ : IsWitness (stepSuppressor k) θ) {y : Label.{u}} (hy : IsSelfVisible k y) :
    IsSelfVisible k (θ y) := by
  have h := hθ.visibilityReplace_comm y k (by rw [stepSuppressor_of_le le_rfl]; exact le_top) k
    le_rfl
  unfold IsSelfVisible at hy ⊢
  rw [hy] at h
  exact h.symm

/-- **Above `ω * C + k` and below `ω * (C + 1)` every label is self-visible at `k`.** -/
theorem isSelfVisible_of_top_block {C k : ℕ} {y : Label.{u}}
    (hlo : (((Ordinal.omega0 * (C : Ordinal.{u}) + (k : Ordinal.{u}) : Ordinal.{u})) :
      Label.{u}) < y)
    (hhi : y < (((Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u})) : Ordinal.{u}) : Label.{u})) :
    IsSelfVisible k y := by
  induction y using recBotCoeTop with
  | bot => exact absurd hlo (not_lt.mpr bot_le)
  | top => exact absurd hhi (not_lt.mpr le_top)
  | coe o =>
    have hlo' : Ordinal.omega0 * (C : Ordinal.{u}) + (k : Ordinal.{u}) < o := by exact_mod_cast hlo
    have hhi' : o < Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u}) := by exact_mod_cast hhi
    have hle : Ordinal.omega0 * (C : Ordinal.{u}) ≤ o := le_self_add.trans hlo'.le
    obtain ⟨r, hr⟩ : ∃ r, o = Ordinal.omega0 * (C : Ordinal.{u}) + r :=
      ⟨_, (Ordinal.add_sub_cancel_of_le hle).symm⟩
    subst hr
    rw [Nat.cast_succ, mul_add_one] at hhi'
    have hrω : r < Ordinal.omega0 := (add_lt_add_iff_left _).mp hhi'
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hrω
    have hkn : k ≤ n := by
      have := (add_lt_add_iff_left _).mp hlo'
      exact_mod_cast this.le
    exact isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) hkn

/-- **The two-level positive constant**: `⊥` at `⊥`, `v₁` on the positive labels below `ω`, `v₂`
from `ω` on. -/
noncomputable def twoLevel (v₁ v₂ : Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x < (Ordinal.omega0 : Label.{u}) then posConst v₁ x else posConst v₂ x

/-- **The two-level positive constant is a witness bounded by `K`** for `v₁ ≤ v₂` self-visible at
`K`. -/
theorem isWitness_twoLevel {K : ℕ} {v₁ v₂ : Label.{u}} (hv₁ : IsSelfVisible K v₁)
    (hv₂ : IsSelfVisible K v₂) (h12 : v₁ ≤ v₂) : IsWitness (stepSuppressor K) (twoLevel v₁ v₂) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := by
    unfold twoLevel
    rw [ite_eq_left (WithBot.bot_lt_coe _)]
    exact (isWitness_posConst hv₁).map_bot
  monotone x y hxy := by
    unfold twoLevel
    split_ifs with hx hy hy
    · exact (isWitness_posConst hv₁).monotone hxy
    · unfold posConst
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact bot_le
      · exact absurd (le_bot_iff.mp (h2 ▸ hxy)) h1
      · exact h12
    · exact absurd (hxy.trans_lt hy) hx
    · exact (isWitness_posConst hv₂).monotone hxy
  visibilityReplace_comm x k hx i hi := by
    unfold twoLevel at hx ⊢
    by_cases hω : x < (Ordinal.omega0 : Label.{u})
    · rw [ite_eq_left hω] at hx
      rw [ite_eq_left ((visibilityReplace_lt_omega0_iff k i x).mpr hω), ite_eq_left hω]
      exact (isWitness_posConst hv₁).visibilityReplace_comm x k hx i hi
    · rw [ite_eq_right hω] at hx
      rw [ite_eq_right (mt (visibilityReplace_lt_omega0_iff k i x).mp hω), ite_eq_right hω]
      exact (isWitness_posConst hv₂).visibilityReplace_comm x k hx i hi

theorem twoLevel_eq_bot_iff {v₁ v₂ x : Label.{u}} (hv₁ : v₁ ≠ ⊥) (hv₂ : v₂ ≠ ⊥) :
    twoLevel v₁ v₂ x = ⊥ ↔ x = ⊥ := by
  unfold twoLevel
  split_ifs
  · exact posConst_eq_bot_iff hv₁
  · exact posConst_eq_bot_iff hv₂

theorem twoLevel_mem {v₁ v₂ : Label.{u}} (x : Label.{u}) :
    twoLevel v₁ v₂ x = ⊥ ∨ twoLevel v₁ v₂ x = v₁ ∨ twoLevel v₁ v₂ x = v₂ := by
  unfold twoLevel posConst
  split_ifs <;> simp

theorem twoLevel_of_lt {v₁ v₂ x : Label.{u}} (hx0 : x ≠ ⊥) (hx : x < (Ordinal.omega0 : Label.{u})) :
    twoLevel v₁ v₂ x = v₁ := by
  unfold twoLevel posConst; rw [ite_eq_left hx, ite_eq_right hx0]

theorem twoLevel_of_le {v₁ v₂ x : Label.{u}} (hx : (Ordinal.omega0 : Label.{u}) ≤ x) :
    twoLevel v₁ v₂ x = v₂ := by
  have hx0 : x ≠ ⊥ := fun h ↦ absurd (h ▸ hx) (not_le.mpr (WithBot.bot_lt_coe _))
  unfold twoLevel posConst; rw [ite_eq_right (not_lt.mpr hx), ite_eq_right hx0]

/-- Between `β + n` and `β + (n + 1)` there is only `β + (n + 1)`. -/
theorem eq_of_lt_of_le_succ {β : Ordinal.{u}} {n : ℕ} {x : Label.{u}}
    (h1 : (((β + (n : Ordinal.{u})) : Ordinal.{u}) : Label.{u}) < x)
    (h2 : x ≤ (((β + ((n + 1 : ℕ) : Ordinal.{u})) : Ordinal.{u}) : Label.{u})) :
    x = (((β + ((n + 1 : ℕ) : Ordinal.{u})) : Ordinal.{u}) : Label.{u}) := by
  refine le_antisymm h2 ?_
  induction x using recBotCoeTop with
  | bot => exact absurd h1 (not_lt.mpr bot_le)
  | top => exact le_top
  | coe o =>
    have h1' : β + (n : Ordinal.{u}) < o := by exact_mod_cast h1
    have := Order.succ_le_of_lt h1'
    rw [Order.succ_eq_add_one, add_assoc, ← Nat.cast_succ] at this
    exact_mod_cast this

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

variable (I g H Γ A B') in
/-- **A reachable cut at the grade `k`**: a value of the row of a cell of full scope at `(univ, k)`
of the replicated scheme at a cell of the attachment of grade at most `k`, self-visible at `k`.
No lift, ambient or cap enters: a lift reads its ambient through such a row, and the cut of the gap
analysis (`Seed.not_gap_of_context_cell`: the context cell's value or the tied value) is such a
value. -/
def ReachableCut (k : ℕ) (x : Label.{u}) : Prop :=
  ∃ f : Fin (I.attachTower g H Γ A B').card,
    (I.attachTower g H Γ A B').toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k) ∧
    ∃ d : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade d ≤ k ∧
      (I.replicated g H Γ A B').rowAt (Fin.castAdd _ f) (I.attachEmb g H Γ A B' d) = x ∧
      IsSelfVisible k x

/-- **Every reachable cut is a value of `Γ` and a height at `k`**: the row of a cell of full scope
at `(univ, k)` reads a state of the catalogue at `k` on the attachment
(`Seed.exists_reading_of_writing`). -/
theorem reachableCut_mem (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ} (hk2 : 2 ≤ k)
    (hkm : k ≤ m + 1) {x : Label.{u}} (hx : I.ReachableCut g H Γ A B' k x) :
    x ∈ Γ ∧ x ∈ Scheme.heightSet Γ B' k := by
  obtain ⟨f, hf, d, hd, rfl, hv⟩ := hx
  obtain ⟨R, hR, hrow, -⟩ := exists_reading_of_writing (Γh := Γ) hcard hk2 hkm f hf
    (CellScheme.Rows.isLawful_const_bot (R := (I.attachment g).rows))
  have hRΓ := (Scheme.LadderBaseData.mem_towerCat.mp hR).1 d
  rw [← hrow d hd] at hRΓ
  exact ⟨hRΓ, Scheme.mem_heightSet.mpr (.inr ⟨hRΓ, hv⟩)⟩

/-- **The values of the seed lie below `ω * (C + 1)`** (`C` the number of cells of the
attachment), except `⊥`: the compressed labels have blocks below the number of blocks of the
labels, and the code set has blocks at most `C`. -/
theorem lt_omega0_mul_of_mem_seedValues {x : Label.{u}} (hx : x ∈ I.seedValues g) :
    x < (((Ordinal.omega0 * (((I.attachment g).card + 1 : ℕ) : Ordinal.{u})) : Ordinal.{u}) :
      Label.{u}) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact WithBot.bot_lt_coe _
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    refine (blockCompress_lt (label_mem_attachLabels c) (m + 2)).trans_le ?_
    rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
    refine omega0_mul_natCast_le_iff.mpr ?_
    have h1 := blockCount_le (I.attachLabels g)
    have h2 : #(I.attachLabels g) ≤ (I.attachment g).card := card_image_le.trans (by simp; rfl)
    omega
  · rcases mem_insert.mp hx with rfl | hx
    · exact WithBot.bot_lt_coe _
    obtain ⟨⟨i, f⟩, hif, rfl⟩ := mem_image.mp hx
    obtain ⟨hi, -⟩ := mem_product.mp hif
    rw [mem_range] at hi
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    calc Ordinal.omega0 * (i : Ordinal.{u}) + (f : Ordinal.{u})
        < Ordinal.omega0 * (i : Ordinal.{u}) + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 f)
      _ = Ordinal.omega0 * ((i + 1 : ℕ) : Ordinal.{u}) := by rw [Nat.cast_succ, mul_add_one]
      _ ≤ _ := omega0_mul_natCast_le_iff.mpr (by omega)

/-- **No headroom in the top block**: above `ω * C + k` every value of `Seed.seedValues` is
self-visible at `k`, so every witness bounded by `k` reads it as a label self-visible at `k`. -/
theorem isSelfVisible_witness_of_mem_seedValues {k : ℕ} {θ : Label.{u} → Label.{u}}
    (hθ : IsWitness (stepSuppressor k) θ) {y : Label.{u}} (hy : y ∈ I.seedValues g)
    (hlo : (((Ordinal.omega0 * ((I.attachment g).card : Ordinal.{u}) + (k : Ordinal.{u}) :
      Ordinal.{u})) : Label.{u}) < y) : IsSelfVisible k (θ y) :=
  Label.isSelfVisible_witness hθ
    (Label.isSelfVisible_of_top_block hlo (lt_omega0_mul_of_mem_seedValues hy))

/-- **No code above a cut of the top block**: for a cut `x` at least `ω * C + k`, no value of
`Seed.seedValues` above `x` is read by a witness bounded by `k` as a label `P` not self-visible at
`k`. -/
theorem not_exists_code_above_top {k : ℕ} {x P : Label.{u}}
    (hx : (((Ordinal.omega0 * ((I.attachment g).card : Ordinal.{u}) + (k : Ordinal.{u}) :
      Ordinal.{u})) : Label.{u}) ≤ x) (hP : ¬ IsSelfVisible k P) :
    ¬ ∃ y ∈ I.seedValues g, x < y ∧
      ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor k) θ ∧ θ y = P := by
  rintro ⟨y, hy, hxy, θ, hθ, rfl⟩
  exact hP (isSelfVisible_witness_of_mem_seedValues hθ hy (hx.trans_lt hxy))

end Seed

namespace TieInstance

open SeparationObstruction

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- The value `ω * C + n` of the top block of the code set (`C` a number of cells). -/
noncomputable abbrev topCode (C n : ℕ) : Label.{u} :=
  (((Ordinal.omega0 * (C : Ordinal.{u}) + (n : Ordinal.{u}) : Ordinal.{u})) : Label.{u})

/-- **The prescription above the cut**: `ω * (C + 1) + 1` at `y` and `z`, `ω * C + 5` at `o`,
`ω * C + 3` at `r`; lawful on the context, its value at `y` not self-visible at `2`. -/
noncomputable def topSection (C : ℕ) : Fin 5 → Label.{u} :=
  lab (labelAdd (Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u})) 1) (topCode C 5) (topCode C 3)

theorem isSelfVisible_topCode (C : ℕ) {n k : ℕ} (hk : k ≤ n) :
    IsSelfVisible k (topCode.{u} C n) :=
  isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) hk

theorem not_isSelfVisible_topSection_y (C : ℕ) : ¬ IsSelfVisible 2 (topSection.{u} C 0) := by
  change ¬ IsSelfVisible 2 (labelAdd (Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u})) 1)
  rw [labelAdd, isSelfVisible_coe_add_natCast_iff (Label.isSuccPrelimit_omega0_mul _)]
  omega

theorem topCode_lt (C : ℕ) {n n' : ℕ} (h : n < n') : topCode.{u} C n < topCode C n' := by
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  exact (add_lt_add_iff_left _).mpr (by exact_mod_cast h)

theorem topCode_lt_labelAdd (C n : ℕ) :
    topCode.{u} C n < labelAdd (Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u})) 1 := by
  rw [labelAdd, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  calc Ordinal.omega0 * (C : Ordinal.{u}) + (n : Ordinal.{u})
      < Ordinal.omega0 * (C : Ordinal.{u}) + Ordinal.omega0 :=
        (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 n)
    _ = Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u}) := by rw [Nat.cast_succ, mul_add_one]
    _ ≤ _ := le_self_add

/-- **The prescription above the cut is lawful on the context.** -/
theorem isLawful_topSection (C : ℕ) : (ctx ω).rows.IsLawful (topSection.{u} C) := by
  have h35 := topCode_lt.{u} C (show 3 < 5 by omega)
  refine isLawful_lab (isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) (by omega))
    (isSelfVisible_topCode C (by omega)) (isSelfVisible_topCode C (by omega))
    (topCode_lt_labelAdd C 5).le ?_
  rw [min_eq_right ((h35.trans (topCode_lt_labelAdd C 5)).le), min_eq_right h35.le]

/-- **The prescription agrees with the two-level state of `sep` at the cap `ω * C + 4`.** -/
theorem min_topSection_eq (C : ℕ) (x : Fin 5) :
    min (topSection.{u} C x) (topCode C 4) =
      min (Label.twoLevel (topCode C 3) (topCode C 4) (sep ω x)) (topCode C 4) := by
  have hω3 : (Ordinal.omega0 : Label.{u}) ≤ labelAdd Ordinal.omega0 3 := by
    rw [labelAdd, WithBot.coe_le_coe, WithTop.coe_le_coe]; exact le_self_add
  have h3ω : labelAdd (0 : Ordinal.{u}) 3 < (Ordinal.omega0 : Label.{u}) := by
    rw [labelAdd, zero_add, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    exact Ordinal.natCast_lt_omega0 3
  have h34 := topCode_lt.{u} C (show 3 < 4 by omega)
  have h45 := topCode_lt.{u} C (show 4 < 5 by omega)
  fin_cases x
  · change min (labelAdd _ 1) _ = min (Label.twoLevel _ _ (labelAdd Ordinal.omega0 3)) _
    rw [Label.twoLevel_of_le hω3, min_self, min_eq_right (topCode_lt_labelAdd C 4).le]
  · change min ⊥ _ = min (Label.twoLevel _ _ ⊥) _
    rw [(Label.isWitness_twoLevel (K := 2) (isSelfVisible_topCode C (by omega))
      (isSelfVisible_topCode C (by omega)) h34.le).map_bot]
  · change min (labelAdd _ 1) _ = min (Label.twoLevel _ _ (labelAdd Ordinal.omega0 3)) _
    rw [Label.twoLevel_of_le hω3, min_self, min_eq_right (topCode_lt_labelAdd C 4).le]
  · change min (topCode C 5) _ = min (Label.twoLevel _ _ (labelAdd Ordinal.omega0 3)) _
    rw [Label.twoLevel_of_le hω3, min_self, min_eq_right h45.le]
  · change min (topCode C 3) _ = min (Label.twoLevel _ _ (labelAdd 0 3)) _
    rw [Label.twoLevel_of_lt (WithBot.coe_ne_bot) h3ω]

/-- The top cut at the input, for the first coatom type given up to equality. -/
theorem exists_topCut_aux {I : Seed.{u} ω 1} {t' : StageType.{u} ω 2} (hI : I.left = t')
    {p : StageType.{u} ω 1} {hte : restrictFace ((𝕣).trans Fin.castSuccEmb) t' = some p}
    {d : StageType.{u} ω 2} (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {u' : Fin t'.card → Label.{u}} (hu' : t'.rows.IsLawful u') {xo : Fin t'.card}
    (hxo : t'.toCellScheme.grade xo = 2) (ho : (Ordinal.omega0 : Label.{u}) ≤ u' xo) :
    ∃ R₀ ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q))
        (1 + 2),
      (∀ x : Fin t'.card, R₀ (I.attachCtxCell 𝕣 (Fin.cast (congrArg (fun t ↦ t.card) hI.symm) x)) =
        Label.twoLevel (topCode (I.attachment 𝕣).card 3) (topCode (I.attachment 𝕣).card 4)
          (u' x)) ∧
      I.ReachableCut 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q))
        (I.seedGridBound 𝕣) 2 (topCode (I.attachment 𝕣).card 4) := by
  subst hI
  set C := (I.attachment 𝕣).card with hC
  obtain ⟨P, hPl, hPu, hadm⟩ := I.exists_admitted_completion_attachment hte hdp hdA hpair hrel hu'
  have hPA : I.attachAdmits 𝕣 hdA Q (1 + 2) P :=
    Seed.attachAdmits_of_admitsOnClass hdA hQ (1 + 2) (by
      rw [show (fun x ↦ P (I.attachCtxCell 𝕣 x)) = u' from funext hPu]
      exact hadm)
  have hv₁ : IsSelfVisible (1 + 2) (topCode.{u} C 3) := isSelfVisible_topCode C (by omega)
  have hv₂ : IsSelfVisible (1 + 2) (topCode.{u} C 4) := isSelfVisible_topCode C (by omega)
  have h12 := (topCode_lt.{u} C (show 3 < 4 by omega)).le
  have hw := Label.isWitness_twoLevel hv₁ hv₂ h12
  have hb (a : Fin (I.attachment 𝕣).card) :
      Label.twoLevel (topCode C 3) (topCode C 4) (P a) = ⊥ ↔ P a = ⊥ :=
    Label.twoLevel_eq_bot_iff WithBot.coe_ne_bot WithBot.coe_ne_bot
  have hgr (a : Fin (I.attachment 𝕣).card) : (I.attachment 𝕣).toCellScheme.grade a ≤ 1 + 2 :=
    (I.attachmentType 𝕣).grade_le a
  have hA : ∀ k R, I.attachAdmits 𝕣 hdA Q (k + 3) R → I.attachAdmits 𝕣 hdA Q (k + 2) R :=
    fun k R h ↦ I.attachAdmits_succ 𝕣 hdA Q k R h
  have hR₀ : (Label.twoLevel (topCode C 3) (topCode C 4) ∘ P) ∈
      (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA Q) (1 + 2) := by
    refine Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ ?_,
      hPl.map_of_bot_iff hPl hgr hw hb, Seed.attachAdmits_comp hdA hQ hPA hw hb _⟩
    have hcode (n : ℕ) (hn : n < 3 * (1 + 2) + C + 3) : topCode.{u} C n ∈ I.seedValues 𝕣 :=
      I.codeSet_subset_seedValues 𝕣 (mem_codeSet le_rfl hn)
    rcases Label.twoLevel_mem (v₁ := topCode C 3) (v₂ := topCode C 4) (P a) with h | h | h <;>
      change Label.twoLevel _ _ (P a) ∈ _ <;> rw [h]
    · exact I.bot_mem_seedValues 𝕣
    · exact hcode 3 (by omega)
    · exact hcode 4 (by omega)
  refine ⟨_, hR₀, fun x ↦ congrArg (Label.twoLevel _ _) (hPu x), ?_⟩
  obtain ⟨u, -, hu, hrowA, -⟩ := Scheme.LadderBaseData.exists_cell_of_mem_towerCat
    (B := I.attachmentBase 𝕣) (Γ := I.seedValues 𝕣) (A := I.attachAdmits 𝕣 hdA Q)
    (B' := I.seedGridBound 𝕣) (G := fun k ↦ Scheme.heightSet (I.seedValues 𝕣) (I.seedGridBound 𝕣) k)
    (I.card_le_seedHeight 𝕣) 0 1 le_rfl
    (Scheme.LadderBaseData.towerCat_mono hA (by omega : 0 ≤ 1) hR₀)
  have hgo : (I.attachment 𝕣).toCellScheme.grade (I.attachCtxCell 𝕣 xo) = 2 :=
    (Seed.grade_attachCtxCell xo).trans hxo
  refine ⟨u, hu, I.attachCtxCell 𝕣 xo, hgo.le, ?_, isSelfVisible_topCode C (by omega)⟩
  refine (Scheme.rowAt_mirror_castAdd _ _).trans ((hrowA _ hgo.le).trans ?_)
  have hPo : P (I.attachCtxCell 𝕣 xo) = u' xo := hPu xo
  change Label.twoLevel _ _ (P (I.attachCtxCell 𝕣 xo)) = _
  rw [hPo]
  exact Label.twoLevel_of_le ho

/-- **The gate at the input fails: a reachable cut at the top of the values with no code above
it.**  At every seed of the input, at the choice of the assembly, at the grade `2`:

* the state `R₀ = twoLevel (ω * C + 3) (ω * C + 4) ∘ P₀` (with `P₀` the admitted completion of
  `sep ω`) is a state of the catalogue, equal on the context to the two-level state of `sep ω`;
* its cut `ω * C + 4` is reachable (`Seed.ReachableCut`): the row of its cell at `(univ, 2)` at
  the context cell `o`; and it is the only label in `(R₀ r, R₀ o] = (ω * C + 3, ω * C + 4]`;
* the lawful context section `topSection C` agrees with the two-level state of `sep ω` capped at
  `ω * C + 4` (`TieInstance.min_topSection_eq`) and carries at `y` a label above the cap not
  self-visible at `2`;
* no value of `Seed.seedValues` above the cut is read by a witness bounded by `2` as that label
  (`Seed.not_exists_code_above_top`). -/
theorem gradeGate_fails (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω)) :
    ∃ R₀ ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ req ω))
        (1 + 2),
      (∀ x : Fin (ctx.{u} ω).card,
        R₀ (I.attachCtxCell 𝕣 (Fin.cast (congrArg (fun t ↦ t.card) hI.symm) x)) =
          Label.twoLevel (topCode (I.attachment 𝕣).card 3) (topCode (I.attachment 𝕣).card 4)
            (sep ω x)) ∧
      I.ReachableCut 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ req ω))
        (I.seedGridBound 𝕣) 2 (topCode (I.attachment 𝕣).card 4) ∧
      (∀ x : Label.{u}, topCode (I.attachment 𝕣).card 3 < x → x ≤ topCode (I.attachment 𝕣).card 4 →
        x = topCode (I.attachment 𝕣).card 4) ∧
      (ctx ω).rows.IsLawful (topSection.{u} (I.attachment 𝕣).card) ∧
      ¬ IsSelfVisible 2 (topSection.{u} (I.attachment 𝕣).card 0) ∧
      topCode (I.attachment 𝕣).card 4 < topSection.{u} (I.attachment 𝕣).card 0 ∧
      ¬ ∃ y ∈ I.seedValues 𝕣, topCode (I.attachment 𝕣).card 4 < y ∧
        ∃ θ : Label.{u} → Label.{u}, IsWitness (stepSuppressor 2) θ ∧
          θ y = topSection.{u} (I.attachment 𝕣).card 0 := by
  obtain ⟨R₀, hR₀, hctx, hcut⟩ := exists_topCut_aux hI (hte := restrictFace_ctx_root ω)
    (don_mem_cofaces ω).2 hdA (correctAt_req ω) (classCalibrated_req ω)
    (hasRelativeLiftOnClass_req ω) (isLawful_sep ω) (xo := cellO.{u} ω) rfl (by
      change (Ordinal.omega0 : Label.{u}) ≤ labelAdd Ordinal.omega0 3
      rw [labelAdd, WithBot.coe_le_coe, WithTop.coe_le_coe]; exact le_self_add)
  refine ⟨R₀, hR₀, hctx, hcut, fun x h1 h2 ↦ ?_, isLawful_topSection _,
    not_isSelfVisible_topSection_y _, topCode_lt_labelAdd _ 4, ?_⟩
  · exact Label.eq_of_lt_of_le_succ (n := 3) h1 h2
  · exact Seed.not_exists_code_above_top (I := I) (g := 𝕣)
      (topCode_lt.{u} _ (show 2 < 4 by omega)).le (not_isSelfVisible_topSection_y _)

end TieInstance

end VaughtConjecture

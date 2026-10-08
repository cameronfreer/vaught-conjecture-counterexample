/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerSpreadTops

/-!
# Refining servers at the grade `1`

Roadmap, Layer 3 ((R3) of the table of 3.4).

* **Shifts across a block** (`Label.shiftL`, `Label.subL`, defined here;
  `Label.isWitness_piecewise`, compiled): a map that is one witness below a multiple `θ` of `ω`
  and another above it is a witness.
* **The lexicographic combination** (`CellScheme.Rows.IsLawfulBelow.lex`, compiled): `a` below `θ`
  and `θ + q` above is lawful when `a` and `q` are and `a` is at least `θ` exactly where `q` is at
  least a cap.  Availability is through `q` above `θ`; no uniqueness of graded indices is used.
* **The refining server at the grade `1`** (`TowerProfile.exists_one_of_target`, compiled): for
  every target `q` on the amalgam lawful below `(univ, 1)`, agreeing with the reading mark `e`
  capped at `h` and at least `V` where at least `h`, with a cell of grade `1` where `e` is at least
  `h`, some labelling of the profile layer lawful below `(univ, 1)` is `q` on the amalgam, agrees
  with `e` capped at `h`, and is at least `V` where `e` is at least `h`.  It is the lexicographic
  raise of an available entry across the block of its least code at the cells at least the cap,
  extended through the cells of full scope (`Scheme.exists_extension_fieldLayer`) and decoded
  piecewise.  This is the statement "a refining server exists at the grade `1`".

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal


/-! ### Shifting labels past a block -/


namespace Label

/-- Visibility replacement commutes with adding a multiple of `ω` on the left. -/
theorem ord_visibilityReplace_omega0_mul_add (β y : Ordinal.{u}) (k i : ℕ) :
    _root_.Ordinal.visibilityReplace k i (ω * β + y) =
      ω * β + _root_.Ordinal.visibilityReplace k i y := by
  unfold _root_.Ordinal.visibilityReplace
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero, Ordinal.mul_add_mod_self, mul_add,
    add_assoc]

/-- The **shift** of a label by an ordinal `o` on the left: `o + x` on the ordinals, `⊥` and `⊤`
kept. -/
noncomputable def shiftL (o : Ordinal.{u}) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (o + ·))

/-- The **subtraction** of an ordinal `o` from a label: `x - o` on the ordinals, `⊥` and `⊤`
kept. -/
noncomputable def subL (o : Ordinal.{u}) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (· - o))

@[simp] theorem shiftL_coe (o x : Ordinal.{u}) : shiftL o (x : Label.{u}) = ((o + x : Ordinal.{u}) :
    Label.{u}) := rfl

@[simp] theorem shiftL_top (o : Ordinal.{u}) : shiftL o (⊤ : Label.{u}) = ⊤ := rfl

@[simp] theorem shiftL_bot (o : Ordinal.{u}) : shiftL o (⊥ : Label.{u}) = ⊥ := rfl

@[simp] theorem subL_coe (o x : Ordinal.{u}) : subL o (x : Label.{u}) = ((x - o : Ordinal.{u}) :
    Label.{u}) := rfl

@[simp] theorem subL_top (o : Ordinal.{u}) : subL o (⊤ : Label.{u}) = ⊤ := rfl

theorem monotone_shiftL (o : Ordinal.{u}) : Monotone (shiftL o) := by
  intro x y hxy
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top => rw [top_le_iff.mp hxy]
  | coe a =>
    induction y using recBotCoeTop with
    | bot => exact absurd hxy (not_le.mpr (WithBot.bot_lt_coe _))
    | top => exact le_top
    | coe b =>
      rw [shiftL_coe, shiftL_coe]
      have hab : a ≤ b := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hxy)
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((add_le_add_iff_left o).mpr hab))

theorem coe_le_shiftL (o : Ordinal.{u}) {x : Label.{u}} (hx : x ≠ ⊥) :
    ((o : Ordinal.{u}) : Label.{u}) ≤ shiftL o x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe a => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

theorem shiftL_visibilityReplace (β : Ordinal.{u}) (k i : ℕ) (x : Label.{u}) :
    shiftL (ω * β) (visibilityReplace k i x) = visibilityReplace k i (shiftL (ω * β) x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe a =>
    rw [visibilityReplace_coe, shiftL_coe, shiftL_coe, visibilityReplace_coe,
      ord_visibilityReplace_omega0_mul_add]

theorem subL_shiftL (o : Ordinal.{u}) (x : Label.{u}) : subL o (shiftL o x) = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe a => rw [shiftL_coe, subL_coe, Ordinal.add_sub_cancel]

theorem shiftL_subL {o : Ordinal.{u}} {x : Label.{u}} (hx : ((o : Ordinal.{u}) : Label.{u}) ≤ x) :
    shiftL o (subL o x) = x := by
  induction x using recBotCoeTop with
  | bot => exact absurd hx (not_le.mpr (WithBot.bot_lt_coe _))
  | top => rfl
  | coe a =>
    rw [subL_coe, shiftL_coe,
      Ordinal.add_sub_cancel_of_le (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hx))]

theorem subL_visibilityReplace {β : Ordinal.{u}} {x : Label.{u}}
    (hx : (((ω * β : Ordinal.{u})) : Label.{u}) ≤ x) (k i : ℕ) :
    subL (ω * β) (visibilityReplace k i x) = visibilityReplace k i (subL (ω * β) x) := by
  conv_lhs => rw [← shiftL_subL hx, ← shiftL_visibilityReplace, subL_shiftL]

theorem monotone_subL (o : Ordinal.{u}) : Monotone (subL o) := by
  intro x y hxy
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top => rw [top_le_iff.mp hxy]
  | coe a =>
    induction y using recBotCoeTop with
    | bot => exact absurd hxy (not_le.mpr (WithBot.bot_lt_coe _))
    | top => exact le_top
    | coe b =>
      rw [subL_coe, subL_coe]
      have hab : a ≤ b := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hxy)
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (Ordinal.sub_le.mpr (hab.trans (Ordinal.le_add_sub b o))))

/-- Visibility replacement keeps a label below a multiple of `ω` exactly when it was below. -/
theorem visibilityReplace_lt_omega0_mul_iff (β : Ordinal.{u}) (k i : ℕ) (x : Label.{u}) :
    visibilityReplace k i x < (((ω * β : Ordinal.{u})) : Label.{u}) ↔
      x < (((ω * β : Ordinal.{u})) : Label.{u}) := by
  rw [← not_le, ← not_le, omega0_mul_le_visibilityReplace_iff]

/-- **A piecewise witness across a block.**  Let `c` and `L` be witnesses bounded by grade `m`,
`θ = ω * β`, and `U` monotone, commuting with visibility replacement at the thresholds `k ≤ m` on
the labels with `θ ≤ c x`, never `⊥` there, and above `L` across the threshold.  If `L x = ⊥`
keeps `c` below `θ` after every visibility replacement, then `x ↦ if c x < θ then L x else U x`
is a witness bounded by grade `m`. -/
theorem isWitness_piecewise {m : ℕ} {β : Ordinal.{u}} {c L U : Label.{u} → Label.{u}}
    (hc : IsWitness (stepSuppressor m) c) (hL : IsWitness (stepSuppressor m) L)
    (hUm : ∀ x y, (((ω * β : Ordinal.{u})) : Label.{u}) ≤ c x → x ≤ y → U x ≤ U y)
    (hUcomm : ∀ x, (((ω * β : Ordinal.{u})) : Label.{u}) ≤ c x → ∀ k ≤ m, ∀ i ≤ k,
      U (visibilityReplace k i x) = visibilityReplace k i (U x))
    (hUne : ∀ x, (((ω * β : Ordinal.{u})) : Label.{u}) ≤ c x → U x ≠ ⊥)
    (hLU : ∀ x y, c x < (((ω * β : Ordinal.{u})) : Label.{u}) →
      (((ω * β : Ordinal.{u})) : Label.{u}) ≤ c y → L x ≤ U y)
    (hcbot : ∀ x, c x < (((ω * β : Ordinal.{u})) : Label.{u}) → L x = ⊥ → ∀ k, ∀ i ≤ k,
      c (visibilityReplace k i x) < (((ω * β : Ordinal.{u})) : Label.{u})) :
    IsWitness (stepSuppressor m)
      (fun x ↦ if c x < (((ω * β : Ordinal.{u})) : Label.{u}) then L x else U x) where
  antitone := (IsWitness.id_step m).antitone
  isSelfVisible := (IsWitness.id_step m).isSelfVisible
  map_bot := by
    have : c ⊥ < (((ω * β : Ordinal.{u})) : Label.{u}) := by
      rw [hc.map_bot]; exact WithBot.bot_lt_coe _
    simp only [this, ↓reduceIte, hL.map_bot]
  monotone := by
    intro x y hxy
    dsimp only
    by_cases hx : c x < (((ω * β : Ordinal.{u})) : Label.{u})
    · simp only [hx, ↓reduceIte]
      by_cases hy : c y < (((ω * β : Ordinal.{u})) : Label.{u})
      · simp only [hy, ↓reduceIte]; exact hL.monotone hxy
      · simp only [hy, ↓reduceIte]; exact hLU x y hx (not_lt.mp hy)
    · have hy : ¬ c y < (((ω * β : Ordinal.{u})) : Label.{u}) := fun hy ↦
        hx ((hc.monotone hxy).trans_lt hy)
      simp only [hx, hy, ↓reduceIte]
      exact hUm x y (not_lt.mp hx) hxy
  visibilityReplace_comm := by
    intro x k hk i hi
    by_cases hkm : k ≤ m
    · have hcv : c (visibilityReplace k i x) = visibilityReplace k i (c x) :=
        hc.visibilityReplace_comm x k (by simp [hkm]) i hi
      by_cases hx : c x < (((ω * β : Ordinal.{u})) : Label.{u})
      · have hx' : c (visibilityReplace k i x) < (((ω * β : Ordinal.{u})) : Label.{u}) := by
          rw [hcv, visibilityReplace_lt_omega0_mul_iff]; exact hx
        simp only [hx, hx', ↓reduceIte]
        exact hL.visibilityReplace_comm x k (by simp [hkm]) i hi
      · have hx' : ¬ c (visibilityReplace k i x) < (((ω * β : Ordinal.{u})) : Label.{u}) := by
          rw [hcv, visibilityReplace_lt_omega0_mul_iff]; exact hx
        simp only [hx, hx', ↓reduceIte]
        exact hUcomm x (not_lt.mp hx) k hkm i hi
    · -- above the bound the suppressor asks the value to be `⊥`
      rw [stepSuppressor_of_lt (not_le.mp hkm), le_bot_iff] at hk
      by_cases hx : c x < (((ω * β : Ordinal.{u})) : Label.{u})
      · simp only [hx, ↓reduceIte] at hk ⊢
        simp only [hcbot x hx hk k i hi, ↓reduceIte, hk, visibilityReplace_bot]
        exact hL.apply_visibilityReplace_eq_bot hk k hi
      · simp only [hx, ↓reduceIte] at hk
        exact absurd hk (hUne x (not_lt.mp hx))

end Label


namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **The lexicographic combination of two lawful labellings across a block.**  Let `a` and `q`
be lawful below `X`, `θ = ω * β`, and `h` positive and self-visible at a bound `K` of the grades,
such that `a` is at least `θ` exactly where `q` is at least `h`.  Then the labelling that is `a`
below `θ` and `θ + q` elsewhere is lawful below `X`.  Below `θ` it reads as `a`; above, as `a`
below `θ` and as `θ + q` from `θ` (a piecewise witness, `Label.isWitness_piecewise`); a cell above
`θ` is available through `q`, and its available cell is above `θ` again. -/
theorem IsLawfulBelow.lex {X : Finset α × ℕ} {a q : ι → Label.{u}}
    (ha : R.IsLawfulBelow X fun d ↦ a d) (hq : R.IsLawfulBelow X fun d ↦ q d)
    {β : Ordinal.{u}} {h : Label.{u}} {K : ℕ} (hh : IsSelfVisible K h) (hhb : ⊥ < h)
    (hK : ∀ d ∈ D.below X, D.grade d ≤ K)
    (hlink : ∀ d ∈ D.below X, (((ω * β : Ordinal.{u})) : Label.{u}) ≤ a d ↔ h ≤ q d) :
    R.IsLawfulBelow X fun d ↦
      if a d < (((ω * β : Ordinal.{u})) : Label.{u}) then a d else shiftL (ω * β) (q d) := by
  classical
  set θ : Label.{u} := (((ω * β : Ordinal.{u})) : Label.{u}) with hθ
  obtain ⟨hao, hal, haa⟩ := isLawfulBelow_iff_forall.mp ha
  obtain ⟨hqo, hql, hqa⟩ := isLawfulBelow_iff_forall.mp hq
  have hsh (y : Label.{u}) (hy : y ≠ ⊥) : θ ≤ shiftL (ω * β) y := coe_le_shiftL _ hy
  have hqne (d : ι) (hd : d ∈ D.below X) (hda : θ ≤ a d) : q d ≠ ⊥ :=
    (hhb.trans_le ((hlink d hd).mp hda)).ne'
  have hbelow {d : ι} {s : ι} (hds : D.gradedIndex d ≤ D.gradedIndex s) (hs : s ∈ D.below X) :
      d ∈ D.below X := (le_trans hds hs : D.gradedIndex d ≤ X)
  refine (isLawfulBelow_iff_forall (w := fun d ↦ if a d < θ then a d else shiftL (ω * β) (q d))).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · -- orderly
    by_cases hda : a d < θ
    · simp only [hda, ↓reduceIte]; exact hao d hd
    · simp only [hda, ↓reduceIte]
      have hv := hqo d hd
      unfold IsSelfVisible at hv ⊢
      rw [← shiftL_visibilityReplace, hv]
  · -- locality
    by_cases hsa : a s < θ
    · have heq : (fun d : D.below (D.gradedIndex s) ↦
          min ((fun d ↦ if a d < θ then a d else shiftL (ω * β) (q d)) d.1)
            ((fun d ↦ if a d < θ then a d else shiftL (ω * β) (q d)) s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (a d.1) (a s) := by
        funext d
        simp only [hsa, ↓reduceIte]
        by_cases hda : a d < θ
        · simp only [hda, ↓reduceIte]
        · simp only [hda, ↓reduceIte]
          have hdX : (d : ι) ∈ D.below X := hbelow d.2 hs
          have h1 : a s < shiftL (ω * β) (q d) :=
            hsa.trans_le (hsh _ (hqne d hdX (not_lt.mp hda)))
          rw [min_eq_right h1.le, min_eq_right (hsa.le.trans (not_lt.mp hda))]
      rw [heq]
      exact hal s hs
    · have hsθ : θ ≤ a s := not_lt.mp hsa
      have hmax : ∀ d : D.below (D.gradedIndex s), D.grade d ≤
          D.grade (⟨s, D.mem_below_gradedIndex s⟩ : D.below (D.gradedIndex s)) := fun d ↦ d.2.2
      obtain ⟨τa, hτa, -, hτaE⟩ := (hal s hs).exists_isWitness_capped hmax (hao s hs)
      obtain ⟨τq, hτq, -, hτqE⟩ := (hql s hs).exists_isWitness_capped hmax (hqo s hs)
      have hgs : D.grade s ≤ K := hK s hs
      have hσ := isWitness_piecewise (m := D.grade s) (β := β) (c := τa) (L := τa)
        (U := fun x ↦ shiftL (ω * β) (max h (τq x))) hτa hτa
        (fun x y _ hxy ↦ monotone_shiftL _ (max_le_max le_rfl (hτq.monotone hxy)))
        (fun x _ k hk i hi ↦ by
          rw [← shiftL_visibilityReplace, visibilityReplace_max hi,
            (hh.mono (hk.trans hgs)).visibilityReplace_eq,
            hτq.visibilityReplace_comm x k (by simp [hk]) i hi])
        (fun x _ ↦ (lt_of_lt_of_le (WithBot.bot_lt_coe _)
          (hsh _ (hhb.trans_le (le_max_left _ _)).ne')).ne')
        (fun x y hx _ ↦ hx.le.trans (hsh _ (hhb.trans_le (le_max_left _ _)).ne'))
        (fun x _ hx k i hi ↦ by
          rw [hτa.apply_visibilityReplace_eq_bot hx k hi]; exact WithBot.bot_lt_coe _)
      refine ⟨_, _, hσ, fun d ↦ ?_⟩
      change min (if a d < θ then a d else shiftL (ω * β) (q d))
          (if a s < θ then a s else shiftL (ω * β) (q s)) =
        min (if τa (R.row s d) < θ then τa (R.row s d)
          else shiftL (ω * β) (max h (τq (R.row s d))))
          (stepSuppressor (D.grade s) (D.grade d.1))
      rw [stepSuppressor_of_le (show D.grade d.1 ≤ D.grade s from d.2.2), min_top_right, hτaE d,
        hτqE d]
      simp only [hsa, ↓reduceIte]
      have hdX : (d : ι) ∈ D.below X := hbelow d.2 hs
      by_cases hda : a d < θ
      · have hm' : min (a d) (a s) = a d := min_eq_left (hda.le.trans hsθ)
        simp only [hda, ↓reduceIte, hm']
        exact min_eq_left (hda.le.trans (hsh _ (hqne s hs hsθ)))
      · have hm : ¬ min (a d) (a s) < θ := not_lt.mpr (le_min (not_lt.mp hda) hsθ)
        simp only [hda, hm, ↓reduceIte]
        rw [max_eq_right (le_min ((hlink d hdX).mp (not_lt.mp hda)) ((hlink s hs).mp hsθ))]
        exact ((monotone_shiftL _).map_min).symm
  · -- availability
    have hsX : s ∈ D.below X :=
      hbelow ((D.gradedIndex_le_iff).mpr ⟨hst, hg.le⟩) ht
    by_cases hsa : a s < θ
    · obtain ⟨u, hu, hle⟩ := haa s t ht hst hg
      have huX : u ∈ D.below X := (le_of_eq hu).trans ht
      refine ⟨u, hu, ?_⟩
      simp only [hsa, ↓reduceIte]
      by_cases hua : a u < θ
      · simp only [hua, ↓reduceIte]; exact hle
      · simp only [hua, ↓reduceIte]
        exact hsa.le.trans (hsh _ (hqne u huX (not_lt.mp hua)))
    · obtain ⟨u, hu, hle⟩ := hqa s t ht hst hg
      have huX : u ∈ D.below X := (le_of_eq hu).trans ht
      have hqu : h ≤ q u := ((hlink s hsX).mp (not_lt.mp hsa)).trans hle
      have hua : ¬ a u < θ := not_lt.mpr ((hlink u huX).mpr hqu)
      refine ⟨u, hu, ?_⟩
      simp only [hsa, hua, ↓reduceIte]
      exact monotone_shiftL _ hle

end CellScheme.Rows

namespace TowerProfile

open TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **Lawfulness below `(univ, 1)` passes from the layer at the grade `1` to the profile layer.** -/
theorem isLawfulBelow_scheme_of_one {w : Fin (scheme I).card → Label.{u}}
    (hw : (I.tower 1).rows.IsLawfulBelow (univ, 1) fun d ↦ w (oneCell I d)) :
    (scheme I).rows.IsLawfulBelow (univ, 1) fun d ↦ w d := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower 1) (k := 2)
    (M := ((I.tower 1).catalogue 2).card)
    (r := fun i ↦ (I.tower 1).fieldRow 2 ((I.tower 1).catalogueEntry 2 i))
    (h := I.not_univ_succ_le_tower 1) (v := fun d ↦ w (Fin.castAdd _ d))
    (X := ((univ : Finset (Fin 5)), 1)) (fun h ↦ absurd h.2 (by omega))).mpr hw
  exact (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower 2) (k := 3) (M := mult I)
    (r := fun i ↦ fieldLab I (entry I i)) (h := I.not_univ_succ_le_tower 2) (v := w)
    (X := ((univ : Finset (Fin 5)), 1)) (fun h ↦ absurd h.2 (by omega))).mpr h1

/-- Every cell of the profile layer below `(univ, 1)` is a cell of the layer at the grade `1`. -/
theorem exists_oneCell_eq {x : Fin (scheme I).card}
    (hx : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
    ∃ y, oneCell I y = x := by
  have h1 : (x : ℕ) < (I.tower 2).card :=
    Scheme.lt_card_of_mem_below (S := I.tower 2) (k := 3) (M := mult I)
      (fun h ↦ absurd h.2 (by omega)) hx
  have hx2 : (⟨x, h1⟩ : Fin (I.tower 2).card) ∈ (I.tower 2).toCellScheme.below
      ((univ : Finset (Fin 5)), 1) := by
    rw [CellScheme.mem_below, ← Scheme.appendFullCellsScheme_gradedIndex_of_lt (k := 3)
      (M := mult I) h1]
    exact hx
  have h2 : (x : ℕ) < (I.tower 1).card :=
    Scheme.lt_card_of_mem_below (S := I.tower 1) (k := 2) (M := ((I.tower 1).catalogue 2).card)
      (fun h ↦ absurd h.2 (by omega)) hx2
  exact ⟨⟨x, h2⟩, Fin.ext rfl⟩

/-- A positive label self-visible at `1` is at least `1`. -/
theorem one_le_of_isSelfVisible {x : Label.{u}} (hx : IsSelfVisible 1 x) (hx0 : ⊥ < x) :
    (1 : Label.{u}) ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact absurd hx0 (lt_irrefl _)
  | top => exact le_top
  | coe o =>
    have h1 := isSelfVisible_coe.mp hx
    have ho : o ≠ 0 := fun h0 ↦ by
      rw [h0, Ordinal.zero_mod] at h1
      exact absurd h1 (by simp)
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (Order.one_le_iff_ne_zero.mpr ho))

/-- **The fill at the grade `1` for any target (a refining server at the grade `1`).**  Let `e` be
lawful below `(univ, 1)` in the profile layer, `h` a positive cap self-visible at `4`, `V ≥ h`
self-visible at `1`, and `q` a labelling of the amalgam lawful below `(univ, 1)` agreeing with `e`
capped at `h`, at least `V` where it is at least `h`, with some cell of grade `1` where `e` is at
least `h`.  Then some labelling of the profile layer lawful below `(univ, 1)` is `q` on the
amalgam, agrees with `e` capped at `h`, and is at least `V` where `e` is at least `h`.

An available entry `a₀` at a cell where `e` is at least `h` reads, through the witness `τ₀` of
`e` there, every cell where `e` is at least `h` at a code at least `ω * β + 1`, the least such
code, and every other cell of the amalgam below `ω * β`.  The **lexicographic raise**
(`CellScheme.Rows.IsLawfulBelow.lex`): `a₀` below `ω * β` and `ω * β + q` above, agreeing with
`a₀` capped at `ω * β + 1`, extends through the cells of full scope agreeing with the field row of
`a₀` capped there (`Scheme.exists_extension_fieldLayer`), and the piecewise decoder
(`Label.isWitness_piecewise`) reads it as `e` below `ω * β` (raised to `V` from `h`) and as
`q` above. -/
theorem exists_one_of_target {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 1) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {V : Label.{u}} (hV : IsSelfVisible 1 V) (hhV : h ≤ V)
    {q : Fin I.amalgam.card → Label.{u}}
    (hq : (I.tower 0).rows.IsLawfulBelow (univ, 1) fun d ↦ q d.1)
    (hqe : ∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → min (q d) h = min (e (embed3 I d)) h)
    (hqV : ∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → h ≤ q d → V ≤ q d)
    {z₀ : Fin I.amalgam.card} (hz₀ : I.amalgam.toCellScheme.grade z₀ = 1)
    (hez₀ : h ≤ e (embed3 I z₀)) :
    ∃ w₁ : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 1) (fun d ↦ w₁ d) ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → w₁ (embed3 I d) = q d) ∧
      (∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1),
        min (w₁ x) h = min (e x) h) ∧
      ∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1), h ≤ e x → V ≤ w₁ x := by
  classical
  have hh1 : IsSelfVisible 1 h := hh.mono (by omega)
  have hh0 : h ≠ ⊥ := hhb.ne'
  -- `e` on the layer at the grade `1`
  have he₁ := isLawfulBelow_one_of_scheme he
  -- a cell of full scope at least `h`, and its entry `a₀`
  obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq
    (Scheme.orbitCode_splice_bot_mem_catalogue (S := I.tower 0) (k := 1) (p := fun _ ↦ ⊥)
      (CellScheme.Rows.isLawfulBelow_const_bot _))
  obtain ⟨-, -, havail⟩ :=
    (CellScheme.Rows.isLawfulBelow_iff_forall (w := fun d ↦ e (oneCell I d))).mp he₁
  obtain ⟨u, hu, hzu⟩ := havail (Fin.castAdd _ z₀) (Fin.natAdd _ i₀)
    (Scheme.natAdd_mem_below (hS := I.not_univ_succ_le_tower 0) i₀)
    (by
      have h1 : (I.tower 1).toCellScheme.scope (Fin.natAdd _ i₀) = univ :=
        Scheme.appendFullCellsScheme_scope_natAdd (I.tower 0) 1 _ i₀
      rw [h1]; exact subset_univ _)
    (by
      have g1 : (I.tower 1).toCellScheme.gradedIndex (Fin.castAdd _ z₀) =
          I.amalgam.toCellScheme.gradedIndex z₀ :=
        Scheme.appendFullCellsScheme_gradedIndex_castAdd (I.tower 0) 1 _ z₀
      have g2 : (I.tower 1).toCellScheme.gradedIndex (Fin.natAdd _ i₀) =
          ((univ : Finset (Fin 5)), 1) :=
        Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 0) 1 _ i₀
      exact (congrArg Prod.snd g1).trans (hz₀.trans (congrArg Prod.snd g2).symm))
  have hu' : (I.tower 1).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 1) :=
    hu.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 0) 1 _ i₀)
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (hS := I.not_univ_succ_le_tower 0) hu'
  set a₀ := (I.tower 0).catalogueEntry 1 i with ha₀def
  have ha₀ : a₀ ∈ (I.tower 0).catalogue 1 := Scheme.catalogueEntry_mem i
  have heu : h ≤ e (oneCell I (Fin.natAdd _ i)) := hez₀.trans hzu
  -- the witness of `e` at that cell
  obtain ⟨τ₀, hτ₀, hτ₀h, hτ₀E⟩ := CellScheme.Rows.exists_isWitness_rowBelow
    (R := (I.tower 1).rows) hu' he₁ (c := h) hh1 heu
  have hfr (x : Fin (I.tower 1).card)
      (hx : x ∈ (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
      τ₀ ((I.tower 0).fieldRow 1 a₀ x) = min (e (oneCell I x)) h := by
    have := hτ₀E ⟨x, hx⟩
    have h2 := Scheme.fieldLayer_row_natAdd (S := I.tower 0) (k := 1)
      (hS := I.not_univ_succ_le_tower 0) i ⟨x, le_trans hx hu'.ge⟩
    exact (congrArg τ₀ h2).symm.trans this
  -- the amalgam inside the layer
  have hpos (d : Fin I.amalgam.card) : 1 ≤ I.amalgam.toCellScheme.grade d :=
    I.amalgam.isWellFormed.isWellFormed.grade_pos d
  have hcast (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      (Fin.castAdd _ d : Fin (I.tower 1).card) ∈
        (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1) := by
    have g1 : (I.tower 1).toCellScheme.gradedIndex (Fin.castAdd _ d) =
        I.amalgam.toCellScheme.gradedIndex d :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd (I.tower 0) 1 _ d
    exact (CellScheme.mem_below _).mpr (g1.trans_le
      ((I.amalgam.toCellScheme.gradedIndex_le_iff).mpr ⟨subset_univ _, hd⟩))
  have hτa (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      τ₀ (a₀ d) = min (e (embed3 I d)) h := by
    exact (congrArg τ₀ (Scheme.fieldRow_castAdd (S := I.tower 0) (k := 1) a₀ d)).symm.trans
      (hfr _ (hcast d hd))
  have hvis1 (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      IsSelfVisible 1 (a₀ d) := by
    have := (Scheme.mem_catalogue.mp ha₀).1.orderly d
    have hg1 : (I.tower 0).toCellScheme.grade d = 1 := le_antisymm hd (hpos d)
    rwa [hg1] at this
  -- the least code at the cells where `e` is at least `h`
  set Z : Finset (Fin I.amalgam.card) := (univ : Finset (Fin I.amalgam.card)).filter
    fun z ↦ I.amalgam.toCellScheme.grade z ≤ 1 ∧ h ≤ τ₀ (a₀ z) with hZdef
  have hz₀Z : z₀ ∈ Z := mem_filter.mpr ⟨mem_univ _, hz₀.le, by
    rw [hτa z₀ hz₀.le, min_eq_right hez₀]⟩
  obtain ⟨zm, hzmZ, hzm⟩ := Z.exists_min_image a₀ ⟨z₀, hz₀Z⟩
  obtain ⟨hgzm, hτzm⟩ := (mem_filter.mp hzmZ).2
  have hzm0 : a₀ zm ≠ ⊥ := fun h0 ↦ by
    rw [h0, hτ₀.map_bot] at hτzm
    exact hh0 (le_bot_iff.mp hτzm)
  obtain ⟨β, hβ⟩ := exists_eq_omega0_mul_add_one (Scheme.mem_codeGrid_of_mem_catalogue ha₀ zm)
    (hvis1 zm hgzm) hzm0
  set θ : Label.{u} := (((ω * β : Ordinal.{u})) : Label.{u}) with hθdef
  have hθc : θ ≤ (((ω * β + 1 : Ordinal.{u})) : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
  have hlinke (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      θ ≤ a₀ d ↔ h ≤ e (embed3 I d) := by
    constructor
    · intro hθd
      have h1 : a₀ zm ≤ a₀ d := hβ ▸ omega0_mul_add_one_le (hvis1 d hd) hθd
      have h2 := hτzm.trans (hτ₀.monotone h1)
      rw [hτa d hd] at h2
      exact (le_min_iff.mp h2).1
    · intro hed
      have hdZ : d ∈ Z := mem_filter.mpr ⟨mem_univ _, hd, by rw [hτa d hd, min_eq_right hed]⟩
      exact hθc.trans (hβ ▸ hzm d hdZ)
  have hlink (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      θ ≤ a₀ d ↔ h ≤ q d :=
    (hlinke d hd).trans ⟨fun hed ↦ Label.le_of_min_eq_of_le' (hqe d hd) hed,
      fun hqd ↦ Label.le_of_min_eq_of_le' (hqe d hd).symm hqd⟩
  -- the lexicographic raise
  set c : Label.{u} := (((ω * β + 1 : Ordinal.{u})) : Label.{u}) with hcdef
  have hc : IsSelfVisible 1 c := hβ ▸ hvis1 zm hgzm
  have ha₀l : (I.tower 0).rows.IsLawfulBelow (univ, 1) fun d ↦ a₀ d.1 :=
    (Scheme.mem_catalogue.mp ha₀).1.isLawfulBelow _
  have hW := CellScheme.Rows.IsLawfulBelow.lex ha₀l hq (β := β) (K := 1) hh1 hhb
    (fun d hd ↦ hd.2) (fun d hd ↦ hlink d hd.2)
  have hq1 (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) (hθd : θ ≤ a₀ d) :
      c ≤ shiftL (ω * β) (q d) := by
    have hqd : h ≤ q d := (hlink d hd).mp hθd
    have h1 : (((1 : Ordinal.{u})) : Label.{u}) ≤ q d :=
      (one_le_of_isSelfVisible hh1 hhb).trans hqd
    exact monotone_shiftL _ h1
  have hag (d : Fin I.amalgam.card) (hd : (I.tower 0).toCellScheme.grade d ≤ 1) :
      min (if a₀ d < θ then a₀ d else shiftL (ω * β) (q d)) c = min (a₀ d) c := by
    by_cases had : a₀ d < θ
    · simp only [had, ↓reduceIte]
    · simp only [had, ↓reduceIte]
      have hθd : θ ≤ a₀ d := not_lt.mp had
      rw [min_eq_right (hq1 d hd hθd), min_eq_right (omega0_mul_add_one_le (hvis1 d hd) hθd)]
  obtain ⟨r, hr, hrW, hrc⟩ := Scheme.exists_extension_fieldLayer (S := I.tower 0) (k := 1)
    (hS := I.not_univ_succ_le_tower 0) hW ha₀ (h := c) hc (WithBot.bot_lt_coe _)
    (.inr fun d hd ↦ le_antisymm hd (hpos d)) hag
  -- the decoder
  have hV0 : V ≠ ⊥ := (hhb.trans_le hhV).ne'
  have hL : IsWitness (stepSuppressor 1) ((fun t ↦ min (raise h t) V) ∘ τ₀) :=
    hτ₀.comp_of_bot_reflecting ((isWitness_raise (K := 1) (hh.mono (by omega)) hhb).min_const hV)
      fun t ht ↦ eq_bot_of_raise_eq_bot ((min_eq_bot.mp ht).resolve_right hV0)
  have hD := isWitness_piecewise (m := 1) (β := β) (c := id)
    (L := (fun t ↦ min (raise h t) V) ∘ τ₀) (U := fun t ↦ max V (subL (ω * β) t))
    (IsWitness.id_step 1) hL
    (fun x y _ hxy ↦ max_le_max le_rfl (monotone_subL _ hxy))
    (fun x hx k hk i hi ↦ by
      have hx' : (((ω * β : Ordinal.{u})) : Label.{u}) ≤ x := hx
      rw [subL_visibilityReplace hx', visibilityReplace_max hi,
        (hV.mono hk).visibilityReplace_eq])
    (fun x _ ↦ (hhb.trans_le (hhV.trans (le_max_left _ _))).ne')
    (fun x y _ _ ↦ (min_le_right _ _).trans (le_max_left _ _))
    (fun x hx _ k i hi ↦ by
      change visibilityReplace k i x < θ
      rw [visibilityReplace_lt_omega0_mul_iff]
      exact hx)
  set D : Label.{u} → Label.{u} := fun t ↦
    if id t < θ then ((fun t ↦ min (raise h t) V) ∘ τ₀) t else max V (subL (ω * β) t) with hDdef
  -- the decoded extension, cell by cell
  have hcell (x : (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
      min (D (r x)) h = min (e (oneCell I x)) h ∧ (h ≤ e (oneCell I x) → V ≤ D (r x)) := by
    have hfrx := hfr x.1 x.2
    by_cases hrx : r x < θ
    · have hrc' := hrc x
      have hrxc : r x < c := hrx.trans_le hθc
      have hfx : (I.tower 0).fieldRow 1 a₀ x.1 = r x := by
        rw [min_eq_left hrxc.le] at hrc'
        rcases lt_or_ge ((I.tower 0).fieldRow 1 a₀ x.1) c with hl | hl
        · rw [min_eq_left hl.le] at hrc'
          exact hrc'.symm
        · rw [min_eq_right hl] at hrc'
          exact absurd hrc' hrxc.ne
      have hDx : D (r x) = min (raise h (τ₀ (r x))) V := by
        simp only [hDdef, id, hrx, ↓reduceIte, Function.comp]
      rw [hDx, ← hfx, hfrx]
      by_cases hex : h ≤ e (oneCell I x)
      · rw [min_eq_right hex, show raise h h = ⊤ from ite_eq_left le_rfl, min_top_left,
          min_eq_right hhV]
        exact ⟨rfl, fun _ ↦ le_rfl⟩
      · have hlt := not_le.mp hex
        rw [min_eq_left hlt.le, show raise h (e (oneCell I x)) = e (oneCell I x) from
          ite_eq_right hex, min_eq_left (hlt.le.trans hhV)]
        exact ⟨min_eq_left hlt.le, fun h' ↦ absurd h' hex⟩
    · have hθr : θ ≤ r x := not_lt.mp hrx
      have hg1 : (I.tower 1).toCellScheme.grade x = 1 := by
        have h1 : (I.tower 1).toCellScheme.grade x ≤ 1 := x.2.2
        have h2 := isWellFormed_scheme.isWellFormed.grade_pos (oneCell I x.1)
        rw [← CellScheme.gradedIndex_snd, gradedIndex_oneCell, CellScheme.gradedIndex_snd] at h2
        omega
      have hvr : IsSelfVisible 1 (r x) := by
        have := (CellScheme.Rows.isLawfulBelow_iff.mp hr).orderly x
        change IsSelfVisible ((I.tower 1).toCellScheme.grade x.1) (r x) at this
        rwa [hg1] at this
      have hcr : c ≤ r x := omega0_mul_add_one_le hvr hθr
      have hcf : c ≤ (I.tower 0).fieldRow 1 a₀ x.1 := by
        have := hrc x
        rw [min_eq_right hcr] at this
        exact min_eq_right_iff.mp this.symm
      have hex : h ≤ e (oneCell I x) := by
        have h1 := hτzm.trans (hτ₀.monotone (hβ ▸ hcf))
        rw [hfrx] at h1
        exact (le_min_iff.mp h1).1
      have hDV : V ≤ D (r x) := by
        simp only [hDdef, id, hrx, ↓reduceIte]
        exact le_max_left _ _
      exact ⟨by rw [min_eq_right (hhV.trans hDV), min_eq_right hex], fun _ ↦ hDV⟩
  -- lawful on the layer at the grade `1`, by the companion `e`
  have hlaw : (I.tower 1).rows.IsLawfulBelow (univ, 1) (D ∘ r) :=
    hr.map_of_bot_iff he₁ (fun d ↦ d.2.2) hD fun x ↦ eq_bot_iff_of_min_eq (hcell x).1 hh0
  -- the labelling of the profile layer
  set rt : Fin (I.tower 1).card → Label.{u} := fun x ↦
    if hx : x ∈ (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1) then D (r ⟨x, hx⟩)
    else ⊥ with hrtdef
  set w₁ : Fin (scheme I).card → Label.{u} := fun x ↦
    if hx : (x : ℕ) < (I.tower 1).card then rt ⟨x, hx⟩ else ⊥ with hw₁def
  have hw₁one (y : Fin (I.tower 1).card) : w₁ (oneCell I y) = rt y := by
    have hy : ((oneCell I y : Fin (scheme I).card) : ℕ) < (I.tower 1).card := y.2
    simp only [hw₁def, hy, ↓reduceDIte]
    rfl
  have hrt (x : (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
      rt x.1 = D (r x) := by
    simp only [hrtdef, x.2, ↓reduceDIte]
    rfl
  have hmemone {x : Fin (scheme I).card}
      (hx : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 1)) :
      ∃ y : (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1), oneCell I y.1 = x := by
    obtain ⟨y, rfl⟩ := exists_oneCell_eq hx
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [CellScheme.mem_below, ← gradedIndex_oneCell]
    exact hx
  refine ⟨w₁, isLawfulBelow_scheme_of_one ?_, fun d hd ↦ ?_, fun x hx ↦ ?_, fun x hx hex ↦ ?_⟩
  · have heq : (fun d : (I.tower 1).toCellScheme.below ((univ : Finset (Fin 5)), 1) ↦
        w₁ (oneCell I d)) = D ∘ r := funext fun d ↦ (hw₁one d).trans (hrt d)
    rw [heq]
    exact hlaw
  · change w₁ (oneCell I (Fin.castAdd ((I.tower 0).catalogue 1).card
      (d : Fin (I.tower 0).card))) = q d
    refine (hw₁one _).trans ((hrt ⟨_, hcast d hd⟩).trans ((congrArg D (hrW d hd)).trans ?_))
    by_cases had : a₀ d < θ
    · have hed : ¬ h ≤ e (embed3 I d) := fun hed ↦ had.not_ge ((hlinke d hd).mpr hed)
      have hlt := not_le.mp hed
      simp only [had, ↓reduceIte, hDdef, id, Function.comp, hτa d hd, min_eq_left hlt.le,
        show raise h (e (embed3 I d)) = e (embed3 I d) from ite_eq_right hed,
        min_eq_left (hlt.le.trans hhV)]
      exact (Label.eq_of_min_eq_of_lt (hqe d hd).symm hlt).symm
    · have hθd : θ ≤ a₀ d := not_lt.mp had
      have hqd : h ≤ q d := (hlink d hd).mp hθd
      have hns : ¬ shiftL (ω * β) (q d) < θ :=
        not_lt.mpr (coe_le_shiftL _ (hhb.trans_le hqd).ne')
      simp only [had, ↓reduceIte, hDdef, id, hns, subL_shiftL]
      exact max_eq_right (hqV d hd hqd)
  · obtain ⟨y, rfl⟩ := hmemone hx
    rw [hw₁one, hrt]
    exact (hcell y).1
  · obtain ⟨y, rfl⟩ := hmemone hx
    rw [hw₁one, hrt]
    exact (hcell y).2 hex

end TowerProfile

end VaughtConjecture

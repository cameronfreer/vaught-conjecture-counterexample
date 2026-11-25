/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.ProcessRank.SpanTests

/-!
# Legality of the test pairs

Process rank `ω₁`, the finite span of mutual rigidity: the two concrete pairs of
`VaughtConjecture.ProcessRank.SpanTests` are legal stage types at the stage `ω ^ 2`.

**The test scheme is legal** (`ProcessRank.isLegal_testScheme`).

* Coded: every row value is `ω * k + j < ω ^ 2`.
* Consistent: every row is the test row restricted, and the test row is a lawful section
  (`ProcessRank.isLawful_testRow`).
* Complete: the graded faces are `({0}, 1)`, `({1}, 1)`, `({0, 1}, 1)` and `({0, 1}, 2)`, each the
  graded index of a cell.
* Bountiful: by `CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst` only the lifts at a fixed
  grade remain, and those within one face are automatic (`CellScheme.Rows.cappedLift_of_fst_eq`).
  The two others go from `({0}, 1)` and from `({1}, 1)` to `({0, 1}, 1)`.  A labelling `w` is lawful
  below `({0, 1}, 1)` exactly when `w c₀` and `w c₁` are self-visible at the grade one,
  `w c₀₁ = w c₀` and `w c₁ ≤ w c₀` (`ProcessRank.isLawfulBelow_univ_one_iff`; the cell `c₀₁` reads
  `c₀` and itself through the same row value, and the converse uses the witness constant on the
  classes `⊥`, `[0, ω * 2)` and `[ω * 2, ⊤]`).  The lifts are `(p, min (q c₁) p, p)` from `c₀` and
  `(max (q c₀) p, p, max (q c₀) p)` from `c₁`; a prescribed value below the old one is at least
  the cap.

**The label sections** (`ProcessRank.k2Pair`, `ProcessRank.k1Pair`).  The witness is
`ProcessRank.lowTop L`: the map `L` below `ω * 2` and `⊤` from `ω * 2` on, with `L` the identity
for the left types and the shift `x ↦ ω + x` for the right ones (it commutes with visibility
replacement, `ProcessRank.visibilityReplace_shiftOmega`).  The suppressor is `⊤`, except at the
apex of the pair with `K = 1`, where it is the apex label `μ` up to the grade two and `⊥` above.

Proved: `K2PairTarget` and `K1PairTarget`.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- The test scheme has cells. -/
instance : NeZero testScheme.{u}.card := ⟨by decide⟩

/-! ### Values of the test row -/

theorem omega0_add_one_lt_omega0_mul_two :
    ((ω + 1 : Ordinal.{u}) : Label.{u}) < ((ω * 2 : Ordinal.{u}) : Label.{u}) := by
  have hlt : (ω : Ordinal.{u}) < ω * 2 := by simp
  have h := (isSuccPrelimit_omega0_mul.{u} 2).succ_lt (by exact_mod_cast hlt)
  rw [Order.succ_eq_add_one] at h
  exact_mod_cast h

theorem omega0_mul_two_le_add (j : Ordinal.{u}) :
    ((ω * 2 : Ordinal.{u}) : Label.{u}) ≤ ((ω * 2 + j : Ordinal.{u}) : Label.{u}) := by
  exact_mod_cast le_self_add

theorem isSuccPrelimit_omega0_mul_two : Order.IsSuccPrelimit (ω * 2 : Ordinal.{u}) := by
  simpa using isSuccPrelimit_omega0_mul.{u} 2

theorem omega0_mul_add_lt_omega0_sq (k j : ℕ) :
    (ω * k + j : Ordinal.{u}) < ω ^ 2 := by
  have : (ω * k + j : Ordinal.{u}) < ω * ω + 0 :=
    omega0_mul_add_natCast_lt (Ordinal.natCast_lt_omega0 k) j 0
  rwa [add_zero, ← pow_two] at this

theorem testRow_lt_omega0_sq (d : Fin 4) :
    testRow.{u} d < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have h21 : (ω * 2 + 1 : Ordinal.{u}) < ω ^ 2 := by
    simpa using omega0_mul_add_lt_omega0_sq.{u} 2 1
  have h11 : (ω + 1 : Ordinal.{u}) < ω ^ 2 := by
    simpa using omega0_mul_add_lt_omega0_sq.{u} 1 1
  have h22 : (ω * 2 + 2 : Ordinal.{u}) < ω ^ 2 := by
    simpa using omega0_mul_add_lt_omega0_sq.{u} 2 2
  fin_cases d
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h21)
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h11)
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h21)
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h22)

/-! ### Witnesses -/

/-- The shift `x ↦ ω + x` of labels. -/
noncomputable def shiftOmega : Label.{u} → Label.{u} :=
  recBotCoeTop ⊥ (fun o ↦ ((ω + o : Ordinal.{u}) : Label.{u})) ⊤

@[simp] theorem shiftOmega_bot : shiftOmega (⊥ : Label.{u}) = ⊥ := rfl

@[simp] theorem shiftOmega_coe (o : Ordinal.{u}) :
    shiftOmega (o : Label.{u}) = ((ω + o : Ordinal.{u}) : Label.{u}) := rfl

@[simp] theorem shiftOmega_top : shiftOmega (⊤ : Label.{u}) = ⊤ := rfl

theorem monotone_shiftOmega : Monotone shiftOmega.{u} := by
  intro x y hxy
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | top =>
    obtain rfl : y = ⊤ := top_le_iff.mp hxy
    exact le_rfl
  | coe o =>
    induction y using recBotCoeTop with
    | bot => exact absurd hxy (not_le.mpr (WithBot.bot_lt_coe _))
    | top => exact le_top
    | coe o' =>
      have h : o ≤ o' := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hxy)
      simp only [shiftOmega_coe]
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by gcongr))

/-- **The shift by `ω` commutes with visibility replacement.** -/
theorem visibilityReplace_shiftOmega (k i : ℕ) (x : Label.{u}) :
    visibilityReplace k i (shiftOmega x) = shiftOmega (visibilityReplace k i x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
    have hμ' : Order.IsSuccPrelimit (ω + μ : Ordinal.{u}) :=
      Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr
        (dvd_add dvd_rfl (Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ))
    rw [shiftOmega_coe, ← add_assoc, visibilityReplace_coe_add hμ', visibilityReplace_coe_add hμ]
    split_ifs <;> rw [shiftOmega_coe, add_assoc]

/-- The map `L` below `ω * 2` and `⊤` from `ω * 2` on. -/
noncomputable def lowTop (L : Label.{u} → Label.{u}) (t : Label.{u}) : Label.{u} :=
  if t < ((ω * 2 : Ordinal.{u}) : Label.{u}) then L t else ⊤

/-- **The witness `lowTop L`**, for `L` monotone, fixing `⊥` and commuting with every visibility
replacement, with any suppressor. -/
theorem isWitness_lowTop {L : Label.{u} → Label.{u}} (hL0 : L ⊥ = ⊥) (hLm : Monotone L)
    (hLc : ∀ k i x, L (visibilityReplace k i x) = visibilityReplace k i (L x))
    {g : ℕ → Label.{u}} (hg : Antitone g) (hgv : ∀ n, IsSelfVisible n (g n)) :
    IsWitness g (lowTop L) where
  antitone := hg
  isSelfVisible := hgv
  map_bot := by
    unfold lowTop
    rw [ite_eq_left (WithBot.bot_lt_coe _), hL0]
  monotone := by
    intro x y hxy
    unfold lowTop
    split_ifs with hx hy hy
    · exact hLm hxy
    · exact le_top
    · exact absurd (lt_of_le_of_lt hxy hy) hx
    · exact le_rfl
  visibilityReplace_comm x k _ i _ := by
    unfold lowTop
    by_cases hx : x < ((ω * 2 : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left ((visibilityReplace_lt_iff isSuccPrelimit_omega0_mul_two).mpr hx),
        ite_eq_left hx]
      exact hLc k i x
    · rw [ite_eq_right (mt (visibilityReplace_lt_iff isSuccPrelimit_omega0_mul_two).mp hx),
        ite_eq_right hx]
      rfl

theorem lowTop_testRow_one (L : Label.{u} → Label.{u}) :
    lowTop L (testRow (1 : Fin 4)) = L ((ω + 1 : Ordinal.{u}) : Label.{u}) :=
  ite_eq_left omega0_add_one_lt_omega0_mul_two

theorem lowTop_testRow_of_ne {d : Fin 4} (hd : d ≠ 1) (L : Label.{u} → Label.{u}) :
    lowTop L (testRow d) = ⊤ := by
  unfold lowTop
  rw [ite_eq_right]
  fin_cases d
  · exact not_lt.mpr (omega0_mul_two_le_add 1)
  · exact absurd rfl hd
  · exact not_lt.mpr (omega0_mul_two_le_add 1)
  · exact not_lt.mpr (omega0_mul_two_le_add 2)

/-- The suppressor equal to `μ` up to the grade two and `⊥` above. -/
noncomputable def apexSuppressor (μ : Label.{u}) (n : ℕ) : Label.{u} := if n ≤ 2 then μ else ⊥

theorem antitone_apexSuppressor (μ : Label.{u}) : Antitone (apexSuppressor μ) := by
  intro n m hnm
  unfold apexSuppressor
  split_ifs <;> first | exact le_rfl | exact bot_le | omega

theorem isSelfVisible_apexSuppressor {μ : Label.{u}} (hμ : IsSelfVisible 2 μ) (n : ℕ) :
    IsSelfVisible n (apexSuppressor μ n) := by
  unfold apexSuppressor
  split_ifs with h
  · exact hμ.mono h
  · exact isSelfVisible_bot n

theorem lowTop_testRow (L : Label.{u} → Label.{u}) (d : Fin 4) :
    lowTop L (testRow d) = if (d : ℕ) = 1 then L ((ω + 1 : Ordinal.{u}) : Label.{u}) else ⊤ := by
  split_ifs with h
  · obtain rfl : d = 1 := Fin.ext h
    exact lowTop_testRow_one L
  · exact lowTop_testRow_of_ne (fun h' ↦ h (by rw [h']; rfl)) L

theorem shiftOmega_omega0_add_one :
    shiftOmega ((ω + 1 : Ordinal.{u}) : Label.{u}) = ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) := by
  rw [shiftOmega_coe, ← add_assoc, Ordinal.mul_two]

/-! ### Lawful labellings of the test scheme -/

/-- **Lawfulness of a labelling of the test scheme from a witness `lowTop L`.** -/
theorem isLawful_test {ℓ : Fin 4 → Label.{u}} {L : Label.{u} → Label.{u}} (hL0 : L ⊥ = ⊥)
    (hLm : Monotone L) (hLc : ∀ k i x, L (visibilityReplace k i x) = visibilityReplace k i (L x))
    (hord : ∀ d, IsSelfVisible (testGrade d) (ℓ d))
    (hav : ∀ s t : Fin 4, testScope s ⊆ testScope t → testGrade s = testGrade t → ℓ s ≤ ℓ t)
    (g : Fin 4 → ℕ → Label.{u}) (hg : ∀ s, Antitone (g s))
    (hgv : ∀ s n, IsSelfVisible n (g s n))
    (hloc : ∀ s d : Fin 4, testScope d ⊆ testScope s → testGrade d ≤ testGrade s →
      min (ℓ d) (ℓ s) = min (lowTop L (testRow d)) (g s (testGrade d))) :
    testScheme.{u}.rows.IsLawful ℓ where
  orderly d := hord d
  locality s := ⟨g s, lowTop L, isWitness_lowTop hL0 hLm hLc (hg s) (hgv s),
    fun d ↦ hloc s d.1 d.2.1 d.2.2⟩
  availability s t hst hgr := ⟨t, rfl, hav s t hst hgr⟩

/-- The class map: `⊥` at `⊥`, `a` below `ω * 2`, `b` from `ω * 2` on. -/
noncomputable def classMap (a b t : Label.{u}) : Label.{u} :=
  if t = ⊥ then ⊥ else if t < ((ω * 2 : Ordinal.{u}) : Label.{u}) then a else b

theorem classMap_visibilityReplace (a b : Label.{u}) (k i : ℕ) (t : Label.{u}) :
    classMap a b (visibilityReplace k i t) = classMap a b t := by
  unfold classMap
  simp only [visibilityReplace_eq_bot_iff,
    visibilityReplace_lt_iff isSuccPrelimit_omega0_mul_two]

theorem isWitness_classMap {a b : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hab : a ≤ b) : IsWitness (stepSuppressor 1) (classMap a b) where
  antitone := (IsWitness.id_step 1).antitone
  isSelfVisible := (IsWitness.id_step 1).isSelfVisible
  map_bot := ite_eq_left rfl
  monotone := by
    intro x y hxy
    unfold classMap
    by_cases hx : x = ⊥
    · rw [ite_eq_left hx]
      exact bot_le
    have hy : y ≠ ⊥ := fun h ↦ hx (le_bot_iff.mp (h ▸ hxy))
    rw [ite_eq_right hx, ite_eq_right hy]
    by_cases hy2 : y < ((ω * 2 : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (lt_of_le_of_lt hxy hy2), ite_eq_left hy2]
    · rw [ite_eq_right hy2]
      split_ifs
      exacts [hab, le_rfl]
  visibilityReplace_comm x k hbound i hi := by
    rw [classMap_visibilityReplace]
    have hsv : IsSelfVisible 1 (classMap a b x) := by
      unfold classMap
      split_ifs
      exacts [isSelfVisible_bot 1, ha, hb]
    by_cases hk : k ≤ 1
    · exact ((hsv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hbound
      rw [hbound, visibilityReplace_bot]

theorem classMap_testRow (a b : Label.{u}) (d : Fin 4) :
    classMap a b (testRow d) = if (d : ℕ) = 1 then a else b := by
  unfold classMap
  rw [ite_eq_right (testRow_ne_bot d)]
  fin_cases d
  · exact ite_eq_right (not_lt.mpr (omega0_mul_two_le_add 1))
  · exact ite_eq_left omega0_add_one_lt_omega0_mul_two
  · exact ite_eq_right (not_lt.mpr (omega0_mul_two_le_add 1))
  · exact ite_eq_right (not_lt.mpr (omega0_mul_two_le_add 2))

theorem eq_two_of_gradedIndex (u : Fin 4) (h : (testScope u, testGrade u) = (univ, 1)) : u = 2 := by
  revert u
  decide

/-- **Lawful labellings below `({0, 1}, 1)`**: `w c₀` and `w c₁` self-visible at the grade one,
`w c₀₁ = w c₀` and `w c₁ ≤ w c₀`. -/
theorem isLawfulBelow_univ_one_iff (w : Fin 4 → Label.{u}) :
    testScheme.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d.1) ↔
      IsSelfVisible 1 (w 0) ∧ IsSelfVisible 1 (w 1) ∧ w 2 = w 0 ∧ w 1 ≤ w 0 := by
  have hm (d : Fin 4) (hd : testGrade d ≤ 1) :
      d ∈ testScheme.{u}.toCellScheme.below ((univ : Finset (Fin 2)), 1) :=
    mem_below_testScheme.mpr ⟨subset_univ _, hd⟩
  constructor
  · intro hw
    obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
    have h20 : w 2 ≤ w 0 := by
      obtain ⟨g, σ, -, heq⟩ := hl 2 (hm 2 (by decide))
      have h0 := heq ⟨0, mem_below_testScheme.mpr (by decide)⟩
      have h2 := heq ⟨2, mem_below_testScheme.mpr (by decide)⟩
      have h : min (w 0) (w 2) = w 2 := h0.trans (h2.symm.trans (min_self _))
      exact min_eq_right_iff.mp h
    have hav (s : Fin 4) (hs : testScope s ⊆ testScope 2) (hg : testGrade s = testGrade 2) :
        w s ≤ w 2 := by
      obtain ⟨u, hu, hle⟩ := ha s 2 (hm 2 (by decide)) hs hg
      rwa [eq_two_of_gradedIndex u hu] at hle
    exact ⟨ho 0 (hm 0 (by decide)), ho 1 (hm 1 (by decide)),
      le_antisymm h20 (hav 0 (by decide) rfl), (hav 1 (by decide) rfl).trans h20⟩
  · rintro ⟨h0, h1, h20, h10⟩
    have hcases (d : Fin 4) (hd : testGrade d ≤ 1) : d = 0 ∨ d = 1 ∨ d = 2 := by
      revert d
      decide
    refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_,
      fun s t ht hst hg ↦ ⟨t, rfl, ?_⟩⟩
    · rcases hcases d hd.2 with rfl | rfl | rfl
      exacts [h0, h1, h20 ▸ h0]
    · refine ⟨stepSuppressor 1, classMap (w 1) (w 0), isWitness_classMap h1 h0 h10, fun d ↦ ?_⟩
      obtain ⟨d, hd⟩ := d
      change testScope d ⊆ testScope s ∧ testGrade d ≤ testGrade s at hd
      change min (w d) (w s) = min (classMap (w 1) (w 0) (testRow d))
        (stepSuppressor 1 (testGrade d))
      rw [stepSuppressor_of_le (hd.2.trans hs.2), min_top_right, classMap_testRow (w 1) (w 0) d]
      rcases hcases s hs.2 with rfl | rfl | rfl <;>
        rcases hcases d (hd.2.trans hs.2) with rfl | rfl | rfl <;>
        first
        | exact absurd hd (by decide)
        | (rw [min_self]; rfl)
        | (rw [h20, min_self]; rfl)
        | (rw [h20, min_eq_left h10]; rfl)
    · have htg : testGrade t ≤ 1 := ht.2
      change testScope s ⊆ testScope t at hst
      change testGrade s = testGrade t at hg
      change w s ≤ w t
      rcases hcases t htg with rfl | rfl | rfl <;> revert hst hg <;> revert s <;>
        (intro s; fin_cases s <;> intro hst hg <;>
          first
          | exact le_rfl
          | exact absurd hst (by decide)
          | exact absurd hg (by decide)
          | exact h20.symm ▸ le_rfl
          | exact h20 ▸ h10)

/-! ### The test scheme is legal -/

theorem le_of_min_eq_of_lt {a b c : Label.{u}} (h : min a c = min b c) (hba : b < a) : c ≤ b := by
  by_contra hcb
  rw [not_le] at hcb
  rw [min_eq_left hcb.le] at h
  rcases le_total a c with hac | hac
  · rw [min_eq_left hac] at h
    exact absurd h hba.ne'
  · rw [min_eq_right hac] at h
    exact absurd h hcb.ne'

theorem eq_zero_or_one_or_two (d : Fin 4) (hd : testGrade d ≤ 1) : d = 0 ∨ d = 1 ∨ d = 2 := by
  revert d
  decide

/-- **The capped lift from `({0}, 1)` to `({0, 1}, 1)`**: `(p, min (q c₁) p, p)`. -/
theorem cappedLift_testScheme_zero :
    testScheme.{u}.rows.CappedLift (X := (({0} : Finset (Fin 2)), 1))
      (Y := ((univ : Finset (Fin 2)), 1)) ⟨subset_univ _, le_rfl⟩ := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c _ p q hp hq hpq ↦ ?_
  set Q : Fin 4 → Label.{u} := CellScheme.Rows.extendBot _ q with hQdef
  have hQq (d : Fin 4) (hd : d ∈ testScheme.{u}.toCellScheme.below ((univ : Finset (Fin 2)), 1)) :
      Q d = q ⟨d, hd⟩ := CellScheme.Rows.extendBot_of_mem q hd
  obtain ⟨-, hQ1, hQ20, hQ10⟩ :=
    (isLawfulBelow_univ_one_iff Q).mp (CellScheme.Rows.isLawfulBelow_extendBot.mpr hq)
  have hm0 : (0 : Fin 4) ∈ testScheme.{u}.toCellScheme.below (({0} : Finset (Fin 2)), 1) :=
    mem_below_testScheme.mpr (by decide)
  set P0 := p ⟨0, hm0⟩ with hP0def
  have hP0 : IsSelfVisible 1 P0 := hp.orderly ⟨0, hm0⟩
  have hagr : min (Q 0) c = min P0 c := by
    rw [hQq 0 (mem_below_testScheme.mpr (by decide))]
    exact hpq ⟨0, hm0⟩
  set W : Fin 4 → Label.{u} := ![P0, min (Q 1) P0, P0, ⊥] with hW
  refine ⟨fun d ↦ W d.1, (isLawfulBelow_univ_one_iff W).mpr
    ⟨hP0, hQ1.min hP0, rfl, min_le_right _ _⟩, fun d ↦ ?_, fun d ↦ ?_⟩
  · obtain ⟨d, hd⟩ := d
    change min (W d) c = min (q ⟨d, hd⟩) c
    rw [← hQq d hd]
    rcases eq_zero_or_one_or_two d hd.2 with rfl | rfl | rfl
    · exact hagr.symm
    · change min (min (Q 1) P0) c = min (Q 1) c
      by_cases h : Q 1 ≤ P0
      · rw [min_eq_left h]
      · have hlt : P0 < Q 1 := not_le.mp h
        have hc0 : c ≤ P0 := le_of_min_eq_of_lt hagr (lt_of_lt_of_le hlt hQ10)
        rw [min_eq_right hlt.le, min_eq_right hc0, min_eq_right (hc0.trans hlt.le)]
    · change min P0 c = min (Q 2) c
      rw [hQ20]
      exact hagr.symm
  · obtain ⟨d, hd⟩ := d
    obtain rfl : d = 0 :=
      (by decide : ∀ d : Fin 4, testScope d ⊆ {0} ∧ testGrade d ≤ 1 → d = 0) d hd
    rfl

/-- **The capped lift from `({1}, 1)` to `({0, 1}, 1)`**: `(max (q c₀) p, p, max (q c₀) p)`. -/
theorem cappedLift_testScheme_one :
    testScheme.{u}.rows.CappedLift (X := (({1} : Finset (Fin 2)), 1))
      (Y := ((univ : Finset (Fin 2)), 1)) ⟨subset_univ _, le_rfl⟩ := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists _).mpr fun c _ p q hp hq hpq ↦ ?_
  set Q : Fin 4 → Label.{u} := CellScheme.Rows.extendBot _ q with hQdef
  have hQq (d : Fin 4) (hd : d ∈ testScheme.{u}.toCellScheme.below ((univ : Finset (Fin 2)), 1)) :
      Q d = q ⟨d, hd⟩ := CellScheme.Rows.extendBot_of_mem q hd
  obtain ⟨hQ0, -, hQ20, hQ10⟩ :=
    (isLawfulBelow_univ_one_iff Q).mp (CellScheme.Rows.isLawfulBelow_extendBot.mpr hq)
  have hm1 : (1 : Fin 4) ∈ testScheme.{u}.toCellScheme.below (({1} : Finset (Fin 2)), 1) :=
    mem_below_testScheme.mpr (by decide)
  set P1 := p ⟨1, hm1⟩ with hP1def
  have hP1 : IsSelfVisible 1 P1 := hp.orderly ⟨1, hm1⟩
  have hagr : min (Q 1) c = min P1 c := by
    rw [hQq 1 (mem_below_testScheme.mpr (by decide))]
    exact hpq ⟨1, hm1⟩
  set M := max (Q 0) P1 with hM
  have hMc : min M c = min (Q 0) c := by
    by_cases h : P1 ≤ Q 0
    · rw [hM, max_eq_left h]
    · have hlt : Q 0 < P1 := not_le.mp h
      have hc1 : c ≤ Q 1 := le_of_min_eq_of_lt hagr.symm (lt_of_le_of_lt hQ10 hlt)
      rw [hM, max_eq_right hlt.le, min_eq_right (hc1.trans (hQ10.trans hlt.le)),
        min_eq_right (hc1.trans hQ10)]
  set W : Fin 4 → Label.{u} := ![M, P1, M, ⊥] with hW
  refine ⟨fun d ↦ W d.1, (isLawfulBelow_univ_one_iff W).mpr
    ⟨hQ0.max hP1, hP1, rfl, le_max_right _ _⟩, fun d ↦ ?_, fun d ↦ ?_⟩
  · obtain ⟨d, hd⟩ := d
    change min (W d) c = min (q ⟨d, hd⟩) c
    rw [← hQq d hd]
    rcases eq_zero_or_one_or_two d hd.2 with rfl | rfl | rfl
    · exact hMc
    · exact hagr.symm
    · change min M c = min (Q 2) c
      rw [hQ20]
      exact hMc
  · obtain ⟨d, hd⟩ := d
    obtain rfl : d = 1 :=
      (by decide : ∀ d : Fin 4, testScope d ⊆ {1} ∧ testGrade d ≤ 1 → d = 1) d hd
    rfl

theorem isBountiful_testScheme : testScheme.{u}.rows.IsBountiful := by
  refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  by_cases hXY : X.1 = Y.1
  · exact CellScheme.Rows.cappedLift_of_fst_eq _ hXY
  obtain ⟨B, k⟩ := X
  obtain ⟨C, l⟩ := Y
  obtain ⟨-, hk0, hk⟩ := hX
  have hB := (by decide : ∀ B C : Finset (Fin 2), B ⊆ C → B ≠ C → 0 < #B →
    (B = {0} ∨ B = {1}) ∧ C = univ) B C h.1 hXY (hk0.trans_le hk)
  change k ≤ #B at hk
  obtain ⟨hB | hB, rfl⟩ := hB <;> subst hB
  · obtain rfl : k = 1 := le_antisymm (hk.trans_eq (by decide)) hk0
    exact cappedLift_testScheme_zero
  · obtain rfl : k = 1 := le_antisymm (hk.trans_eq (by decide)) hk0
    exact cappedLift_testScheme_one

theorem isComplete_testScheme : testScheme.{u}.toCellScheme.IsComplete := by
  rintro ⟨B, k⟩ ⟨-, hk0, hk⟩
  change k ≤ #B at hk
  have hB2 : #B ≤ 2 := (card_le_univ B).trans_eq (Fintype.card_fin 2)
  obtain ⟨d, hd⟩ := (by decide : ∀ B : Finset (Fin 2), ∀ k : Fin 3, 0 < (k : ℕ) → (k : ℕ) ≤ #B →
    ∃ d : Fin 4, (testScope d, testGrade d) = (B, (k : ℕ))) B ⟨k, by omega⟩ hk0 hk
  exact ⟨d, hd⟩

theorem isCoded_testScheme : testScheme.{u}.IsCoded := fun _ t ↦ testRow_lt_omega0_sq t.1

/-- **The test scheme is legal.** -/
theorem isLegal_testScheme : testScheme.{u}.IsLegal where
  isWellFormed := isWellFormed_testScheme
  isCoded := isCoded_testScheme
  isConsistent _ := isLawful_testRow.isLawfulBelow _
  isBountiful := isBountiful_testScheme
  isComplete := isComplete_testScheme

/-! ### The label sections and the pairs -/

theorem atStage_omega0_mul_add (k j : ℕ) :
    AtStage (ω ^ 2 : Ordinal.{u}) ((ω * k + j : Ordinal.{u}) : Label.{u}) :=
  .inl (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (omega0_mul_add_lt_omega0_sq k j)))

theorem atStage_omega0_add_one :
    AtStage (ω ^ 2 : Ordinal.{u}) ((ω + 1 : Ordinal.{u}) : Label.{u}) := by
  simpa using atStage_omega0_mul_add.{u} 1 1

theorem isSelfVisible_omega0_mul_add_two (k : ℕ) :
    IsSelfVisible 2 ((ω * k + 2 : Ordinal.{u}) : Label.{u}) := by
  simpa using isSelfVisible_omega0_mul_add.{u} (i := 2) (j := 2) k le_rfl

theorem isLawful_k2Left : testScheme.{u}.rows.IsLawful k2Left := by
  refine isLawful_test (L := id) rfl monotone_id (fun _ _ _ ↦ rfl) (fun d ↦ ?_)
    (fun s t h1 h2 ↦ ?_)
    (fun _ _ ↦ ⊤) (fun _ ↦ antitone_const) (fun _ n ↦ isSelfVisible_top n) (fun s d h1 h2 ↦ ?_)
  · fin_cases d
    exacts [isSelfVisible_top _, isSelfVisible_omega0_add_one, isSelfVisible_top _,
      isSelfVisible_top _]
  · fin_cases s <;> fin_cases t <;>
      first | exact le_rfl | exact le_top | exact absurd h1 (by decide)
  · rw [lowTop_testRow, min_top_right]
    fin_cases s <;> fin_cases d <;>
      first | exact absurd (⟨h1, h2⟩ : _ ∧ _) (by decide) | simp [k2Left]

theorem isLawful_k2Right : testScheme.{u}.rows.IsLawful k2Right := by
  refine isLawful_test (L := shiftOmega) rfl monotone_shiftOmega
    (fun k i x ↦ (visibilityReplace_shiftOmega k i x).symm) (fun d ↦ ?_) (fun s t h1 h2 ↦ ?_)
    (fun _ _ ↦ ⊤) (fun _ ↦ antitone_const) (fun _ n ↦ isSelfVisible_top n) (fun s d h1 h2 ↦ ?_)
  · fin_cases d
    exacts [isSelfVisible_top _, isSelfVisible_omega0_mul_two_add_one, isSelfVisible_top _,
      isSelfVisible_top _]
  · fin_cases s <;> fin_cases t <;>
      first | exact le_rfl | exact le_top | exact absurd h1 (by decide)
  · rw [lowTop_testRow, shiftOmega_omega0_add_one, min_top_right]
    fin_cases s <;> fin_cases d <;>
      first | exact absurd (⟨h1, h2⟩ : _ ∧ _) (by decide) | simp [k2Right]

/-- The suppressors of the pair with `K = 1`: the apex suppressor at the apex, `⊤` elsewhere. -/
noncomputable def k1Suppressor (μ : Label.{u}) (s : Fin 4) : ℕ → Label.{u} :=
  if (s : ℕ) = 3 then apexSuppressor μ else fun _ ↦ ⊤

theorem antitone_k1Suppressor (μ : Label.{u}) (s : Fin 4) : Antitone (k1Suppressor μ s) := by
  unfold k1Suppressor
  split_ifs
  exacts [antitone_apexSuppressor μ, antitone_const]

theorem isSelfVisible_k1Suppressor {μ : Label.{u}} (hμ : IsSelfVisible 2 μ) (s : Fin 4) (n : ℕ) :
    IsSelfVisible n (k1Suppressor μ s n) := by
  unfold k1Suppressor
  split_ifs
  exacts [isSelfVisible_apexSuppressor hμ n, isSelfVisible_top n]

theorem isLawful_k1Left : testScheme.{u}.rows.IsLawful k1Left := by
  have hμ : IsSelfVisible 2 ((ω * 3 + 2 : Ordinal.{u}) : Label.{u}) := by
    simpa using isSelfVisible_omega0_mul_add_two.{u} 3
  refine isLawful_test (L := id) rfl monotone_id (fun _ _ _ ↦ rfl) (fun d ↦ ?_)
    (fun s t h1 h2 ↦ ?_)
    (k1Suppressor _) (antitone_k1Suppressor _) (isSelfVisible_k1Suppressor hμ)
    (fun s d h1 h2 ↦ ?_)
  · fin_cases d
    exacts [isSelfVisible_top _, isSelfVisible_omega0_add_one, isSelfVisible_top _, hμ]
  · fin_cases s <;> fin_cases t <;>
      first | exact le_rfl | exact le_top | exact absurd h1 (by decide) |
        exact absurd h2 (by decide)
  · rw [lowTop_testRow]
    fin_cases s <;> fin_cases d <;>
      first
      | exact absurd (⟨h1, h2⟩ : _ ∧ _) (by decide)
      | simp [k1Left, k1Suppressor, apexSuppressor, testGrade]

theorem isLawful_k1Right : testScheme.{u}.rows.IsLawful k1Right := by
  have hμ : IsSelfVisible 2 ((ω * 4 + 2 : Ordinal.{u}) : Label.{u}) := by
    simpa using isSelfVisible_omega0_mul_add_two.{u} 4
  refine isLawful_test (L := shiftOmega) rfl monotone_shiftOmega
    (fun k i x ↦ (visibilityReplace_shiftOmega k i x).symm) (fun d ↦ ?_) (fun s t h1 h2 ↦ ?_)
    (k1Suppressor _) (antitone_k1Suppressor _) (isSelfVisible_k1Suppressor hμ)
    (fun s d h1 h2 ↦ ?_)
  · fin_cases d
    exacts [isSelfVisible_top _, isSelfVisible_omega0_mul_two_add_one, isSelfVisible_top _, hμ]
  · fin_cases s <;> fin_cases t <;>
      first | exact le_rfl | exact le_top | exact absurd h1 (by decide) |
        exact absurd h2 (by decide)
  · rw [lowTop_testRow, shiftOmega_omega0_add_one]
    fin_cases s <;> fin_cases d <;>
      first
      | exact absurd (⟨h1, h2⟩ : _ ∧ _) (by decide)
      | simp [k1Right, k1Suppressor, apexSuppressor, testGrade]

/-- The test type with labels `ℓ`, from a lawful section at the stage `ω ^ 2`. -/
noncomputable def testType (ℓ : Fin 4 → Label.{u}) (hℓ : testScheme.{u}.rows.IsLawful ℓ)
    (hα : ∀ d, AtStage (ω ^ 2 : Ordinal.{u}) (ℓ d)) : StageType.{u} (ω ^ 2) 2 where
  toScheme := testScheme
  label := ℓ
  isWellFormed := isWellFormed_testScheme
  isCoded := isCoded_testScheme
  isLawful := hℓ
  atStage := hα

theorem isTestType_testType (ℓ : Fin 4 → Label.{u}) (hℓ) (hα) :
    IsTestType (testType ℓ hℓ hα) ℓ :=
  ⟨rfl, fun _ _ h ↦ congrArg ℓ (Fin.ext h)⟩

theorem isLegal_testType (ℓ : Fin 4 → Label.{u}) (hℓ) (hα) : (testType ℓ hℓ hα).IsLegal :=
  isLegal_testScheme

theorem atStage_lit_two_one :
    AtStage (ω ^ 2 : Ordinal.{u}) ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) := by
  simpa using atStage_omega0_mul_add.{u} 2 1

theorem atStage_lit_three_two :
    AtStage (ω ^ 2 : Ordinal.{u}) ((ω * 3 + 2 : Ordinal.{u}) : Label.{u}) := by
  simpa using atStage_omega0_mul_add.{u} 3 2

theorem atStage_lit_four_two :
    AtStage (ω ^ 2 : Ordinal.{u}) ((ω * 4 + 2 : Ordinal.{u}) : Label.{u}) := by
  simpa using atStage_omega0_mul_add.{u} 4 2

/-- **The pair with `K = 2` exists and is legal.** -/
theorem k2Pair : K2PairTarget.{u} := by
  have hl : ∀ d, AtStage (ω ^ 2 : Ordinal.{u}) (k2Left d) := fun d ↦ by
    fin_cases d
    exacts [.inr rfl, atStage_omega0_add_one, .inr rfl, .inr rfl]
  have hr : ∀ d, AtStage (ω ^ 2 : Ordinal.{u}) (k2Right d) := fun d ↦ by
    fin_cases d
    exacts [.inr rfl, atStage_lit_two_one, .inr rfl, .inr rfl]
  exact ⟨testType _ isLawful_k2Left hl, testType _ isLawful_k2Right hr,
    isTestType_testType _ _ _, isTestType_testType _ _ _, isLegal_testType _ _ _,
    isLegal_testType _ _ _⟩

/-- **The pair with `K = 1` exists and is legal.** -/
theorem k1Pair : K1PairTarget.{u} := by
  have hl : ∀ d, AtStage (ω ^ 2 : Ordinal.{u}) (k1Left d) := fun d ↦ by
    fin_cases d
    exacts [.inr rfl, atStage_omega0_add_one, .inr rfl, atStage_lit_three_two]
  have hr : ∀ d, AtStage (ω ^ 2 : Ordinal.{u}) (k1Right d) := fun d ↦ by
    fin_cases d
    exacts [.inr rfl, atStage_lit_two_one, .inr rfl,
      atStage_lit_four_two]
  exact ⟨testType _ isLawful_k1Left hl, testType _ isLawful_k1Right hr,
    isTestType_testType _ _ _, isTestType_testType _ _ _, isLegal_testType _ _ _,
    isLegal_testType _ _ _⟩

end VaughtConjecture.ProcessRank

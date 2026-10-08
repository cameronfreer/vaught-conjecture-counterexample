/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderLift

/-!
# The members of the ladder base: dense rank vectors with lawful tables

Roadmap, Layer 3 ((R3) and (R4), the members of the padded grade-one base).

A rank vector `w` on the cells of `S` has **lawful tables** (`Scheme.HasLawfulTables`) when every
positive table read at `w` on the cells of grade one, `⊥` above, is lawful on `S`; it is
**dense** (`Scheme.IsDenseRanks`) when every positive rank below a realized rank is realized.  The
**rank members** (`Scheme.RankMember`) are the dense rank vectors with values at most `H` and lawful
tables; they form a finite family, and the rank tables of the base over them are lawful by
definition (`Scheme.rankTablesLawful_rankMember`).

**Lawful tables from order** (`Scheme.hasLawfulTables_of_order`): by order interpolation at the
grade one (`Label.transformsTo_one_of_order`), a rank vector has lawful tables when, at every cell
`s` of grade one, its minimum with the rank of `s` is monotone along the row of `s` (in the sense of
`Label.TransformsTo.le_of_le_visibilityReplace`), its zero set at grade one is that of a lawful
section, and availability holds for its ranks at grade one.

## References

Lawful sections are [Kni26, Definition 2.5.4]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

/-- The codes of the ladder reflect the order of the ranks up to the ceiling. -/
theorem ladderSource_le_ladderSource_iff {H i j : ℕ} (hi : i ≤ H) (hj : j ≤ H) :
    ladderSource.{u} H i ≤ ladderSource H j ↔ i ≤ j := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [ladderSource_le_iff hpos hi, min_eq_left hj]

variable {ι : Type*} [Fintype ι] {Z : ι → Label.{u}}

/-- On the values of `Z`, the value rank reflects the order. -/
theorem le_of_valueRank_le {d e : ι} (h : valueRank Z (Z e) ≤ valueRank Z (Z d)) :
    Z e ≤ Z d := by
  by_contra hlt
  exact absurd h (not_le.mpr (valueRank_lt_valueRank (ne_bot_of_gt (not_le.mp hlt))
    (not_le.mp hlt)))

/-- The value rank is at most the number of values other than `⊥`. -/
theorem valueRank_le_card_values (x : Label.{u}) :
    valueRank Z x ≤ #((univ.image Z).filter (· ≠ ⊥)) :=
  card_le_card fun y hy ↦ by
    simp only [mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.1⟩

/-- **Every positive rank up to the number of values is the rank of a value.** -/
theorem exists_valueRank_eq {i : ℕ} (hi : 0 < i)
    (hiV : i ≤ #((univ.image Z).filter (· ≠ ⊥))) : ∃ e, Z e ≠ ⊥ ∧ valueRank Z (Z e) = i := by
  classical
  set V := (univ.image Z).filter (· ≠ ⊥) with hV
  have hmemV {x : Label.{u}} (hx : x ∈ V) : ∃ e, Z e = x ∧ Z e ≠ ⊥ := by
    obtain ⟨hx1, hx0⟩ := mem_filter.mp hx
    obtain ⟨e, -, rfl⟩ := mem_image.mp hx1
    exact ⟨e, rfl, hx0⟩
  have hinj : Set.InjOn (valueRank Z) V := by
    intro x hx y hy hxy
    obtain ⟨e, rfl, he0⟩ := hmemV hx
    obtain ⟨d, rfl, hd0⟩ := hmemV hy
    rcases lt_trichotomy (Z e) (Z d) with h | h | h
    · exact absurd hxy (valueRank_lt_valueRank hd0 h).ne
    · exact h
    · exact absurd hxy.symm (valueRank_lt_valueRank he0 h).ne
  have hsub : V.image (valueRank Z) ⊆ Icc 1 #V := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
    obtain ⟨e, rfl, he0⟩ := hmemV hx
    refine mem_Icc.mpr ⟨?_, valueRank_le_card_values _⟩
    exact card_pos.mpr ⟨Z e, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), he0, le_rfl⟩⟩
  have heq : V.image (valueRank Z) = Icc 1 #V :=
    eq_of_subset_of_card_le hsub (by rw [card_image_of_injOn hinj, Nat.card_Icc]; omega)
  have hmem : i ∈ V.image (valueRank Z) := heq ▸ mem_Icc.mpr ⟨hi, hiV⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hmem
  obtain ⟨e, rfl, he0⟩ := hmemV hx
  exact ⟨e, he0, rfl⟩

open Classical in
/-- The **value table** of `Z`: at the rank `i`, the largest value of `Z` of rank at most `i`. -/
noncomputable def valueTable (Z : ι → Label.{u}) (i : ℕ) : Label.{u} :=
  (univ.filter fun e ↦ valueRank Z (Z e) ≤ i).sup Z

theorem monotone_valueTable : Monotone (valueTable Z) := by
  classical
  intro i j hij
  exact sup_mono fun e he ↦ mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2.trans hij⟩

/-- The value table reads every value at its rank. -/
theorem valueTable_valueRank (d : ι) : valueTable Z (valueRank Z (Z d)) = Z d := by
  classical
  exact le_antisymm (Finset.sup_le fun e he ↦ le_of_valueRank_le (mem_filter.mp he).2)
    (Finset.le_sup (f := Z) (mem_filter.mpr ⟨mem_univ _, le_rfl⟩))

theorem valueTable_zero : valueTable Z 0 = ⊥ := by
  classical
  refine (Finset.sup_eq_bot_iff _ _).mpr fun e he ↦ ?_
  have h0 : valueRank Z (Z e) = 0 := Nat.le_zero.mp (mem_filter.mp he).2
  exact (rankVector_eq_zero_iff (R := Z) e).mp h0

theorem isSelfVisible_valueTable (hZ : ∀ e, IsSelfVisible 1 (Z e)) (i : ℕ) :
    IsSelfVisible 1 (valueTable Z i) := by
  classical
  exact Finset.sup_induction (p := IsSelfVisible 1) (isSelfVisible_bot _)
    (fun _ ha _ hb ↦ ha.max hb) fun e _ ↦ hZ e

end Label

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) (H : ℕ)

/-- A rank vector is **dense**: every positive rank below a realized rank is realized. -/
def IsDenseRanks (w : Fin S.card → ℕ) : Prop :=
  ∀ i, 0 < i → ∀ d, i ≤ w d → ∃ e, w e = i

/-- A rank vector has **lawful tables**: every positive table read at it on the cells of grade
one, `⊥` above, is lawful on `S`. -/
def HasLawfulTables (w : Fin S.card → ℕ) : Prop :=
  ∀ f : ℕ → Label.{u}, Monotone f → f 0 = ⊥ → (∀ i, IsSelfVisible 1 (f i)) →
    (∀ i, 0 < i → i ≤ H → f i ≠ ⊥) →
    S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then f (w d) else ⊥

/-- The **rank members**: dense rank vectors with values at most `H` and lawful tables. -/
def RankMember : Type :=
  {w : Fin S.card → Fin (H + 1) //
    IsDenseRanks S (fun d ↦ (w d : ℕ)) ∧ HasLawfulTables.{u} S H fun d ↦ (w d : ℕ)}

instance : Finite (RankMember S H) := by unfold RankMember; infer_instance

noncomputable instance : Fintype (RankMember S H) := Fintype.ofFinite _

instance : Nonempty (RankMember S H) :=
  ⟨⟨fun _ ↦ 0, fun i hi d hd ↦ absurd hd (by simp; omega), fun f _ h0 _ _ ↦ by
    simp only [Fin.val_zero, h0, ite_self]
    exact CellScheme.Rows.isLawful_const_bot⟩⟩

/-- The rank vector of a rank member. -/
def rankProf : RankMember S H → Fin S.card → ℕ := fun a d ↦ a.1 d

theorem rankProf_le (a : RankMember S H) (d : Fin S.card) : rankProf S H a d ≤ H :=
  Nat.lt_succ_iff.mp (a.1 d).isLt

/-- **The rank tables of the rank members are lawful**, by definition. -/
theorem rankTablesLawful_rankMember : RankTablesLawful S H (rankProf.{u} S H) :=
  fun a f hf h0 hv hp ↦ a.2.2 f hf h0 hv hp

variable {S H}

/-- **Lawful sections at grade one are monotone along the rows**: for a lawful section `Z` of a
well-formed scheme and a cell `s` of grade one, `min (Z e) (Z s) ≤ min (Z d) (Z s)` whenever the
row of `s` reads `e` at most as the replacement at `1` of its reading of `d`. -/
theorem min_le_min_of_isLawful (hwf : S.IsWellFormed) {Z : Fin S.card → Label.{u}}
    (hZ : S.rows.IsLawful Z) {s : Fin S.card} (hs : S.toCellScheme.grade s = 1)
    {d e : S.toCellScheme.below (S.toCellScheme.gradedIndex s)}
    (h : S.rows.row s e ≤ visibilityReplace 1 1 (S.rows.row s d)) :
    min (Z e) (Z s) ≤ min (Z d) (Z s) := by
  have hg1 (x : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
      S.toCellScheme.grade x = 1 := by
    have h1 : S.toCellScheme.grade x ≤ 1 := hs ▸ x.2.2
    have h2 := hwf.isWellFormed.grade_pos x.1
    omega
  have hloc := hZ.locality s
  have hgr : (fun x : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
      S.toCellScheme.grade x) = fun _ ↦ 1 := funext hg1
  rw [hgr] at hloc
  exact hloc.le_of_le_visibilityReplace
    (fun x ↦ ((hg1 x) ▸ hZ.orderly x.1).min (hs ▸ hZ.orderly s)) h

/-- **Lawful tables from order.**  A rank vector `w` with values at most `H` at grade one has
lawful tables when, at every cell `s` of grade one, `min (w ·) (w s)` is monotone along the row of
`s`, `w` is `0` at grade one exactly where a lawful section `Y` is `⊥`, and availability holds for
`w` at grade one. -/
theorem hasLawfulTables_of_order (hwf : S.IsWellFormed) {w : Fin S.card → ℕ}
    (hwH : ∀ d, S.toCellScheme.grade d = 1 → w d ≤ H) {Y : Fin S.card → Label.{u}}
    (hY : S.rows.IsLawful Y)
    (hzero : ∀ d, S.toCellScheme.grade d = 1 → (w d = 0 ↔ Y d = ⊥))
    (hord : ∀ s, S.toCellScheme.grade s = 1 →
      ∀ d e : S.toCellScheme.below (S.toCellScheme.gradedIndex s),
        S.rows.row s e ≤ visibilityReplace 1 1 (S.rows.row s d) →
          min (w e) (w s) ≤ min (w d) (w s))
    (havail : ∀ s t, S.toCellScheme.grade s = 1 → S.toCellScheme.grade t = 1 →
      S.toCellScheme.scope s ⊆ S.toCellScheme.scope t →
        ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex t ∧ w s ≤ w u) :
    HasLawfulTables.{u} S H w := by
  intro f hf h0 hv hp
  have hf0 (i : ℕ) (hi : i ≤ H) : f i = ⊥ ↔ i = 0 :=
    ⟨fun h ↦ by_contra fun h' ↦ hp i (Nat.pos_of_ne_zero h') hi h, fun h ↦ h ▸ h0⟩
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · split_ifs with hd
    · rw [hd]; exact hv _
    · exact isSelfVisible_bot _
  · by_cases hs : S.toCellScheme.grade s = 1
    swap
    · have hz : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
          min ((fun d ↦ if S.toCellScheme.grade d = 1 then f (w d) else ⊥) d.1)
            (if S.toCellScheme.grade s = 1 then f (w s) else ⊥)) = fun _ ↦ ⊥ := by
        funext d; rw [ite_eq_right hs, min_bot_right]
      rw [hz]
      exact TransformsTo.bot _ _
    have hg1 (x : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
        S.toCellScheme.grade x = 1 := by
      have h1 : S.toCellScheme.grade x ≤ 1 := hs ▸ x.2.2
      have h2 := hwf.isWellFormed.grade_pos x.1
      omega
    have hloc := hY.locality s
    have hgr : (fun x : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦
        S.toCellScheme.grade x) = fun _ ↦ 1 := funext hg1
    rw [hgr] at hloc ⊢
    have h := transformsTo_one_of_order hloc
      (r := fun x : S.toCellScheme.below (S.toCellScheme.gradedIndex s) ↦ f (min (w x) (w s)))
      (fun _ ↦ hv _) (fun d e hed ↦ hf (hord s hs d e hed)) fun x ↦ by
        rw [hf0 _ ((min_le_right _ _).trans (hwH s hs)), min_eq_bot, Nat.min_eq_zero_iff,
          hzero _ (hg1 x), hzero _ hs]
    convert h using 2 with x
    rw [ite_eq_left (hg1 x), ite_eq_left hs, hf.map_min]
  · by_cases ht : S.toCellScheme.grade t = 1
    · obtain ⟨u, hu, hle⟩ := havail s t (hg.trans ht) ht hst
      have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
      refine ⟨u, hu, ?_⟩
      simp only [ite_eq_left (hg.trans ht), ite_eq_left hgu]
      exact hf hle
    · refine ⟨t, rfl, ?_⟩
      simp only [ite_eq_right (hg ▸ ht : ¬ S.toCellScheme.grade s = 1)]
      exact bot_le

/-- The values other than `⊥` of a labelling of the cells are at most as many as the cells. -/
theorem card_values_le (Z : Fin S.card → Label.{u}) :
    #((univ.image Z).filter (· ≠ ⊥)) ≤ S.card :=
  (card_filter_le _ _).trans (card_image_le.trans (by simp))

/-- **Gluing at the cut `0`**: the rank vector of a lawful section at grade one is a rank member,
and its value table, made positive, reads the section. -/
theorem exists_rankMember_of_isLawful (hwf : S.IsWellFormed) (hcard : S.card ≤ H)
    {Y : Fin S.card → Label.{u}}
    (hYl : S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then Y d else ⊥) :
    ∃ (a : RankMember S H) (F' : ℕ → Label.{u}), Monotone F' ∧ F' 0 = ⊥ ∧
      (∀ i, IsSelfVisible 1 (F' i)) ∧ (∀ i, 0 < i → i ≤ H → F' i ≠ ⊥) ∧
      ∀ d, S.toCellScheme.grade d = 1 → F' (rankProf S H a d) = Y d := by
  classical
  set Yt : Fin S.card → Label.{u} := fun d ↦ if S.toCellScheme.grade d = 1 then Y d else ⊥
    with hYt
  have hYtv (d : Fin S.card) : IsSelfVisible 1 (Yt d) := by
    by_cases hd : S.toCellScheme.grade d = 1
    · have h := hYl.orderly d
      rw [hd] at h
      exact h
    · simp only [hYt, hd, ite_false]
      exact isSelfVisible_bot _
  have hwH (d : Fin S.card) : rankVector Yt d ≤ H := (rankVector_le d).trans (by simpa using hcard)
  let a : RankMember S H := ⟨fun d ↦ ⟨rankVector Yt d, Nat.lt_succ_of_le (hwH d)⟩,
    fun i hi d hd ↦ by
      obtain ⟨e, -, he⟩ := exists_valueRank_eq (Z := Yt) hi
        ((show i ≤ valueRank Yt (Yt d) from hd).trans (valueRank_le_card_values _))
      exact ⟨e, he⟩,
    fun f hf h0 hv hp ↦ isLawful_rankTable hwf hYl hwH hf h0 hv hp⟩
  set m : Label.{u} := (univ.filter fun e ↦ Yt e ≠ ⊥).inf Yt with hm
  have hm0 : m ≠ ⊥ := by
    refine Finset.inf_induction (p := fun y ↦ y ≠ ⊥) (by simp) (fun x hx y hy ↦ ?_) ?_
    · rcases min_choice x y with h | h <;> rw [h] <;> assumption
    · intro e he; exact (mem_filter.mp he).2
  have hmv : IsSelfVisible 1 m :=
    Finset.inf_induction (p := IsSelfVisible 1) (isSelfVisible_top _)
      (fun _ ha _ hb ↦ ha.min hb) fun e _ ↦ hYtv e
  refine ⟨a, fun i ↦ if i = 0 then ⊥ else max (valueTable Yt i) m, fun i i' hii' ↦ ?_,
    by simp, fun i ↦ ?_, fun i hi _ ↦ ?_, fun d hd ↦ ?_⟩
  · by_cases hi : i = 0
    · simp only [hi, ite_true]; exact bot_le
    · simp only [hi, ite_false, show i' ≠ 0 by omega]
      exact max_le_max (monotone_valueTable hii') le_rfl
  · dsimp only
    split_ifs
    · exact isSelfVisible_bot _
    · exact (isSelfVisible_valueTable hYtv i).max hmv
  · simp only [show i ≠ 0 by omega, ite_false]
    exact fun h ↦ hm0 (le_bot_iff.mp (h ▸ le_max_right _ _))
  · change (if rankVector Yt d = 0 then ⊥ else max (valueTable Yt (rankVector Yt d)) m) = Y d
    have hYd : Yt d = Y d := by simp only [hYt, hd, ite_true]
    by_cases h0 : rankVector Yt d = 0
    · rw [ite_eq_left h0, ← hYd, (rankVector_eq_zero_iff d).mp h0]
    · have hmd : m ≤ Yt d := Finset.inf_le (mem_filter.mpr
        ⟨mem_univ _, fun h ↦ h0 ((rankVector_eq_zero_iff d).mpr h)⟩)
      rw [ite_eq_right h0, rankVector, valueTable_valueRank, max_eq_left hmd, hYd]

end Scheme

end VaughtConjecture

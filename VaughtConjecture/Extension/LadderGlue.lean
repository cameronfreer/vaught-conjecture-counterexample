/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderMembers

/-!
# Gluing of rank members

Roadmap, Layer 3 ((R3) and (R4), legality of the padded grade-one base at the ladder).

**The rank members glue** (`Scheme.rankGlue_rankMember`), at a height at least the number of cells.
Let `b` be a rank member with a positive table `F`, `k ≤ H` the first rank where `F` reaches a
cap `c`, and `Y` a lawful labelling at grade one agreeing with the table of `b` capped at `c`.
At the cut `0` the rank vector of `Y` is a member (`Scheme.exists_rankMember_of_isLawful`).  At a
positive cut the cells split into the **low** ones (rank of `b` below `k`), where `Y` is the table
of `b`, and the **high** ones, where `Y` is at least `c`.  The glued vector keeps the ranks of `b`
on the low cells, ranks the high cells of grade one by their values of `Y` from `k` on, and gives
the other high cells the rank `k`:

* it is at most the number of cells (the low ranks `1, …, k - 1` are realized by low cells, by
  density of `b`, and the high values by high cells) and dense;
* its tables are lawful (`Scheme.hasLawfulTables_of_order`): at a low cell its minimum with the
  rank of the cell is that of `b`; at a high cell the order along the row comes from that of `b`
  (read through the codes of the ladder, which reflect the order of ranks) on low cells and from
  that of `Y` on high cells, and a high cell is never read below a low one since `Y` separates
  them at `c`;
* the table equal to `F` before `k` and above it `c` or the value table of `Y` on the high cells
  reads `Y` at the glued ranks.

Hence the ladder base over the rank members is consistent
(`Scheme.isConsistent_ladderBase_rankMember`) and lifts capped into the full face of grade one
from every pair below it from which `S` does (`Scheme.cappedLift_ladderBase_rankMember`); the rank
vector of every lawful state is a rank member (`Scheme.RankMember.ofLawful`).

## References

Lawful sections are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {H : ℕ}

/-- **The rank members glue**, at a height at least the number of cells. -/
theorem rankGlue_rankMember (hwf : S.IsWellFormed) (hcard : S.card ≤ H) :
    RankGlue S H (rankProf.{u} S H) := by
  classical
  intro b F k c Y hF hF0 hFv hFp hkH hlow hck hc hYl hYb
  by_cases hk0 : k = 0
  · -- the cut `0`
    subst hk0
    have hc0 : c = ⊥ := le_bot_iff.mp (hF0 ▸ hck)
    obtain ⟨a, F', hF', hF'0, hF'v, hF'p, hF'Y⟩ := exists_rankMember_of_isLawful hwf hcard hYl
    exact ⟨a, F', hF', hF'0, hF'v, hF'p, fun _ ↦ by simp, fun _ h ↦ absurd h (Nat.not_lt_zero _),
      hc0 ▸ bot_le, hF'Y⟩
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hcb : ⊥ < c := hF0 ▸ hlow 0 hk1
  set bv : Fin S.card → ℕ := rankProf S H b with hbv
  have hbH (d : Fin S.card) : bv d ≤ H := rankProf_le S H b d
  have hFb (i : ℕ) (hi : i ≤ H) : F i = ⊥ ↔ i = 0 :=
    ⟨fun h ↦ by_contra fun h' ↦ hFp i (Nat.pos_of_ne_zero h') hi h, fun h ↦ h ▸ hF0⟩
  -- the values of `Y` at grade one
  have hYv (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) : IsSelfVisible 1 (Y d) := by
    have h := hYl.orderly d
    simp only [hd, ite_true] at h
    exact h
  have hYlow (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) (hb : bv d < k) :
      Y d = F (bv d) := by
    have h := hYb d hd
    rw [min_eq_left (hlow _ hb).le] at h
    rcases le_total (Y d) c with h' | h'
    · rwa [min_eq_left h'] at h
    · rw [min_eq_right h'] at h
      exact absurd h.symm (hlow _ hb).ne
  have hYhigh (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) (hb : k ≤ bv d) : c ≤ Y d := by
    have h := hYb d hd
    rw [min_eq_right (hck.trans (hF hb))] at h
    exact min_eq_right_iff.mp h
  -- the high values and their ranks
  set Yh : Fin S.card → Label.{u} := fun e ↦
    if S.toCellScheme.grade e = 1 ∧ k ≤ bv e then Y e else ⊥ with hYh
  have hYhe (e : Fin S.card) (he : S.toCellScheme.grade e = 1) (hb : k ≤ bv e) : Yh e = Y e := by
    simp only [hYh, he, hb, and_self, ite_true]
  have hYh0 (e : Fin S.card) (he : Yh e ≠ ⊥) : S.toCellScheme.grade e = 1 ∧ k ≤ bv e := by
    by_contra h
    simp only [hYh, ite_eq_right h, ne_eq, not_true_eq_false] at he
  have hYhv (e : Fin S.card) : IsSelfVisible 1 (Yh e) := by
    by_cases he : S.toCellScheme.grade e = 1 ∧ k ≤ bv e
    · rw [hYhe e he.1 he.2]; exact hYv e he.1
    · simp only [hYh, ite_eq_right he]; exact isSelfVisible_bot _
  set j : Fin S.card → ℕ := fun d ↦ valueRank Yh (Y d) with hj
  -- the glued vector
  set wv : Fin S.card → ℕ := fun d ↦
    if bv d < k then bv d else if S.toCellScheme.grade d = 1 then k - 1 + j d else k with hwv
  have hwlow (d : Fin S.card) (hb : bv d < k) : wv d = bv d := by simp only [hwv, hb, ite_true]
  have hwhigh1 (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) (hb : k ≤ bv d) :
      wv d = k - 1 + j d := by
    simp only [hwv, not_lt.mpr hb, hd, ite_true, ite_false]
  have hwhigh (d : Fin S.card) (hb : k ≤ bv d) : k ≤ wv d := by
    simp only [hwv, not_lt.mpr hb, ite_false]
    split_ifs with hd
    · have : 1 ≤ j d := by
        rw [hj]; simp only
        rw [← hYhe d hd hb]
        exact Nat.pos_of_ne_zero fun h0 ↦ (hcb.trans_le (hYhigh d hd hb)).ne'
          ((rankVector_eq_zero_iff (R := Yh) d).mp h0 ▸ (hYhe d hd hb).symm)
      omega
    · exact le_rfl
  -- the bound
  have hjle (d : Fin S.card) : j d ≤ #((univ.image Yh).filter (· ≠ ⊥)) :=
    valueRank_le_card_values _
  have hcount (d : Fin S.card) (hb : k ≤ bv d) :
      k - 1 + #((univ.image Yh).filter (· ≠ ⊥)) ≤ S.card := by
    set A := univ.filter fun e ↦ 0 < bv e ∧ bv e < k with hA
    set B := univ.filter fun e ↦ S.toCellScheme.grade e = 1 ∧ k ≤ bv e with hB
    have hAk : k - 1 ≤ #A := by
      have hsub : Icc 1 (k - 1) ⊆ A.image bv := by
        intro i hi
        obtain ⟨hi1, hi2⟩ := mem_Icc.mp hi
        obtain ⟨e, he⟩ := b.2.1 i hi1 d (by change i ≤ bv d; omega)
        have he' : bv e = i := he
        refine mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, ?_⟩, he'⟩
        rw [he']
        omega
      calc k - 1 = #(Icc 1 (k - 1)) := by simp
        _ ≤ #(A.image bv) := card_le_card hsub
        _ ≤ #A := card_image_le
    have hBV : #((univ.image Yh).filter (· ≠ ⊥)) ≤ #B := by
      refine (card_le_card fun x hx ↦ ?_).trans (card_image_le (s := B) (f := Y))
      obtain ⟨hx1, hx0⟩ := mem_filter.mp hx
      obtain ⟨e, -, rfl⟩ := mem_image.mp hx1
      obtain ⟨he1, he2⟩ := hYh0 e hx0
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, he1, he2⟩, (hYhe e he1 he2).symm⟩
    have hdisj : Disjoint A B := disjoint_filter.mpr fun e _ h1 h2 ↦ by omega
    have hAB : #A + #B ≤ S.card := by
      rw [← card_union_of_disjoint hdisj]
      exact (card_le_univ _).trans (by simp)
    omega
  have hwvH (d : Fin S.card) : wv d ≤ H := by
    by_cases hb : bv d < k
    · rw [hwlow d hb]; exact hbH d
    · by_cases hd : S.toCellScheme.grade d = 1
      · rw [hwhigh1 d hd (not_lt.mp hb)]
        have := hcount d (not_lt.mp hb)
        have := hjle d
        omega
      · simp only [hwv, hb, hd, ite_false]; exact hkH
  -- density
  have hdense : IsDenseRanks S wv := by
    intro i hi d hd
    by_cases hik : i < k
    · have hbd : i ≤ bv d := by
        by_cases hb : bv d < k
        · rw [hwlow d hb] at hd; exact hd
        · omega
      obtain ⟨e, he⟩ := b.2.1 i hi d hbd
      have he' : bv e = i := he
      exact ⟨e, by rw [hwlow e (he' ▸ hik), he']⟩
    · have hb : k ≤ bv d := by
        by_contra hb
        rw [hwlow d (not_le.mp hb)] at hd
        omega
      by_cases hd1 : S.toCellScheme.grade d = 1
      · rw [hwhigh1 d hd1 hb] at hd
        obtain ⟨e, he0, he⟩ := exists_valueRank_eq (Z := Yh) (i := i - (k - 1)) (by omega)
          ((show i - (k - 1) ≤ j d by omega).trans (hjle d))
        obtain ⟨he1, he2⟩ := hYh0 e he0
        refine ⟨e, ?_⟩
        rw [hwhigh1 e he1 he2]
        have hje : j e = i - (k - 1) := by
          rw [hj]
          simp only
          rw [← hYhe e he1 he2]
          exact he
        omega
      · have hwd : wv d = k := by simp only [hwv, not_lt.mpr hb, hd1, ite_false]
        exact ⟨d, by omega⟩
  -- the cells below a cell of grade one have grade one
  have hg1 (s : Fin S.card) (hs : S.toCellScheme.grade s = 1)
      (x : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
      S.toCellScheme.grade x = 1 := by
    have h1 : S.toCellScheme.grade x ≤ 1 := hs ▸ x.2.2
    have h2 := hwf.isWellFormed.grade_pos x.1
    omega
  -- the order and availability of `b`, read through the codes of the ladder
  have hTb := b.2.2 (ladderSource H) (monotone_ladderSource H) (ladderSource_zero H)
    (isSelfVisible_ladderSource H) fun i hi _ h0 ↦ by
      rw [ladderSource_eq_bot_iff] at h0; omega
  have hbord (s : Fin S.card) (hs : S.toCellScheme.grade s = 1)
      (d e : S.toCellScheme.below (S.toCellScheme.gradedIndex s))
      (h : S.rows.row s e ≤ visibilityReplace 1 1 (S.rows.row s d)) :
      min (bv e) (bv s) ≤ min (bv d) (bv s) := by
    have h1 := min_le_min_of_isLawful hwf hTb hs h
    change min (if S.toCellScheme.grade e = 1 then ladderSource H (bv e) else ⊥)
        (if S.toCellScheme.grade s = 1 then ladderSource H (bv s) else ⊥) ≤
      min (if S.toCellScheme.grade d = 1 then ladderSource H (bv d) else ⊥)
        (if S.toCellScheme.grade s = 1 then ladderSource H (bv s) else ⊥) at h1
    rw [ite_eq_left (hg1 s hs e), ite_eq_left (hg1 s hs d), ite_eq_left hs,
      ← (monotone_ladderSource H).map_min, ← (monotone_ladderSource H).map_min] at h1
    exact (ladderSource_le_ladderSource_iff ((min_le_left _ _).trans (hbH _))
      ((min_le_left _ _).trans (hbH _))).mp h1
  have hbav (s t : Fin S.card) (hs : S.toCellScheme.grade s = 1)
      (ht : S.toCellScheme.grade t = 1) (hst : S.toCellScheme.scope s ⊆ S.toCellScheme.scope t) :
      ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex t ∧ bv s ≤ bv u := by
    obtain ⟨u, hu, hle⟩ := hTb.availability s t hst (hs.trans ht.symm)
    have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
    refine ⟨u, hu, ?_⟩
    change (if S.toCellScheme.grade s = 1 then ladderSource H (bv s) else ⊥) ≤
      (if S.toCellScheme.grade u = 1 then ladderSource H (bv u) else ⊥) at hle
    rw [ite_eq_left hs, ite_eq_left hgu] at hle
    exact (ladderSource_le_ladderSource_iff (hbH s) (hbH u)).mp hle
  -- the order and availability of `Y`
  have hYord (s : Fin S.card) (hs : S.toCellScheme.grade s = 1)
      (d e : S.toCellScheme.below (S.toCellScheme.gradedIndex s))
      (h : S.rows.row s e ≤ visibilityReplace 1 1 (S.rows.row s d)) :
      min (Y e) (Y s) ≤ min (Y d) (Y s) := by
    have h1 := min_le_min_of_isLawful hwf hYl hs h
    simp only [hg1 s hs e, hg1 s hs d, hs, ite_true] at h1
    exact h1
  have hYav (s t : Fin S.card) (hs : S.toCellScheme.grade s = 1)
      (ht : S.toCellScheme.grade t = 1) (hst : S.toCellScheme.scope s ⊆ S.toCellScheme.scope t) :
      ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex t ∧
        S.toCellScheme.grade u = 1 ∧ Y s ≤ Y u := by
    obtain ⟨u, hu, hle⟩ := hYl.availability s t hst (hs.trans ht.symm)
    have hgu : S.toCellScheme.grade u = 1 := (congrArg Prod.snd hu).trans ht
    simp only [hs, hgu, ite_true] at hle
    exact ⟨u, hu, hgu, hle⟩
  -- the glued vector has lawful tables
  have htab : HasLawfulTables.{u} S H wv := by
    refine hasLawfulTables_of_order hwf (fun d _ ↦ hwvH d) hYl (fun d hd ↦ ?_)
      (fun s hs d e h ↦ ?_) (fun s t hs ht hst ↦ ?_)
    · rw [ite_eq_left hd]
      by_cases hb : bv d < k
      · rw [hwlow d hb, hYlow d hd hb, hFb _ (hbH d)]
      · have := hwhigh d (not_lt.mp hb)
        refine ⟨fun h ↦ by omega, fun h ↦ absurd h ?_⟩
        exact (hcb.trans_le (hYhigh d hd (not_lt.mp hb))).ne'
    · have hb := hbord s hs d e h
      have hy := hYord s hs d e h
      have hd1 := hg1 s hs d
      have he1 := hg1 s hs e
      by_cases hsl : bv s < k
      · have key (x : Fin S.card) : min (wv x) (wv s) = min (bv x) (bv s) := by
          rw [hwlow s hsl]
          by_cases hxl : bv x < k
          · rw [hwlow x hxl]
          · have := hwhigh x (not_lt.mp hxl)
            omega
        rw [key, key]
        exact hb
      · have hsh := not_lt.mp hsl
        have hws : k ≤ wv s := hwhigh s hsh
        by_cases hdl : bv d < k
        · rw [hwlow d hdl, min_eq_left (by omega : bv d ≤ wv s)]
          by_cases hel : bv e < k
          · rw [hwlow e hel, min_eq_left (by omega : bv e ≤ wv s)]
            omega
          · exfalso
            have h1 : c ≤ min (Y e) (Y s) := le_min (hYhigh e he1 (not_lt.mp hel))
              (hYhigh s hs hsh)
            have h2 : min (Y d) (Y s) < c :=
              (min_le_left _ _).trans_lt (by rw [hYlow d hd1 hdl]; exact hlow _ hdl)
            exact absurd (h1.trans hy) (not_le.mpr h2)
        · have hdh := not_lt.mp hdl
          by_cases hel : bv e < k
          · rw [hwlow e hel]
            have := hwhigh d hdh
            omega
          · have heh := not_lt.mp hel
            rw [hwhigh1 e he1 heh, hwhigh1 d hd1 hdh, hwhigh1 s hs hsh]
            have hj' : min (j e) (j s) ≤ min (j d) (j s) := by
              simp only [hj]
              rw [← (monotone_valueRank Yh).map_min, ← (monotone_valueRank Yh).map_min]
              exact monotone_valueRank Yh hy
            omega
    · by_cases hsl : bv s < k
      · obtain ⟨u, hu, hle⟩ := hbav s t hs ht hst
        refine ⟨u, hu, ?_⟩
        rw [hwlow s hsl]
        by_cases hul : bv u < k
        · rw [hwlow u hul]; exact hle
        · have := hwhigh u (not_lt.mp hul)
          omega
      · obtain ⟨u, hu, hgu, hle⟩ := hYav s t hs ht hst
        have hsh := not_lt.mp hsl
        have huh : k ≤ bv u := by
          by_contra hul
          have hYu := hYlow u hgu (not_le.mp hul)
          exact absurd ((hYhigh s hs hsh).trans hle) (not_le.mpr (hYu ▸ hlow _ (not_le.mp hul)))
        refine ⟨u, hu, ?_⟩
        rw [hwhigh1 s hs hsh, hwhigh1 u hgu huh]
        have : j s ≤ j u := monotone_valueRank Yh hle
        omega
  -- the member and its table
  let a : RankMember S H := ⟨fun d ↦ ⟨wv d, Nat.lt_succ_of_le (hwvH d)⟩, hdense, htab⟩
  refine ⟨a, fun i ↦ if i < k then F i else max c (valueTable Yh (i - (k - 1))),
    fun i i' hii' ↦ ?_, ?_, fun i ↦ ?_, fun i hi hiH ↦ ?_, fun d ↦ ?_, fun i hi ↦ ?_, ?_,
    fun d hd ↦ ?_⟩
  · dsimp only
    by_cases hi' : i' < k
    · rw [ite_eq_left hi', ite_eq_left (by omega)]
      exact hF hii'
    · by_cases hi : i < k
      · rw [ite_eq_left hi, ite_eq_right hi']
        exact (hlow i hi).le.trans (le_max_left _ _)
      · rw [ite_eq_right hi, ite_eq_right hi']
        exact max_le_max le_rfl (monotone_valueTable (by omega))
  · dsimp only
    rw [ite_eq_left (by omega)]
    exact hF0
  · dsimp only
    split_ifs
    · exact hFv i
    · exact hc.max (isSelfVisible_valueTable hYhv _)
  · dsimp only
    split_ifs with hik
    · exact hFp i hi hiH
    · exact fun h ↦ hcb.ne' (le_bot_iff.mp (h ▸ le_max_left _ _))
  · change min (wv d) k = min (bv d) k
    by_cases hb : bv d < k
    · rw [hwlow d hb]
    · have := hwhigh d (not_lt.mp hb)
      omega
  · dsimp only
    rw [ite_eq_left hi]
  · dsimp only
    rw [ite_eq_right (lt_irrefl k)]
    exact le_max_left _ _
  · change (if wv d < k then F (wv d) else max c (valueTable Yh (wv d - (k - 1)))) = Y d
    by_cases hb : bv d < k
    · rw [hwlow d hb, ite_eq_left hb, hYlow d hd hb]
    · have hbh := not_lt.mp hb
      have hk' := hwhigh d hbh
      rw [hwhigh1 d hd hbh] at hk' ⊢
      rw [ite_eq_right (by omega), show k - 1 + j d - (k - 1) = j d by omega]
      simp only [hj]
      rw [← hYhe d hd hbh, valueTable_valueRank, hYhe d hd hbh, max_eq_right (hYhigh d hd hbh)]

/-- **The rank vector of a lawful state is a rank member**, at a height at least the number of
cells. -/
noncomputable def RankMember.ofLawful (hwf : S.IsWellFormed) (hcard : S.card ≤ H)
    {R : Fin S.card → Label.{u}} (hR : S.rows.IsLawful R) : RankMember S H :=
  ⟨fun d ↦ ⟨rankVector R d, Nat.lt_succ_of_le ((rankVector_le d).trans (by simpa using hcard))⟩,
    fun i hi d hd ↦ by
      obtain ⟨e, -, he⟩ := exists_valueRank_eq (Z := R) hi
        ((show i ≤ valueRank R (R d) from hd).trans (valueRank_le_card_values _))
      exact ⟨e, he⟩,
    fun _ hf h0 hv hp ↦ isLawful_rankTable hwf hR
      (fun d ↦ (rankVector_le d).trans (by simpa using hcard)) hf h0 hv hp⟩

theorem rankProf_ofLawful (hwf : S.IsWellFormed) (hcard : S.card ≤ H)
    {R : Fin S.card → Label.{u}} (hR : S.rows.IsLawful R) (d : Fin S.card) :
    rankProf S H (RankMember.ofLawful hwf hcard hR) d = rankVector R d := rfl

/-! ### The padded grade-one base over the rank members -/

/-- **The ladder base over the rank members is consistent.** -/
theorem isConsistent_ladderBase_rankMember {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hcons : S.rows.IsConsistent) (hH : 0 < H) :
    (ladderBase H (rankProf.{u} S H) hS).rows.IsConsistent :=
  isConsistent_ladderBase hwf hcons hH (rankProf_le S H) (rankTablesLawful_rankMember S H)

/-- **The lift into the full face of grade one over the rank members**: for `X ≤ (univ, 1)` not
above `(univ, 1)`, the ladder base over the rank members lifts capped from `X` to `(univ, 1)`
whenever `S` does, at a height at least the number of cells. -/
theorem cappedLift_ladderBase_rankMember {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hcard : S.card ≤ H) {X : Finset (Fin n) × ℕ}
    (hXU : X ≤ ((univ : Finset (Fin n)), 1)) (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X)
    (hold : S.rows.CappedLift hXU) :
    (ladderBase H (rankProf.{u} S H) hS).rows.CappedLift hXU :=
  cappedLift_ladderBase_one hwf hH (rankProf_le S H) (rankGlue_rankMember hwf hcard) hXU hX hold

/-- **The lift into the full face of grade one through two faces**: if the cells of `S` of grade
one lie below `U` or below `V` (two pairs below `(univ, 1)`), those below both lie below `O`, and
`S` lifts capped from `I` to `U` and from `O` to `V`, then the ladder base over the rank members
lifts capped from `I` to `(univ, 1)` (`CellScheme.Rows.cappedLift_of_union`).  For the attachment
of a donor to a context along a root, `U` and `V` are the context and donor faces at grade one and
`O` the root. -/
theorem cappedLift_ladderBase_rankMember_of_union {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hcard : S.card ≤ H) {I U V O : Finset (Fin n) × ℕ}
    (hIU : I ≤ U) (hOU : O ≤ U) (hOV : O ≤ V) (hUY : U ≤ ((univ : Finset (Fin n)), 1))
    (hVY : V ≤ ((univ : Finset (Fin n)), 1)) (hI : ¬ ((univ : Finset (Fin n)), 1) ≤ I)
    (hcover : ∀ d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), 1),
      d ∈ S.toCellScheme.below U ∨ d ∈ S.toCellScheme.below V)
    (hinter : ∀ d ∈ S.toCellScheme.below U, d ∈ S.toCellScheme.below V →
      d ∈ S.toCellScheme.below O)
    (hleft : S.rows.CappedLift hIU) (hright : S.rows.CappedLift hOV) :
    (ladderBase H (rankProf.{u} S H) hS).rows.CappedLift (hIU.trans hUY) :=
  cappedLift_ladderBase_rankMember hwf hH hcard _ hI
    (CellScheme.Rows.cappedLift_of_union hIU hOU hOV hUY hVY hcover hinter hleft hright)

end Scheme

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Extension.LadderRendering

/-!
# The lift into the full face of grade one of the ladder base

Roadmap, Layer 3 ((R3) and (R4), legality of the padded grade-one base at the ladder).

Let `X ≤ (univ, 1)` be a pair below the full face of grade one and not above it.  The cells of the
ladder base below `X` are old cells of grade one; below `(univ, 1)` lie the old cells of grade one
and all the ladder points.  **The base lifts capped from `X` to `(univ, 1)`**
(`Scheme.cappedLift_ladderBase_one`) when `S` does and the members are closed under **gluing of
rank vectors** (`Scheme.RankGlue`):

* a lawful section `v` of the base below `(univ, 1)` is, at grade one, `⊥` or the rendering of a
  positive table `F` for a member `b` (`Scheme.exists_render_of_isLawful`);
* the lift of `S` gives the old cells of grade one a labelling `Y`, lawful, agreeing with `v`
  capped at the cap `c`, and equal to the prescription below `X`;
* at the cap `⊥` gluing at the cut `0` gives a member and a table reading `Y`; at a positive cap,
  if `F` stays below `c` up to the height, `v` itself is the lift; otherwise at the first rank `k`
  where `F` reaches `c`, gluing gives a member `a` agreeing with `b` capped at `k` and a table
  equal to `F` before `k`, reaching `c` at `k`, reading `Y`.  Its rendering is lawful
  (`Scheme.isLawful_render`) and agrees with that of `F` for `b`, hence with `v`, capped at `c`
  (`Scheme.min_render_eq_of_prefix`).

Gluing is a closure property of the members; it is the remaining content of the lift.

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {X Y : Finset α × ℕ}

/-- **Capped lifts from labellings of all cells**: it suffices to extend labellings of all cells,
lawful below `X` and `Y` and agreeing capped at `c` below `X`. -/
theorem cappedLift_of_forall_full (h : X ≤ Y)
    (H : ∀ c : Label.{u}, IsSelfVisible Y.2 c → ∀ w v : ι → Label.{u},
      R.IsLawfulBelow X (fun e ↦ w e) → R.IsLawfulBelow Y (fun e ↦ v e) →
      (∀ e ∈ D.below X, min (v e) c = min (w e) c) →
      ∃ r : ι → Label.{u}, R.IsLawfulBelow Y (fun e ↦ r e) ∧
        (∀ e ∈ D.below Y, min (r e) c = min (v e) c) ∧ ∀ e ∈ D.below X, r e = w e) :
    R.CappedLift h := by
  refine (cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨r, hr, hrc, hrp⟩ := H c hc (extendBot X p) (extendBot Y q)
    (isLawfulBelow_extendBot.mpr hp) (isLawfulBelow_extendBot.mpr hq) fun e he ↦ by
      rw [extendBot_of_mem _ he, extendBot_of_mem _ (D.below_mono h he)]
      exact hpq ⟨e, he⟩
  exact ⟨fun e ↦ r e, hr, fun e ↦ by rw [hrc e e.2, extendBot_of_mem _ e.2],
    fun e ↦ (hrp e.1 e.2).trans (extendBot_of_mem p e.2)⟩

end CellScheme.Rows

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {Q : Type} [Fintype Q] {H : ℕ} {prof : Q → Fin S.card → ℕ}

/-- **The old cells of a lawful section of the base form a lawful section of `S`.** -/
theorem isLawful_castAdd_of_isLawful {hS : S.NoFullOne}
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (ladderBase H prof hS).rows.IsLawful v) :
    S.rows.IsLawful fun d ↦ v (Fin.castAdd _ d) := by
  have h := hv.comap (isLowerEmbedding_castAdd (S := S) 1 (ladderCard S Q H) (baseRow H prof) hS)
  rw [comap_rows_castAdd] at h
  exact h

variable (S H prof) in
/-- **Gluing of rank vectors**: for a member `b` with a positive table `F`, a cut `k ≤ H` before
which `F` is below a cap `c` self-visible at `1` and at which it is at least `c`, and a labelling
`Y` of the cells, lawful on `S` at grade one (`⊥` above) and agreeing with the table of `b`
capped at `c` at grade one, some member `a` agrees with `b` capped at `k` and has a positive table
`F'`, equal to `F` before `k` and at least `c` at `k`, that reads `Y` at the ranks of `a` at grade
one. -/
def RankGlue : Prop :=
  ∀ (b : Q) (F : ℕ → Label.{u}) (k : ℕ) (c : Label.{u}) (Y : Fin S.card → Label.{u}),
    Monotone F → F 0 = ⊥ → (∀ i, IsSelfVisible 1 (F i)) → (∀ i, 0 < i → i ≤ H → F i ≠ ⊥) →
    k ≤ H → (∀ i < k, F i < c) → c ≤ F k → IsSelfVisible 1 c →
    S.rows.IsLawful (fun d ↦ if S.toCellScheme.grade d = 1 then Y d else ⊥) →
    (∀ d, S.toCellScheme.grade d = 1 → min (Y d) c = min (F (prof b d)) c) →
    ∃ (a : Q) (F' : ℕ → Label.{u}), Monotone F' ∧ F' 0 = ⊥ ∧ (∀ i, IsSelfVisible 1 (F' i)) ∧
      (∀ i, 0 < i → i ≤ H → F' i ≠ ⊥) ∧ (∀ d, min (prof a d) k = min (prof b d) k) ∧
      (∀ i < k, F' i = F i) ∧ c ≤ F' k ∧
      ∀ d, S.toCellScheme.grade d = 1 → F' (prof a d) = Y d

/-- **The lift into the full face of grade one**: for `X ≤ (univ, 1)` not above `(univ, 1)`, the
ladder base lifts capped from `X` to `(univ, 1)` when `S` does and the members glue. -/
theorem cappedLift_ladderBase_one [Nonempty Q] {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H) (hglue : RankGlue S H prof)
    {X : Finset (Fin n) × ℕ} (hXU : X ≤ ((univ : Finset (Fin n)), 1))
    (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X) (hold : S.rows.CappedLift hXU) :
    (ladderBase H prof hS).rows.CappedLift hXU := by
  classical
  refine CellScheme.Rows.cappedLift_of_forall_full hXU fun c hc w v hw hv hwv ↦ ?_
  have hc1 : IsSelfVisible 1 c := hc
  -- the cells below the full face of grade one are the cells of grade one
  have hgpos (t : Fin (S.card + ladderCard S Q H)) :
      0 < (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t := by
    induction t using Fin.addCases with
    | left d => rw [appendFullCellsScheme_grade_castAdd]; exact hwf.isWellFormed.grade_pos d
    | right j => rw [appendFullCellsScheme_grade_natAdd]; omega
  have hU (t : Fin (S.card + ladderCard S Q H)) :
      t ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) ↔
        (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 :=
    ⟨fun ht ↦ grade_eq_one_of_mem_below hwf ht, fun ht ↦ ⟨subset_univ _, ht.le⟩⟩
  have hSU (d : Fin S.card) : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), 1) ↔
      S.toCellScheme.grade d = 1 :=
    ⟨fun hd ↦ by
      have h1 := hwf.isWellFormed.grade_pos d
      have h2 : S.toCellScheme.grade d ≤ 1 := hd.2
      omega,
      fun hd ↦ ⟨subset_univ _, hd.le⟩⟩
  -- the cells below `X` are old cells of grade one
  have hXold (e : Fin (S.card + ladderCard S Q H))
      (he : e ∈ (ladderBase H prof hS).toCellScheme.below X) :
      ∃ d, e = Fin.castAdd _ d ∧ d ∈ S.toCellScheme.below X ∧
        S.toCellScheme.grade d = 1 := by
    rw [← image_castAdd_below (r := baseRow H prof) (h := hS) hX] at he
    obtain ⟨d, hd, rfl⟩ := he
    exact ⟨d, rfl, hd, (hSU d).mp (S.toCellScheme.below_mono hXU hd)⟩
  -- the section `v`, made `⊥` above grade one, is lawful on the base
  set v0 : Fin (S.card + ladderCard S Q H) → Label.{u} := fun t ↦
    if (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 then v t else ⊥ with hv0
  have hv0l : (ladderBase H prof hS).rows.IsLawful v0 := by
    have h := isLawful_splice_bot (S := ladderBase H prof hS) (k := 1) hv
    convert h using 1
    funext t
    simp only [hv0, CellScheme.splice]
    by_cases ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1
    · rw [ite_eq_left ht, ite_eq_left ht.le]
    · rw [ite_eq_right ht, ite_eq_right (by have := hgpos t; omega)]
  -- the lift of `S`
  have hwold : S.rows.IsLawfulBelow X fun d ↦ w (Fin.castAdd _ d) :=
    (isLawfulBelow_ladderBase_iff hX).mp hw
  have hvold : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1)
      fun d ↦ v (Fin.castAdd _ d) := by
    have h := (isLawful_castAdd_of_isLawful hv0l).isLawfulBelow ((univ : Finset (Fin n)), 1)
    convert h using 1
    funext d
    simp only [hv0, appendFullCellsScheme_grade_castAdd, ite_eq_left ((hSU d).mp d.2)]
  obtain ⟨q', hq', hq'c, hq'w⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXU).mp hold c hc
    (fun d ↦ w (Fin.castAdd _ d)) (fun d ↦ v (Fin.castAdd _ d)) hwold hvold
    fun d ↦ by
      have h := hwv (Fin.castAdd _ d) (by
        rw [← image_castAdd_below (r := baseRow H prof) (h := hS) hX]
        exact ⟨d, d.2, rfl⟩)
      exact h
  set Y : Fin S.card → Label.{u} := CellScheme.Rows.extendBot _ q' with hY
  have hYl : S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then Y d else ⊥ := by
    have h := isLawful_splice_bot (S := S) (k := 1)
      (CellScheme.Rows.isLawfulBelow_extendBot.mpr hq')
    convert h using 1
    funext d
    simp only [CellScheme.splice]
    by_cases hd : S.toCellScheme.grade d = 1
    · rw [ite_eq_left hd, ite_eq_left hd.le]
    · rw [ite_eq_right hd, ite_eq_right (by have := hwf.isWellFormed.grade_pos d; omega)]
  have hYv (d : Fin S.card) (hd : S.toCellScheme.grade d = 1) :
      min (Y d) c = min (v (Fin.castAdd _ d)) c := by
    rw [hY, CellScheme.Rows.extendBot_of_mem _ ((hSU d).mpr hd)]
    exact hq'c ⟨d, (hSU d).mpr hd⟩
  have hYw (d : Fin S.card) (hd : d ∈ S.toCellScheme.below X) : Y d = w (Fin.castAdd _ d) := by
    rw [hY, CellScheme.Rows.extendBot_of_mem _ (S.toCellScheme.below_mono hXU hd)]
    exact hq'w ⟨d, hd⟩
  -- the rendering of a glued table is the lift
  have hfinish (a : Q) (F' : ℕ → Label.{u}) (hF' : Monotone F') (hF'0 : F' 0 = ⊥)
      (hF'v : ∀ i, IsSelfVisible 1 (F' i)) (hF'p : ∀ i, 0 < i → i ≤ H → F' i ≠ ⊥)
      (hF'Y : ∀ d, S.toCellScheme.grade d = 1 → F' (prof a d) = Y d)
      (hcap : ∀ e ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1),
        min (render S H prof a F' e) c = min (v e) c) :
      ∃ r : Fin (S.card + ladderCard S Q H) → Label.{u},
        (ladderBase H prof hS).rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) (fun e ↦ r e) ∧
        (∀ e ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1),
          min (r e) c = min (v e) c) ∧
        ∀ e ∈ (ladderBase H prof hS).toCellScheme.below X, r e = w e := by
    refine ⟨render S H prof a F',
      (isLawful_render hwf hH hprof a hF' hF'0 hF'v hF'p ?_).isLawfulBelow _,
      hcap, fun e he ↦ ?_⟩
    · convert hYl using 1
      funext d
      by_cases hd : S.toCellScheme.grade d = 1
      · rw [ite_eq_left hd, ite_eq_left hd, hF'Y d hd]
      · rw [ite_eq_right hd, ite_eq_right hd]
    · obtain ⟨d, rfl, hdX, hd1⟩ := hXold e he
      rw [render_castAdd, ite_eq_left hd1, hF'Y d hd1, hYw d hdX]
  by_cases hcb : c = ⊥
  · -- the cap `⊥`: gluing at the cut `0`
    obtain ⟨b⟩ := ‹Nonempty Q›
    obtain ⟨a, F', hF', hF'0, hF'v, hF'p, -, -, -, hF'Y⟩ := hglue b (ladderSource H) 0 c Y
      (monotone_ladderSource H) (ladderSource_zero H) (isSelfVisible_ladderSource H)
      (fun i hi hiH h0 ↦ by rw [ladderSource_eq_bot_iff] at h0; omega) (Nat.zero_le _)
      (fun _ h ↦ absurd h (Nat.not_lt_zero _)) (hcb ▸ bot_le) hc1 hYl
      (fun d _ ↦ by rw [hcb, min_bot_right, min_bot_right])
    exact hfinish a F' hF' hF'0 hF'v hF'p hF'Y fun e _ ↦ by rw [hcb, min_bot_right, min_bot_right]
  -- a positive cap: the shape of `v`
  rcases exists_render_of_isLawful hwf hH hprof hv0l with hzero | ⟨b, F, hF, hF0, hFv, hFp, hFv0⟩
  · -- `v` is `⊥` at grade one: it is the lift
    refine ⟨v, hv, fun _ _ ↦ rfl, fun e he ↦ ?_⟩
    obtain ⟨d, rfl, -, hd1⟩ := hXold e he
    have hg : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade (Fin.castAdd _ d) = 1 :=
      by
      rw [appendFullCellsScheme_grade_castAdd]; exact hd1
    have h0 : v (Fin.castAdd _ d) = ⊥ := by
      have := hzero _ hg
      simpa only [hv0, ite_eq_left hg] using this
    have h := hwv _ he
    rw [h0, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h.symm with h' | h'
    · rw [h0, h']
    · exact absurd h' hcb
  have hvF (t : Fin (S.card + ladderCard S Q H))
      (ht : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1) :
      v t = F (baseIndex H prof b t) := by
    have := hFv0 t ht
    simpa only [hv0, ite_eq_left ht] using this
  by_cases hreach : ∃ i, i ≤ H ∧ c ≤ F i
  swap
  · -- `F` stays below the cap: `v` is the lift
    push Not at hreach
    refine ⟨v, hv, fun _ _ ↦ rfl, fun e he ↦ ?_⟩
    obtain ⟨d, rfl, -, hd1⟩ := hXold e he
    have hg : (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade (Fin.castAdd _ d) = 1 :=
      by
      rw [appendFullCellsScheme_grade_castAdd]; exact hd1
    have hlt : v (Fin.castAdd _ d) < c := by
      rw [hvF _ hg]; exact hreach _ (baseIndex_le hprof b _)
    have h := hwv _ he
    rw [min_eq_left hlt.le] at h
    rcases le_total (w (Fin.castAdd _ d)) c with hle | hle
    · rw [min_eq_left hle] at h; exact h
    · rw [min_eq_right hle] at h; exact absurd h hlt.ne
  -- the first rank where `F` reaches the cap
  set k := Nat.find hreach with hk
  obtain ⟨hkH, hck⟩ := Nat.find_spec hreach
  have hlow (i : ℕ) (hi : i < k) : F i < c := by
    have := Nat.find_min hreach hi
    push Not at this
    exact this (by omega)
  obtain ⟨a, F', hF', hF'0, hF'v, hF'p, hab, hF'low, hF'k, hF'Y⟩ := hglue b F k c Y hF hF0 hFv hFp
    hkH hlow hck hc1 hYl fun d hd ↦ by
      rw [hYv d hd, hvF _ (by rw [appendFullCellsScheme_grade_castAdd]; exact hd),
        baseIndex_castAdd]
  refine hfinish a F' hF' hF'0 hF'v hF'p hF'Y fun e he ↦ ?_
  have he1 := (hU e).mp he
  rw [min_render_eq_of_prefix hkH hab hF' hF hF'low hF'k hck e, hvF e he1, render, ite_eq_left he1]

end Scheme

end VaughtConjecture

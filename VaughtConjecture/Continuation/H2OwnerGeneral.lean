/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OwnerAt

/-!
# Owner lowering below the designated tops on the grade-`K` faces at every arity (work file)

WORK FILE (branch `research/work-owner-general`).  No `sorry`.

On `k + 1` points with the lost point last, below the full grade (`K ≤ k`), **owner lowering
below the designated tops on the grade-`K` faces** (`H2.OwnerLoweringBelowAt k`) holds with no
condition on the root of the donor faces (`H2.RootBelowTops` is not used), under the named
condition `H2.TopsAtLeastGrade` on the designated tops; at `k = 1` with no condition
(`H2.ownerLoweringBelowAt_one`).

**The lowered face at a cap `c > ⊥`** (`H2.exists_lowered_at`), self-visible at `K`, at least `h`
and at least every root cell not labelled `⊤`.  Let `W₁` be the capped lift at `h` from the root of
the donor face (bountifulness).  If its frontier is at most `c` it serves.  Otherwise the owner is
above `c`; with `c'` the next label self-visible at `K` above `c`
(`H2.exists_next_isSelfVisible`, nothing strictly between), `W₁` capped at `c'` has its largest
label at the owner.  Cap it at `c` at the cells read by the owner at most the **threshold**
`visibilityReplace K K (rowAt o r)` (`H2.capBelowAt`): a grade-`K` face
(`H2.lawfulAt_capBelowAt_of_max`) with frontier at most `c`, agreeing with the root of the donor
face capped at `c'` (root tops are read above the threshold by the strict source gaps; the other
root cells are below `c`).  The capped lift at `c'` from the root of the donor face with this face
as ambient restores the root exactly and keeps the frontier.  The capped face is lawful:
* at a capped cell, locality is that of the face capped at `c`;
* at a cell `s` not capped, the row of the owner is lawful (consistency), so its values below `s`,
  capped at its value at `s`, are a transformation `τ` of the row of `s`; the capped cells below
  `s` are those whose argument has `τ`-image at most the threshold, a set closed downward and
  invariant under replacement at every threshold up to the grade of `s`, and capping the shifter
  of `s` there gives a witness (`H2.isWitness_capBelowAt`, which needs `c > ⊥`);
* availability from a source `s` not capped is served by the cell serving it in the row of the
  owner, not capped, and above `s` since the face is a transformation of the row of the owner
  (the owner carries the largest label).

**The cap** (`H2.ownerLoweringBelow_of_topsAtLeastGrade`).  With the designated cells below the top
`Lo` (every cell not labelled `⊤`), take `c = max h (visibilityReplace K K (Lo.sup g))`, at most
every designated top concerned.  If it is `⊥` (so `h = ⊥` and the low maximum is `⊥`), take `c = K`,
the least label above `⊥` self-visible at `K`; it is at most every designated top concerned under
**`H2.TopsAtLeastGrade`**: every designated top above `⊥` of a donor face with low maximum `⊥` is
at least `K`.  This holds at `K = 1` (`H2.topsAtLeastGrade_one`) and when the designated tops have
grade `K` (`H2.topsAtLeastGrade_of_grade`).

**The residual** (argued, not compiled): `h = ⊥`, low maximum `⊥`, and a designated top `t` of grade
below `K` with `⊥ < g t < K`.  The frontier, self-visible at `K`, must then be `⊥`.  Capping at `⊥`
fails: if the owner reads the lost top at `μ + j` and a root top at `μ + j'` in the same block
(`j < K < j'`, so the strict gap `μ + K < μ + j'` holds), a witness sending `μ + j` to
`⊥` sends `μ + j'` to `⊥` (replacement at a threshold above `j'`), so the lost top at `⊥` forces the
root top or the owner to `⊥`; when the owner is the only cell of its graded index above that root
top of grade `K`, availability keeps the owner above `⊥`.  So a context on three points with these
readings and such a donor would refute owner lowering below the designated tops there.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission CellScheme

/-! ### Labels -/

/-- Replacement keeps a label above a bound self-visible at the threshold above it. -/
theorem lt_visibilityReplace_of_lt {k i : ℕ} (hi : i ≤ k) {θ y : Label.{u}}
    (hθ : IsSelfVisible k θ) (hy : θ < y) : θ < visibilityReplace k i y := by
  by_contra h
  have h' := monotone_visibilityReplace (le_refl k) (not_lt.mp h)
  rw [visibilityReplace_self_visibilityReplace hi, hθ] at h'
  exact hy.not_ge ((le_visibilityReplace (by omega) y).trans h')

/-- **The next label self-visible at `K`**: above a label `⊥ < c < ⊤` self-visible at `K` there is a
label `c'` self-visible at `K` with nothing strictly between. -/
theorem exists_next_isSelfVisible {K : ℕ} {c : Label.{u}} (hc : IsSelfVisible K c)
    (hc0 : ⊥ < c) (hct : c ≠ ⊤) :
    ∃ c' : Label.{u}, IsSelfVisible K c' ∧ c < c' ∧ ∀ x, c < x → c' ≤ x := by
  induction c using recBotCoeTop with
  | bot => exact absurd hc0 (lt_irrefl _)
  | top => exact absurd rfl hct
  | coe μ =>
    obtain ⟨ν₀, hν₀, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit μ
    have hjK : K ≤ j := (isSelfVisible_coe_add_natCast_iff hν₀).mp hc
    have hsucc : ν₀ + ((j + 1 : ℕ) : Ordinal.{u}) = Order.succ (ν₀ + (j : Ordinal.{u})) := by
      rw [Order.succ_eq_add_one, add_assoc, Nat.cast_succ]
    refine ⟨((ν₀ + ((j + 1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}),
      isSelfVisible_coe_add hν₀ (by omega), ?_, fun x hx ↦ ?_⟩
    · rw [hsucc]
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (Order.lt_succ _))
    · induction x using recBotCoeTop with
      | bot => exact absurd hx (not_lt_bot)
      | top => exact le_top
      | coe ν =>
        rw [hsucc]
        exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
          (Order.succ_le_of_lt (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hx))))

/-- **Capping a shifter below a threshold of another reading, at a bound `M` of the grades.**  Let
`(g, σ)` and `(gτ, τ)` be witnesses, `θ` self-visible at `M` and below `gτ M`, and `c > ⊥`
self-visible at `M`.  Capping `σ` at `c` at the arguments `x` with `τ x ≤ θ` gives a witness with
the suppressor truncated above `M`: the set `τ x ≤ θ` is closed downward and invariant under
replacement at every threshold at most `M`. -/
theorem isWitness_capBelowAt {M : ℕ} {g gτ : ℕ → Label.{u}} {σ τ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) (hτ : IsWitness gτ τ) {θ c : Label.{u}} (hθ : IsSelfVisible M θ)
    (hθg : θ < gτ M) (hc : IsSelfVisible M c) (hc0 : ⊥ < c) :
    IsWitness (fun n ↦ if n ≤ M then g n else ⊥)
      (fun x ↦ if τ x ≤ θ then min (σ x) c else σ x) := by
  have hw' := hw.truncate M
  have hinv (x : Label.{u}) {k i : ℕ} (hk : k ≤ M) (hi : i ≤ k) :
      τ (visibilityReplace k i x) ≤ θ ↔ τ x ≤ θ := by
    have hθk : θ < gτ k := hθg.trans_le (hτ.antitone hk)
    constructor
    · intro h
      by_contra hx
      have hx' : θ < τ x := not_le.mp hx
      by_cases hg : τ x ≤ gτ k
      · rw [hτ.visibilityReplace_comm x k hg i hi] at h
        exact (lt_visibilityReplace_of_lt hi (hθ.mono hk) hx').not_ge h
      · exact (hθk.trans (hτ.lt_apply_visibilityReplace (not_le.mp hg) hi)).not_ge h
    · intro h
      rw [hτ.visibilityReplace_comm x k (h.trans hθk.le) i hi]
      calc visibilityReplace k i (τ x) ≤ visibilityReplace k i θ :=
            monotone_visibilityReplace hi h
        _ = θ := (hθ.mono hk).visibilityReplace_eq i
  refine ⟨hw'.antitone, hw'.isSelfVisible, ?_, ?_, ?_⟩
  · simp only [hw.map_bot, hτ.map_bot, bot_le, ite_true, min_eq_left]
  · intro x y hxy
    simp only
    split_ifs with h1 h2 h2
    · exact min_le_min_right c (hw.monotone hxy)
    · exact (min_le_left _ _).trans (hw.monotone hxy)
    · exact absurd ((hτ.monotone hxy).trans h2) h1
    · exact hw.monotone hxy
  · intro x k hx i hi
    by_cases hk : k ≤ M
    · simp only [hinv x hk hi]
      have hck : IsSelfVisible k c := hc.mono hk
      split_ifs with hP
      · have hx' : min (σ x) c ≤ g k := by simpa [hP, hk] using hx
        rw [visibilityReplace_min hi, hck.visibilityReplace_eq]
        by_cases hσ : σ x ≤ g k
        · rw [hw.visibilityReplace_comm x k hσ i hi]
        · have hcg : c ≤ g k := by
            rcases le_total (σ x) c with h | h
            · exact absurd ((min_eq_left h) ▸ hx') hσ
            · exact (min_eq_right h) ▸ hx'
          have hlt : c < σ x := hcg.trans_lt (not_le.mp hσ)
          rw [min_eq_right (hcg.trans (hw.lt_apply_visibilityReplace (not_le.mp hσ) hi).le),
            min_eq_right (lt_visibilityReplace_of_lt hi hck hlt).le]
      · have hx' : σ x ≤ g k := by simpa [hP, hk] using hx
        exact hw.visibilityReplace_comm x k hx' i hi
    · have hx' : (if τ x ≤ θ then min (σ x) c else σ x) = ⊥ := by
        simpa only [hk, ite_false, le_bot_iff] using hx
      have hσ0 : σ x = ⊥ := by
        split_ifs at hx' with hP
        · rcases le_total (σ x) c with h | h
          · exact (min_eq_left h) ▸ hx'
          · exact absurd ((min_eq_right h) ▸ hx') hc0.ne'
        · exact hx'
      have hcomm := hw'.visibilityReplace_comm x k (by simp only [hk, ite_false, hσ0, le_refl]) i hi
      rw [hσ0, visibilityReplace_bot] at hcomm
      have hle : (if τ (visibilityReplace k i x) ≤ θ then min (σ (visibilityReplace k i x)) c
          else σ (visibilityReplace k i x)) ≤ σ (visibilityReplace k i x) := by
        split_ifs
        · exact min_le_left _ _
        · exact le_rfl
      rw [hx', visibilityReplace_bot]
      exact le_bot_iff.mp (hcomm ▸ hle)

/-! ### Capping below the threshold of the owner -/

section Cap

variable {α : Ordinal.{u}} {m K : ℕ} {t' : StageType.{u} α m} {n : ℕ} {h₀ : Fin n ↪ Fin m}
  {l : Fin m} {o r : Fin t'.card}

/-- The **threshold** of a context of grade `K` at the owner: the replaced reading of the lost
top. -/
noncomputable def thresholdAt (t' : StageType.{u} α m) (K : ℕ) (o r : Fin t'.card) : Label.{u} :=
  visibilityReplace K K (t'.rowAt o r)

/-- **The labelling capped below the threshold**: capped at `c` at the cells read by the owner at
most the threshold. -/
noncomputable def capBelowAt (t' : StageType.{u} α m) (K : ℕ) (o r : Fin t'.card)
    (W : Fin t'.card → Label.{u}) (c : Label.{u}) (d : Fin t'.card) : Label.{u} :=
  if t'.rowAt o d ≤ thresholdAt t' K o r then min (W d) c else W d

theorem capBelowAt_le (W : Fin t'.card → Label.{u}) (c : Label.{u}) (d : Fin t'.card) :
    capBelowAt t' K o r W c d ≤ W d := by
  unfold capBelowAt
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem capBelowAt_of_le {W : Fin t'.card → Label.{u}} {c : Label.{u}} {d : Fin t'.card}
    (hd : t'.rowAt o d ≤ thresholdAt t' K o r) : capBelowAt t' K o r W c d = min (W d) c := by
  simp only [capBelowAt, hd, ↓reduceIte]

theorem capBelowAt_of_not_le {W : Fin t'.card → Label.{u}} {c : Label.{u}} {d : Fin t'.card}
    (hd : ¬ t'.rowAt o d ≤ thresholdAt t' K o r) : capBelowAt t' K o r W c d = W d := by
  simp only [capBelowAt, hd, ↓reduceIte]

/-- **Capping below the threshold keeps a grade-`K` face carrying its largest label at the
owner**, for a cap `c > ⊥` self-visible at `K`.  At a capped cell, locality is that of the face
capped at `c`.  At a cell `s` not capped, the row of the owner is lawful (consistency), so its
values below `s`, capped at its value at `s`, are a transformation `τ` of the row of `s`; the
capped cells below `s` are those whose argument has `τ`-image at most the threshold, and capping
the shifter of `s` there gives a witness (`H2.isWitness_capBelowAt` at the grade of `s`).
Availability from a capped source is that of the face; from a source `s` not capped it is served
by the cell `u` serving `s` in the row of the owner: `u` is not capped, and the face, below its
value at the owner, is a transformation of the row of the owner, so `s` is at most `u` there. -/
theorem lawfulAt_capBelowAt_of_max (hleg : t'.IsLegal) (hs : t'.IsSourceGapContextAt K h₀ l o r)
    {W : Fin t'.card → Label.{u}} (hW : LawfulAt t' K W) (hmax : ∀ d, W d ≤ W o)
    {c : Label.{u}} (hc : IsSelfVisible K c) (hc0 : ⊥ < c) :
    LawfulAt t' K (capBelowAt t' K o r W c) := by
  classical
  set X := t'.toCellScheme.gradedIndex o with hX
  set θ := thresholdAt t' K o r
  have hgi : X = ((univ : Finset (Fin m)), K) := Prod.ext hs.scope_owner hs.grade_owner
  have hθ : IsSelfVisible K θ := visibilityReplace_self_visibilityReplace le_rfl _
  have hmem (d : Fin t'.card) : d ∈ t'.toCellScheme.below X ↔ t'.toCellScheme.grade d ≤ K := by
    rw [hgi]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨subset_univ _, h⟩⟩
  have hWX : t'.rows.IsLawfulBelow X (fun d ↦ W d) := by rw [hgi]; exact hW.1
  obtain ⟨hWo, hWl, hWa⟩ := Rows.isLawfulBelow_iff_forall.mp hWX
  have hRX : t'.rows.IsLawfulBelow X (fun d ↦ t'.rowAt o d) := by
    convert hleg.isConsistent o using 1
    funext d
    exact Scheme.rowAt_of_mem d.2
  obtain ⟨-, hRl, hRa⟩ := Rows.isLawfulBelow_iff_forall.mp hRX
  refine ⟨?_, fun d hd ↦ le_bot_iff.mp ((capBelowAt_le W c d).trans (hW.2 d hd).le)⟩
  have key : t'.rows.IsLawfulBelow X (fun d ↦ capBelowAt t' K o r W c d) := by
    refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs' ↦ ?_, fun s t ht hst hg ↦ ?_⟩
    · -- order
      unfold capBelowAt
      split_ifs
      · exact (hWo d hd).min (hc.mono ((hmem d).mp hd))
      · exact hWo d hd
    · -- locality
      have hsK : t'.toCellScheme.grade s ≤ K := (hmem s).mp hs'
      have hgle (d : t'.toCellScheme.below (t'.toCellScheme.gradedIndex s)) :
          t'.toCellScheme.grade d.1 ≤ t'.toCellScheme.grade s := d.2.2
      by_cases hZs : t'.rowAt o s ≤ θ
      · convert (hWl s hs').min_const (K := K) (fun d ↦ (hgle d).trans hsK) hc using 2 with d
        rw [capBelowAt_of_le hZs]
        by_cases hZd : t'.rowAt o d ≤ θ
        · rw [capBelowAt_of_le hZd, min_min_min_comm, min_self]
        · rw [capBelowAt_of_not_le hZd, min_assoc]
      · obtain ⟨g, σ, hw, heq⟩ := hWl s hs'
        obtain ⟨gτ, τ, hτ, heqτ⟩ := hRl s hs'
        set M := t'.toCellScheme.grade s with hM
        have hθs : θ < t'.rowAt o s := not_le.mp hZs
        have hgτ : θ < gτ M := by
          have e : min (t'.rowAt o s) (t'.rowAt o s) = min (τ (t'.rows.row s
              ⟨s, t'.toCellScheme.mem_below_gradedIndex s⟩)) (gτ M) :=
            heqτ ⟨s, t'.toCellScheme.mem_below_gradedIndex s⟩
          rw [min_self] at e
          exact hθs.trans_le (e ▸ min_le_right _ _)
        refine ⟨_, _, isWitness_capBelowAt (M := M) hw hτ (hθ.mono hsK) hgτ (hc.mono hsK) hc0,
          fun d ↦ ?_⟩
        have hgd : t'.toCellScheme.grade d.1 ≤ M := hgle d
        have e : min (W d) (W s) = min (σ (t'.rows.row s d)) (g (t'.toCellScheme.grade d.1)) :=
          heq d
        have eτ : min (t'.rowAt o d) (t'.rowAt o s) =
            min (τ (t'.rows.row s d)) (gτ (t'.toCellScheme.grade d.1)) := heqτ d
        have hθd : θ < gτ (t'.toCellScheme.grade d.1) := hgτ.trans_le (hτ.antitone hgd)
        change min (capBelowAt t' K o r W c d) (capBelowAt t' K o r W c s) =
          min (if τ (t'.rows.row s d) ≤ θ then min (σ (t'.rows.row s d)) c
            else σ (t'.rows.row s d)) (if t'.toCellScheme.grade d.1 ≤ M then g _ else ⊥)
        simp only [hgd, ↓reduceIte]
        rw [capBelowAt_of_not_le hZs]
        by_cases hP : τ (t'.rows.row s d) ≤ θ
        · have hZd : t'.rowAt o d ≤ θ := by
            have h1 : min (t'.rowAt o d) (t'.rowAt o s) ≤ θ := by
              rw [eτ, min_eq_left (hP.trans hθd.le)]
              exact hP
            rcases le_total (t'.rowAt o d) (t'.rowAt o s) with h | h
            · rwa [min_eq_left h] at h1
            · rw [min_eq_right h] at h1
              exact absurd h1 (not_le.mpr hθs)
          simp only [hP, ↓reduceIte]
          rw [capBelowAt_of_le hZd, min_right_comm, e, min_right_comm]
        · have hZd : ¬ t'.rowAt o d ≤ θ := by
            intro hZd
            have h1 : min (t'.rowAt o d) (t'.rowAt o s) ≤ θ := (min_le_left _ _).trans hZd
            rw [eτ] at h1
            rcases le_total (τ (t'.rows.row s d)) (gτ (t'.toCellScheme.grade d.1)) with h | h
            · exact hP ((min_eq_left h) ▸ h1)
            · exact absurd ((min_eq_right h) ▸ h1) (not_le.mpr hθd)
          simp only [hP, ↓reduceIte]
          rw [capBelowAt_of_not_le hZd, e]
    · -- availability
      by_cases hZs : t'.rowAt o s ≤ θ
      · obtain ⟨u, hu, hle⟩ := hWa s t ht hst hg
        refine ⟨u, hu, ?_⟩
        rw [capBelowAt_of_le hZs]
        by_cases hZu : t'.rowAt o u ≤ θ
        · rw [capBelowAt_of_le hZu]
          exact min_le_min_right c hle
        · rw [capBelowAt_of_not_le hZu]
          exact (min_le_left _ _).trans hle
      · obtain ⟨u, hu, hle⟩ := hRa s t ht hst hg
        have hZu : ¬ t'.rowAt o u ≤ θ := fun h ↦ hZs ((show t'.rowAt o s ≤ t'.rowAt o u
          from hle).trans h)
        refine ⟨u, hu, ?_⟩
        rw [capBelowAt_of_not_le hZs, capBelowAt_of_not_le hZu]
        have hsX : s ∈ t'.toCellScheme.below X :=
          (CellScheme.mem_below _).mpr ⟨hst.trans ht.1, hg.le.trans ht.2⟩
        have huX : u ∈ t'.toCellScheme.below X := (CellScheme.mem_below _).mpr (hu ▸ ht)
        have hoX : o ∈ t'.toCellScheme.below X := t'.toCellScheme.mem_below_gradedIndex o
        have hgu : t'.toCellScheme.grade u = t'.toCellScheme.grade s :=
          (congrArg Prod.snd hu).trans hg.symm
        have h1 := (hWl o hoX).le_of_le (d := ⟨s, hsX⟩) (d' := ⟨u, huX⟩)
          (by
            rw [← Scheme.rowAt_of_mem hsX, ← Scheme.rowAt_of_mem huX]
            exact hle) hgu.le
        change min (W s) (W o) ≤ min (W u) (W o) at h1
        rwa [min_eq_left (hmax s), min_eq_left (hmax u)] at h1
  rw [show ((univ : Finset (Fin m)), K) = t'.toCellScheme.gradedIndex o from hgi.symm]
  exact key

/-- A grade-`K` face capped at a label self-visible at `K` is a grade-`K` face. -/
theorem lawfulAt_min {E : StageType.{u} α m} {W : Fin E.card → Label.{u}} (hW : LawfulAt E K W)
    {c : Label.{u}} (hc : IsSelfVisible K c) : LawfulAt E K fun d ↦ min (W d) c :=
  ⟨hW.1.min_const_of_isSelfVisible hc, fun d hd ↦ by simp only [hW.2 d hd, bot_le, min_eq_left]⟩

end Cap

/-! ### The lowered face -/

variable {α : Ordinal.{u}}

/-- **The lowered face at a cap `c > ⊥`**, at a legal source-gap context of grade `K ≤ k` on `k + 1`
points with the lost point last, for a legal donor with the same root face: for every cap `h ≤ c`
self-visible at `K`, every context face `L` and donor face `g` agreeing on the root capped at `h`,
with the root cells not labelled `⊤` at most `c` in `g`, there is a grade-`K` face with the root of
`g`, agreeing with `L` capped at `h`, with frontier at most `c`.  The capped lift `W₁` at `h` serves
if its frontier is at most `c`; otherwise the owner is above `c` in `W₁`, and with `c'` the next
label self-visible at `K` above `c`, `W₁` capped at `c'` has its largest label at the owner; its
capping below the threshold at `c` (`H2.lawfulAt_capBelowAt_of_max`) is a grade-`K` face `L₁` with
frontier at most `c`, agreeing with the root of `g` capped at `c'` (the root tops are read above the
threshold, by the strict source gaps, so not capped); the capped lift at `c'` from the root of `g`
with ambient `L₁` keeps the frontier of `L₁`. -/
theorem exists_lowered_at {k K n : ℕ} {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal)
    {g₀ : Fin n ↪ Fin k} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g₀.trans Fin.castSuccEmb) (Fin.last k) o r) (hKk : K ≤ k)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {h : Label.{u}} (hh : IsSelfVisible K h)
    {L : Fin t'.card → Label.{u}} {g : Fin tb.card → Label.{u}} (hL : LawfulAt t' K L)
    (hg : LawfulAt tb K g)
    (hagr : ∀ x, min (g (StageType.faceCell htbp x)) h = min (L (StageType.faceCell hp x)) h)
    {c : Label.{u}} (hc : IsSelfVisible K c) (hc0 : ⊥ < c) (hhc : h ≤ c)
    (hlow : ∀ x : Fin p.card, p.label x ≠ ⊤ → g (StageType.faceCell htbp x) ≤ c) :
    ∃ W : Fin t'.card → Label.{u}, LawfulAt t' K W ∧
      (∀ x, W (StageType.faceCell hp x) = g (StageType.faceCell htbp x)) ∧
      (∀ d, min (W d) h = min (L d) h) ∧ frontierAt o r K W ≤ c := by
  classical
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hCL : HasCappedLifts (StageType.faceCell htbp) (StageType.faceCell hp) K (LawfulAt tb K)
      (LawfulAt t' K) := hasCappedLifts_lawfulAt' hK0 (by omega) htbleg htbp hleg hp
  obtain ⟨W1, hW1, hW1r, hW1L⟩ := hCL hh hL hg hagr
  by_cases hF : frontierAt o r K W1 ≤ c
  · exact ⟨W1, hW1, hW1r, hW1L, hF⟩
  have hFc : c < frontierAt o r K W1 := not_le.mp hF
  have hct : c ≠ ⊤ := fun e ↦ by rw [e] at hFc; exact not_top_lt hFc
  obtain ⟨c', hc', hcc', hnext⟩ := exists_next_isSelfVisible hc hc0 hct
  have hW1o : c' ≤ W1 o := hnext _ (hFc.trans_le (min_le_left _ _))
  set W2 : Fin t'.card → Label.{u} := fun d ↦ min (W1 d) c' with hW2def
  have hW2 : LawfulAt t' K W2 := lawfulAt_min hW1 hc'
  have hW2o : W2 o = c' := min_eq_right hW1o
  have hmax (d : Fin t'.card) : W2 d ≤ W2 o := hW2o ▸ min_le_right _ _
  set L1 := capBelowAt t' K o r W2 c with hL1def
  have hL1 : LawfulAt t' K L1 := lawfulAt_capBelowAt_of_max hleg hs hW2 hmax hc hc0
  have hroot1 (x : Fin p.card) : min (g (StageType.faceCell htbp x)) c' =
      min (L1 (StageType.faceCell hp x)) c' := by
    by_cases hZ : t'.rowAt o (StageType.faceCell hp x) ≤ thresholdAt t' K o r
    · rw [hL1def, capBelowAt_of_le hZ]
      change _ = min (min (min (W1 _) c') c) c'
      rw [hW1r x]
      have hgx : g (StageType.faceCell htbp x) ≤ c := by
        by_cases hx : p.label x = ⊤
        · exact absurd hZ (not_le.mpr (hs.gap_retained _
            ((StageType.label_faceCell hp x).trans hx)
            (StageType.last_notMem_scope_faceCell hp x)))
        · exact hlow x hx
      rw [min_eq_left (hgx.trans hcc'.le), min_eq_left hgx, min_eq_left (hgx.trans hcc'.le)]
    · rw [hL1def, capBelowAt_of_not_le hZ]
      change _ = min (min (W1 _) c') c'
      rw [hW1r x, min_assoc, min_self]
  obtain ⟨W, hW, hWr, hWL1⟩ := hCL hc' hL1 hg hroot1
  have hhc' : h ≤ c' := hhc.trans hcc'.le
  have hL1h (d : Fin t'.card) : min (L1 d) h = min (W1 d) h := by
    by_cases hZ : t'.rowAt o d ≤ thresholdAt t' K o r
    · rw [hL1def, capBelowAt_of_le hZ]
      change min (min (min (W1 d) c') c) h = _
      rw [min_assoc, min_eq_right hhc, min_assoc, min_eq_right hhc']
    · rw [hL1def, capBelowAt_of_not_le hZ]
      change min (min (W1 d) c') h = _
      rw [min_assoc, min_eq_right hhc']
  have hFL1 : frontierAt o r K L1 ≤ c := by
    have hZr : t'.rowAt o r ≤ thresholdAt t' K o r := le_visibilityReplace (by omega) _
    refine (min_le_right _ _).trans ?_
    rw [hL1def, capBelowAt_of_le hZr, visibilityReplace_min le_rfl, hc.visibilityReplace_eq]
    exact min_le_right _ _
  have hFW : frontierAt o r K W = frontierAt o r K L1 :=
    Label.eq_of_min_eq_of_lt (frontierAt_cap (o := o) (r := r) hc' hWL1).symm
      (hFL1.trans_lt hcc')
  refine ⟨W, hW, hWr, fun d ↦ ?_, hFW ▸ hFL1⟩
  calc min (W d) h = min (min (W d) c') h := by rw [min_assoc, min_eq_right hhc']
    _ = min (min (L1 d) c') h := by rw [hWL1 d]
    _ = min (L1 d) h := by rw [min_assoc, min_eq_right hhc']
    _ = min (W1 d) h := hL1h d
    _ = min (L d) h := hW1L d

/-! ### Owner lowering below the designated tops -/

/-- A label self-visible at `K` above `⊥` is at least `K`. -/
theorem natCast_le_of_isSelfVisible {K : ℕ} {x : Label.{u}} (hx : IsSelfVisible K x)
    (hx0 : ⊥ < x) : ((K : ℕ) : Label.{u}) ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact absurd hx0 (lt_irrefl _)
  | top => exact le_top
  | coe o =>
    have h1 : ((K : ℕ) : Ordinal.{u}) ≤ o := (isSelfVisible_coe.mp hx).trans (Ordinal.mod_le _ _)
    rw [← WithBot.coe_natCast, ← WithTop.coe_natCast]
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h1)

/-- **The designated tops concerned at the bottom are at least the grade** (a named condition on
the donor faces): for every donor face `g` whose designated cells below the top have replaced
maximum `⊥`, every designated top of `g` above `⊥` is at least `K`.  It holds at `K = 1`
(`H2.topsAtLeastGrade_one`) and whenever the designated tops have grade `K`
(`H2.topsAtLeastGrade_of_grade`); it fails only through a designated top of grade below `K` whose
value lies strictly between `⊥` and `K`. -/
def TopsAtLeastGrade {ιD : Type*} (K : ℕ) (D : (ιD → Label.{u}) → Prop) (Lo Tops : Finset ιD) :
    Prop :=
  ∀ {g : ιD → Label.{u}}, D g → visibilityReplace K K (Lo.sup g) = ⊥ → ∀ t ∈ Tops, ⊥ < g t →
    ((K : ℕ) : Label.{u}) ≤ g t

/-- **Owner lowering below the designated tops on the grade-`K` faces** at a legal source-gap
context of grade `K ≤ k` on `k + 1` points with the lost point last, for a legal donor with the
same root face and the designation of the clause (every cell not labelled `⊤` designated below the
top), under `H2.TopsAtLeastGrade`.  The cap is `c = max h (visibilityReplace K K (Lo.sup g))` when
it is above `⊥`, and `K` otherwise (`H2.exists_lowered_at`); it is at most every designated top
concerned, and every root cell not labelled `⊤` is at most it. -/
theorem ownerLoweringBelow_of_topsAtLeastGrade {k K n : ℕ} {t' : StageType.{u} α (k + 1)}
    (hleg : t'.IsLegal) {g₀ : Fin n ↪ Fin k} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g₀.trans Fin.castSuccEmb) (Fin.last k) o r) (hKk : K ≤ k)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hcond : TopsAtLeastGrade K (LawfulAt tb K)
      (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops) :
    OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r K (LawfulAt t' K)
      (LawfulAt tb K) (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops := by
  classical
  intro h hh L g hL hg hagr
  set Lo1 := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K with hLo1
  set m0 := max h (visibilityReplace K K (Lo1.sup g)) with hm0def
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hlowS (x : Fin p.card) (hx : p.label x ≠ ⊤) : g (StageType.faceCell htbp x) ≤ m0 := by
    refine le_trans ?_ ((le_visibilityReplace (by omega) _).trans (le_max_right _ _))
    by_cases hgr : tb.toCellScheme.grade (StageType.faceCell htbp x) ≤ K
    · exact Finset.le_sup (f := g) (mem_filter.mpr
        ⟨hLo _ (by rw [StageType.label_faceCell]; exact hx), hgr⟩)
    · rw [hg.2 _ hgr]
      exact bot_le
  by_cases hm0 : ⊥ < m0
  · have hc : IsSelfVisible K m0 :=
      hh.max (visibilityReplace_self_visibilityReplace le_rfl _)
    obtain ⟨W, hW, hWr, hWL, hWF⟩ := exists_lowered_at hleg hs hKk hp htbleg htbp hh hL hg hagr
      hc hm0 (le_max_left _ _) hlowS
    exact ⟨W, hW, hWr, hWL, fun t _ hht hlt ↦ hWF.trans (max_le hht hlt.le)⟩
  · have hm0b : m0 = ⊥ := le_bot_iff.mp (not_lt.mp hm0)
    have hvr : visibilityReplace K K (Lo1.sup g) = ⊥ :=
      le_bot_iff.mp (hm0b ▸ le_max_right _ _)
    have hcK : IsSelfVisible K ((K : ℕ) : Label.{u}) := (isSelfVisible_natCast K).mpr le_rfl
    have hc0 : (⊥ : Label.{u}) < ((K : ℕ) : Label.{u}) := by
      rw [← WithBot.coe_natCast]
      exact WithBot.bot_lt_coe _
    obtain ⟨W, hW, hWr, hWL, hWF⟩ := exists_lowered_at hleg hs hKk hp htbleg htbp hh hL hg hagr
      hcK hc0 ((hm0b ▸ le_max_left h _ : h ≤ ⊥).trans bot_le)
      (fun x hx ↦ (hlowS x hx).trans (hm0b ▸ bot_le))
    refine ⟨W, hW, hWr, hWL, fun t ht _ hlt ↦ hWF.trans (hcond hg hvr t ht ?_)⟩
    rw [hvr] at hlt
    exact hlt

/-- **At grade `1` the designated tops concerned are at least the grade**: a donor value above `⊥`
at a cell of grade `1` is self-visible at `1`. -/
theorem topsAtLeastGrade_one {m : ℕ} {tb : StageType.{u} α m} {Lo Tops : Finset (Fin tb.card)} :
    TopsAtLeastGrade 1 (LawfulAt tb 1) Lo Tops := by
  intro g hg _ t _ ht0
  have hg1 : tb.toCellScheme.grade t ≤ 1 := by
    by_contra hgt
    rw [hg.2 t hgt] at ht0
    exact lt_irrefl _ ht0
  have hgt1 : tb.toCellScheme.grade t = 1 :=
    le_antisymm hg1 (tb.isWellFormed.isWellFormed.grade_pos t)
  have := (Rows.isLawfulBelow_iff_forall.mp hg.1).1 t ⟨subset_univ _, hg1⟩
  rw [hgt1] at this
  exact natCast_le_of_isSelfVisible this ht0

/-- **Designated tops of grade `K` are at least the grade** when above `⊥`. -/
theorem topsAtLeastGrade_of_grade {m K : ℕ} {tb : StageType.{u} α m}
    {Lo Tops : Finset (Fin tb.card)} (hT : ∀ t ∈ Tops, tb.toCellScheme.grade t = K) :
    TopsAtLeastGrade K (LawfulAt tb K) Lo Tops := by
  intro g hg _ t ht ht0
  have := (Rows.isLawfulBelow_iff_forall.mp hg.1).1 t ⟨subset_univ _, (hT t ht).le⟩
  rw [hT t ht] at this
  exact natCast_le_of_isSelfVisible this ht0

/-- **The designated tops concerned at the bottom are at least the grade at every legal context of
arity `k + 1`** (a named condition, in the binders of `H2.OwnerLoweringBelowAt`). -/
def TopsAtLeastGradeAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)), t'.IsLegal →
    ∀ (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r → K ≤ k →
    ∀ {p : StageType.{u} α k} (_ : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)}, tb.IsLegal →
      ∀ (_ : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x, tb.label x ≠ ⊤ → x ∈ Lo) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops) →
      TopsAtLeastGrade K (LawfulAt tb K) (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops

/-- **`H2.OwnerLoweringBelowAt k` from `H2.TopsAtLeastGradeAt k`**, at every arity (no condition on
the root of the donor faces: `H2.RootBelowTops` is not used). -/
theorem ownerLoweringBelowAt_of_topsAtLeastGradeAt {k : ℕ} (hcond : TopsAtLeastGradeAt.{u} k) :
    OwnerLoweringBelowAt.{u} k := by
  intro α K n t' hleg g o r hs hKk p hp tb htbleg htbp Lo Tops hLo hTops
  exact ownerLoweringBelow_of_topsAtLeastGrade hleg hs hKk hp htbleg htbp hLo
    (hcond t' hleg g hs hKk hp htbleg htbp hLo hTops)

/-- **`H2.OwnerLoweringBelowAt 1`**, with no condition (two points, `K = 1`). -/
theorem ownerLoweringBelowAt_one : OwnerLoweringBelowAt.{u} 1 :=
  ownerLoweringBelowAt_of_topsAtLeastGradeAt fun _ K _ t' _ _ _ _ hs hKk _ _ _ _ _ _ _ _ _ ↦ by
    obtain rfl : K = 1 :=
      le_antisymm hKk (hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos _)
    exact topsAtLeastGrade_one

end VaughtConjecture.H2

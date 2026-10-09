/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStepAbove

/-!
# A donor top pinned by a reader above the grade

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the layers of states
above the controllers); semantic contract, items 3, 4 and 8.

Above the grade `K` of the controllers the LOW step for states (`ProfileTower.StateCatStep`) is
compiled for the states below the cap at the cells of grade in `(K, j]`
(`ProfileTower.stateCatStep_low_seed_of_lt_cap`).  This file isolates what stops it in general: a
cell above `K` whose row reads a donor top at most the replacement at `K` of a proper cell.

**The pinning of a cell by a reader** (`CellScheme.Rows.le_visibilityReplace_of_row_le`, compiled
in this repository).  Let the row of a cell `s` transform to `d ↦ min (w d) (w s)`, `k` at most
the grade of `s`, and let the row of `s` read a cell `d` at most the replacement at `k` of its
reading of a cell `y`.  If `w s` is above the replacement at `k` of `w y`, then `w d` is at most
that replacement.  The witness `(g, σ)` of the locality at `s` has `g` at least `w s` at every
grade up to that of `s`, so `σ` reads `y` exactly (`σ (row y) = w y`) and commutes with the
replacement at `k` there; `σ (row d) ≤ σ (R_k (row y)) = R_k (w y) < w s` then caps the reading of
`d`.  For a top cell `s` (label `⊤`) the row separates the tops strictly
(`StageType.visibilityReplace_rowAt_lt_of_top`), so no top is pinned; a proper reader may read a
top at the replacement of a proper cell (a tie in its row), and then it pins it.

**Every reader at a graded index pins the top** (`ProfileTower.le_visibilityReplace_of_pin`,
compiled in this repository).  If every cell of the graded index of `s` pins `d` to `y` at the
level `k`, and a cell `u` of that grade with scope inside that of `s` carries a label above
`R_k (w y)`, availability gives a reader at that index above `R_k (w y)`, so `w d ≤ R_k (w y)` in
every profile lawful below the donor coatom.

**The level of a pin below a cap self-visible at `j`** (`ProfileTower.pin_level_eq`,
`Label.visibilityReplace_lt_of_isSelfVisible`, compiled in this repository).  With a cap `h`
self-visible at `j`, `w y < h < w u` and `h ≤ w d`, the level is `k = j` and the reader has grade
exactly `j`: below `j` the replacement of `w y < h` stays below `h`.  So a donor top read at least
at the cap can be pinned only by a reader of grade exactly `j`, at the tie `h = R_j (w y)` (the
finite part of `h` is then exactly `j`).  The ties at the grade `K` of the controllers do not
recur above it at caps self-visible at `j > K`.

**The step for states fails at a pinned configuration**
(`ProfileTower.not_stateCatStep_of_pin`, `ProfileTower.not_stateCatStep_of_pin'`, compiled in this
repository).  Let `P` be a state active below the cap `h` (its donor maximum below `h` and below
its cutoff), let a prescription `a` from the coatom `univ.erase x` fix the owner, the lost top and
a cell `u` with `a u > h`, with frontier of `a` above `h`, and let a designated donor top `d` be
pinned to a proper donor field `y` by every reader at the graded index of a cell `s` (scope
containing that of `u`, grade that of `u`) below the donor coatom.  Then no profile `W` and cutoff
`β` satisfy the conclusion of the step: the LOW clause of `withCut W β` needs `W d` at least the
frontier of `a`, while the pinning gives `W d ≤ R_k (W y) ≤ h`.  No template, of the type or of the
layers above (such as the controller of the state), can help the step: the pinning holds in every
profile lawful below the donor coatom on the rows of the amalgam, whatever its origin, and the
controllers are not cells of the amalgam.

**Not claimed.**  No legal seed realizing a pinned configuration is constructed here; by
`ProfileTower.pin_level_eq` it needs a reader of grade exactly `j` whose row reads the donor top at
the replacement at `j` of a proper donor field, a root cell `u` of grade `j` inside it prescribed
above the cap, and a cap with finite part exactly `j`.  The type's own labels are consistent with
it (a pinned reader of a top has `label s ≤ R_j (label y)`).  The step for states is a sufficient
condition for the lift of a layer of states; whether the lift itself fails at a pinned
configuration is not decided here (the lift may label the layer cells otherwise than by the
sections of states, though its amalgam part is pinned as well).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

/-- **Replacement at a lower threshold stays below a label self-visible higher**: if `c` is
self-visible at `j`, `k < j` and `y < c`, then the replacement of `y` at `k` is below `c` (it is
`y` or has finite part `k < j`, while `c` has finite part at least `j`). -/
theorem visibilityReplace_lt_of_isSelfVisible {j k : ℕ} (hk : k < j) {c y : Label.{u}}
    (hc : IsSelfVisible j c) (h : y < c) : visibilityReplace k k y < c := by
  refine (visibilityReplace_le_of_le le_rfl (hc.mono hk.le) h.le).lt_of_ne fun he ↦ ?_
  by_cases hy : IsSelfVisible k y
  · exact h.ne ((hy.visibilityReplace_eq k).symm.trans he)
  have hb : y ≠ ⊥ := fun h' ↦ hy (h' ▸ isSelfVisible_bot k)
  have ht : y ≠ ⊤ := fun h' ↦ hy (h' ▸ isSelfVisible_top k)
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn : n < k := by
    by_contra hn
    exact hy (isSelfVisible_block.mpr (by omega))
  rw [← he, visibilityReplace_block, ite_eq_left hn, isSelfVisible_block] at hc
  omega

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}

/-- **The pinning of a cell by a reader.**  If the row of `s` transforms to
`d ↦ min (w d) (w s)`, `K ≤ grade s`, the row of `s` reads `d` at most the replacement at `K` of
its reading of `y`, and `w s` is above the replacement at `K` of `w y`, then `w d` is at most that
replacement. -/
theorem le_visibilityReplace_of_row_le {w : ι → Label.{u}} {s : ι}
    (hloc : TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
      (fun d ↦ min (w d) (w s)))
    {K : ℕ} (hK : K ≤ D.grade s) {d y : D.below (D.gradedIndex s)}
    (hrow : R.row s d ≤ visibilityReplace K K (R.row s y))
    (hlt : visibilityReplace K K (w y) < w s) : w d ≤ visibilityReplace K K (w y) := by
  obtain ⟨g, σ, hσ, heq⟩ := hloc
  have hss := heq ⟨s, D.mem_below_gradedIndex s⟩
  change min (w s) (w s) = min (σ (R.row s ⟨s, _⟩)) (g (D.grade s)) at hss
  rw [min_self] at hss
  have hgs : w s ≤ g (D.grade s) := hss ▸ min_le_right _ _
  have hwy : w y < w s := (le_visibilityReplace (by omega) _).trans_lt hlt
  have hgy : w s ≤ g (D.grade y.1) := hgs.trans (hσ.antitone y.2.2)
  -- `σ` reads `y` exactly
  have hσy : σ (R.row s y) = w y := by
    have h1 := heq y
    change min (w y) (w s) = min (σ (R.row s y)) (g (D.grade y.1)) at h1
    rw [min_eq_left hwy.le] at h1
    rcases min_choice (σ (R.row s y)) (g (D.grade y.1)) with h2 | h2
    · rw [h2] at h1; exact h1.symm
    · rw [h2] at h1; exact absurd (h1 ▸ hgy) (not_le.mpr hwy)
  have hgK : σ (R.row s y) ≤ g K := by
    rw [hσy]; exact hwy.le.trans (hgs.trans (hσ.antitone hK))
  have hcomm : σ (visibilityReplace K K (R.row s y)) = visibilityReplace K K (w y) := by
    rw [hσ.visibilityReplace_comm _ K hgK K le_rfl, hσy]
  have hd := heq d
  change min (w d) (w s) = min (σ (R.row s d)) (g (D.grade d.1)) at hd
  have h3 : min (w d) (w s) ≤ visibilityReplace K K (w y) :=
    hd ▸ (min_le_left _ _).trans ((hσ.monotone hrow).trans_eq hcomm)
  rcases min_choice (w d) (w s) with h4 | h4
  · rwa [h4] at h3
  · rw [h4] at h3; exact absurd h3 (not_le.mpr hlt)

end VaughtConjecture.CellScheme.Rows

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **Every reader at a graded index pins the top.**  Let `W` be lawful below `(coatD, j)`, `s` a
cell below it with `K ≤ grade s`, `d`, `y` cells below `s`, and let every cell `v` of the graded
index of `s` read `d` at most the replacement at `K` of its reading of `y`.  If a cell `u` with
scope inside that of `s` and the grade of `s` has `R_K (W y) < W u`, then
`W d ≤ R_K (W y)` (availability, then `CellScheme.Rows.le_visibilityReplace_of_row_le`). -/
theorem le_visibilityReplace_of_pin {j k : ℕ} {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow (coatD, j) fun e ↦ W e) {s d y u : Fin I.amalgam.card}
    (hs : s ∈ I.amalgam.toCellScheme.below (coatD, j)) (hk : k ≤ I.amalgam.toCellScheme.grade s)
    (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hy : y ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hpin : ∀ v (hv : I.amalgam.toCellScheme.gradedIndex v = I.amalgam.toCellScheme.gradedIndex s),
      I.amalgam.rows.row v ⟨d, hv ▸ hd⟩ ≤ visibilityReplace k k (I.amalgam.rows.row v ⟨y, hv ▸ hy⟩))
    (hus : I.amalgam.toCellScheme.scope u ⊆ I.amalgam.toCellScheme.scope s)
    (hug : I.amalgam.toCellScheme.grade u = I.amalgam.toCellScheme.grade s)
    (hu : visibilityReplace k k (W y) < W u) : W d ≤ visibilityReplace k k (W y) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  obtain ⟨v, hv, hle⟩ := ha u s hs hus hug
  have hvs : v ∈ I.amalgam.toCellScheme.below (coatD, j) := by
    rw [CellScheme.mem_below, hv]; exact hs
  have hgv : I.amalgam.toCellScheme.grade v = I.amalgam.toCellScheme.grade s := congrArg Prod.snd hv
  exact Rows.le_visibilityReplace_of_row_le (hl v hvs) (hgv ▸ hk) (d := ⟨d, hv ▸ hd⟩)
    (y := ⟨y, hv ▸ hy⟩) (hpin v hv) (hu.trans_le hle)

/-- **A pin below a cap self-visible at `j` is at the grade `j`.**  In the pinned configuration
of `ProfileTower.le_visibilityReplace_of_pin` at the level `k` (so `k ≤ grade s ≤ j`), with a cap
`h` self-visible at `j`, `W y < h < W u` and `h ≤ W d`, the level is `j`: below `j` the
replacement at `k` of `W y < h` stays below `h`
(`Label.visibilityReplace_lt_of_isSelfVisible`), so the pin would put `W d` below `h`.  So above the
grade of the controllers a pinned donor top below a cap self-visible at `j` is pinned by a reader
of grade exactly `j`, at the replacement at `j`. -/
theorem pin_level_eq {j k : ℕ} {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow (coatD, j) fun e ↦ W e) {s d y u : Fin I.amalgam.card}
    (hs : s ∈ I.amalgam.toCellScheme.below (coatD, j)) (hk : k ≤ I.amalgam.toCellScheme.grade s)
    (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hy : y ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hpin : ∀ v (hv : I.amalgam.toCellScheme.gradedIndex v = I.amalgam.toCellScheme.gradedIndex s),
      I.amalgam.rows.row v ⟨d, hv ▸ hd⟩ ≤ visibilityReplace k k (I.amalgam.rows.row v ⟨y, hv ▸ hy⟩))
    (hus : I.amalgam.toCellScheme.scope u ⊆ I.amalgam.toCellScheme.scope s)
    (hug : I.amalgam.toCellScheme.grade u = I.amalgam.toCellScheme.grade s)
    {h : Label.{u}} (hh : IsSelfVisible j h) (hWy : W y < h) (hWu : h < W u) (hWd : h ≤ W d) :
    k = j ∧ I.amalgam.toCellScheme.grade s = j := by
  have hsj : I.amalgam.toCellScheme.grade s ≤ j := hs.2
  have hRy : visibilityReplace k k (W y) ≤ h :=
    visibilityReplace_le_of_le le_rfl (hh.mono (hk.trans hsj)) hWy.le
  have hpinW := le_visibilityReplace_of_pin hW hs hk hd hy hpin hus hug (hRy.trans_lt hWu)
  by_contra hne
  have hkj : k < j := by omega
  exact absurd (hWd.trans hpinW) (not_le.mpr (visibilityReplace_lt_of_isSelfVisible hkj hh hWy))

variable {K j : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The step for states fails at a pinned configuration.**  Let `P` be a state with donor
maximum below the cap `h` and below its cutoff, `h` self-visible at `K`, and `a` a prescription
from the coatom `univ.erase x` (any labelling), whose frontier is above `h`, with
the owner `o`, the lost top `r` and a cell `u` with `h < a u` below the coatom.  Let `d` be a
designated donor top and `y` a proper donor field, pinned at the graded index of a cell `s` below
the donor coatom of the grade of `u`, with scope containing that of `u` and grade at least `K`.
Then the conclusion of the step for states fails at `P`, `h`, `a`: no profile lawful on the cut,
equal to `a` below the coatom and agreeing with `P` capped at `h`, carries a cutoff agreeing with
that of `P` capped at `h` making it LOW. -/
theorem not_stateCatStep_of_pin (hN : Sum.inr () ∉ N) {x : Fin (m + 2)} {P : CProf I}
    {h : Label.{u}} {k : ℕ} (hhk : IsSelfVisible k h) (hMh : donorMax N P < h)
    (hact : donorMax N P < P (Sum.inr ())) {a : Prof I}
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hfr : h < frontier K (Sum.inl o) (Sum.inl r) (withCut a ⊥))
    {s d y u : Fin I.amalgam.card} (hdT : Sum.inl d ∈ T) (hyN : Sum.inl y ∈ N)
    (hs : s ∈ I.amalgam.toCellScheme.below (coatD, j)) (hk : k ≤ I.amalgam.toCellScheme.grade s)
    (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hy : y ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hpin : ∀ v (hv : I.amalgam.toCellScheme.gradedIndex v = I.amalgam.toCellScheme.gradedIndex s),
      I.amalgam.rows.row v ⟨d, hv ▸ hd⟩ ≤ visibilityReplace k k (I.amalgam.rows.row v ⟨y, hv ▸ hy⟩))
    (hus : I.amalgam.toCellScheme.scope u ⊆ I.amalgam.toCellScheme.scope s)
    (hug : I.amalgam.toCellScheme.grade u = I.amalgam.toCellScheme.grade s)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, j)) (hau : h < a u) :
    ¬ ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I j W ∧
      (∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W e = a e) ∧
      (∀ e, min (W e) h = min (P (Sum.inl e)) h) ∧
      min β h = min (P (Sum.inr ())) h ∧ lowPred K N T o r (withCut W β) := by
  rintro ⟨W, β, hW, hWa, hWP, hβ, hlow⟩
  -- the proper donor fields of `W` are those of `P`, below the cap
  have hNW : ∀ f ∈ N, withCut W β f = P f := by
    rintro (e | z) hf
    · exact eq_of_min_eq_of_lt (hWP e).symm ((le_donorMax hf).trans_lt hMh)
    · cases z; exact absurd hf hN
  have hMW : donorMax N (withCut W β) = donorMax N P := donorMax_congr hNW
  -- the state of `W` is active
  have hβ' : donorMax N P < β := by
    rcases le_total (P (Sum.inr ())) h with hle | hle
    · rw [min_eq_left hle] at hβ
      exact hact.trans_le (hβ ▸ min_le_left _ _)
    · rw [min_eq_right hle] at hβ
      exact hMh.trans_le (min_eq_right_iff.mp hβ)
  have hlowd := (le_max_right _ _).trans (hlow (by rw [hMW]; exact hβ') _ hdT)
  -- the frontier of `W` is that of `a`
  have hfW : frontier K (Sum.inl o) (Sum.inl r) (withCut W β) =
      frontier K (Sum.inl o) (Sum.inl r) (withCut a ⊥) := by
    unfold Label.frontier
    change min (W o) (visibilityReplace K K (W r)) = min (a o) (visibilityReplace K K (a r))
    rw [hWa o ho, hWa r hr]
  rw [hfW] at hlowd
  -- the pinning
  have hWy : W y < h := by
    have := hNW _ hyN
    change W y = P (Sum.inl y) at this
    rw [this]; exact (le_donorMax hyN).trans_lt hMh
  have hRy : visibilityReplace k k (W y) ≤ h := visibilityReplace_le_of_le le_rfl hhk hWy.le
  have hWu : visibilityReplace k k (W y) < W u := by rw [hWa u hux]; exact hRy.trans_lt hau
  have hpinW := le_visibilityReplace_of_pin hW.2 hs hk hd hy hpin hus hug hWu
  have : frontier K (Sum.inl o) (Sum.inl r) (withCut a ⊥) ≤ h :=
    hlowd.trans (hpinW.trans hRy)
  exact absurd hfr (not_lt.mpr this)

/-- **The step for states fails at a pinned configuration**, as a statement on
`ProfileTower.StateCatStep`: at a state `P` of the catalogue (code grid, amalgam part lawful on the
cut, LOW) active below a cap `h` self-visible and short at `j`, and a prescription `a` lawful below
the coatom and agreeing there with `P` capped at `h`, with the pinned configuration of
`ProfileTower.not_stateCatStep_of_pin`, the step for states at `j` from the coatom fails. -/
theorem not_stateCatStep_of_pin' {k : ℕ} (hN : Sum.inr () ∉ N) {x : Fin (m + 2)}
    {P : CProf I} (hPB : ∀ f, P f ∈ codeGrid j (bound I)) (hPC : IsCutLawful I j (camal P))
    (hPlow : lowPred K N T o r P) {h : Label.{u}} (hh : IsSelfVisible j h) (hsh : IsShort j h)
    (hMh : donorMax N P < h) (hact : donorMax N P < P (Sum.inr ())) {a : Prof I}
    (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
      min (a e) h = min (P (Sum.inl e)) h)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hfr : h < frontier K (Sum.inl o) (Sum.inl r) (withCut a ⊥))
    {s d y u : Fin I.amalgam.card} (hdT : Sum.inl d ∈ T) (hyN : Sum.inl y ∈ N)
    (hs : s ∈ I.amalgam.toCellScheme.below (coatD, j)) (hk : k ≤ I.amalgam.toCellScheme.grade s)
    (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hy : y ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
    (hpin : ∀ v (hv : I.amalgam.toCellScheme.gradedIndex v = I.amalgam.toCellScheme.gradedIndex s),
      I.amalgam.rows.row v ⟨d, hv ▸ hd⟩ ≤ visibilityReplace k k (I.amalgam.rows.row v ⟨y, hv ▸ hy⟩))
    (hus : I.amalgam.toCellScheme.scope u ⊆ I.amalgam.toCellScheme.scope s)
    (hug : I.amalgam.toCellScheme.grade u = I.amalgam.toCellScheme.grade s)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, j)) (hau : h < a u) :
    ¬ StateCatStep I j (lowPred K N T o r) x := by
  intro hstep
  have hb : ⊥ < h := lt_of_le_of_lt bot_le hMh
  obtain ⟨W, β, hW, hWa, hWP, -, hβ, hlow⟩ := hstep P hPB hPC hPlow h hh hsh hb a ha haP
  exact not_stateCatStep_of_pin hN (hh.mono (hk.trans hs.2)) hMh hact ho hr hfr hdT hyN hs hk hd hy
    hpin hus
    hug hux hau ⟨W, β, hW, hWa, hWP, hβ, hlow⟩

end VaughtConjecture.ProfileTower

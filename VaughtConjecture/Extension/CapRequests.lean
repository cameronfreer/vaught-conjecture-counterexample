/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Basic

/-!
# Cap requests: correctness of a state capped at a cap

Roadmap, Layer 3 (3.3: the private cap, the marker and the references of (R3) and (R4)).

A *state* is a labelling `s : ι → Label` of a family of cells `ι` (in the application, the cells
of the amalgam of a context and a donor).  **Cap requests** (`CapRequests ι`) fix:

* a cell `cap` (the private cap) and a threshold `N` (its grade in the application);
* a marker offset `R < N` and a cell `marker` (the marker);
* three sets of cells `Z`, `F` and `T` (the cells of the donor labelled `⊥`, proper, and `⊤`);
* for every cell `f` a reference cell `ref f` and an offset `off f`.

Write `c = s cap` and `vR N i` for visibility replacement at threshold `N` with value `i`.  The
**reference value** of `f` is `min (vR N (off f) (s (ref f))) c` (`CapRequests.refValue`) and the
**marker value** is `min (vR N R (s marker)) c` (`CapRequests.markerValue`).  The state is
**correct** (`CapRequests.IsCorrect`) when, everything capped at `c`,

* `min (s z) c = ⊥` for `z ∈ Z`;
* `min (s f) c` is the reference value of `f`, for `f ∈ F`;
* the marker value is at most `min (s y) c`, for `y ∈ T`.

**The marker convention.**  The marker is a datum of the requests, and where it sits decides what
correctness asks on `T`, hence what a construction of correct states must deliver.

* **The marker a separate cell below the cap** (the intended convention).  In (R4) it is a cell
  labelled `λ + i` with `i < N` (`λ` zero or a limit), so the marker value is `λ + R` under a cap
  at least `λ + R`, and correctness asks `λ + R ≤ s y` on `T`, strictly less than the capped
  reading when `λ + R` is below the cap.  In (R3) it is a cell labelled `⊤` (the marker of the top
  cap, a cell below it at which the row of the cap is least among the cells labelled `⊤`).
* **The marker at the cap** (the degenerate convention).  If the value of the cap is self-visible
  at `N`, the marker value is the value of the cap (`CapRequests.markerValue_of_marker_eq_cap`),
  and correctness on `T` is the **capped reading** `s cap ≤ s y`
  (`CapRequests.isCorrect_iff_of_marker_eq_cap`).  It asks the most: a state correct with the
  marker at the cap is correct for every marker (`CapRequests.IsCorrect.of_marker_eq_cap`), and a
  state reading a cell of `T` below its own cap is not correct with the marker at the cap.

## The algebra of correctness

Each item below is compiled in this file (theorem named).

* **The bottom cases** (`CapRequests.isCorrect_of_cap_eq_bot`, `CapRequests.isCorrect_bot`): a
  state whose cap is `⊥` is correct, the constant `⊥` state in particular.
* **Capping** (`CapRequests.IsCorrect.cap`): for `h` self-visible at `N` and offsets at most `N`
  on `F`, capping a correct state at `h` keeps it correct.
* **Transformations** (`CapRequests.IsCorrect.map`, `CapRequests.IsCorrect.of_transformsTo`): for
  a witness `(g, σ)` (`Label.IsWitness`), the state `d ↦ min (σ (s d)) (g (grade d))` of a correct
  state `s` is correct, provided the requests are graded (`CapRequests.IsGraded`): `N` is at most
  the grade of the cap, the offsets on `F` are at most `N`, and the cells of `Z`, `F` and `T`, the
  references of `F` and the marker have grade at most that of the cap.  Where the shifter at a
  reference value does not commute with visibility replacement at `N`, it exceeds the suppressor
  at `N`, and both sides are the capped cap; elsewhere it commutes.  No bottom reflection and no
  orderliness of the state is needed.
* **The actual state** (`CapRequests.isCorrect_of_forall`, `CapRequests.isCorrect_actual`): a
  state that is `⊥` on `Z`, at least the marker value on `T`, and reads every `f ∈ F` in the block
  of its reference, `s (ref f) = μ + k` with `k < N` and `s f = μ + off f` (`μ` zero or a limit),
  is correct; for a stage type, its own labels.  With cap and marker `⊤`, correctness is exactly
  `⊥` on `Z`, `⊤` on `T` and `s f = vR N (off f) (s (ref f))` on `F`
  (`CapRequests.isCorrect_iff_of_eq_top`), so two correct states with cap and marker `⊤` that agree
  at the references agree on `Z`, `F` and `T` (`CapRequests.IsCorrect.eq_of_eq_top`).

## The readings

* **(R3), cap and marker `⊤`** (`CapRequests.IsCorrect.eq_top_of_mem_T`): every cell of `T` is
  `⊤`; every cell of `Z` is `⊥` as soon as the cap is not `⊥`
  (`CapRequests.IsCorrect.eq_bot_of_mem_Z`).
* **(R4), a proper cap** (`CapRequests.IsCorrect.label_eq`, `CapRequests.IsCorrect.le_label`,
  `CapRequests.IsCorrect.lt_label`): if the reference of `f ∈ F` is `μ + k` with `k < N` and
  `μ + off f` is below the cap, then `s f = μ + off f`; if the marker is `λ + i` with `λ` zero or
  a limit, `i < N` and `λ + R` at most the cap, then every `y ∈ T` has `λ + R ≤ s y`, so
  `γ < s y` for every `γ < λ + R`.  At a cap at least `λ + N`, the first applies to every block
  `μ ≤ λ` and offset below `N` (`CapRequests.IsCorrect.label_eq_of_le`).

## The bottom class and admission

A state is **in the bottom class** `ZA` on a set of cells `B` (`InBottomClass B ZA s`) when its
`⊥` cells in `B` are exactly those of `ZA`.  A state is **admitted** by the requests
(`CapRequests.Admits`) when it is correct as soon as it is in the class.  Admission holds at the
constant `⊥` state (`CapRequests.admits_bot`), is kept by capping
(`CapRequests.Admits.cap`), and by the state of a transformation whose shifter reflects `⊥` and
whose suppressor is not `⊥` at the grades of `B` (`CapRequests.Admits.map`, through
`inBottomClass_map_iff`).  Without bottom reflection the class of the transformed state says
nothing about the class of the source, so admission is not kept by every transformation: a
transformation may send to `⊥` a positive value at a cell of `ZA`.

## References

Visibility replacement and witnesses are [Kni26, Definitions 2.2.3 and 2.3.9].  The correctness
relation is a capped variant of the correctness of [Kni26, Definition 8.3.1]: references are read
in their block, the marker at the offset `R`, and everything under the cap.
-/

universe u

namespace VaughtConjecture

open Label

/-- **Cap requests** on a family of cells `ι`: the cap and its threshold `N`, the marker offset
`R < N`, the cells `Z`, `F`, `T` to be read as `⊥`, exactly, and from below, the reference cell and
the offset of each cell, and the marker. -/
structure CapRequests (ι : Type*) where
  /-- The cap. -/
  cap : ι
  /-- The threshold of the cap. -/
  N : ℕ
  /-- The marker offset. -/
  R : ℕ
  /-- The marker offset is below the threshold. -/
  R_lt_N : R < N
  /-- The cells read as `⊥` under the cap. -/
  Z : Set ι
  /-- The cells read exactly under the cap, through their references. -/
  F : Set ι
  /-- The cells read from below under the cap, through the marker. -/
  T : Set ι
  /-- The reference cell of a cell. -/
  ref : ι → ι
  /-- The offset of a cell. -/
  off : ι → ℕ
  /-- The marker. -/
  marker : ι

namespace CapRequests

variable {ι : Type*} (r : CapRequests ι) {s s' : ι → Label.{u}}

/-- The **reference value** of a cell `f` in a state `s`: the visibility replacement at `N` with
the offset of `f` of the value at the reference cell, capped at the cap. -/
noncomputable def refValue (s : ι → Label.{u}) (f : ι) : Label.{u} :=
  min (visibilityReplace r.N (r.off f) (s (r.ref f))) (s r.cap)

/-- The **marker value** of a state `s`: the visibility replacement at `N` with value `R` of the
value at the marker, capped at the cap. -/
noncomputable def markerValue (s : ι → Label.{u}) : Label.{u} :=
  min (visibilityReplace r.N r.R (s r.marker)) (s r.cap)

/-- A state is **correct** for the requests: capped at the cap, it is `⊥` on `Z`, the reference
value on `F`, and at least the marker value on `T`. -/
structure IsCorrect (s : ι → Label.{u}) : Prop where
  /-- The cells of `Z` are `⊥` under the cap. -/
  eq_bot : ∀ z ∈ r.Z, min (s z) (s r.cap) = ⊥
  /-- The cells of `F` are their reference values under the cap. -/
  eq_refValue : ∀ f ∈ r.F, min (s f) (s r.cap) = r.refValue s f
  /-- The cells of `T` are at least the marker value under the cap. -/
  markerValue_le : ∀ y ∈ r.T, r.markerValue s ≤ min (s y) (s r.cap)

/-- The requests are **graded** by `grade`: the threshold is at most the grade of the cap, the
offsets of `F` are at most the threshold, and the requested cells, the references of `F` and the
marker have grade at most that of the cap. -/
structure IsGraded (grade : ι → ℕ) : Prop where
  /-- The threshold is at most the grade of the cap. -/
  le_grade_cap : r.N ≤ grade r.cap
  /-- The offsets of `F` are at most the threshold. -/
  off_le : ∀ f ∈ r.F, r.off f ≤ r.N
  /-- The cells of `Z` lie at most at the grade of the cap. -/
  grade_le_of_mem_Z : ∀ z ∈ r.Z, grade z ≤ grade r.cap
  /-- The cells of `F` lie at most at the grade of the cap. -/
  grade_le_of_mem_F : ∀ f ∈ r.F, grade f ≤ grade r.cap
  /-- The cells of `T` lie at most at the grade of the cap. -/
  grade_le_of_mem_T : ∀ y ∈ r.T, grade y ≤ grade r.cap
  /-- The references of `F` lie at most at the grade of the cap. -/
  grade_ref_le : ∀ f ∈ r.F, grade (r.ref f) ≤ grade r.cap
  /-- The marker lies at most at the grade of the cap. -/
  grade_marker_le : grade r.marker ≤ grade r.cap

variable {r}

/-! ### The bottom cases -/

/-- A state whose cap is `⊥` is correct. -/
theorem isCorrect_of_cap_eq_bot (h : s r.cap = ⊥) : r.IsCorrect s where
  eq_bot _ _ := by rw [h, min_bot_right]
  eq_refValue _ _ := by rw [refValue, h, min_bot_right, min_bot_right]
  markerValue_le _ _ := by rw [markerValue, h, min_bot_right]; exact bot_le

variable (r) in
/-- The constant `⊥` state is correct. -/
theorem isCorrect_bot : r.IsCorrect fun _ ↦ (⊥ : Label.{u}) :=
  isCorrect_of_cap_eq_bot rfl

/-! ### Capping -/

/-- Two labels capped at one cap: their minimum, capped. -/
private theorem min_min_cap (a b h : Label.{u}) : min (min a b) h = min (min a h) (min b h) :=
  inf_inf_distrib_right a b h

/-- **Capping keeps correctness**: for offsets of `F` at most `N` and a label `h` self-visible at
`N`, the state `s` capped at `h` is correct when `s` is. -/
theorem IsCorrect.cap (hs : r.IsCorrect s) (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) {h : Label.{u}}
    (hh : IsSelfVisible r.N h) : r.IsCorrect fun d ↦ min (s d) h where
  eq_bot z hz := by
    rw [← min_min_cap, hs.eq_bot z hz, min_eq_left bot_le]
  eq_refValue f hf := by
    rw [← min_min_cap, hs.eq_refValue f hf]
    dsimp only [refValue]
    rw [visibilityReplace_min_of_isSelfVisible (hoff f hf) hh, min_min_cap]
  markerValue_le y hy := by
    dsimp only [markerValue]
    rw [← min_min_cap, visibilityReplace_min_of_isSelfVisible r.R_lt_N.le hh,
      ← min_min_cap]
    exact min_le_min_right _ (hs.markerValue_le y hy)

/-! ### Transformations -/

section Map

variable {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

/-- Two caps, the second below the second argument of the first: the first argument and the
second cap. -/
private theorem min_min_min_of_le {a b c e : Label.{u}} (h : e ≤ b) :
    min (min a b) (min c e) = min a (min c e) := by
  rw [min_assoc, min_eq_right ((min_le_right c e).trans h)]

/-- **A shifter under a cap at the threshold**: for a witness `(g, σ)`, `N ≤ K`, `i ≤ N` and
`e ≥ g K`, replacing at `N` with value `i` the shifted value `σ x` capped at `e`, or shifting the
replaced value, gives the same label under the cap `min c (g K)`. -/
private theorem IsWitness.min_visibilityReplace (hw : IsWitness g σ) {N K i : ℕ} (hNK : N ≤ K)
    (hi : i ≤ N) (x c : Label.{u}) {e : Label.{u}} (he : g K ≤ e) :
    min (visibilityReplace N i (min (σ x) e)) (min c (g K)) =
      min (σ (visibilityReplace N i x)) (min c (g K)) := by
  have hgK : IsSelfVisible N (g K) := (hw.isSelfVisible K).mono hNK
  have hgN : IsSelfVisible N (g N) := hw.isSelfVisible N
  -- the replaced cap `e` stays above `g K`
  have hve : g K ≤ visibilityReplace N i e :=
    (hgK.visibilityReplace_eq i).symm.le.trans (monotone_visibilityReplace hi he)
  rw [visibilityReplace_min hi, min_min_min_of_le hve]
  rcases le_or_gt (σ x) (g N) with h₁ | h₁
  · rw [hw.visibilityReplace_comm x N h₁ i hi]
  · -- the shifter exceeds the suppressor at `N`, before and after replacement
    have hKN : g K ≤ g N := hw.antitone hNK
    have h₂ : g K ≤ σ (visibilityReplace N i x) :=
      hKN.trans (hw.lt_apply_visibilityReplace h₁ hi).le
    have h₃ : g K ≤ visibilityReplace N i (σ x) :=
      hKN.trans ((hgN.visibilityReplace_eq i).symm.le.trans
        (monotone_visibilityReplace hi h₁.le))
    rw [min_eq_right ((min_le_right _ _).trans h₂), min_eq_right ((min_le_right _ _).trans h₃)]

/-- **Transformations keep correctness**: for graded requests and a witness `(g, σ)`, the state
`d ↦ min (σ (s d)) (g (grade d))` is correct when `s` is. -/
theorem IsCorrect.map (hs : r.IsCorrect s) {grade : ι → ℕ} (hgr : r.IsGraded grade)
    (hw : IsWitness g σ) : r.IsCorrect fun d ↦ min (σ (s d)) (g (grade d)) := by
  set K := grade r.cap
  have hmono := hw.monotone
  -- a requested cell under the transformed cap
  have hcell {d : ι} (hd : grade d ≤ K) :
      min (min (σ (s d)) (g (grade d))) (min (σ (s r.cap)) (g K)) =
        min (σ (min (s d) (s r.cap))) (g K) := by
    rw [min_min_min_of_le (hw.antitone hd), hmono.map_min, min_assoc]
  refine ⟨fun z hz ↦ ?_, fun f hf ↦ ?_, fun y hy ↦ ?_⟩
  · rw [hcell (hgr.grade_le_of_mem_Z z hz), hs.eq_bot z hz, hw.map_bot, min_eq_left bot_le]
  · rw [hcell (hgr.grade_le_of_mem_F f hf), hs.eq_refValue f hf]
    dsimp only [refValue]
    rw [hmono.map_min, min_assoc, IsWitness.min_visibilityReplace hw hgr.le_grade_cap
      (hgr.off_le f hf) _ _ (hw.antitone (hgr.grade_ref_le f hf))]
  · dsimp only [markerValue]
    rw [hcell (hgr.grade_le_of_mem_T y hy), IsWitness.min_visibilityReplace hw hgr.le_grade_cap
      r.R_lt_N.le _ _ (hw.antitone hgr.grade_marker_le), ← min_assoc,
      ← hmono.map_min]
    exact min_le_min_right _ (hmono (hs.markerValue_le y hy))

/-- **Transformations keep correctness**, in terms of `Label.TransformsTo`: if `s` transforms to
`s'` over the grades `grade` and the requests are graded by `grade`, then `s'` is correct when `s`
is. -/
theorem IsCorrect.of_transformsTo (hs : r.IsCorrect s) {grade : ι → ℕ} (hgr : r.IsGraded grade)
    (h : TransformsTo grade s s') : r.IsCorrect s' := by
  obtain ⟨g, σ, hw, heq⟩ := h
  obtain rfl : s' = fun d ↦ min (σ (s d)) (g (grade d)) := funext heq
  exact hs.map hgr hw

end Map

/-! ### The actual state -/

/-- **A state reading its references is correct**: a state `⊥` on `Z`, at least the marker value
on `T`, and reading every `f ∈ F` in the block of its reference (`s (ref f) = μ + k` with `k < N`
and `s f = μ + off f`, `μ` zero or a limit) is correct. -/
theorem isCorrect_of_forall (hZ : ∀ z ∈ r.Z, s z = ⊥)
    (hF : ∀ f ∈ r.F, ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ k < r.N,
      s (r.ref f) = ((μ + k : Ordinal.{u}) : Label.{u}) ∧
        s f = ((μ + r.off f : Ordinal.{u}) : Label.{u}))
    (hT : ∀ y ∈ r.T, r.markerValue s ≤ s y) : r.IsCorrect s where
  eq_bot z hz := by rw [hZ z hz, min_eq_left bot_le]
  eq_refValue f hf := by
    obtain ⟨μ, hμ, k, hk, hr, hf⟩ := hF f hf
    rw [refValue, hr, visibilityReplace_coe_add_natCast hμ hk, hf]
  markerValue_le y hy := le_min (hT y hy) (min_le_right _ _)

/-- **The actual state is correct**: the labels of a stage type `t`, when they are `⊥` on `Z`,
`⊤` on `T`, and read every `f ∈ F` in the block of its reference. -/
theorem isCorrect_actual {α : Ordinal.{u}} {n : ℕ} (t : StageType.{u} α n)
    {r : CapRequests (Fin t.card)} (hZ : ∀ z ∈ r.Z, t.label z = ⊥)
    (hF : ∀ f ∈ r.F, ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ k < r.N,
      t.label (r.ref f) = ((μ + k : Ordinal.{u}) : Label.{u}) ∧
        t.label f = ((μ + r.off f : Ordinal.{u}) : Label.{u}))
    (hT : ∀ y ∈ r.T, t.label y = ⊤) : r.IsCorrect t.label :=
  isCorrect_of_forall hZ hF fun y hy ↦ by rw [hT y hy]; exact le_top

/-- **Correctness at a cap and marker `⊤`**: the state is `⊥` on `Z`, `⊤` on `T`, and the
replacement at `N` with the offset of the reference on `F`. -/
theorem isCorrect_iff_of_eq_top (hc : s r.cap = ⊤) (ha : s r.marker = ⊤) :
    r.IsCorrect s ↔ (∀ z ∈ r.Z, s z = ⊥) ∧
      (∀ f ∈ r.F, s f = visibilityReplace r.N (r.off f) (s (r.ref f))) ∧ ∀ y ∈ r.T, s y = ⊤ := by
  have hm : r.markerValue s = ⊤ := by rw [markerValue, ha, hc, visibilityReplace_top, min_self]
  constructor
  · intro h
    refine ⟨fun z hz ↦ ?_, fun f hf ↦ ?_, fun y hy ↦ ?_⟩
    · simpa [hc] using h.eq_bot z hz
    · simpa [refValue, hc] using h.eq_refValue f hf
    · simpa [hm, hc] using h.markerValue_le y hy
  · rintro ⟨hZ, hF, hT⟩
    refine ⟨fun z hz ↦ ?_, fun f hf ↦ ?_, fun y hy ↦ ?_⟩
    · rw [hc, min_top_right, hZ z hz]
    · rw [refValue, hc, min_top_right, min_top_right, hF f hf]
    · rw [hm, hT y hy, hc, min_self]

/-- **Uniqueness at a cap and marker `⊤`**: two correct states with cap and marker `⊤` that agree
at the references of `F` agree on `Z`, `F` and `T`. -/
theorem IsCorrect.eq_of_eq_top (hs : r.IsCorrect s) (hs' : r.IsCorrect s')
    (hc : s r.cap = ⊤) (ha : s r.marker = ⊤) (hc' : s' r.cap = ⊤) (ha' : s' r.marker = ⊤)
    (href : ∀ f ∈ r.F, s (r.ref f) = s' (r.ref f)) {d : ι} (hd : d ∈ r.Z ∨ d ∈ r.F ∨ d ∈ r.T) :
    s d = s' d := by
  obtain ⟨hZ, hF, hT⟩ := (isCorrect_iff_of_eq_top hc ha).mp hs
  obtain ⟨hZ', hF', hT'⟩ := (isCorrect_iff_of_eq_top hc' ha').mp hs'
  rcases hd with hd | hd | hd
  · rw [hZ d hd, hZ' d hd]
  · rw [hF d hd, hF' d hd, href d hd]
  · rw [hT d hd, hT' d hd]

/-! ### The marker at the cap -/

/-- **The marker at the cap**: if the value of the cap is self-visible at `N`, the marker value is
the value of the cap. -/
theorem markerValue_of_marker_eq_cap (hm : r.marker = r.cap) (hc : IsSelfVisible r.N (s r.cap)) :
    r.markerValue s = s r.cap := by
  rw [markerValue, hm, hc.visibilityReplace_eq, min_self]

/-- **Correctness with the marker at the cap is the capped reading on `T`**: for a cap value
self-visible at `N`, a state is correct exactly when it is `⊥` on `Z` and the reference value on
`F` under the cap, and every cell of `T` is at least the cap. -/
theorem isCorrect_iff_of_marker_eq_cap (hm : r.marker = r.cap)
    (hc : IsSelfVisible r.N (s r.cap)) :
    r.IsCorrect s ↔ (∀ z ∈ r.Z, min (s z) (s r.cap) = ⊥) ∧
      (∀ f ∈ r.F, min (s f) (s r.cap) = r.refValue s f) ∧ ∀ y ∈ r.T, s r.cap ≤ s y := by
  have hT (y : ι) : r.markerValue s ≤ min (s y) (s r.cap) ↔ s r.cap ≤ s y := by
    rw [markerValue_of_marker_eq_cap hm hc]
    exact ⟨fun h ↦ h.trans (min_le_left _ _), fun h ↦ le_min h le_rfl⟩
  exact ⟨fun h ↦ ⟨h.eq_bot, h.eq_refValue, fun y hy ↦ (hT y).mp (h.markerValue_le y hy)⟩,
    fun ⟨hZ, hF, h⟩ ↦ ⟨hZ, hF, fun y hy ↦ (hT y).mpr (h y hy)⟩⟩

/-- **The marker at the cap asks the most**: for a cap value self-visible at `N`, a state correct
for the requests with the marker moved to the cap is correct for every marker. -/
theorem IsCorrect.of_marker_eq_cap (hs : ({ r with marker := r.cap } : CapRequests ι).IsCorrect s)
    (hc : IsSelfVisible r.N (s r.cap)) : r.IsCorrect s := by
  obtain ⟨hZ, hF, hT⟩ :=
    (isCorrect_iff_of_marker_eq_cap (r := { r with marker := r.cap }) rfl hc).mp hs
  exact ⟨hZ, hF, fun y hy ↦ le_min ((min_le_right _ _).trans (hT y hy)) (min_le_right _ _)⟩

/-! ### The readings -/

/-- A label whose minimum with a cap `c` is a label `v` below `c` is `v`. -/
private theorem eq_of_min_eq_of_lt {a c v : Label.{u}} (h : min a c = v) (hv : v < c) : a = v := by
  rcases le_total a c with hac | hac
  · rwa [min_eq_left hac] at h
  · rw [min_eq_right hac] at h
    exact absurd h hv.ne'

/-- **The cells of `Z` are `⊥`** under a cap that is not `⊥`. -/
theorem IsCorrect.eq_bot_of_mem_Z (hs : r.IsCorrect s) {z : ι} (hz : z ∈ r.Z)
    (hc : s r.cap ≠ ⊥) : s z = ⊥ :=
  (min_eq_bot.mp (hs.eq_bot z hz)).resolve_right hc

/-- **(R3): the cells of `T` are `⊤`** at a cap and marker `⊤`. -/
theorem IsCorrect.eq_top_of_mem_T (hs : r.IsCorrect s) {y : ι} (hy : y ∈ r.T)
    (hc : s r.cap = ⊤) (ha : s r.marker = ⊤) : s y = ⊤ :=
  ((isCorrect_iff_of_eq_top hc ha).mp hs).2.2 y hy

/-- **(R4): a cell of `F` is read in the block of its reference**: if the reference of `f ∈ F` is
`μ + k` (`μ` zero or a limit, `k < N`) and `μ + off f` is below the cap, then
`s f = μ + off f`. -/
theorem IsCorrect.label_eq (hs : r.IsCorrect s) {f : ι} (hf : f ∈ r.F) {μ : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {k : ℕ} (hk : k < r.N)
    (href : s (r.ref f) = ((μ + k : Ordinal.{u}) : Label.{u}))
    (hlt : ((μ + r.off f : Ordinal.{u}) : Label.{u}) < s r.cap) :
    s f = ((μ + r.off f : Ordinal.{u}) : Label.{u}) := by
  have h := hs.eq_refValue f hf
  rw [refValue, href, visibilityReplace_coe_add_natCast hμ hk, min_eq_left hlt.le] at h
  exact eq_of_min_eq_of_lt h hlt

/-- `μ + o < c` for `μ ≤ λ`, `o < N` and `λ + N ≤ c`. -/
theorem coe_add_lt_of_le {μ lam : Ordinal.{u}} {o N : ℕ} {c : Label.{u}} (hμ : μ ≤ lam)
    (ho : o < N) (hc : ((lam + N : Ordinal.{u}) : Label.{u}) ≤ c) :
    ((μ + o : Ordinal.{u}) : Label.{u}) < c := by
  refine lt_of_lt_of_le ?_ hc
  have : μ + (o : Ordinal.{u}) < lam + N :=
    (add_lt_add_right (by exact_mod_cast ho) μ).trans_le (add_le_add_left hμ _)
  exact_mod_cast this

/-- **(R4) at a cap at least `λ + N`**: every `f ∈ F` whose reference is `μ + k` with `μ ≤ λ`
(`μ` zero or a limit), `k < N` and offset below `N` has `s f = μ + off f`. -/
theorem IsCorrect.label_eq_of_le (hs : r.IsCorrect s) {f : ι} (hf : f ∈ r.F)
    {μ lam : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (hμl : μ ≤ lam) {k : ℕ} (hk : k < r.N)
    (href : s (r.ref f) = ((μ + k : Ordinal.{u}) : Label.{u})) (hoff : r.off f < r.N)
    (hc : ((lam + r.N : Ordinal.{u}) : Label.{u}) ≤ s r.cap) :
    s f = ((μ + r.off f : Ordinal.{u}) : Label.{u}) :=
  hs.label_eq hf hμ hk href (coe_add_lt_of_le hμl hoff hc)

/-- **(R4): the cells of `T` are at least `λ + R`**: if the marker is `λ + i` (`λ` zero or a
limit, `i < N`) and `λ + R` is at most the cap, every `y ∈ T` has `λ + R ≤ s y`. -/
theorem IsCorrect.le_label (hs : r.IsCorrect s) {y : ι} (hy : y ∈ r.T) {lam : Ordinal.{u}}
    (hlam : Order.IsSuccPrelimit lam) {i : ℕ} (hi : i < r.N)
    (ha : s r.marker = ((lam + i : Ordinal.{u}) : Label.{u}))
    (hc : ((lam + r.R : Ordinal.{u}) : Label.{u}) ≤ s r.cap) :
    ((lam + r.R : Ordinal.{u}) : Label.{u}) ≤ s y := by
  have h := hs.markerValue_le y hy
  rw [markerValue, ha, visibilityReplace_coe_add_natCast hlam hi, min_eq_left hc] at h
  exact h.trans (min_le_left _ _)

/-- **(R4): the cells of `T` lie above every `γ < λ + R`**, under the hypotheses of
`CapRequests.IsCorrect.le_label`. -/
theorem IsCorrect.lt_label (hs : r.IsCorrect s) {y : ι} (hy : y ∈ r.T) {lam : Ordinal.{u}}
    (hlam : Order.IsSuccPrelimit lam) {i : ℕ} (hi : i < r.N)
    (ha : s r.marker = ((lam + i : Ordinal.{u}) : Label.{u}))
    (hc : ((lam + r.R : Ordinal.{u}) : Label.{u}) ≤ s r.cap) {γ : Label.{u}}
    (hγ : γ < ((lam + r.R : Ordinal.{u}) : Label.{u})) : γ < s y :=
  hγ.trans_le (hs.le_label hy hlam hi ha hc)

end CapRequests

/-! ### The bottom class and admission -/

section BottomClass

variable {ι : Type*} {s : ι → Label.{u}}

/-- A state is **in the bottom class** `ZA` on the cells `B`: its `⊥` cells in `B` are exactly the
cells of `ZA` in `B`. -/
def InBottomClass (B ZA : Set ι) (s : ι → Label.{u}) : Prop :=
  ∀ d ∈ B, s d = ⊥ ↔ d ∈ ZA

variable {B ZA : Set ι}

/-- Capping at a label other than `⊥` keeps the bottom class, in both directions. -/
theorem inBottomClass_min_iff {h : Label.{u}} (hh : h ≠ ⊥) :
    InBottomClass B ZA (fun d ↦ min (s d) h) ↔ InBottomClass B ZA s := by
  simp only [InBottomClass, min_eq_bot, hh, or_false]

/-- **The bottom class of a transformation**: for a witness whose shifter reflects `⊥` and whose
suppressor is not `⊥` at the grades of the cells of `B`, the state
`d ↦ min (σ (s d)) (g (grade d))` is in the class exactly when `s` is. -/
theorem inBottomClass_map_iff {grade : ι → ℕ} {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) (hσ : ∀ x, σ x = ⊥ → x = ⊥) (hg : ∀ d ∈ B, g (grade d) ≠ ⊥) :
    InBottomClass B ZA (fun d ↦ min (σ (s d)) (g (grade d))) ↔ InBottomClass B ZA s := by
  refine forall₂_congr fun d hd ↦ ?_
  have e : σ (s d) = ⊥ ↔ s d = ⊥ := ⟨hσ _, fun h ↦ h ▸ hw.map_bot⟩
  rw [min_eq_bot, or_iff_left (hg d hd), e]

namespace CapRequests

variable (r : CapRequests ι)

/-- A state is **admitted** by the requests on the cells `B` with the bottom class `ZA`: it is
correct as soon as it is in the class. -/
def Admits (B ZA : Set ι) (s : ι → Label.{u}) : Prop :=
  InBottomClass B ZA s → r.IsCorrect s

variable {r}

/-- A correct state is admitted. -/
theorem IsCorrect.admits (hs : r.IsCorrect s) : r.Admits B ZA s := fun _ ↦ hs

variable (r B ZA) in
/-- The constant `⊥` state is admitted. -/
theorem admits_bot : r.Admits B ZA fun _ ↦ (⊥ : Label.{u}) :=
  (isCorrect_bot r).admits

/-- **Capping keeps admission**: for offsets of `F` at most `N` and `h` self-visible at `N`. -/
theorem Admits.cap (hs : r.Admits B ZA s) (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) {h : Label.{u}}
    (hh : IsSelfVisible r.N h) : r.Admits B ZA fun d ↦ min (s d) h := by
  intro hcl
  by_cases hb : h = ⊥
  · subst hb
    exact isCorrect_of_cap_eq_bot (min_bot_right _)
  · exact (hs ((inBottomClass_min_iff hb).mp hcl)).cap hoff hh

/-- **Transformations keep admission** when the shifter reflects `⊥` and the suppressor is not `⊥`
at the grades of the cells of `B`, for graded requests. -/
theorem Admits.map (hs : r.Admits B ZA s) {grade : ι → ℕ} (hgr : r.IsGraded grade)
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (hσ : ∀ x, σ x = ⊥ → x = ⊥) (hg : ∀ d ∈ B, g (grade d) ≠ ⊥) :
    r.Admits B ZA fun d ↦ min (σ (s d)) (g (grade d)) := fun hcl ↦
  (hs ((inBottomClass_map_iff hw hσ hg).mp hcl)).map hgr hw

end CapRequests

end BottomClass

end VaughtConjecture

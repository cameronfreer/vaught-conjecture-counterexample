/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.FieldLadder
import VaughtConjecture.MainTheorem.ReplicatedLevelRecovery

/-!
# The admission predicate of a two-sided state, without a cutoff field

Process rank `ω₁`, the finite span of mutual rigidity: the local admission predicate.

**Fields and designated fields.**  Two stage types `p` and `q` on one scheme with the same top
cells are compared on the **fields** `ι ⊕ ι`: the left copy `Sum.inl d` and the right copy
`Sum.inr d` of every cell `d : ι` (`ι = Fin S.card` for the common scheme `S`).  A set `T` of
cells, the common top cells, makes a field **designated** (`ProcessRank.IsDesignated`) when its
cell lies in `T`.  A **state** is a labelling `P : ι ⊕ ι → β` of all fields, in a linear order
with a bottom (`Label`, or the natural numbers for rank vectors).

**Separation and admission.**  A state is **separated** (`ProcessRank.IsSeparated`) when every
designated field is above bottom and above every undesignated field: with `m(P)` the largest
undesignated value (`ProcessRank.undesignatedMax`, bottom when there is none) and `s(P)` the least
designated value, `m(P) < s(P)`.  A state that is not separated is **inactive**.  At a grade `k`
at least a fixed grade `K` (the largest grade of a designated top), a state is **admitted**
(`ProcessRank.IsAdmitted`) when separation forces the two copies of every designated cell to be
equal; below `K` every state is admitted.  Every field is retained: the predicate reads all
fields, including those of grade above `k`, and involves no cutoff coordinate.

**Proved here.**

* Admission descends in the grade (`IsAdmitted.mono`) and holds below `K` (`isAdmitted_of_lt`).
* Admission is preserved by every monotone map fixing bottom applied to the values
  (`IsAdmitted.comp`); separation is reflected by such maps (`IsSeparated.of_comp`).
* Admission and separation depend only on the order and the bottom pattern of the values
  (`isAdmitted_iff_of_le_iff`); in particular a state is admitted exactly when its orbit code is
  (`isAdmitted_orbitCode_iff`), since the orbit code reflects the order of the values
  (`Label.orbitCode_le_iff`) and is bottom exactly where the state is.
* **The inactive-controller bound.**  A separated state `P` and a state `Q` with the same capped
  observation at a cap `h` above `m(P)` are both separated (`IsSeparated.of_min_eq`): the
  undesignated values of `Q` are those of `P`, and its designated values are above `m(P)`.  So an
  agreement height of a separated and an inactive state is at most `m(P)`; for rank vectors, the
  cut of a separated vector `a` and an inactive vector `b` is at most `m(a)`
  (`rankCut_le_undesignatedMax`).  No visibility replacement is used.  Conversely, a state with
  the capped observation of an inactive state at a cap above its `m` is inactive
  (`not_isSeparated_of_min_eq`).
-/

namespace VaughtConjecture.ProcessRank

open Finset

variable {ι β γ : Type*}

/-- The cell of a field: the cell it copies, on either side. -/
def fieldCell : ι ⊕ ι → ι := Sum.elim id id

@[simp] theorem fieldCell_inl (d : ι) : fieldCell (Sum.inl d : ι ⊕ ι) = d := rfl

@[simp] theorem fieldCell_inr (d : ι) : fieldCell (Sum.inr d : ι ⊕ ι) = d := rfl

/-- A field is **designated** for a set `T` of cells when its cell lies in `T`. -/
def IsDesignated (T : Set ι) (x : ι ⊕ ι) : Prop := fieldCell x ∈ T

section Order

variable [LinearOrder β] [OrderBot β] [LinearOrder γ] [OrderBot γ] {T : Set ι}
  {P : ι ⊕ ι → β} {K k k' : ℕ}

/-- A state is **separated**: every designated field is above bottom and above every undesignated
field (`m(P) < s(P)`). -/
def IsSeparated (T : Set ι) (P : ι ⊕ ι → β) : Prop :=
  ∀ x, IsDesignated T x → ⊥ < P x ∧ ∀ y, ¬ IsDesignated T y → P y < P x

/-- A state is **admitted** at the grade `k`, for the threshold grade `K`: at `k ≥ K`, separation
forces the two copies of every designated cell to be equal.  Below `K` the predicate holds. -/
def IsAdmitted (T : Set ι) (K k : ℕ) (P : ι ⊕ ι → β) : Prop :=
  K ≤ k → IsSeparated T P → ∀ d ∈ T, P (Sum.inl d) = P (Sum.inr d)

/-- Every state is admitted below the threshold grade. -/
theorem isAdmitted_of_lt (h : k < K) : IsAdmitted T K k P :=
  fun hK ↦ absurd hK (not_le.mpr h)

/-- **Admission descends** in the grade. -/
theorem IsAdmitted.mono (h : IsAdmitted T K k P) (hk : k' ≤ k) : IsAdmitted T K k' P :=
  fun hK ↦ h (hK.trans hk)

/-- **Separation is reflected** by a monotone map fixing bottom. -/
theorem IsSeparated.of_comp {f : β → γ} (hf : Monotone f) (hf0 : f ⊥ = ⊥)
    (h : IsSeparated T (f ∘ P)) : IsSeparated T P := by
  intro x hx
  obtain ⟨hb, hlt⟩ := h x hx
  refine ⟨bot_lt_iff_ne_bot.mpr fun h0 ↦ ?_, fun y hy ↦ ?_⟩
  · simp [Function.comp, h0, hf0] at hb
  · by_contra hle
    exact absurd (hf (not_lt.mp hle)) (not_le.mpr (hlt y hy))

/-- **Admission is preserved** by a monotone map fixing bottom, applied to the values. -/
theorem IsAdmitted.comp {f : β → γ} (hf : Monotone f) (hf0 : f ⊥ = ⊥)
    (h : IsAdmitted T K k P) : IsAdmitted T K k (f ∘ P) :=
  fun hK hs d hd ↦ congrArg f (h hK (hs.of_comp hf hf0) d hd)

/-- **Separation depends only on the order and the bottom pattern of the values.** -/
theorem isSeparated_iff_of_le_iff {Q : ι ⊕ ι → γ} (hle : ∀ x y, Q x ≤ Q y ↔ P x ≤ P y)
    (hbot : ∀ x, Q x = ⊥ ↔ P x = ⊥) : IsSeparated T Q ↔ IsSeparated T P := by
  have hlt (x y) : Q x < Q y ↔ P x < P y := by
    rw [← not_le, ← not_le, hle]
  refine forall_congr' fun x ↦ forall_congr' fun _ ↦ ?_
  rw [bot_lt_iff_ne_bot, bot_lt_iff_ne_bot, Ne, Ne, hbot]
  exact and_congr Iff.rfl (forall_congr' fun y ↦ forall_congr' fun _ ↦ hlt y x)

/-- **Admission depends only on the order and the bottom pattern of the values.** -/
theorem isAdmitted_iff_of_le_iff {Q : ι ⊕ ι → γ} (hle : ∀ x y, Q x ≤ Q y ↔ P x ≤ P y)
    (hbot : ∀ x, Q x = ⊥ ↔ P x = ⊥) : IsAdmitted T K k Q ↔ IsAdmitted T K k P := by
  have heq (x y) : Q x = Q y ↔ P x = P y := by
    rw [le_antisymm_iff, le_antisymm_iff, hle, hle]
  unfold IsAdmitted
  rw [isSeparated_iff_of_le_iff hle hbot]
  exact imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
    forall_congr' fun d ↦ forall_congr' fun _ ↦ heq _ _

/-- The largest undesignated value `m(P)`, bottom when there is none. -/
noncomputable def undesignatedMax [Fintype ι] (T : Set ι) (P : ι ⊕ ι → β) : β := by
  classical exact (univ.filter fun x ↦ ¬ IsDesignated T x).sup P

theorem le_undesignatedMax [Fintype ι] {y : ι ⊕ ι} (hy : ¬ IsDesignated T y) :
    P y ≤ undesignatedMax T P := by
  classical
  exact Finset.le_sup (f := P) (mem_filter.mpr ⟨mem_univ _, hy⟩)

/-- At a separated state, every designated value is above `m(P)`. -/
theorem IsSeparated.undesignatedMax_lt [Fintype ι] (hP : IsSeparated T P) {x : ι ⊕ ι}
    (hx : IsDesignated T x) : undesignatedMax T P < P x := by
  classical
  obtain ⟨hb, hlt⟩ := hP x hx
  exact (Finset.sup_lt_iff hb).mpr fun y hy ↦ hlt y (mem_filter.mp hy).2

/-- **The inactive-controller bound.**  A state `Q` with the capped observation of a separated
state `P` at a cap `h` above `m(P)` is separated.  So a separated and an inactive state never
agree capped at a cap above `m(P)`. -/
theorem IsSeparated.of_min_eq [Fintype ι] (hP : IsSeparated T P) {Q : ι ⊕ ι → β} {h : β}
    (hh : undesignatedMax T P < h) (hPQ : ∀ x, min (P x) h = min (Q x) h) :
    IsSeparated T Q := by
  -- the undesignated values of `Q` are those of `P`
  have hund {y : ι ⊕ ι} (hy : ¬ IsDesignated T y) : Q y = P y := by
    have hPy : P y < h := (le_undesignatedMax hy).trans_lt hh
    have h1 := hPQ y
    rw [min_eq_left hPy.le] at h1
    rcases le_total (Q y) h with hq | hq
    · rwa [min_eq_left hq, eq_comm] at h1
    · rw [min_eq_right hq] at h1
      exact absurd h1 hPy.ne
  intro x hx
  have hmx : undesignatedMax T P < min (Q x) h := by
    rw [← hPQ x]
    exact lt_min (hP.undesignatedMax_lt hx) hh
  have hQx : undesignatedMax T P < Q x := hmx.trans_le (min_le_left _ _)
  exact ⟨bot_le.trans_lt hQx, fun y hy ↦ (hund hy).symm ▸ (le_undesignatedMax hy).trans_lt hQx⟩

omit [OrderBot β] in
/-- A value below a cap is recovered from its capped observation. -/
theorem eq_of_min_eq_of_lt {a a' h : β} (he : min a' h = min a h) (ha : a < h) : a' = a := by
  rw [min_eq_left ha.le] at he
  rcases le_total a' h with h' | h'
  · rwa [min_eq_left h'] at he
  · rw [min_eq_right h'] at he
    exact absurd he.symm ha.ne

/-- **Inactivity is kept by a cap above `m(P)`**: a state with the capped observation of an
inactive state `P` at a cap above `m(P)` is inactive. -/
theorem not_isSeparated_of_min_eq [Fintype ι] (hP : ¬ IsSeparated T P) {Q : ι ⊕ ι → β} {h : β}
    (hh : undesignatedMax T P < h) (hPQ : ∀ x, min (Q x) h = min (P x) h) :
    ¬ IsSeparated T Q := by
  classical
  intro hQ
  have hund {y : ι ⊕ ι} (hy : ¬ IsDesignated T y) : Q y = P y :=
    eq_of_min_eq_of_lt (hPQ y) ((le_undesignatedMax hy).trans_lt hh)
  have hmQ : undesignatedMax T Q < h := by
    refine lt_of_le_of_lt ?_ hh
    unfold undesignatedMax
    refine Finset.sup_le fun y hy ↦ ?_
    rw [hund (mem_filter.mp hy).2]
    exact le_undesignatedMax (mem_filter.mp hy).2
  exact hP (hQ.of_min_eq hmQ hPQ)

end Order

/-! ### Orbit codes and rank vectors -/

section Instances

variable [Fintype ι] {T : Set ι} {K k j : ℕ}

/-- **A state is admitted exactly when its orbit code is**: the orbit code reflects the order of
the values (`Label.orbitCode_le_iff`) and is bottom exactly where the state is. -/
theorem isAdmitted_orbitCode_iff {P : ι ⊕ ι → Label} :
    IsAdmitted T K k (Label.orbitCode j P) ↔ IsAdmitted T K k P :=
  isAdmitted_iff_of_le_iff (fun _ _ ↦ Label.orbitCode_le_iff)
    (fun _ ↦ Label.orbitCode_eq_bot_iff)

/-- **The inactive-controller bound for rank vectors**: the cut of a separated rank vector `a`
and an inactive rank vector `b` is at most the largest undesignated rank of `a`. -/
theorem rankCut_le_undesignatedMax {a b : ι ⊕ ι → ℕ} (ha : IsSeparated T a)
    (hb : ¬ IsSeparated T b) (H : ℕ) : Label.rankCut H a b ≤ undesignatedMax T a := by
  by_contra hlt
  exact hb (ha.of_min_eq (not_le.mp hlt) (Label.rankAgree_rankCut H a b))

end Instances

end VaughtConjecture.ProcessRank

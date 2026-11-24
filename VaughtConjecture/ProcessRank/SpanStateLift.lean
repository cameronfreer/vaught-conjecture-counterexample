/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanAdmission
import VaughtConjecture.ProcessRank.SpanGraft
import VaughtConjecture.Stage.Legal

/-!
# The one-sided capped lift of two-sided states

Process rank `ω₁`, the finite span of mutual rigidity: the state step of the master levels.

**States.**  For a scheme `S` on `n` points (the common scheme of the two types), a **state** is a
labelling `P` of the fields `Fin S.card ⊕ Fin S.card` (`VaughtConjecture.ProcessRank`): the left
copy `Sum.inl d` and the right copy `Sum.inr d` of every cell.  The copy on the side `b`
(`ProcessRank.sideField`) is the left copy for `false` and the right copy for `true`.  A state is
**lawful at the grade `k`** (`ProcessRank.IsStateLawfulAt`) when both of its sides are lawful below
the pure cut `(univ, k)` of `S`.  The fields of grade above `k` are kept in the state and read by
the admission predicate; they are only required to be self-visible at the grade one.

**The one-sided capped lift** (`ProcessRank.OneSidedStateLiftTarget`).  Let `S` be legal, `T` a
set of cells of grade at most `K`, `P` a state lawful and admitted at the grade `k` with every value
self-visible at the grade one, `c` a cap self-visible at `k`, and `r` lawful below a graded face
`X ≤ (univ, k)` of `S`, agreeing capped at `c` with the side `b` of `P`.  Then some state `P'`,
lawful and admitted at `k` with every value self-visible at the grade one, equals `r` on the side
`b` below `X` and agrees with `P` capped at `c` at **every** field, those above the cut included.
The intended proof extends `r` on its side to the pure cut by bountifulness and chooses the other
side by three cases (for `k ≥ K`; below `K` the other side is kept):

1. `m(P) ≥ c`: cap the other side at `c`, its fields of higher grade included; an undesignated
   field at least `c` on one side and the capped designated fields on the other make the state
   inactive;
2. `m(P) < c` and `P` inactive: keep the other side; the low designated field witnessing
   inactivity and every low field are fixed by the cap agreement;
3. `m(P) < c` and `P` separated: both sides have the same high set (all designated fields
   matched in `P`, all undesignated fields low), and the high tail of the prescribed side is
   grafted onto the other side (`Scheme.GraftHighTailTarget`); designated fields above the
   grade `k` do not occur since `k ≥ K`.

No prescription is made on both sides at once.  Proved (`ProcessRank.oneSidedStateLift`).  The
inactivity in case 1 is that of the state itself: a designated field of the other side is at most
`c`, and an undesignated field reaching `m(P) ≥ c` stays at least `c` (for `c = ⊥` the capped
designated fields are `⊥`).  In case 2 every field below `c` is fixed, so the state stays inactive
(`ProcessRank.not_isSeparated_of_min_eq`).  In case 3 admission holds outright.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label

variable {ι β : Type*}

/-- The copy of a cell on the side `b`: the left copy for `false`, the right copy for `true`. -/
def sideField (b : Bool) (d : ι) : ι ⊕ ι := bif b then Sum.inr d else Sum.inl d

variable {n : ℕ}

/-- A state is **lawful at the grade `k`**: both of its sides are lawful below the pure cut
`(univ, k)`. -/
def IsStateLawfulAt (S : Scheme.{u} n) (k : ℕ) (P : Fin S.card ⊕ Fin S.card → Label.{u}) : Prop :=
  ∀ b : Bool, S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun d ↦ P (sideField b d)

/-- **Target: the one-sided capped lift of admitted states.**  For a legal scheme, a set `T` of
cells of grade at most `K`, a state `P` lawful and admitted at the grade `k` with every value
self-visible at the grade one, a cap `c` self-visible at `k`, and a labelling `r` lawful below a
graded face `X ≤ (univ, k)` agreeing capped at `c` with the side `b` of `P`, some state lawful and
admitted at `k`, with every value self-visible at the grade one, is `r` on the side `b` below `X`
and agrees with `P` capped at `c` at every field.  Stated. -/
def OneSidedStateLiftTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Scheme.{u} n), S.IsLegal → ∀ (T : Set (Fin S.card)) (K k : ℕ),
    (∀ d ∈ T, S.toCellScheme.grade d ≤ K) → ∀ (b : Bool) (X : Finset (Fin n) × ℕ),
    X ∈ S.toCellScheme.gradedFaces → X ≤ ((univ : Finset (Fin n)), k) →
    ∀ (c : Label.{u}) (P : Fin S.card ⊕ Fin S.card → Label.{u})
      (r : S.toCellScheme.below X → Label.{u}),
      IsSelfVisible k c → IsStateLawfulAt S k P → (∀ x, IsSelfVisible 1 (P x)) →
      IsAdmitted T K k P → S.rows.IsLawfulBelow X r →
      (∀ d : S.toCellScheme.below X, min (P (sideField b d.1)) c = min (r d) c) →
      ∃ P' : Fin S.card ⊕ Fin S.card → Label.{u}, IsStateLawfulAt S k P' ∧
        (∀ x, IsSelfVisible 1 (P' x)) ∧ IsAdmitted T K k P' ∧
        (∀ d : S.toCellScheme.below X, P' (sideField b d.1) = r d) ∧
        ∀ x, min (P' x) c = min (P x) c

/-- The state with the labelling `B` on the side `b` and `O` on the other side. -/
def stateOf (b : Bool) (B O : ι → β) : ι ⊕ ι → β :=
  Sum.elim (bif b then O else B) (bif b then B else O)

@[simp] theorem stateOf_sideField_self (b : Bool) (B O : ι → β) (d : ι) :
    stateOf b B O (sideField b d) = B d := by
  cases b <;> rfl

@[simp] theorem stateOf_sideField_not (b : Bool) (B O : ι → β) (d : ι) :
    stateOf b B O (sideField (!b) d) = O d := by
  cases b <;> rfl

/-- Every field is the copy of a cell on the side `b` or on the other side. -/
theorem forall_field_iff (b : Bool) {p : ι ⊕ ι → Prop} :
    (∀ x, p x) ↔ ∀ d, p (sideField b d) ∧ p (sideField (!b) d) := by
  refine ⟨fun h d ↦ ⟨h _, h _⟩, fun h x ↦ ?_⟩
  rcases x with d | d <;> cases b
  exacts [(h d).1, (h d).2, (h d).2, (h d).1]

/-- The two copies of a cell, on the side `b` and the other side, are its two copies. -/
theorem inl_eq_inr_iff_sideField {P : ι ⊕ ι → β} (b : Bool) (d : ι) :
    P (Sum.inl d) = P (Sum.inr d) ↔ P (sideField b d) = P (sideField (!b) d) := by
  cases b
  · rfl
  · exact eq_comm

/-- **The one-sided capped lift of admitted states.**  Proved; see the module docstring. -/
theorem oneSidedStateLift : OneSidedStateLiftTarget.{u} := by
  intro n S hS T K k hTK b X hX hXk c P r hc hP hP1 hPA hr hrP
  classical
  -- the pure cut and its graded face
  have hgrade (d : Fin S.card) : S.toCellScheme.grade d ≤ n :=
    (hS.isWellFormed.isWellFormed.grade_le_card d).trans
      ((card_le_univ _).trans_eq (Fintype.card_fin n))
  have hX1 : 1 ≤ X.2 := hX.2.1
  have hk1 : 1 ≤ k := hX1.trans hXk.2
  set k' := min k n with hk'
  have hXn : X.2 ≤ n := hX.2.2.trans ((card_le_univ _).trans_eq (Fintype.card_fin n))
  have hY : ((univ : Finset (Fin n)), k') ∈ S.toCellScheme.gradedFaces :=
    ⟨hS.isWellFormed.univ_mem_faces, lt_of_lt_of_le hX1 (le_min hXk.2 hXn),
      (min_le_right _ _).trans_eq (by simp)⟩
  have hXY : X ≤ ((univ : Finset (Fin n)), k') := ⟨subset_univ _, le_min hXk.2 hXn⟩
  have hcut (w : Fin S.card → Label.{u}) :
      S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) (fun d ↦ w d) ↔
        S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k') (fun d ↦ w d) := by
    refine ⟨fun h ↦ h.mono (X := ((univ : Finset (Fin n)), k')) ⟨subset_rfl, min_le_left _ _⟩,
      fun h ↦ ?_⟩
    refine (CellScheme.Rows.isLawfulBelow_congr
      (w := fun d ↦ if S.toCellScheme.grade d ≤ k' then w d else ⊥) (w' := w) fun d hd ↦ ?_).mp
      (CellScheme.Rows.isLawfulBelow_extendAbove (K := k) h)
    exact ite_eq_left (le_min hd.2 (hgrade d))
  have hck : IsSelfVisible k' c := hc.mono (min_le_left _ _)
  have hc1 : IsSelfVisible 1 c := hc.mono hk1
  -- the prescribed side, extended to the pure cut by bountifulness
  set PB : Fin S.card → Label.{u} := fun d ↦ P (sideField b d) with hPB
  set PO : Fin S.card → Label.{u} := fun d ↦ P (sideField (!b) d) with hPO
  obtain ⟨q', hq'l, hq'c, hq'r⟩ :=
    (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
      (hS.isBountiful.cappedLift hX hY hXY) c hck r (fun d ↦ PB d) hr
      ((hcut PB).mp (hP b)) fun d ↦ hrP d
  set R : Fin S.card → Label.{u} := fun d ↦
    if h : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), k') then q' ⟨d, h⟩ else PB d
    with hR
  have hRin (d : Fin S.card) (h : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), k')) :
      R d = q' ⟨d, h⟩ := dite_eq_left h
  have hRout (d : Fin S.card) (h : d ∉ S.toCellScheme.below ((univ : Finset (Fin n)), k')) :
      R d = PB d := dite_eq_right h
  have hRl : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) (fun d ↦ R d) := by
    refine (hcut R).mpr ?_
    have he : (fun d : S.toCellScheme.below ((univ : Finset (Fin n)), k') ↦ R d) = q' :=
      funext fun d ↦ hRin d d.2
    rw [he]
    exact hq'l
  have hRc (d : Fin S.card) : min (R d) c = min (PB d) c := by
    by_cases h : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), k')
    · rw [hRin d h]
      exact hq'c ⟨d, h⟩
    · rw [hRout d h]
  have hRr (d : S.toCellScheme.below X) : R d = r d := by
    rw [hRin d ((S.toCellScheme.below_mono hXY) d.2)]
    exact hq'r d
  have hR1 (d : Fin S.card) : IsSelfVisible 1 (R d) := by
    by_cases h : d ∈ S.toCellScheme.below ((univ : Finset (Fin n)), k')
    · rw [hRin d h]
      exact (hq'l.orderly ⟨d, h⟩).mono (hS.isWellFormed.isWellFormed.grade_pos d)
    · rw [hRout d h]
      exact hP1 _
  have hPOl : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) (fun d ↦ PO d) := hP (!b)
  -- a state with `R` on the side `b`, agreeing with `P` capped at `c`, lawful and self-visible
  have hfinish (O : Fin S.card → Label.{u})
      (hOl : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) (fun d ↦ O d))
      (hO1 : ∀ d, IsSelfVisible 1 (O d)) (hOc : ∀ d, min (O d) c = min (PO d) c)
      (hA : IsAdmitted T K k (stateOf b R O)) :
      ∃ P' : Fin S.card ⊕ Fin S.card → Label.{u}, IsStateLawfulAt S k P' ∧
        (∀ x, IsSelfVisible 1 (P' x)) ∧ IsAdmitted T K k P' ∧
        (∀ d : S.toCellScheme.below X, P' (sideField b d.1) = r d) ∧
        ∀ x, min (P' x) c = min (P x) c := by
    refine ⟨stateOf b R O, fun b' ↦ ?_, (forall_field_iff b).mpr fun d ↦ ?_, hA, fun d ↦ ?_,
      (forall_field_iff b).mpr fun d ↦ ?_⟩
    · rcases Bool.eq_or_eq_not b' b with rfl | rfl
      · simpa using hRl
      · simpa using hOl
    · simp only [stateOf_sideField_self, stateOf_sideField_not]
      exact ⟨hR1 d, hO1 d⟩
    · rw [stateOf_sideField_self, hRr]
    · simp only [stateOf_sideField_self, stateOf_sideField_not]
      exact ⟨hRc d, hOc d⟩
  -- the cases
  by_cases hKk : K ≤ k
  swap
  · exact hfinish PO hPOl (fun d ↦ hP1 _) (fun d ↦ rfl) (isAdmitted_of_lt (not_le.mp hKk))
  -- the agreement of the new state with `P`, field by field
  have hagree (O : Fin S.card → Label.{u}) (hOc : ∀ d, min (O d) c = min (PO d) c) :
      ∀ x, min (stateOf b R O x) c = min (P x) c :=
    (forall_field_iff b).mpr fun d ↦ by
      simp only [stateOf_sideField_self, stateOf_sideField_not]
      exact ⟨hRc d, hOc d⟩
  by_cases hmc : c ≤ undesignatedMax T P
  · -- case 1: cap the other side at `c`
    refine hfinish (fun d ↦ min (PO d) c) (hPOl.min_const_of_isSelfVisible hc)
      (fun d ↦ (hP1 _).min hc1) (fun d ↦ by rw [min_assoc, min_self]) ?_
    rintro - hsep d hd
    exfalso
    have hagr := hagree (fun d ↦ min (PO d) c) fun d ↦ by rw [min_assoc, min_self]
    set P' := stateOf b R fun d ↦ min (PO d) c
    have hdes : IsDesignated T (sideField (!b) d) := by
      cases b <;> exact hd
    obtain ⟨hpos, hlt⟩ := hsep _ hdes
    have hle : P' (sideField (!b) d) ≤ c := by
      simp only [P', stateOf_sideField_not]; exact min_le_right _ _
    by_cases hc0 : c = ⊥
    · exact absurd (hle.trans_eq hc0) (not_le.mpr hpos)
    · -- an undesignated field reaching `m(P) ≥ c`
      have hne : (univ.filter fun x ↦ ¬ IsDesignated T x).Nonempty := by
        by_contra hem
        rw [not_nonempty_iff_eq_empty] at hem
        have : undesignatedMax T P = ⊥ := by
          unfold undesignatedMax; rw [hem, sup_empty]
        exact hc0 (le_bot_iff.mp (this ▸ hmc))
      obtain ⟨e, he, hem⟩ := exists_mem_eq_sup _ hne P
      have hce : c ≤ P e := hmc.trans_eq (by unfold undesignatedMax; exact hem)
      have hce' : c ≤ P' e := by
        have h := hagr e
        rw [min_eq_right hce] at h
        exact h ▸ min_le_left _ _
      exact absurd (hle.trans hce') (not_le.mpr (hlt e (mem_filter.mp he).2))
  rw [not_le] at hmc
  by_cases hsepP : IsSeparated T P
  · -- case 3: graft the high tail of the prescribed side onto the other side
    have hBO (d : Fin S.card) (hd : d ∈ T) : PB d = PO d := by
      have := hPA hKk hsepP d hd
      rwa [inl_eq_inr_iff_sideField b] at this
    have hhigh (d : Fin S.card) : c ≤ PO d ↔ c ≤ R d := by
      have hRB : c ≤ R d ↔ c ≤ PB d := by
        rw [← min_eq_right_iff, ← min_eq_right_iff (a := PB d), hRc d]
      rw [hRB]
      by_cases hd : d ∈ T
      · rw [hBO d hd]
      · have hBd : PB d < c := (le_undesignatedMax (P := P) (y := sideField b d)
          (by cases b <;> exact hd)).trans_lt hmc
        have hOd : PO d < c := (le_undesignatedMax (P := P) (y := sideField (!b) d)
          (by cases b <;> exact hd)).trans_lt hmc
        exact iff_of_false (not_le.mpr hOd) (not_le.mpr hBd)
    refine hfinish (fun d ↦ if c ≤ PO d then R d else PO d)
      (Scheme.graftHighTail S _ PO R c hPOl hRl hc fun d _ ↦ hhigh d)
      (fun d ↦ by split_ifs; exacts [hR1 d, hP1 _]) (fun d ↦ ?_) ?_
    · split_ifs with h
      · rw [min_eq_right h, min_eq_right ((hhigh d).mp h)]
      · rfl
    · rintro - - d hd
      rw [inl_eq_inr_iff_sideField b, stateOf_sideField_self, stateOf_sideField_not]
      split_ifs with h
      · rfl
      · have hOd : PO d < c := not_le.mp h
        rw [← hBO d hd] at hOd ⊢
        exact eq_of_min_eq_of_lt (hRc d) hOd
  · -- case 2: keep the other side; the state stays inactive
    refine hfinish PO hPOl (fun d ↦ hP1 _) (fun d ↦ rfl) fun _ hsep ↦ ?_
    exact absurd hsep (not_isSeparated_of_min_eq hsepP hmc (hagree PO fun d ↦ rfl))

end VaughtConjecture.ProcessRank

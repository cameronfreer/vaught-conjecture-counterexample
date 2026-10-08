/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Cap

/-!
# Capping the cells above a grade

**Capping above a grade.**  For a grade `K`, the cells of grade above `K` form an upper set
(`StageType.lt_grade_upper`), and availability relates cells of equal grades only, so no cell
outside the set is carried into it.  So capping them at `c` (`StageType.capAbove`, the instance of
`StageType.capOn`, in `VaughtConjecture.Stage.Cap`) needs no availability condition: the
availability hypothesis of `StageType.capOn` is vacuous, since it concerns cells of equal grade;
the cap premises `c < α` and self-visibility of `c` at the arity remain.  When `c` lies above every
label of `t` other than `⊤`, the capped type
* has the scheme of `t`, so it is legal exactly when `t` is (`StageType.isLegal_capAbove`);
* keeps every label other than `⊤` (`StageType.capAbove_label_of_ne_top`);
* is labelled `⊤` exactly at the cells of `t` labelled `⊤` of grade at most `K`
  (`StageType.capAbove_label_eq_top_iff`);
* has every face of `t` whose cells labelled `⊤` have grade at most `K` as a face, literally,
  labels above `K` included (`StageType.restrictFace_capAbove`).
At a limit stage such a cap exists, self-visible at every arity
(`StageType.exists_cap_ne_top`).  The faces are kept through
`StageType.restrictFace_capOn_of_label_le`: the visible cells of grade above `K` of such a face are
not labelled `⊤`, so they are already below the cap.

Capping above a grade truncates a pinned extension to a top grade at most `K` while keeping its
two faces (`VaughtConjecture.MainTheorem.BoundedCoatomDetermination`).

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.

## References

Capping a lawful section is [Kni26, Lemma 2.5.8].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### Capping above a grade -/

/-- The cells of grade above `K` form an upper set of the graded order. -/
theorem lt_grade_upper (t : StageType.{u} α n) (K : ℕ) (d s : Fin t.card)
    (hd : K < t.toCellScheme.grade d)
    (hds : t.toCellScheme.gradedIndex d ≤ t.toCellScheme.gradedIndex s) :
    K < t.toCellScheme.grade s :=
  hd.trans_le hds.2

/-- The **stage type capped above the grade** `K`: the scheme of `t` with the cells of grade above
`K` capped at `c` and the other labels kept (`StageType.capOn`).  Availability relates cells of
equal grades, so the availability hypothesis of `StageType.capOn` is vacuous. -/
noncomputable def capAbove (t : StageType.{u} α n) (K : ℕ) (c : Ordinal.{u})
    (hc : IsSelfVisible n (c : Label)) (hcα : c < α) : StageType.{u} α n :=
  t.capOn (fun d ↦ K < t.toCellScheme.grade d) c hc hcα (t.lt_grade_upper K)
    fun _ _ _ hg hs hs' ↦ absurd (hg ▸ hs') hs

variable {t : StageType.{u} α n} {K : ℕ} {c : Ordinal.{u}} {hc : IsSelfVisible n (c : Label)}
  {hcα : c < α}

/-- The scheme of a type capped above a grade is the scheme of the type. -/
@[simp] theorem capAbove_toScheme : (t.capAbove K c hc hcα).toScheme = t.toScheme :=
  rfl

/-- A type capped above a grade is legal exactly when the type is: legality concerns the
scheme. -/
@[simp] theorem isLegal_capAbove : (t.capAbove K c hc hcα).IsLegal ↔ t.IsLegal :=
  Iff.rfl

/-- The labels of a type capped above `K`: capped at the cells of grade above `K`, kept
elsewhere. -/
theorem capAbove_label (d : Fin t.card) : (t.capAbove K c hc hcα).label d =
    if K < t.toCellScheme.grade d then min (t.label d) c else t.label d :=
  rfl

/-- The labels of grade at most `K` are kept. -/
theorem capAbove_label_of_le {d : Fin t.card} (hd : t.toCellScheme.grade d ≤ K) :
    (t.capAbove K c hc hcα).label d = t.label d := by
  rw [capAbove_label]
  split_ifs with hK
  · omega
  · rfl

/-- The labels other than `⊤` are kept when the cap lies above them. -/
theorem capAbove_label_of_ne_top (hct : ∀ d, t.label d ≠ ⊤ → t.label d ≤ c) {d : Fin t.card}
    (hd : t.label d ≠ ⊤) : (t.capAbove K c hc hcα).label d = t.label d := by
  rw [capAbove_label]
  split_ifs
  · exact min_eq_left (hct d hd)
  · rfl

/-- **The top labels of a type capped above `K`** are the top labels of the type of grade at
most `K`. -/
theorem capAbove_label_eq_top_iff {d : Fin t.card} :
    (t.capAbove K c hc hcα).label d = ⊤ ↔ t.label d = ⊤ ∧ t.toCellScheme.grade d ≤ K := by
  rw [capAbove_label]
  split_ifs with hK
  · refine iff_of_false (fun h ↦ ?_) fun h ↦ absurd h.2 (not_le.mpr hK)
    have hle : min (t.label d) (c : Label) ≤ c := min_le_right _ _
    rw [h, top_le_iff] at hle
    exact WithBot.coe_injective.ne WithTop.coe_ne_top hle
  · exact ⟨fun h ↦ ⟨h, not_lt.mp hK⟩, And.left⟩

/-- **Faces of top grade at most `K` are kept literally**: when the cap lies above every label of
`t` other than `⊤`, every face `p` of `t` whose cells labelled `⊤` have grade at most `K` is the
face of the type capped above `K` along the same embedding, labels above `K` included. -/
theorem restrictFace_capAbove (hct : ∀ d, t.label d ≠ ⊤ → t.label d ≤ c) {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} (hp : restrictFace f t = some p)
    (hpK : ∀ i, p.label i = ⊤ → p.toCellScheme.grade i ≤ K) :
    restrictFace f (t.capAbove K c hc hcα) = some p := by
  refine (restrictFace_capOn_of_label_le fun d hd hdK ↦ ?_).trans hp
  by_cases htop : t.label d = ⊤
  · obtain ⟨i, rfl⟩ := exists_faceCell_eq hp hd
    rw [label_faceCell] at htop
    have := hpK i htop
    rw [grade_faceCell] at hdK
    omega
  · exact hct d htop

/-- **A cap above the labels other than `⊤`**: at a limit stage `α`, for every stage type and
every arity `k` there is an ordinal below `α`, self-visible at `k`, above every label of the
stage type other than `⊤`. -/
theorem exists_cap_ne_top (hα : Order.IsSuccLimit α) (t : StageType.{u} α n) (k : ℕ) :
    ∃ c : Ordinal.{u}, c < α ∧ IsSelfVisible k (c : Label) ∧
      ∀ d, t.label d ≠ ⊤ → t.label d ≤ c := by
  obtain ⟨o, ho, hle⟩ := t.exists_label_le hα.bot_lt
  obtain ⟨c, hoc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit ho k
  exact ⟨c, hcα, hc, fun d hd ↦ (hle d hd).trans
    (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hoc.le))⟩

end StageType

end VaughtConjecture

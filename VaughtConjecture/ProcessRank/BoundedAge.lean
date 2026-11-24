/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TopGradeTruncation
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem
import VaughtConjecture.Stage.CountOmegaOne

/-!
# The bounded top-grade ages and their witnesses

Companion programme over the density sentence, process rank `ω₁`: the infinite lower bound on the
number of Scott classes.  For a natural number `K`, the **bounded age** `A_K`
(`ProcessRank.Bounded.boundedAge K`) is the family of the legal stage types of top grade at most
`K` (`StageType.topGrade`, the largest grade of a cell labelled `⊤`).  At `K = 0` it is the age of
the legal top-free types of the `ℵ₁` companion construction (`ProcessRank.Bounded.boundedAge_zero`).

**Closure properties** (all proved):

* face closed (`ProcessRank.Bounded.mem_boundedAge_of_restrictFace`): the top grade does not
  increase along face maps (`StageType.topGrade_le_of_restrictFace`);
* reindex closed (`ProcessRank.Bounded.reindex_mem_boundedAge`, `StageType.topGrade_reindex`);
* the bottom one-point type lies in every bounded age
  (`ProcessRank.Bounded.pointType_mem_boundedAge`);
* exact pinned extensions within the age (`ProcessRank.Bounded.exists_pinned_extension_mem`,
  from `StageType.exists_pinned_extension_topGrade_le`: the exact pinned extension capped above
  `K` keeps both prescribed faces literally);
* at most `ℵ₁` members of each arity at stage `ω₁`
  (`ProcessRank.Bounded.mk_boundedAge_le_aleph_one`, from
  `StageType.mk_le_aleph_one_of_omega_one`).

**Witnesses of every top grade.**  The one-point apex type (`StageType.onePointApex`, its single
cell labelled `⊤`) is legal of top grade `1` (`ProcessRank.Bounded.topGrade_onePointApex`, proved).
For every `n ≥ 1` some legal type on `n` points has top grade exactly `n`
(`ProcessRank.Bounded.TopGradeWitnessTarget`, proved, `ProcessRank.Bounded.topGradeWitnessTarget`,
at every stage that is zero or a limit): the proof starts from the
one-point apex type and applies the coatom extension property with apex
(`StageType.HasApexCoatomExtensions`) to two copies of the witness on `n` points over their
common face along the first `n - 1` points; the apex of the extension has full grade `n + 1` and
dominates the inherited cell labelled `⊤`, so it is labelled `⊤`, and no grade exceeds the arity
(`StageType.grade_le`).  The witness of top grade `n` lies in `A_K` exactly when `n ≤ K`.

## Placement

The bounded top-grade part of the process-rank companion programme (the files
`VaughtConjecture/ProcessRank/Bounded*.lean`); the construction is in
`VaughtConjecture.ProcessRank.BoundedConstruction`, the distinctness of the Scott classes in
`VaughtConjecture.ProcessRank.BoundedDistinct`.
-/

universe u

namespace VaughtConjecture.ProcessRank.Bounded

open Ordinal

variable {α : Ordinal.{u}} {n m : ℕ}

/-- The **bounded age** `A_K`: the legal stage types of top grade at most `K`. -/
def boundedAge (K : ℕ) (m : ℕ) : Set (StageType.{u} α m) :=
  {D | D.IsLegal ∧ D.topGrade ≤ K}

theorem mem_boundedAge {K : ℕ} {D : StageType.{u} α m} :
    D ∈ boundedAge K m ↔ D.IsLegal ∧ D.topGrade ≤ K :=
  Iff.rfl

/-- **The bounded age of grade `0` is the age of the legal top-free types**: grades are
positive, so top grade `0` is top-freeness (`StageType.topGrade_eq_zero_iff`). -/
theorem boundedAge_zero (m : ℕ) :
    boundedAge (α := α) 0 m = {D | D.IsLegal ∧ D.IsTopFree} := by
  ext D
  simp only [mem_boundedAge, Nat.le_zero, StageType.topGrade_eq_zero_iff, Set.mem_ofPred_eq]

/-- The bounded ages increase with the bound. -/
theorem boundedAge_mono {K K' : ℕ} (h : K ≤ K') (m : ℕ) :
    boundedAge (α := α) K m ⊆ boundedAge K' m :=
  fun _ hD ↦ ⟨hD.1, hD.2.trans h⟩

/-- **The bounded age is face closed**: a face of a legal type is legal, and the top grade does
not increase along face maps. -/
theorem mem_boundedAge_of_restrictFace {K : ℕ} {D : StageType.{u} α m} (hD : D ∈ boundedAge K m)
    {f : Fin n ↪ Fin m} {p : StageType.{u} α n} (hp : StageType.restrictFace f D = some p) :
    p ∈ boundedAge K n :=
  ⟨hD.1.restrictFace f hp, (StageType.topGrade_le_of_restrictFace hp).trans hD.2⟩

/-- **The bounded age is reindex closed.** -/
theorem reindex_mem_boundedAge {K : ℕ} {D : StageType.{u} α m} (hD : D ∈ boundedAge K m)
    (σ : Equiv.Perm (Fin m)) : D.reindex σ ∈ boundedAge K m :=
  ⟨hD.1.reindex σ, (StageType.topGrade_reindex D σ).trans_le hD.2⟩

/-- The bottom one-point type: the one-point scheme with its labels at the bottom. -/
noncomputable def pointType (α : Ordinal.{u}) : StageType.{u} α 1 :=
  Scheme.isLegal_onePoint.toStageType α

/-- **The bottom one-point type lies in every bounded age**: it is legal and top-free. -/
theorem pointType_mem_boundedAge (K : ℕ) : pointType α ∈ boundedAge K 1 :=
  ⟨Scheme.isLegal_onePoint.isLegal_toStageType α,
    (StageType.topGrade_eq_zero_iff.mpr fun _ ↦ bot_ne_top).trans_le (Nat.zero_le K)⟩

/-- **Exact pinned extensions within the bounded age**: at a limit stage, for `P ∈ A_K`, a face
`f` of `P` with restriction `p`, and a legal coface `d ∈ A_K` of `p`, some one-point extension
`Q ∈ A_K` of `P` has the face `d` along `extendByLast f`, both faces literally
(`StageType.exists_pinned_extension_topGrade_le`). -/
theorem exists_pinned_extension_mem (hα : Order.IsSuccLimit α) {K : ℕ}
    {P : StageType.{u} α n} (hP : P ∈ boundedAge K n) {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)}
    (hPf : StageType.restrictFace f P = some p) (hd : d ∈ boundedAge K (m + 1))
    (hdp : StageType.restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q ∈ boundedAge K (n + 1) ∧
      StageType.restrictFace Fin.castSuccEmb Q = some P ∧
      StageType.restrictFace (extendByLast f) Q = some d := by
  obtain ⟨Q, hQ, hQP, hQd, hQK⟩ :=
    StageType.exists_pinned_extension_topGrade_le hα hP.1 hPf hd.1 hdp hP.2 hd.2
  exact ⟨Q, ⟨hQ, hQK⟩, hQP, hQd⟩

/-- **At most `ℵ₁` members of each arity** of a bounded age at stage `ω₁`. -/
theorem mk_boundedAge_le_aleph_one (K m : ℕ) :
    Cardinal.mk (boundedAge (α := (ω₁ : Ordinal.{u})) K m) ≤ Cardinal.aleph 1 :=
  (Cardinal.mk_subtype_le _).trans (StageType.mk_le_aleph_one_of_omega_one m)

/-! ### Witnesses of every top grade -/

/-- **The one-point apex type has top grade `1`**: its single cell has grade `1` and is labelled
`⊤`. -/
theorem topGrade_onePointApex : (StageType.onePointApex (α := α)).topGrade = 1 := by
  have h0 : 0 < (StageType.onePointApex (α := α)).card := by simp
  refine le_antisymm
    (StageType.topGrade_le_iff.mpr fun d _ ↦ (StageType.onePointApex_grade d).le) ?_
  have h := StageType.grade_le_topGrade (t := StageType.onePointApex (α := α)) (d := ⟨0, h0⟩)
    (StageType.onePointApex_label _)
  rwa [StageType.onePointApex_grade] at h

/-- **The one-point apex type lies in `A_K` exactly when `1 ≤ K`.** -/
theorem onePointApex_mem_boundedAge_iff {K : ℕ} :
    StageType.onePointApex (α := α) ∈ boundedAge K 1 ↔ 1 ≤ K := by
  rw [mem_boundedAge, topGrade_onePointApex]
  exact and_iff_right StageType.isLegal_onePointApex

/-- **Target: witnesses of every top grade.**  At a stage `α` that is zero or a limit, for every
`n ≥ 1` some legal stage type on `n` points has top grade exactly `n`.  Existence statement.
Proved (`ProcessRank.Bounded.topGradeWitnessTarget`). -/
def TopGradeWitnessTarget (α : Ordinal.{u}) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ t : StageType.{u} α n, t.IsLegal ∧ t.topGrade = n

/-- **The witness on `n + 2` points from the witness on `n + 1` points**: two copies of a legal
type `t` of top grade `n + 1` over their common face along the first `n` points have a common
legal extension with an apex of full grade `n + 2` dominating every label
(`StageType.HasApexCoatomExtensions`).  The apex dominates the inherited cell labelled `⊤`, so it
is labelled `⊤`; no grade exceeds the arity `n + 2`.  The face of the extension along the first
`n + 1` points is `t`. -/
theorem exists_topGrade_witness (hα : Order.IsSuccPrelimit α) (n : ℕ) :
    ∃ t : StageType.{u} α (n + 1), t.IsLegal ∧ t.topGrade = n + 1 ∧
      (StageType.restrictFace Fin.castSuccEmb t).isSome := by
  induction n with
  | zero =>
    exact ⟨StageType.onePointApex, StageType.isLegal_onePointApex, topGrade_onePointApex,
      StageType.isSome_restrictFace_of_zero _ _⟩
  | succ n ih =>
    obtain ⟨t, ht, htn, hps⟩ := ih
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hps
    obtain ⟨t', ht', hta, -, d, hd, hdmax⟩ :=
      StageType.hasApexCoatomExtensions hα n t t p ht ht hp hp
    have hnt : ¬ t.IsTopFree := fun h ↦ by
      have := StageType.topGrade_eq_zero_iff.mpr h
      omega
    obtain ⟨e, he⟩ : ∃ e, t.label e = ⊤ := not_forall_not.mp hnt
    have hdtop : t'.label d = ⊤ := by
      have h := hdmax (StageType.faceCell hta e)
      rwa [StageType.label_faceCell, he, top_le_iff] at h
    have hdg : t'.toCellScheme.grade d = n + 2 := congrArg Prod.snd hd
    have h₁ := StageType.grade_le_topGrade hdtop
    have h₂ : t'.topGrade ≤ n + 2 := StageType.topGrade_le_iff.mpr fun c _ ↦ t'.grade_le c
    exact ⟨t', ht', by omega, by simp [hta]⟩

/-- **Witnesses of every top grade**, at every stage that is zero or a limit
(`ProcessRank.Bounded.exists_topGrade_witness`). -/
theorem topGradeWitnessTarget (hα : Order.IsSuccPrelimit α) : TopGradeWitnessTarget α := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, ht, htk, -⟩ := exists_topGrade_witness hα k
  exact ⟨t, ht, htk⟩

/-- A legal type of top grade exactly `n` lies in `A_K` exactly when `n ≤ K`. -/
theorem mem_boundedAge_iff_of_topGrade_eq {K : ℕ} {t : StageType.{u} α m} (ht : t.IsLegal)
    (htn : t.topGrade = n) : t ∈ boundedAge K m ↔ n ≤ K := by
  rw [mem_boundedAge, htn]
  exact and_iff_right ht

end VaughtConjecture.ProcessRank.Bounded

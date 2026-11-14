/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Construction.DenseChain
import VaughtConjecture.Realization.Hull

/-!
# Exhaustive chains of occurrences and of charts

Two statements about realizations built from an increasing sequence of finite pieces.

**An exhaustive chain of occurrences.**  In a covering realization on a countable carrier, every
occurrence begins a monotone sequence of occurrences whose supports exhaust the carrier
(`Realization.ExistsExhaustiveOccurrenceChainTarget`): the sets of occurrences whose support
contains a given point are dense, by covering (`Realization.IsCovering.exists_subset_support`),
and countably many dense sets are met by a chain
(`VaughtConjecture.Construction.exists_monotone_forall_exists_mem`).

**The realization of an exhaustive chain of charts.**  Let `w k` be injective tuples of a type `X`
with stage types `T k`, each `w k` a face of `w (k + 1)` along a literal face map `g` whose
restriction of `T (k + 1)` is `T k`, and let every point of `X` occur in some `w k`.  Then some
exactly consistent covering realization on `X` gives each `w k` the type `T k`, and every type it
assigns is the restriction of some `T k` along the face map of the tuple in `w k`
(`Realization.ChartChainRealizationTarget`).  The intended evaluation of a tuple is the restriction
of `T k` for the first `k` whose chart contains the tuple; it does not depend on `k`, by
`StageType.restrictFace_trans` along the face maps.  Neither the carrier nor the stage is assumed
countable.

Both statements are proved (`Realization.existsExhaustiveOccurrenceChainTarget`,
`Realization.chartChainRealizationTarget`).

## Placement

This file belongs to Layer 0 of `roadmap/README.md` ("Countable construction and comparison"); it
is used by the exact countable attachment of the `ℵ₁` companion construction
(`VaughtConjecture.AlephOne.OptionAttachment`).
-/

universe u v

namespace VaughtConjecture.Realization

/-- **Target: an exhaustive chain of occurrences through a given occurrence.**  In a covering
realization on a countable carrier, every occurrence `x` begins a monotone sequence of occurrences
whose supports exhaust the carrier.  Proved
(`Realization.existsExhaustiveOccurrenceChainTarget`). -/
def ExistsExhaustiveOccurrenceChainTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M] (R : Realization.{u, v} α M), R.IsCovering →
    ∀ x : R.Occurrence, ∃ c : ℕ → R.Occurrence, c 0 = x ∧ Monotone c ∧
      ∀ a : M, ∃ k, a ∈ (c k).support

/-- **Target: the realization of an exhaustive chain of charts.**  Let `w k` be injective tuples
of a type `X` with stage types `T k`, each the face of the next along a literal face map `g`
(`g.trans (w (k + 1)) = w k`, and the restriction of `T (k + 1)` along `g` is `T k`), and let every
point of `X` occur in some `w k`.  Then some exactly consistent covering realization `S` on `X`
gives each `w k` the type `T k`, and every type `p` that `S` assigns to a tuple `t` is the
restriction of some `T k` along a face map `f` with `f.trans (w k) = t`.  No countability of `X`
or of the stage.  Proved (`Realization.chartChainRealizationTarget`). -/
def ChartChainRealizationTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ (N : ℕ → ℕ) (w : ∀ k, Fin (N k) ↪ X)
    (T : ∀ k, StageType.{u} α (N k)),
    (∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k)) →
    (∀ x : X, ∃ k, x ∈ Set.range (w k)) →
      ∃ S : Realization.{u, v} α X, S.IsConsistent ∧ S.IsCovering ∧
        (∀ k, S.eval (w k) = some (T k)) ∧
        ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X) (p : StageType.{u} α n), S.eval t = some p →
          ∃ (k : ℕ) (f : Fin n ↪ Fin (N k)), f.trans (w k) = t ∧
            StageType.restrictFace f (T k) = some p

/-- **An exhaustive chain of occurrences**, the target form: the sets of occurrences whose
support contains a point `a` are dense, since some occurrence contains the support of any
occurrence together with `a` (`Realization.IsCovering.exists_subset_support`), and countably many
dense sets are met by a chain (`Construction.exists_monotone_forall_exists_mem`). -/
theorem existsExhaustiveOccurrenceChainTarget : ExistsExhaustiveOccurrenceChainTarget.{u, v} := by
  intro α M _ R hc x
  classical
  exact Construction.exists_monotone_forall_exists_mem x
    (fun a : M ↦ {y : R.Occurrence | a ∈ y.support}) fun a y _ ↦ by
      obtain ⟨z, hz⟩ := hc.exists_subset_support (insert a y.support)
      exact ⟨z, hz (Finset.mem_insert_self _ _), fun b hb ↦ hz (Finset.mem_insert_of_mem hb)⟩

namespace ChartChain

variable {α : Ordinal.{u}} {X : Type v} {N : ℕ → ℕ} {w : ∀ k, Fin (N k) ↪ X}
  {T : ∀ k, StageType.{u} α (N k)}

/-- Along a chain of charts with literal face maps, every chart is a face of every later chart,
with the restricted type. -/
theorem exists_face_of_le
    (hg : ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k))
    {k l : ℕ} (hkl : k ≤ l) : ∃ G : Fin (N k) ↪ Fin (N l), G.trans (w l) = w k ∧
      StageType.restrictFace G (T l) = some (T k) := by
  induction l, hkl using Nat.le_induction with
  | base => exact ⟨Function.Embedding.refl _, rfl, StageType.restrictFace_refl _⟩
  | succ l _ ih =>
    obtain ⟨G, hGw, hGT⟩ := ih
    obtain ⟨g, hgw, hgT⟩ := hg l
    refine ⟨G.trans g, ?_, ?_⟩
    · rw [Function.Embedding.trans_assoc, hgw, hGw]
    · rw [← StageType.restrictFace_trans _ _ _ hgT, hGT]

/-- Faces of an injective tuple are determined by the tuple. -/
theorem eq_of_trans_eq {n m : ℕ} {u : Fin m ↪ X} {f f' : Fin n ↪ Fin m}
    (h : f.trans u = f'.trans u) : f = f' :=
  Function.Embedding.ext fun i ↦ u.injective (DFunLike.congr_fun h i)

open Classical in
/-- The evaluation of the chart chain: a tuple lying in some chart gets the restriction of the
type of the first chart containing it, along its face map in that chart. -/
noncomputable def eval (w : ∀ k, Fin (N k) ↪ X) (T : ∀ k, StageType.{u} α (N k)) {n : ℕ}
    (t : Fin n ↪ X) : Option (StageType.{u} α n) :=
  if h : ∃ k, ∃ f : Fin n ↪ Fin (N k), f.trans (w k) = t then
    StageType.restrictFace (Nat.find_spec h).choose (T (Nat.find h))
  else none

/-- The evaluation of a tuple inside a chart is the restriction of the type of that chart, for
every chart containing it. -/
theorem eval_eq
    (hg : ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k))
    {n k : ℕ} {f : Fin n ↪ Fin (N k)} {t : Fin n ↪ X} (hf : f.trans (w k) = t) :
    eval w T t = StageType.restrictFace f (T k) := by
  classical
  have h : ∃ k, ∃ f : Fin n ↪ Fin (N k), f.trans (w k) = t := ⟨k, f, hf⟩
  rw [eval, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨G, hGw, hGT⟩ := exists_face_of_le hg (Nat.find_min' h ⟨f, hf⟩)
  have hf₀ := (Nat.find_spec h).choose_spec
  have hfG : f = (Nat.find_spec h).choose.trans G :=
    eq_of_trans_eq (by rw [hf, Function.Embedding.trans_assoc, hGw, hf₀])
  rw [hfG]
  exact StageType.restrictFace_trans _ _ _ hGT

/-- Each chart has its type. -/
theorem eval_chart
    (hg : ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k)) (k : ℕ) :
    eval w T (w k) = some (T k) := by
  rw [eval_eq hg (k := k) (f := Function.Embedding.refl _) (t := w k) rfl,
    StageType.restrictFace_refl]

/-- Every tuple lies in some chart, when every point does. -/
theorem exists_trans_eq
    (hg : ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k))
    (hex : ∀ x : X, ∃ k, x ∈ Set.range (w k)) {n : ℕ} (t : Fin n ↪ X) :
    ∃ k, ∃ f : Fin n ↪ Fin (N k), f.trans (w k) = t := by
  choose K hK using hex
  refine ⟨Finset.univ.sup fun i ↦ K (t i), Function.Embedding.exists_trans_eq fun i ↦ ?_⟩
  obtain ⟨G, hGw, -⟩ := exists_face_of_le hg
    (Finset.le_sup (f := fun i ↦ K (t i)) (Finset.mem_univ i))
  obtain ⟨j, hj⟩ := hK (t i)
  exact ⟨G j, (DFunLike.congr_fun hGw j).trans hj⟩

end ChartChain

/-- **The realization of an exhaustive chain of charts**, the target form: the evaluation of a
tuple is the restriction of the type of a chart containing it (`ChartChain.eval`), which does not
depend on the chart (`ChartChain.eval_eq`, by `StageType.restrictFace_trans` along the face maps);
exact consistency is `StageType.restrictFace_trans` once more, and every tuple lies in a chart
(`ChartChain.exists_trans_eq`). -/
theorem chartChainRealizationTarget : ChartChainRealizationTarget.{u, v} := by
  intro α X N w T hg hex
  refine ⟨⟨fun t ↦ ChartChain.eval w T t⟩, ?_, ?_, fun k ↦ ?_, ?_⟩
  · intro m n t p f hp
    obtain ⟨k, F, hF⟩ := ChartChain.exists_trans_eq hg hex t
    change ChartChain.eval w T t = some p at hp
    rw [ChartChain.eval_eq hg hF] at hp
    change ChartChain.eval w T (f.trans t) = _
    rw [ChartChain.eval_eq hg (f := f.trans F) (by rw [Function.Embedding.trans_assoc, hF]),
      StageType.restrictFace_trans _ _ _ hp]
  · intro n t
    obtain ⟨k, f, hf⟩ := ChartChain.exists_trans_eq hg hex t
    refine ⟨N k, w k, f, hf, ?_⟩
    change (ChartChain.eval w T (w k)).isSome
    rw [ChartChain.eval_chart hg]
    rfl
  · exact ChartChain.eval_chart hg k
  · intro n t p hp
    obtain ⟨k, f, hf⟩ := ChartChain.exists_trans_eq hg hex t
    change ChartChain.eval w T t = some p at hp
    exact ⟨k, f, hf, (ChartChain.eval_eq hg hf).symm.trans hp⟩

end VaughtConjecture.Realization

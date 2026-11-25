/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Model

/-!
# Realizations that are locally models

Companion programme over the density sentence, process rank `ω₁`: the local step of the
reconstruction of receiving expansions (`VaughtConjecture.ProcessRank.Reconstruction`).

For a realization `R` on `M` and an embedding `g : N ↪ M`, the **pullback** `comapRealization R g`
evaluates a tuple of `N` by evaluating its image in `M`.  Every clause of a model, and the
finite-cut receiving property, concerns finitely many points at a time: a typed tuple, its faces,
and witnesses extending it.  So if every finite set of `M` lies in the image of some `g` along
which the pullback of `R` is a model (with finite-cut receiving), then `R` is a model (with
finite-cut receiving): the tuples of a clause are lifted to `N`, the clause is applied there, and
the witnesses are carried back along `g` (`realizesOver_of_comap`, `isModel_of_forall_comap`,
`hasFiniteCutReceiving_of_forall_comap`).  If moreover the pullbacks are expansions of
substructures of a base structure on `M`, then `R` is an expansion of it
(`toStructure_reduce_eq_of_forall_comap`).  Undefined evaluations are pulled back as they are:
the pullback evaluates a tuple to `none` exactly when `R` evaluates its image to `none`.

**Results.**  All proved.
-/

universe u v w

namespace VaughtConjecture.ProcessRank

open Finset FirstOrder Language Structure Realization

variable {α : Ordinal.{u}} {M : Type v} {N : Type w}

/-- The **pullback** of a realization along an embedding of carriers: a tuple of `N` is evaluated
as its image in `M`. -/
def comapRealization (R : Realization.{u, v} α M) (g : N ↪ M) : Realization.{u, w} α N where
  eval s := R.eval (s.trans g)

@[simp] theorem comapRealization_eval (R : Realization.{u, v} α M) (g : N ↪ M) {n : ℕ}
    (s : Fin n ↪ N) : (comapRealization R g).eval s = R.eval (s.trans g) :=
  rfl

/-- The pullback commutes with stage reduction. -/
theorem comapRealization_reduce (R : Realization.{u, v} α M) (g : N ↪ M) {β : Ordinal.{u}}
    (hβ : Order.IsSuccPrelimit β) :
    (comapRealization R g).reduce hβ = comapRealization (R.reduce hβ) g :=
  Realization.ext fun _ ↦ rfl

/-- A tuple of `M` with points in the image of `g` is the image of a tuple of `N`. -/
theorem exists_trans_eq_of_forall_mem_range (g : N ↪ M) {n : ℕ} (t : Fin n ↪ M)
    (ht : ∀ i, t i ∈ Set.range g) : ∃ t' : Fin n ↪ N, t'.trans g = t := by
  choose t' ht' using ht
  exact ⟨⟨t', fun i j hij ↦ t.injective (by rw [← ht' i, ← ht' j, hij])⟩,
    Function.Embedding.ext ht'⟩

/-- The points of a tuple of `M` lie in any set containing its image. -/
theorem forall_mem_range_of_subset {g : N ↪ M} {n : ℕ} (t : Fin n ↪ M)
    (h : (↑(univ.map t) : Set M) ⊆ Set.range g) : ∀ i, t i ∈ Set.range g :=
  fun i ↦ h (Finset.mem_coe.2 (Finset.mem_map_of_mem t (Finset.mem_univ i)))

variable {R : Realization.{u, v} α M}

/-- **Witnesses are carried back along `g`**: realizing a member of a family over a tuple of `N`
in the pullback realizes it over the image tuple in `R`. -/
theorem realizesOver_of_comap {g : N ↪ M} {n : ℕ} {t' : Fin n ↪ N}
    {U : Set (StageType.{u} α (n + 1))} (h : (comapRealization R g).RealizesOver t' U) :
    R.RealizesOver (t'.trans g) U := by
  obtain ⟨u, hu, q, hq, he⟩ := h
  exact ⟨u.trans g, by rw [← hu]; rfl, q, hq, he⟩

/-- An occurrence of `R` whose tuple is the image of a tuple `t'` of `N` is an occurrence of the
pullback. -/
def occurrenceOfComap (g : N ↪ M) (x : R.Occurrence) (t' : Fin x.arity ↪ N)
    (ht' : t'.trans g = x.tuple) : (comapRealization R g).Occurrence where
  arity := x.arity
  tuple := t'
  type := x.type
  eval_tuple := by rw [comapRealization_eval, ht']; exact x.eval_tuple

/-- **Lifting an occurrence**: an occurrence of `R` lies, through an image of `g` containing its
points, over an occurrence of the pullback with the same type. -/
theorem exists_occurrenceOfComap (g : N ↪ M) (x : R.Occurrence)
    (h : (↑(univ.map x.tuple) : Set M) ⊆ Set.range g) :
    ∃ x' : (comapRealization R g).Occurrence, ∃ hx : x'.arity = x.arity,
      x'.tuple.trans g = hx ▸ x.tuple ∧ x'.type = hx ▸ x.type := by
  obtain ⟨t', ht'⟩ := exists_trans_eq_of_forall_mem_range g x.tuple
    (forall_mem_range_of_subset x.tuple h)
  exact ⟨occurrenceOfComap g x t' ht', rfl, ht', rfl⟩

/-- **A realization that is locally a model is a model**: if every finite set of `M` lies in
the image of an embedding along which the pullback of `R` is a model, then `R` is a model. -/
theorem isModel_of_forall_comap
    (h : ∀ X : Finset M, ∃ (N : Type v) (g : N ↪ M), (↑X : Set M) ⊆ Set.range g ∧
      (comapRealization R g).IsModel) : R.IsModel := by
  -- the clauses over an occurrence, through its lift
  have hocc : ∀ (x : R.Occurrence), ∃ (N : Type v) (g : N ↪ M) (t' : Fin x.arity ↪ N)
      (ht' : t'.trans g = x.tuple), (comapRealization R g).IsModel ∧
        (occurrenceOfComap g x t' ht').type = x.type := fun x ↦ by
    obtain ⟨N, g, hX, hN⟩ := h (univ.map x.tuple)
    obtain ⟨t', ht'⟩ := exists_trans_eq_of_forall_mem_range g x.tuple
      (forall_mem_range_of_subset x.tuple hX)
    exact ⟨N, g, t', ht', hN, rfl⟩
  refine ⟨?_, fun n t p hp ↦ ?_, fun m n t p f hp ↦ ?_, fun n t ↦ ?_, fun x S hne ↦ ?_,
    fun x S ρ hne ↦ ?_, fun x γ hγ hγα ↦ ?_, fun x γ hγα ↦ ?_⟩
  · obtain ⟨N, g, -, hN⟩ := h ∅
    obtain ⟨y⟩ := hN.nonempty
    exact ⟨g y⟩
  · obtain ⟨N, g, hX, hN⟩ := h (univ.map t)
    obtain ⟨t', rfl⟩ := exists_trans_eq_of_forall_mem_range g t (forall_mem_range_of_subset t hX)
    exact hN.isLegal t' p hp
  · obtain ⟨N, g, hX, hN⟩ := h (univ.map t)
    obtain ⟨t', rfl⟩ := exists_trans_eq_of_forall_mem_range g t (forall_mem_range_of_subset t hX)
    exact hN.isConsistent t' p f hp
  · obtain ⟨N, g, hX, hN⟩ := h (univ.map t)
    obtain ⟨t', rfl⟩ := exists_trans_eq_of_forall_mem_range g t (forall_mem_range_of_subset t hX)
    obtain ⟨m, u, f, hf, hu⟩ := hN.isCovering t'
    exact ⟨m, u.trans g, f, by rw [← hf]; rfl, hu⟩
  · obtain ⟨N, g, t', ht', hN, -⟩ := hocc x
    rw [← ht']
    exact realizesOver_of_comap (hN.saturation (occurrenceOfComap g x t' ht') S hne)
  · obtain ⟨N, g, t', ht', hN, -⟩ := hocc x
    rw [← ht']
    exact realizesOver_of_comap (hN.bottomPattern (occurrenceOfComap g x t' ht') S ρ hne)
  · obtain ⟨N, g, t', ht', hN, -⟩ := hocc x
    rw [← ht']
    exact realizesOver_of_comap (hN.uniformity (occurrenceOfComap g x t' ht') γ hγ hγα)
  · obtain ⟨N, g, t', ht', hN, -⟩ := hocc x
    rw [← ht']
    exact realizesOver_of_comap (hN.dominance (occurrenceOfComap g x t' ht') γ hγα)

/-- **A realization with finite-cut receiving locally has finite-cut receiving**: if every finite
set of `M` lies in the image of an embedding along which the pullback of `R` has finite-cut
receiving, then so does `R`. -/
theorem hasFiniteCutReceiving_of_forall_comap
    (h : ∀ X : Finset M, ∃ (N : Type v) (g : N ↪ M), (↑X : Set M) ⊆ Set.range g ∧
      (comapRealization R g).HasFiniteCutReceiving) : R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨N, g, hX, hN⟩ := h (univ.map x.tuple)
  obtain ⟨t', ht'⟩ := exists_trans_eq_of_forall_mem_range g x.tuple
    (forall_mem_range_of_subset x.tuple hX)
  rw [← ht']
  exact realizesOver_of_comap (hN (occurrenceOfComap g x t' ht') d hd c hc)

/-- **A realization that is locally an expansion is an expansion**: for a base structure on `M`,
if every finite set of `M` lies in the image of an embedding of base structures `g : N ↪ M` along
which the pullback of `R` is an expansion of `N` (a model whose reduction to `ω` has the structure
of `N`), then the reduction of `R` to `ω` has the structure of `M`.  A relation holds of a tuple
of `M` exactly when it holds of its lift to `N`, since `g` is an embedding of structures. -/
theorem toStructure_reduce_eq_of_forall_comap [baseLanguage.{u}.Structure M]
    (h : ∀ X : Finset M, ∃ (N : Type v) (_ : baseLanguage.{u}.Structure N)
      (g : N ↪[baseLanguage.{u}] M), (↑X : Set M) ⊆ Set.range g ∧
      ∃ e : ModelExpansion N α, e.1 = comapRealization R g.toEmbedding) :
    (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure = ‹_› := by
  classical
  refine baseLanguage.structure_ext fun n p xs ↦ ?_
  obtain ⟨N, _, g, hX, e, he⟩ := h (univ.image xs)
  have hxs : ∀ i, xs i ∈ Set.range g := fun i ↦
    hX (Finset.mem_coe.2 (Finset.mem_image_of_mem xs (Finset.mem_univ i)))
  choose xs' hxs' using hxs
  have hcomp : ⇑g ∘ xs' = xs := funext hxs'
  have hinj : Function.Injective xs ↔ Function.Injective xs' := by
    rw [← hcomp]
    exact ⟨fun h ↦ h.of_comp, fun h ↦ g.injective.comp h⟩
  have hrel : RelMap p xs ↔ RelMap p xs' := by
    rw [← hcomp]
    exact g.map_rel p xs'
  rw [hrel, relMap_toStructure, ← e.2.toStructure_reduce, relMap_toStructure, he,
    comapRealization_reduce]
  refine ⟨fun ⟨hi, hev⟩ ↦ ⟨hinj.1 hi, ?_⟩, fun ⟨hi, hev⟩ ↦ ⟨hinj.2 hi, ?_⟩⟩
  · rwa [comapRealization_eval, show ((⟨xs', hinj.1 hi⟩ : Fin n ↪ N).trans g.toEmbedding) =
      ⟨xs, hi⟩ from Function.Embedding.ext hxs']
  · rwa [comapRealization_eval, show ((⟨xs', hi⟩ : Fin n ↪ N).trans g.toEmbedding) =
      ⟨xs, hinj.2 hi⟩ from Function.Embedding.ext hxs'] at hev

end VaughtConjecture.ProcessRank

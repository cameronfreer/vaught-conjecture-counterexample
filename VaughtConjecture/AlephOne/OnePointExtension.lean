/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Construction
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Realization.Pushforward

/-!
# The one-point extension of a condition

A condition of countable domain extends by one point, the least point outside its domain
(`AlephOne.onePointExtensionTarget`); a condition whose domain is not the whole carrier does too
(`AlephOne.Condition.exists_onePointExtension_of_ne_univ`).

**The proof.**  Let `x` be the least point outside the domain, so that the domain is `Set.Iio x`.
The realization on the domain (`AlephOne.Condition.restrict`) is exactly consistent and covering
with legal top-free types, on a countable carrier.  If the request scheduled at `x` is eligible
(its tuple lies below `x`, has a type `p`, and its donor is a top-free coface of `p`), the exact
one-point attachment (`Realization.optionAttachmentTarget`) attaches a new point realizing the
donor over the tuple; otherwise it attaches a new point with the bottom one-point type over the
empty tuple.  The realization on `Option dom` is pushed forward along the embedding of
`Option dom` onto `insert x dom` sending the new point to `x`
(`AlephOne.Condition.optionEmbedding`, `Realization.pushforward`).  Every old evaluation, `none`
included, is kept (`AlephOne.Condition.pushforward_eval_of_range_subset`), so the old services are
kept, and the request scheduled at `x` is served.

## Placement

This file is Stage 3 (one model of cardinality `ℵ₁`) of the `ℵ₁` companion construction over the
density sentence; that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

namespace VaughtConjecture.AlephOne

open Ordinal Set Realization

/-- **Service depends only on two evaluations**: the tuple of the request and the tuple followed
by the point. -/
theorem ServesAt.of_eval_eq {R R' : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier} {r : Request}
    {γ : Carrier} (hR : ServesAt R r γ)
    (h₁ : (∀ i, r.tuple i < γ) → R'.eval r.tuple = R.eval r.tuple)
    (h₂ : ∀ h : ∀ i, r.tuple i < γ, R'.eval (r.extendAt h) = R.eval (r.extendAt h)) :
    ServesAt R' r γ :=
  fun h p hp hd hdt ↦ (h₂ h).trans (hR h p ((h₁ h).symm.trans hp) hd hdt)

namespace Condition

variable {s : Carrier → Request}

/-- The embedding of `Option dom` into the carrier sending the old points to themselves and the
new point to a point `x` outside the domain. -/
def optionEmbedding (c : Condition s) {x : Carrier} (hx : x ∉ c.dom) : Option c.dom ↪ Carrier :=
  ⟨fun o ↦ o.elim x Subtype.val, by
    rintro (_ | a) (_ | b) h
    · rfl
    · have h : x = b := h
      exact absurd (h ▸ b.2) hx
    · have h : (a : Carrier) = x := h
      exact absurd (h ▸ a.2) hx
    · exact congrArg some (Subtype.ext h)⟩

@[simp] theorem optionEmbedding_none (c : Condition s) {x : Carrier} (hx : x ∉ c.dom) :
    c.optionEmbedding hx none = x :=
  rfl

@[simp] theorem optionEmbedding_some (c : Condition s) {x : Carrier} (hx : x ∉ c.dom)
    (a : c.dom) : c.optionEmbedding hx (some a) = a :=
  rfl

/-- The range of the embedding is the domain with the point `x`. -/
theorem mem_range_optionEmbedding (c : Condition s) {x : Carrier} (hx : x ∉ c.dom) {y : Carrier} :
    y ∈ range (c.optionEmbedding hx) ↔ y ∈ insert x c.dom := by
  constructor
  · rintro ⟨_ | a, rfl⟩
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ a.2
  · rintro (rfl | hy)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨y, hy⟩, rfl⟩

/-- **Old evaluations are kept**: a realization on `Option dom` that gives every tuple of old
points its evaluation on the domain, pushed forward along the embedding, gives every tuple inside
the domain its evaluation in the condition, `none` included. -/
theorem pushforward_eval_of_range_subset (c : Condition s) {x : Carrier} (hx : x ∉ c.dom)
    {S : Realization.{0, 0} (ω₁ : Ordinal.{0}) (Option c.dom)}
    (hS : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ c.dom),
      S.eval (t.trans Function.Embedding.some) = c.restrict.eval t)
    {n : ℕ} {t : Fin n ↪ Carrier} (ht : range t ⊆ c.dom) :
    (S.pushforward (c.optionEmbedding hx)).eval t = c.real.eval t := by
  have key : ((t.codRestrict c.dom fun i ↦ ht ⟨i, rfl⟩).trans Function.Embedding.some).trans
      (c.optionEmbedding hx) = t := rfl
  conv_lhs => rw [← key]
  rw [pushforward_eval_trans, hS]
  rfl

/-- **Extension by an attachment**: a realization on `Option dom` with the structural laws that
keeps every old evaluation and whose pushforward serves the request scheduled at the least point
`x` outside the domain gives a condition extending `c` with domain `insert x dom`. -/
theorem exists_le_of_attachment (c : Condition s) {x : Carrier} (hx : x ∉ c.dom)
    (hmin : ∀ y, y < x → y ∈ c.dom) {S : Realization.{0, 0} (ω₁ : Ordinal.{0}) (Option c.dom)}
    (hSc : S.IsConsistent) (hScov : S.IsCovering) (hSl : S.HasLegalTypes)
    (hSt : S.HasTopFreeTypes)
    (hS : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ c.dom),
      S.eval (t.trans Function.Embedding.some) = c.restrict.eval t)
    (hserve : ServesAt (S.pushforward (c.optionEmbedding hx)) (s x) x) :
    ∃ c' : Condition s, c ≤ c' ∧ c'.dom = insert x c.dom := by
  refine ⟨{
    dom := insert x c.dom
    isLowerSet_dom := fun a b hba hb ↦ by
      rcases hb with rfl | hb
      · rcases hba.lt_or_eq with h | rfl
        · exact mem_insert_of_mem _ (hmin _ h)
        · exact mem_insert _ _
      · exact mem_insert_of_mem _ (c.isLowerSet_dom hba hb)
    real := S.pushforward (c.optionEmbedding hx)
    eval_eq_none := fun n t ht ↦ pushforward_eval_of_not_forall S fun h ↦
      ht (by rintro _ ⟨i, rfl⟩; exact (c.mem_range_optionEmbedding hx).mp (h i))
    isConsistent := hSc.pushforward
    isCovering := fun n t ht ↦
      hScov.pushforward fun i ↦ (c.mem_range_optionEmbedding hx).mpr (ht ⟨i, rfl⟩)
    hasLegalTypes := hSl.pushforward
    hasTopFreeTypes := fun n t p ht ↦ by
      obtain ⟨u, -, hu⟩ := exists_of_pushforward_eval_eq_some ht
      exact hSt u p hu
    serves := fun γ hγ ↦ by
      rcases hγ with rfl | hγ
      · exact hserve
      · exact (c.serves γ hγ).of_eval_eq
          (fun h ↦ c.pushforward_eval_of_range_subset hx hS (c.range_tuple_subset _ hγ h))
          (fun h ↦ c.pushforward_eval_of_range_subset hx hS (c.range_extendAt_subset _ hγ h)) },
    ⟨subset_insert _ _, fun _ _ ht ↦ c.pushforward_eval_of_range_subset hx hS ht⟩, rfl⟩

/-- The bottom one-point stage type at `ω₁`: legal and top-free. -/
noncomputable def pointType : StageType.{0} (ω₁ : Ordinal.{0}) 1 :=
  Scheme.isLegal_onePoint.toStageType _

theorem isLegal_pointType : pointType.IsLegal :=
  Scheme.isLegal_onePoint.isLegal_toStageType _

theorem isTopFree_pointType : pointType.IsTopFree :=
  fun _ ↦ bot_ne_top

/-- The empty tuple of the domain is typed in the realization on the domain. -/
theorem exists_eval_restrict_ofIsEmpty (c : Condition s) :
    ∃ p, c.restrict.eval (Function.Embedding.ofIsEmpty : Fin 0 ↪ c.dom) = some p := by
  obtain ⟨m, u, f, hfu, hu⟩ :=
    c.isCovering_restrict (Function.Embedding.ofIsEmpty : Fin 0 ↪ c.dom)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hu
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (q.isSome_restrictFace_of_zero f)
  exact ⟨p, by rw [← hfu, c.isConsistent_restrict u q f hq, hp]⟩

end Condition

/-- **The one-point extension**, the target form: the least point `x` outside the countable domain
is attached by `Realization.optionAttachmentTarget`, realizing the donor of the request scheduled
at `x` when that request is eligible, and the bottom one-point type over the empty tuple
otherwise. -/
theorem onePointExtensionTarget : OnePointExtensionTarget := by
  intro s c hcount
  have hne : c.domᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    have : Countable Carrier := countable_univ_iff.mp (h ▸ hcount)
    have h₁ := Cardinal.mk_le_aleph0_iff.mpr this
    rw [mk_carrier] at h₁
    exact absurd h₁ (not_le.mpr Cardinal.aleph0_lt_aleph_one)
  obtain ⟨x, hx, hxmin⟩ := wellFounded_lt.has_min _ hne
  have hmin : ∀ y, y < x → y ∈ c.dom := fun y hy ↦ by_contra fun h ↦ hxmin y h hy
  have : Countable c.dom := hcount.to_subtype
  have hα := Cardinal.isSuccLimit_omega 1
  by_cases hE : ∃ (h : ∀ i, (s x).tuple i < x) (p : StageType.{0} (ω₁ : Ordinal.{0}) (s x).arity),
      c.real.eval (s x).tuple = some p ∧ (s x).donor ∈ p.cofaces ∧ (s x).donor.IsTopFree
  · obtain ⟨h, p, hp, hd, hdt⟩ := hE
    let y : c.restrict.Occurrence :=
      ⟨(s x).arity, (s x).tuple.codRestrict c.dom fun i ↦ hmin _ (h i), p, hp⟩
    obtain ⟨S, hSc, hScov, hSl, hSt, hS, hSd⟩ := optionAttachmentTarget hα c.restrict
      c.isConsistent_restrict c.isCovering_restrict c.hasLegalTypes_restrict
      c.hasTopFreeTypes_restrict y (s x).donor hd hdt
    obtain ⟨c', hle, hdom⟩ := c.exists_le_of_attachment hx hmin hSc hScov hSl hSt hS
      fun h' _ _ _ _ ↦ by
        have he : (s x).extendAt h' = (appendNone y.tuple).trans (c.optionEmbedding hx) :=
          Function.Embedding.ext fun i ↦ by
            induction i using Fin.lastCases with
            | last =>
              change _ = c.optionEmbedding hx (appendNone y.tuple (Fin.last y.arity))
              simp [Request.extendAt]
            | cast i => simp [Request.extendAt, y]
        rw [he, pushforward_eval_trans, hSd]
    exact ⟨c', hle, x, hx, hdom⟩
  · obtain ⟨p, hp⟩ := c.exists_eval_restrict_ofIsEmpty
    let y : c.restrict.Occurrence := ⟨0, Function.Embedding.ofIsEmpty, p, hp⟩
    obtain ⟨S, hSc, hScov, hSl, hSt, hS, -⟩ := optionAttachmentTarget hα c.restrict
      c.isConsistent_restrict c.isCovering_restrict c.hasLegalTypes_restrict
      c.hasTopFreeTypes_restrict y Condition.pointType
      (StageType.mem_cofaces_of_zero Condition.isLegal_pointType) Condition.isTopFree_pointType
    obtain ⟨c', hle, hdom⟩ := c.exists_le_of_attachment hx hmin hSc hScov hSl hSt hS
      fun h' p' hp' hd' hdt' ↦ by
        refine absurd ⟨h', p', ?_, hd', hdt'⟩ hE
        have hsub : range (s x).tuple ⊆ c.dom := by
          rintro _ ⟨i, rfl⟩
          exact hmin _ (h' i)
        rwa [c.pushforward_eval_of_range_subset hx hS hsub] at hp'
    exact ⟨c', hle, x, hx, hdom⟩

/-- **The one-point extension of a condition of proper domain**: a proper lower set of the carrier
is countable (`AlephOne.countable_of_isLowerSet_ne_univ`). -/
theorem Condition.exists_onePointExtension_of_ne_univ {s : Carrier → Request} (c : Condition s)
    (h : c.dom ≠ Set.univ) : ∃ c' : Condition s, c ≤ c' ∧ ∃ x ∉ c.dom, c'.dom = insert x c.dom :=
  onePointExtensionTarget s c (countable_of_isLowerSet_ne_univ c.isLowerSet_dom h)

end VaughtConjecture.AlephOne

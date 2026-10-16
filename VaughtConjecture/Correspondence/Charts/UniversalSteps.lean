/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.UniversalModel
import VaughtConjecture.Correspondence.Presentation.Alignment
import VaughtConjecture.Extension.StronglyCodedForcingDonors

/-!
# The universal chart model: the finite steps of the construction

Native construction throughout.  The statements are in
`VaughtConjecture.Correspondence.Charts.UniversalModel`; this file proves the finite steps, before
the scheduling and the limit (`UniversalChainLimitTarget`, not treated here).

**Persistence along extensions** (`UniversalCondition.Extends`).  Extension is reflexive and
transitive (`Extends.refl`, `Extends.trans`), and keeps the points of the old tuple
(`Extends.range_subset`).  **Face evaluations persist, including the value `none`**
(`Extends.restrictFace_eq`): if a tuple `t` is the face of the tuple of `c` along `h` and of the
tuple of `d` along `h'`, then the face of the type of `d` along `h'` is the face of the type of `c`
along `h`, as an `Option`; in particular a face undefined in `c` stays undefined in `d`
(`Extends.restrictFace_eq_none`).  Hence a task done at `c` stays done at every extension
(`ExactTaskDone.mono`), including a task done vacuously because its root face is undefined.

**Receiving.**  Exact receiving of the strongly coded legal donors gives finite-cut receiving of
the cofaces with strongly coded rows
(`Realization.ExactReceivingWithin.hasFiniteCutReceivingIn_isStronglyCoded`): over an occurrence,
a coface with strongly coded rows is legal (a coface is), hence a strongly coded legal donor
along `Fin.castSuccEmb`; exact receiving realizes the donor itself, which lies in each of its
receiving families (`StageType.self_mem_receivingFamily`).  Only strongly coded donors are used;
the implication for all legal donors (`Realization.ExactReceivingWithin.hasFiniteCutReceiving`)
is not.

**The steps.**

* **Fresh placement** (`freshPlacementTarget`): on an infinite carrier, an injective tuple `W` on
  `N` points extends along any `i : Fin N ↪ Fin N'` to an injective tuple `U` on `N'` points with
  `i ; U = W`; the places outside the range of `i` go to points outside the range of `W`.
* **One point** (`UniversalCondition.exists_extends_snoc`): a point `a` outside the tuple of a
  condition is added last.  The type is the exact pinned extension
  (`StageType.exists_stronglyCoded_pinned_extension`) of the type `w` of the condition over its
  face on **no points** (the empty root: the face of `w` along the empty embedding is defined,
  `StageType.isSome_restrictFace_of_zero`), with a strongly coded legal one-point type
  (`StageType.exists_stronglyCodedLegal_onePoint`), whose face on no points is the same stage type
  on no points (`StageType.eq_of_zero`).  The old type is the face along `Fin.castSuccEmb`.
* **The point step** (`universalPointStepTarget`): finitely many points, one at a time.
* **The exact task step** (`universalTaskStepTarget`): a point step for the points of the root
  `t`; if the face `p` of the type `w` along the position `h` of `t` is defined, the donor `D` is
  strongly coded legal and its face along `g` is `p`, the strongly coded amalgam
  (`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit`) gives `Q` with faces `w` along `i`
  and `D` along `j`, and `h ; i = g ; j`; fresh placement along `i` gives the new tuple.  Only the
  places of `Q` outside the range of `i` are new: they go to fresh points.  No disjointness of the
  donor from the old condition outside the root is claimed: a place of `D` outside the root may be
  sent by `j` into the range of `i`, i.e. onto an old point, if the amalgam identifies it so.  The
  donor is realized exactly: the face of `Q` along `j` is `D` itself, and the root is kept
  literally.  Otherwise the task is done vacuously at the condition after the point step.
-/

universe u v

namespace VaughtConjecture

open Finset StageType

noncomputable section

/-! ### Persistence along extensions -/

namespace UniversalCondition

variable {α : Ordinal.{u}} {M : Type v}

/-- Extension is reflexive.  Native construction. -/
theorem Extends.refl (c : UniversalCondition.{u, v} α M) : c.Extends c :=
  ⟨Function.Embedding.refl _, rfl, restrictFace_refl c.w⟩

/-- Extension is transitive.  Native construction. -/
theorem Extends.trans {c d d' : UniversalCondition.{u, v} α M} (hcd : c.Extends d)
    (hdd' : d.Extends d') : c.Extends d' := by
  obtain ⟨e, he, hew⟩ := hcd
  obtain ⟨e', he', hew'⟩ := hdd'
  refine ⟨e.trans e', ?_, ?_⟩
  · rw [← he, ← he']
    rfl
  · rw [← restrictFace_trans d'.w e' e hew', hew]

/-- Along an extension, the points of the old tuple are points of the new one.
Native construction. -/
theorem Extends.range_subset {c d : UniversalCondition.{u, v} α M} (h : c.Extends d) :
    Set.range c.W ⊆ Set.range d.W := by
  obtain ⟨e, he, -⟩ := h
  rintro _ ⟨j, rfl⟩
  exact ⟨e j, by rw [← he]; rfl⟩

/-- **Face evaluations persist along an extension, as `Option`s**: a tuple that is the face of
the tuples of `c` and of `d` along `h` and `h'` has the same face of the two types, defined or
not.  Native construction. -/
theorem Extends.restrictFace_eq {c d : UniversalCondition.{u, v} α M} (hcd : c.Extends d)
    {k : ℕ} {t : Fin k ↪ M} {h : Fin k ↪ Fin c.N} {h' : Fin k ↪ Fin d.N}
    (hh : h.trans c.W = t) (hh' : h'.trans d.W = t) :
    restrictFace h' d.w = restrictFace h c.w := by
  obtain ⟨e, he, hew⟩ := hcd
  have : h' = h.trans e := Function.Embedding.ext fun j ↦ d.W.injective <| by
    have h1 := DFunLike.congr_fun hh' j
    have h2 := DFunLike.congr_fun hh j
    have h3 := DFunLike.congr_fun he (h j)
    simp only [Function.Embedding.trans_apply] at h1 h2 h3 ⊢
    rw [h1, ← h2, ← h3]
  rw [this, ← restrictFace_trans d.w e h hew]

/-- **An undefined face stays undefined along an extension.**  Native construction. -/
theorem Extends.restrictFace_eq_none {c d : UniversalCondition.{u, v} α M} (hcd : c.Extends d)
    {k : ℕ} {t : Fin k ↪ M} {h : Fin k ↪ Fin c.N} {h' : Fin k ↪ Fin d.N}
    (hh : h.trans c.W = t) (hh' : h'.trans d.W = t) (hnone : restrictFace h c.w = none) :
    restrictFace h' d.w = none :=
  (hcd.restrictFace_eq hh hh').trans hnone

/-- **A task done at a condition stays done at every extension**, including a task done
vacuously because its root face is undefined.  Native construction. -/
theorem ExactTaskDone.mono {c d : UniversalCondition.{u, v} α M} (hcd : c.Extends d) {k m : ℕ}
    {t : Fin k ↪ M} {D : StageType.{u} α m} {g : Fin k ↪ Fin m}
    (hdone : c.ExactTaskDone t D g) : d.ExactTaskDone t D g := by
  obtain ⟨e, he, hew⟩ := hcd
  obtain ⟨h₀, hh₀, hd⟩ := hdone
  refine ⟨h₀.trans e, ?_, fun p hp hD hg ↦ ?_⟩
  · rw [← hh₀, ← he]
    rfl
  · rw [← restrictFace_trans d.w e h₀ hew] at hp
    obtain ⟨i, hi, hiD⟩ := hd p hp hD hg
    refine ⟨i.trans e, ?_, ?_⟩
    · rw [← hi, ← he]
      rfl
    · rw [← restrictFace_trans d.w e i hew, hiD]

end UniversalCondition

/-! ### Exact receiving gives finite-cut receiving, for strongly coded donors -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Exact receiving of the strongly coded legal donors gives finite-cut receiving of the cofaces
with strongly coded rows**: a coface with strongly coded rows is a strongly coded legal donor
along `Fin.castSuccEmb`; the received type is the donor itself, which is in each of its receiving
families (`StageType.self_mem_receivingFamily`).  Native construction. -/
theorem ExactReceivingWithin.hasFiniteCutReceivingIn_isStronglyCoded
    (h : R.ExactReceivingWithin fun m ↦ {D : StageType.{u} α m | D.IsStronglyCodedLegal}) :
    R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded := by
  intro x d hd hds c _
  obtain ⟨u, hu, hug⟩ := h x.type x.tuple (covers_of_eval _ x.eval_tuple) d Fin.castSuccEmb
    (show d.IsLegal ∧ d.rows.IsStronglyCoded from ⟨hd.1, hds⟩) hd.2
  exact ⟨⟨u, hu.injective⟩, Function.Embedding.ext (congrFun hug), d,
    StageType.self_mem_receivingFamily d c, hu.eval_eq⟩

end Realization

/-! ### Fresh placement -/

/-- **Fresh placement holds** (`FreshPlacementTarget M`): on an infinite carrier, the places
outside the range of `i` are sent injectively to points outside the range of `W`.
Native construction. -/
theorem freshPlacementTarget (M : Type v) : FreshPlacementTarget M := by
  intro hM N N' i W
  classical
  have := hM
  have : Infinite ↥(Set.range W)ᶜ := (Set.finite_range W).infinite_compl.to_subtype
  let f : {j : Fin N' // j ∉ Set.range i} ↪ ↥(Set.range W)ᶜ :=
    (Fintype.equivFin _).toEmbedding.trans (Fin.valEmbedding.trans (Infinite.natEmbedding _))
  let U : Fin N' → M := fun j ↦ if h : j ∈ Set.range i then W h.choose else (f ⟨j, h⟩ : M)
  have hU (a : Fin N) : U (i a) = W a := by
    have h : i a ∈ Set.range i := ⟨a, rfl⟩
    rw [show U (i a) = W h.choose from dite_eq_left h]
    exact congrArg W (i.injective h.choose_spec)
  have hUn {j : Fin N'} (hj : j ∉ Set.range i) : U j = (f ⟨j, hj⟩ : M) := dite_eq_right hj
  have hUinj : Function.Injective U := by
    intro j j' hjj'
    by_cases hj : j ∈ Set.range i <;> by_cases hj' : j' ∈ Set.range i
    · obtain ⟨a, rfl⟩ := hj
      obtain ⟨a', rfl⟩ := hj'
      rw [hU, hU] at hjj'
      rw [W.injective hjj']
    · obtain ⟨a, rfl⟩ := hj
      rw [hU, hUn hj'] at hjj'
      exact ((f ⟨j', hj'⟩).2 ⟨a, hjj'⟩).elim
    · obtain ⟨a', rfl⟩ := hj'
      rw [hU, hUn hj] at hjj'
      exact ((f ⟨j, hj⟩).2 ⟨a', hjj'.symm⟩).elim
    · rw [hUn hj, hUn hj'] at hjj'
      exact congrArg Subtype.val (f.injective (Subtype.ext hjj'))
  exact ⟨⟨U, hUinj⟩, Function.Embedding.ext hU⟩

/-! ### The point step -/

namespace UniversalCondition

variable {α : Ordinal.{u}} {M : Type v}

/-- **Adding one point** (native construction): at a stage that is zero or a limit, a point `a`
outside the tuple of a condition is added last, with the exact pinned extension of the type over
its face on no points (the empty root) by a strongly coded legal one-point type. -/
theorem exists_extends_snoc (hα : Order.IsSuccPrelimit α) (c : UniversalCondition.{u, v} α M)
    {a : M} (ha : a ∉ Set.range c.W) :
    ∃ d : UniversalCondition.{u, v} α M, c.Extends d ∧ a ∈ Set.range d.W := by
  -- the empty root: the face of the type of `c` on no points
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (c.w.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin c.N))
  -- a strongly coded legal one-point type, whose face on no points is the same
  obtain ⟨d₀, hd₀⟩ := exists_stronglyCodedLegal_onePoint (α := α)
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp
    (d₀.isSome_restrictFace_of_zero (Fin.castSuccEmb : Fin 0 ↪ Fin 1))
  have hd₀p : restrictFace Fin.castSuccEmb d₀ = some p :=
    hp₀.trans (congrArg some (eq_of_zero p₀ p))
  obtain ⟨Q, hQ, hQw, -⟩ := exists_stronglyCoded_pinned_extension
    (hasStronglyCodedApexCoatomExtensions hα) c.isStronglyCodedLegal hp hd₀ hd₀p
  let W' : Fin (c.N + 1) ↪ M :=
    ⟨Fin.snoc (fun j ↦ c.W j) a, Fin.snoc_injective_of_injective c.W.injective ha⟩
  refine ⟨⟨c.N + 1, W', Q, hQ⟩, ⟨Fin.castSuccEmb, Function.Embedding.ext fun j ↦ ?_, hQw⟩,
    ⟨Fin.last _, ?_⟩⟩
  · simp [W']
  · simp [W']

end UniversalCondition

section Steps

variable (α : Ordinal.{u}) (M : Type v)

/-- **The point step holds** (`UniversalPointStepTarget α M`): finitely many points are added one
at a time (`UniversalCondition.exists_extends_snoc`).  Native construction. -/
theorem universalPointStepTarget : UniversalPointStepTarget α M := by
  intro hα c A
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨c, UniversalCondition.Extends.refl c, fun a ha ↦ by simp at ha⟩
  | insert a A _ ih =>
    obtain ⟨d, hcd, hd⟩ := ih
    by_cases had : a ∈ Set.range d.W
    · refine ⟨d, hcd, fun x hx ↦ ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact had
      · exact hd x hx
    · obtain ⟨d', hdd', hd'⟩ := d.exists_extends_snoc hα had
      refine ⟨d', hcd.trans hdd', fun x hx ↦ ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hd'
      · exact hdd'.range_subset (hd x hx)

/-- **The exact task step holds** (`UniversalTaskStepTarget α M`): a point step for the points of
the root; then, when the root face is defined and the donor is a strongly coded legal coface over
it, the strongly coded amalgam of the donor with the type of the condition over the literal root
face, and fresh placement of the places of the amalgam outside the old tuple.  Otherwise the task
is done vacuously after the point step.  Native construction. -/
theorem universalTaskStepTarget : UniversalTaskStepTarget α M := by
  intro hα hM c k m t D g
  classical
  obtain ⟨c₁, hcc₁, hc₁⟩ := universalPointStepTarget α M hα c (Finset.univ.image t)
  obtain ⟨h, hh⟩ := Realization.exists_trans_eq_of_forall_mem_range (w := c₁.W) (t := t)
    fun j ↦ hc₁ _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  by_cases hdone : ∃ p, restrictFace h c₁.w = some p ∧ D.IsStronglyCodedLegal ∧
      restrictFace g D = some p
  · obtain ⟨p, hp, hD, hg⟩ := hdone
    obtain ⟨N', Q, i, j, hQ, hQw, hQD, hij⟩ :=
      exists_stronglyCoded_amalgam_of_isSuccPrelimit hα c₁.isStronglyCodedLegal hD hp hg
    -- only the places of `Q` outside the range of `i` are new; they go to fresh points
    obtain ⟨U, hU⟩ := freshPlacementTarget M hM i c₁.W
    refine ⟨⟨N', U, Q, hQ⟩, hcc₁.trans ⟨i, hU, hQw⟩, h.trans i, ?_,
      fun _ _ _ _ ↦ ⟨j, ?_, hQD⟩⟩
    · rw [← hh, ← hU]
      rfl
    · rw [← Function.Embedding.trans_assoc, ← hij, ← hh, ← hU]
      rfl
  · exact ⟨c₁, hcc₁, h, hh, fun p hp hD hg ↦ absurd ⟨p, hp, hD, hg⟩ hdone⟩

end Steps

end

end VaughtConjecture

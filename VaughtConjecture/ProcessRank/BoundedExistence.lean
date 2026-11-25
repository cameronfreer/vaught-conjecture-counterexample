/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Zorn
import VaughtConjecture.AlephOne.ReceivingModel
import VaughtConjecture.ProcessRank.BoundedConstruction

/-!
# One receiving model per bounded age, on the carrier of size `ℵ₁`: the proofs

Proofs of the statements of `VaughtConjecture.ProcessRank.BoundedConstruction`, following the
`ℵ₁` companion construction (`VaughtConjecture.AlephOne.OptionAttachment` to
`VaughtConjecture.AlephOne.ReceivingModel`) with the bounded age `A_K` in place of the top-free
age.

* **Exact one-point attachment within `A_K`** (`boundedOptionAttachmentTarget`): compatible
  attachments along a monotone chain of occurrences by the bounded pinned extension
  (`ProcessRank.Bounded.exists_pinned_extension_mem`), whose input of top grade at most `K` is the
  type of the next occurrence, then the realization of the chain of charts
  (`Realization.chartChainRealizationTarget`).
* **Zorn's lemma on bounded conditions** (`boundedChainUnionTarget`,
  `boundedOnePointExtensionTarget`, `boundedExistsFullHeightConditionTarget`): the initial
  condition, unions of chains, and the one-point extension at the least point outside a countable
  domain.
* **Exact receiving within `A_K`** from the served requests
  (`boundedFullHeightExactReceivingTarget`).
* **Finite-cut receiving** (`boundedFiniteCutReceivingTarget`): the coface capped above the grade
  `K` (`StageType.capAbove`) at an ordinal above the cutoff and above every label of the coface
  other than `⊤`; it keeps the root literally, since the cells of the root labelled `⊤` have
  grade at most `K` (`StageType.restrictFace_capAbove`).
* **The receiving model** (`boundedIsReceivingModelOfExactReceivingTarget`,
  `existsBoundedReceivingModelTarget`).

## Placement

The bounded top-grade part of the process-rank companion programme (the files
`VaughtConjecture/ProcessRank/Bounded*.lean`).
-/

universe u v

namespace VaughtConjecture.ProcessRank.Bounded

open Ordinal Set Realization AlephOne

/-! ### Exact one-point attachment within the bounded age -/

/-- **Compatible one-point attachments within `A_K` along a chain of occurrences**: at a limit
stage, in an exactly consistent realization with legal types of top grades at most `K`, along a
monotone sequence `c` of occurrences, a coface `d` of top grade at most `K` of the type of `c 0`
extends to cofaces `Q k` of top grade at most `K` of the types of `c k`, each the restriction of
the next along the face map of `c k` in `c (k + 1)` extended by the new point. -/
theorem exists_boundedCompatibleAttachments {α : Ordinal.{u}} {M : Type v}
    (hα : Order.IsSuccLimit α) (K : ℕ) (R : Realization.{u, v} α M) (hR : R.IsConsistent)
    (hL : R.HasLegalTypes) (hK : HasTopGradeLe R K) (c : ℕ → R.Occurrence) (hc : Monotone c)
    (d : StageType.{u} α ((c 0).arity + 1)) (hd : d ∈ (c 0).type.cofaces) (hdK : d.topGrade ≤ K) :
    ∃ Q : ∀ k, StageType.{u} α ((c k).arity + 1), Q 0 = d ∧
      (∀ k, Q k ∈ (c k).type.cofaces ∧ (Q k).topGrade ≤ K) ∧
      ∀ k (g : Fin (c k).arity ↪ Fin (c (k + 1)).arity),
        g.trans (c (k + 1)).tuple = (c k).tuple →
          StageType.restrictFace (extendByLast g) (Q (k + 1)) = some (Q k) := by
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hc (Nat.le_succ k))
  let A : ℕ → Type _ := fun k ↦
    {q : StageType.{u} α ((c k).arity + 1) // q ∈ (c k).type.cofaces ∧ q.topGrade ≤ K}
  have hstep : ∀ k (q : A k), ∃ q' : A (k + 1),
      StageType.restrictFace (extendByLast (g k)) q'.1 = some q.1 := fun k q ↦ by
    obtain ⟨Q, hQ, hQP, hQd⟩ := exists_pinned_extension_mem hα
      ⟨hL _ _ (c (k + 1)).eval_tuple, hK _ _ (c (k + 1)).eval_tuple⟩ (hgt k)
      ⟨q.2.1.1, q.2.2⟩ q.2.1.2
    exact ⟨⟨Q, ⟨hQ.1, hQP⟩, hQ.2⟩, hQd⟩
  choose step hstep using hstep
  let Q : ∀ k, A k := fun k ↦ Nat.rec (motive := A) ⟨d, hd, hdK⟩ step k
  refine ⟨fun k ↦ (Q k).1, rfl, fun k ↦ (Q k).2, fun k g' hg' ↦ ?_⟩
  have : g' = g k := Function.Embedding.ext fun i ↦
    (c (k + 1)).tuple.injective
      ((DFunLike.congr_fun hg' i).trans (DFunLike.congr_fun (hgc k) i).symm)
  subst this
  exact hstep k (Q k)

/-- **Exact one-point attachment within `A_K` over a countable realization**, the target form: an
exhaustive chain of occurrences through `x` (`Realization.existsExhaustiveOccurrenceChainTarget`)
carries compatible attachments within `A_K` (`exists_boundedCompatibleAttachments`), realized by
one exactly consistent covering realization (`Realization.chartChainRealizationTarget`); its types
are faces of the attachments, hence legal of top grade at most `K`, and a tuple of old points has
its evaluation in `R` by exact consistency of `R`. -/
theorem boundedOptionAttachmentTarget : BoundedOptionAttachmentTarget.{u, v} := by
  intro α M _ hα K R hR hc hL hK x d hd hdK
  obtain ⟨c, rfl, hmono, hex⟩ := existsExhaustiveOccurrenceChainTarget R hc x
  obtain ⟨Q, hQ0, hQ, hQc⟩ := exists_boundedCompatibleAttachments hα K R hR hL hK c hmono d hd hdK
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hmono (Nat.le_succ k))
  have hold : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), ∃ k, ∃ h : Fin n ↪ Fin (c k).arity,
      h.trans (c k).tuple = t := fun n t ↦ by
    have hex' := hex
    choose N hN using hex'
    refine ⟨Finset.univ.sup fun i ↦ N (t i), (c _).exists_trans_eq fun a ha ↦ ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
    exact hmono (Finset.le_sup (f := fun i ↦ N (t i)) (Finset.mem_univ i)) (hN (t i))
  obtain ⟨S, hSc, hScov, hSw, hSf⟩ := chartChainRealizationTarget (fun k ↦ (c k).arity + 1)
    (fun k ↦ appendNone (c k).tuple) Q
    (fun k ↦ ⟨extendByLast (g k), extendByLast_trans_appendNone (hgc k), hQc k (g k) (hgc k)⟩)
    fun y ↦ by
      cases y with
      | none => exact ⟨0, Fin.last _, appendNone_last _⟩
      | some a =>
        obtain ⟨k, hk⟩ := hex a
        obtain ⟨i, rfl⟩ := (Occurrence.mem_support _).mp hk
        exact ⟨k, i.castSucc, appendNone_castSucc _ _⟩
  refine ⟨S, hSc, hScov, fun n t p hp ↦ ?_, fun n t p hp ↦ ?_, fun n t ↦ ?_, ?_⟩
  · obtain ⟨k, f, -, hf⟩ := hSf t p hp
    exact (hQ k).1.1.restrictFace _ hf
  · obtain ⟨k, f, -, hf⟩ := hSf t p hp
    exact (StageType.topGrade_le_of_restrictFace hf).trans (hQ k).2
  · obtain ⟨k, h, rfl⟩ := hold t
    have ht : (h.trans (c k).tuple).trans Function.Embedding.some =
        (h.trans Fin.castSuccEmb).trans (appendNone (c k).tuple) := by
      rw [Function.Embedding.trans_assoc, Function.Embedding.trans_assoc,
        castSuccEmb_trans_appendNone]
    rw [ht, hSc _ _ _ (hSw k), ← StageType.restrictFace_trans _ _ _ (hQ k).1.2,
      eval_face hR]
  · rw [← hQ0]
    exact hSw 0

/-! ### Bounded conditions: the initial condition and unions of chains -/

/-- The bottom one-point type at `ω₁` has top grade `0`. -/
theorem topGrade_pointType : (pointType (ω₁ : Ordinal.{0})).topGrade = 0 :=
  StageType.topGrade_eq_zero_iff.mpr fun _ ↦ bot_ne_top

/-- **Service within `A_K` depends only on two evaluations.** -/
theorem BoundedServesAt.of_eval_eq {K : ℕ} {R R' : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier}
    {r : Request} {γ : Carrier} (hR : BoundedServesAt K R r γ)
    (h₁ : (∀ i, r.tuple i < γ) → R'.eval r.tuple = R.eval r.tuple)
    (h₂ : ∀ h : ∀ i, r.tuple i < γ, R'.eval (r.extendAt h) = R.eval (r.extendAt h)) :
    BoundedServesAt K R' r γ :=
  fun h p hp hd hdK ↦ (h₂ h).trans (hR h p ((h₁ h).symm.trans hp) hd hdK)

namespace BoundedCondition

variable {K : ℕ} {s : Carrier → Request}

theorem le_def {c c' : BoundedCondition K s} : c ≤ c' ↔ c.dom ⊆ c'.dom ∧
    ∀ ⦃n : ℕ⦄ (t : Fin n ↪ Carrier), range t ⊆ c.dom → c'.real.eval t = c.real.eval t :=
  Iff.rfl

/-- A typed tuple lies inside the domain. -/
theorem range_subset_of_isSome (c : BoundedCondition K s) {n : ℕ} {t : Fin n ↪ Carrier}
    (ht : (c.real.eval t).isSome) : range t ⊆ c.dom := by
  by_contra h
  simp [c.eval_eq_none t h] at ht

/-- A tuple below a point of the domain followed by that point lies inside the domain. -/
theorem range_extendAt_subset (c : BoundedCondition K s) (r : Request) {γ : Carrier}
    (hγ : γ ∈ c.dom) (h : ∀ i, r.tuple i < γ) : range (r.extendAt h) ⊆ c.dom := by
  rintro _ ⟨i, rfl⟩
  exact c.isLowerSet_dom (r.extendAt_le h i) hγ

/-- A tuple below a point of the domain lies inside the domain. -/
theorem range_tuple_subset (c : BoundedCondition K s) (r : Request) {γ : Carrier}
    (hγ : γ ∈ c.dom) (h : ∀ i, r.tuple i < γ) : range r.tuple ⊆ c.dom := by
  rintro _ ⟨i, rfl⟩
  exact c.isLowerSet_dom (h i).le hγ

/-- The **initial bounded condition**: empty domain, only the empty tuple typed. -/
noncomputable def initial (K : ℕ) (s : Carrier → Request) : BoundedCondition K s where
  dom := ∅
  isLowerSet_dom := isLowerSet_empty
  real := Condition.initialRealization
  eval_eq_none := (Condition.initial s).eval_eq_none
  isConsistent := (Condition.initial s).isConsistent
  isCovering := (Condition.initial s).isCovering
  hasLegalTypes := (Condition.initial s).hasLegalTypes
  hasTopGradeLe n t p ht := by
    have := StageType.topGrade_eq_zero_iff.mpr ((Condition.initial s).hasTopFreeTypes t p ht)
    omega
  serves _ h := h.elim

open Classical in
/-- The **union realization** of a set of bounded conditions. -/
noncomputable def unionRealization (C : Set (BoundedCondition K s)) :
    Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier where
  eval t := if h : ∃ c ∈ C, range t ⊆ c.dom then h.choose.real.eval t else none

/-- The union realization agrees with every member of a chain on the tuples inside its domain. -/
theorem eval_unionRealization {C : Set (BoundedCondition K s)} (hC : IsChain (· ≤ ·) C)
    {c : BoundedCondition K s} (hc : c ∈ C) {n : ℕ} {t : Fin n ↪ Carrier}
    (ht : range t ⊆ c.dom) : (unionRealization C).eval t = c.real.eval t := by
  simp only [unionRealization]
  split_ifs with h
  swap
  · exact absurd ⟨c, hc, ht⟩ h
  obtain ⟨hc', ht'⟩ := h.choose_spec
  rcases eq_or_ne h.choose c with heq | hne
  · rw [heq]
  rcases hC hc' hc hne with hle | hle
  · exact (hle.2 t ht').symm
  · exact hle.2 t ht

/-- A typed tuple of the union realization is typed alike in some member. -/
theorem exists_of_eval_unionRealization {C : Set (BoundedCondition K s)}
    (hC : IsChain (· ≤ ·) C) {n : ℕ} {t : Fin n ↪ Carrier}
    {p : StageType.{0} (ω₁ : Ordinal.{0}) n} (ht : (unionRealization C).eval t = some p) :
    ∃ c ∈ C, range t ⊆ c.dom ∧ c.real.eval t = some p := by
  by_cases h : ∃ c ∈ C, range t ⊆ c.dom
  · obtain ⟨c, hc, htc⟩ := h
    exact ⟨c, hc, htc, (eval_unionRealization hC hc htc).symm.trans ht⟩
  · simp [unionRealization, h] at ht

/-- A finite tuple inside the union of the domains of a nonempty chain lies inside one domain. -/
theorem exists_range_subset_dom {C : Set (BoundedCondition K s)} (hne : C.Nonempty) {n : ℕ}
    {t : Fin n ↪ Carrier} (ht : range t ⊆ ⋃ c ∈ C, c.dom) : ∃ c ∈ C, range t ⊆ c.dom := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · obtain ⟨c, hc⟩ := hne
    exact ⟨c, hc, by simp [range_eq_empty]⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ t i) Finset.univ_nonempty
  obtain ⟨c, hc, hci⟩ := mem_iUnion₂.mp (ht ⟨i₀, rfl⟩)
  refine ⟨c, hc, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact c.isLowerSet_dom (hi₀ i (Finset.mem_univ _)) hci

/-- The **union** of a nonempty chain of bounded conditions. -/
noncomputable def union (C : Set (BoundedCondition K s)) (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) : BoundedCondition K s where
  dom := ⋃ c ∈ C, c.dom
  isLowerSet_dom := isLowerSet_iUnion₂ fun c _ ↦ c.isLowerSet_dom
  real := unionRealization C
  eval_eq_none n t ht := by
    by_cases h : ∃ c ∈ C, range t ⊆ c.dom
    · obtain ⟨c, hc, htc⟩ := h
      exact absurd (htc.trans (subset_biUnion_of_mem hc)) ht
    · simp [unionRealization, h]
  isConsistent m n t p f ht := by
    obtain ⟨c, hc, htc, htp⟩ := exists_of_eval_unionRealization hC ht
    have hft : range (f.trans t) ⊆ c.dom := by
      rintro _ ⟨i, rfl⟩
      exact htc ⟨f i, rfl⟩
    rw [eval_unionRealization hC hc hft]
    exact c.isConsistent t p f htp
  isCovering n t ht := by
    obtain ⟨c, hc, htc⟩ := exists_range_subset_dom hne ht
    obtain ⟨m, u, f, hfu, hu⟩ := c.isCovering t htc
    exact ⟨m, u, f, hfu, by rwa [eval_unionRealization hC hc (c.range_subset_of_isSome hu)]⟩
  hasLegalTypes n t p ht := by
    obtain ⟨c, -, -, htp⟩ := exists_of_eval_unionRealization hC ht
    exact c.hasLegalTypes t p htp
  hasTopGradeLe n t p ht := by
    obtain ⟨c, -, -, htp⟩ := exists_of_eval_unionRealization hC ht
    exact c.hasTopGradeLe t p htp
  serves γ hγ h p ht hd hdK := by
    obtain ⟨c, hc, hγc⟩ := mem_iUnion₂.mp hγ
    rw [eval_unionRealization hC hc (c.range_tuple_subset _ hγc h)] at ht
    rw [eval_unionRealization hC hc (c.range_extendAt_subset _ hγc h)]
    exact c.serves γ hγc h p ht hd hdK

/-- The union is an upper bound of the chain. -/
theorem le_union {C : Set (BoundedCondition K s)} (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty)
    {c : BoundedCondition K s} (hc : c ∈ C) : c ≤ union C hC hne :=
  ⟨subset_biUnion_of_mem hc, fun _ _ ht ↦ eval_unionRealization hC hc ht⟩

/-- Every chain of bounded conditions has an upper bound. -/
theorem exists_upperBound (C : Set (BoundedCondition K s)) (hC : IsChain (· ≤ ·) C) :
    ∃ ub : BoundedCondition K s, ∀ c ∈ C, c ≤ ub := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨initial K s, fun _ h ↦ h.elim⟩
  · exact ⟨union C hC hne, fun _ hc ↦ le_union hC hne hc⟩

/-! ### The realization on the domain -/

/-- The realization on the domain of a bounded condition. -/
def restrict (c : BoundedCondition K s) : Realization.{0, 0} (ω₁ : Ordinal.{0}) c.dom where
  eval t := c.real.eval (t.trans (Function.Embedding.subtype _))

theorem isConsistent_restrict (c : BoundedCondition K s) : c.restrict.IsConsistent :=
  fun _ _ _ p f ht ↦ c.isConsistent _ p f ht

theorem hasLegalTypes_restrict (c : BoundedCondition K s) : c.restrict.HasLegalTypes :=
  fun _ _ p ht ↦ c.hasLegalTypes _ p ht

theorem hasTopGradeLe_restrict (c : BoundedCondition K s) : HasTopGradeLe c.restrict K :=
  fun _ _ p ht ↦ c.hasTopGradeLe _ p ht

theorem isCovering_restrict (c : BoundedCondition K s) : c.restrict.IsCovering := by
  intro n t
  have ht : range (t.trans (Function.Embedding.subtype _)) ⊆ c.dom := by
    rintro _ ⟨i, rfl⟩
    exact (t i).2
  obtain ⟨m, u, f, hfu, hu⟩ := c.isCovering _ ht
  have hud := c.range_subset_of_isSome hu
  refine ⟨m, u.codRestrict c.dom fun i ↦ hud ⟨i, rfl⟩, f, ?_, hu⟩
  exact Function.Embedding.ext fun i ↦ Subtype.ext (congrArg (fun v : Fin n ↪ Carrier ↦ v i) hfu)

/-- A bounded condition of full domain is covering on the whole carrier. -/
theorem isCovering_of_dom_eq_univ (c : BoundedCondition K s) (h : c.dom = Set.univ) :
    c.real.IsCovering :=
  fun _ t ↦ c.isCovering t (h ▸ subset_univ _)

/-! ### The one-point extension -/

/-- The embedding of `Option dom` into the carrier sending the new point to `x`. -/
def optionEmbedding (c : BoundedCondition K s) {x : Carrier} (hx : x ∉ c.dom) :
    Option c.dom ↪ Carrier :=
  ⟨fun o ↦ o.elim x Subtype.val, by
    rintro (_ | a) (_ | b) h
    · rfl
    · have h : x = b := h
      exact absurd (h ▸ b.2) hx
    · have h : (a : Carrier) = x := h
      exact absurd (h ▸ a.2) hx
    · exact congrArg some (Subtype.ext h)⟩

@[simp] theorem optionEmbedding_none (c : BoundedCondition K s) {x : Carrier}
    (hx : x ∉ c.dom) : c.optionEmbedding hx none = x :=
  rfl

@[simp] theorem optionEmbedding_some (c : BoundedCondition K s) {x : Carrier}
    (hx : x ∉ c.dom) (a : c.dom) : c.optionEmbedding hx (some a) = a :=
  rfl

theorem mem_range_optionEmbedding (c : BoundedCondition K s) {x : Carrier} (hx : x ∉ c.dom)
    {y : Carrier} : y ∈ range (c.optionEmbedding hx) ↔ y ∈ insert x c.dom := by
  constructor
  · rintro ⟨_ | a, rfl⟩
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ a.2
  · rintro (rfl | hy)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨y, hy⟩, rfl⟩

/-- Old evaluations are kept by the pushforward of a realization on `Option dom` that keeps
them. -/
theorem pushforward_eval_of_range_subset (c : BoundedCondition K s) {x : Carrier}
    (hx : x ∉ c.dom) {S : Realization.{0, 0} (ω₁ : Ordinal.{0}) (Option c.dom)}
    (hS : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ c.dom),
      S.eval (t.trans Function.Embedding.some) = c.restrict.eval t)
    {n : ℕ} {t : Fin n ↪ Carrier} (ht : range t ⊆ c.dom) :
    (S.pushforward (c.optionEmbedding hx)).eval t = c.real.eval t := by
  have key : ((t.codRestrict c.dom fun i ↦ ht ⟨i, rfl⟩).trans Function.Embedding.some).trans
      (c.optionEmbedding hx) = t := rfl
  conv_lhs => rw [← key]
  rw [pushforward_eval_trans, hS]
  rfl

/-- **Extension by an attachment** within `A_K`. -/
theorem exists_le_of_attachment (c : BoundedCondition K s) {x : Carrier} (hx : x ∉ c.dom)
    (hmin : ∀ y, y < x → y ∈ c.dom) {S : Realization.{0, 0} (ω₁ : Ordinal.{0}) (Option c.dom)}
    (hSc : S.IsConsistent) (hScov : S.IsCovering) (hSl : S.HasLegalTypes)
    (hSK : HasTopGradeLe S K)
    (hS : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ c.dom),
      S.eval (t.trans Function.Embedding.some) = c.restrict.eval t)
    (hserve : BoundedServesAt K (S.pushforward (c.optionEmbedding hx)) (s x) x) :
    ∃ c' : BoundedCondition K s, c ≤ c' ∧ c'.dom = insert x c.dom := by
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
    hasTopGradeLe := fun n t p ht ↦ by
      obtain ⟨u, -, hu⟩ := exists_of_pushforward_eval_eq_some ht
      exact hSK u p hu
    serves := fun γ hγ ↦ by
      rcases hγ with rfl | hγ
      · exact hserve
      · exact (c.serves γ hγ).of_eval_eq
          (fun h ↦ c.pushforward_eval_of_range_subset hx hS (c.range_tuple_subset _ hγ h))
          (fun h ↦ c.pushforward_eval_of_range_subset hx hS (c.range_extendAt_subset _ hγ h)) },
    ⟨subset_insert _ _, fun _ _ ht ↦ c.pushforward_eval_of_range_subset hx hS ht⟩, rfl⟩

/-- The empty tuple of the domain is typed in the realization on the domain. -/
theorem exists_eval_restrict_ofIsEmpty (c : BoundedCondition K s) :
    ∃ p, c.restrict.eval (Function.Embedding.ofIsEmpty : Fin 0 ↪ c.dom) = some p := by
  obtain ⟨m, u, f, hfu, hu⟩ :=
    c.isCovering_restrict (Function.Embedding.ofIsEmpty : Fin 0 ↪ c.dom)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hu
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (q.isSome_restrictFace_of_zero f)
  exact ⟨p, by rw [← hfu, c.isConsistent_restrict u q f hq, hp]⟩

end BoundedCondition

/-- **Upper bounds of chains of bounded conditions**, the target form. -/
theorem boundedChainUnionTarget (K : ℕ) : BoundedChainUnionTarget K := fun _ C hC ↦
  ⟨BoundedCondition.exists_upperBound C hC, fun hne ↦
    ⟨BoundedCondition.union C hC hne, fun _ hc ↦ BoundedCondition.le_union hC hne hc, rfl⟩⟩

/-- **The one-point extension of a bounded condition**, the target form: the least point `x`
outside the countable domain is attached by `boundedOptionAttachmentTarget`, realizing the donor
of the request scheduled at `x` when that request is eligible, and the bottom one-point type over
the empty tuple otherwise. -/
theorem boundedOnePointExtensionTarget (K : ℕ) : BoundedOnePointExtensionTarget K := by
  intro s c hcount
  have hne : c.domᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact not_countable_carrier (countable_univ_iff.mp (h ▸ hcount))
  obtain ⟨x, hx, hxmin⟩ := wellFounded_lt.has_min _ hne
  have hmin : ∀ y, y < x → y ∈ c.dom := fun y hy ↦ by_contra fun h ↦ hxmin y h hy
  have : Countable c.dom := hcount.to_subtype
  have hα := Cardinal.isSuccLimit_omega 1
  by_cases hE : ∃ (h : ∀ i, (s x).tuple i < x) (p : StageType.{0} (ω₁ : Ordinal.{0}) (s x).arity),
      c.real.eval (s x).tuple = some p ∧ (s x).donor ∈ p.cofaces ∧ (s x).donor.topGrade ≤ K
  · obtain ⟨h, p, hp, hd, hdK⟩ := hE
    let y : c.restrict.Occurrence :=
      ⟨(s x).arity, (s x).tuple.codRestrict c.dom fun i ↦ hmin _ (h i), p, hp⟩
    obtain ⟨S, hSc, hScov, hSl, hSK, hS, hSd⟩ := boundedOptionAttachmentTarget hα K c.restrict
      c.isConsistent_restrict c.isCovering_restrict c.hasLegalTypes_restrict
      c.hasTopGradeLe_restrict y (s x).donor hd hdK
    obtain ⟨c', hle, hdom⟩ := c.exists_le_of_attachment hx hmin hSc hScov hSl hSK hS
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
    obtain ⟨S, hSc, hScov, hSl, hSK, hS, -⟩ := boundedOptionAttachmentTarget hα K c.restrict
      c.isConsistent_restrict c.isCovering_restrict c.hasLegalTypes_restrict
      c.hasTopGradeLe_restrict y (pointType _)
      (StageType.mem_cofaces_of_zero (pointType_mem_boundedAge K).1)
      (topGrade_pointType.trans_le (Nat.zero_le K))
    obtain ⟨c', hle, hdom⟩ := c.exists_le_of_attachment hx hmin hSc hScov hSl hSK hS
      fun h' p' hp' hd' hdK' ↦ by
        refine absurd ⟨h', p', ?_, hd', hdK'⟩ hE
        have hsub : range (s x).tuple ⊆ c.dom := by
          rintro _ ⟨i, rfl⟩
          exact hmin _ (h' i)
        rwa [c.pushforward_eval_of_range_subset hx hS hsub] at hp'
    exact ⟨c', hle, x, hx, hdom⟩

/-- **A bounded condition of full domain exists**, the target form: Zorn's lemma on bounded
conditions; a maximal one has full domain, since otherwise its domain is a proper lower set,
hence countable (`AlephOne.countable_of_isLowerSet_ne_univ`), and the one-point extension is
strictly larger. -/
theorem boundedExistsFullHeightConditionTarget (K : ℕ) :
    BoundedExistsFullHeightConditionTarget K := by
  intro s
  obtain ⟨c, hc⟩ : ∃ c : BoundedCondition K s, IsMax c :=
    zorn_le fun C hC ↦ BoundedCondition.exists_upperBound C hC
  refine ⟨c, ?_⟩
  by_contra hne
  obtain ⟨c', hcc', x, hx, hdom⟩ := boundedOnePointExtensionTarget K s c
    (countable_of_isLowerSet_ne_univ c.isLowerSet_dom hne)
  exact hx ((hc hcc').1 (hdom ▸ Set.mem_insert x c.dom))

/-- **Exact receiving within `A_K` from the served requests**, the target form: over a cover `x`
of `t`, the request `(x, D)` is scheduled at a point above every point of `x`, where it is
served; the one-point form gives every arity, `A_K` being face closed. -/
theorem boundedFullHeightExactReceivingTarget (K : ℕ) :
    BoundedFullHeightExactReceivingTarget K := by
  intro s hs c hc
  refine ExactReceivingWithin.of_one_point c.isConsistent
    (fun _ _ _ _ _ hD hp ↦ mem_boundedAge_of_restrictFace hD hp) ?_
  intro n t x hx D hD hDt
  obtain ⟨hinj, hxt⟩ := hx
  obtain ⟨b, hb⟩ := exists_forall_lt x
  obtain ⟨γ, hbγ, hγ⟩ := hs ⟨n, ⟨x, hinj⟩, D⟩ b
  have hserv := c.serves γ (hc ▸ Set.mem_univ γ)
  rw [hγ] at hserv
  have hlt : ∀ i, x i < γ := fun i ↦ (hb i).trans_le hbγ
  have heval := hserv hlt t hxt ⟨hD.1, hDt⟩ hD.2
  refine ⟨_, covers_of_eval _ heval, funext fun i ↦ ?_⟩
  simp [Request.extendAt]

/-! ### Finite-cut receiving and the receiving model -/

/-- **Finite-cut receiving from exact receiving within `A_K`**, the target form: over an
occurrence of type `p`, a legal coface `d` and a cutoff `δ`, the donor is `d` capped above the
grade `K` at an ordinal `c' < α`, self-visible at the arity of `d`, above `δ` and above every
label of `d` other than `⊤`.  It is legal, of top grade at most `K`, restricts to `p` literally
(the cells of `p` labelled `⊤` have grade at most `K`), and agrees with `d` below `δ`. -/
theorem boundedFiniteCutReceivingTarget : BoundedFiniteCutReceivingTarget.{u, v} := by
  intro α M hα K R hK hrec x d hd c hc
  obtain ⟨δ, hδ, rfl⟩ := Label.isPermittedCutoff_iff.mp hc
  obtain ⟨c₀, hc₀α, -, hc₀⟩ := StageType.exists_cap_ne_top hα d (x.arity + 1)
  obtain ⟨c', hc₀c', hc'α, hc'⟩ :=
    Label.exists_lt_lt_isSelfVisible hα.isSuccPrelimit (max_lt hc₀α hδ) (x.arity + 1)
  have hle {y : Ordinal.{u}} (hy : y ≤ max c₀ δ) : (y : Label.{u}) ≤ c' :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (hy.trans hc₀c'.le))
  have hct : ∀ e, d.label e ≠ ⊤ → d.label e ≤ c' :=
    fun e he ↦ (hc₀ e he).trans (hle (le_max_left _ _))
  have hQ : StageType.restrictFace Fin.castSuccEmb (d.capAbove K c' hc' hc'α) = some x.type :=
    StageType.restrictFace_capAbove hct hd.2 fun i hi ↦
      (StageType.grade_le_topGrade hi).trans (hK _ _ x.eval_tuple)
  obtain ⟨u, ⟨hinj, hu⟩, huc⟩ := hrec x.type x.tuple (covers_of_eval _ x.eval_tuple)
    (d.capAbove K c' hc' hc'α) Fin.castSuccEmb
    ⟨StageType.isLegal_capAbove.mpr hd.1, StageType.topGrade_capAbove_le⟩ hQ
  refine ⟨⟨u, hinj⟩, Function.Embedding.ext fun i ↦ congrFun huc i, d.capAbove K c' hc' hc'α,
    ⟨rfl, fun i j hij ↦ ?_⟩, hu⟩
  obtain rfl : i = j := Fin.ext hij
  refine (congrArg (min · _) (StageType.capAbove_label (t := d) (K := K) (hc := hc')
    (hcα := hc'α) i)).trans ?_
  split_ifs
  · rw [min_assoc, min_eq_right (hle (le_max_right _ _))]
  · rfl

/-- **Exact receiving within `A_K` makes a receiving model**, the target form: finite-cut
receiving (`boundedFiniteCutReceivingTarget`), then `Realization.isModel_of_hasFiniteCutReceiving`
with the uniformity and dominance instances from the coatom extension property with apex. -/
theorem boundedIsReceivingModelOfExactReceivingTarget :
    BoundedIsReceivingModelOfExactReceivingTarget.{v} := by
  intro α M hα K R hne hc hcov hl hK hrec
  have hr := boundedFiniteCutReceivingTarget hα K R hK hrec
  have hext := StageType.hasApexCoatomExtensions hα.isSuccPrelimit
  exact ⟨isModel_of_hasFiniteCutReceiving hα hne hl hc hcov hr
    (fun x _ _ hγα ↦ StageType.nonempty_cofaces_inter_uniformityFamily hext.hasCoatomExtensions
      hα.isSuccPrelimit (hl _ _ x.eval_tuple) hγα)
    (fun x _ hγα ↦ StageType.nonempty_cofaces_inter_dominanceFamily hext hα.isSuccPrelimit
      (hl _ _ x.eval_tuple) hγα), hr⟩

/-- **A receiving model for every bounded age, on the carrier**, the target form: an unbounded
schedule (`AlephOne.existsUnboundedScheduleTarget`), a bounded condition of full domain, exact
receiving within `A_K` from the served requests, and the receiving model. -/
theorem existsBoundedReceivingModelTarget (K : ℕ) : ExistsBoundedReceivingModelTarget K := by
  obtain ⟨s, hs⟩ := existsUnboundedScheduleTarget
  obtain ⟨c, hc⟩ := boundedExistsFullHeightConditionTarget K s
  have hrec := boundedFullHeightExactReceivingTarget K s hs c hc
  exact ⟨c.real, boundedIsReceivingModelOfExactReceivingTarget (Cardinal.isSuccLimit_omega 1) K
    c.real inferInstance c.isConsistent (c.isCovering_of_dom_eq_univ hc) c.hasLegalTypes
    c.hasTopGradeLe hrec, c.hasTopGradeLe, hrec⟩

end VaughtConjecture.ProcessRank.Bounded

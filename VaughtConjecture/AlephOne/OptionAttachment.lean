/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TopFreePinnedExtension
import VaughtConjecture.Realization.ChartChain
import VaughtConjecture.Realization.Model

/-!
# Exact one-point attachment over a countable realization

Stage 2 of the `ℵ₁` companion construction: one new point is attached to a countable realization,
keeping every old evaluation and realizing a prescribed top-free donor over a given occurrence.

**Top-free types.**  A realization has top-free types when every type it assigns is top-free
(`Realization.HasTopFreeTypes`).

**The new point.**  The carrier of the extension is `Option M`, with the old points `some a` and
the new point `none`; a tuple of old points followed by the new point is
`Realization.appendNone`.

**The statements** (all proved):

* compatible one-point attachments along a monotone sequence of occurrences, one finite step at a
  time (`Realization.ExistsCompatibleAttachmentsTarget`), from the top-free pinned extension
  (`StageType.exists_isTopFree_pinned_extension`); no countability;
* the attachment on `Option M` over a countable carrier `M`
  (`Realization.OptionAttachmentTarget`): an exactly consistent covering realization with legal
  top-free types on `Option M` that gives every tuple of old points its old evaluation, `none`
  included, and gives a given occurrence followed by the new point the prescribed donor.  The
  intended proof takes an exhaustive chain of occurrences through the given occurrence
  (`Realization.ExistsExhaustiveOccurrenceChainTarget`), compatible attachments along it, and the
  realization of the chain of charts `appendNone (c k).tuple`
  (`Realization.ChartChainRealizationTarget`).

Countability is of the old carrier only; the stage is any limit ordinal.  The statement is a
construction over a given realization.

## Placement

This file is Stage 2 (exact countable attachment) of the `ℵ₁` companion construction over the
density sentence; that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- A realization **has top-free types** when every type it assigns is top-free. -/
def HasTopFreeTypes (R : Realization.{u, v} α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p → p.IsTopFree

/-- A tuple of old points followed by the new point: the tuple `t` of `M`, read in `Option M`,
followed by `none`. -/
def appendNone {n : ℕ} (t : Fin n ↪ M) : Fin (n + 1) ↪ Option M :=
  Fin.Embedding.snoc (t.trans Function.Embedding.some) (a := none) (by simp)

/-- `appendNone t` sends an old position `i` to the old point `t i`. -/
@[simp] theorem appendNone_castSucc {n : ℕ} (t : Fin n ↪ M) (i : Fin n) :
    appendNone t i.castSucc = some (t i) :=
  Fin.Embedding.snoc_castSucc

/-- `appendNone t` sends the last position to the new point. -/
@[simp] theorem appendNone_last {n : ℕ} (t : Fin n ↪ M) : appendNone t (Fin.last n) = none :=
  Fin.Embedding.snoc_last

/-- On the old positions, `appendNone t` is `t` read in `Option M`. -/
theorem castSuccEmb_trans_appendNone {n : ℕ} (t : Fin n ↪ M) :
    Fin.castSuccEmb.trans (appendNone t) = t.trans Function.Embedding.some :=
  Fin.Embedding.init_snoc _ _

/-- A face of tuples, extended by the new point, is a face of the tuples followed by the new
point. -/
theorem extendByLast_trans_appendNone {n m : ℕ} {g : Fin m ↪ Fin n} {t : Fin n ↪ M}
    {s : Fin m ↪ M} (hg : g.trans t = s) : (extendByLast g).trans (appendNone t) = appendNone s :=
  Function.Embedding.ext fun i ↦ by
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp [← hg]

/-- **Target: compatible one-point attachments along a chain of occurrences.**  At a limit stage,
in an exactly consistent realization with legal top-free types, along a monotone sequence `c` of
occurrences, a top-free coface `d` of the type of `c 0` extends to top-free cofaces `Q k` of the
types of `c k`, with `Q 0 = d`, each the restriction of the next along the face map `g` of `c k`
in `c (k + 1)` extended by the new point (`extendByLast g`).  The face map is unique, so the
statement quantifies over every face map.  No countability.  Proved
(`Realization.existsCompatibleAttachmentsTarget`). -/
def ExistsCompatibleAttachmentsTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (R : Realization.{u, v} α M),
    R.IsConsistent → R.HasLegalTypes → R.HasTopFreeTypes →
    ∀ (c : ℕ → R.Occurrence), Monotone c → ∀ d ∈ (c 0).type.cofaces, d.IsTopFree →
      ∃ Q : ∀ k, StageType.{u} α ((c k).arity + 1), Q 0 = d ∧
        (∀ k, Q k ∈ (c k).type.cofaces ∧ (Q k).IsTopFree) ∧
        ∀ k (g : Fin (c k).arity ↪ Fin (c (k + 1)).arity),
          g.trans (c (k + 1)).tuple = (c k).tuple →
            StageType.restrictFace (extendByLast g) (Q (k + 1)) = some (Q k)

/-- **Compatible one-point attachments along a chain of occurrences**, the target form: by
recursion along the chain, the attachment at `c k` is extended to `c (k + 1)` by the top-free
pinned extension (`StageType.exists_isTopFree_pinned_extension`) of the type of `c (k + 1)` along
the face map of `c k` in `c (k + 1)` (`Realization.Occurrence.le_iff_exists_restrictFace`); that
face map is the only one, by injectivity of the tuple of `c (k + 1)`. -/
theorem existsCompatibleAttachmentsTarget : ExistsCompatibleAttachmentsTarget.{u, v} := by
  intro α M hα R hR hL hT c hc d hd hdt
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hc (Nat.le_succ k))
  let A : ℕ → Type _ := fun k ↦
    {q : StageType.{u} α ((c k).arity + 1) // q ∈ (c k).type.cofaces ∧ q.IsTopFree}
  have hstep : ∀ k (q : A k), ∃ q' : A (k + 1),
      StageType.restrictFace (extendByLast (g k)) q'.1 = some q.1 := fun k q ↦ by
    obtain ⟨Q, hQ, hQt, hQP, hQd⟩ := StageType.exists_isTopFree_pinned_extension hα
      (hL _ _ (c (k + 1)).eval_tuple) (hT _ _ (c (k + 1)).eval_tuple) (hgt k) q.2.1.1 q.2.2
      q.2.1.2
    exact ⟨⟨Q, ⟨hQ, hQP⟩, hQt⟩, hQd⟩
  choose step hstep using hstep
  let Q : ∀ k, A k := fun k ↦ Nat.rec (motive := A) ⟨d, hd, hdt⟩ step k
  refine ⟨fun k ↦ (Q k).1, rfl, fun k ↦ (Q k).2, fun k g' hg' ↦ ?_⟩
  have : g' = g k := Function.Embedding.ext fun i ↦
    (c (k + 1)).tuple.injective
      ((DFunLike.congr_fun hg' i).trans (DFunLike.congr_fun (hgc k) i).symm)
  subst this
  exact hstep k (Q k)

/-- **Target: exact one-point attachment over a countable realization.**  At a limit stage `α`
(of any cardinality), let `R` be an exactly consistent covering realization with legal top-free
types on a countable carrier `M`, `x` an occurrence of `R`, and `d` a top-free coface of the type
of `x`.  Some exactly consistent covering realization `S` with legal top-free types on `Option M`
gives every tuple of old points its evaluation in `R` (`none` included) and gives the tuple of `x`
followed by the new point `none` the type `d`.  Construction over a given realization;
countability is of the old carrier only.  Proved (`Realization.optionAttachmentTarget`). -/
def OptionAttachmentTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes → ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, d.IsTopFree →
        ∃ S : Realization.{u, v} α (Option M), S.IsConsistent ∧ S.IsCovering ∧
          S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
          (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.some) = R.eval t) ∧
          S.eval (appendNone x.tuple) = some d

/-- **Exact one-point attachment over a countable realization**, the target form.  An exhaustive
chain `c` of occurrences through `x` (`Realization.existsExhaustiveOccurrenceChainTarget`) carries
compatible attachments `Q k` of the new point with `Q 0 = d`
(`Realization.existsCompatibleAttachmentsTarget`); the charts `appendNone (c k).tuple` with the
types `Q k` exhaust `Option M` and are realized by one exactly consistent covering realization
(`Realization.chartChainRealizationTarget`).  Its types are faces of the `Q k`, hence legal and
top-free; a tuple of old points lies in some `c k` and its evaluation is the restriction of the
type of `c k`, which is its evaluation in `R` by exact consistency of `R`, `none` included. -/
theorem optionAttachmentTarget : OptionAttachmentTarget.{u, v} := by
  intro α M _ hα R hR hc hL hT x d hd hdt
  obtain ⟨c, rfl, hmono, hex⟩ := existsExhaustiveOccurrenceChainTarget R hc x
  obtain ⟨Q, hQ0, hQ, hQc⟩ := existsCompatibleAttachmentsTarget hα R hR hL hT c hmono d hd hdt
  choose g hgc hgt using fun k : ℕ ↦ (Occurrence.le_iff_exists_restrictFace hR).mp
    (hmono (Nat.le_succ k))
  -- Every finite tuple of old points lies in some occurrence of the chain.
  have hold : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), ∃ k, ∃ h : Fin n ↪ Fin (c k).arity,
      h.trans (c k).tuple = t := fun n t ↦ by
    have hex' := hex
    choose K hK using hex'
    refine ⟨Finset.univ.sup fun i ↦ K (t i), (c _).exists_trans_eq fun a ha ↦ ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
    exact hmono (Finset.le_sup (f := fun i ↦ K (t i)) (Finset.mem_univ i)) (hK (t i))
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
    exact (hQ k).2.restrictFace hf
  · obtain ⟨k, h, rfl⟩ := hold t
    have ht : (h.trans (c k).tuple).trans Function.Embedding.some =
        (h.trans Fin.castSuccEmb).trans (appendNone (c k).tuple) := by
      rw [Function.Embedding.trans_assoc, Function.Embedding.trans_assoc,
        castSuccEmb_trans_appendNone]
    rw [ht, hSc _ _ _ (hSw k), ← StageType.restrictFace_trans _ _ _ (hQ k).1.2,
      eval_face hR]
  · rw [← hQ0]
    exact hSw 0

end VaughtConjecture.Realization

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Basic
import VaughtConjecture.Realization.Model

/-!
# Receiving for finite extensions

Roadmap, Layer 3 (receiving for finite extensions); semantic contract, item 12 (one permitted
cutoff at a time; the donor is a type at the stage of the realization, so no projected-donor
lifting is involved).

Fix a realization `R` at a stage `α`.  A **root** is a typed tuple `t` of `R`, of type `p`.  A
**donor** over `t` is a legal stage type `D` on `m` points together with an embedding
`g : Fin n ↪ Fin m` of coordinates along which `D` restricts to `p`.  Receiving the donor gives a
tuple `u` with `g.trans u = t`, so that `t` is kept literally.  Finite-cut receiving
(`HasFiniteCutReceiving`) receives donors on one new point; finite-extension receiving
(`HasFiniteExtensionReceiving`) receives donors on any finite number of new points.  This file
proves that the first gives the second for an exactly consistent realization at a stage that is
zero or a limit
(`HasFiniteCutReceiving.hasFiniteExtensionReceiving`), so that the two are equivalent there
(`hasFiniteExtensionReceiving_iff`, `IsModel.hasFiniteExtensionReceiving_iff`).  No countability
of the stage, covering, legality of the types of `R`, or family clause of a model is used.

**The chain.**  The points of `D` outside the face `g` are added one at a time, in an order given
by the **donor's plan** (the closed faces of the scheme of `D`): by accessibility of the plan
(`Geometry.IsPlan.exists_insert_mem`) some point `x` outside the face spans, with the face, a
closed face again, so the face `g` followed by `x` (`Fin.Embedding.snoc`) restricts `D` to a legal
stage type `D₁` on `n + 1` points whose face along the initial segment is that of `D` along `g`.
The chain is run at an **auxiliary cap** `c'`, an ordinal with `c < c' < α` self-visible at the
arity `m` of the donor (`Label.exists_lt_lt_isSelfVisible`); at the end the observation at the
requested cutoff `c` is read off by capping (`StageType.mem_receivingFamily_of_le`).  The
**received root** of a step is the tuple received so far: it extends `t` literally, and its type
`q` agrees with the corresponding face of `D` at `c'`.  Each step has two parts.

* **Repair** (`StageType.exists_restrictFace_eq_mem_receivingFamily`): the type `q` of the
  received root agrees with the face of `D₁` along the initial segment only at the cap.
  Bountifulness of the scheme of `D₁` extends the labels of `q` to a lawful section with the
  observation of `D₁` at `c'`; its stage reduction is a legal coface `d` of `q` with the
  observation of `D₁` at `c'`.
* **Receive**: finite-cut receiving over the received root, with donor `d` at the permitted cutoff
  `c'`, gives one new point; the extended tuple is the next received root, and its type agrees
  with `d`, hence with `D₁`, at `c'` (`StageType.mem_receivingFamily_trans`).

When every point of `D` has been added, the received root enumerates the points of `D` in the
order of the chain; reindexing it along the final face, now a bijection (exact consistency,
`eval_equiv_trans_of_eval`) gives a tuple `u` with `g.trans u = t` and a type in the receiving
family of `D` (`StageType.reindex_mem_receivingFamily`).

**Where literal restriction could be lost.**

* *The next donor is not a coface of the received root.*  The face `D₁` of `D` restricts along
  the initial segment to the face `p'` of `D` along `g`, whereas the received root has a type `q`
  that agrees with `p'` only below the cap: labels at or above the cap may differ, and
  some may be the formal top.  In general `q ≠ p'`, so `D₁` is not a coface of `q` and finite-cut
  receiving does not apply to it.  The repair replaces `D₁` by a coface `d` of `q`.
* *The requested cutoff cannot be the repair cap.*  Bountifulness extends lawful sections only at
  caps self-visible at the arity of the scheme, and a permitted cutoff need not be self-visible
  at any positive arity: `0` is not, and neither is the cutoff `λ_η = ω + ω · η` of the transfer
  of `VaughtConjecture.Expansion.Agreement`, whose finite part is `0` (`Label.isSelfVisible_coe`).
  The auxiliary cap `c'` is self-visible at the arity `m` of `D`, hence at every arity of the
  chain (`Label.IsSelfVisible.mono`).
* *Agreement is kept at the auxiliary cap through the chain.*  If a step received only at `c`,
  the next repair, at `c'`, would lack its hypothesis (agreement of `q` with `p'` at `c'`).  So
  every step receives at `c'`, which is a permitted cutoff because `c' < α`; this is why `c'`
  is an ordinal strictly below the stage, and not the formal top, which is self-visible but not
  permitted.
* *The root `t` itself* is never lost: each step extends the received root literally, and the
  composite embeddings agree by `Fin.Embedding.init_snoc`.
* *The order of the chain and the coordinates of `D`* differ; the final reindexing along a
  bijection is where exact consistency is used, and it is the only place.

**Hypotheses.**  The stage is zero or a limit (`Order.IsSuccPrelimit α`): the repaired type is a
stage reduction of a lawful section (`StageType.ofIsLawful`), and the auxiliary cap exists
strictly between `c` and `α`.  At stage zero there are no permitted cutoffs, so the statement is
vacuous there.  Exact consistency (`IsConsistent`) is used once, in the final reindexing: when `g`
is a permutation of the coordinates of the root, the requested tuple is a permutation of `t`,
which without permutation invariance may be untyped.

**Status.**  The reduction of finite-extension receiving to finite-cut receiving is proved here.
Finite-cut receiving of models, (R1) of the table of Layer 3, is not proved; through
`Expansion.FiniteCutReceiving` it is the remaining hypothesis of the transfer of
`VaughtConjecture.Expansion.Agreement`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Realization

open Finset Label StageType

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Receiving along the donor's plan, at a self-visible cap.**  Let `R` have the finite-cut
receiving property and be exactly consistent at a stage that is zero or a limit, let `D` be a
legal stage type on `m` points, and let `c` be a permitted cutoff self-visible at `m`.  If a root
`t` has a type `p` that agrees at `c` with the face `p'` of `D` along `g`, then some tuple `u`
extends `t` along `g` literally and has a type that agrees with `D` at `c`.  The proof is by
induction on the number `m - n` of new points; at `p = p'` this is finite-extension receiving at
the cap `c`. -/
theorem HasFiniteCutReceiving.exists_extend_of_mem_receivingFamily
    (hrec : R.HasFiniteCutReceiving) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α)
    {m : ℕ} {D : StageType.{u} α m} (hD : D.IsLegal)
    {c : Label.{u}} (hc : IsPermittedCutoff α c) (hcv : IsSelfVisible m c)
    {n : ℕ} {t : Fin n ↪ M} {p : StageType.{u} α n} (ht : R.eval t = some p)
    {g : Fin n ↪ Fin m} {p' : StageType.{u} α n} (hg : restrictFace g D = some p')
    (hp : p ∈ receivingFamily p' c) :
    ∃ u : Fin m ↪ M, g.trans u = t ∧ ∃ q ∈ receivingFamily D c, R.eval u = some q := by
  induction hk : m - n using Nat.strong_induction_on generalizing n t p p' g with
  | _ k ih =>
    subst hk
    by_cases hsurj : Function.Surjective g
    · -- The face is the whole donor: `D` is `p'` transported along the inverse of `g`, and the
      -- root, reindexed along the inverse of `g`, is received.
      set G := Equiv.ofBijective g ⟨g.injective, hsurj⟩
      have hDp : p'.reindex G.symm = D := by
        have h := map_reindex_restrictFace D g G.symm
        rw [hg, Option.map_some] at h
        have hid : G.symm.toEmbedding.trans g = Function.Embedding.refl (Fin m) :=
          Function.Embedding.ext fun i ↦ G.apply_symm_apply i
        rw [hid, restrictFace_refl] at h
        exact Option.some_injective _ h
      refine ⟨G.symm.toEmbedding.trans t, ?_, p.reindex G.symm,
        hDp ▸ reindex_mem_receivingFamily G.symm hp, eval_equiv_trans_of_eval hR ht G.symm⟩
      exact Function.Embedding.ext fun i ↦ congrArg t (G.symm_apply_apply i)
    -- A point `x` of `D` outside the face whose addition keeps the face closed.
    have hgD : univ.map g ∈ D.toCellScheme.faces := ((restrictFace_eq_some_iff D g).mp hg).1
    have hplan := D.isWellFormed.isWellFormed.isPlan
    rw [D.isWellFormed.ground_eq] at hplan
    have hne : univ.map g ≠ univ := fun he ↦ hsurj fun y ↦ by
      have hy : y ∈ univ.map g := he ▸ mem_univ y
      simpa using hy
    obtain ⟨x, hx, hxD⟩ := hplan.exists_insert_mem hgD hne
    have hx' : x ∉ Set.range g := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set g' := Fin.Embedding.snoc g hx'
    have hgg' : Fin.castSuccEmb.trans g' = g := Fin.Embedding.init_snoc g hx'
    have hg'D : univ.map g' ∈ D.toCellScheme.faces := by
      rwa [Fin.Embedding.univ_map_snoc]
    have hDg' : restrictFace g' D = some (D.comap g' hg'D) := restrictFace_of_mem D g' hg'D
    have hD₁p' : restrictFace Fin.castSuccEmb (D.comap g' hg'D) = some p' := by
      rw [restrictFace_trans D g' _ hDg', hgg', hg]
    have hnm : n < m := by
      have hle : n ≤ m := by simpa using Fintype.card_le_of_embedding g
      refine lt_of_le_of_ne hle fun he ↦ hsurj ?_
      exact ((Fintype.bijective_iff_injective_and_card g).mpr ⟨g.injective, by simp [he]⟩).2
    -- Repair: a coface `d` of `p` with the observation of the enlarged face at `c`.
    obtain ⟨d, hd, hdp, hdD⟩ := exists_restrictFace_eq_mem_receivingFamily hα
      (hD.restrictFace g' hDg') hD₁p' (hcv.mono hnm) hc.2.le hp
    -- Receive `d` over `t` at `c`.
    obtain ⟨v, hv, q, hq, hvq⟩ := hrec ⟨n, t, p, ht⟩ d ⟨hd, hdp⟩ c hc
    -- The remaining points.
    obtain ⟨u, hu, q', hq', huq'⟩ :=
      ih (m - (n + 1)) (by omega) hvq hDg' (mem_receivingFamily_trans hq hdD) rfl
    refine ⟨u, ?_, q', hq', huq'⟩
    rw [← hgg', Function.Embedding.trans_assoc, hu, hv]

/-- **Finite-cut receiving gives finite-extension receiving** at a stage that is zero or a limit,
for an exactly consistent realization.  For a permitted cutoff `δ` and a donor on `m` points, the
chain of `HasFiniteCutReceiving.exists_extend_of_mem_receivingFamily` is run at the auxiliary cap
`δ + (m + 1)`, strictly between `δ` and the stage and self-visible at `m`, and the observation at
`δ` is read off at the end. -/
theorem HasFiniteCutReceiving.hasFiniteExtensionReceiving (h : R.HasFiniteCutReceiving)
    (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α) : R.HasFiniteExtensionReceiving := by
  intro n m t p ht D g hD hg c hc
  obtain ⟨δ, hδ, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨c', hδc', hc'α, hc'⟩ := exists_lt_lt_isSelfVisible hα hδ m
  obtain ⟨u, hu, q, hq, huq⟩ := h.exists_extend_of_mem_receivingFamily hR hα hD
    (isPermittedCutoff_coe.mpr hc'α) hc' ht hg (self_mem_receivingFamily p _)
  exact ⟨u, hu, q, mem_receivingFamily_of_le hq (by exact_mod_cast hδc'.le), huq⟩

/-- **Finite-extension receiving is finite-cut receiving** for an exactly consistent realization
at a stage that is zero or a limit. -/
theorem hasFiniteExtensionReceiving_iff (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α) :
    R.HasFiniteExtensionReceiving ↔ R.HasFiniteCutReceiving :=
  ⟨HasFiniteExtensionReceiving.hasFiniteCutReceiving, (·.hasFiniteExtensionReceiving hR hα)⟩

/-- A model at a stage that is zero or a limit has finite-extension receiving exactly when it has
finite-cut receiving. -/
theorem IsModel.hasFiniteExtensionReceiving_iff (hR : R.IsModel) (hα : Order.IsSuccPrelimit α) :
    R.HasFiniteExtensionReceiving ↔ R.HasFiniteCutReceiving :=
  Realization.hasFiniteExtensionReceiving_iff hR.isConsistent hα

end VaughtConjecture.Realization

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.StronglyCodedAmalgamation
import VaughtConjecture.Realization.Receiving

/-!
# Receiving restricted to a class of stage types

Roadmap, Layer 3 (receiving for finite extensions) and Correspondence, item 1 (the strongly coded
legal stage types); semantic contract, item 12.  All results here are native constructions of this
repository.

**Classes.**  A **class** is a predicate `𝒮` on stage types at every stage and arity,
`𝒮 : ∀ {α n}, StageType α n → Prop`.  Three closure properties are used, each stated separately:

* **faces** (`StageType.FaceClosed`): a defined face of a member is a member;
* **same scheme** (`StageType.SchemeInvariant`): membership depends only on the scheme (rows
  included), not on the labels, at a fixed stage;
* **stage reduction** (`StageType.ReductionInvariant`): a stage type is a member exactly when its
  stage reduction to any stage that is zero or a limit is.

The two classes used are the legal stage types (`StageType.IsLegal`) and the stage types with
strongly coded rows (`CellScheme.Rows.IsStronglyCoded`).  Both have the three properties
(`StageType.faceClosed_isLegal`, `StageType.schemeInvariant_isLegal`,
`StageType.reductionInvariant_isLegal`; `StageType.faceClosed_isStronglyCoded`,
`StageType.schemeInvariant_isStronglyCoded`, `StageType.reductionInvariant_isStronglyCoded`).
Strong coding is a property of the rows, hence of the scheme, and stage reduction keeps the scheme.

**Receiving in a class.**  `Realization.HasFiniteCutReceivingIn 𝒮` is finite-cut receiving for
the cofaces in `𝒮`, and `Realization.HasFiniteExtensionReceivingIn 𝒮` is finite-extension
receiving for the legal donors in `𝒮`.  For the class of legal stage types they are the
unrestricted notions (`Realization.hasFiniteCutReceivingIn_isLegal_iff`,
`Realization.hasFiniteExtensionReceivingIn_isLegal_iff`).

**One point and many points** (`Realization.hasFiniteExtensionReceivingIn_iff`).  For a class
closed under faces and invariant under same-scheme changes of labels, an exactly consistent
realization at a stage that is zero or a limit has finite-extension receiving in the class exactly
when it has finite-cut receiving in it.  The proof is the chain of
`Realization.HasFiniteCutReceiving.exists_extend_of_mem_receivingFamily`: each step receives the
**repaired** face of the donor, which has the scheme of a face of the donor and other labels.
Face closure puts the face in the class, and same-scheme invariance puts the repaired face in the
class; face closure alone does not suffice.

**Descent along stage reduction** (`Realization.HasFiniteCutReceivingIn.reduce`).  As
`Realization.HasFiniteCutReceiving.reduce`: a coface in the class at the lower stage is lifted to a
coface at the upper stage on the same scheme with other labels; same-scheme invariance at the
lower stage and reduction invariance put the lift in the class.

**Stages.**  The literal stage `0` has no permitted cutoff, and receiving there is vacuous.  The
manuscript level zero is the block stage `blockStage 0 = ω`, a limit, where receiving is not
vacuous; it is covered by the statements at stages that are zero or a limit.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace StageType

/-! ### Closure properties of a class of stage types -/

/-- A class of stage types is **closed under faces** when every defined face of a member is a
member. -/
def FaceClosed (𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ ⦃t : StageType.{u} α n⦄ ⦃s : StageType.{u} α m⦄
    ⦃f : Fin m ↪ Fin n⦄, restrictFace f t = some s → 𝒮 t → 𝒮 s

/-- A class of stage types is **invariant under same-scheme changes** when, at a fixed stage,
membership depends only on the scheme (rows included), not on the labels. -/
def SchemeInvariant (𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n : ℕ⦄ ⦃t s : StageType.{u} α n⦄, s.toScheme = t.toScheme → 𝒮 t → 𝒮 s

/-- A class of stage types is **invariant under stage reduction** when a stage type is a member
exactly when its stage reduction to a stage that is zero or a limit is. -/
def ReductionInvariant (𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop) : Prop :=
  ∀ ⦃α β : Ordinal.{u}⦄ ⦃n : ℕ⦄ (t : StageType.{u} α n) (hβ : Order.IsSuccPrelimit β),
    𝒮 (t.reduce hβ) ↔ 𝒮 t

/-- The legal stage types are closed under faces. -/
theorem faceClosed_isLegal : FaceClosed.{u} fun t ↦ t.IsLegal :=
  fun _ _ _ _ _ _ h ht ↦ ht.restrictFace _ h

/-- Legality is a property of the scheme. -/
theorem schemeInvariant_isLegal : SchemeInvariant.{u} fun t ↦ t.IsLegal :=
  fun _ _ _ _ h ht ↦ by
    change Scheme.IsLegal _
    rw [h]
    exact ht

/-- Stage reduction keeps legality, in both directions: it keeps the scheme. -/
theorem reductionInvariant_isLegal : ReductionInvariant.{u} fun t ↦ t.IsLegal :=
  fun _ _ _ _ _ ↦ Iff.rfl

/-- The stage types with strongly coded rows are closed under faces
(`StageType.isStronglyCoded_of_restrictFace`). -/
theorem faceClosed_isStronglyCoded : FaceClosed.{u} fun t ↦ t.rows.IsStronglyCoded :=
  fun _ _ _ _ _ _ h ht ↦ isStronglyCoded_of_restrictFace h ht

/-- Strong coding is a property of the rows, which are part of the scheme. -/
theorem schemeInvariant_isStronglyCoded : SchemeInvariant.{u} fun t ↦ t.rows.IsStronglyCoded :=
  fun _ _ _ s h ht ↦ by
    change s.toScheme.rows.IsStronglyCoded
    rw [h]
    exact ht

/-- Stage reduction keeps strong coding, in both directions: it keeps the rows. -/
theorem reductionInvariant_isStronglyCoded :
    ReductionInvariant.{u} fun t ↦ t.rows.IsStronglyCoded :=
  fun _ _ _ _ _ ↦ Iff.rfl

end StageType

namespace Realization

open StageType

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}
  {𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop}

/-! ### Receiving in a class -/

section Definitions

variable (𝒮) (R)

/-- **Finite-cut receiving in a class** `𝒮`: over every occurrence, for every coface `d` of its
type in `𝒮` and every permitted cutoff `c`, some point extends the occurrence to one with a type
on the scheme of `d` with the observation of `d` at `c`. -/
def HasFiniteCutReceivingIn : Prop :=
  ∀ x : R.Occurrence, ∀ d ∈ x.type.cofaces, 𝒮 d → ∀ c : Label.{u}, IsPermittedCutoff α c →
    R.RealizesOver x.tuple (receivingFamily d c)

/-- **Finite-extension receiving in a class** `𝒮`: for every actual root `t` of type `p`, every
legal stage type `D` in `𝒮` restricting to `p` along an embedding `g` of coordinates, and every
permitted cutoff `c`, some injective tuple `u` extends `t` along `g` literally and has a type in
the receiving family of `D` at `c`. -/
def HasFiniteExtensionReceivingIn : Prop :=
  ∀ ⦃n m : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
    ∀ (D : StageType.{u} α m) (g : Fin n ↪ Fin m), D.IsLegal → 𝒮 D →
      restrictFace g D = some p → ∀ c : Label.{u}, IsPermittedCutoff α c →
        ∃ u : Fin m ↪ M, g.trans u = t ∧ ∃ q ∈ receivingFamily D c, R.eval u = some q

end Definitions

/-- **Finite-cut receiving in the class of legal stage types is finite-cut receiving**: every
coface is legal. -/
theorem hasFiniteCutReceivingIn_isLegal_iff :
    R.HasFiniteCutReceivingIn (fun t ↦ t.IsLegal) ↔ R.HasFiniteCutReceiving :=
  ⟨fun h x d hd c hc ↦ h x d hd hd.1 c hc, fun h x d hd _ c hc ↦ h x d hd c hc⟩

/-- **Finite-extension receiving in the class of legal stage types is finite-extension
receiving**. -/
theorem hasFiniteExtensionReceivingIn_isLegal_iff :
    R.HasFiniteExtensionReceivingIn (fun t ↦ t.IsLegal) ↔ R.HasFiniteExtensionReceiving :=
  ⟨fun h _ _ t p ht D g hD hg c hc ↦ h t p ht D g hD hD hg c hc,
    fun h _ _ t p ht D g hD _ hg c hc ↦ h t p ht D g hD hg c hc⟩

/-- Receiving in a class is receiving for the members of every subclass. -/
theorem HasFiniteCutReceivingIn.mono {𝒯 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop}
    (h : R.HasFiniteCutReceivingIn 𝒮)
    (h𝒯 : ∀ ⦃α : Ordinal.{u}⦄ ⦃n : ℕ⦄ (t : StageType.{u} α n), 𝒯 t → 𝒮 t) :
    R.HasFiniteCutReceivingIn 𝒯 :=
  fun x d hd hd𝒯 c hc ↦ h x d hd (h𝒯 d hd𝒯) c hc

/-- Finite-cut receiving gives finite-cut receiving in every class. -/
theorem HasFiniteCutReceiving.hasFiniteCutReceivingIn (h : R.HasFiniteCutReceiving) :
    R.HasFiniteCutReceivingIn 𝒮 :=
  fun x d hd _ c hc ↦ h x d hd c hc

/-- Finite-extension receiving gives finite-extension receiving in every class. -/
theorem HasFiniteExtensionReceiving.hasFiniteExtensionReceivingIn
    (h : R.HasFiniteExtensionReceiving) : R.HasFiniteExtensionReceivingIn 𝒮 :=
  fun _ _ t p ht D g hD _ hg c hc ↦ h t p ht D g hD hg c hc

/-- **Finite-extension receiving in a class gives finite-cut receiving in it**: the case of a donor
on one more point, along the initial segment. -/
theorem HasFiniteExtensionReceivingIn.hasFiniteCutReceivingIn
    (h : R.HasFiniteExtensionReceivingIn 𝒮) : R.HasFiniteCutReceivingIn 𝒮 :=
  fun x d hd hd𝒮 c hc ↦ h x.tuple x.type x.eval_tuple d Fin.castSuccEmb hd.1 hd𝒮 hd.2 c hc

/-! ### One point and many points in a class -/

/-- **Receiving along the donor's plan in a class, at a self-visible cap** (native construction):
`Realization.HasFiniteCutReceiving.exists_extend_of_mem_receivingFamily` with the donor `D` in a
class `𝒮` closed under faces and invariant under same-scheme changes, and finite-cut receiving in
`𝒮` only.  Each step receives the repaired face of `D`, which has the scheme of a face of `D`. -/
theorem HasFiniteCutReceivingIn.exists_extend_of_mem_receivingFamily
    (h𝒮f : StageType.FaceClosed 𝒮) (h𝒮s : StageType.SchemeInvariant 𝒮)
    (hrec : R.HasFiniteCutReceivingIn 𝒮) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α)
    {m : ℕ} {D : StageType.{u} α m} (hD : D.IsLegal) (hD𝒮 : 𝒮 D)
    {c : Label.{u}} (hc : IsPermittedCutoff α c) (hcv : IsSelfVisible m c)
    {n : ℕ} {t : Fin n ↪ M} {p : StageType.{u} α n} (ht : R.eval t = some p)
    {g : Fin n ↪ Fin m} {p' : StageType.{u} α n} (hg : restrictFace g D = some p')
    (hp : p ∈ receivingFamily p' c) :
    ∃ u : Fin m ↪ M, g.trans u = t ∧ ∃ q ∈ receivingFamily D c, R.eval u = some q := by
  induction hk : m - n using Nat.strong_induction_on generalizing n t p p' g with
  | _ k ih =>
    subst hk
    by_cases hsurj : Function.Surjective g
    · -- The face is the whole donor: `D` is `p'` transported along the inverse of `g`.
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
    -- Repair: a coface `d` of `p` on the scheme of the face of `D` along `g'`.
    obtain ⟨d, hd, hdp, hdD⟩ := exists_restrictFace_eq_mem_receivingFamily hα
      (hD.restrictFace g' hDg') hD₁p' (hcv.mono hnm) hc.2.le hp
    -- The repaired face is in the class: face closure, then same-scheme invariance.
    have hd𝒮 : 𝒮 d := h𝒮s hdD.1 (h𝒮f hDg' hD𝒮)
    -- Receive `d` over `t` at `c`.
    obtain ⟨v, hv, q, hq, hvq⟩ := hrec ⟨n, t, p, ht⟩ d ⟨hd, hdp⟩ hd𝒮 c hc
    -- The remaining points.
    obtain ⟨u, hu, q', hq', huq'⟩ :=
      ih (m - (n + 1)) (by omega) hvq hDg' (mem_receivingFamily_trans hq hdD) rfl
    refine ⟨u, ?_, q', hq', huq'⟩
    rw [← hgg', Function.Embedding.trans_assoc, hu, hv]

/-- **Finite-cut receiving in a class gives finite-extension receiving in it** (native
construction), at a stage that is zero or a limit, for an exactly consistent realization and a
class closed under faces and invariant under same-scheme changes. -/
theorem HasFiniteCutReceivingIn.hasFiniteExtensionReceivingIn (h𝒮f : StageType.FaceClosed 𝒮)
    (h𝒮s : StageType.SchemeInvariant 𝒮) (h : R.HasFiniteCutReceivingIn 𝒮) (hR : R.IsConsistent)
    (hα : Order.IsSuccPrelimit α) : R.HasFiniteExtensionReceivingIn 𝒮 := by
  intro n m t p ht D g hD hD𝒮 hg c hc
  obtain ⟨δ, hδ, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨c', hδc', hc'α, hc'⟩ := exists_lt_lt_isSelfVisible hα hδ m
  obtain ⟨u, hu, q, hq, huq⟩ := h.exists_extend_of_mem_receivingFamily h𝒮f h𝒮s hR hα hD hD𝒮
    (isPermittedCutoff_coe.mpr hc'α) hc' ht hg (self_mem_receivingFamily p _)
  exact ⟨u, hu, q, mem_receivingFamily_of_le hq (by exact_mod_cast hδc'.le), huq⟩

/-- **One point and many points in a class** (native construction): for a class `𝒮` closed under
faces (`StageType.FaceClosed`) and invariant under same-scheme changes
(`StageType.SchemeInvariant`), an exactly consistent realization at a stage that is zero or a limit
has finite-extension receiving in `𝒮` exactly when it has finite-cut receiving in `𝒮`. -/
theorem hasFiniteExtensionReceivingIn_iff (h𝒮f : StageType.FaceClosed 𝒮)
    (h𝒮s : StageType.SchemeInvariant 𝒮) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α) :
    R.HasFiniteExtensionReceivingIn 𝒮 ↔ R.HasFiniteCutReceivingIn 𝒮 :=
  ⟨HasFiniteExtensionReceivingIn.hasFiniteCutReceivingIn,
    (·.hasFiniteExtensionReceivingIn h𝒮f h𝒮s hR hα)⟩

/-- **One point and many points for strongly coded donors** (native construction): an exactly
consistent realization at a stage that is zero or a limit has finite-extension receiving for the
legal donors with strongly coded rows exactly when it has finite-cut receiving for the cofaces with
strongly coded rows. -/
theorem hasFiniteExtensionReceivingIn_isStronglyCoded_iff (hR : R.IsConsistent)
    (hα : Order.IsSuccPrelimit α) :
    R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) ↔
      R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) :=
  hasFiniteExtensionReceivingIn_iff StageType.faceClosed_isStronglyCoded
    StageType.schemeInvariant_isStronglyCoded hR hα

/-! ### Descent along stage reduction in a class -/

/-- **Receiving in a class descends along stage reduction** (native construction), cutoff by
cutoff: as `Realization.HasFiniteCutReceiving.reduce`, for a class `𝒮` invariant under same-scheme
changes and under stage reduction.  The lift of a coface in `𝒮` at `β` is a coface at `α` on the
same scheme; its reduction to `β` has the scheme of the coface, hence is in `𝒮`, and so is the lift
(`StageType.ReductionInvariant`).  At the literal stage `β = 0` there is no permitted cutoff and
the statement is vacuous; at the block stage `blockStage 0 = ω` it is not. -/
theorem HasFiniteCutReceivingIn.reduce {β : Ordinal.{u}} (h𝒮s : StageType.SchemeInvariant 𝒮)
    (h𝒮r : StageType.ReductionInvariant 𝒮) (h : R.HasFiniteCutReceivingIn 𝒮)
    (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccPrelimit β) (hβα : β ≤ α) :
    (R.reduce hβ).HasFiniteCutReceivingIn 𝒮 := by
  intro y d hd hd𝒮 c hc
  obtain ⟨x, rfl⟩ := Occurrence.exists_reduce_eq hβ y
  obtain ⟨δ, hδ, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨c', hδc', hc'β, hc'⟩ := exists_lt_lt_isSelfVisible hβ hδ (x.arity + 1)
  have hc'le : (c' : Label.{u}) ≤ β := by exact_mod_cast hc'β.le
  have hδc : (δ : Label.{u}) ≤ c' := by exact_mod_cast hδc'.le
  obtain ⟨ρ, hρ, hρc, hext⟩ := exists_isLawful_lift (p := x.type) hβ hd.1 hd.2 hc' hc'le
  have hlift := ofIsLawful_mem_cofaces_of_lift hα hβ hd hρ hext
  -- the lift has the scheme of `d`, so its reduction to `β` is in the class, and so is the lift
  have hlift𝒮 : 𝒮 (StageType.ofIsLawful hα d.toScheme d.isWellFormed d.isCoded ρ hρ) :=
    (h𝒮r _ hβ).mp (h𝒮s (t := d) rfl hd𝒮)
  obtain ⟨u, hu, q, hq, hqe⟩ := h x _ hlift hlift𝒮 c'
    (isPermittedCutoff_coe.mpr (hc'β.trans_le hβα))
  refine ⟨u, hu, q.reduce hβ, ⟨hq.1, fun i j hij ↦ ?_⟩,
    congrArg (Option.map (StageType.reduce · hβ)) hqe⟩
  -- agreement at `c'`, then at `δ ≤ c'`
  have key : min (q.label i) c' = min (d.label j) c' := by
    rw [hq.2 i j hij, ofIsLawful_label, min_reduce_of_le (hc'le.trans (by exact_mod_cast hβα)),
      hρc j]
  change min (Label.reduce β (q.label i)) _ = _
  rw [min_reduce_of_le (hδc.trans hc'le)]
  simpa only [min_assoc, min_eq_right hδc] using congrArg (min · (δ : Label.{u})) key

/-- **Strongly coded receiving descends along stage reduction** (native construction):
`Realization.HasFiniteCutReceivingIn.reduce` for the stage types with strongly coded rows. -/
theorem HasFiniteCutReceivingIn.reduce_isStronglyCoded {β : Ordinal.{u}}
    (h : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccPrelimit β) (hβα : β ≤ α) :
    (R.reduce hβ).HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded :=
  h.reduce StageType.schemeInvariant_isStronglyCoded StageType.reductionInvariant_isStronglyCoded
    hα hβ hβα

end Realization

end VaughtConjecture

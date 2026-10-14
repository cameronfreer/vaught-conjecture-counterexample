/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Presentation.StableLabelInvariance
import VaughtConjecture.Correspondence.Presentation.Targets
import VaughtConjecture.Extension.StronglyCodedForcingDonors

/-!
# Lifting a coherent renaming through one block

Native construction throughout.  Write `λ_η = blockStage η`.

**Theorem** (`liftingTarget`).  The target `LiftingTarget η M` holds for every `η` and `M`: for
realizations `R`, `R'` at `λ_{η+1}` satisfying, each, the premises of the restricted next-block
determination (types with strongly coded rows, exact consistency, covering, legal types, and
finite-extension receiving for the strongly coded legal donors), every coherent renaming `c` of
their reductions to `λ_η` is, with the **same** bijections of cells, a coherent renaming of `R`
and `R'`.  No premise is added, and no equality of class readings at `λ_{η+1}` is assumed.

**Proof.**

* **The lifted family** (`Realization.CoherentRenaming.ofReduce`).  Stage reduction keeps the
  cells, the schemes and the face cell maps.  So the bijections of `c` form a coherent renaming of
  `R` and `R'` as soon as they preserve the labels at `λ_{η+1}`.  The schemes are preserved
  because the renaming equation of the reductions has the same schemes.  The face-map
  commutation is that of `c`, since the face cell maps of a type and of its reduction are the
  same map.
* **Labels** (`Realization.label_cellEquiv_eq_of_stronglyCoded`).  Let `σ` be the bijection of
  `c` at a tuple `t` typed by `p` in `R` and by `q` in `R'`, and `i` a cell of `p`.  The renaming
  equation of the reductions gives `reduce (q.label (σ i)) = reduce (p.label i)` at `λ_η`.
  * **Proper reduced label** (not the formal top): both labels are below `λ_η`, so they equal
    their reductions, and are equal.
  * **Top reduced label**: both reduced labels are the formal top.  By restricted normalization
    (`Realization.label_eq_stableLabel_stronglyCoded`, whose premises are those of the target),
    `p.label i` is the stable label of the reduction of `R` at `(t, p↓, i)` and `q.label (σ i)` is
    the stable label of the reduction of `R'` at `(t, q↓, σ i)`.  By stable-label invariance
    (`Realization.stableLabel_eq_of_coherentRenaming`, for the exactly consistent reductions and
    `c`), these are equal.
-/

universe u v

namespace VaughtConjecture

open Finset StageType

namespace Realization

variable {β : Ordinal.{u}} {M : Type v} {R R' : Realization.{u, v} β M}

namespace CoherentRenaming

variable {α : Ordinal.{u}} {R₁ R₁' : Realization.{u, v} α M}

/-- **A coherent renaming of the reductions preserving the labels is a coherent renaming**
(native construction): if the bijections of a coherent renaming `c` of the reductions of `R₁`,
`R₁'` to a stage `β` that is zero or a limit preserve the labels of the types of `R₁` and `R₁'`,
they form, unchanged, a coherent renaming of `R₁` and `R₁'`.  Stage reduction keeps the cells,
the schemes and the face cell maps. -/
noncomputable def ofReduce (hβ : Order.IsSuccPrelimit β)
    (c : CoherentRenaming (R₁.reduce hβ) (R₁'.reduce hβ))
    (hlab : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) ⦃p q : StageType.{u} α n⦄ (hp : R₁.eval t = some p)
      (hq : R₁'.eval t = some q) (i : Fin p.card),
      q.label (c.cellEquiv t (R₁.reduce_eval_of_eval_eq_some hβ hp)
        (R₁'.reduce_eval_of_eval_eq_some hβ hq) i) = p.label i) :
    CoherentRenaming R₁ R₁' where
  isSome_eval_iff _ t := by
    rw [← isSome_reduce_eval R₁ hβ t, ← isSome_reduce_eval R₁' hβ t]
    exact c.isSome_eval_iff t
  renamingAt _ t _ _ hp hq :=
    { toEquiv := c.cellEquiv t (R₁.reduce_eval_of_eval_eq_some hβ hp)
        (R₁'.reduce_eval_of_eval_eq_some hβ hq)
      renameCells_eq := by
        have hred := (c.renamingAt t (R₁.reduce_eval_of_eval_eq_some hβ hp)
          (R₁'.reduce_eval_of_eval_eq_some hβ hq)).renameCells_eq
        refine StageType.ext (congrArg (fun x : StageType.{u} β _ ↦ x.toScheme) hred)
          fun i j hij ↦ ?_
        obtain rfl := Fin.ext hij
        exact hlab t hp hq i }
  faceCellMap_comm _ _ t f p q p₀ q₀ hp hq hp₀ hq₀ hfp hfq i := by
    have hfp' : restrictFace f (p.reduce hβ) = some (p₀.reduce hβ) := by
      rw [restrictFace_reduce, hfp, Option.map_some]
    have hfq' : restrictFace f (q.reduce hβ) = some (q₀.reduce hβ) := by
      rw [restrictFace_reduce, hfq, Option.map_some]
    exact c.faceCellMap_comm t f (R₁.reduce_eval_of_eval_eq_some hβ hp)
      (R₁'.reduce_eval_of_eval_eq_some hβ hq) (R₁.reduce_eval_of_eval_eq_some hβ hp₀)
      (R₁'.reduce_eval_of_eval_eq_some hβ hq₀) hfp' hfq' i

/-- The bijections of `ofReduce` are those of the coherent renaming of the reductions.
Native construction. -/
theorem cellEquiv_ofReduce (hβ : Order.IsSuccPrelimit β)
    (c : CoherentRenaming (R₁.reduce hβ) (R₁'.reduce hβ)) (hlab) {n : ℕ} (t : Fin n ↪ M)
    {p q : StageType.{u} α n} (hp : R₁.eval t = some p) (hq : R₁'.eval t = some q) :
    (ofReduce hβ c hlab).cellEquiv t hp hq =
      c.cellEquiv t (R₁.reduce_eval_of_eval_eq_some hβ hp)
        (R₁'.reduce_eval_of_eval_eq_some hβ hq) :=
  rfl

end CoherentRenaming

section Labels

variable {η : Ordinal.{u}} {R R' : Realization.{u, v} (blockStage (η + 1)) M}

/-- **The bijections of a coherent renaming of the reductions preserve the labels at
`λ_{η+1}`** (native construction), for realizations `R`, `R'` at `λ_{η+1}` each with types with
strongly coded rows, exact consistency, legal types, and finite-extension receiving for the
strongly coded legal donors.  A cell whose reduced label is proper keeps it, by the renaming
equation of the reductions; a cell whose reduced label is the formal top has as label the stable
label of the reduction (`Realization.label_eq_stableLabel_stronglyCoded`), and stable labels are
invariant under coherent renaming (`Realization.stableLabel_eq_of_coherentRenaming`). -/
theorem label_cellEquiv_eq_of_stronglyCoded
    (h𝒮 : ∀ x : R.Occurrence, x.type.rows.IsStronglyCoded) (hR : R.IsConsistent)
    (hl : R.HasLegalTypes) (hrec : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (h𝒮' : ∀ x : R'.Occurrence, x.type.rows.IsStronglyCoded) (hR' : R'.IsConsistent)
    (hl' : R'.HasLegalTypes)
    (hrec' : R'.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (c : CoherentRenaming (R.reduce (isSuccPrelimit_blockStage η))
      (R'.reduce (isSuccPrelimit_blockStage η)))
    {n : ℕ} (t : Fin n ↪ M) {p q : StageType.{u} (blockStage (η + 1)) n}
    (hp : R.eval t = some p) (hq : R'.eval t = some q) (i : Fin p.card) :
    q.label (c.cellEquiv t (R.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hp)
      (R'.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hq) i) = p.label i := by
  have hred := (c.renamingAt t (R.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hp)
    (R'.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hq)).renameCells_eq
  have hlr : Label.reduce (blockStage η) (q.label (c.cellEquiv t
      (R.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hp)
      (R'.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hq) i)) =
      Label.reduce (blockStage η) (p.label i) :=
    label_congr hred rfl
  by_cases htop : Label.reduce (blockStage η) (p.label i) = ⊤
  · -- top reduced label: restricted normalization and stable-label invariance
    have hp' : (p.reduce (isSuccPrelimit_blockStage η)).label i = ⊤ := htop
    have hq' : (q.reduce (isSuccPrelimit_blockStage η)).label (c.cellEquiv t
        (R.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hp)
        (R'.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hq) i) = ⊤ :=
      hlr.trans htop
    rw [label_eq_stableLabel_stronglyCoded hR' hl' h𝒮' hrec' (covers_of_eval t hq) _ hq',
      label_eq_stableLabel_stronglyCoded hR hl h𝒮 hrec (covers_of_eval t hp) i hp']
    exact (stableLabel_eq_of_coherentRenaming (α := blockStage (η + 1))
      (hβ := isSuccPrelimit_blockStage η) (hR.reduce _) (hR'.reduce _) c t
      (R.reduce_eval_of_eval_eq_some _ hp) (R'.reduce_eval_of_eval_eq_some _ hq) i).symm
  · -- proper reduced label: the renaming equation of the reductions
    have hpl : p.label i < (blockStage η : Label.{u}) :=
      lt_of_not_ge (mt Label.reduce_eq_top_iff.mpr htop)
    have hql : q.label (c.cellEquiv t
        (R.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hp)
        (R'.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hq) i) <
          (blockStage η : Label.{u}) :=
      lt_of_not_ge (mt Label.reduce_eq_top_iff.mpr fun h ↦ htop (hlr.symm.trans h))
    rw [← Label.reduce_of_lt hql, hlr, Label.reduce_of_lt hpl]

end Labels

end Realization

/-- **The lifting target holds** (native construction): `LiftingTarget η M` for every `η` and `M`.
Every coherent renaming of the reductions to `λ_η` of two realizations at `λ_{η+1}` satisfying the
premises of `Realization.eq_stableCandidate_stronglyCoded` is, with the same bijections, a
coherent renaming of the realizations (`Realization.CoherentRenaming.ofReduce`,
`Realization.label_cellEquiv_eq_of_stronglyCoded`).  Covering is not used.  No equality of class
readings at `λ_{η+1}` is assumed; it follows from the conclusion
(`Realization.classReading_eq_of_coherentRenaming`). -/
theorem liftingTarget (η : Ordinal.{u}) (M : Type v) : LiftingTarget η M :=
  fun _ _ h𝒮 hR _ hl hrec h𝒮' hR' _ hl' hrec' c ↦
    ⟨Realization.CoherentRenaming.ofReduce _ c fun _ t _ _ hp hq i ↦
      Realization.label_cellEquiv_eq_of_stronglyCoded h𝒮 hR hl hrec h𝒮' hR' hl' hrec' c t hp hq i,
      fun _ _ _ _ _ _ ↦ rfl⟩

end VaughtConjecture

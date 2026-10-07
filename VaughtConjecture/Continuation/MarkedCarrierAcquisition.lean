/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCap
import VaughtConjecture.Continuation.MarkedCarrier
import VaughtConjecture.Continuation.RestrictedHollow
import VaughtConjecture.Realization.PrivateContext

/-!
# Acquisition of marked-carrier contexts, and (R3) from marked carriers

Roadmap, Layer 3 ((R3) of the table of 3.4) and Layer 4 (cover-hollowness).

**Acquisition** (`Realization.IsModel.exists_isMarkedCarrierContext`, compiled in this repository
(theorem named)).  In a model at a block stage `λ_ξ` that is cover-hollow and has unbounded
growth, every cover of a type `t` extends, for every donor `d`, to a cover of a marked-carrier
context for `d` (`StageType.IsMarkedCarrierContext`).  The construction synchronizes, in one
occurrence given by covering: the private context of the root for the donor (its reference cells,
`Realization.IsModel.exists_privateContext`), an occurrence of large top grade, and for every top
of the root a rooted cover forcing `n + 1` there, which cover-hollowness provides
(`Realization.IsTopAnchor`).  Forcing passes to the occurrence along the faces
(`StageType.ForcesThreshold.trans_face`), and the rows of a top cap read it
(`StageType.IsMarker.visibilityReplace_le_of_forcesThreshold`, from
`StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`).  The clauses of modelhood
used are uniformity, high-arity dominance, exact consistency, covering and legal types; neither
generalized saturation nor any receiving hypothesis is used.

**(R3) from marked carriers** (`Realization.hollowReceiving_of_hasMarkedCarriers`, compiled in this
repository (theorem named)): `Realization.HollowReceiving` for `Realization.IsCoverHollowAtBlock`
holds if `StageType.HasMarkedCarriers` (open) holds at every block stage, through the acquisition,
scheme determination by a marked carrier
(`StageType.HasMarkedCarriers.exists_coface_isDeterminedWithin`) and generalized saturation.
The restricted form follows (`Realization.hollowReceiving_withoutRigidCore_of_hasMarkedCarriers`),
and so does the form from
`StageType.HasPrescribedFullRows` with the compatibility of the marked prescriptions
(`Realization.hollowReceiving_of_hasPrescribedFullRows`).  These are conditional: marked carriers,
prescribed full rows and that compatibility are open, and no implication from the coatom
extension property is compiled.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace StageType

variable {α β : Ordinal.{u}} {m n : ℕ} {q : StageType.{u} β m} {c r : Fin q.card}

/-- **Forcing at the root tops gives the row inequality at a given marker**: let `β` be a limit,
`β + ω ≤ α`, `q` a legal stage type at `β` restricting along `f : Fin n ↪ Fin m` to `p`, `c` a
top cap of `q` and `r` a marker of `c`.  If `(q, f)` forces `n + 1` at every cell of `p` labelled
`⊤`, then `visibilityReplace N (n + 1) (q.rowAt c r) ≤ q.rowAt c a` at every cell `a` of `q`
visible through `f` and labelled `⊤`. -/
theorem IsMarker.visibilityReplace_le_of_forcesThreshold (hβ : Order.IsSuccLimit β)
    (hα : β + ω ≤ α) (hq : q.IsLegal) {f : Fin n ↪ Fin m} {p : StageType.{u} β n}
    (hp : restrictFace f q = some p) (hc : q.IsTopCap c) (hr : q.IsMarker c r)
    (hforce : ∀ d : Fin p.card, p.label d = ⊤ →
      ForcesThreshold α hβ.isSuccPrelimit q f p d (n + 1)) :
    ∀ a ∈ q.visibleCells f, q.label a = ⊤ →
      visibilityReplace (q.toCellScheme.grade c) (n + 1) (q.rowAt c r) ≤ q.rowAt c a := by
  intro a ha hat
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β n ↦ s.card) hqp
  obtain ⟨i, rfl⟩ : a ∈ Set.range (q.cellMap f) := by
    rw [Scheme.range_cellMap]
    exact ha
  set d : Fin p.card := ⟨i, lt_of_lt_of_eq i.2 hcard⟩
  have hd : p.label d = ⊤ := by
    rw [← hat]
    exact (label_congr hqp.symm rfl).trans (comap_label q f hf i)
  exact (ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hr (hforce d hd) hd
    fun i' hi' ↦ congrArg (q.cellMap f) (Fin.ext hi')).2

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- A label other than `⊥` and `⊤` is an ordinal. -/
private theorem exists_coe_eq_of_ne {x : Label.{u}} (hb : x ≠ ⊥) (ht : x ≠ ⊤) :
    ∃ o : Ordinal.{u}, x = o := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hb
  | coe o => exact ⟨o, rfl⟩
  | top => exact absurd rfl ht

/-- **Acquisition of a marked-carrier context.**  Let `R` be a model at the block stage `λ_ξ`,
cover-hollow, with unbounded growth (`R.topGradeSup = ⊤`).  Over every cover `c` of a type `t` on
`n` points and for every donor `d` on `n + 1` points, some cover `c'` of a type `t'` restricts
along an embedding `h` to `c`, and `t'` is a marked-carrier context along `h` for `d`.

The context is assembled in one occurrence `Z` containing: the private context of the root for the
donor (`Realization.IsModel.exists_privateContext`: reference cells for the proper labels of `d`),
an occurrence of top grade above the arity of the private context (unbounded growth), and, for
every cell of the root labelled `⊤`, a rooted cover forcing `n + 1` there (cover-hollowness).  By
covering one occurrence contains all of them; forcing is monotone along extensions
(`StageType.ForcesThreshold.trans_face`), the reference cells keep their labels and grades, and
the top grade only grows.  A top cap of the type of `Z` has the top grade, above `n + 1` and above
the finite parts and grades of the reference cells; with a marker, forcing gives the row
inequality at the root (`StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`).

Of modelhood, uniformity, high-arity dominance, exact consistency, covering and legal types are
used; generalized saturation and the bottom pattern are not. -/
theorem IsModel.exists_isMarkedCarrierContext (hR : R.IsModel) (hhol : R.IsCoverHollow)
    (htop : R.topGradeSup = ⊤) {n : ℕ} {t : StageType.{u} (blockStage ξ) n} {c : Fin n → M}
    (hc : R.Covers t c) (d : StageType.{u} (blockStage ξ) (n + 1)) :
    ∃ (k : ℕ) (t' : StageType.{u} (blockStage ξ) k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ t'.IsMarkedCarrierContext h d := by
  classical
  have hβ := isSuccLimit_blockStage ξ
  have hα : blockStage ξ + ω ≤ blockStage (ξ + 1) := (blockStage_add_one ξ).ge
  set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩ with hxdef
  -- the private context: reference cells for the proper labels of the donor
  obtain ⟨y, f, C, hf, hny, -, -, -, hanc⟩ := hR.exists_privateContext x d hβ.pos 0
  -- for every cell of the root labelled `⊤`, a rooted cover forcing `n + 1` there
  have hO (a : Fin t.card) : ∃ O : R.Occurrence, t.label a = ⊤ →
      ∃ g : Fin n ↪ Fin O.arity, g.trans O.tuple = x.tuple ∧
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) O.type g t a
          (n + 1) := by
    by_cases ha : t.label a = ⊤
    · have hno : ¬ R.IsTopAnchor x a (n + 1) := fun hA ↦ hhol ⟨x, a, n + 1, hA⟩
      simp only [IsTopAnchor, not_and, not_forall, not_not] at hno
      obtain ⟨⟨m, q, g⟩, ⟨s, hs, hsq⟩, hforce⟩ := hno ha
      refine ⟨⟨m, ⟨s, hsq.injective⟩, q, hsq.eval_eq⟩, fun _ ↦ ⟨g, ?_, hforce⟩⟩
      exact Function.Embedding.ext fun i ↦ congrFun hs i
    · exact ⟨x, fun h ↦ absurd h ha⟩
  choose O hO using hO
  -- an occurrence of top grade above the arity of the private context
  obtain ⟨w, hw⟩ : ∃ w : R.Occurrence, y.arity + 1 < w.type.topGrade := by
    have hlt : ((y.arity + 1 : ℕ) : ℕ∞) < R.topGradeSup := htop ▸ ENat.natCast_lt_top _
    obtain ⟨w, hw⟩ := lt_iSup_iff.mp hlt
    exact ⟨w, by exact_mod_cast hw⟩
  -- one occurrence containing all of them
  obtain ⟨Z, hZ⟩ := hR.isCovering.exists_subset_support
    (y.support ∪ w.support ∪ univ.biUnion fun a ↦ (O a).support)
  have hyZ : y ≤ Z := subset_union_left.trans (subset_union_left.trans hZ)
  have hwZ : w ≤ Z := subset_union_right.trans (subset_union_left.trans hZ)
  have hOZ (a : Fin t.card) : O a ≤ Z :=
    (subset_biUnion_of_mem (fun a ↦ (O a).support) (mem_univ a)).trans
      (subset_union_right.trans hZ)
  obtain ⟨gy, hgy, -⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp hyZ
  set fZ : Fin n ↪ Fin Z.arity := f.trans gy
  have hfZ : fZ.trans Z.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hgy, hf]
  have htZ : StageType.restrictFace fZ Z.type = some t :=
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hfZ
  have hlegal : Z.type.IsLegal := hR.isLegal _ _ Z.eval_tuple
  -- the top grade of `Z`
  have hNZ : y.arity + 1 < Z.type.topGrade :=
    hw.trans_le (Occurrence.topGrade_mono hR.isConsistent hwZ)
  have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    omega
  obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap hlegal hnt
  obtain ⟨r, hr⟩ := StageType.exists_isMarker hcc.2.1
  have hgcc := hcc.grade_eq_topGrade
  -- forcing at the root tops, transported to `Z`
  have hforce (a : Fin t.card) (ha : t.label a = ⊤) :
      StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) Z.type fZ t a
        (n + 1) := by
    obtain ⟨g, hg, hfa⟩ := hO a ha
    obtain ⟨ga, hga, hgar⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp (hOZ a)
    have heq : g.trans ga = fZ := by
      refine Function.Embedding.ext fun i ↦ Z.tuple.injective ?_
      have h₁ := DFunLike.congr_fun (congrArg (fun e ↦ g.trans e) hga) i
      have h₂ := DFunLike.congr_fun hg i
      have h₃ := DFunLike.congr_fun hfZ i
      simp only [Function.Embedding.trans_apply] at h₁ h₂ h₃ ⊢
      rw [h₁, h₂, h₃]
    exact heq ▸ hfa.trans_face hgar
  refine ⟨Z.arity, Z.type, Z.tuple, fZ, covers_of_eval _ Z.eval_tuple, ?_, cc, r, hcc, hr, ?_,
    hr.visibilityReplace_le_of_forcesThreshold hβ hα hlegal htZ hcc hforce, fun j hj hjb hjt ↦ ?_⟩
  · funext i
    exact DFunLike.congr_fun hfZ i
  · rw [hgcc]
    have : x.arity + 1 < y.arity := hny
    change n + 1 < y.arity at this
    omega
  · -- the reference cell of the private context, in `Z`
    obtain ⟨o, ho⟩ := exists_coe_eq_of_ne hjb hjt
    obtain ⟨zy, i, hi, hdj, hns, -⟩ := hanc j o ho
    -- the label of the reference cell is `μ + kz` with `kz` below the arity of `y`
    have hzb : y.type.label zy ≠ ⊥ := fun h ↦ hns (h ▸ isSelfVisible_bot _)
    have hzt : y.type.label zy ≠ ⊤ := fun h ↦ hns (h ▸ isSelfVisible_top _)
    obtain ⟨o', ho'⟩ := exists_coe_eq_of_ne hzb hzt
    obtain ⟨μ, hμ, kz, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o'
    rw [ho', isSelfVisible_coe_add_natCast_iff hμ, not_le] at hns
    rw [ho', visibilityReplace_coe_add_natCast hμ hns] at hdj
    obtain ⟨z, hzl, hzg⟩ :=
      Occurrence.exists_label_grade_eq_of_trans_eq hR.isConsistent hgy zy
    have hyN : y.arity < Z.type.toCellScheme.grade cc := by omega
    refine ⟨z, ?_, μ, kz, i, hμ, hzl.trans ho', by omega, hdj, by omega⟩
    rw [hzg]
    exact (y.type.grade_le zy).trans hyN.le

/-! ### (R3) from marked carriers -/

/-- **(R3) for cover-hollowness from marked carriers**: if `StageType.HasMarkedCarriers` holds at
every block stage, then (R3) holds for cover-hollowness at a block stage.  Over a cover in a
cover-hollow model with unbounded growth, a marked-carrier context is acquired for the donor
(`Realization.IsModel.exists_isMarkedCarrierContext`); a marked carrier over it determines the
donor within the stage types on its scheme
(`StageType.HasMarkedCarriers.exists_coface_isDeterminedWithin`); generalized saturation
realizes one of them over the context, and the donor is received
(`Realization.exists_covers_snoc_of_isDeterminedWithin`).  No receiving hypothesis is used. -/
theorem hollowReceiving_of_hasMarkedCarriers
    (hcar : ∀ ξ : Ordinal.{u}, StageType.HasMarkedCarriers.{u} (blockStage ξ)) :
    HollowReceiving.{u, w} IsCoverHollowAtBlock where
  exists_covers α M R hα hR hH htop n t c hc d hd := by
    obtain ⟨ξ, rfl, hhol⟩ := hH
    obtain ⟨k, t', c', h, hc', hcc', hctx⟩ := hR.exists_isMarkedCarrierContext hhol htop hc d
    have ht : StageType.restrictFace h t' = some t := by
      rw [← hR.isConsistent ⟨c', hc'.injective⟩ t' h hc'.eval_eq, ← hc.eval_eq]
      congr 1
      ext i
      exact congrFun hcc' i
    obtain ⟨D', hD', hdet⟩ := (hcar ξ).exists_coface_isDeterminedWithin
      (hR.isLegal _ _ hc'.eval_eq) ht hd hctx
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      (hR.realizesOver_saturationFamily hc' hD') hdet

/-- **The restricted form (item 6′) from marked carriers**: (R3) for cover-hollowness without a
globally rigid core at a block stage, through `Realization.HollowReceiving.withoutRigidCore`. -/
theorem hollowReceiving_withoutRigidCore_of_hasMarkedCarriers
    (hcar : ∀ ξ : Ordinal.{u}, StageType.HasMarkedCarriers.{u} (blockStage ξ)) :
    HollowReceiving.{u, w} IsCoverHollowWithoutRigidCoreAtBlock :=
  (hollowReceiving_of_hasMarkedCarriers hcar).withoutRigidCore

/-- **(R3) from prescribed rows and compatible marked prescriptions**: the hypotheses of
`Realization.hollowReceiving_of_hasMarkedCarriers` follow from `StageType.HasPrescribedFullRows`
and `StageType.HasCompatibleMarkedPrescriptions` at every block stage. -/
theorem hollowReceiving_of_hasPrescribedFullRows
    (hpr : ∀ ξ : Ordinal.{u}, StageType.HasPrescribedFullRows.{u} (blockStage ξ))
    (hcomp : ∀ ξ : Ordinal.{u}, StageType.HasCompatibleMarkedPrescriptions.{u} (blockStage ξ)) :
    HollowReceiving.{u, w} IsCoverHollowAtBlock :=
  hollowReceiving_of_hasMarkedCarriers fun ξ ↦ (hpr ξ).hasMarkedCarriers (hcomp ξ)

end Realization

end VaughtConjecture

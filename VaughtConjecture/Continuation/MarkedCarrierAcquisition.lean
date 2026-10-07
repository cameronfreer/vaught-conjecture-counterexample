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
# Acquisition of marked-cap contexts, and (R3) from marked carriers

Roadmap, Layer 3 ((R3) of the table of 3.4) and Layer 4 (cover-hollowness).

**Synchronization** (`Realization.IsModel.exists_synchronized`, compiled in this repository
(theorem named)).  In a model at a block stage `λ_ξ` that is cover-hollow and has unbounded
growth, every occurrence `y` containing a root `x` extends to an occurrence of top grade above
`y.arity + 1` in which the rows of every top cap read the thresholds forced at the tops of the
root.  By covering one occurrence contains `y`, an occurrence of large top grade, and for every top
of the root a rooted cover forcing `x.arity + 1` there, which cover-hollowness provides
(`Realization.IsTopAnchor`).  Forcing passes to the occurrence along the faces
(`StageType.ForcesThreshold.trans_face`), and the rows of a top cap read it
(`StageType.IsMarker.visibilityReplace_le_of_forcesThreshold`, from
`StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`).

**Acquisition.**  `Realization.hollowAcquisition_isMarkedCapContext` (compiled in this repository
(theorem named)) is `Realization.HollowAcquisition` for `Realization.IsCoverHollowAtBlock` and the
marked-cap context, with `y` the root.  `Realization.IsModel.exists_isMarkedCarrierContext`
(compiled in this repository (theorem named)) acquires, for every donor, a marked-carrier context
(`StageType.IsMarkedCarrierContext`), with `y` the private context of the root for the donor
(`Realization.IsModel.exists_privateContext`), whose reference cells keep their labels and grades.
The clauses of modelhood used are uniformity, high-arity dominance (for the private context),
exact consistency, covering and legal types; neither generalized saturation nor any receiving
hypothesis is used.

**(R3), scheme form** (`Realization.hollowReceiving_of_hasMarkedCarriers`, compiled in this
repository (theorem named)): `Realization.HollowReceiving` for `Realization.IsCoverHollowAtBlock`
holds if `StageType.HasMarkedCarriers` (open) holds at every block stage, through the acquisition
of marked-carrier contexts, determination by a marked carrier within its bottom-pattern family
(`StageType.HasMarkedCarriers.exists_coface_isDeterminedWithin`) and the bottom-pattern clause of
modelhood.  No receiving hypothesis is used.  The restricted form follows
(`Realization.hollowReceiving_withoutRigidCore_of_hasMarkedCarriers`), and so does the form from
`StageType.HasPrescribedFullRows` with the compatibility of the marked prescriptions
(`Realization.hollowReceiving_of_hasPrescribedFullRows`).

**(R3), cutoff form** (`Realization.hollowReceiving_of_hasTopMarkedCarriers`, compiled in this
repository (theorem named)): (R3) holds if `StageType.HasTopMarkedCarriers` (open; it prescribes
only the readings of the new tops) holds at every block stage and every model at every block stage
has finite-cut receiving ((R1), open; asked here at every block stage and in every universe, which
is more than the hypothesis `Expansion.FiniteCutReceiving`).  The receiving family at a cutoff
above the labels of the carrier other than `⊤` keeps the donor's labels other than `⊤`, so no
reference cell is needed.

All of these are conditional: marked carriers, top-marked carriers, prescribed full rows, the
compatibility of the prescriptions and (R1) at every block stage are open, and no implication
from the coatom extension property is compiled.

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

/-- **Synchronization**: let `R` be a model at the block stage `λ_ξ`, cover-hollow, with unbounded
growth, `x` an occurrence (the root) and `y` an occurrence containing `x` as a literal face along
`f`.  Some occurrence `Z` contains `y` as a literal face along an embedding `gy`, has top grade
above `y.arity + 1`, and at every top cap `c` of its type and every marker `r` of `c` the row of
`c` satisfies `visibilityReplace N (x.arity + 1) (rowAt c r) ≤ rowAt c a` at every cell `a` of the
root labelled `⊤` (`N` the grade of `c`).

`Z` contains, by covering, `y`, an occurrence of top grade above `y.arity + 1` (unbounded growth),
and for every cell of the root labelled `⊤` a rooted cover forcing `x.arity + 1` there
(cover-hollowness, `Realization.IsTopAnchor`).  Forcing is monotone along extensions
(`StageType.ForcesThreshold.trans_face`), the top grade only grows, and the rows of a top cap
read the forced thresholds (`StageType.IsMarker.visibilityReplace_le_of_forcesThreshold`). -/
theorem IsModel.exists_synchronized (hR : R.IsModel) (hhol : R.IsCoverHollow)
    (htop : R.topGradeSup = ⊤) (x y : R.Occurrence) {f : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) :
    ∃ (Z : R.Occurrence) (gy : Fin y.arity ↪ Fin Z.arity), gy.trans Z.tuple = y.tuple ∧
      y.arity + 1 < Z.type.topGrade ∧ ∀ cc r, Z.type.IsTopCap cc → Z.type.IsMarker cc r →
        ∀ a ∈ Z.type.visibleCells (f.trans gy), Z.type.label a = ⊤ →
          visibilityReplace (Z.type.toCellScheme.grade cc) (x.arity + 1) (Z.type.rowAt cc r) ≤
            Z.type.rowAt cc a := by
  classical
  have hβ := isSuccLimit_blockStage ξ
  have hα : blockStage ξ + ω ≤ blockStage (ξ + 1) := (blockStage_add_one ξ).ge
  -- for every cell of the root labelled `⊤`, a rooted cover forcing `x.arity + 1` there
  have hO (a : Fin x.type.card) : ∃ O : R.Occurrence, x.type.label a = ⊤ →
      ∃ g : Fin x.arity ↪ Fin O.arity, g.trans O.tuple = x.tuple ∧
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) O.type g
          x.type a (x.arity + 1) := by
    by_cases ha : x.type.label a = ⊤
    · have hno : ¬ R.IsTopAnchor x a (x.arity + 1) := fun hA ↦ hhol ⟨x, a, x.arity + 1, hA⟩
      simp only [IsTopAnchor, not_and, not_forall, not_not] at hno
      obtain ⟨⟨m, q, g⟩, ⟨s, hs, hsq⟩, hforce⟩ := hno ha
      refine ⟨⟨m, ⟨s, hsq.injective⟩, q, hsq.eval_eq⟩, fun _ ↦ ⟨g, ?_, hforce⟩⟩
      exact Function.Embedding.ext fun i ↦ congrFun hs i
    · exact ⟨x, fun h ↦ absurd h ha⟩
  choose O hO using hO
  -- an occurrence of top grade above `y.arity + 1`
  obtain ⟨w, hw⟩ : ∃ w : R.Occurrence, y.arity + 1 < w.type.topGrade := by
    have hlt : ((y.arity + 1 : ℕ) : ℕ∞) < R.topGradeSup := htop ▸ ENat.natCast_lt_top _
    obtain ⟨w, hw⟩ := lt_iSup_iff.mp hlt
    exact ⟨w, by exact_mod_cast hw⟩
  -- one occurrence containing all of them
  obtain ⟨Z, hZ⟩ := hR.isCovering.exists_subset_support
    (y.support ∪ w.support ∪ univ.biUnion fun a ↦ (O a).support)
  have hyZ : y ≤ Z := subset_union_left.trans (subset_union_left.trans hZ)
  have hwZ : w ≤ Z := subset_union_right.trans (subset_union_left.trans hZ)
  have hOZ (a : Fin x.type.card) : O a ≤ Z :=
    (subset_biUnion_of_mem (fun a ↦ (O a).support) (mem_univ a)).trans
      (subset_union_right.trans hZ)
  obtain ⟨gy, hgy, -⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp hyZ
  set fZ : Fin x.arity ↪ Fin Z.arity := f.trans gy
  have hfZ : fZ.trans Z.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hgy, hf]
  have htZ : StageType.restrictFace fZ Z.type = some x.type :=
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hfZ
  have hlegal : Z.type.IsLegal := hR.isLegal _ _ Z.eval_tuple
  -- forcing at the root tops, transported to `Z`
  have hforce (a : Fin x.type.card) (ha : x.type.label a = ⊤) :
      StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) Z.type fZ
        x.type a (x.arity + 1) := by
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
  exact ⟨Z, gy, hgy, hw.trans_le (Occurrence.topGrade_mono hR.isConsistent hwZ),
    fun cc r hcc hr ↦ hr.visibilityReplace_le_of_forcesThreshold hβ hα hlegal htZ hcc hforce⟩

/-- An occurrence of positive top grade has a top cap with a marker. -/
private theorem exists_top_cap_marker (hR : R.IsModel) (Z : R.Occurrence)
    (hZ : 0 < Z.type.topGrade) :
    ∃ cc r, Z.type.IsTopCap cc ∧ Z.type.IsMarker cc r := by
  have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    omega
  obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap (hR.isLegal _ _ Z.eval_tuple) hnt
  obtain ⟨r, hr⟩ := StageType.exists_isMarker hcc.2.1
  exact ⟨cc, r, hcc, hr⟩

/-- **Hollow acquisition of the marked-cap context**: in every model at a limit stage that is
cover-hollow at a block stage and has unbounded growth, every cover extends to a cover of a
marked-cap context (`StageType.IsMarkedCapContext`) along the root.  This is
`Realization.HollowAcquisition` for `Realization.IsCoverHollowAtBlock` and the marked-cap
context, through `Realization.IsModel.exists_synchronized` with `y` the root itself. -/
theorem hollowAcquisition_isMarkedCapContext :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock fun t' h ↦ t'.IsMarkedCapContext h where
  exists_context α M R hα hR hH htop n t c hc := by
    obtain ⟨ξ, rfl, hhol⟩ := hH
    set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨Z, gy, hgy, hNZ, hineq⟩ := hR.exists_synchronized hhol htop x x
      (f := Function.Embedding.refl _) (Function.Embedding.refl_trans _)
    obtain ⟨cc, r, hcc, hr⟩ := exists_top_cap_marker hR Z (by omega)
    refine ⟨Z.arity, Z.type, Z.tuple, (Function.Embedding.refl _).trans gy,
      covers_of_eval _ Z.eval_tuple, ?_, cc, r, hcc, hr, ?_, hineq cc r hcc hr⟩
    · funext i
      exact DFunLike.congr_fun hgy i
    · rw [hcc.grade_eq_topGrade]
      exact hNZ

/-- **Acquisition of a marked-carrier context.**  Let `R` be a model at the block stage `λ_ξ`,
cover-hollow, with unbounded growth (`R.topGradeSup = ⊤`).  Over every cover `c` of a type `t` on
`n` points and for every donor `d` on `n + 1` points, some cover `c'` of a type `t'` restricts
along an embedding `h` to `c`, and `t'` is a marked-carrier context along `h` for `d`.

The private context of the root for the donor (`Realization.IsModel.exists_privateContext`)
gives the reference cells; synchronization (`Realization.IsModel.exists_synchronized`) extends it
to an occurrence of larger top grade where the rows of a top cap read the forced thresholds at the
root; the reference cells keep their labels and grades, below the top grade.

Of modelhood, uniformity, high-arity dominance, exact consistency, covering and legal types are
used; generalized saturation and the bottom pattern are not. -/
theorem IsModel.exists_isMarkedCarrierContext (hR : R.IsModel) (hhol : R.IsCoverHollow)
    (htop : R.topGradeSup = ⊤) {n : ℕ} {t : StageType.{u} (blockStage ξ) n} {c : Fin n → M}
    (hc : R.Covers t c) (d : StageType.{u} (blockStage ξ) (n + 1)) :
    ∃ (k : ℕ) (t' : StageType.{u} (blockStage ξ) k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ t'.IsMarkedCarrierContext h d := by
  classical
  have hβ := isSuccLimit_blockStage ξ
  set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩ with hxdef
  -- the private context: reference cells for the proper labels of the donor
  obtain ⟨y, f, C, hf, hny, -, -, -, hanc⟩ := hR.exists_privateContext x d hβ.pos 0
  obtain ⟨Z, gy, hgy, hNZ, hineq⟩ := hR.exists_synchronized hhol htop x y hf
  obtain ⟨cc, r, hcc, hr⟩ := exists_top_cap_marker hR Z (by omega)
  have hgcc := hcc.grade_eq_topGrade
  have hfZ : (f.trans gy).trans Z.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hgy, hf]
  refine ⟨Z.arity, Z.type, Z.tuple, f.trans gy, covers_of_eval _ Z.eval_tuple, ?_, cc, r, hcc, hr,
    ?_, hineq cc r hcc hr, fun j hj hjb hjt ↦ ?_⟩
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
(`StageType.HasMarkedCarriers.exists_coface_isDeterminedWithin`); the bottom-pattern
clause of modelhood realizes one of them over the context, and the donor is received
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
    -- the bottom pattern of `D'` over the cover `c'`
    have hU : R.RealizesOver ⟨c', hc'.injective⟩
        (StageType.bottomPatternFamily D'.toScheme D'.label) :=
      hR.bottomPattern ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩ D'.toScheme D'.label
        ⟨D', hD', rfl, fun i j hij _ ↦ by rw [Fin.ext hij]⟩
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc' hU hdet

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

/-! ### (R3) from top-marked carriers and (R1) -/

/-- **(R3) for cover-hollowness from top-marked carriers and finite-cut receiving**: if
`StageType.HasTopMarkedCarriers` holds at every block stage, and every model at every block stage
has finite-cut receiving ((R1); this asks more than the hypothesis `Expansion.FiniteCutReceiving`,
which concerns countable stages in universe `0`), then (R3) holds for cover-hollowness at a block
stage.  Over a cover in a cover-hollow model with unbounded growth, a marked-cap context is
acquired (`Realization.hollowAcquisition_isMarkedCapContext`); a top-marked carrier over it
carrying the donor, at a permitted cutoff above its labels other than `⊤`, determines the donor
within its receiving family
(`StageType.isDeterminedWithin_receivingFamily_of_isPrescribedExtension`); (R1) realizes a member
of that family over the context, and the donor is received. -/
theorem hollowReceiving_of_hasTopMarkedCarriers
    (hcar : ∀ ξ : Ordinal.{u}, StageType.HasTopMarkedCarriers.{u} (blockStage ξ))
    (hrec : ∀ (ξ : Ordinal.{u}) (M : Type w) (R : Realization.{u, w} (blockStage ξ) M),
      R.IsModel → R.HasFiniteCutReceiving) :
    HollowReceiving.{u, w} IsCoverHollowAtBlock where
  exists_covers α M R hα hR hH htop n t c hc d hd := by
    obtain ⟨k, t', c', h, hc', hcc', ctx, r, hctx⟩ :=
      hollowAcquisition_isMarkedCapContext.exists_context hα hR hH htop t c hc
    obtain ⟨ξ, rfl, -⟩ := hH
    have ht : StageType.restrictFace h t' = some t := by
      rw [← hR.isConsistent ⟨c', hc'.injective⟩ t' h hc'.eval_eq, ← hc.eval_eq]
      congr 1
      ext i
      exact congrFun hcc' i
    obtain ⟨D, hD⟩ := hcar ξ t' h t ht d hd.2 ctx r (hR.isLegal _ _ hc'.eval_eq) hd.1 hctx
    obtain ⟨δ, hδα, hδ⟩ := D.exists_lt_forall_label_lt hα
    have hδc : IsPermittedCutoff (blockStage ξ) (δ : Label.{u}) := isPermittedCutoff_coe.mpr hδα
    have hdet := StageType.isDeterminedWithin_receivingFamily_of_isPrescribedExtension ht hd.2
      hctx.1 hctx.2.1.1 hctx.2.2.1.le hD hδ
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      ((hrec ξ M R hR).realizesOver_receivingFamily hc' ⟨hD.1, hD.2.1⟩ hδc) hdet

end Realization

end VaughtConjecture

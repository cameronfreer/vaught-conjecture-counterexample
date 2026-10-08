/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCap
import VaughtConjecture.Continuation.MarkedCarrierAcquisition
import VaughtConjecture.Continuation.TiedRootCapCounterexample

/-!
# Acquiring marked-cap contexts whose cap keeps the root ties

Roadmap, Layer 3 ((R3) of the table of 3.4) and Layer 4 (acquisition).

The refutation schema of the raise has a legal instance at a marked-cap context whose top cap
separates two root cells that its labels tie (`VaughtConjecture.Continuation.
TiedRootCapCounterexample`); a cap whose row keeps the root ties excludes the schema
(`StageType.le_of_tie_of_keepsRootTies`).  This file asks whether acquisition can produce such
contexts.

* **Tied marked-cap contexts** (`StageType.IsTiedMarkedCapContext`, defined here): a marked-cap
  context with top cap `c` and marker `r` (`StageType.IsMarkedCapContextAt`) whose row keeps the
  root ties (`StageType.KeepsRootTies`).  The context of `TiedRootCapCounterexample` is not one
  (`TiedRootCapCounterexample.not_isTiedMarkedCapContext`, compiled in this repository (theorem
  named)).
* **Apex types** (`StageType.isTiedMarkedCapContext_of_addApex`, compiled): a stage type with the
  scheme of `t₀.addApex`, `⊤` at the apex, and the labels of `t₀.addApex` on the root, is a tied
  marked-cap context along every root of `n` points with `n + 1 < k`.  The apex reads every cell
  labelled `⊤` at the code of `⊤`, the largest value of its row, so the row inequality of a
  marked-cap context holds at every marker; its row is the code of the labels, so it keeps the
  root ties.
* **Acquisition, conditional** (`Realization.hollowAcquisition_isTiedMarkedCapContext`,
  compiled): `HollowAcquisition IsCoverHollowAtBlock IsTiedMarkedCapContext` holds under two
  hypotheses:
  - `Realization.HollowFullTopSaturation` (a named statement, prospective; not a clause of
    `Realization.IsModel`): every hollow model at a limit stage realizes, over every occurrence,
    a member of the full-top family of a scheme and a labelling (`Realization.fullTopFamily`:
    the scheme, and `⊤` at the cells of full grade where the labelling is `⊤`) whenever some
    legal one-point coface lies in it.  Generalized saturation (clause 4(a)i) realizes a type on
    the scheme with no control of the labels; the bottom pattern (clause 4(a)ii) controls `⊥` at
    the cells of grade at most the arity only; neither forces `⊤` at the new apex, and without
    `⊤` there the apex is not a top cap.
  - `Seed.HasCompletions α` at every stage that is zero or a limit: every seed has a completion
    below the full grade.  It is compiled, at every arity, as
    `Seed.nonempty_completionBelowFullGrade` on the completion lane (`research/lane-close-merge`),
    and is discharged there on merge.  The weaker `StageType.HasApexCoatomExtensions` does not
    suffice: it gives a cell of full grade carrying the largest label, not its row, and the root
    ties are a property of the row.
  The proof: synchronization (`Realization.IsModel.exists_synchronized`) gives an occurrence `Z`
  of arity above `n + 1` containing the root; a closed coatom of its plan
  (`Geometry.IsPlan.exists_erase_mem`), moved to the last point, gives a seed of two copies of
  the type of `Z` (reindexed); the apex of its completion is labelled `⊤`; full-top saturation
  realizes over `Z` a type on that scheme with `⊤` at the apex, literal on `Z`.
* **What this says about the hypothesis.**  The forced thresholds of synchronization are not
  used: at an apex the row inequality of a marked-cap context is automatic.  So under full-top
  saturation the tied marked-cap contexts are acquired with no hollow content in the cap's row;
  determination at such contexts (hollow cutoff determination, stated on the compositions lane,
  or a carrier theorem)
  remains the open core, and is not addressed here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label

/-! ### A coatom of a plan -/

namespace Geometry

variable {α : Type*} [DecidableEq α] {A : Finset α} {P : Finset (Finset α)}

/-- **A nonempty plan has a closed coatom**: some point of the ground set has the rest of the
ground set as a closed face. -/
theorem IsPlan.exists_erase_mem (hP : IsPlan A P) (hA : A.Nonempty) : ∃ a ∈ A, A.erase a ∈ P := by
  cases hP with
  | empty => exact absurd hA (by simp)
  | singleton a => exact ⟨a, mem_singleton_self a, by simp⟩
  | step ha _ _ hQ _ _ _ =>
    exact ⟨_, ha, mem_insert_of_mem (mem_union_left _ hQ.ground_mem)⟩

end Geometry

/-! ### Tied marked-cap contexts -/

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- A **tied marked-cap context** along `h`: a marked-cap context with a top cap `c` and a marker
`r` (`StageType.IsMarkedCapContextAt`) whose row keeps the ties of the labels on the root
(`StageType.KeepsRootTies`). -/
def IsTiedMarkedCapContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.KeepsRootTies h c

/-- A tied marked-cap context is a marked-cap context. -/
theorem IsTiedMarkedCapContext.isMarkedCapContext {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : t'.IsTiedMarkedCapContext h) : t'.IsMarkedCapContext h :=
  let ⟨c, r, hc, _⟩ := ht
  ⟨c, r, hc⟩

section Apex

variable {t₀ : StageType.{u} α k} (ht₀ : t₀.IsLegalBelowFullGrade) (hk : 0 < k)

/-- Every cell lies below the apex. -/
theorem mem_below_addApex_last (z : Fin (t₀.addApex ht₀ hk).card) :
    z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _)) := by
  rw [CellScheme.mem_below, addApex_gradedIndex_last]
  exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t₀.addApex ht₀ hk).grade_le z⟩

/-- The apex reads every cell at the code of its label. -/
theorem rowAt_addApex_last (z : Fin (t₀.addApex ht₀ hk).card) :
    (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) z =
      blockEncode (apexCodes ht₀) k ((t₀.addApex ht₀ hk).label z) := by
  rw [Scheme.rowAt_of_mem (mem_below_addApex_last ht₀ hk z)]
  exact row_addApex_last_eq ht₀ hk _

/-- **A relabelling of an apex type, `⊤` at the apex and literal on the root, is a tied
marked-cap context.**  Let `q` have the scheme of `t₀.addApex`, label the apex `⊤`, and agree with
`t₀.addApex` at the cells visible through `h : Fin n ↪ Fin k`, with `n + 1 < k`.  The apex is a
top cap (full scope, the full grade `k`); its row is the code of the labels of `t₀.addApex`, so
every cell of the root labelled `⊤` is read at the code of `⊤`, the largest value of the row, and
the row keeps the root ties. -/
theorem isTiedMarkedCapContext_of_addApex {q : StageType.{u} α k}
    (hS : q.toScheme = (t₀.addApex ht₀ hk).toScheme)
    (htop : ∀ (i : Fin q.card) (j : Fin (t₀.addApex ht₀ hk).card), (i : ℕ) = j →
      q.toCellScheme.grade i = k → (t₀.addApex ht₀ hk).label j = ⊤ → q.label i = ⊤)
    {h : Fin n ↪ Fin k} (hn : n + 1 < k)
    (hl : ∀ (i : Fin q.card) (j : Fin (t₀.addApex ht₀ hk).card), (i : ℕ) = j →
      i ∈ q.visibleCells h → q.label i = (t₀.addApex ht₀ hk).label j) :
    q.IsTiedMarkedCapContext h := by
  obtain ⟨S, ℓ, h₁, h₂, h₃, h₄⟩ := q
  change S = _ at hS
  subst hS
  have hl' (i : Fin (t₀.addApex ht₀ hk).card) (hi : i ∈ (t₀.addApex ht₀ hk).visibleCells h) :
      ℓ i = (t₀.addApex ht₀ hk).label i := hl i i rfl hi
  have hg : (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _) = k :=
    congrArg Prod.snd (addApex_gradedIndex_last ht₀ hk)
  have hc : ℓ (Fin.last _) = ⊤ := htop _ _ rfl hg (addApex_label_last ht₀ hk)
  obtain ⟨r, hr⟩ := exists_isMarker (q := ⟨_, ℓ, h₁, h₂, h₃, h₄⟩) (c := Fin.last _) hc
  refine ⟨Fin.last _, r, ⟨⟨addApex_scope_last ht₀ hk, hc, fun x _ ↦ ?_⟩, hr, ?_,
    fun a ha hat ↦ ?_⟩, ?_⟩
  · change (t₀.addApex ht₀ hk).toCellScheme.grade x ≤
      (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _)
    rw [hg]
    exact (t₀.addApex ht₀ hk).grade_le x
  · change n + 1 < (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _)
    rw [hg]
    exact hn
  · have haA : (t₀.addApex ht₀ hk).label a = ⊤ := (hl' a ha).symm.trans hat
    change visibilityReplace ((t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _)) (n + 1)
      ((t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) r) ≤
      (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) a
    rw [hg, rowAt_addApex_last, rowAt_addApex_last, haA]
    exact visibilityReplace_le_of_le hn.le (isSelfVisible_blockEncode_top le_rfl)
      (blockEncode_le_blockEncode_top _)
  · intro y₁ hy₁ y₂ hy₂ hle hgr
    change ℓ y₁ ≤ ℓ y₂ at hle
    rw [hl' y₁ hy₁, hl' y₂ hy₂] at hle
    exact keepsRootTies_addApex ht₀ hk h y₁ hy₁ y₂ hy₂ hle hgr

end Apex

/-- Two stage types on one scheme with the same face along `f` agree at the cells visible through
`f`. -/
theorem label_eq_of_restrictFace_eq {q D : StageType.{u} α k} (hS : q.toScheme = D.toScheme)
    {f : Fin n ↪ Fin k} {T : StageType.{u} α n} (hq : restrictFace f q = some T)
    (hD : restrictFace f D = some T) (i : Fin q.card) (j : Fin D.card) (hij : (i : ℕ) = j)
    (hi : i ∈ q.visibleCells f) : q.label i = D.label j := by
  obtain ⟨S, ℓ, h₁, h₂, h₃, h₄⟩ := q
  change S = _ at hS
  subst hS
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨z, rfl⟩ := exists_faceCell_eq hq hi
  exact (label_faceCell hq z).trans (label_faceCell hD z).symm

end StageType

/-! ### Completions and the full-top saturation -/

/-- An equivalence onto the points sends the points other than the last onto the points other
than the image of the last. -/
theorem univ_map_castSuccEmb_trans_eq_erase {m : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (e : Fin (m + 1) ≃ β) :
    univ.map (Fin.castSuccEmb.trans e.toEmbedding) = univ.erase (e (Fin.last m)) := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [mem_map, mem_univ, true_and, mem_erase, ne_eq, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, Fin.coe_castSuccEmb, EmbeddingLike.apply_eq_iff_eq, and_true]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.castSucc_ne_last i
  · intro hy
    exact ⟨y.castPred hy, Fin.castSucc_castPred y hy⟩

namespace Seed

variable (α) in
/-- **Every seed at the stage `α` has a completion below the full grade** (a named statement
here).  It is compiled unconditionally, at every arity, as `Seed.nonempty_completionBelowFullGrade`
on the research branch of the completion lane (`research/lane-close-merge`), not on this branch;
the hypothesis is discharged there on merge. -/
def HasCompletions (α : Ordinal.{u}) : Prop :=
  ∀ (m : ℕ) (I : Seed.{u} α m), Nonempty (CompletionBelowFullGrade I)

end Seed

namespace Realization

variable {α : Ordinal.{u}} {M : Type w}

/-- The **full-top family** of a scheme `S` on `n + 1` points and a labelling `ρ` of its cells:
the stage types with scheme `S` labelled `⊤` at every cell of full grade `n + 1` at which `ρ` is
`⊤`. -/
def fullTopFamily {n : ℕ} (S : Scheme.{u} (n + 1)) (ρ : Fin S.card → Label.{u}) :
    Set (StageType.{u} α (n + 1)) :=
  {q | q.toScheme = S ∧ ∀ (i : Fin q.card) (j : Fin S.card), (i : ℕ) = j →
    q.toCellScheme.grade i = n + 1 → ρ j = ⊤ → q.label i = ⊤}

/-- **Full-top saturation** of a realization (a named clause, prospective: not a clause of
`Realization.IsModel`): generalized saturation (clause 4(a)i) keeping the formal top at the cells
of full grade.  If some one-point coface of the type of an occurrence lies in the full-top family
of `S` and `ρ`, a member of that family is realized over the occurrence.  The bottom-pattern
clause 4(a)ii is the analogue for `⊥` at the cells of grade at most the arity. -/
def HasFullTopSaturation (R : Realization.{u, w} α M) : Prop :=
  ∀ (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) (ρ : Fin S.card → Label.{u}),
    (x.type.cofaces ∩ fullTopFamily S ρ).Nonempty → R.RealizesOver x.tuple (fullTopFamily S ρ)

/-- **Full-top saturation of the hollow models** (a named statement, prospective): every model at
a limit stage that is cover-hollow at a block stage and has unbounded growth has full-top
saturation. -/
def HollowFullTopSaturation : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ (R : Realization.{u, w} α M), Order.IsSuccLimit α →
    R.IsModel → R.IsCoverHollowAtBlock → R.topGradeSup = ⊤ → R.HasFullTopSaturation

/-- **Acquisition of tied marked-cap contexts**, conditional on the full-top saturation of the
hollow models (prospective) and on completions of seeds at every stage that is zero or a limit
(compiled on the completion lane).  Over a cover `c` of `t`, synchronization gives an occurrence
`Z` of arity above `n + 1` containing the root; a closed coatom of its plan, moved to the last
point, gives a seed of two copies of the type of `Z`; the apex of its completion is labelled `⊤`
and its row is the code of the labels; full-top saturation realizes over `Z` a type with that
scheme, `⊤` at the apex and the labels of `Z` on the old points, which is a tied marked-cap
context along the root (`StageType.isTiedMarkedCapContext_of_addApex`).  The forced thresholds
of synchronization are not used: the apex reads every cell of the root labelled `⊤` at the
largest value of its row. -/
theorem hollowAcquisition_isTiedMarkedCapContext (hsat : HollowFullTopSaturation.{u, w})
    (hcomp : ∀ α : Ordinal.{u}, Order.IsSuccPrelimit α → Seed.HasCompletions α) :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock fun t' h ↦ t'.IsTiedMarkedCapContext h where
  exists_context α M R hα hR hH htop n t c hc := by
    classical
    have hsatR := hsat R hα hR hH htop
    obtain ⟨ξ, rfl, hhol⟩ := hH
    set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨Z, gy, hgy, hNZ, -⟩ := hR.exists_synchronized hhol htop x x
      (f := Function.Embedding.refl _) (Function.Embedding.refl_trans _)
    -- the arity of `Z` exceeds `n + 1`
    have hZleg : Z.type.IsLegal := hR.isLegal _ _ Z.eval_tuple
    have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
      rw [← StageType.topGrade_eq_zero_iff] at htf
      omega
    obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap hZleg hnt
    have hnk : n + 1 < Z.arity := by
      have := Z.type.grade_le cc
      rw [hcc.grade_eq_topGrade] at this
      exact hNZ.trans_le this
    obtain ⟨m, hm⟩ : ∃ m, Z.arity = m + 1 := ⟨Z.arity - 1, by omega⟩
    -- a closed coatom of the plan of `Z`
    have hplan := Z.type.isWellFormed.isWellFormed.isPlan
    rw [Z.type.isWellFormed.ground_eq] at hplan
    obtain ⟨a, -, ha⟩ := hplan.exists_erase_mem
      ⟨⟨0, by omega⟩, mem_univ _⟩
    -- move it to the last point
    set e : Fin (m + 1) ≃ Fin Z.arity :=
      (Equiv.swap (Fin.last m) (Fin.cast hm a)).trans (finCongr hm.symm) with he
    have hea : e (Fin.last m) = a := by simp [he]
    have hfe : univ.map e.toEmbedding ∈ Z.type.toCellScheme.faces := by
      rw [map_univ_equiv]
      exact Z.type.univ_mem_faces
    set T₁ := Z.type.comap e.toEmbedding hfe
    have hZT : StageType.restrictFace e.toEmbedding Z.type = some T₁ :=
      StageType.restrictFace_of_mem _ _ hfe
    set x₁ : R.Occurrence := ⟨m + 1, e.toEmbedding.trans Z.tuple, T₁, by
      rw [hR.isConsistent _ _ _ Z.eval_tuple, hZT]⟩
    have hT₁ : T₁.IsLegal := hR.isLegal _ _ x₁.eval_tuple
    have hfp : univ.map (Fin.castSuccEmb.trans e.toEmbedding) ∈ Z.type.toCellScheme.faces := by
      rw [univ_map_castSuccEmb_trans_eq_erase, hea]
      exact ha
    have hp : StageType.restrictFace Fin.castSuccEmb T₁ = some (Z.type.comap _ hfp) := by
      rw [StageType.restrictFace_trans _ _ _ hZT]
      exact StageType.restrictFace_of_mem _ _ hfp
    -- the seed of two copies of `T₁`, its completion, and the full-top realization
    set I : Seed.{u} (blockStage ξ) m := Seed.ofCoatoms hT₁ hT₁ hp hp
    have hα' : Order.IsSuccPrelimit (blockStage ξ) := hα.isSuccPrelimit
    set F : CompletionBelowFullGrade I := (hcomp _ hα' m I).some
    set D := F.completion hα'
    have hDcof : D ∈ T₁.cofaces := ⟨F.isLegal_completion hα', F.restrictFace_left_completion hα'⟩
    obtain ⟨u, hu, q, ⟨hqS, hqtop⟩, hqe⟩ := hsatR x₁ D.toScheme D.label
      ⟨D, hDcof, rfl, fun i j hij _ hj ↦ by obtain rfl := Fin.ext hij; exact hj⟩
    have hqT : StageType.restrictFace Fin.castSuccEmb q = some T₁ := by
      rw [← hR.isConsistent _ _ _ hqe, hu]
      exact x₁.eval_tuple
    set h' : Fin n ↪ Fin (m + 2) := gy.trans (e.symm.toEmbedding.trans Fin.castSuccEmb)
    refine ⟨m + 2, q, u, h', covers_of_eval u hqe, ?_, ?_⟩
    · funext i
      have h₁ : u (Fin.castSucc (e.symm (gy i))) = Z.tuple (gy i) := by
        have := DFunLike.congr_fun hu (e.symm (gy i))
        simpa [x₁] using this
      exact h₁.trans (DFunLike.congr_fun hgy i)
    · refine StageType.isTiedMarkedCapContext_of_addApex (t₀ := F.truncate hα')
        F.isLegalBelowFullGrade (Nat.succ_pos _) hqS hqtop (by omega) fun i j hij hi ↦ ?_
      refine StageType.label_eq_of_restrictFace_eq hqS hqT (F.restrictFace_left_completion hα')
        i j hij ?_
      rw [Scheme.mem_visibleCells] at hi ⊢
      refine hi.trans ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨_, rfl⟩

end Realization

/-! ### The context with separated tied root cells is not tied -/

namespace TiedRootCapCounterexample

open StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **The context of `TiedRootCapCounterexample` is not a tied marked-cap context**: its only top
cap is the cap (the other cells have grade below `3`), whose row separates the tied root cells. -/
theorem not_isTiedMarkedCapContext : ¬ (context hα).IsTiedMarkedCapContext rootEmb := by
  rintro ⟨c, r, hc, hk⟩
  have hle := hc.1.2.2 (capCell hα) (context_label_cap hα)
  rw [context_grade_cap] at hle
  induction c using Fin.lastCases with
  | last => exact not_keepsRootTies hα hk
  | cast d =>
    have hlt := (lower hα).isLegalBelowFullGrade.grade_lt d
    change (lower hα).scheme.toCellScheme.grade d < 3 at hlt
    have hg : (context hα).toCellScheme.grade d.castSucc = (base hα).toCellScheme.grade d :=
      Scheme.appendFullCellScheme_grade_castSucc _ _ d
    rw [hg] at hle
    change 3 ≤ (lower hα).scheme.toCellScheme.grade d at hle
    omega

end TiedRootCapCounterexample

end VaughtConjecture

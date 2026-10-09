/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2Two

/-!
# h2 at every arity, with the lost point last

Roadmap, Layer 3 ((R2) of the table of 3.4: coatom cutoff determination at source-gap contexts,
`Realization.CoatomCutoffDetermination`, written **h2** in the names of this family of modules).
Every declaration is proved; the three general-arity inputs below are hypotheses of the
implications.

**The target** (`H2.CoatomCutoffDeterminationLast`): the coatom form of cutoff determination
(`Realization.CoatomCutoffDetermination`) for source-gap contexts with the lost point
last (`StageType.IsSourceGapContextLast`), on `k + 1` points.

**The implication** (`H2.coatomCutoffDeterminationLast_of_hasRecCompletions`): the target follows
from completions with the reading property (`H2.HasRecCompletions`): for every legal source-gap
context `t'` with the lost point last and every legal coface `tb` of its coatom face, and every
designation (non-top cells low; top cells of grade at most `K` off the root and not determined by
the root designated), a completion below the full grade of the seed of `t'` and `tb` whose lawful
labellings with the owner at `⊤` satisfy the clause (`H2.RecProp`).  The rest (designation,
cutoff, the coface `F.completion`, the key step `H2.key_completion`) holds at every arity.

**The three general-arity inputs** (`H2.coatomCutoffDeterminationLast_of_inputs`, through
`H2.hasRecCompletions_of`), on the grade-`K` faces (`H2.LawfulAt`: lawful below `(univ, K)`, `⊥`
above): donor raising with the gap (`H2.DonorRaisingAt`), owner lowering (`H2.OwnerLoweringAt`),
and the engine (`H2.AdmittedCompletionsAt`: an admission of states between the grade-`K` faces
gives the completion).  The order law at the owner and the frontier bound there are compiled
(`H2.frontier_le_lawfulAt`, through the extension at the cap `⊥`, `H2.exists_ext_bot_at`).

**At two points** the completions are `H2.exists_completion_recProp` at the lost point `1`, given
the case of top grade `1` (its hypothesis `hone`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

/-! ### The grade-`K` faces -/

/-- The **grade-`K` faces** of a stage type: labellings lawful below `(univ, K)` and `⊥` above. -/
def LawfulAt {α : Ordinal.{u}} {m : ℕ} (t : StageType.{u} α m) (K : ℕ)
    (W : Fin t.card → Label.{u}) : Prop :=
  t.rows.IsLawfulBelow ((univ : Finset (Fin m)), K) (fun d ↦ W d) ∧
    ∀ d, ¬ t.toCellScheme.grade d ≤ K → W d = ⊥

/-- A grade-`K` face extends at the cap `⊥` to a lawful labelling, unchanged at the grades at most
`K` (bountifulness from `(univ, K)` to `(univ, m)`). -/
theorem exists_ext_bot_at {α : Ordinal.{u}} {m K : ℕ} {t : StageType.{u} α m} (hleg : t.IsLegal)
    (hK0 : 0 < K) (hKm : K ≤ m) {W : Fin t.card → Label.{u}} (hW : LawfulAt t K W) :
    ∃ W', t.rows.IsLawful W' ∧ ∀ d, t.toCellScheme.grade d ≤ K → W' d = W d := by
  have hle : (((univ : Finset (Fin m)), K) : Finset (Fin m) × ℕ) ≤ ((univ : Finset (Fin m)), m) :=
    ⟨subset_rfl, hKm⟩
  obtain ⟨q', hq', -, hq'w⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hle).mp
    (hleg.isBountiful ⟨t.univ_mem_faces, hK0, by simpa using hKm⟩
      ⟨t.univ_mem_faces, hK0.trans_le hKm, by simp⟩ hle) ⊥ (isSelfVisible_bot m)
    (fun d ↦ W d) (fun _ ↦ ⊥) hW.1 (CellScheme.Rows.isLawfulBelow_const_bot _) (fun _ ↦ by simp)
  have hall (d : Fin t.card) : d ∈ t.toCellScheme.below ((univ : Finset (Fin m)), m) :=
    ⟨subset_univ _, t.grade_le d⟩
  exact ⟨fun d ↦ q' ⟨d, hall d⟩, hq'.isLawful hall, fun d hd ↦ hq'w ⟨d, subset_univ _, hd⟩⟩

/-- A cell **determined by the root on the grade-`K` faces**: two grade-`K` faces agreeing at
the root cells agree at it. -/
def RootDetAt {α : Ordinal.{u}} {m : ℕ} (t : StageType.{u} α (m + 1)) (K : ℕ)
    (x : Fin t.card) : Prop :=
  ∀ s s' : Fin t.card → Label.{u}, LawfulAt t K s → LawfulAt t K s' →
    (∀ y ∈ t.toScheme.visibleCells Fin.castSuccEmb, s y = s' y) → s x = s' x

/-- A cell of grade at most `K` determined by the root on the grade-`K` faces is determined by the
root (truncate lawful labellings above `K`). -/
theorem rootDet_of_rootDetAt {α : Ordinal.{u}} {m K : ℕ} {t : StageType.{u} α (m + 1)}
    {x : Fin t.card}
    (hx : t.toCellScheme.grade x ≤ K) (h : RootDetAt t K x) : RootDet t x := by
  classical
  intro s s' hs hs' hag
  have htr (q : Fin t.card → Label.{u}) (hq : t.rows.IsLawful q) :
      LawfulAt t K fun d ↦ if t.toCellScheme.grade d ≤ K then q d else ⊥ := by
    refine ⟨?_, fun d hd ↦ ite_eq_right hd⟩
    convert hq.isLawfulBelow ((univ : Finset (Fin (m + 1))), K) using 1
    exact funext fun d ↦ ite_eq_left d.2.2
  have := h _ _ (htr s hs) (htr s' hs') fun y hy ↦ by
    split_ifs
    · exact hag y hy
    · rfl
  simpa [hx] using this

/-! ### The target and its input -/

/-- **Coatom cutoff determination for source-gap contexts with the lost point last**, on `k + 1`
points (the clause of `Realization.CoatomCutoffDetermination` for
`StageType.IsSourceGapContextLast`). -/
def CoatomCutoffDeterminationLast : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (g : Fin n ↪ Fin k)
    (p : StageType.{u} α k), Order.IsSuccLimit α → t'.IsLegal →
    (∃ o r, t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r) →
    restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
      restrictFace (extendByLast g) tb = some d → d.topGrade ≤ K →
        ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Completions with the reading property** at a source-gap context `t'` on `k + 1` points with
the lost point last, for every legal coface `tb` of its coatom face and every designation. -/
def HasRecCompletions (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)) (hleg : t'.IsLegal)
    (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
      (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x ∈ Lo, tb.label x ≠ ⊤) → (∀ x, tb.label x ≠ ⊤ → x ∈ Lo) →
      (∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops) →
      ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
        RecProp F o r K Lo Tops

/-! ### The implication -/

/-- **h2 at one context with the lost point last**, from completions with the reading property at
its arity. -/
theorem exists_coface_last {α : Ordinal.{u}} {K n k : ℕ} (hrec : HasRecCompletions.{u} k)
    {t' : StageType.{u} α (k + 1)} {g : Fin n ↪ Fin k} {p : StageType.{u} α k}
    (hα : Order.IsSuccLimit α) (hleg : t'.IsLegal) {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r)
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α (k + 1)}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)
    (hdK : d.topGrade ≤ K) :
    ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d := by
  have hα' := hα.isSuccPrelimit
  set Lo : Finset (Fin tb.card) := univ.filter fun x ↦ tb.label x ≠ ⊤
  have := Classical.decPred (RootDetAt tb K)
  set Tops : Finset (Fin tb.card) := ((univ.filter fun x ↦ tb.label x = ⊤ ∧
    tb.toCellScheme.grade x ≤ K) \ tb.toScheme.visibleCells Fin.castSuccEmb) \
      (univ.filter (RootDetAt tb K))
  have hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤ := fun x hx ↦ (mem_filter.mp hx).2
  have hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb := by
    intro x hx
    simp only [Tops, mem_sdiff, mem_filter, mem_univ, true_and] at hx
    exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2⟩
  have hmem : ∀ x, tb.label x = ⊤ → x ∈ tb.toScheme.visibleCells (extendByLast g) →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops := by
    intro x hxt hxv hxr hxd
    have hg : tb.toCellScheme.grade x ≤ K := by
      obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hd) hxv
      have hdi : d.label i = ⊤ := (StageType.label_faceCell hd i).symm.trans hxt
      exact (StageType.grade_faceCell hd i).trans_le ((grade_le_topGrade hdi).trans hdK)
    have hxd' : ¬ RootDetAt tb K x := fun h ↦ hxd (rootDet_of_rootDetAt hg h)
    simp [Tops, hxt, hg, hxr, hxd']
  obtain ⟨F, hF⟩ := hrec t' hleg g hs hp htbleg htbp hLo (fun x hx ↦ by simp [Lo, hx]) hTops
    (fun x h1 h2 h3 h4 ↦ by
      have h4' : ¬ RootDetAt tb K x := fun h ↦ h4 (rootDet_of_rootDetAt h2 h)
      simp [Tops, h1, h2, h3, h4'])
    fun x h1 h2 h3 h4 ↦ by simp [Tops, h1, h2, h3, h4]
  obtain ⟨c, δ, hc, hδlab, hδ, hcδ⟩ := exists_cutoff K hα tb
  have hR := F.restrictFace_right_completion hα'
  refine ⟨F.completion hα', ⟨F.isLegal_completion hα', F.restrictFace_left_completion hα'⟩, hR,
    δ, hδ, ?_⟩
  have hd' : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') = some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  exact isDeterminedWithin_of_key (F.restrictFace_left_completion hα') hd'
    fun ℓ hℓ hleft hcap ↦ key_completion F hα' hs.label_owner hs.label_lost hF hc hδlab hcδ hLo
      hmem ℓ hℓ hleft hcap

/-- **h2 with the lost point last, from completions with the reading property** at every
arity. -/
theorem coatomCutoffDeterminationLast_of_hasRecCompletions
    (hrec : ∀ k, HasRecCompletions.{u} k) : CoatomCutoffDeterminationLast.{u} := by
  intro α K n k t' g p hα hleg ⟨o, r, hs⟩ hp tb ⟨htbleg, htbp⟩ d hd hdK
  exact exists_coface_last (hrec k) hα hleg hs hp htbleg htbp hd hdK

/-- The root cells of the coatom face carrying `⊤` (on `k + 1` points with the lost point last,
every root cell avoids the lost point). -/
def rootTops' {α : Ordinal.{u}} {k : ℕ} {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) : Set (Fin p.card) :=
  {a | p.label a = ⊤ ∧ Fin.last k ∉ t'.toCellScheme.scope (StageType.faceCell hp a)}

/-- **The order law at the owner and the frontier bound on the grade-`K` faces** of a legal
source-gap context of grade `K`. -/
theorem frontier_le_lawfulAt {α : Ordinal.{u}} {K m n : ℕ} {t' : StageType.{u} α m}
    (hleg : t'.IsLegal) {h : Fin n ↪ Fin m} {l : Fin m} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K h l o r) {f : Fin t'.card → Label.{u}}
    (hf : LawfulAt t' K f) :
    IsSelfVisible K (f o) ∧ ∀ a, t'.label a = ⊤ → l ∉ t'.toCellScheme.scope a →
      frontierAt o r K f ≤ f a := by
  have ho : t'.toCellScheme.grade o ≤ K := hs.grade_owner.le
  have hr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKm : K ≤ m := hs.grade_owner ▸ t'.grade_le o
  refine ⟨?_, fun a ha hla ↦ ?_⟩
  · have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hf.1).1 o ⟨subset_univ _, ho⟩
    rwa [hs.grade_owner] at this
  obtain ⟨f', hf', hf'f⟩ := exists_ext_bot_at hleg hK0 hKm hf
  have hag : t'.toCellScheme.grade a ≤ K := hs.topGrade_eq ▸ grade_le_topGrade ha
  have := hs.frontier_le hf' ha hla
  unfold frontierAt
  rwa [hf'f o ho, hf'f r hr, hf'f _ hag] at this

/-! ### The general-arity inputs -/

/-- **Donor raising with the gap on the grade-`K` faces** at a source-gap context on `k + 1`
points with the lost point last (generalizing `H2.donorRaisingGap_oneFace` and
`H2.donorRaising_two_of_root`). -/
def DonorRaisingAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)), t'.IsLegal →
    ∀ (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)}, tb.IsLegal →
      ∀ (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x, tb.label x ≠ ⊤ → x ∈ Lo) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops) →
      DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) K (LawfulAt t' K)
        (LawfulAt tb K) (rootTops' hp) (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops

/-- **Owner lowering on the grade-`K` faces** at a source-gap context on `k + 1` points with the
lost point last. -/
def OwnerLoweringAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)), t'.IsLegal →
    ∀ (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)}, tb.IsLegal →
      ∀ (htbp : restrictFace Fin.castSuccEmb tb = some p),
      OwnerLowering (StageType.faceCell hp) (StageType.faceCell htbp) o r K (LawfulAt t' K)
        (LawfulAt tb K)

/-- **The admitted completion on the grade-`K` faces** (the engine: the LOW row family at the
grades at least `max K` and the donor top grade): an admission of states between the grade-`K`
faces gives a completion below the full grade with the reading property. -/
def AdmittedCompletionsAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)) (hleg : t'.IsLegal)
    (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
      (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x ∈ Lo, tb.label x ≠ ⊤) →
      (∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) →
      IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) K (LawfulAt t' K)
        (LawfulAt tb K) (SelfLowG o r K (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops) →
      ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
        RecProp F o r K Lo Tops

/-- **Completions with the reading property from the three general-arity inputs**: donor raising
and owner lowering on the grade-`K` faces give the admission of states of the clause there
(`H2.selfLow_isStateAdmissionGap`, with the order law and the frontier bound of
`H2.frontier_le_lawfulAt`), and the engine gives the completion. -/
theorem hasRecCompletions_of {k : ℕ} (hDR : DonorRaisingAt.{u} k) (hOL : OwnerLoweringAt.{u} k)
    (hEN : AdmittedCompletionsAt.{u} k) : HasRecCompletions.{u} k := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops hLo hLo' hTops _ hTops'
  refine hEN t' hleg g hs hp htbleg htbp hLo hTops ?_
  refine selfLow_isStateAdmissionGap (rootTops' hp) (fun _ hf ↦ (frontier_le_lawfulAt hleg hs hf).1)
    (fun _ hf a ha ↦ ?_) (hDR t' hleg g hs hp htbleg htbp hLo' hTops')
    (hOL t' hleg g hs hp htbleg htbp)
  exact (frontier_le_lawfulAt hleg hs hf).2 _ ((StageType.label_faceCell hp a).trans ha.1) ha.2

/-- **h2 with the lost point last from the three general-arity inputs** at every arity. -/
theorem coatomCutoffDeterminationLast_of_inputs (hDR : ∀ k, DonorRaisingAt.{u} k)
    (hOL : ∀ k, OwnerLoweringAt.{u} k) (hEN : ∀ k, AdmittedCompletionsAt.{u} k) :
    CoatomCutoffDeterminationLast.{u} :=
  coatomCutoffDeterminationLast_of_hasRecCompletions fun k ↦
    hasRecCompletions_of (hDR k) (hOL k) (hEN k)

end VaughtConjecture.H2

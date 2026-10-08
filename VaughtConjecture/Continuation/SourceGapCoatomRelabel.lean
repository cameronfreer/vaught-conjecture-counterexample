/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledTower
import VaughtConjecture.Continuation.SourceGapSeparatedInstance

/-!
# The self-donor coatom step at every coatom

Roadmap, Layer 3 ((R2) of the table of 3.4, the coatom step of
`VaughtConjecture.Continuation.SourceGapCoatomStep` when the donor is the context, relabelled).

The coatom step (`StageType.HasTopReadingCoatomSteps`) quantifies over every closed coatom
`f : Fin m ↪ Fin (m + 1)` of the context `t'`, and its donor `d'` is a one-point coface of the face
`p` of `t'` along `f`: `d'` has face `p` along `Fin.castSuccEmb`.  At `f = Fin.castSuccEmb` the
context itself is such a donor (`StageType.exists_coatomStep_self_succ`).  At another coatom the
context is a donor **after relabelling its points**: for the permutation `σ` of `Fin (m + 1)` with
`Fin.castSuccEmb.trans σ = f` (it exists, `StageType.exists_perm_castSuccEmb_trans`, and is unique,
since it is `f` on the first `m` points and sends the last point to the point missed by `f`), the
reindexed context `t'.reindex σ` has face `p` along `Fin.castSuccEmb`
(`StageType.reindex_mem_cofaces_of_trans_eq`).

**The permutation action** is `StageType.reindex` (`VaughtConjecture.Stage.Basic`): the face map
along a bijection of points.  It commutes with the face maps (`StageType.restrictFace_reindex`),
composes (`StageType.reindex_reindex`) and keeps legality (`StageType.IsLegal.reindex`).  Added
here (compiled in this repository):

* `StageType.ReadsEachNewTop.of_reindex`: **the reading is transported along a relabelling** of
  the one-point coface that fixes the new point: if `D'` is the face of `D''` along a bijection `τ`
  fixing the last point, with `(extendByLast h).trans τ = extendByLast h''`, then reading each new
  top along `h''` in `D''` (over its face `t''`) gives reading each new top along `h` in `D'` (over
  its face `t'`).  The cells correspond through the face map along `τ`
  (`StageType.faceCell`); the cells of the two faces along `Fin.castSuccEmb` correspond because
  `τ` fixes the last point.
* `StageType.exists_coatomStep_self_any`: **the top-reading coatom step for the relabelled context
  at every coatom**: for every legal `t'` on `m + 1` points, every coatom `f` with face `p`, the
  permutation `σ` with `Fin.castSuccEmb.trans σ = f`, and every root `h = g.trans f`, one legal
  one-point coface `D'` of `t'` has face `t'.reindex σ` along `extendByLast f` and reads each new
  top along `h` at every cell of full scope, hence at its tops.  One `D'` is chosen for each input,
  before any labelling.  Proof: the coface of `t'.reindex σ` given by
  `StageType.exists_coatomStep_self_succ`, reindexed along the extension `τ` of `σ⁻¹` fixing the
  new point.
* `StageType.exists_coatomStep_self_any'`: the same with the permutation produced
  (`StageType.exists_perm_castSuccEmb_trans`, through `StageType.permOfEmbedding`), together with
  the membership of the donor `t'.reindex σ` in the cofaces of `p`.
* `StageType.exists_coatomStep_self_any_T` (a positive instance, feasibility only): at the input
  `SeparationObstruction.T α` along the coatom `{1}`, which is not `Fin.castSuccEmb`.

**Not treated.**  Donors other than relabellings of the context; and a donor `t'.reindex ρ` with
face `p` along `Fin.castSuccEmb` for a permutation `ρ` with `Fin.castSuccEmb.trans ρ ≠ f` (possible
only when `t'` has the same face along two coatoms).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

/-- A self-embedding of `Fin k` as a permutation. -/
noncomputable def permOfEmbedding {k : ℕ} (e : Fin k ↪ Fin k) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective e (Finite.injective_iff_bijective.mp e.injective)

@[simp] theorem permOfEmbedding_apply {k : ℕ} (e : Fin k ↪ Fin k) (i : Fin k) :
    permOfEmbedding e i = e i :=
  rfl

/-- **Every coatom is the first coatom after relabelling**: for every embedding
`f : Fin m ↪ Fin (m + 1)` some permutation `σ` has `Fin.castSuccEmb.trans σ = f`. -/
theorem exists_perm_castSuccEmb_trans {m : ℕ} (f : Fin m ↪ Fin (m + 1)) :
    ∃ σ : Equiv.Perm (Fin (m + 1)), Fin.castSuccEmb.trans σ.toEmbedding = f := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Set.range f := by
    by_contra hall
    push Not at hall
    have h := Fintype.card_le_of_surjective f fun a ↦ hall a
    simp at h
  refine ⟨permOfEmbedding (Fin.Embedding.snoc f ha), Function.Embedding.ext fun i ↦ ?_⟩
  simp [Fin.Embedding.snoc_castSucc]

variable {α : Ordinal.{u}}

/-- **The relabelled context is a donor at the coatom**: if `Fin.castSuccEmb.trans σ = f` and `p`
is the face of a legal `t'` along `f`, then `t'.reindex σ` is a legal one-point coface of `p`. -/
theorem reindex_mem_cofaces_of_trans_eq {m : ℕ} {t' : StageType.{u} α (m + 1)}
    (ht' : t'.IsLegal) {f : Fin m ↪ Fin (m + 1)} {p : StageType.{u} α m}
    (hp : restrictFace f t' = some p) {σ : Equiv.Perm (Fin (m + 1))}
    (hσ : Fin.castSuccEmb.trans σ.toEmbedding = f) : t'.reindex σ ∈ p.cofaces :=
  ⟨ht'.reindex σ, by rw [restrictFace_reindex, hσ, hp]⟩

/-- **The reading is transported along a relabelling fixing the new point**: if `D'` is the face of
`D''` along a bijection `τ` of the points fixing the last point, and `(extendByLast h).trans τ` is
`extendByLast h''`, then if `D''` reads each new top along `h''` over its face `t''`, `D'` reads
each new top along `h` over its face `t'`. -/
theorem ReadsEachNewTop.of_reindex {k n : ℕ} {t' t'' : StageType.{u} α k}
    {D' D'' : StageType.{u} α (k + 1)} {hD' : restrictFace Fin.castSuccEmb D' = some t'}
    {hD'' : restrictFace Fin.castSuccEmb D'' = some t''} {τ : Fin (k + 1) ≃ Fin (k + 1)}
    (hτ : restrictFace τ.toEmbedding D'' = some D') (hlast : τ (Fin.last k) = Fin.last k)
    {h h'' : Fin n ↪ Fin k} (hh : (extendByLast h).trans τ.toEmbedding = extendByLast h'')
    (hr : ReadsEachNewTop hD'' h'') : ReadsEachNewTop hD' h := by
  intro x hx hxl hxt
  have hsy : D''.toCellScheme.scope (faceCell hτ x) =
      (D'.toCellScheme.scope x).map τ.toEmbedding := scope_faceCell hτ x
  have hy : faceCell hτ x ∈ D''.visibleCells (extendByLast h'') := by
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and] at hx ⊢
    rw [hsy, ← hh, ← map_map]
    exact map_subset_map.mpr hx
  have hyl : Fin.last k ∈ D''.toCellScheme.scope (faceCell hτ x) := by
    rw [hsy]
    exact mem_map.mpr ⟨_, hxl, hlast⟩
  have hyt : D''.label (faceCell hτ x) = ⊤ := by rw [label_faceCell]; exact hxt
  obtain ⟨w, s, hw, hs, hsw, hyw, hu⟩ := hr _ hy hyl hyt
  -- the cells of the face `t''` are cells of the face `t'`, through `τ`
  have back (z : Fin t''.card) : ∃ z' : Fin t'.card,
      faceCell hτ (faceCell hD' z') = faceCell hD'' z := by
    obtain ⟨a, ha⟩ := D''.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hτ)
      (d := faceCell hD'' z) (Scheme.mem_visibleCells.mpr fun y _ ↦ ⟨τ.symm y, by simp⟩)
    have hal : Fin.last k ∉ D'.toCellScheme.scope a := fun hm ↦ by
      apply last_notMem_scope_faceCell hD'' z
      have ha' : faceCell hτ a = faceCell hD'' z := ha
      rw [← ha', scope_faceCell]
      exact mem_map.mpr ⟨_, hm, hlast⟩
    obtain ⟨z', rfl⟩ := exists_faceCell_eq_of_last_notMem hD' hal
    exact ⟨z', ha⟩
  have hlab {z : Fin t''.card} {z' : Fin t'.card}
      (he : faceCell hτ (faceCell hD' z') = faceCell hD'' z) : t'.label z' = t''.label z := by
    rw [← label_faceCell hD', ← label_faceCell hτ, he, label_faceCell]
  have hgr {z : Fin t''.card} {z' : Fin t'.card}
      (he : faceCell hτ (faceCell hD' z') = faceCell hD'' z) :
      t'.toCellScheme.grade z' = t''.toCellScheme.grade z := by
    rw [← grade_faceCell hD', ← grade_faceCell hτ, he, grade_faceCell]
  obtain ⟨w', hw'⟩ := back w
  obtain ⟨s', hs'⟩ := back s
  refine ⟨w', s', (hlab hw').trans hw, (hlab hs').trans hs, by rw [hgr hw', hgr hs']; exact hsw,
    ?_, fun u hu' ↦ ?_⟩
  · rw [hgr hw', ← grade_faceCell hτ x]
    exact hyw
  · have hu'' : D''.toCellScheme.gradedIndex (faceCell hτ u) =
        ((univ : Finset (Fin (k + 1))), t''.toCellScheme.grade w) := by
      refine Prod.ext ?_ ?_
      · change D''.toCellScheme.scope (faceCell hτ u) = univ
        rw [scope_faceCell, show D'.toCellScheme.scope u = univ from congrArg Prod.fst hu',
          map_univ_equiv]
      · change D''.toCellScheme.grade (faceCell hτ u) = _
        rw [grade_faceCell, ← hgr hw']
        exact congrArg Prod.snd hu'
    rw [SeparatedInstance.rowAt_faceCell hτ, SeparatedInstance.rowAt_faceCell hτ, hs']
    exact hu _ hu''

/-- **The top-reading coatom step for the relabelled context at every coatom**: for every legal
`t'` on `m + 1` points, every coatom `f` of `t'` with face `p`, the permutation `σ` with
`Fin.castSuccEmb.trans σ = f`, and every root `h = g.trans f`, one legal one-point coface `D'` of
`t'` has face `t'.reindex σ` along `extendByLast f` and reads each new top along `h` at every cell
of full scope, hence at its tops.  No hypothesis on the stage or on the context is used. -/
theorem exists_coatomStep_self_any {m : ℕ} {t' : StageType.{u} α (m + 1)} (ht' : t'.IsLegal)
    {f : Fin m ↪ Fin (m + 1)} {p : StageType.{u} α m} (hp : restrictFace f t' = some p)
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : Fin.castSuccEmb.trans σ.toEmbedding = f) {n : ℕ}
    (g : Fin n ↪ Fin m) {h : Fin n ↪ Fin (m + 1)} (hg : g.trans f = h) :
    ∃ (D' : StageType.{u} α (m + 2)) (hD' : D' ∈ t'.cofaces),
      restrictFace (extendByLast f) D' = some (t'.reindex σ) ∧ ReadsEachNewTop hD'.2 h ∧
        ReadsEachNewTopAtTops hD'.2 h := by
  obtain ⟨hl'', hp''⟩ := reindex_mem_cofaces_of_trans_eq ht' hp hσ
  obtain ⟨D'', hD'', hface'', hr'', -⟩ := exists_coatomStep_self_succ hl'' hp'' g rfl
  -- the extension of `σ⁻¹` fixing the new point
  set τ := permOfEmbedding (extendByLast σ.symm.toEmbedding) with hτdef
  have hτc (i : Fin (m + 1)) : τ i.castSucc = (σ.symm i).castSucc := by
    rw [hτdef, permOfEmbedding_apply, extendByLast_castSucc]
    rfl
  have hτl : τ (Fin.last (m + 1)) = Fin.last (m + 1) := by
    rw [hτdef, permOfEmbedding_apply, extendByLast_last]
  have hσf (i : Fin m) : σ.symm (f i) = i.castSucc := by
    rw [← hσ]
    simp
  have hext (j : Fin n ↪ Fin (m + 1)) (j'' : Fin n ↪ Fin m)
      (hj : ∀ i, σ.symm (j i) = (j'' i).castSucc) :
      (extendByLast j).trans τ.toEmbedding = extendByLast (j''.trans Fin.castSuccEmb) := by
    refine Function.Embedding.ext fun i ↦ ?_
    induction i using Fin.lastCases with
    | last => simp [hτl]
    | cast i => simp [hτc, hj]
  have h1 : restrictFace Fin.castSuccEmb (D''.reindex τ) = some t' := by
    have he : Fin.castSuccEmb.trans τ.toEmbedding = σ.symm.toEmbedding.trans Fin.castSuccEmb :=
      Function.Embedding.ext fun i ↦ by simp [hτc]
    rw [restrictFace_reindex, he, ← restrictFace_trans D'' _ _ hD''.2, restrictFace_equiv,
      reindex_reindex, Equiv.symm_trans_self, reindex_refl]
  have h2 : restrictFace (extendByLast f) (D''.reindex τ) = some (t'.reindex σ) := by
    have he : (extendByLast f).trans τ.toEmbedding = extendByLast Fin.castSuccEmb := by
      refine Function.Embedding.ext fun i ↦ ?_
      induction i using Fin.lastCases with
      | last => simp [hτl]
      | cast i => simp [hτc, hσf]
    rw [restrictFace_reindex, he, hface'']
  have hr : ReadsEachNewTop h1 h :=
    hr''.of_reindex (restrictFace_equiv D'' τ) hτl
      (hext h g fun i ↦ by rw [← hg]; exact hσf (g i))
  exact ⟨D''.reindex τ, ⟨hD''.1.reindex τ, h1⟩, h2, hr, hr.atTops⟩

/-- **The relabelled self-donor coatom step without the permutation in the hypotheses**: for every
legal `t'` on `m + 1` points, every coatom `f` with face `p`, and every root `h = g.trans f`, some
relabelling `t'.reindex σ` of `t'` is a legal one-point coface of `p`, and one legal one-point
coface `D'` of `t'` has face `t'.reindex σ` along `extendByLast f` and reads each new top along `h`
at every cell of full scope and at its tops. -/
theorem exists_coatomStep_self_any' {m : ℕ} {t' : StageType.{u} α (m + 1)} (ht' : t'.IsLegal)
    {f : Fin m ↪ Fin (m + 1)} {p : StageType.{u} α m} (hp : restrictFace f t' = some p) {n : ℕ}
    (g : Fin n ↪ Fin m) {h : Fin n ↪ Fin (m + 1)} (hg : g.trans f = h) :
    ∃ σ : Equiv.Perm (Fin (m + 1)), Fin.castSuccEmb.trans σ.toEmbedding = f ∧
      t'.reindex σ ∈ p.cofaces ∧
      ∃ (D' : StageType.{u} α (m + 2)) (hD' : D' ∈ t'.cofaces),
        restrictFace (extendByLast f) D' = some (t'.reindex σ) ∧ ReadsEachNewTop hD'.2 h ∧
          ReadsEachNewTopAtTops hD'.2 h := by
  obtain ⟨σ, hσ⟩ := exists_perm_castSuccEmb_trans f
  exact ⟨σ, hσ, reindex_mem_cofaces_of_trans_eq ht' hp hσ,
    exists_coatomStep_self_any ht' hp hσ g hg⟩

/-- The coatom `{1}` of a type on two points: the point `0` sent to `1`. -/
def coatomOne : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, fun a b _ ↦ Subsingleton.elim a b⟩

/-- **A positive instance at the coatom other than `Fin.castSuccEmb`** (feasibility only): at the
input `SeparationObstruction.T α`, along the coatom `{1}` and the root `{1}`, the relabelled
context is a donor and a reading coface exists. -/
theorem exists_coatomStep_self_any_T (α : Ordinal.{u}) :
    ∃ σ : Equiv.Perm (Fin 2), Fin.castSuccEmb.trans σ.toEmbedding = coatomOne ∧
      ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ (SeparationObstruction.T α).cofaces),
        restrictFace (extendByLast coatomOne) D' = some ((SeparationObstruction.T α).reindex σ) ∧
        ReadsEachNewTopAtTops hD'.2 coatomOne := by
  have hf : univ.map coatomOne ∈ (SeparationObstruction.T α).toCellScheme.faces := by
    -- the faces of the input are the interval plan
    change _ ∈ Geometry.intervalPlan univ
    decide
  obtain ⟨σ, hσ, -, D', hD', h2, -, hr⟩ := exists_coatomStep_self_any'
    (SeparationObstruction.isLegal_T α) (restrictFace_of_mem _ _ hf)
    (Function.Embedding.refl _) (h := coatomOne) rfl
  exact ⟨σ, hσ, D', hD', h2, hr⟩

end StageType

end VaughtConjecture

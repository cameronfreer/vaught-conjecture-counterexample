/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralOwner

/-!
# Owner lowering below the designated tops on the grade-`K` faces (work file)

WORK FILE (branch `research/work-ownerAt`).  No `sorry`.

On `k + 1` points with the lost point last, below the full grade (`K ≤ k`), the root (the cells of
the common face, which avoid the lost point) has cells of grade `K`, so the cap at the grade `K` of
`FieldAdmission.ownerLowering_of_isLegal` would move them.  Here the cap is taken only on the cells
through the lost point (`CellScheme.Rows.IsLawful.min_const_of_mem_scope`), after the capped lift
of the donor face's root at the cap `h` (bountifulness from the root face to `(univ, K)`).  The
owner has full scope, so it is capped, and the frontier is at most the cap.  Availability at the
capped cells asks that the cells avoiding the lost point, the root, be at most the cap; on the
grade-`K` faces the cells above `K` are `⊥`.  So the cap must lie between `h`, the replaced maximum
of the root of the donor face, and every designated top concerned.

* **The residual** (`H2.RootBelowTops`, a named condition on the donor faces): for every donor face
  and every designated top `t` at least `h` and above the replaced maximum of the designated cells
  below the top, the replaced maximum of the root is at most `t`.
* **The implication** (`H2.ownerLoweringBelow_of_rootBelowTops`, every arity `k + 1` and every
  `K ≤ k`; `H2.ownerLoweringBelowAt_of_rootBelowTopsAt`, the form `H2.OwnerLoweringBelowAt k`).
* **No root top** (`H2.rootBelowTops_of_forall_ne_top`): when no root cell of the donor is labelled
  `⊤`, every root cell is a designated cell below the top, and the residual holds.

The residual can fail only through root cells labelled `⊤`: a root top `a` of grade at most `K`
whose value in the donor face is above a designated top.  **It does fail at a legal context**
(`OwnerGradeOneTop.not_rootBelowTopsAt_one`, module
`VaughtConjecture.Continuation.H2OwnerAtTop`): at the owner lane's context `OwnerGradeOneTop.ctx`
(two points, grade `1`) the lost top lies below the root top in every lawful labelling, so a donor
face with the designated lost top below the root top violates it.  There owner lowering below the
designated tops need not fail: the lost top, not the owner, has to be lowered.  So the cap through
the lost point is too strong a route below the full grade; the cap on the cells read by the owner at
most the lost top (the owner lane's construction at grade `1`) is the one to generalize.  Owner
lowering below the designated tops itself fails only if the root top also bounds the lost top from
below (the owner and the lost top alone at graded indices above that of the root top, same grade:
three points at least; not compiled).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- **The root below the designated tops** (a named condition on the donor faces): for every cap
`h` self-visible at `K`, every donor face `g`, and every designated top `t` with `h ≤ g t` above the
replaced maximum of `Lo`, the replaced maximum of `g` on the root is at most `g t`. -/
def RootBelowTops {ιR ιD : Type*} [Fintype ιR] (rd : ιR → ιD) (K : ℕ)
    (D : (ιD → Label.{u}) → Prop) (Lo Tops : Finset ιD) : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible K h → ∀ {g : ιD → Label.{u}}, D g → ∀ t ∈ Tops, h ≤ g t →
    visibilityReplace K K (Lo.sup g) < g t →
      visibilityReplace K K (Finset.univ.sup fun x ↦ g (rd x)) ≤ g t

/-- **Owner lowering below the designated tops on the grade-`K` faces from the root below the
designated tops**, at a legal source-gap context of grade `K ≤ k` on `k + 1` points with the lost
point last: the capped lift of the root of the donor face at `h`, then the cap at
`max h (visibilityReplace K K (sup of the root))` on the cells through the lost point. -/
theorem ownerLoweringBelow_of_rootBelowTops {k n K : ℕ} {t' : StageType.{u} α (k + 1)}
    (hleg : t'.IsLegal) {g₀ : Fin n ↪ Fin k} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g₀.trans Fin.castSuccEmb) (Fin.last k) o r) (hKk : K ≤ k)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α (k + 1)} (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)}
    (hres : RootBelowTops (StageType.faceCell htbp) K (LawfulAt tb K) Lo Tops) :
    OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r K (LawfulAt t' K)
      (LawfulAt tb K) Lo Tops := by
  classical
  intro h hh L g hL hg hroot
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  -- the root of the donor face, lawful on the common face
  have hetb := StageType.comap_toScheme_of_restrictFace htbp
  have het := StageType.comap_toScheme_of_restrictFace hp
  obtain ⟨hfm, -⟩ := (StageType.restrictFace_eq_some_iff (t := t') (f := Fin.castSuccEmb)).mp hp
  have hXle : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), K) ≤
      ((univ : Finset (Fin (k + 1))), K) := ⟨subset_univ _, le_rfl⟩
  have hy : p.rows.IsLawfulBelow ((univ : Finset (Fin k)), K)
      (fun i ↦ g (StageType.faceCell htbp i)) :=
    (Scheme.isLawfulBelow_faceCell_iff hetb _ g).mpr (by exact hg.1.mono hXle)
  have hinj : Function.Injective (StageType.faceCell hp) := by
    intro i j hij
    have := (t'.toScheme.cellMap Fin.castSuccEmb).injective hij
    exact Fin.cast_injective _ this
  set x : Fin t'.card → Label.{u} := Function.extend (StageType.faceCell hp)
    (fun i ↦ g (StageType.faceCell htbp i)) (fun _ ↦ ⊥)
  have hx (i : Fin p.card) : x (StageType.faceCell hp i) = g (StageType.faceCell htbp i) :=
    hinj.extend_apply _ _ i
  have hpX : t'.rows.IsLawfulBelow
      (Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), K)) (fun d ↦ x d) := by
    refine (Scheme.isLawfulBelow_faceCell_iff het _ x).mp ?_
    convert hy using 2 with i
    exact hx i.1
  have hX : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), K) ∈
      t'.toCellScheme.gradedFaces := ⟨hfm, hK0, by simpa using hKk⟩
  have hY : ((univ : Finset (Fin (k + 1))), K) ∈ t'.toCellScheme.gradedFaces :=
    ⟨t'.univ_mem_faces, hK0, by simp; omega⟩
  have hlift := (CellScheme.Rows.cappedLift_iff_forall_exists hXle).mp
    (hleg.isBountiful hX hY hXle) h hh (fun d ↦ x d) (fun d ↦ L d) hpX hL.1 (fun d ↦ ?_)
  rotate_left
  · have hvis : d.1 ∈ t'.toScheme.visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
      have hy' : y ∈ (univ : Finset (Fin k)).map Fin.castSuccEmb := d.2.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq het hvis
    change min (L d.1) h = min (x d.1) h
    rw [← hi]
    change min (L (StageType.faceCell hp i)) h = min (x (StageType.faceCell hp i)) h
    rw [hx]
    exact (hroot i).symm
  obtain ⟨q', hq', hq'L, hq'x⟩ := hlift
  -- the capped lift, `⊥` above `K`
  set W₁ : Fin t'.card → Label.{u} := fun d ↦
    if hd : d ∈ t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K) then q' ⟨d, hd⟩
    else ⊥ with hW₁def
  have hW₁in {d : Fin t'.card} (hd : d ∈ t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K)) :
      W₁ d = q' ⟨d, hd⟩ := dite_eq_left hd
  have hW₁out {d : Fin t'.card}
      (hd : d ∉ t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K)) : W₁ d = ⊥ :=
    dite_eq_right hd
  have hW₁law : t'.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), K) (fun d ↦ W₁ d) := by
    convert hq' using 1
    exact funext fun d ↦ hW₁in d.2
  have hW₁root (i : Fin p.card) :
      W₁ (StageType.faceCell hp i) = g (StageType.faceCell htbp i) := by
    by_cases hd : StageType.faceCell hp i ∈ t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K)
    · rw [hW₁in hd]
      have hvX : StageType.faceCell hp i ∈ t'.toCellScheme.below
          (Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), K)) :=
        ⟨show t'.toCellScheme.scope (StageType.faceCell hp i) ⊆ _ by
          rw [StageType.scope_faceCell]; exact map_subset_map.mpr (subset_univ _), hd.2⟩
      exact (hq'x ⟨_, hvX⟩).trans (hx i)
    · rw [hW₁out hd]
      refine (hg.2 _ fun hle ↦ hd ⟨subset_univ _, ?_⟩).symm
      change t'.toCellScheme.grade (StageType.faceCell hp i) ≤ K
      rw [StageType.grade_faceCell] at hle ⊢
      exact hle
  -- the cap through the lost point
  obtain ⟨S, hSdef⟩ : ∃ S, S = Finset.univ.sup fun x ↦ g (StageType.faceCell htbp x) :=
    ⟨_, rfl⟩
  have hSle (z : Fin p.card) : g (StageType.faceCell htbp z) ≤ S := by
    rw [hSdef]
    exact Finset.le_sup (f := fun x ↦ g (StageType.faceCell htbp x)) (mem_univ z)
  obtain ⟨c, hcdef⟩ : ∃ c, c = max h (visibilityReplace K K S) := ⟨_, rfl⟩
  have hhc : h ≤ c := by rw [hcdef]; exact le_max_left _ _
  have hSc : S ≤ c := by
    rw [hcdef]; exact (le_visibilityReplace (by omega) S).trans (le_max_right _ _)
  have hc : IsSelfVisible K c := by
    rcases le_total h (visibilityReplace K K S) with hle | hle
    · rw [hcdef, max_eq_right hle]
      exact visibilityReplace_self_visibilityReplace le_rfl _
    · rw [hcdef, max_eq_left hle]
      exact hh
  have hroot_c : ∀ s : t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K),
      Fin.last k ∉ t'.toCellScheme.scope s.1 → W₁ s.1 ≤ c := fun s hsl ↦ by
    obtain ⟨z, hz⟩ := StageType.exists_faceCell_eq_of_last_notMem hp hsl
    rw [← hz, hW₁root]
    exact (hSle z).trans hSc
  have hWlaw : t'.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), K) (fun d ↦
      if Fin.last k ∈ t'.toCellScheme.scope d.1 then min (W₁ d.1) c else W₁ d.1) :=
    CellScheme.Rows.isLawfulBelow_iff.mpr
      ((CellScheme.Rows.isLawfulBelow_iff.mp hW₁law).min_const_of_mem_scope (Fin.last k)
        (K := K) (fun d ↦ d.2.2) hc fun s _ _ _ hsl _ ↦ hroot_c s hsl)
  refine ⟨fun d ↦ if Fin.last k ∈ t'.toCellScheme.scope d then min (W₁ d) c else W₁ d,
    ⟨hWlaw, fun d hd ↦ ?_⟩, fun i ↦ ?_, fun d ↦ ?_, fun t ht hgt hlt ↦ ?_⟩
  · have hdo : d ∉ t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K) := fun h' ↦ hd h'.2
    change (if Fin.last k ∈ t'.toCellScheme.scope d then min (W₁ d) c else W₁ d) = ⊥
    rw [hW₁out hdo]
    split_ifs
    · exact min_eq_left bot_le
    · rfl
  · change (if Fin.last k ∈ t'.toCellScheme.scope (StageType.faceCell hp i) then
      min (W₁ (StageType.faceCell hp i)) c else W₁ (StageType.faceCell hp i)) = _
    rw [ite_eq_right (StageType.last_notMem_scope_faceCell hp i), hW₁root]
  · have hW₁L : min (W₁ d) h = min (L d) h := by
      by_cases hd : d ∈ t'.toCellScheme.below ((univ : Finset (Fin (k + 1))), K)
      · rw [hW₁in hd]
        exact hq'L ⟨d, hd⟩
      · rw [hW₁out hd, hL.2 d fun h' ↦ hd ⟨subset_univ _, h'⟩]
    change min (if Fin.last k ∈ t'.toCellScheme.scope d then min (W₁ d) c else W₁ d) h = _
    split_ifs
    · rw [min_assoc, min_eq_right hhc, hW₁L]
    · exact hW₁L
  · have hco : c ≤ g t := by
      rw [hcdef]
      refine max_le hgt ?_
      have := hres hh hg t ht hgt hlt
      rwa [← hSdef] at this
    have hlo : Fin.last k ∈ t'.toCellScheme.scope o := by
      rw [hs.scope_owner]; exact mem_univ _
    refine (min_le_left _ _).trans ?_
    change (if Fin.last k ∈ t'.toCellScheme.scope o then min (W₁ o) c else W₁ o) ≤ g t
    rw [ite_eq_left hlo]
    exact (min_le_right _ _).trans hco

/-- **The root below the designated tops when no root cell is a top**: every root cell is then a
designated cell below the top (or `⊥` on the grade-`K` faces). -/
theorem rootBelowTops_of_forall_ne_top {k K : ℕ} {p : StageType.{u} α k}
    {tb : StageType.{u} α (k + 1)} (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hnt : ∀ x : Fin p.card, p.label x ≠ ⊤) :
    RootBelowTops (StageType.faceCell htbp) K (LawfulAt tb K)
      (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops := by
  intro h _ g hg t _ _ hlt
  refine (monotone_visibilityReplace le_rfl ?_).trans hlt.le
  refine Finset.sup_le fun x _ ↦ ?_
  by_cases hx : tb.toCellScheme.grade (StageType.faceCell htbp x) ≤ K
  · refine Finset.le_sup (f := g) (mem_filter.mpr ⟨hLo _ ?_, hx⟩)
    rw [StageType.label_faceCell]
    exact hnt x
  · rw [hg.2 _ hx]
    exact bot_le

/-- **The root below the designated tops at every legal context of arity `k + 1`** (a named
condition, in the binders of `H2.OwnerLoweringBelowAt`). -/
def RootBelowTopsAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)), t'.IsLegal →
    ∀ (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r → K ≤ k →
    ∀ {p : StageType.{u} α k} (_ : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)}, tb.IsLegal →
      ∀ (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x, tb.label x ≠ ⊤ → x ∈ Lo) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops) →
      RootBelowTops (StageType.faceCell htbp) K (LawfulAt tb K)
        (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops

/-- **`H2.OwnerLoweringBelowAt k` from the root below the designated tops**, at every arity
`k + 1` (`H2.ownerLoweringBelow_of_rootBelowTops`). -/
theorem ownerLoweringBelowAt_of_rootBelowTopsAt {k : ℕ} (hres : RootBelowTopsAt.{u} k) :
    OwnerLoweringBelowAt.{u} k := by
  intro α K n t' hleg g o r hs hKk p hp tb htbleg htbp Lo Tops hLo hTops
  exact ownerLoweringBelow_of_rootBelowTops hleg hs hKk hp htbp
    (hres t' hleg g hs hKk hp htbleg htbp hLo hTops)

end VaughtConjecture.H2

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CutoffCoatomRelabel
import VaughtConjecture.MainTheorem.GrowthAdmittedCarrier

/-!
# Growth carriers under relabelling

Roadmap, Layer 3 ((R3) and (R4), the growth carrier at a calibrated context).

A growth carrier for a context scheme `C` on `J` points and a donor scheme `P` along a root `e` is
a legal scheme on `J + 1` points with `C` and `P` as literal faces (`GrowthCarrier`).  For a
permutation `σ` of the points of the context, let `τ` be its extension fixing the new point
(`StageType.extendPerm`).  A carrier for the relabelled context `C.comap σ` along a root `e''`
gives, reindexed along `τ⁻¹`, a carrier for `C` along `e''.trans σ`
(`GrowthCarrier.relabel`): the context face along the first points is `C` itself and the donor
face along the root followed by the new point is `P` itself, both literally.

Reindexing along a bijection keeps every cell, with its rows (`Scheme.surjective_cellMap_equiv`),
so lawful sections correspond (`CellScheme.Rows.isLawful_comap_equiv_iff`), and the cells of the
two faces correspond with their positions (`GrowthCarrier.relabel_contextCell`,
`GrowthCarrier.relabel_donorCell`).  Hence **recovery is transported**
(`GrowthCarrier.Recovers.relabel`): if the relabelled carrier recovers `ρ` from the section `s`
read along the cell map of `σ`, the carrier for `C` recovers `ρ` from `s`.

**The surjective root.**  Calibrated requests (`StageType.GrowthRequests.Calibrated`) have a cap of
full scope whose grade, the threshold, is at least `n + 1`; grades are at most the number of points,
so `n < k` and the root is not onto (`StageType.GrowthRequests.Calibrated.lt`,
`StageType.GrowthRequests.Calibrated.not_surjective`).  The same holds for the hollow reference
calibration (`StageType.HollowReferenceCalibration'.not_surjective`), whose marked cap has grade
above `j + 1` for an enlarged root on `j ≥ n` points.  So every contract of the chain of record is
vacuous at a surjective root: no carrier is asked for there.

## References

Reindexing of stage types is [Kni26, Definition 3.1.2]; the growth construction is that of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace Scheme

variable {N m k : ℕ} (S : Scheme.{u} N)

/-- **Cells of a face of a face**: the cell of `S` under a cell of the face along `g` of the face
along `f` is the cell of the face of `S` along the composite, at the same position. -/
theorem cellMap_faceCell_comap (f : Fin m ↪ Fin N) (g : Fin k ↪ Fin m) {U : Scheme.{u} k}
    (hg : (S.comap f).comap g = U) (x : Fin U.card) :
    S.cellMap f ((S.comap f).faceCell g hg x) =
      S.faceCell (g.trans f) ((S.comap_comap f g).symm.trans hg) x := by
  subst hg
  exact S.cellMap_cellMap f g rfl

/-- The cells of the faces along equal embeddings agree. -/
theorem faceCell_congr {f f' : Fin m ↪ Fin N} (hf : f = f') {U : Scheme.{u} m}
    (h : S.comap f = U) (h' : S.comap f' = U) (x : Fin U.card) :
    S.faceCell f h x = S.faceCell f' h' x := by
  subst hf
  rfl

/-- The face along the identity has the cells themselves. -/
theorem faceCell_refl (h : S.comap (Function.Embedding.refl (Fin N)) = S) (x : Fin S.card) :
    S.faceCell (Function.Embedding.refl (Fin N)) h x = x :=
  (S.cellMap_eq_of_strictMono _ strictMono_id
    (fun d ↦ by simp [Function.Embedding.coe_refl]) rfl).symm

/-- **Reindexing back**: along a permutation `σ`, the face along `σ⁻¹` of the reindexed scheme is
the scheme itself, and its cell at the image of a cell `y` under the cell map of `σ` is `y`. -/
theorem faceCell_symm_cellMap (σ : Equiv.Perm (Fin N))
    (h : (S.comap σ.toEmbedding).comap σ.symm.toEmbedding = S)
    (y : Fin (S.comap σ.toEmbedding).card) :
    (S.comap σ.toEmbedding).faceCell σ.symm.toEmbedding h (S.cellMap σ.toEmbedding y) = y := by
  have hrefl : σ.symm.toEmbedding.trans σ.toEmbedding = Function.Embedding.refl (Fin N) :=
    Function.Embedding.ext fun i ↦ by simp
  apply (S.cellMap σ.toEmbedding).injective
  rw [S.cellMap_faceCell_comap, S.faceCell_congr hrefl _ (by rw [comap_refl]), faceCell_refl]

/-- **Reindexing back**, for a scheme equal to the reindexed scheme: the cell at the image of `y`
is `y`, at the same position. -/
theorem faceCell_symm_cellMap_of_eq (σ : Equiv.Perm (Fin N)) {D : Scheme.{u} N}
    (hD : D = S.comap σ.toEmbedding) (h : D.comap σ.symm.toEmbedding = S)
    (y : Fin (S.comap σ.toEmbedding).card) :
    D.faceCell σ.symm.toEmbedding h (S.cellMap σ.toEmbedding y) =
      Fin.cast (congrArg Scheme.card hD).symm y := by
  subst hD
  exact S.faceCell_symm_cellMap σ h y

/-- Restriction along a permutation and then its inverse is the identity. -/
theorem comap_symm_comap (σ : Equiv.Perm (Fin N)) :
    (S.comap σ.toEmbedding).comap σ.symm.toEmbedding = S := by
  rw [comap_comap, show σ.symm.toEmbedding.trans σ.toEmbedding =
    Function.Embedding.refl (Fin N) from Function.Embedding.ext fun i ↦ by simp, comap_refl]

/-- **Lawful sections along a permutation**: the cell map of a permutation of the points is a
bijection of the cells, and a labelling of the cells of `S` is lawful exactly when its reading
along the cell map is lawful for the reindexed scheme. -/
theorem isLawful_comap_perm_iff (σ : Equiv.Perm (Fin N)) (x : Fin S.card → Label.{u}) :
    (S.comap σ.toEmbedding).rows.IsLawful (fun i ↦ x (S.cellMap σ.toEmbedding i)) ↔
      S.rows.IsLawful x := by
  let φ : Fin (S.comap σ.toEmbedding).card ≃ Fin S.card :=
    Equiv.ofBijective (S.cellMap σ.toEmbedding)
      ⟨(S.cellMap σ.toEmbedding).injective, S.surjective_cellMap_equiv σ⟩
  exact CellScheme.Rows.isLawful_comap_equiv_iff (R := S.rows) (e := φ)
    (S.isLowerEmbedding_comap σ.toEmbedding)

end Scheme

namespace GrowthCarrier

variable {J n : ℕ} {C : Scheme.{u} J} {P : Scheme.{u} (n + 1)}

/-- **The relabelled carrier**: a growth carrier for the relabelled context `C.comap σ` along
`e''`, reindexed along the inverse of the extension of `σ` fixing the new point, is a growth
carrier for `C` along `e''.trans σ`, with literal faces. -/
noncomputable def relabel (σ : Equiv.Perm (Fin J)) {e'' : Fin n ↪ Fin J}
    (G : GrowthCarrier (C.comap σ.toEmbedding) P e'') :
    GrowthCarrier C P (e''.trans σ.toEmbedding) where
  scheme := G.scheme.comap (extendPerm σ).symm.toEmbedding
  isLegal := G.isLegal.reindex _
  context_mem := by
    rw [Scheme.mem_comap_faces, map_map, castSuccEmb_trans_extendPerm_symm, ← map_map,
      map_univ_equiv]
    exact G.context_mem
  comap_context := by
    rw [Scheme.comap_comap, castSuccEmb_trans_extendPerm_symm, ← Scheme.comap_comap,
      G.comap_context, Scheme.comap_symm_comap]
  donor_mem := by
    rw [Scheme.mem_comap_faces, map_map, extendByLast_trans_extendPerm_symm,
      show (e''.trans σ.toEmbedding).trans σ.symm.toEmbedding = e'' from
        Function.Embedding.ext fun i ↦ by simp]
    exact G.donor_mem
  comap_donor := by
    rw [Scheme.comap_comap, extendByLast_trans_extendPerm_symm,
      show (e''.trans σ.toEmbedding).trans σ.symm.toEmbedding = e'' from
        Function.Embedding.ext fun i ↦ by simp]
    exact G.comap_donor

variable (σ : Equiv.Perm (Fin J)) {e'' : Fin n ↪ Fin J}
  (G : GrowthCarrier (C.comap σ.toEmbedding) P e'')

/-- The scheme of the relabelled carrier is the carrier reindexed along the inverse extension. -/
theorem relabel_scheme :
    (G.relabel σ).scheme = G.scheme.comap (extendPerm σ).symm.toEmbedding :=
  rfl

/-- **The donor cells correspond**: the cell of the carrier under a donor cell of the relabelled
carrier is the donor cell of the carrier at the same position. -/
theorem relabel_donorCell (j : Fin P.card) :
    G.scheme.cellMap (extendPerm σ).symm.toEmbedding
        ((G.relabel σ).scheme.faceCell (extendByLast (e''.trans σ.toEmbedding))
          (G.relabel σ).comap_donor j) =
      G.scheme.faceCell (extendByLast e'') G.comap_donor j := by
  refine (G.scheme.cellMap_faceCell_comap _ _ (G.relabel σ).comap_donor j).trans ?_
  refine G.scheme.faceCell_congr ?_ _ _ j
  rw [extendByLast_trans_extendPerm_symm]
  congr 1
  exact Function.Embedding.ext fun i ↦ by simp

/-- **The context cells correspond**: the cell of the carrier under the context cell of the
relabelled carrier at the image of a cell `y` of `C.comap σ` under the cell map of `σ` is the
context cell of the carrier at `y`. -/
theorem relabel_contextCell (y : Fin (C.comap σ.toEmbedding).card) :
    G.scheme.cellMap (extendPerm σ).symm.toEmbedding
        ((G.relabel σ).scheme.faceCell Fin.castSuccEmb (G.relabel σ).comap_context
          (C.cellMap σ.toEmbedding y)) =
      G.scheme.faceCell Fin.castSuccEmb G.comap_context y := by
  refine (G.scheme.cellMap_faceCell_comap _ _ (G.relabel σ).comap_context _).trans ?_
  have h2 : (G.scheme.comap Fin.castSuccEmb).comap σ.symm.toEmbedding = C := by
    rw [G.comap_context, Scheme.comap_symm_comap]
  rw [G.scheme.faceCell_congr (castSuccEmb_trans_extendPerm_symm σ) _
      ((G.scheme.comap_comap _ _).symm.trans h2),
    ← G.scheme.cellMap_faceCell_comap Fin.castSuccEmb σ.symm.toEmbedding h2]
  exact congrArg (G.scheme.cellMap Fin.castSuccEmb)
    (C.faceCell_symm_cellMap_of_eq σ G.comap_context h2 y)

/-- **Recovery in the face formulation**: a carrier recovers `ρ` from `s` exactly when every lawful
section equal to `s` at the context cells satisfies `ρ` at the donor cells. -/
theorem recovers_iff {e : Fin n ↪ Fin J} (G : GrowthCarrier C P e) (s : Fin C.card → Label.{u})
    (ρ : Fin P.card → Label.{u} → Prop) :
    G.Recovers s ρ ↔ ∀ v : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful v →
      (∀ x, v (G.scheme.faceCell Fin.castSuccEmb G.comap_context x) = s x) →
      ∀ j, ρ j (v (G.scheme.faceCell (extendByLast e) G.comap_donor j)) := by
  constructor
  · intro h v hv hctx j
    exact h v hv (fun i x hix ↦ (congrArg v (congrArg _ (Fin.ext hix))).trans (hctx x)) _ j rfl
  · intro h v hv hctx i j hij
    have := h v hv (fun x ↦ hctx _ x rfl) j
    rwa [show G.scheme.faceCell (extendByLast e) G.comap_donor j =
      G.scheme.cellMap (extendByLast e) i from
        congrArg (G.scheme.cellMap (extendByLast e)) (Fin.ext hij.symm)] at this

/-- **Recovery is transported along a relabelling**: if the carrier for the relabelled context
recovers `ρ` from the section `s` read along the cell map of `σ`, the relabelled carrier recovers
`ρ` from `s`.  A lawful section of the relabelled carrier is read back along the bijection of the
cells; the context and donor cells correspond (`GrowthCarrier.relabel_contextCell`,
`GrowthCarrier.relabel_donorCell`). -/
theorem Recovers.relabel {s : Fin C.card → Label.{u}} {ρ : Fin P.card → Label.{u} → Prop}
    (h : G.Recovers (fun y ↦ s (C.cellMap σ.toEmbedding y)) ρ) : (G.relabel σ).Recovers s ρ := by
  rw [recovers_iff] at h ⊢
  intro v hv hctx j
  let f := (extendPerm σ).symm.toEmbedding
  let φ : Fin (G.relabel σ).scheme.card ≃ Fin G.scheme.card :=
    Equiv.ofBijective (G.scheme.cellMap f)
      ⟨(G.scheme.cellMap f).injective, G.scheme.surjective_cellMap_equiv _⟩
  let w : Fin G.scheme.card → Label.{u} := fun x ↦ v (φ.symm x)
  have hwv (i : Fin (G.relabel σ).scheme.card) : w (G.scheme.cellMap f i) = v i :=
    congrArg v (φ.symm_apply_apply i)
  have hfun : (fun i : Fin (G.scheme.comap f).card ↦ w (G.scheme.cellMap f i)) = v :=
    funext hwv
  have hw : G.scheme.rows.IsLawful w := by
    refine (G.scheme.isLawful_comap_perm_iff (extendPerm σ).symm w).mp ?_
    rw [hfun]
    exact hv
  have hd := h w hw (fun y ↦
    (congrArg w (relabel_contextCell σ G y)).symm.trans ((hwv _).trans (hctx _))) j
  have e1 : w (G.scheme.faceCell (extendByLast e'') G.comap_donor j) =
      v ((G.relabel σ).scheme.faceCell (extendByLast (e''.trans σ.toEmbedding))
        (G.relabel σ).comap_donor j) :=
    (congrArg w (relabel_donorCell σ G j)).symm.trans (hwv _)
  rwa [e1] at hd

end GrowthCarrier

/-! ### The surjective root -/

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Calibrated requests leave a point off the root**: the threshold is the grade of the cap, at
most the number `k` of points, and at least `n + 1`. -/
theorem GrowthRequests.Calibrated.lt {t' : StageType.{u} α k} {e : Fin n ↪ Fin k}
    {p : StageType.{u} α n} {hte : restrictFace e t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.Calibrated hte) : n < k := by
  have h1 := hQ.arity
  have h2 : Q.threshold ≤ k := t'.grade_le Q.cap
  omega

/-- A root on fewer points than the context is not onto. -/
theorem not_surjective_of_lt {e : Fin n ↪ Fin k} (h : n < k) : ¬ Function.Surjective e := by
  intro hs
  have := Fintype.card_le_of_surjective e hs
  simp only [Fintype.card_fin] at this
  omega

/-- **Under calibrated requests the root is not onto**: the contracts of the chain of record
(`StageType.HasAdmittedGrowthCarriers`, `StageType.HasRecognizingGrowthCarriers`,
`StageType.HasLadderGrowthCarriers`) ask for nothing at a surjective root. -/
theorem GrowthRequests.Calibrated.not_surjective {t' : StageType.{u} α k} {e : Fin n ↪ Fin k}
    {p : StageType.{u} α n} {hte : restrictFace e t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.Calibrated hte) : ¬ Function.Surjective e :=
  not_surjective_of_lt hQ.lt

/-- **The hollow reference calibration leaves two points off the root**: the marked cap has grade
above `j + 1` for the enlarged root on `j ≥ n` points, and at most `k`. -/
theorem HollowReferenceCalibration'.add_one_lt {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hC : HollowReferenceCalibration' t' h d) : n + 1 < k := by
  obtain ⟨j, g, h₀, c, r, -, ⟨-, -, hcg, -⟩, -⟩ := hC
  have hnj : n ≤ j := by simpa using Fintype.card_le_of_embedding h₀
  have := t'.grade_le c
  omega

/-- **Under the hollow reference calibration the root is not onto**. -/
theorem HollowReferenceCalibration'.not_surjective {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hC : HollowReferenceCalibration' t' h d) :
    ¬ Function.Surjective h :=
  not_surjective_of_lt (by have := hC.add_one_lt; omega)

/-- **Under the hollow reference calibration the donor's top grade is at most the context's**:
the donor's grades are at most `n + 1`, below the grade of the marked cap, which is labelled `⊤`. -/
theorem HollowReferenceCalibration'.topGrade_le {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hC : HollowReferenceCalibration' t' h d) :
    d.topGrade ≤ t'.topGrade := by
  obtain ⟨j, g, h₀, c, r, -, ⟨hcap, -, hcg, -⟩, -⟩ := hC
  have hnj : n ≤ j := by simpa using Fintype.card_le_of_embedding h₀
  have hct : t'.toCellScheme.grade c ≤ t'.topGrade := grade_le_topGrade hcap.2.1
  exact topGrade_le_iff.mpr fun i _ ↦ by have := d.grade_le i; omega

end StageType

end VaughtConjecture

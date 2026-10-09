/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthRelabelInputs
import VaughtConjecture.MainTheorem.GrowthStableLadder

/-!
# Ladder carriers under relabelling

Roadmap, Layer 3 ((R3) and (R4), the growth carrier at a calibrated context).

The body of the ladder contracts (`StageType.HasLadderGrowthCarriers`,
`StageType.HasLadderGrowthCarriersStable`) is a growth carrier with a cell of full scope at the
threshold, a field ladder, and every cell of full scope at the threshold a ladder controller
(`StageType.LadderCarrierBody`).  Along a permutation `σ` of the points of the context, the
relabelled carrier (`GrowthCarrier.relabel`) keeps all of it: its cells are those of the carrier
through the bijection of the cells, with their rows (`Scheme.rowAt_comap`) and, for the cells of
full scope, their graded indices (`Scheme.gradedIndex_comap_perm_eq_univ_iff`); the context and
donor cells correspond; and a ladder controller for the relabelled requests is a ladder controller
for the requests (`GrowthCarrier.IsLadderController.relabel`, by the invariance of admission on the
exact class).  So `StageType.LadderCarrierBody.relabel`.

The inputs of the stable ladder contract (the labels pair admitted, requests calibrated on the
class, the relative lift on the exact class) are kept under relabelling
(`StageType.GrowthRequests.ClassCalibrated.reindex`), and calibration on the class leaves a point
off the root (`StageType.GrowthRequests.ClassCalibrated.not_surjective`).  Hence the ladder contract
for requests calibrated on the class **at the seed position gives it at every context**
(`StageType.hasLadderGrowthCarriersStable_of_seed`), and, when the contract at the seed position
asks the donor's top grade to be at most the context's, at every context with that bound
(`StageType.ladderCarrierBody_of_seed_topGrade`).  Under the stable hypotheses alone that bound is
not implied: the labels pair admitted does not force the cap to be labelled `⊤`.

## References

Reindexing of stage types is [Kni26, Definition 3.1.2]; the growth construction is that of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace Scheme

variable {N m : ℕ} (S : Scheme.{u} N)

/-- **Rows along a restriction**: the row of a cell of the restriction at a cell is the row of
the corresponding cells. -/
theorem rowAt_comap (f : Fin m ↪ Fin N) (i j : Fin (S.comap f).card) :
    (S.comap f).rowAt i j = S.rowAt (S.cellMap f i) (S.cellMap f j) := by
  have hle := S.isLowerEmbedding_comap f
  unfold Scheme.rowAt
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((hle.le_iff j i).mpr h1) h2
  · exact absurd ((hle.le_iff j i).mp h2) h1
  · rfl

/-- **Cells of full scope along a permutation**: a cell of the reindexed scheme has graded index
`(univ, k)` exactly when its cell does. -/
theorem gradedIndex_comap_perm_eq_univ_iff (σ : Equiv.Perm (Fin N))
    (i : Fin (S.comap σ.toEmbedding).card) (k : ℕ) :
    (S.comap σ.toEmbedding).toCellScheme.gradedIndex i = (univ, k) ↔
      S.toCellScheme.gradedIndex (S.cellMap σ.toEmbedding i) = (univ, k) := by
  have hs : (S.comap σ.toEmbedding).toCellScheme.scope i = univ ↔
      S.toCellScheme.scope (S.cellMap σ.toEmbedding i) = univ := by
    rw [comap_scope]
    constructor
    · intro h
      ext y
      have : σ.symm y ∈ (S.toCellScheme.scope (S.cellMap σ.toEmbedding i)).preimage
          σ.toEmbedding σ.toEmbedding.injective.injOn := h ▸ mem_univ _
      simpa using this
    · intro h
      rw [h]
      exact preimage_univ _
  constructor
  · intro h
    exact Prod.ext (hs.mp (congrArg Prod.fst h)) (congrArg Prod.snd h :)
  · intro h
    exact Prod.ext (hs.mpr (congrArg Prod.fst h)) (congrArg Prod.snd h :)

end Scheme

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {P : Scheme.{u} (n + 1)} {t' : StageType.{u} α J}
  (σ : Equiv.Perm (Fin J)) {e'' : Fin n ↪ Fin J} (G : GrowthCarrier (t'.reindex σ).toScheme P e'')

/-- The **bijection of the cells** of the relabelled carrier onto the cells of the carrier. -/
noncomputable def relabelCell :
    Fin (G.relabel (C := t'.toScheme) σ).scheme.card ≃ Fin G.scheme.card :=
  Equiv.ofBijective (G.scheme.cellMap (extendPerm σ).symm.toEmbedding)
    ⟨(G.scheme.cellMap _).injective, G.scheme.surjective_cellMap_equiv _⟩

theorem relabelCell_apply (x : Fin (G.relabel (C := t'.toScheme) σ).scheme.card) :
    G.relabelCell σ x = G.scheme.cellMap (extendPerm σ).symm.toEmbedding x :=
  rfl

theorem rowAt_relabel (x y : Fin (G.relabel (C := t'.toScheme) σ).scheme.card) :
    (G.relabel (C := t'.toScheme) σ).scheme.rowAt x y =
      G.scheme.rowAt (G.relabelCell σ x) (G.relabelCell σ y) :=
  G.scheme.rowAt_comap _ x y

theorem gradedIndex_relabel_eq_univ_iff (x : Fin (G.relabel (C := t'.toScheme) σ).scheme.card)
    (k : ℕ) :
    (G.relabel (C := t'.toScheme) σ).scheme.toCellScheme.gradedIndex x = (univ, k) ↔
      G.scheme.toCellScheme.gradedIndex (G.relabelCell σ x) = (univ, k) :=
  G.scheme.gradedIndex_comap_perm_eq_univ_iff (extendPerm σ).symm x k

theorem relabelCell_contextCell (x : Fin t'.card) :
    G.relabelCell σ ((G.relabel (C := t'.toScheme) σ).contextCell x) =
      G.contextCell (t'.reindexCell σ x) :=
  relabel_contextCell' σ G x

theorem relabelCell_donorCell (j : Fin P.card) :
    G.relabelCell σ ((G.relabel (C := t'.toScheme) σ).donorCell j) = G.donorCell j :=
  relabel_donorCell (C := t'.toScheme) σ G j

/-- **Ladder controllers are transported along a relabelling**: a ladder controller of the carrier
for the relabelled requests is, through the bijection of the cells, a ladder controller of the
relabelled carrier for the requests. -/
theorem IsLadderController.relabel {Q : GrowthRequests t' P} {Mb : Type*} {H : ℕ}
    {r : Mb → ℕ → Fin G.scheme.card} {u : Fin G.scheme.card} {a : Mb} {F : ℕ → Label.{u}}
    (h : G.IsLadderController (Q.reindex σ) (H := H) r u a F) :
    (G.relabel (C := t'.toScheme) σ).IsLadderController Q (H := H)
      (fun a i ↦ (G.relabelCell σ).symm (r a i)) ((G.relabelCell σ).symm u) a F := by
  obtain ⟨hadm, htop, hrung, hval⟩ := h
  have hrow (x : Fin (G.relabel (C := t'.toScheme) σ).scheme.card) :
      (G.relabel (C := t'.toScheme) σ).scheme.rowAt ((G.relabelCell σ).symm u) x =
        G.scheme.rowAt u (G.relabelCell σ x) := by
    rw [rowAt_relabel, Equiv.apply_symm_apply]
  have hctx (x : Fin t'.card) :
      (G.relabel (C := t'.toScheme) σ).scheme.rowAt ((G.relabelCell σ).symm u)
        ((G.relabel (C := t'.toScheme) σ).contextCell x) =
          G.scheme.rowAt u (G.contextCell (t'.reindexCell σ x)) := by
    rw [hrow, relabelCell_contextCell]
  refine ⟨?_, ?_, fun i hi ↦ ?_, fun x hx hne ↦ ?_⟩
  · have e1 : (fun x ↦ (G.relabel (C := t'.toScheme) σ).scheme.rowAt ((G.relabelCell σ).symm u)
        ((G.relabel (C := t'.toScheme) σ).contextCell x)) =
          fun x ↦ G.scheme.rowAt u (G.contextCell (t'.reindexCell σ x)) := funext hctx
    have e2 : (fun j ↦ (G.relabel (C := t'.toScheme) σ).scheme.rowAt ((G.relabelCell σ).symm u)
        ((G.relabel (C := t'.toScheme) σ).donorCell j)) =
          fun j ↦ G.scheme.rowAt u (G.donorCell j) :=
      funext fun j ↦ by rw [hrow, relabelCell_donorCell]
    rw [e1, e2]
    refine (GrowthRequests.admitsOnClass_reindex_iff σ Q
      (fun x ↦ G.scheme.rowAt u (G.contextCell (t'.reindexCell σ x))) _).mp ?_
    simpa only [reindexCell_cellMap] using hadm
  · rw [hctx, hrow, Equiv.apply_symm_apply]
    exact htop
  · rw [hrow, Equiv.apply_symm_apply]
    exact hrung i hi
  · rw [hctx] at hne ⊢
    exact hval _ ((reindexCell_mem_below_iff t' σ x Q.cap).mpr hx) hne

end GrowthCarrier

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The **body of the ladder contracts** at `t'`, `e`, `d` and `Q`: a growth carrier with the
schemes of `t'` and `d` as literal faces, a cell of full scope at the threshold, a field ladder of
height `H ≥ 1`, and every cell of full scope at the threshold a ladder controller. -/
def LadderCarrierBody (t' : StageType.{u} α k) (e : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1))
    (Q : GrowthRequests t' d.toScheme) : Prop :=
  ∃ G : GrowthCarrier t'.toScheme d.toScheme e,
    (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
    ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
      (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
      (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
      (∀ a, ∀ i < H, 0 < i →
        G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
      ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
        ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F

/-- **The body of the ladder contracts is transported along a relabelling**: a ladder carrier at
`t'.reindex σ` for the relabelled requests gives, relabelled back, a ladder carrier at `t'` for the
requests. -/
theorem LadderCarrierBody.relabel {t' : StageType.{u} α k} (σ : Equiv.Perm (Fin k))
    {e'' : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {Q : GrowthRequests t' d.toScheme}
    (h : LadderCarrierBody (t'.reindex σ) e'' d (Q.reindex σ)) :
    LadderCarrierBody t' (e''.trans σ.toEmbedding) d Q := by
  obtain ⟨G, ⟨w, hw⟩, Mb, H, r, hH, hr, hrd, hrp, hctrl⟩ := h
  rw [GrowthRequests.threshold_reindex] at hw hctrl
  refine ⟨G.relabel (C := t'.toScheme) σ, ⟨(G.relabelCell σ).symm w, ?_⟩, Mb, H,
    fun a i ↦ (G.relabelCell σ).symm (r a i), hH, fun a i hi ↦ ?_, fun a i hi ↦ ?_,
    fun a i hi hi0 ↦ ?_, fun u hu ↦ ?_⟩
  · rw [GrowthCarrier.gradedIndex_relabel_eq_univ_iff, Equiv.apply_symm_apply]
    exact hw
  · rw [GrowthCarrier.gradedIndex_relabel_eq_univ_iff, Equiv.apply_symm_apply]
    exact hr a i hi
  · rw [GrowthCarrier.rowAt_relabel, Equiv.apply_symm_apply]
    exact hrd a i hi
  · rw [GrowthCarrier.rowAt_relabel, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hrp a i hi hi0
  · obtain ⟨a, F, hc⟩ := hctrl _ ((G.gradedIndex_relabel_eq_univ_iff σ u _).mp hu)
    refine ⟨a, F, ?_⟩
    have := hc.relabel σ G
    rwa [Equiv.symm_apply_apply] at this

namespace GrowthRequests

variable {t' : StageType.{u} α k} {d : StageType.{u} α (n + 1)}

/-- **Requests calibrated on the class leave a point off the root**: the threshold is at least
`n + 1` and at most `k`. -/
theorem ClassCalibrated.not_surjective {e : Fin n ↪ Fin k} {p : StageType.{u} α n}
    {hte : restrictFace e t' = some p} {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.ClassCalibrated hte) : ¬ Function.Surjective e :=
  not_surjective_of_lt (by have h1 := hQ.arity; have h2 := t'.grade_le Q.cap
                           unfold threshold at h1; omega)

variable (σ : Equiv.Perm (Fin k)) {e'' : Fin n ↪ Fin k} {p : StageType.{u} α n}
  (hte'' : restrictFace e'' (t'.reindex σ) = some p)
  (hte : restrictFace (e''.trans σ.toEmbedding) t' = some p)

/-- **Calibration on the class is kept under relabelling.** -/
theorem ClassCalibrated.reindex {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte) :
    (Q.reindex σ).ClassCalibrated hte'' where
  cover := hQ.cover
  scope_cap := by
    change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding
      (t'.reindexCell σ Q.cap))).preimage σ.toEmbedding σ.toEmbedding.injective.injOn = univ
    rw [cellMap_reindexCell, hQ.scope_cap]
    exact preimage_univ _
  label_cap := by
    change (t'.reindex σ).label (t'.reindexCell σ Q.cap) ≠ ⊥
    rw [label_reindexCell]
    exact hQ.label_cap
  ref j hj := by
    obtain ⟨h1, h2, h3⟩ := hQ.ref j hj
    refine ⟨?_, ?_, ?_⟩
    · change (t'.reindex σ).toCellScheme.grade (t'.reindexCell σ (Q.ref j)) ≤ _
      rw [grade_reindexCell, threshold_reindex]
      exact h1
    · rw [threshold_reindex]
      exact h2
    · change (t'.reindex σ).label (t'.reindexCell σ (Q.ref j)) ≠ ⊥
      rw [label_reindexCell]
      exact h3
  marker := by
    obtain ⟨h1, h2, h3⟩ := hQ.marker
    refine ⟨?_, ?_, ?_⟩
    · change (t'.reindex σ).toCellScheme.grade (t'.reindexCell σ Q.marker) ≤ _
      rw [grade_reindexCell, threshold_reindex]
      exact h1
    · rw [threshold_reindex]
      exact h2
    · change (t'.reindex σ).label (t'.reindexCell σ Q.marker) ≠ ⊥
      rw [label_reindexCell]
      exact h3
  root i := by
    change t'.toCellScheme.grade (t'.toScheme.cellMap σ.toEmbedding _) ≤ _
    rw [cellMap_faceCell_reindex t' σ hte'' hte i, threshold_reindex]
    exact hQ.root i
  arity := by
    rw [threshold_reindex]
    exact hQ.arity

end GrowthRequests

/-- **The stable inputs at a relabelled context.**  For calibrated-on-the-class requests at `t'`
along `e` with the labels pair admitted and the relative lift on the exact class, some relabelling
`σ` puts the root in the first coatom, a closed face, and the relabelled requests at
`t'.reindex σ` have the same three properties, with the same donor's top-grade comparison; and a
ladder carrier there gives one at `t'`. -/
theorem ladderCarrierBody_of_reindex {α : Ordinal.{u}} {n j : ℕ}
    {t' : StageType.{u} α (j + 1)} {e : Fin n ↪ Fin (j + 1)} {p : StageType.{u} α n}
    (hte : restrictFace e t' = some p) {d : StageType.{u} α (n + 1)}
    (hdp : restrictFace Fin.castSuccEmb d = some p) {Q : GrowthRequests t' d.toScheme}
    (hlab : ∀ i, Q.CorrectAt t'.label i (d.label i)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hseed : ∀ (σ : Equiv.Perm (Fin (j + 1))) (g : Fin n ↪ Fin j) (p' : StageType.{u} α j),
      restrictFace Fin.castSuccEmb (t'.reindex σ) = some p' →
      ∀ hte'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some p,
      (∀ i, (Q.reindex σ).CorrectAt (t'.reindex σ).label i (d.label i)) →
      (Q.reindex σ).ClassCalibrated hte'' → (Q.reindex σ).HasRelativeLiftOnClass hte'' hdp →
      LadderCarrierBody (t'.reindex σ) (g.trans Fin.castSuccEmb) d (Q.reindex σ)) :
    LadderCarrierBody t' e d Q := by
  obtain ⟨σ, g, p', rfl, hp'⟩ := Realization.exists_perm_root_eq hte hQ.not_surjective
  have hte'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some p := by
    rw [restrictFace_reindex]
    exact hte
  exact (hseed σ g p' hp' hte''
    (fun i ↦ (GrowthRequests.correctAt_reindex_iff σ Q t'.label i _).mpr (hlab i))
    (hQ.reindex σ hte'' hte) (hrel.reindex σ hte'' hte hdp)).relabel σ

/-- **The stable ladder contract from the seed position** (asked there without a top-grade bound):
ladder carriers for requests calibrated on the class at every context on `m + 1` points with a
closed first coatom and the root inside it give `StageType.HasLadderGrowthCarriersStable`. -/
theorem hasLadderGrowthCarriersStable_of_seed
    (h : ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
      (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
      restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
        (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
        (hd : d ∈ p.cofaces), 0 < n → ∀ Q : GrowthRequests t' d.toScheme,
          (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
          Q.HasRelativeLiftOnClass hte hd.2 → LadderCarrierBody t' (g.trans Fin.castSuccEmb) d Q) :
    HasLadderGrowthCarriersStable.{u} := by
  intro α n k t' e hα ht' p hte d hd hn Q hlab hQ hrel
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range e := by
      by_contra! hall
      exact hQ.not_surjective hall
    exact ⟨k - 1, by have := x.2; omega⟩
  exact ladderCarrierBody_of_reindex hte hd.2 hlab hQ hrel
    fun σ g p' hp' hte'' hlab'' hQ'' hrel'' ↦
      h (t'.reindex σ) g p' hα (ht'.reindex σ) hp' p hte'' d hd hn _ hlab'' hQ'' hrel''

/-- **The stable ladder contract from the seed position with the top-grade bound**: ladder
carriers for requests calibrated on the class at the seed position, asked only for donors of top
grade at most the context's, give the body at every context for such donors.  The bound is kept
under relabelling (`StageType.topGrade_reindex`). -/
theorem ladderCarrierBody_of_seed_topGrade
    (h : ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
      (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
      restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
        (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
        (hd : d ∈ p.cofaces), d.topGrade ≤ t'.topGrade → 0 < n →
        ∀ Q : GrowthRequests t' d.toScheme,
          (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
          Q.HasRelativeLiftOnClass hte hd.2 → LadderCarrierBody t' (g.trans Fin.castSuccEmb) d Q)
    {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k) (e : Fin n ↪ Fin k)
    (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal) (p : StageType.{u} α n)
    (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces)
    (hdK : d.topGrade ≤ t'.topGrade) (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hlab : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) : LadderCarrierBody t' e d Q := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range e := by
      by_contra! hall
      exact hQ.not_surjective hall
    exact ⟨k - 1, by have := x.2; omega⟩
  exact ladderCarrierBody_of_reindex hte hd.2 hlab hQ hrel
    fun σ g p' hp' hte'' hlab'' hQ'' hrel'' ↦
      h (t'.reindex σ) g p' hα (ht'.reindex σ) hp' p hte'' d hd
        (by rw [topGrade_reindex]; exact hdK) hn _ hlab'' hQ'' hrel''

end StageType

end VaughtConjecture

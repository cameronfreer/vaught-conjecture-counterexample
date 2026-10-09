/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedMixedLift
import VaughtConjecture.Extension.LadderLift
import VaughtConjecture.Extension.SourcePrefix

/-!
# The lift from a face of the attachment into a mixed face at the grade one

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces of the replicated carrier).

Let `V` be a face inside the context face or the donor face and `U ⊇ V` a mixed face.  Below
`(V, 1)` the replicated scheme has only cells of the attachment; below `(U, 1)` it has the cells
of the attachment inside `U` and the copies of the ladder at the mixed faces inside `U`.

* **Lifts through a larger pair** (`CellScheme.Rows.cappedLift_of_extend`): a capped lift from
  `X` to `Z` and a capped lift from `Y` to `Z` at the same grade give a capped lift from `X` to
  `Y`: extend the ambient below `Y` to `Z` (a capped lift at the cap `⊥` extends every lawful
  section, `CellScheme.Rows.CappedLift.exists_extend`), lift into `Z`, and restrict.
* **Sections of the tower** (`Seed.isLawfulBelow_castAdd_replicated`): a section of the replicated
  scheme lawful below a pair, read on the cells of the tower, is lawful below that pair.
* **Lifts from the tower** (`Seed.cappedLift_replicated_of_tower`): from a pair inside the context
  face or the donor face, a capped lift of the tower is one of the replicated scheme: the lift of
  the tower, read through the originals, is lawful (the mirroring is saturated), and the ambient
  carries at every cell the label of its original.
* **The padded base in the tower** (`Seed.cappedLift_attachTower_one`): the tower lifts capped from
  `(V, 1)` into the full face of grade one when the attachment does (the padded grade-one base is
  a source prefix of the tower at `(univ, 1)`, and the rank members glue).

* **Capping a class of cells of the top grade** (`CellScheme.Rows.isLawfulBelow_capOn`): a section
  lawful below a pair, capped at a self-visible label on a class of cells of the top grade closed
  upward and under availability, is lawful.
* **The root and the donor face** (`Seed.inter_map_eq_root`, `Seed.card_root`,
  `Seed.root_mem_faces`, `Seed.donor_mem_faces`): the intersection of the context face and the
  donor face is the image of the root, a face of the amalgam when the root is a face of the
  context; the donor face is a face of the amalgam when the donor is.
* **Through the full face** (`Seed.cappedLift_attached_mixed_of_univ`): a lift from `(V, k)` into
  `(univ, k)` gives one into every mixed face `U ⊇ V` with `k ≤ |U|` (`Seed.cappedLift_mixed_univ`).

**The lift** (`Seed.cappedLift_attached_mixed_one`): the replicated scheme lifts capped from
`(V, 1)` to `(U, 1)` when the attachment lifts capped from `(V, 1)` into `(univ, 1)`: through the
full face of grade one, with the extension from `(U, 1)` given by the lift from a mixed face into
the full face at the grade one (`Seed.cappedLift_mixed_univ_one`).  The attachment lifts so
(`Seed.cappedLift_attachment_univ_one`) when the donor face and the root (its intersection with
the context face) are faces of the amalgam and the root is nonempty, at every grade
`k ≤ |V|` (`Seed.cappedLift_attachment_univ`): the lifts of the amalgam within the context face and
the donor face glue along the root
(`Seed.cappedLift_attached_mixed_one_of_faces`).

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {X Y Z : Finset α × ℕ}

/-- **Extension from a capped lift**: a capped lift from `Y` to `Z` extends every labelling lawful
below `Y` to one lawful below `Z` (the lift at the cap `⊥` with the ambient `⊥`). -/
theorem CappedLift.exists_extend (h : Y ≤ Z) (hl : R.CappedLift h) {v : ι → Label.{u}}
    (hv : R.IsLawfulBelow Y fun e ↦ v e) :
    ∃ v' : ι → Label.{u}, R.IsLawfulBelow Z (fun e ↦ v' e) ∧ ∀ e ∈ D.below Y, v' e = v e := by
  obtain ⟨q, hq, -, hqp⟩ := (cappedLift_iff_forall_exists h).mp hl ⊥ (isSelfVisible_bot _)
    (fun e ↦ v e) (fun _ ↦ ⊥) hv (isLawfulBelow_const_bot _)
    fun _ ↦ by rw [min_bot_right, min_bot_right]
  refine ⟨extendBot Z q, isLawfulBelow_extendBot.mpr hq, fun e he ↦ ?_⟩
  rw [extendBot_of_mem q (D.below_mono h he)]
  exact hqp ⟨e, he⟩

/-- **Lifts through a larger pair at the same grade**: capped lifts from `X` to `Z` and from `Y` to
`Z`, for `X ≤ Y ≤ Z` with `Y` and `Z` of the same grade, give a capped lift from `X` to `Y`. -/
theorem cappedLift_of_extend (hXY : X ≤ Y) (hYZ : Y ≤ Z) (hg : Y.2 = Z.2)
    (hl : R.CappedLift (hXY.trans hYZ)) (hext : R.CappedLift hYZ) : R.CappedLift hXY := by
  refine cappedLift_of_forall_full hXY fun c hc w v hw hv hwv ↦ ?_
  obtain ⟨v', hv', hvv⟩ := hext.exists_extend hYZ hv
  obtain ⟨q, hq, hqc, hqw⟩ := (cappedLift_iff_forall_exists (hXY.trans hYZ)).mp hl c (hg ▸ hc)
    (fun e ↦ w e) (fun e ↦ v' e) hw hv' fun d ↦ by
      change min (v' d) c = min (w d) c
      rw [hvv d (D.below_mono hXY d.2)]
      exact hwv d d.2
  refine ⟨extendBot Z q, (isLawfulBelow_extendBot.mpr hq).mono hYZ, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · rw [extendBot_of_mem q (D.below_mono hYZ he), hqc ⟨e, D.below_mono hYZ he⟩]
    exact congrArg (min · c) (hvv e he)
  · rw [extendBot_of_mem q (D.below_mono (hXY.trans hYZ) he)]
    exact hqw ⟨e, he⟩

/-- **Capping a class of cells of the top grade**: let `w` be lawful below `X`, `c` self-visible at
the grade `X.2`, and `K` a class of cells of the grade `X.2`, determined by the graded index, closed
upward below `X`, and containing every cell of its grade whose scope lies inside the scope of one of
its cells.  Then `w` capped at `c` on `K` is lawful below `X`: a cell of `K` reads the row of `w`
capped at `c`, a cell outside `K` reads no cell of `K`, and availability inside `K` is capped
alike. -/
theorem isLawfulBelow_capOn {w : ι → Label.{u}} (hw : R.IsLawfulBelow X fun d ↦ w d)
    {c : Label.{u}} (hc : IsSelfVisible X.2 c) (K : ι → Prop) [DecidablePred K]
    (hKg : ∀ a, K a → D.grade a = X.2)
    (hup : ∀ d s, K d → d ∈ D.below (D.gradedIndex s) → s ∈ D.below X → K s)
    (hav : ∀ s t, D.scope s ⊆ D.scope t → D.grade s = D.grade t → t ∈ D.below X → K t → K s)
    (hgi : ∀ u t, D.gradedIndex u = D.gradedIndex t → K t → K u) :
    R.IsLawfulBelow X fun d ↦ if K d then min (w d) c else w d := by
  obtain ⟨ho, hl, ha⟩ := isLawfulBelow_iff_forall.mp hw
  refine (isLawfulBelow_iff_forall (w := fun d ↦ if K d then min (w d) c else w d)).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · split_ifs with h
    · exact (ho d hd).min (hKg d h ▸ hc)
    · exact ho d hd
  · by_cases hKs : K s
    · have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if K d.1 then min (w d.1) c else w d.1) (if K s then min (w s) c else w s)) =
          fun d ↦ min (min (w d.1) (w s)) c := by
        funext d
        rw [ite_eq_left hKs]
        split_ifs
        · rw [min_min_min_comm, min_self]
        · rw [← min_assoc]
      rw [he]
      exact (hl s hs).min_const (fun d ↦ d.2.2.trans hs.2) hc
    · have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if K d.1 then min (w d.1) c else w d.1) (if K s then min (w s) c else w s)) =
          fun d ↦ min (w d.1) (w s) := by
        funext d
        rw [ite_eq_right hKs, ite_eq_right fun h ↦ hKs (hup d.1 s h d.2 hs)]
      rw [he]
      exact hl s hs
  · obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
    refine ⟨u, hu, ?_⟩
    by_cases hKt : K t
    · rw [ite_eq_left (hav s t hst hg ht hKt), ite_eq_left (hgi u t hu hKt)]
      exact min_le_min_right c hle
    · have hKu : ¬ K u := fun h ↦ hKt (hgi t u hu.symm h)
      rw [ite_eq_right hKu]
      split_ifs
      · exact (min_le_left _ _).trans hle
      · exact hle

end CellScheme.Rows

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U V : Finset (Fin (m + 2))}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

theorem gradedIndex_replicated_castAdd (x : Fin (𝕋).card) :
    (𝔼).toCellScheme.gradedIndex (Fin.castAdd _ x) = (𝕋).toCellScheme.gradedIndex x :=
  Scheme.gradedIndex_mirror_castAdd (hmix := I.not_subset_scope_tower g H Γ A B') x

/-- **Sections of the tower from sections of the replicated scheme**: a labelling of the replicated
scheme lawful below a pair, read on the cells of the tower, is lawful below that pair.  The cells
of the tower read the cells of the tower below them as in the replicated scheme, and a cell of the
replicated scheme of the graded index of a cell of the tower is a cell of the tower: a copy has a
mixed scope, which is neither the ground set nor inside the scope of a cell of proper scope. -/
theorem isLawfulBelow_castAdd_replicated {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (𝔼).card → Label.{u}} (hw : (𝔼).rows.IsLawfulBelow Y fun d ↦ w d) :
    (𝕋).rows.IsLawfulBelow Y fun x ↦ w (Fin.castAdd _ x) := by
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hmem (x : Fin (𝕋).card) (Z : Finset (Fin (m + 2)) × ℕ) :
      (Fin.castAdd _ x : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below Z ↔
        x ∈ (𝕋).toCellScheme.below Z := by
    rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_replicated_castAdd]
  have hgr (x : Fin (𝕋).card) :
      (𝔼).toCellScheme.grade (Fin.castAdd _ x) = (𝕋).toCellScheme.grade x :=
    congrArg Prod.snd (gradedIndex_replicated_castAdd x)
  have hsc (x : Fin (𝕋).card) :
      (𝔼).toCellScheme.scope (Fin.castAdd _ x) = (𝕋).toCellScheme.scope x :=
    congrArg Prod.fst (gradedIndex_replicated_castAdd x)
  refine (CellScheme.Rows.isLawfulBelow_iff_forall
    (w := fun x ↦ w (Fin.castAdd _ x))).mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_,
    fun s t ht hst hg ↦ ?_⟩
  · rw [← hgr]
    exact ho _ ((hmem d Y).mpr hd)
  · have hφ (d : (𝕋).toCellScheme.below ((𝕋).toCellScheme.gradedIndex s)) :
        (Fin.castAdd _ d.1 : Fin (𝔼).card) ∈
          (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ s)) := by
      rw [gradedIndex_replicated_castAdd]
      exact (hmem _ _).mpr d.2
    have h := (hl _ ((hmem s Y).mpr hs)).reindex
      fun d : (𝕋).toCellScheme.below ((𝕋).toCellScheme.gradedIndex s) ↦
        (⟨Fin.castAdd _ d.1, hφ d⟩ :
          (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ s)))
    convert h using 1
    · funext d
      exact (hgr d.1).symm
    · funext d
      change (𝕋).rows.row s d = (𝔼).rows.row (Fin.castAdd _ s) ⟨Fin.castAdd _ d.1, hφ d⟩
      rw [← Scheme.rowAt_of_mem d.2, ← Scheme.rowAt_of_mem (hφ d), Scheme.rowAt_mirror_castAdd]
    · rfl
  · obtain ⟨u', hu', hle⟩ := ha (Fin.castAdd _ s) (Fin.castAdd _ t) ((hmem t Y).mpr ht)
      (by rw [hsc, hsc]; exact hst) (by rw [hgr, hgr]; exact hg)
    induction u' using Fin.addCases with
    | left x =>
      refine ⟨x, ?_, hle⟩
      rw [← gradedIndex_replicated_castAdd, hu', gradedIndex_replicated_castAdd]
    | right j =>
      exfalso
      have hj : (𝔼).toCellScheme.scope (Fin.natAdd _ j) = (𝕋).toCellScheme.scope t :=
        (congrArg Prod.fst hu').trans (hsc t)
      have hm := scope_replicated_natAdd (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
        (B' := B') j
      by_cases htu : (𝕋).toCellScheme.scope t = univ
      · exact ((I.mem_mixedFaces g).mp hm).2.1 (hj.trans htu)
      · exact I.not_subset_scope_tower g H Γ A B' t htu _ hm (le_of_eq hj)

/-- **Lifts from the tower into a full face**: from a pair whose face lies in the context face or
the donor face into a pair of full scope, a capped lift of the tower is a capped lift of the
replicated scheme.  The ambient read on the tower
is lawful (`Seed.isLawfulBelow_castAdd_replicated`), and so is the prescription (below the pair
the cells are cells of the attachment); the lift of the tower read through the originals is lawful
(the mirroring is saturated), is the prescription below the pair, and keeps the observation of the
ambient, which carries at every cell the label of its original. -/
theorem cappedLift_replicated_of_tower {X Y : Finset (Fin (m + 2)) × ℕ} (h : X ≤ Y)
    (hY : Y.1 = univ)
    (hX : X.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hT : (𝕋).rows.CappedLift h) : (𝔼).rows.CappedLift h := by
  refine CellScheme.Rows.cappedLift_of_forall_full h fun c hc w v hw hv hwv ↦ ?_
  have hmix := I.not_subset_scope_tower g H Γ A B'
  obtain ⟨q, hq, hqc, hqw⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists h).mp hT c hc
    (fun x ↦ w (Fin.castAdd _ x.1)) (fun x ↦ v (Fin.castAdd _ x.1))
    (isLawfulBelow_castAdd_replicated hw) (isLawfulBelow_castAdd_replicated hv) fun d ↦
      hwv _ (by rw [CellScheme.mem_below, gradedIndex_replicated_castAdd]; exact d.2)
  set r : Fin (𝕋).card → Label.{u} := CellScheme.Rows.extendBot Y q with hr
  have hrl : (𝕋).rows.IsLawfulBelow Y fun x ↦ r x :=
    CellScheme.Rows.isLawfulBelow_extendBot.mpr hq
  have horig (t : Fin (𝔼).card) (ht : t ∈ (𝔼).toCellScheme.below Y) :
      (𝕋).mirrorOrig (I.mixedFaces g) t ∈ (𝕋).toCellScheme.below Y :=
    ⟨hY ▸ subset_univ _, ht.2⟩
  refine ⟨fun t ↦ r ((𝕋).mirrorOrig (I.mixedFaces g) t),
    (Scheme.mirrorData hmix).isLawfulBelow_comp hrl horig (Scheme.saturated_mirrorData _ Y),
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · -- the observation of the ambient
    have hcY : (Fin.castAdd _ ((𝕋).mirrorOrig (I.mixedFaces g) t) : Fin (𝔼).card) ∈
        (𝔼).toCellScheme.below Y := by
      rw [CellScheme.mem_below, gradedIndex_replicated_castAdd]; exact horig t ht
    have hvt : v t = v (Fin.castAdd _ ((𝕋).mirrorOrig (I.mixedFaces g) t)) :=
      Scheme.eq_of_mirrorOrig_eq hv (Scheme.mirrorOrig_castAdd _ _ _).symm
        (((Scheme.mirrorData hmix).scope_subset t).trans
          (le_of_eq (congrArg Prod.fst (gradedIndex_replicated_castAdd _)).symm)) hcY
    beta_reduce
    rw [hvt, hr, CellScheme.Rows.extendBot_of_mem q (horig t ht)]
    exact hqc ⟨_, horig t ht⟩
  · -- the prescription below `X`
    obtain ⟨e, rfl⟩ := mem_range_attachEmb t
      (hX.imp (fun hc ↦ ht.1.trans hc) fun hc ↦ ht.1.trans hc)
    have he : (I.attachmentBase g).baseCellEmb m e ∈ (𝕋).toCellScheme.below X := by
      rw [CellScheme.mem_below, ← gradedIndex_replicated_castAdd]
      exact ht
    beta_reduce
    rw [mirrorOrig_attachEmb, hr, CellScheme.Rows.extendBot_of_mem q (CellScheme.below_mono _ h he)]
    exact hqw ⟨_, he⟩

/-- **The padded base in the tower at the grade one**: for a pair `X ≤ (univ, 1)` not above
`(univ, 1)`, the ladder tower over the attachment lifts capped from `X` to `(univ, 1)` when the
attachment does.  Below `(univ, 1)` the tower is the padded grade-one base (its layers have grades
at least `2`), which lifts by gluing of rank members (`Scheme.cappedLift_ladderBase_rankMember`). -/
theorem cappedLift_attachTower_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {X : Finset (Fin (m + 2)) × ℕ} (hXU : X ≤ ((univ : Finset (Fin (m + 2))), 1))
    (hX : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ X)
    (hold : (I.attachmentBase g).S.rows.CappedLift hXU) : (𝕋).rows.CappedLift hXU := by
  have hpre : ((I.attachmentBase g).ladderBase H).toCellScheme.IsSourcePrefix (𝕋).toCellScheme
      ((I.attachmentBase g).towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m)
      ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨Scheme.isLowerEmbedding_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
        (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) m,
      fun t ↦ Scheme.scope_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
        (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) t m,
      fun d hd ↦ Scheme.mem_range_layerTowerEmb_of_grade (B := (I.attachmentBase g).towerBase H)
        (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) m d hd.2⟩
  rw [← hpre.cappedLift_iff hXU le_rfl]
  have hrows := Scheme.comap_rows_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k) m
  rw [show (𝕋).rows.comap hpre.isLowerEmbedding = ((I.attachmentBase g).ladderBase H).rows
    from hrows]
  exact Scheme.cappedLift_ladderBase_rankMember (I.attachmentBase g).wf hH hcard hXU hX hold

/-! ### The donor face and the root -/

/-- **The root**: the intersection of the context face and the donor face is the image of the
root. -/
theorem inter_map_eq_root :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
        univ.map (extendByLast (g.trans Fin.castSuccEmb)) =
      univ.map ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) := by
  ext x
  simp only [mem_inter, mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
    Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨⟨a, rfl⟩, ⟨y, hy⟩⟩
    induction y using Fin.lastCases with
    | last =>
      rw [extendByLast_last] at hy
      exact absurd hy (Fin.castSucc_lt_last a).ne'
    | cast i =>
      rw [extendByLast_castSucc, Function.Embedding.trans_apply, Fin.castSuccEmb_apply] at hy
      exact ⟨i, hy⟩
  · rintro ⟨i, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨Fin.castSucc i, ?_⟩⟩
    rw [extendByLast_castSucc, Function.Embedding.trans_apply, Fin.castSuccEmb_apply]

/-- The root has `n` points. -/
theorem card_root :
    #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))) = n := by
  rw [inter_map_eq_root, card_map, card_univ, Fintype.card_fin]

/-- **The root is a face of the amalgam** when it is a face of the context. -/
theorem root_mem_faces {p : StageType.{u} α n}
    (hte : StageType.restrictFace (g.trans Fin.castSuccEmb) I.left = some p) :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces := by
  rw [inter_map_eq_root]
  have h := (StageType.restrictFace_trans I.amalgam _ (g.trans Fin.castSuccEmb)
    I.restrictFace_left).symm.trans hte
  exact ((StageType.restrictFace_eq_some_iff _ _).mp h).1

/-- **The donor face is a face of the amalgam** when the amalgam has the donor as a face. -/
theorem donor_mem_faces {d : StageType.{u} α (n + 1)}
    (hd : StageType.restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d) :
    univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces :=
  ((StageType.restrictFace_eq_some_iff _ _).mp hd).1

/-- **The attachment lifts like the amalgam below its faces**: between graded faces `X ≤ Y` of the
amalgam with `Y` inside the context face or the donor face, the attachment lifts capped (below
`Y` it is the amalgam). -/
theorem cappedLift_attachment_of_subset {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hY : Y ∈ I.amalgam.toCellScheme.gradedFaces)
    (h : X ≤ Y)
    (hYc : Y.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      Y.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    (I.attachmentBase g).S.rows.CappedLift h := by
  have hpreA : (I.attachment g).toCellScheme.IsSourcePrefix I.amalgam.toCellScheme
      (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)) Y :=
    ⟨Scheme.isLowerEmbedding_lowerEmb _ _ (I.attachmentCells_lower g), fun _ ↦ rfl,
      fun c hc ↦ by
        have hcL : c ∈ I.attachmentCells g := (I.mem_attachmentCells g).mpr
          (hYc.imp (fun h' ↦ hc.1.trans h') fun h' ↦ hc.1.trans h')
        have h' := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hcL)
        exact h'⟩
  exact (hpreA.cappedLift_iff (R := I.amalgam.rows) h le_rfl).mpr (I.isBountiful hX hY h)

/-- **The attachment lifts into the full face** at a grade `k ≤ |V|` from a face `V` inside the
context face or the donor face, when the donor face and its intersection with the context face (the
root) are faces of the amalgam, the root nonempty: the cells below `(univ, k)` lie below the context
face or the donor face (at the grade `min k |D|`), those below both below the root (at the grade
`min k |root|`), and the lifts of the amalgam within the two faces glue
(`CellScheme.Rows.cappedLift_of_union`). -/
theorem cappedLift_attachment_univ
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hVF : V ∈ I.amalgam.toCellScheme.faces) {k : ℕ} (hk1 : 1 ≤ k) (hkV : k ≤ #V)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    (I.attachmentBase g).S.rows.CappedLift
      (X := (V, k)) (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨subset_univ _, le_rfl⟩ := by
  set C := univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) with hC
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hD
  have hCF : C ∈ I.amalgam.toCellScheme.faces :=
    ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hC1 : 1 ≤ #C := by rw [hC, card_map, card_univ, Fintype.card_fin]; omega
  have hD1 : 1 ≤ #D := by rw [hD, card_map, card_univ, Fintype.card_fin]; omega
  have hgc (d : Fin (I.attachmentBase g).S.card) :
      (I.attachmentBase g).S.toCellScheme.grade d ≤
        #((I.attachmentBase g).S.toCellScheme.scope d) :=
    (I.isWellFormed_attachment g).isWellFormed.grade_le_card d
  have hbelow (d : Fin (I.attachmentBase g).S.card) (Z : Finset (Fin (m + 2))) (i : ℕ)
      (hdZ : (I.attachmentBase g).S.toCellScheme.scope d ⊆ Z)
      (hdi : (I.attachmentBase g).S.toCellScheme.grade d ≤ i) :
      d ∈ (I.attachmentBase g).S.toCellScheme.below (Z, min i #Z) :=
    ⟨hdZ, le_min hdi ((hgc d).trans (card_le_card hdZ))⟩
  have hcover (d) (hd : d ∈ (I.attachmentBase g).S.toCellScheme.below
      ((univ : Finset (Fin (m + 2))), k)) :
      d ∈ (I.attachmentBase g).S.toCellScheme.below (C, min k #C) ∨
        d ∈ (I.attachmentBase g).S.toCellScheme.below (D, min k #D) :=
    (I.scope_attachment g d).imp (fun h ↦ hbelow d C k h hd.2) fun h ↦ hbelow d D k h hd.2
  have hinter (d) (h1 : d ∈ (I.attachmentBase g).S.toCellScheme.below (C, min k #C))
      (h2 : d ∈ (I.attachmentBase g).S.toCellScheme.below (D, min k #D)) :
      d ∈ (I.attachmentBase g).S.toCellScheme.below (C ∩ D, min k #(C ∩ D)) :=
    hbelow d _ k (subset_inter h1.1 h2.1) (h1.2.trans (min_le_left _ _))
  have hsub (X Y : Finset (Fin (m + 2))) (i j : ℕ) (hX : X ∈ I.amalgam.toCellScheme.faces)
      (hi : 1 ≤ i) (hiX : i ≤ #X) (hY : Y ∈ I.amalgam.toCellScheme.faces) (hjY : j ≤ #Y)
      (hXY : X ⊆ Y) (hij : i ≤ j) (hYc : Y = C ∨ Y = D) :
      (I.attachmentBase g).S.rows.CappedLift (X := (X, i)) (Y := (Y, j)) ⟨hXY, hij⟩ :=
    cappedLift_attachment_of_subset ⟨hX, by omega, hiX⟩ ⟨hY, by omega, hjY⟩ _
      (by rcases hYc with rfl | rfl; exacts [.inl subset_rfl, .inr subset_rfl])
  have hkC : min k #C = k := min_eq_left
    (hkV.trans (hV.elim (card_le_card) fun h ↦ (card_le_card h).trans (by
      have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
      rw [hD, hC, card_map, card_map, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin]
      omega)))
  have hr : 1 ≤ min k #(C ∩ D) := le_min hk1 hr1
  rcases hV with hV | hV
  · have h := CellScheme.Rows.cappedLift_of_union (O := (C ∩ D, min k #(C ∩ D)))
      (U := (C, min k #C)) (V := (D, min k #D)) (Y := ((univ : Finset (Fin (m + 2))), k))
      (⟨hV, hkC.symm.le⟩ : ((V, k) : Finset (Fin (m + 2)) × ℕ) ≤ (C, min k #C))
      ⟨inter_subset_left, min_le_min_left _ (card_le_card inter_subset_left)⟩
      ⟨inter_subset_right, min_le_min_left _ (card_le_card inter_subset_right)⟩
      ⟨subset_univ _, min_le_left _ _⟩ ⟨subset_univ _, min_le_left _ _⟩ hcover hinter
      (hsub V C k _ hVF hk1 hkV hCF (min_le_right _ _) hV hkC.symm.le (.inl rfl))
      (hsub _ D _ _ hrF hr (min_le_right _ _) hdF (min_le_right _ _) inter_subset_right
        (min_le_min_left _ (card_le_card inter_subset_right)) (.inr rfl))
    exact h
  · have hkD : min k #D = k := min_eq_left (hkV.trans (card_le_card hV))
    have h := CellScheme.Rows.cappedLift_of_union (O := (C ∩ D, min k #(C ∩ D)))
      (U := (D, min k #D)) (V := (C, min k #C)) (Y := ((univ : Finset (Fin (m + 2))), k))
      (⟨hV, hkD.symm.le⟩ : ((V, k) : Finset (Fin (m + 2)) × ℕ) ≤ (D, min k #D))
      ⟨inter_subset_right, min_le_min_left _ (card_le_card inter_subset_right)⟩
      ⟨inter_subset_left, min_le_min_left _ (card_le_card inter_subset_left)⟩
      ⟨subset_univ _, min_le_left _ _⟩ ⟨subset_univ _, min_le_left _ _⟩
      (fun d hd ↦ (hcover d hd).symm) (fun d h1 h2 ↦ hinter d h2 h1)
      (hsub V D k _ hVF hk1 hkV hdF (min_le_right _ _) hV hkD.symm.le (.inr rfl))
      (hsub _ C _ _ hrF hr (min_le_right _ _) hCF (min_le_right _ _) inter_subset_left
        (min_le_min_left _ (card_le_card inter_subset_left)) (.inl rfl))
    exact h

/-- **The attachment lifts into the full face at the grade one** (`Seed.cappedLift_attachment_univ`
at `k = 1`). -/
theorem cappedLift_attachment_univ_one
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hVF : V ∈ I.amalgam.toCellScheme.faces) (hV1 : 1 ≤ #V)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    (I.attachmentBase g).S.rows.CappedLift
      (X := (V, 1)) (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_attachment_univ hdF hrF hr1 hVF le_rfl hV1 hV

/-- **The lift from a face of the attachment into a mixed face at the grade one.**  For a face `V`
inside the context face or the donor face and a mixed face `U ⊇ V`, the replicated scheme lifts
capped from `(V, 1)` to `(U, 1)` when the attachment lifts capped from `(V, 1)` into the full face
of grade one: the replicated scheme then lifts from `(V, 1)` to `(univ, 1)`
(`Seed.cappedLift_attachTower_one`, `Seed.cappedLift_replicated_of_tower`), and from `(U, 1)` to
`(univ, 1)` (`Seed.cappedLift_mixed_univ_one`), which extends every section lawful below `(U, 1)`
(`CellScheme.Rows.cappedLift_of_extend`). -/
theorem cappedLift_attached_mixed_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hU : U ∈ I.mixedFaces g) (hVU : V ⊆ U)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hold : (I.attachmentBase g).S.rows.CappedLift
      (X := (V, 1)) (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_univ _, le_rfl⟩) :
    (𝔼).rows.CappedLift (X := (V, 1)) (Y := (U, 1)) ⟨hVU, le_rfl⟩ := by
  have hVu : ¬ ((univ : Finset (Fin (m + 2))), 1) ≤ ((V, 1) : Finset (Fin (m + 2)) × ℕ) :=
    fun hle ↦ hV.elim
      (fun h ↦ map_castSuccEmb_ne_univ (univ_subset_iff.mp (hle.1.trans h)))
      fun h ↦ map_extendByLast_ne_univ g (univ_subset_iff.mp (hle.1.trans h))
  have hT := cappedLift_attachTower_one (Γ := Γ) (A := A) (B' := B') hH hcard
    (⟨subset_univ _, le_rfl⟩ : ((V, 1) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, 1)) hVu hold
  exact CellScheme.Rows.cappedLift_of_extend (X := (V, 1)) (Y := (U, 1))
    (Z := ((univ : Finset (Fin (m + 2))), 1))
    ⟨hVU, le_rfl⟩ ⟨subset_univ _, le_rfl⟩ rfl
    (cappedLift_replicated_of_tower _ rfl hV hT) (cappedLift_mixed_univ_one hH hcard hΓ hA hU)

/-- **Lifts into a mixed face through the full face**: for a mixed face `U ⊇ V` and a grade
`1 ≤ k ≤ m + 1` with `k ≤ |U|`, a capped lift of the replicated scheme from `(V, k)` into
`(univ, k)` gives one into `(U, k)`, since the lift from `(U, k)` into `(univ, k)`
(`Seed.cappedLift_mixed_univ`) extends every section lawful below `(U, k)`. -/
theorem cappedLift_attached_mixed_of_univ (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hA0 : ∀ k, A k fun _ ↦ ⊥) (hU : U ∈ I.mixedFaces g) (hVU : V ⊆ U) {k : ℕ} (hk1 : 1 ≤ k)
    (hkm : k ≤ m + 1) (hkU : k ≤ #U)
    (hl : (𝔼).rows.CappedLift (X := (V, k)) (Y := ((univ : Finset (Fin (m + 2))), k))
      ⟨subset_univ _, le_rfl⟩) :
    (𝔼).rows.CappedLift (X := (V, k)) (Y := (U, k)) ⟨hVU, le_rfl⟩ :=
  CellScheme.Rows.cappedLift_of_extend (X := (V, k)) (Y := (U, k))
    (Z := ((univ : Finset (Fin (m + 2))), k)) ⟨hVU, le_rfl⟩ ⟨subset_univ _, le_rfl⟩ rfl hl
    (cappedLift_mixed_univ hH hcard hΓ0 hΓ hA hA0 hU hk1 hkm hkU)

/-- **The lift from a face of the attachment into a mixed face at the grade one**, when the donor
face and the root are faces of the amalgam, the root nonempty
(`Seed.cappedLift_attachment_univ_one`). -/
theorem cappedLift_attached_mixed_one_of_faces (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hU : U ∈ I.mixedFaces g) (hVF : V ∈ I.amalgam.toCellScheme.faces) (hV1 : 1 ≤ #V)
    (hVU : V ⊆ U)
    (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    (𝔼).rows.CappedLift (X := (V, 1)) (Y := (U, 1)) ⟨hVU, le_rfl⟩ :=
  cappedLift_attached_mixed_one hH hcard hΓ hA hU hVU hV
    (cappedLift_attachment_univ_one hdF hrF hr1 hVF hV1 hV)

end Seed

end VaughtConjecture

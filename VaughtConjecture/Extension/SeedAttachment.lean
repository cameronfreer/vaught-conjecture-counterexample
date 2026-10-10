/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.FaceGluing
import VaughtConjecture.Extension.LadderBase
import VaughtConjecture.Extension.LowerRestriction
import VaughtConjecture.Extension.Seed

/-!
# The attachment of a donor to a context, inside a seed

Roadmap, Layer 3 ((R3) and (R4), the base of the replicated carrier).

For a seed `I` and a root `g` of the context inside its first coatom, the **attachment**
(`Seed.attachment I g`) is the restriction of the amalgam to its cells whose scope lies in the
context face or in the donor face (the root followed by the new point): the cells of the context
and the new cells of the donor, with the plan of the amalgam.  Its mixed faces carry no cell; they
receive the copies of the cells of full scope in the replicated carrier.

* It is well formed, coded and consistent, and no cell has full scope
  (`Seed.isWellFormed_attachment`, `Seed.isCoded_attachment`, `Seed.isConsistent_attachment`,
  `Seed.noFullOne_attachment`).
* Its faces along the context and along the donor face are those of the amalgam, literally
  (`Seed.comap_left_attachment`, `Seed.comap_donor_attachment`).

## References

The amalgam is [Kni26, Definition 4.3.1].
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

open Classical in
/-- The cells of the amalgam whose scope lies in the context face or in the donor face. -/
noncomputable def attachmentCells : Finset (Fin I.amalgam.card) :=
  univ.filter fun c ↦
    I.amalgam.toCellScheme.scope c ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      I.amalgam.toCellScheme.scope c ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))

theorem mem_attachmentCells {c : Fin I.amalgam.card} :
    c ∈ I.attachmentCells g ↔
      I.amalgam.toCellScheme.scope c ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        I.amalgam.toCellScheme.scope c ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
  classical
  simp only [attachmentCells, mem_filter, mem_univ, true_and]

theorem attachmentCells_lower (c : Fin I.amalgam.card) (hc : c ∈ I.attachmentCells g)
    (d : Fin I.amalgam.card)
    (hd : I.amalgam.toCellScheme.gradedIndex d ≤ I.amalgam.toCellScheme.gradedIndex c) :
    d ∈ I.attachmentCells g := by
  rw [mem_attachmentCells] at hc ⊢
  exact hc.imp (fun h ↦ hd.1.trans h) fun h ↦ hd.1.trans h

/-- **The attachment**: the amalgam restricted to its cells whose scope lies in the context face
or in the donor face. -/
noncomputable abbrev attachment : Scheme.{u} (m + 2) :=
  I.amalgam.toScheme.restrictLower (I.attachmentCells g) (I.attachmentCells_lower g)

theorem isWellFormed_attachment : (I.attachment g).IsWellFormed :=
  Scheme.isWellFormed_restrictLower I.amalgam.isWellFormed

theorem isCoded_attachment : (I.attachment g).IsCoded :=
  Scheme.isCoded_restrictLower I.amalgam.isCoded

theorem isConsistent_attachment : (I.attachment g).rows.IsConsistent :=
  Scheme.isConsistent_restrictLower I.isConsistent

/-- **No cell of the attachment has full scope.** -/
theorem noFullOne_attachment : (I.attachment g).NoFullOne := fun _ h ↦
  I.scope_ne_univ _ (univ_subset_iff.mp h.1)

/-- The face of the attachment along a proper face whose visible cells are attachment cells is
that of the amalgam. -/
theorem comap_attachment {k : ℕ} (f : Fin k ↪ Fin (m + 2))
    (hf : ∀ c : Fin I.amalgam.card,
      (I.amalgam.toCellScheme.scope c : Set (Fin (m + 2))) ⊆ Set.range f →
        c ∈ I.attachmentCells g) :
    (I.attachment g).comap f = I.amalgam.toScheme.comap f :=
  (Scheme.comap_eq_of_strictMono f (S := I.attachment g) (T := I.amalgam.toScheme)
    (φ := I.amalgam.toScheme.lowerEmb (I.attachmentCells g))
    (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)).strictMono
    (Scheme.isLowerEmbedding_lowerEmb _ _ (I.attachmentCells_lower g)) (fun _ ↦ rfl) rfl rfl rfl
    fun z hz ↦ by
      have hzL := hf z hz
      have h := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hzL)
      exact h).symm

/-- **The context face of the attachment is that of the amalgam.** -/
theorem comap_left_attachment :
    (I.attachment g).comap Fin.castSuccEmb = I.amalgam.toScheme.comap Fin.castSuccEmb :=
  I.comap_attachment g _ fun c hc ↦ (I.mem_attachmentCells g).mpr (.inl fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hc (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))

/-- **The donor face of the attachment is that of the amalgam.** -/
theorem comap_donor_attachment :
    (I.attachment g).comap (extendByLast (g.trans Fin.castSuccEmb)) =
      I.amalgam.toScheme.comap (extendByLast (g.trans Fin.castSuccEmb)) :=
  I.comap_attachment g _ fun c hc ↦ (I.mem_attachmentCells g).mpr (.inr fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hc (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))

/-! ### The attachment as a stage type -/

/-- **The attachment as a stage type**: the labels of the amalgam on its cells. -/
noncomputable def attachmentType : StageType.{u} α (m + 2) where
  toScheme := I.attachment g
  label c := I.amalgam.label (I.amalgam.toScheme.lowerEmb (I.attachmentCells g) c)
  isWellFormed := I.isWellFormed_attachment g
  isCoded := I.isCoded_attachment g
  isLawful := Scheme.isLawful_restrictLower I.amalgam.isLawful
  atStage _ := I.amalgam.atStage _

/-- The faces of the attachment along a proper face whose visible cells are attachment cells are
those of the amalgam, labels included. -/
theorem restrictFace_attachmentType {k : ℕ} (f : Fin k ↪ Fin (m + 2))
    (hf : ∀ c : Fin I.amalgam.card,
      (I.amalgam.toCellScheme.scope c : Set (Fin (m + 2))) ⊆ Set.range f →
        c ∈ I.attachmentCells g) :
    restrictFace f (I.attachmentType g) = restrictFace f I.amalgam :=
  Eq.symm <| StageType.restrictFace_eq_of_strictMono f (s := I.attachmentType g) (t := I.amalgam)
    (φ := I.amalgam.toScheme.lowerEmb (I.attachmentCells g))
    (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)).strictMono
    (Scheme.isLowerEmbedding_lowerEmb _ _ (I.attachmentCells_lower g)) (fun _ ↦ rfl) rfl rfl rfl
    (fun _ ↦ rfl) fun z hz ↦ by
      have hzL := hf z hz
      have h := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hzL)
      exact h

/-- **The context face of the attachment is the first coatom type.** -/
theorem restrictFace_left_attachmentType :
    restrictFace Fin.castSuccEmb (I.attachmentType g) = some I.left :=
  (I.restrictFace_attachmentType g _ fun c hc ↦ (I.mem_attachmentCells g).mpr (.inl fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hc (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))).trans I.restrictFace_left

/-- **The donor face of the attachment is the donor.** -/
theorem restrictFace_donor_attachmentType {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (I.attachmentType g) = some d :=
  (I.restrictFace_attachmentType g _ fun c hc ↦ (I.mem_attachmentCells g).mpr (.inr fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hc (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))).trans hd

/-- **The attachment is covered by its context and donor faces.** -/
theorem attachment_cover (c : Fin (I.attachmentType g).card) :
    c ∈ (I.attachmentType g).toScheme.visibleCells Fin.castSuccEmb ∨
      c ∈ (I.attachmentType g).toScheme.visibleCells (extendByLast (g.trans Fin.castSuccEmb)) := by
  have hc := (I.mem_attachmentCells g).mp
    ((I.attachmentCells g).orderEmbOfFin_mem rfl c)
  rcases hc with h | h
  · left
    refine Scheme.mem_visibleCells.mpr fun x hx ↦ ?_
    obtain ⟨y, -, rfl⟩ := mem_map.mp (h (mem_coe.mp hx))
    exact ⟨y, rfl⟩
  · right
    refine Scheme.mem_visibleCells.mpr fun x hx ↦ ?_
    obtain ⟨y, -, rfl⟩ := mem_map.mp (h (mem_coe.mp hx))
    exact ⟨y, rfl⟩

end Seed

namespace Seed

open Finset Label CellScheme StageType

variable {m n : ℕ} {g : Fin n ↪ Fin m}

/-- The context face does not lie in the donor face: it contains the point `m`. -/
theorem not_map_castSuccEmb_subset_donor :
    ¬ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ⊆
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
  intro hsub
  obtain ⟨y, -, hy⟩ := mem_map.mp (hsub (mem_map_of_mem _ (mem_univ (Fin.last m))))
  induction y using Fin.lastCases with
  | last =>
    rw [extendByLast_last] at hy
    exact (Fin.castSucc_lt_last (Fin.last m)).ne' hy
  | cast i =>
    rw [extendByLast_castSucc, Function.Embedding.trans_apply, Fin.castSuccEmb_apply,
      Fin.castSuccEmb_apply] at hy
    exact (Fin.castSucc_lt_last (g i)).ne (Fin.castSucc_injective _ hy)

variable (g) in
/-- **For an onto root the donor face is the second coatom** (the points other than `m`). -/
theorem donorFace_eq_coatom_of_surjective (hg : Function.Surjective g) :
    univ.map (extendByLast (g.trans Fin.castSuccEmb)) = univ.erase (Fin.castSucc (Fin.last m)) := by
  rw [← Coatom.univ_map_right, Coatom.right, univ_map_extendByLast, univ_map_extendByLast,
    ← map_map, map_univ_of_surjective hg]

/-- The **context coatom**: the points other than the last. -/
abbrev ctxCoatom (m : ℕ) : Finset (Fin (m + 2)) := univ.erase (Fin.last (m + 1))

theorem ctxCoatom_le (j : ℕ) :
    ((ctxCoatom m, j) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), j) :=
  ⟨erase_subset _ _, le_rfl⟩

/-- The context coatom is the image of the first points. -/
theorem map_castSuccEmb_eq_ctxCoatom :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) = ctxCoatom m :=
  Coatom.univ_map_left

end Seed

namespace StageType

open Finset Label CellScheme
variable {α : Ordinal.{u}} {n : ℕ}

/-- **The root lift of a legal donor at a grade `K`**, with a cap self-visible at `K`. -/
theorem IsLegal.exists_rootLift_le {d : StageType.{u} α (n + 1)} (hd : d.IsLegal) (hn : 0 < n)
    {p : StageType.{u} α n}
    (hdp : VaughtConjecture.StageType.restrictFace Fin.castSuccEmb d = some p)
    {v : Fin d.card → Label.{u}} (hv : d.rows.IsLawful v) {ρ : Fin p.card → Label.{u}}
    (hρ : p.rows.IsLawful ρ) {K : ℕ} (hK1 : 1 ≤ K) (hKn : K ≤ n + 1)
    (hρK : ∀ i, K < p.toCellScheme.grade i → ρ i = ⊥) {γ : Label.{u}} (hγ : IsSelfVisible K γ)
    (hag : ∀ i, p.toCellScheme.grade i ≤ K → min (ρ i) γ = min (v (d.faceCell hdp i)) γ) :
    ∃ v' : Fin d.card → Label.{u}, d.rows.IsLawful v' ∧ (∀ i, v' (d.faceCell hdp i) = ρ i) ∧
      (∀ j, K < d.toCellScheme.grade j → v' j = ⊥) ∧
      ∀ j, d.toCellScheme.grade j ≤ K → min (v' j) γ = min (v j) γ := by
  classical
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff d _).mp hdp
  set K' := min K n with hK'
  set X : Finset (Fin (n + 1)) × ℕ := (univ.map Fin.castSuccEmb, K')
  set Y : Finset (Fin (n + 1)) × ℕ := ((univ : Finset (Fin (n + 1))), K)
  have hXY : X ≤ Y := ⟨subset_univ _, min_le_left _ _⟩
  have hφ := d.toScheme.isLowerEmbedding_comap Fin.castSuccEmb
  have himg : d.toScheme.cellMap Fin.castSuccEmb ''
      (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
        ((univ : Finset (Fin n)), K') = d.toCellScheme.below X := by
    rw [Scheme.image_cellMap_below]
    rfl
  let r : d.toCellScheme.below X → Label.{u} := fun x ↦ ρ ((hφ.belowEquiv himg).symm x).1
  have hr : d.rows.IsLawfulBelow X r := by
    rw [← CellScheme.Rows.isLawfulBelow_comap_iff hφ himg]
    have h1 : (d.rows.comap hφ).IsLawfulBelow ((univ : Finset (Fin n)), K') fun x ↦ ρ x.1 :=
      hρ.isLawfulBelow _
    convert h1 using 1
    funext x
    simp [r]
  have hsymm (i : Fin (d.comap Fin.castSuccEmb hf).card)
      (hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below ((univ : Finset (Fin n)), K'))
      (hm : d.toScheme.cellMap Fin.castSuccEmb i ∈ d.toCellScheme.below X) :
      ((hφ.belowEquiv himg).symm ⟨_, hm⟩).1 = i := by
    have : (hφ.belowEquiv himg) ⟨i, hi⟩ = ⟨_, hm⟩ := Subtype.ext rfl
    rw [← this, Equiv.symm_apply_apply]
  have hmemX (i : Fin (d.comap Fin.castSuccEmb hf).card)
      (hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
        ((univ : Finset (Fin n)), K')) :
      d.toScheme.cellMap Fin.castSuccEmb i ∈ d.toCellScheme.below X := by
    rw [← himg]
    exact ⟨i, hi, rfl⟩
  have hlift : d.rows.CappedLift hXY :=
    hd.isBountiful.cappedLift ⟨hf, lt_min (by omega) hn,
      by rw [card_map, card_univ, Fintype.card_fin]; exact min_le_right _ _⟩
      ⟨d.univ_mem_faces, (by omega : 0 < K), by rw [card_univ, Fintype.card_fin]; exact hKn⟩ hXY
  obtain ⟨q', hq', hq'cap, hq'r⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    hlift γ hγ r (fun x ↦ v x) hr (hv.isLawfulBelow _) (fun x ↦ by
      obtain ⟨x, hx⟩ := x
      have hx' := hx
      rw [← himg] at hx'
      obtain ⟨i, hi, rfl⟩ := hx'
      simp only [r]
      rw [hsymm i hi (hmemX i hi), hag i (hi.2.trans (min_le_left _ _))]
      rfl)
  let w : Fin d.card → Label.{u} := fun j ↦
    if h : d.toCellScheme.grade j ≤ K then q' ⟨j, ⟨subset_univ _, h⟩⟩ else ⊥
  have hw_le (j : Fin d.card) (h : d.toCellScheme.grade j ≤ K) :
      w j = q' ⟨j, ⟨subset_univ _, h⟩⟩ := by simp only [w, h, dite_true]
  have hw_lt (j : Fin d.card) (h : K < d.toCellScheme.grade j) : w j = ⊥ := by
    simp only [w, not_le.mpr h, dite_false]
  have hwY : (fun t : d.toCellScheme.below Y ↦ w t) = q' := funext fun t ↦ hw_le t.1 t.2.2
  have hwl : d.rows.IsLawfulBelow Y fun t ↦ w t := by rw [hwY]; exact hq'
  have hext := CellScheme.Rows.isLawfulBelow_extendAbove (K := n + 1) hwl
  have hext' : d.rows.IsLawfulBelow ((univ : Finset (Fin (n + 1))), n + 1) fun j ↦ w j := by
    refine (CellScheme.Rows.isLawfulBelow_congr (w := fun j ↦ if d.toCellScheme.grade j ≤ K
      then w j else ⊥) fun j _ ↦ ?_).mp hext
    by_cases h : d.toCellScheme.grade j ≤ K
    · exact ite_eq_left h
    · rw [ite_eq_right h, hw_lt j (not_le.mp h)]
  have hwL : d.rows.IsLawful w :=
    CellScheme.Rows.isLawful_of_isLawfulBelow (fun j ↦ by exact ⟨subset_univ _, d.grade_le j⟩)
      hext'
  refine ⟨w, hwL, fun i ↦ ?_, hw_lt, fun j hj ↦ ?_⟩
  · have hgi : (d.comap Fin.castSuccEmb hf).toCellScheme.grade i ≤ n :=
      (d.comap Fin.castSuccEmb hf).grade_le i
    have hgc : d.toCellScheme.grade (d.toScheme.cellMap Fin.castSuccEmb i) =
        (d.comap Fin.castSuccEmb hf).toCellScheme.grade i := rfl
    by_cases hik : (d.comap Fin.castSuccEmb hf).toCellScheme.grade i ≤ K
    · have hi : i ∈ (d.toScheme.comap Fin.castSuccEmb).toCellScheme.below
          ((univ : Finset (Fin n)), K') := ⟨subset_univ _, le_min hik hgi⟩
      change w (d.toScheme.cellMap Fin.castSuccEmb i) = ρ i
      rw [hw_le _ (hgc ▸ hik)]
      have h1 := hq'r ⟨_, hmemX i hi⟩
      simp only [r] at h1
      rw [hsymm i hi (hmemX i hi)] at h1
      exact h1
    · change w (d.toScheme.cellMap Fin.castSuccEmb i) = ρ i
      rw [hw_lt _ (hgc ▸ not_le.mp hik), hρK i (not_le.mp hik)]
  · rw [hw_le j hj]
    exact hq'cap ⟨j, ⟨subset_univ _, hj⟩⟩

end StageType

end VaughtConjecture

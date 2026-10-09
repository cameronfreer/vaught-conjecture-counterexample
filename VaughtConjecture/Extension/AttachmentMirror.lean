/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachmentLadderTower
import VaughtConjecture.Extension.MirrorScheme

/-!
# The replicated scheme over the attachment

Roadmap, Layer 3 ((R3) and (R4), the replicated carrier).

For a seed `I`, a root `g` of the context inside its first coatom, and the ladder tower over the
attachment at the height `m` (`Seed.attachmentBase`), the **mixed faces** (`Seed.mixedFaces`) are
the proper faces of the amalgam lying neither in the context face nor in the donor face.  No mixed
face lies inside the scope of a cell of proper scope of the tower (`Seed.not_subset_scope_tower`:
such a cell is a cell of the attachment, of scope inside the context face or the donor face), so
the tower carries copies of its cells of full scope at the mixed faces: the **replicated scheme**
(`Seed.replicated`, an instance of `Scheme.mirror`).

* **Laws** (`Seed.isWellFormed_replicated`, `Seed.isCoded_replicated`,
  `Seed.isConsistent_replicated`, `Seed.grade_lt_replicated`).
* **Completeness below the full grade** (`Seed.exists_gradedIndex_replicated`): the full faces
  from the tower (`Scheme.LadderBaseData.exists_gradedIndex_univ_ladderTower`), the faces inside
  the context or the donor face from the amalgam through the attachment, the mixed faces from the
  copies (`Scheme.exists_gradedIndex_mirror`).
* **The attachment inside the replicated scheme** (`Seed.attachEmb`): a strictly monotone lower
  embedding keeping scopes and rows (`Seed.isLowerEmbedding_attachEmb`,
  `Seed.comap_rows_attachEmb`), whose image contains every cell of scope inside the context face
  or the donor face (`Seed.mem_range_attachEmb`).  Hence the **literal faces**
  (`Seed.comap_left_replicated`, `Seed.comap_donor_replicated`): the context face of the
  replicated scheme is the first coatom type, its donor face the donor.

## References

The amalgam is [Kni26, Definition 4.3.1]; lawful sections and consistency are
[Kni26, Definitions 2.5.4 and 2.5.12].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-! ### The mixed faces -/

open Classical in
/-- The **mixed faces**: the proper faces of the amalgam lying neither in the context face nor in
the donor face. -/
noncomputable def mixedFaces : Finset (Finset (Fin (m + 2))) :=
  univ.filter fun U ↦ U ∈ I.amalgam.toCellScheme.faces ∧ U ≠ univ ∧
    ¬ U ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∧
      ¬ U ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))

theorem mem_mixedFaces {U : Finset (Fin (m + 2))} :
    U ∈ I.mixedFaces g ↔ U ∈ I.amalgam.toCellScheme.faces ∧ U ≠ univ ∧
      ¬ U ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∧
        ¬ U ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
  classical
  simp only [mixedFaces, mem_filter, mem_univ, true_and]

/-- Every cell of the attachment has scope inside the context face or the donor face. -/
theorem scope_attachment (d : Fin (I.attachment g).card) :
    (I.attachment g).toCellScheme.scope d ⊆
        univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      (I.attachment g).toCellScheme.scope d ⊆
        univ.map (extendByLast (g.trans Fin.castSuccEmb)) :=
  (I.mem_attachmentCells g).mp ((I.attachmentCells g).orderEmbOfFin_mem rfl d)

/-- The face of the context, as a finite set of points, is not the ground set. -/
theorem map_castSuccEmb_ne_univ :
    univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ≠ univ :=
  Coatom.univ_map_left_ne

/-- The donor face, as a finite set of points, is not the ground set. -/
theorem map_extendByLast_ne_univ :
    univ.map (extendByLast (g.trans Fin.castSuccEmb)) ≠ (univ : Finset (Fin (m + 2))) := by
  intro he
  have h := mem_univ (Fin.castSucc (Fin.last m) : Fin (m + 2))
  rw [← he, mem_map] at h
  obtain ⟨a, -, ha⟩ := h
  induction a using Fin.lastCases with
  | last => rw [extendByLast_last] at ha; exact absurd ha (Fin.castSucc_lt_last _).ne'
  | cast a =>
    rw [extendByLast_castSucc, Function.Embedding.trans_apply] at ha
    have ha' := Fin.castSucc_injective _ ha
    simp at ha'

variable (H : ℕ) (Γ : Finset Label.{u})
  (A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop) (B' : ℕ)

/-- The ladder tower over the attachment at the height `m`. -/
noncomputable abbrev attachTower
    (G : ℕ → Finset Label.{u} := fun j ↦ Scheme.heightSet Γ B' j) : Scheme.{u} (m + 2) :=
  ((I.attachmentBase g).ladderTower H Γ A B' m G).S

/-- **No mixed face lies inside the scope of a cell of proper scope of the tower**: such a cell is
a cell of the attachment. -/
theorem not_subset_scope_tower {G : ℕ → Finset Label.{u}}
    (z : Fin (I.attachTower g H Γ A B' G).card)
    (hz : (I.attachTower g H Γ A B' G).toCellScheme.scope z ≠ univ) (U : Finset (Fin (m + 2)))
    (hU : U ∈ I.mixedFaces g) : ¬ U ⊆ (I.attachTower g H Γ A B' G).toCellScheme.scope z := by
  obtain ⟨d, rfl⟩ := (I.attachmentBase g).mem_range_baseCellEmb m z hz
  rw [Scheme.LadderBaseData.scope_baseCellEmb]
  obtain ⟨-, -, hc, hdn⟩ := (I.mem_mixedFaces g).mp hU
  intro hUd
  rcases I.scope_attachment g d with h | h
  · exact hc (hUd.trans h)
  · exact hdn (hUd.trans h)

/-- **The replicated scheme over the attachment**: the ladder tower over the attachment with a
copy of each cell of full scope at each mixed face of size at least its grade. -/
noncomputable abbrev replicated
    (G : ℕ → Finset Label.{u} := fun j ↦ Scheme.heightSet Γ B' j) : Scheme.{u} (m + 2) :=
  Scheme.mirror (I.not_subset_scope_tower g H Γ A B' (G := G))

variable {I g H Γ A B'} {G : ℕ → Finset Label.{u}}

/-! ### Laws -/

/-- The faces of the replicated scheme are those of the amalgam. -/
theorem faces_replicated :
    (I.replicated g H Γ A B' G).toCellScheme.faces = I.amalgam.toCellScheme.faces :=
  (I.attachmentBase g).faces_ladderTower m

/-- The ground set of the replicated scheme is that of the amalgam. -/
theorem ground_replicated :
    (I.replicated g H Γ A B' G).toCellScheme.ground = I.amalgam.toCellScheme.ground :=
  (I.attachmentBase g).ground_ladderTower m

/-- **The replicated scheme is well formed.** -/
theorem isWellFormed_replicated : (I.replicated g H Γ A B' G).IsWellFormed :=
  Scheme.isWellFormed_mirror (Scheme.LadderBaseData.isWellFormed_ladderTower (by omega))
    fun U hU ↦ (I.attachmentBase g).faces_ladderTower (H := H) (Γ := Γ) (A := A) (B' := B')
      (G := G) m ▸
      ((I.mem_mixedFaces g).mp hU).1

/-- **The replicated scheme is consistent.** -/
theorem isConsistent_replicated (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) :
    (I.replicated g H Γ A B').rows.IsConsistent :=
  Scheme.isConsistent_mirror (Scheme.LadderBaseData.ladderTower_lawful hH hcard hΓ hA m).1

/-- **The replicated scheme is coded.** -/
theorem isCoded_replicated (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) : (I.replicated g H Γ A B').IsCoded :=
  Scheme.isCoded_mirror (Scheme.LadderBaseData.isCoded_ladderTower hcard hΓω hA m)

/-- **Every cell of the replicated scheme has grade below the full grade.** -/
theorem grade_lt_replicated (k : Fin (I.replicated g H Γ A B' G).card) :
    (I.replicated g H Γ A B' G).toCellScheme.grade k < m + 2 :=
  Scheme.LadderBaseData.grade_lt_ladderTower (K := m) (by omega) _

/-- **Completeness of the replicated scheme below the full grade**, for nonempty catalogues. -/
theorem exists_gradedIndex_replicated (hH : 0 < H)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty)
    {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ (I.replicated g H Γ A B' G).toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ k, (I.replicated g H Γ A B' G).toCellScheme.gradedIndex k = X := by
  have hXF : X.1 ∈ I.amalgam.toCellScheme.faces := faces_replicated ▸ hX.1
  have hX0 : 0 < X.2 := hX.2.1
  by_cases hXu : X.1 = univ
  · obtain ⟨d, hd⟩ := (I.attachmentBase g).exists_gradedIndex_univ_ladderTower (B' := B') hH hne
      m X.2 hX0 (by omega)
    refine ⟨Fin.castAdd _ d, (Scheme.gradedIndex_mirror_castAdd d).trans ?_⟩
    rw [hd]
    exact Prod.ext hXu.symm rfl
  by_cases hXc : X.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))
  · obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq X ⟨hXF, hX.2⟩ hXu
    have hcL : c ∈ I.attachmentCells g := (I.mem_attachmentCells g).mpr (by
      rw [show I.amalgam.toCellScheme.scope c = X.1 from congrArg Prod.fst hc]
      exact hXc)
    obtain ⟨d, hd⟩ : c ∈ Set.range (I.amalgam.toScheme.lowerEmb (I.attachmentCells g)) := by
      have h := ((I.attachmentCells g).range_orderEmbOfFin rfl).symm ▸ (mem_coe.mpr hcL)
      exact h
    refine ⟨Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m d),
      (Scheme.gradedIndex_mirror_castAdd _).trans
        (((I.attachmentBase g).gradedIndex_baseCellEmb m d).trans ?_)⟩
    change I.amalgam.toCellScheme.gradedIndex (I.amalgam.toScheme.lowerEmb _ d) = X
    rw [hd, hc]
  · push Not at hXc
    have hU : X.1 ∈ I.mixedFaces g := (I.mem_mixedFaces g).mpr ⟨hXF, hXu, hXc.1, hXc.2⟩
    have hlt : #X.1 < m + 2 := by
      simpa using card_lt_card (ssubset_univ_iff.mpr hXu)
    obtain ⟨f, hf⟩ := (I.attachmentBase g).exists_gradedIndex_univ_ladderTower (B' := B') (A := A)
      hH hne m X.2 hX0 (by have := hX.2.2; omega)
    exact Scheme.exists_gradedIndex_mirror hU hX.2.2 hf

/-! ### The attachment inside the replicated scheme -/

variable (I g H Γ A B') in
/-- The cells of the attachment in the replicated scheme. -/
noncomputable def attachEmb (d : Fin (I.attachment g).card) :
    Fin (I.replicated g H Γ A B' G).card :=
  Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m d)

theorem strictMono_attachEmb : StrictMono (I.attachEmb g H Γ A B' (G := G)) :=
  (Fin.castAddOrderEmb _).strictMono.comp ((I.attachmentBase g).strictMono_baseCellEmb m)

/-- The cells of the attachment keep their graded indices in the replicated scheme. -/
theorem gradedIndex_attachEmb (d : Fin (I.attachment g).card) :
    (I.replicated g H Γ A B' G).toCellScheme.gradedIndex (I.attachEmb g H Γ A B' d) =
      (I.attachment g).toCellScheme.gradedIndex d :=
  (Scheme.gradedIndex_mirror_castAdd _).trans ((I.attachmentBase g).gradedIndex_baseCellEmb m d)

theorem scope_attachEmb (d : Fin (I.attachment g).card) :
    (I.replicated g H Γ A B' G).toCellScheme.scope (I.attachEmb g H Γ A B' d) =
      (I.attachment g).toCellScheme.scope d :=
  congrArg Prod.fst (gradedIndex_attachEmb d)

/-- The copies have mixed scope. -/
theorem scope_replicated_natAdd
    (j : Fin ((I.attachTower g H Γ A B' G).copyCount (I.mixedFaces g))) :
    (I.replicated g H Γ A B' G).toCellScheme.scope (Fin.natAdd _ j) ∈ I.mixedFaces g := by
  rw [Scheme.scope_mirror_natAdd]
  exact (((I.attachTower g H Γ A B' G).copyEquiv (I.mixedFaces g)).symm j).2.1

/-- **Every cell of the replicated scheme of scope inside the context face or the donor face is a
cell of the attachment.** -/
theorem mem_range_attachEmb (z : Fin (I.replicated g H Γ A B' G).card)
    (hz : (I.replicated g H Γ A B' G).toCellScheme.scope z ⊆
        univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
      (I.replicated g H Γ A B' G).toCellScheme.scope z ⊆
        univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
    z ∈ Set.range (I.attachEmb g H Γ A B') := by
  induction z using Fin.addCases with
  | right j =>
    exfalso
    obtain ⟨-, -, hc, hdn⟩ := (I.mem_mixedFaces g).mp (scope_replicated_natAdd j)
    exact hz.elim hc hdn
  | left c =>
    have hsc : (I.replicated g H Γ A B' G).toCellScheme.scope (Fin.castAdd _ c) =
        (I.attachTower g H Γ A B' G).toCellScheme.scope c :=
      congrArg Prod.fst
        (Scheme.gradedIndex_mirror_castAdd (hmix := I.not_subset_scope_tower g H Γ A B') c)
    have hne : (I.attachTower g H Γ A B' G).toCellScheme.scope c ≠ univ := by
      intro he
      rw [hsc, he] at hz
      rcases hz with h | h
      · exact map_castSuccEmb_ne_univ (univ_subset_iff.mp h)
      · exact map_extendByLast_ne_univ g (univ_subset_iff.mp h)
    obtain ⟨d, rfl⟩ := (I.attachmentBase g).mem_range_baseCellEmb m c hne
    exact ⟨d, rfl⟩

/-- **The attachment is a lower embedding into the replicated scheme.** -/
theorem isLowerEmbedding_attachEmb :
    (I.attachment g).toCellScheme.IsLowerEmbedding (I.replicated g H Γ A B' G).toCellScheme
      (I.attachEmb g H Γ A B') where
  injective := strictMono_attachEmb.injective
  grade_eq d := congrArg Prod.snd (gradedIndex_attachEmb d)
  le_iff s t := by rw [gradedIndex_attachEmb, gradedIndex_attachEmb]
  mem_range t z hz := by
    rw [gradedIndex_attachEmb] at hz
    exact mem_range_attachEmb z ((I.scope_attachment g t).imp (fun h ↦ hz.1.trans h)
      fun h ↦ hz.1.trans h)

/-- **The replicated scheme reads the cells of the attachment as the attachment does.** -/
theorem rowAt_attachEmb (z x : Fin (I.attachment g).card) :
    (I.replicated g H Γ A B' G).rowAt (I.attachEmb g H Γ A B' z) (I.attachEmb g H Γ A B' x) =
      (I.attachment g).rowAt z x :=
  (Scheme.rowAt_mirror_castAdd _ _).trans ((I.attachmentBase g).rowAt_baseCellEmb m z x)

/-- The original of a cell of the attachment in the replicated scheme is its cell in the tower. -/
theorem mirrorOrig_attachEmb (e : Fin (I.attachment g).card) :
    (I.attachTower g H Γ A B' G).mirrorOrig (I.mixedFaces g) (I.attachEmb g H Γ A B' e) =
      (I.attachmentBase g).baseCellEmb m e :=
  Scheme.mirrorOrig_castAdd _ _ _

/-- **The rows of the replicated scheme pull back to those of the attachment.** -/
theorem comap_rows_attachEmb :
    (I.replicated g H Γ A B' G).rows.comap isLowerEmbedding_attachEmb = (I.attachment g).rows := by
  ext s t
  rw [CellScheme.Rows.comap_row]
  have h := rowAt_attachEmb (I := I) (g := g) (H := H) (Γ := Γ) (A := A) (B' := B') (G := G) s t.1
  rw [Scheme.rowAt_of_mem, Scheme.rowAt_of_mem t.2] at h
  exact h

/-! ### The literal faces -/

/-- The cells of the replicated scheme visible through the context face are cells of the
attachment. -/
theorem mem_range_attachEmb_left (z : Fin (I.replicated g H Γ A B' G).card)
    (hz : ((I.replicated g H Γ A B' G).toCellScheme.scope z : Set (Fin (m + 2))) ⊆
      Set.range (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2))) :
    z ∈ Set.range (I.attachEmb g H Γ A B') :=
  mem_range_attachEmb z (.inl fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))

/-- The cells of the replicated scheme visible through the donor face are cells of the
attachment. -/
theorem mem_range_attachEmb_donor (z : Fin (I.replicated g H Γ A B' G).card)
    (hz : ((I.replicated g H Γ A B' G).toCellScheme.scope z : Set (Fin (m + 2))) ⊆
      Set.range (extendByLast (g.trans Fin.castSuccEmb))) :
    z ∈ Set.range (I.attachEmb g H Γ A B') :=
  mem_range_attachEmb z (.inr fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y))

/-- **The context face of the replicated scheme is the first coatom type.** -/
theorem comap_left_replicated :
    (I.replicated g H Γ A B' G).comap Fin.castSuccEmb = I.left.toScheme :=
  ((Scheme.comap_eq_of_strictMono Fin.castSuccEmb strictMono_attachEmb isLowerEmbedding_attachEmb
    scope_attachEmb comap_rows_attachEmb ground_replicated faces_replicated
    mem_range_attachEmb_left).trans (I.comap_left_attachment g)).trans
    (congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp I.restrictFace_left).2)

/-- **The donor face of the replicated scheme is the donor.** -/
theorem comap_donor_replicated {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d) :
    (I.replicated g H Γ A B' G).comap (extendByLast (g.trans Fin.castSuccEmb)) = d.toScheme :=
  ((Scheme.comap_eq_of_strictMono _ strictMono_attachEmb isLowerEmbedding_attachEmb
    scope_attachEmb comap_rows_attachEmb ground_replicated faces_replicated
    mem_range_attachEmb_donor).trans (I.comap_donor_attachment g)).trans
    (congrArg StageType.toScheme ((restrictFace_eq_some_iff _ _).mp hd).2)

end Seed

end VaughtConjecture

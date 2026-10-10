/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SeedLadderTower

/-!
# The ladder tower of a seed as a completion below the full grade

Roadmap, Layer 3 ((R3) and (R4), the assembly of the recognizing growth carrier).

The ladder tower of a seed at the height `m` (`Seed.ladderTower`) carries the amalgam as its old
cells (`Seed.towerAmalgamEmb`: the cells of the amalgam in the base, then in the tower), a lower
embedding keeping scopes and rows, containing every cell of proper scope, with the faces of the
amalgam.  It satisfies every law of `Scheme.IsLegalBelowFullGrade` except bountifulness
(`VaughtConjecture.Extension.SeedLadderTower`).  So, given

* **bountifulness of the tower** (open: the lifts into the full faces of grades `2` and above),
* **a lawful labelling extending the glued labels of the amalgam**,

the tower is a completion below the full grade (`Seed.ladderCompletion`,
`CompletionBelowFullGrade`), whose completion at a stage that is zero or a limit is a legal stage
type with the two coatom types of the seed as literal faces.

**Scope.**  Part of the earlier route (the replicated scheme over the height-set tower, or the
ladder tower of the amalgam), whose open inputs the levels re-rendered per grade replace; not used
by the main theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept
as reusable constructions.

## References

The completion of [Kni26, Definition 4.3.14]; the coatom extension is [Kni26, Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (H : ℕ) (Γ : Finset Label.{u})
  (A : ℕ → (Fin I.amalgam.card → Label.{u}) → Prop) (B' : ℕ)

/-- The cells of the amalgam in the ladder tower at the height `m`. -/
noncomputable def towerAmalgamEmb : Fin I.amalgam.card ↪o Fin (I.ladderTower H Γ A B' m).S.card :=
  OrderEmbedding.ofStrictMono (fun d ↦ Scheme.layerTowerEmb (B := I.towerBase H)
      (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m (Fin.castAdd _ d))
    ((Scheme.strictMono_layerTowerEmb m).comp (Fin.castAddOrderEmb _).strictMono)

theorem towerAmalgamEmb_apply (d : Fin I.amalgam.card) :
    I.towerAmalgamEmb H Γ A B' d = Scheme.layerTowerEmb (B := I.towerBase H)
      (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m (Fin.castAdd _ d) := rfl

/-- The amalgam is a lower embedding into the ladder tower. -/
theorem isLowerEmbedding_towerAmalgamEmb :
    I.amalgam.toCellScheme.IsLowerEmbedding (I.ladderTower H Γ A B' m).S.toCellScheme
      (I.towerAmalgamEmb H Γ A B') := by
  exact (Scheme.isLowerEmbedding_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
    (G := fun k ↦ grid k B') m).comp
    (Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 _ _ I.noFullOne)

theorem scope_towerAmalgamEmb (d : Fin I.amalgam.card) :
    (I.ladderTower H Γ A B' m).S.toCellScheme.scope (I.towerAmalgamEmb H Γ A B' d) =
      I.amalgam.toCellScheme.scope d := by
  rw [towerAmalgamEmb_apply]
  exact (Scheme.scope_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
    (G := fun k ↦ grid k B') _ m).trans (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d)

theorem comap_rows_towerAmalgamEmb :
    (I.ladderTower H Γ A B' m).S.rows.comap (I.isLowerEmbedding_towerAmalgamEmb H Γ A B') =
      I.amalgam.rows := by
  exact (congrArg (fun R ↦ CellScheme.Rows.comap R
    (Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 _ _ I.noFullOne))
    (Scheme.comap_rows_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
      (G := fun k ↦ grid k B') m)).trans (Scheme.comap_rows_castAdd (S := I.amalgam.toScheme))

theorem mem_range_towerAmalgamEmb (z : Fin (I.ladderTower H Γ A B' m).S.card)
    (hz : (I.ladderTower H Γ A B' m).S.toCellScheme.scope z ≠ univ) :
    z ∈ Set.range (I.towerAmalgamEmb H Γ A B') := by
  obtain ⟨t, rfl⟩ := Scheme.mem_range_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
    (G := fun k ↦ grid k B') m z hz
  have hz' := hz
  change (Scheme.layerTower (I.towerBase H) (I.towerCat Γ A) (fun k ↦ grid k B')
    m).S.toCellScheme.scope (Scheme.layerTowerEmb m t) ≠ univ at hz'
  rw [Scheme.scope_layerTowerEmb] at hz'
  induction t using Fin.addCases with
  | left d => exact ⟨d, rfl⟩
  | right j =>
    exfalso
    change (I.amalgam.toScheme.appendFullCellsScheme 1 _).scope (Fin.natAdd _ j) ≠ univ at hz'
    exact hz' (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j)

theorem faces_ladderTower :
    (I.ladderTower H Γ A B' m).S.toCellScheme.faces = I.amalgam.toCellScheme.faces :=
  Scheme.faces_layerTower (B := I.towerBase H) (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m

/-- **Bountifulness of the ladder tower from the two coatom lifts**: below a pair of proper scope
the tower is the amalgam (bountiful), into the full face of grade one it is the padded grade-one
base (`Seed.cappedLift_ladderBase`), and the lifts from the two coatoms into the full faces of the
grades `2, …, m + 1` give the rest (`CellScheme.Rows.isBountiful_of_coatoms`). -/
theorem isBountiful_ladderTower_of_coatomLifts (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    (hlift : ∀ x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} : Finset (Fin (m + 2))),
      ∀ j, 2 ≤ j → j ≤ m + 1 →
        (I.ladderTower H Γ A B' m).S.rows.CappedLift (X := (univ.erase x, j))
          (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩) :
    (I.ladderTower H Γ A B' m).S.rows.IsBountiful := by
  classical
  set T := I.ladderTower H Γ A B' m with hT
  have hfacesT := I.faces_ladderTower H Γ A B'
  -- the amalgam is a source prefix of the tower below every pair of proper scope
  have hpre {Y : Finset (Fin (m + 2)) × ℕ} (hY : Y.1 ≠ univ) :
      I.amalgam.toCellScheme.IsSourcePrefix T.S.toCellScheme (I.towerAmalgamEmb H Γ A B') Y :=
    ⟨I.isLowerEmbedding_towerAmalgamEmb H Γ A B', I.scope_towerAmalgamEmb H Γ A B',
      fun z hz ↦ I.mem_range_towerAmalgamEmb H Γ A B' z fun he ↦
        hY (univ_subset_iff.mp (he ▸ (hz.1 : T.S.toCellScheme.scope z ⊆ Y.1)))⟩
  have hgf {X : Finset (Fin (m + 2)) × ℕ} (hX : X ∈ T.S.toCellScheme.gradedFaces) :
      X ∈ I.amalgam.toCellScheme.gradedFaces := ⟨hfacesT ▸ hX.1, hX.2⟩
  have hproper : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄, X ∈ T.S.toCellScheme.gradedFaces →
      Y ∈ T.S.toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ≠ univ → T.S.rows.CappedLift h := by
    intro X Y hX hY h hY1
    rw [← ((hpre hY1).cappedLift_iff h le_rfl), I.comap_rows_towerAmalgamEmb H Γ A B']
    exact I.isBountiful (hgf hX) (hgf hY) h
  -- the base is a source prefix of the tower below the full face of grade one
  have hbase : (I.ladderBase H).toCellScheme.IsSourcePrefix T.S.toCellScheme
      (Scheme.layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m)
      ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨Scheme.isLowerEmbedding_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
        (G := fun k ↦ grid k B') m,
      fun t ↦ Scheme.scope_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
        (G := fun k ↦ grid k B') t m,
      fun z hz ↦ Scheme.mem_range_layerTowerEmb_of_grade (B := I.towerBase H)
        (C := I.towerCat Γ A) (G := fun k ↦ grid k B') m z hz.2⟩
  have hone (x : Fin (m + 2)) (hxF : univ.erase x ∈ I.amalgam.toCellScheme.faces) :
      T.S.rows.CappedLift (X := (univ.erase x, 1)) (Y := ((univ : Finset (Fin (m + 2))), 1))
        ⟨erase_subset _ _, le_rfl⟩ := by
    have hcl : T.S.rows.comap hbase.isLowerEmbedding = (I.ladderBase H).rows :=
      Scheme.comap_rows_layerTowerEmb (B := I.towerBase H) (C := I.towerCat Γ A)
        (G := fun k ↦ grid k B') m
    rw [← (hbase.cappedLift_iff _ le_rfl), hcl]
    have hcard' : 1 ≤ #(univ.erase x) := by
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
    exact I.cappedLift_ladderBase H hH hcard ⟨hxF, by omega, hcard'⟩
      ⟨I.amalgam.isWellFormed.univ_mem_faces, by omega, by simp⟩ _ (.inr rfl)
  have hfull (x : Fin (m + 2)) (hx : x ∈ ({Fin.last (m + 1), Fin.castSucc (Fin.last m)} :
      Finset (Fin (m + 2)))) (hxF : univ.erase x ∈ I.amalgam.toCellScheme.faces) :
      ∀ j ≤ #(univ.erase x), T.S.rows.CappedLift (X := (univ.erase x, j))
        (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
    intro j hj
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · rcases Nat.lt_or_ge j 1 with hj1 | hj1
      · have hj0 : j = 0 := by omega
        subst hj0
        refine CellScheme.Rows.cappedLift_of_below_eq_empty ?_ _
        ext z
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hz
        have h1 : T.S.toCellScheme.grade z ≤ 0 := hz.2
        have h2 := (I.isWellFormed_ladderTower (H := H) (Γ := Γ) (A := A) (B' := B') (k := m)
          (by omega)).isWellFormed.grade_pos z
        exact Nat.lt_irrefl 0 (h2.trans_le h1)
      · have hj1' : j = 1 := by omega
        subst hj1'
        exact hone x hxF
    · exact hlift x hx j hj2 (by omega)
  have hleftF : univ.erase (Fin.last (m + 1)) ∈ I.amalgam.toCellScheme.faces := by
    rw [← Coatom.univ_map_left]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hrightF : univ.erase (Fin.castSucc (Fin.last m)) ∈ I.amalgam.toCellScheme.faces := by
    rw [← Coatom.univ_map_right]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (mem_univ (Fin.last (m + 1)))
    (mem_univ (Fin.castSucc (Fin.last m))) (fun B hB hBu ↦ ?_) (hfacesT ▸ hleftF)
    (hfacesT ▸ hrightF) hproper (hfull _ (by simp) hleftF) (hfull _ (by simp) hrightF)
  exact I.subset_or_subset B (hfacesT ▸ hB) hBu

variable {I H Γ A B'}

/-- **The ladder tower as a completion below the full grade**, given its bountifulness and a lawful
labelling extending the glued labels of the amalgam. -/
noncomputable def ladderCompletion (hH : 0 < H) (hcard : I.amalgam.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (hne : ∀ k, (I.towerCat Γ A (k + 2)).Nonempty)
    (hbount : (I.ladderTower H Γ A B' m).S.rows.IsBountiful)
    (hlab : ∃ q : Fin (I.ladderTower H Γ A B' m).S.card → Label.{u},
      (I.ladderTower H Γ A B' m).S.rows.IsLawful q ∧
        ∀ d, q (I.towerAmalgamEmb H Γ A B' d) = I.amalgam.label d) :
    CompletionBelowFullGrade I where
  scheme := (I.ladderTower H Γ A B' m).S
  embed := I.towerAmalgamEmb H Γ A B'
  isLowerEmbedding := I.isLowerEmbedding_towerAmalgamEmb H Γ A B'
  scope_embed := I.scope_towerAmalgamEmb H Γ A B'
  comap_rows := I.comap_rows_towerAmalgamEmb H Γ A B'
  mem_range_embed := I.mem_range_towerAmalgamEmb H Γ A B'
  faces_eq := I.faces_ladderTower H Γ A B'
  isLegalBelowFullGrade :=
    { isWellFormed := I.isWellFormed_ladderTower (k := m) (by omega)
      isCoded := isCoded_ladderTower hcard hΓω hA m
      isConsistent := (ladderTower_lawful hH hcard hΓ hA m).1
      isBountiful := hbount
      grade_lt := grade_lt_ladderTower
      exists_gradedIndex_eq := fun X hX hX2 ↦ exists_gradedIndex_ladderTower hH hne hX hX2 }
  label := hlab.choose
  isLawful := hlab.choose_spec.1
  label_embed := hlab.choose_spec.2

end Seed

end VaughtConjecture

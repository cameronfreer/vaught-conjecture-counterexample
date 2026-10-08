/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CompletionBelowFullGrade
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

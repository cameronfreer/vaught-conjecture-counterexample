/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerTwoValued

/-!
# The fills of the reading layer and the ties of the common face

Roadmap, Layer 3 ((R3) of the table of 3.4).

The four fill conditions of the reading layer (`TowerProfile.isLegalBelowFullGrade_readingTop_iff`)
against the ties of the common face, at markers whose row reads cells strictly between `⊥` and
itself.

* **A failing fill** (`TowerProfile.not_readingFillBot_left_of_inversion`,
  `TowerProfile.not_isLegalBelowFullGrade_readingTop_of_inversion`, compiled in this repository
  (theorem named)): if a cell `x ∈ X` reads two cells `y₁`, `y₂` of the left coatom with `y₁` at
  most as `y₂` (the second of grade at most the first), and a labelling `f` lawful below the left
  coatom inverts them below its value at the marker (`f y₂ < f y₁ ≤ f r`), the fill at `⊥` from the
  left coatom fails at `f`, and the reading layer is not legal.  This is the seed-level form of the
  refutation schema `StageType.not_raisesNewTops_of_row_le`; no instance at five points is
  compiled here.
* **A marker that keeps the tie excludes it** (`TowerProfile.le_of_row_le_marker`, compiled): if
  the row of the marker reads `y₁` at most as `y₂`, every lawful `f` with `f y₁ ≤ f r` has
  `f y₁ ≤ f y₂`.
* **The fill at `⊥` from the left coatom when the marker reads the common face as `⊥`**
  (`TowerProfile.exists_glue_four`, `TowerProfile.readingFillBot_left_of_face_bot`,
  `TowerProfile.readingFillBot_left_of_left`, compiled): the given labelling is `⊥` on the common
  face and is glued to a labelling `⊤` on `X`; no condition on the other readings of the marker.
* **A proper-labelled marker** (`TopReadingApexExample.threeType`,
  `TopReadingApexExample.seedThree`,
  `TopReadingApexExample.rowAt_threeType_three`, `TopReadingApexExample.readingFills_seedThree`,
  compiled): the type `S` labelled `3` at its live cells of grade at most `2`, with the apex; the
  apex reads the cell `{3}` at the code of `3`, strictly between `⊥` and its reading of itself.
  At the seed with `rightType`, three of the four fills hold: at `⊥` from the left coatom (the
  apex reads the common face as `⊥`) and both fills from the right coatom
  (`TowerProfile.readingFillBot_right_of_unique`, `TowerProfile.readingFillPos_right_of_unique`).
  **Open**: the fill at the short positive caps from the left coatom.  Below a proper label the
  given labelling is no longer fixed by the marker capped at its value, and the fill needs a
  labelling that agrees with it on the left coatom and with the mark capped at the cap elsewhere:
  a union of the two coatoms capped at the cap, which the profile layer gives only along its own
  rows (`TowerProfile.extendsFromBoundary_row`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {r : Fin (scheme I).card}
  {X : Finset (Fin (scheme I).card)}

/-! ### A failing fill: an inversion under a tie of a new top -/

/-- **The fill at `⊥` from the left coatom fails at an inversion under a tie.**  Let `f` be lawful
below the left coatom, `x ∈ X` a cell whose row reads two cells `y₁`, `y₂` of the left coatom
(the second of grade at most the first) with `y₁` at most as `y₂`, and suppose `f` inverts them
below its value at the marker: `f y₂ < f y₁ ≤ f r`.  Then no fill at `⊥` extends `f`: a fill reads
`x` at least as `r`, so at least as `f y₁`, and locality at `x` puts `y₁` at most at `y₂`. -/
theorem not_readingFillBot_left_of_inversion {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {x : Fin (scheme I).card} (hx : x ∈ X) {y₁ y₂ : Fin (scheme I).card}
    (hy₁ : y₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hy₂ : y₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hC₁ : y₁ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hC₂ : y₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hrow : (scheme I).rows.row x ⟨y₁, hy₁⟩ ≤ (scheme I).rows.row x ⟨y₂, hy₂⟩)
    (hg : (scheme I).toCellScheme.grade y₂ ≤ (scheme I).toCellScheme.grade y₁)
    (hinv : f y₂ < f y₁) (hfr : f y₁ ≤ f r) : ¬ ReadingFillBot I r X (Fin.last 4) := by
  intro hfill
  obtain ⟨g, hg', hgf, hgr⟩ := hfill f hf
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg'
  have h := (hloc x (mem_below_univ_four x)).le_of_le (d := ⟨y₁, hy₁⟩) (d' := ⟨y₂, hy₂⟩) hrow hg
  change min (g y₁) (g x) ≤ min (g y₂) (g x) at h
  rw [hgf y₁ hC₁, hgf y₂ hC₂] at h
  have hx' : f y₁ ≤ g x := hfr.trans ((hgf r hrC).symm.trans_le (hgr x hx))
  rw [min_eq_left hx'] at h
  exact absurd (h.trans (min_le_left _ _)) (not_le.mpr hinv)

/-- **The reading layer is not legal at an inversion under a tie**
(`TowerProfile.not_readingFillBot_left_of_inversion`,
`TowerProfile.isLegalBelowFullGrade_readingTop_iff`). -/
theorem not_isLegalBelowFullGrade_readingTop_of_inversion
    (hgr : (scheme I).toCellScheme.grade r = 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {x : Fin (scheme I).card} (hx : x ∈ X) {y₁ y₂ : Fin (scheme I).card}
    (hy₁ : y₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hy₂ : y₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hC₁ : y₁ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hC₂ : y₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hrow : (scheme I).rows.row x ⟨y₁, hy₁⟩ ≤ (scheme I).rows.row x ⟨y₂, hy₂⟩)
    (hg : (scheme I).toCellScheme.grade y₂ ≤ (scheme I).toCellScheme.grade y₁)
    (hinv : f y₂ < f y₁) (hfr : f y₁ ≤ f r) : ¬ (readingTop I r X).IsLegalBelowFullGrade :=
  fun hleg ↦ not_readingFillBot_left_of_inversion hf hrC hx hy₁ hy₂ hC₁ hC₂ hrow hg hinv hfr
    (((isLegalBelowFullGrade_readingTop_iff hgr hX).mp hleg).1 _ (by simp))

/-- **A marker whose row keeps the tie excludes the inversion**: if the row of the marker reads
`y₁` at most as `y₂` (the second of grade at most the first, both below the marker), then every
labelling lawful below the left coatom with `f y₁ ≤ f r` has `f y₁ ≤ f y₂` (locality at the marker).
So `TowerProfile.not_readingFillBot_left_of_inversion` never applies to a tie that the row of the
marker keeps. -/
theorem le_of_row_le_marker {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {y₁ y₂ : Fin (scheme I).card}
    (hy₁ : y₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hy₂ : y₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hrow : (scheme I).rows.row r ⟨y₁, hy₁⟩ ≤ (scheme I).rows.row r ⟨y₂, hy₂⟩)
    (hg : (scheme I).toCellScheme.grade y₂ ≤ (scheme I).toCellScheme.grade y₁)
    (hfr : f y₁ ≤ f r) : f y₁ ≤ f y₂ := by
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  have h := (hloc r hrC).le_of_le (d := ⟨y₁, hy₁⟩) (d' := ⟨y₂, hy₂⟩) hrow hg
  change min (f y₁) (f r) ≤ min (f y₂) (f r) at h
  rw [min_eq_left hfr] at h
  exact h.trans (min_le_left _ _)

/-! ### Gluing the two coatoms at the grade `4` -/

/-- **Gluing at the grade `4`**: a labelling lawful below both coatoms at the grade `4` of the
profile layer extends, unchanged below the coatoms, to a labelling lawful below `(univ, 4)`
(`TowerProfile.exists_extension_bot` at the grade `3`, and
`CellScheme.Rows.IsLawfulBelow.glue₃`). -/
theorem exists_glue_four {w : Fin (scheme I).card → Label.{u}}
    (hwC : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d)
    (hwD : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 4)
      fun d ↦ w d) :
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      ∀ d, d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) ∨
        d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) →
        g d = w d := by
  classical
  obtain ⟨r₃, hr₃, hr₃w⟩ := exists_extension_bot (w := w)
    (hwC.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩) (hwD.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩)
  obtain ⟨g, hg_def⟩ : ∃ g : Fin (scheme I).card → Label.{u}, g = fun e ↦
      if he : e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) then r₃ ⟨e, he⟩
      else w e := ⟨_, rfl⟩
  have hgw (e : Fin (scheme I).card) (he : (scheme I).toCellScheme.scope e ≠ univ) :
      g e = w e := by
    rw [hg_def]
    beta_reduce
    by_cases h3 : e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)
    · rw [dite_eq_left h3]; exact hr₃w ⟨e, h3⟩ he
    · exact dite_eq_right h3
  have hne {z : Fin 5} {e : Fin (scheme I).card}
      (he : e ∈ (scheme I).toCellScheme.below (univ.erase z, 4)) :
      (scheme I).toCellScheme.scope e ≠ univ := fun hs ↦
    Seed.ne_univ_erase z (univ_subset_iff.mp (hs.ge.trans he.1))
  have hgz (z : Fin 5) (hwz : (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ w d) :
      (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ g e :=
    (CellScheme.Rows.isLawfulBelow_congr (R := (scheme I).rows) (X := (univ.erase z, 4)) (w := g)
      (w' := w) fun e he ↦ hgw e (hne he)).mpr hwz
  have hg3 : (scheme I).rows.IsLawfulBelow (univ, 3) fun e ↦ g e := by
    convert hr₃ using 1
    exact funext fun e ↦ by rw [hg_def]; exact dite_eq_left e.2
  refine ⟨g, CellScheme.Rows.IsLawfulBelow.glue₃ (hgz _ hwC) hg3 (hgz _ hwD)
    (mem_below_cover (by simp) (by simp) (by decide)), fun d hd ↦ hgw d ?_⟩
  rcases hd with hd | hd
  exacts [hne hd, hne hd]

/-- **The fill at `⊥` from the left coatom when the marker reads the common face as `⊥`**: at the
marker `⊥`, the fill in the profile layer; otherwise the given labelling is `⊥` on the common face
(`TowerProfile.eq_bot_of_row_eq_bot`) and is glued to a labelling `L` that is `⊥` on the common face
and `⊤` on `X` (`TowerProfile.exists_glue_four`).  No condition on the other readings of the
marker. -/
theorem readingFillBot_left_of_face_bot
    (hgr : (scheme I).toCellScheme.grade r = 4)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hface : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
      y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) →
        (scheme I).rows.row r ⟨y, hy⟩ = ⊥)
    {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 4) fun d ↦ L d)
    (hLface : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) → L y = ⊥)
    (hXD : ∀ x ∈ X, x ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4))
    (hLX : ∀ x ∈ X, L x = ⊤) : ReadingFillBot I r X (Fin.last 4) := by
  classical
  intro f hf
  by_cases hfr : f r = ⊥
  · obtain ⟨g, hg, hgf, -⟩ := exists_fill_four (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3))
      (by simp) (by simp) (by decide) hf (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot
      (isSelfVisible_bot 4) fun _ _ ↦ by simp
    exact ⟨g, hg, hgf, fun x _ ↦ by rw [hgf r hrC, hfr]; exact bot_le⟩
  have hbelow {y : Fin (scheme I).card}
      (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
      y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r) :=
    mem_below_marker hgr hrC hy
  have hfface (y : Fin (scheme I).card)
      (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
      (hyD : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4)) :
      f y = ⊥ :=
    eq_bot_of_row_eq_bot hrC hf hfr (hbelow hy) (hface y (hbelow hy) hyD)
  set w : Fin (scheme I).card → Label.{u} := fun d ↦
    if d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) then f d else L d with hw
  have hwC : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d :=
    (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ (ite_eq_left hd :)).mpr hf
  have hwD : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 4)
      fun d ↦ w d := by
    refine (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ ?_).mpr hL
    by_cases hdC : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)
    · rw [hw]; dsimp only; rw [ite_eq_left hdC, hfface d hdC hd, hLface d hdC hd]
    · rw [hw]; dsimp only; rw [ite_eq_right hdC]
  obtain ⟨g, hg, hgw⟩ := exists_glue_four hwC hwD
  refine ⟨g, hg, fun d hd ↦ (hgw d (.inl hd)).trans (ite_eq_left hd), fun x hx ↦ ?_⟩
  have hxC : x ∉ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := fun hxC ↦ by
    have := hLface x hxC (hXD x hx)
    rw [hLX x hx] at this
    exact top_ne_bot this
  rw [hgw x (.inr (hXD x hx)), hw]
  dsimp only
  rw [ite_eq_right hxC, hLX x hx]
  exact le_top


/-- **The cell of a unique top cell of the left type** in the profile layer: of the grade `4`,
below the left coatom, the only cell there at or above its graded index. -/
theorem leftCell_props {a : Fin I.left.card} (ha : I.left.toCellScheme.gradedIndex a = (univ, 4))
    (hu : ∀ z, I.left.toCellScheme.gradedIndex z = (univ, 4) → z = a) :
    (scheme I).toCellScheme.grade (leftCell I a) = 4 ∧
      leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) ∧
      ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.gradedIndex (leftCell I a) ≤
          (scheme I).toCellScheme.gradedIndex y → y = leftCell I a := by
  have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst ha
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hgi : (scheme I).toCellScheme.gradedIndex (leftCell I a) =
      (univ.erase (Fin.last 4), 4) := by
    rw [gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
  refine ⟨congrArg Prod.snd hgi, by rw [CellScheme.mem_below, hgi], fun y hy hle ↦ ?_⟩
  obtain ⟨z, rfl⟩ := exists_leftCell_eq (I := I) fun h ↦ (notMem_erase _ _) (hy.1 h)
  have heq : (scheme I).toCellScheme.gradedIndex (leftCell I z) =
      (univ.erase (Fin.last 4), 4) := le_antisymm hy (hgi ▸ hle)
  rw [gradedIndex_leftCell, ← univ_map_left_eq] at heq
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
  rw [map_inj] at h1
  exact congrArg (leftCell I) (hu z (Prod.ext h1 h2))

/-! ### A left coatom type labelled `⊥` on the common face -/

/-- The image of the right coatom of `Fin 5`. -/
theorem univ_map_right_eq :
    (univ : Finset (Fin 4)).map (Coatom.right 3) = univ.erase (Fin.castSucc (Fin.last 3)) := by
  decide

/-- **The fill at `⊥` from the left coatom, for a left type labelled `⊥` on the common face**:
let `a` be the only cell of the left type of graded index `(univ, 4)`, whose row reads every cell
labelled `⊥` as `⊥`, the left type labelled `⊥` at every cell off the point `3` (the common face),
and `Z` a set of cells of the right type labelled `⊤`.  Then the fill at `⊥` from the left coatom
holds for the cell of `a` and the cells of `Z` (`TowerProfile.readingFillBot_left_of_face_bot`, with
the glued labelling of the completion). -/
theorem readingFillBot_left_of_left {a : Fin I.left.card}
    (ha : I.left.toCellScheme.gradedIndex a = (univ, 4))
    (hrowbot : ∀ z, I.left.label z = ⊥ → I.left.toScheme.rowAt a z = ⊥)
    (hfaceL : ∀ z, Fin.last 3 ∉ I.left.toCellScheme.scope z → I.left.label z = ⊥)
    (Z : Finset (Fin I.right.card)) (hZ : ∀ z ∈ Z, I.right.label z = ⊤) :
    ReadingFillBot I (leftCell I a)
      (Z.image fun z ↦ embed3 I (StageType.faceCell I.restrictFace_right z)) (Fin.last 4) := by
  have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst ha
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hgi : (scheme I).toCellScheme.gradedIndex (leftCell I a) =
      (univ.erase (Fin.last 4), 4) := by
    rw [gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
  have hgr : (scheme I).toCellScheme.grade (leftCell I a) = 4 := congrArg Prod.snd hgi
  have hrC : leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := by
    rw [CellScheme.mem_below, hgi]
  -- a cell below both coatoms is a cell of the left type off the point `3`, labelled `⊥`
  have hcommon {y : Fin (scheme I).card}
      (hyC : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
      (hyD : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4)) :
      ∃ z, leftCell I z = y ∧ I.left.label z = ⊥ := by
    obtain ⟨z, rfl⟩ := exists_leftCell_eq (I := I) fun h ↦ (notMem_erase _ _) (hyC.1 h)
    refine ⟨z, rfl, hfaceL z fun h3 ↦ ?_⟩
    have h := hyD.1
    rw [gradedIndex_leftCell] at h
    have := h (mem_map_of_mem _ h3)
    simp at this
  obtain ⟨q, hq, hqe⟩ := exists_isLawful_top (I := I)
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  have hold (d : Fin I.amalgam.card) :
      q (Fin.castAdd _ (embed3 I d)) = I.amalgam.label d := hqe d
  refine readingFillBot_left_of_face_bot hgr hrC (fun y hy hyD ↦ ?_)
    (L := fun d ↦ q (Fin.castAdd _ d)) (hL.isLawfulBelow _) (fun y hyC hyD ↦ ?_)
    (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨z, rfl, hz⟩ := hcommon (hgi ▸ hy) hyD
    rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
    exact hrowbot z hz
  · obtain ⟨z, rfl, hz⟩ := hcommon hyC hyD
    change q (Fin.castAdd _ (embed3 I (StageType.faceCell I.restrictFace_left z))) = ⊥
    rw [hold, StageType.label_faceCell]
    exact hz
  · obtain ⟨z, -, rfl⟩ := mem_image.mp hx
    rw [CellScheme.mem_below, gradedIndex_embed3]
    refine ⟨?_, ?_⟩
    · change I.amalgam.toCellScheme.scope _ ⊆ _
      rw [StageType.scope_faceCell, ← univ_map_right_eq]
      exact map_subset_map.mpr (subset_univ _)
    · change I.amalgam.toCellScheme.grade _ ≤ 4
      rw [StageType.grade_faceCell]
      exact I.right.grade_le z
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [hold, StageType.label_faceCell]
    exact hZ z hz

end TowerProfile

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The label `3`. -/
noncomputable abbrev lab3 : Label.{u} := ((3 : ℕ) : Label.{u})

/-- The cells of `S` off the point `3` are labelled `⊥` by `labelling A F ⊥`. -/
theorem labelling_bot_eq_bot_of_notMem {A F : Label.{u}} (d : Fin 19)
    (hd : (3 : Fin 4) ∉ TwoFaceLiftCounterexample.cellScope d) :
    CaseSplitCounterexample.labelling A F ⊥ d = ⊥ := by
  have key : ∀ d : Fin 19, (3 : Fin 4) ∉ TwoFaceLiftCounterexample.cellScope d →
      CaseSplitCounterexample.live d = false ∨ TwoFaceLiftCounterexample.cellGrade d = 3 := by
    decide
  unfold CaseSplitCounterexample.labelling
  rcases key d hd with h | h
  · simp [h]
  · simp [h]

include hα in
/-- The type `S` labelled `3` at its live cells of grade at most `2` and `⊥` elsewhere: proper
labels off the common face. -/
noncomputable def threeBase : StageType.{u} α 4 where
  toScheme := S
  label := CaseSplitCounterexample.labelling lab3 lab3 ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling ((isSelfVisible_natCast 3).mpr (by omega))
    ((isSelfVisible_natCast 3).mpr (by omega)) (isSelfVisible_bot 3) bot_le bot_le
  atStage d := by
    have h3 : AtStage α lab3.{u} := (atStage_natCast 3).mpr (Ordinal.natCast_lt_of_isSuccLimit hα 3)
    unfold CaseSplitCounterexample.labelling
    split_ifs <;> first | exact h3 | exact atStage_bot

/-- **The left coatom type with a proper-labelled apex**: `threeBase` with the apex added.  Its
apex row reads the cells labelled `3` at the code of `3`, strictly between `⊥` and the code of
`⊤` at which it reads the apex. -/
noncomputable def threeType : StageType.{u} α 4 :=
  (threeBase hα).addApex isLegalBelowFullGrade_S (by omega)

theorem isLegal_threeType : (threeType hα).IsLegal := StageType.isLegal_addApex _ _

/-- The type `threeType` has the face of `T5`: on the face `{0, 1, 2}` its labels are `⊥`. -/
theorem restrictFace_threeType :
    StageType.restrictFace (Coatom.face 3) (threeType hα) = some (faceT5 α) := by
  have hne : univ.map (Coatom.face 3) ≠ (univ : Finset (Fin 4)) := by decide
  rw [threeType, StageType.restrictFace_addApex (t := threeBase hα) isLegalBelowFullGrade_S
    (by omega) (Coatom.face 3) hne, ← restrictFace_T5, T5,
    StageType.restrictFace_addApex (t := T5₀ α) isLegalBelowFullGrade_S (by omega) (Coatom.face 3)
      hne]
  refine StageType.restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  change CaseSplitCounterexample.labelling lab3 lab3 ⊥ i = ⊥
  refine labelling_bot_eq_bot_of_notMem i fun h3 ↦ ?_
  obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hi (mem_coe.mpr h3)
  exact (Fin.castSucc_lt_last y).ne hy

/-- **The seed of `threeType` and `rightType`.** -/
noncomputable def seedThree : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_threeType hα) (isLegal_rightType α) (restrictFace_threeType hα)
    (restrictFace_rightType α)

/-- **The apex of `threeType` reads a cell strictly between `⊥` and itself**: the cell `{3}`,
labelled `3`. -/
theorem rowAt_threeType_three :
    ⊥ < (threeType hα).toScheme.rowAt (Fin.last _)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ∧
      (threeType hα).toScheme.rowAt (Fin.last _)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) <
      (threeType hα).toScheme.rowAt (Fin.last _) (Fin.last _) := by
  have h3 : (threeType hα).label
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = lab3 := by
    change CaseSplitCounterexample.labelling lab3 lab3 ⊥ (3 : Fin 19) = lab3
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]
  have e1 := StageType.rowAt_addApex_last (t₀ := threeBase hα) isLegalBelowFullGrade_S
    (by omega) (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
  have e2 := StageType.rowAt_addApex_last (t₀ := threeBase hα) isLegalBelowFullGrade_S
    (by omega) (Fin.last _)
  change ⊥ < ((threeBase hα).addApex isLegalBelowFullGrade_S _).toScheme.rowAt _ _ ∧
    ((threeBase hα).addApex isLegalBelowFullGrade_S _).toScheme.rowAt _ _ <
      ((threeBase hα).addApex isLegalBelowFullGrade_S _).toScheme.rowAt _ _
  rw [e1, e2]
  change ⊥ < blockEncode _ 4 ((threeType hα).label _) ∧
    blockEncode _ 4 ((threeType hα).label _) < blockEncode _ 4 ((threeType hα).label _)
  rw [h3, show (threeType hα).label (Fin.last _) = ⊤ from
    StageType.addApex_label_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega)]
  refine ⟨bot_lt_iff_ne_bot.mpr fun h ↦ natCast_label_ne_bot 3 (blockEncode_eq_bot_iff.mp h),
    blockEncode_lt_blockEncode ?_ ?_⟩
  · rw [← h3]
    exact StageType.label_mem_apexCodes (t := threeBase hα) isLegalBelowFullGrade_S
      (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)
  · exact lt_top_iff_ne_top.mpr fun h ↦ by
      rw [lab3, natCast_label] at h
      exact WithTop.coe_ne_top (WithBot.coe_injective h)

/-- **Three of the four fills at the proper-labelled apex** (the seed of `threeType` and
`rightType`, the marker the apex of `threeType`, `X` the cell `{3}` of `rightType`): the fill at `⊥`
from the left coatom (`TowerProfile.readingFillBot_left_of_left`: the apex reads the common face as
`⊥`), and both fills from the right coatom (`TowerProfile.readingFillBot_right_of_unique`,
`TowerProfile.readingFillPos_right_of_unique`).  The fill at the short positive caps from the left
coatom is not decided here. -/
theorem readingFills_seedThree :
    ReadingFillBot (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
        (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
            (StageType.faceCell (seedThree hα).restrictFace_right z)) (Fin.last 4) ∧
      ReadingFillBot (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
        (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
            (StageType.faceCell (seedThree hα).restrictFace_right z)) (Fin.castSucc (Fin.last 3)) ∧
      ReadingFillPos (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
        (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
            (StageType.faceCell (seedThree hα).restrictFace_right z))
        (Fin.castSucc (Fin.last 3)) := by
  have ha := StageType.addApex_gradedIndex_last (t := threeBase hα) isLegalBelowFullGrade_S
    (by omega)
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := seedThree hα) (a := Fin.last _) ha
    fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := threeBase hα)
      isLegalBelowFullGrade_S (by omega) hz
  have hX3 : ∀ x ∈ (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
      Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
        (StageType.faceCell (seedThree hα).restrictFace_right z)),
      (scheme (seedThree hα)).toCellScheme.grade x ≤ 3 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [mem_singleton.mp hz]
    have h2 := congrArg Prod.snd (gradedIndex_embed3 (I := seedThree hα)
      (StageType.faceCell (seedThree hα).restrictFace_right
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))))
    simp only [CellScheme.gradedIndex_snd] at h2
    refine (h2.trans (StageType.grade_faceCell _ _)).trans_le ?_
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ≤ 3
    rw [Scheme.appendFullCellScheme_grade_castSucc]
    decide
  refine ⟨readingFillBot_left_of_left ha (fun z hz ↦ ?_) (fun z hz ↦ ?_) _ fun z hz ↦ ?_,
    readingFillBot_right_of_unique hgr hrC huniq,
    readingFillPos_right_of_unique hgr hrC huniq hX3⟩
  · exact (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := threeBase hα) isLegalBelowFullGrade_S
      (by omega) z).mpr hz
  · change (threeType hα).label z = ⊥
    change Fin ((threeBase hα).card + 1) at z
    induction z using Fin.lastCases with
    | last =>
      exact absurd (Finset.eq_univ_iff_forall.mp (StageType.addApex_scope_last
        (t := threeBase hα) isLegalBelowFullGrade_S (by omega)) _) hz
    | cast d =>
      refine (StageType.addApex_label_castSucc (t := threeBase hα) isLegalBelowFullGrade_S
        (by omega) d).trans (labelling_bot_eq_bot_of_notMem d fun h3 ↦ hz ?_)
      exact (Scheme.appendFullCellScheme_scope_castSucc (S := CaseSplitCounterexample.S) (j := 4)
        (d := d)).symm ▸ h3
  · rw [mem_singleton.mp hz]
    change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]

end TopReadingApexExample

end VaughtConjecture

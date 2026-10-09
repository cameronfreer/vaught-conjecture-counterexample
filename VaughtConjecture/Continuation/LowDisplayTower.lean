/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowTowerLevel
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Extension.RowCompletionZero

/-!
# The completed display over the catalogue layer

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display as a stage
type); semantic contract, items 3, 4 and 8.

Let `I` be a seed on `m + 2` points, `L` a good level at the grade `g` and `A` a predicate on
profiles with a cutoff holding with the cutoff `⊥`, whose catalogue layer at the grade `g + 1`
lifts capped from the two coatoms, so that it is a good level (`ProfileTower.Lvl.Good.catNext`).
This file completes it to a stage type on `m + 2` points.

**Grade prefixes** (`Scheme.IsGradePrefix`).  A lower embedding of the cells of a scheme `E` into
those of `D` keeping scopes and rows, whose image contains every cell of grade at most `K`.  Rows
are read through it (`Scheme.IsGradePrefix.rowAt_eq`); it composes, and appending cells of full
scope above `K` gives one (`Scheme.IsGradePrefix.castAdd`, `Scheme.IsGradePrefix.castSucc`).

**The tower above the catalogue layer** (compiled in this repository).  The levels from the grade
`0` (`ProfileTower.lvlZero`, good up to `m`, from the level at the grade `0`,
`ProfileTower.base₀`), so the base levels need no bound `K ≥ 3`.  The canonical levels above the
catalogue layer (`ProfileTower.Lvl.iter`) are good up to `m`; the catalogue layer extends at `⊥`
from the two coatoms (`ProfileTower.Lvl.Good.hasBotExtension_catNext`), and so does every level
above (`ProfileTower.Lvl.Good.hasBotExtension_iter`), so the completion below the full grade over
the level at `m` applies also when the catalogue layer is that level (`K = m`).  The catalogue
layer is a grade prefix at `g + 1` of every level above (`ProfileTower.Lvl.isGradePrefix_iter`).

**The display** (`CompletionBelowFullGrade.display`).  Over a lawful labelling `q` at the stage
of a completed scheme, extending the glued labels: the completed scheme labelled by `q`, with the
apex added.  It is legal (`CompletionBelowFullGrade.isLegal_display`); its faces along the two
coatoms are the private context and the donor, literally, labels included
(`CompletionBelowFullGrade.restrictFace_left_display`,
`CompletionBelowFullGrade.restrictFace_right_display`); the completed scheme is a grade prefix of
it below the full grade (`CompletionBelowFullGrade.isGradePrefix_display`); and the cells of its
proper faces are the old cells of the amalgam at the same positions
(`CompletionBelowFullGrade.faceCell_display`).  Over the catalogue layer the completion is
`ProfileTower.lowCompletion`, and the catalogue layer is a grade prefix of its scheme at `g + 1`
(`ProfileTower.isGradePrefix_lowCompletion`), its old cells reached through the old cells of
the catalogue layer (`ProfileTower.lowCompletion_embed`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label CellScheme

variable {n : ℕ}

/-- A **grade prefix** of `E` in `D` at the grade `K`: a lower embedding of the cells keeping scopes
and rows whose image contains every cell of grade at most `K`. -/
structure IsGradePrefix (E D : Scheme.{u} n) (φ : Fin E.card → Fin D.card) (K : ℕ) : Prop where
  /-- The cell map is a lower embedding. -/
  lowerEmb : E.toCellScheme.IsLowerEmbedding D.toCellScheme φ
  /-- The cell map keeps scopes. -/
  scope_eq (t : Fin E.card) : D.toCellScheme.scope (φ t) = E.toCellScheme.scope t
  /-- The rows pull back to those of `E`. -/
  comap_rows : D.rows.comap lowerEmb = E.rows
  /-- Every cell of grade at most `K` is in the image. -/
  mem_range (d : Fin D.card) : D.toCellScheme.grade d ≤ K → d ∈ Set.range φ

namespace IsGradePrefix

variable {E D F : Scheme.{u} n} {φ : Fin E.card → Fin D.card} {ψ : Fin F.card → Fin E.card}
  {K : ℕ}

/-- The identity is a grade prefix. -/
protected theorem id (E : Scheme.{u} n) (K : ℕ) : IsGradePrefix E E id K :=
  ⟨IsLowerEmbedding.id _, fun _ ↦ rfl, Rows.comap_id _, fun d _ ↦ ⟨d, rfl⟩⟩

/-- Grade prefixes compose. -/
theorem comp (h : IsGradePrefix E D φ K) (h' : IsGradePrefix F E ψ K) :
    IsGradePrefix F D (φ ∘ ψ) K where
  lowerEmb := h.lowerEmb.comp h'.lowerEmb
  scope_eq t := (h.scope_eq _).trans (h'.scope_eq t)
  comap_rows := by
    change (D.rows.comap h.lowerEmb).comap h'.lowerEmb = F.rows
    rw [h.comap_rows, h'.comap_rows]
  mem_range d hd := by
    obtain ⟨e, rfl⟩ := h.mem_range d hd
    obtain ⟨f, rfl⟩ := h'.mem_range e (by rwa [h.lowerEmb.grade_eq] at hd)
    exact ⟨f, rfl⟩

/-- A grade prefix at `K` is a grade prefix at every smaller grade. -/
theorem mono (h : IsGradePrefix E D φ K) {K' : ℕ} (hK : K' ≤ K) : IsGradePrefix E D φ K' :=
  ⟨h.lowerEmb, h.scope_eq, h.comap_rows, fun d hd ↦ h.mem_range d (hd.trans hK)⟩

/-- A grade prefix keeps graded indices. -/
theorem gradedIndex_eq (h : IsGradePrefix E D φ K) (t : Fin E.card) :
    D.toCellScheme.gradedIndex (φ t) = E.toCellScheme.gradedIndex t :=
  Prod.ext (h.scope_eq t) (h.lowerEmb.grade_eq t)

/-- **Rows are read through a grade prefix.** -/
theorem rowAt_eq (h : IsGradePrefix E D φ K) (u x : Fin E.card) :
    D.rowAt (φ u) (φ x) = E.rowAt u x := by
  have hiff : φ x ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex (φ u)) ↔
      x ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, CellScheme.mem_below]
    exact h.lowerEmb.le_iff x u
  by_cases hx : x ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u)
  · rw [rowAt_of_mem (hiff.mpr hx), rowAt_of_mem hx]
    exact congrArg (fun R : E.toCellScheme.Rows ↦ R.row u ⟨x, hx⟩) h.comap_rows
  · rw [rowAt_of_notMem (mt hiff.mp hx), rowAt_of_notMem hx]

/-- **Appending cells of full scope above `K`** gives a grade prefix at `K`. -/
theorem castAdd {S : Scheme.{u} n} {k M : ℕ} {r : Fin M → Fin (S.card + M) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d} (hK : K < k) :
    IsGradePrefix S (S.appendFullCells k M r h) (Fin.castAdd M) K where
  lowerEmb := isLowerEmbedding_castAdd k M r h
  scope_eq := appendFullCellsScheme_scope_castAdd S k M
  comap_rows := comap_rows_castAdd
  mem_range d hd := by
    induction d using Fin.addCases with
    | left e => exact ⟨e, rfl⟩
    | right i =>
      have : (S.appendFullCellsScheme k M).grade (Fin.natAdd S.card i) ≤ K := hd
      rw [appendFullCellsScheme_grade_natAdd] at this
      omega

/-- **Appending one cell of full scope above `K`** gives a grade prefix at `K`. -/
theorem castSucc {S : Scheme.{u} n} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d} (hK : K < j) :
    IsGradePrefix S (S.appendFullCell j r h) Fin.castSucc K where
  lowerEmb := isLowerEmbedding_castSucc j r h
  scope_eq := appendFullCellScheme_scope_castSucc S j
  comap_rows := comap_rows_castSucc
  mem_range d hd := by
    induction d using Fin.lastCases with
    | cast e => exact ⟨e, rfl⟩
    | last =>
      have : (S.appendFullCellScheme j).grade (Fin.last _) ≤ K := hd
      rw [appendFullCellScheme_grade_last] at this
      omega

end IsGradePrefix

end VaughtConjecture.Scheme

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ}

/-! ### The levels from the grade `0` -/

variable (I : Seed.{u} α m) in
/-- **The levels from the grade `0`**: the level at the grade `0` (`ProfileTower.base₀`) and the
canonical next levels. -/
noncomputable def lvlZero : (g : ℕ) → Lvl I g
  | 0 => base₀ I
  | g + 1 => (lvlZero g).next

variable {I : Seed.{u} α m}

/-- **The levels from the grade `0` are good up to `m`.** -/
theorem lvlZero_good : ∀ g, g ≤ m → (lvlZero I g).Good
  | 0, _ => base₀_good
  | g + 1, h => (lvlZero_good g (by omega)).next h

/-! ### The canonical levels above a level -/

/-- The cells of a level among those of the canonical levels above it. -/
noncomputable def Lvl.iterEmb {g' : ℕ} (N : Lvl I g') :
    (j : ℕ) → Fin N.S.card → Fin (N.iter j).S.card
  | 0 => id
  | j + 1 => Fin.castAdd _ ∘ N.iterEmb j

/-- **A level is a grade prefix of every canonical level above it**, at its grade. -/
theorem Lvl.isGradePrefix_iter {g' : ℕ} (N : Lvl I g') :
    ∀ j, Scheme.IsGradePrefix N.S (N.iter j).S (N.iterEmb j) g'
  | 0 => Scheme.IsGradePrefix.id _ _
  | j + 1 => (Scheme.IsGradePrefix.castAdd (S := (N.iter j).S) (k := g' + j + 1)
      (M := (cat I (g' + j + 1)).card) (r := fun i ↦ (N.iter j).Φ (entry I (g' + j + 1) i))
      (h := (N.iter j).not_le) (by omega)).comp (N.isGradePrefix_iter j)

/-- The old cells of a canonical level above `N` are those of `N`. -/
theorem Lvl.iter_embed {g' : ℕ} (N : Lvl I g') :
    ∀ j d, (N.iter j).embed d = N.iterEmb j (N.embed d)
  | 0, _ => rfl
  | j + 1, d => congrArg (Fin.castAdd _) (N.iter_embed j d)

/-- **The canonical levels above a level extending at `⊥` extend at `⊥`.** -/
theorem Lvl.Good.hasBotExtension_iter {g' : ℕ} {N : Lvl I g'} (hN : N.Good)
    (hB : N.HasBotExtension) : ∀ j, g' + j ≤ m → (N.iter j).HasBotExtension
  | 0, _ => hB
  | j + 1, h => (hN.iter j (by omega)).hasBotExtension_next

/-! ### The catalogue layer extends at `⊥` -/

variable {g : ℕ} {L : Lvl I g} {A : CProf I → Prop}

local notation "𝒞" => predCat I (g + 1) A

/-- **The catalogue layer over a good level extends at `⊥`** from the two coatoms at the grade
`g + 1`, when `A` holds with the cutoff `⊥`: the old labels at the grade `g + 1` are lawful on the
cut, and their orbit code with the cutoff `⊥` lies in the catalogue
(`ProfileTower.Lvl.Good.exists_extension_cat_bot`). -/
theorem Lvl.Good.hasBotExtension_catNext (hL : L.Good) (hA0 : ∀ W : Prof I, A (withCut W ⊥)) :
    (L.catNext A).HasBotExtension := by
  classical
  change ∀ w : Fin (L.catS 𝒞).card → Label.{u},
    (L.catS 𝒞).rows.IsLawfulBelow (coatC, g + 1) (fun z ↦ w z) →
    (L.catS 𝒞).rows.IsLawfulBelow (coatD, g + 1) (fun z ↦ w z) →
    ∃ r : (L.catS 𝒞).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (L.catS 𝒞).rows.IsLawfulBelow (univ, g + 1) r ∧
        ∀ z, (L.catS 𝒞).toCellScheme.scope z.1 ≠ univ → r z = w z
  intro w hwC hwD
  have hCsub : ∀ P ∈ 𝒞, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) := fun P hP ↦ ⟨(mem_predCat.mp hP).1, (mem_predCat.mp hP).2.1⟩
  set W : Prof I := fun d ↦
    if I.amalgam.toCellScheme.grade d ≤ g + 1 then w (Fin.castAdd _ (L.embed d)) else ⊥ with hW
  have hWc (x : Fin (m + 2))
      (hw : (L.catS 𝒞).rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ w z) :
      I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ W d := by
    have h1 := (L.isLawfulBelow_catS_iff (C := 𝒞) (X := (univ.erase x, g + 1))
      (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1))).mp hw
    have h2 := (hL.isLawfulBelow_old_iff (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp h1
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase x, g + 1))
      fun d hd ↦ (show W d = _ from ite_eq_left hd.2).symm).mp h2
  have hWcut : IsCutLawful I (g + 1) W := ⟨hWc _ hwC, hWc _ hwD⟩
  obtain ⟨q, hq, hqW⟩ := hL.exists_extension_cat_bot hCsub (W := W)
    (mem_predCat_of hWcut (Finset.mem_insert_self _ _) (hA0 _))
  refine ⟨q, hq, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, hdz⟩ := hL.exists_old_catS z.2 hz
  obtain ⟨z, hzm⟩ := z
  subst hdz
  exact (hqW d hd).trans (ite_eq_left hd)

end VaughtConjecture.ProfileTower

/-! ### The completed scheme with a labelling and the apex -/

namespace VaughtConjecture.CompletionBelowFullGrade

open Finset Label StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  {q : Fin F.scheme.card → Label.{u}} (hq : F.scheme.rows.IsLawful q) (hqα : ∀ d, AtStage α (q d))

/-- **The display of a completion below the full grade** over a lawful labelling `q` at the stage:
the completed scheme labelled by `q`, with the apex added. -/
noncomputable def display : StageType.{u} α (m + 2) :=
  (F.withLabel hq hqα).addApex F.isLegalBelowFullGrade (Nat.succ_pos _)

/-- **The display is legal.** -/
theorem isLegal_display : (F.display hq hqα).IsLegal := StageType.isLegal_addApex _ _

/-- The labels of the display are `q` on the completed scheme. -/
theorem display_label_castSucc (d : Fin F.scheme.card) :
    (F.display hq hqα).label (Fin.castSucc d) = q d :=
  StageType.addApex_label_castSucc (t := F.withLabel hq hqα) F.isLegalBelowFullGrade
    (Nat.succ_pos _) d

/-- **The completed scheme is a grade prefix of the display** at every grade below `m + 2`. -/
theorem isGradePrefix_display {K : ℕ} (hK : K < m + 2) :
    Scheme.IsGradePrefix F.scheme (F.display hq hqα).toScheme Fin.castSucc K :=
  Scheme.IsGradePrefix.castSucc (h := F.isLegalBelowFullGrade.not_le) hK

variable {hq hqα}

/-- **The faces of the display along a proper face are those of the amalgam**, when `q` extends
the glued labels. -/
theorem restrictFace_display (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) {k : ℕ}
    (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ) :
    restrictFace f (F.display hq hqα) = restrictFace f I.amalgam :=
  (StageType.restrictFace_addApex _ _ _ hf).trans (F.restrictFace_withLabel hq hqα hqe f hf)

/-- **The private face of the display is the first coatom type**, literally. -/
theorem restrictFace_left_display (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) :
    restrictFace Fin.castSuccEmb (F.display hq hqα) = some I.left :=
  (F.restrictFace_display hqe _ Coatom.univ_map_left_ne).trans I.restrictFace_left

/-- **The donor face of the display is the second coatom type**, literally. -/
theorem restrictFace_right_display (hqe : ∀ d, q (F.embed d) = I.amalgam.label d) :
    restrictFace (extendByLast Fin.castSuccEmb) (F.display hq hqα) = some I.right :=
  (F.restrictFace_display hqe _ Coatom.univ_map_right_ne).trans I.restrictFace_right

/-- **The cells of a proper face of the display are the old cells** of the amalgam at the same
positions. -/
theorem faceCell_display {k : ℕ} {f : Fin k ↪ Fin (m + 2)} (hf : univ.map f ≠ univ)
    {t : StageType.{u} α k} (h : restrictFace f (F.display hq hqα) = some t)
    (h' : restrictFace f I.amalgam = some t) (i : Fin t.card) :
    faceCell h i = Fin.castSucc (F.embed (faceCell h' i)) := by
  have hmono : StrictMono (Fin.castSucc ∘ F.embed) :=
    Fin.strictMono_castSucc.comp F.embed.strictMono
  have hscope (d : Fin I.amalgam.card) : (F.display hq hqα).toCellScheme.scope
      ((Fin.castSucc ∘ F.embed) d) = I.amalgam.toCellScheme.scope d :=
    (Scheme.appendFullCellScheme_scope_castSucc _ _ _).trans (F.scope_embed d)
  have hvis (z : Fin (F.display hq hqα).card)
      (hz : ((F.display hq hqα).toCellScheme.scope z : Set (Fin (m + 2))) ⊆ Set.range f) :
      z ∈ Set.range (Fin.castSucc ∘ F.embed) := by
    have hne : (F.display hq hqα).toCellScheme.scope z ≠ univ := fun he ↦ hf
      (eq_univ_of_forall fun x ↦ by
        obtain ⟨y, rfl⟩ : x ∈ Set.range f := hz (mem_coe.mpr (he.symm ▸ mem_univ x))
        exact mem_map_of_mem _ (mem_univ y))
    induction z using Fin.lastCases with
    | last => exact absurd (Scheme.appendFullCellScheme_scope_last _ _) hne
    | cast z =>
      rw [show (F.display hq hqα).toCellScheme.scope (Fin.castSucc z) =
        F.scheme.toCellScheme.scope z from Scheme.appendFullCellScheme_scope_castSucc _ _ _]
        at hne
      obtain ⟨d, rfl⟩ := F.mem_range_embed z hne
      exact ⟨d, rfl⟩
  exact Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme)
    (T := (F.display hq hqα).toScheme) (φ := Fin.castSucc ∘ F.embed) f hmono hscope hvis rfl

end VaughtConjecture.CompletionBelowFullGrade

/-! ### The completion over the catalogue layer -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {g j : ℕ} {I : Seed.{u} α (g + 1 + j)} {L : Lvl I g}
  {A : CProf I → Prop}

local notation "𝒞" => predCat I (g + 1) A

/-- **The completion over the catalogue layer**: the completion below the full grade
(`ProfileTower.Lvl.Good.completion`) over the level at the grade `m = g + 1 + j`, the `j`-th
canonical level above the catalogue layer of a good level, when the catalogue layer is a good
level and `A` holds with the cutoff `⊥`. -/
noncomputable def lowCompletion (hL : L.Good) (hN : (L.catNext A).Good)
    (hA0 : ∀ W : Prof I, A (withCut W ⊥)) : CompletionBelowFullGrade I :=
  (hN.iter j le_rfl).completion
    (hN.hasBotExtension_iter (hL.hasBotExtension_catNext hA0) j le_rfl) (by omega)

variable (hL : L.Good) (hN : (L.catNext A).Good) (hA0 : ∀ W : Prof I, A (withCut W ⊥))

/-- The completed scheme over the catalogue layer is the top layer over the level at `m`. -/
theorem lowCompletion_scheme : (lowCompletion hL hN hA0).scheme = ((L.catNext A).iter j).top :=
  rfl

variable (A j) in
/-- The cells of the catalogue layer among those of the completed scheme. -/
noncomputable def lowCellMap (L : Lvl I g) :
    Fin (L.catS 𝒞).card → Fin ((L.catNext A).iter j).top.card :=
  Fin.castAdd _ ∘ (L.catNext A).iterEmb j

/-- **The catalogue layer is a grade prefix of the completed scheme** at the grade `g + 1`. -/
theorem isGradePrefix_lowCompletion :
    Scheme.IsGradePrefix (L.catS 𝒞) (lowCompletion hL hN hA0).scheme (lowCellMap j A L) (g + 1) :=
  (Scheme.IsGradePrefix.castAdd (S := ((L.catNext A).iter j).S) (k := g + 1 + j + 1)
    (M := (((L.catNext A).iter j).S.catalogue (g + 1 + j + 1)).card)
    (r := fun i ↦ ((L.catNext A).iter j).S.fieldRow (g + 1 + j + 1)
      (((L.catNext A).iter j).S.catalogueEntry (g + 1 + j + 1) i))
    (h := ((L.catNext A).iter j).not_le) (by omega)).comp ((L.catNext A).isGradePrefix_iter j)

/-- The old cells of the completed scheme are the old cells of the catalogue layer. -/
theorem lowCompletion_embed (d : Fin I.amalgam.card) :
    (lowCompletion hL hN hA0).embed d = lowCellMap j A L (Fin.castAdd _ (L.embed d)) :=
  congrArg (Fin.castAdd _) ((L.catNext A).iter_embed j d)

end VaughtConjecture.ProfileTower

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapAdmittedEngine
import VaughtConjecture.Continuation.SourceGapLowProvision
import VaughtConjecture.Continuation.SourceGapTwistedEntry

/-!
# The LOW-admitted completion at the twisted seed

Roadmap, Layer 3 ((R2) of the table of 3.4; 3.1, (R6), the completion below the full grade with a
restricted catalogue at the reading grades).  The go/no-go test of bountifulness (B3) at the seed
of the input `SeparationObstruction.T α` with the twisted donor `TwistedDonor.Utop` (labels
`(⊤, ⊥, ⊤, ⊤, v)`), the smallest donor other than the context whose new top `o'` is not forced by a
root top.  The amalgam of that seed has the scheme of the amalgam of the input with itself
(`TwistedDonor.amalgam_seedU`), so the completion is built over the doubled lower layer of the input
with itself (`MixedSeed.lowerT`: the copies of `z` at the grade `1`), with the field layer at the
grade `2` restricted to the entries satisfying the LOW admission (`MixedSeed.AdmU`: the partner the
owner `o`; the designated tops `z'`, `o'`; the designated cells below the top `e'`, `r'`).

* **Gluing** (`MixedSeed.exists_glue_lowerT`): two lawful labellings of the input with one root
  value glue to a lawful labelling of the lower layer.
* **The lift provisions on the lower layer** (`MixedSeed.botProvision_left`,
  `MixedSeed.botProvision_right`, `MixedSeed.capProvision_left`, `MixedSeed.capProvision_right`):
  the provisions of `VaughtConjecture.Continuation.SourceGapLowProvision` on the two copies, glued,
  with the admission passing to the orbit code (`MixedSeed.admU_code`, through
  `MixedSeed.lowVia_comp`).
* **Bountifulness and legality** (`MixedSeed.cappedLift_admittedT_left`,
  `MixedSeed.cappedLift_admittedT_right`, `MixedSeed.isBountiful_admittedT`,
  `MixedSeed.isLegalBelowFullGrade_admittedT`): through the lift into an admitted field layer and
  the assembly over the doubled lower layer of
  `VaughtConjecture.Continuation.SourceGapAdmittedEngine`.  **The LOW-admitted completion at the
  twisted seed is legal below the full grade.**
* **The labels of the twisted seed** (`MixedSeed.exists_isLawful_admittedT`): the input on the
  context copy and the twisted donor on the donor copy extend to a labelling of the LOW-admitted
  completion lawful below `(univ, 2)`.
* **Determination of `o'`** (`MixedSeed.eq_top_of_admittedT`): in every labelling of the
  LOW-admitted completion lawful below `(univ, 2)` with `o` at `⊤` and `r'` below `⊤`, `o'` is `⊤`;
  by recognition at a reader (`Scheme.exists_admitted_image`).  The full-catalogue completion fails
  this (`TwistedDonor.not_forall_lowAdmitted`).

**For an admission.**  The construction and its legality use of the admission only that it holds
at `⊥` and at the labels of the input on both faces, passes to images under monotone maps, and has
the lift provisions from both coatoms at every cap (`MixedSeed.IsLowAdmission`); the completion
`MixedSeed.admittedBy α Adm` is legal below the full grade for every admission
(`MixedSeed.isLegalBelowFullGrade_admittedBy`), and `MixedSeed.admittedT α` is the case of the
owner-as-partner clause (`MixedSeed.isLowAdmission_lowVia`).  **The self seed**: the clause
`SeparationObstruction.LowViaSelf` (the designated tops `z'`, `o'`, `r'`; the designated cell below
the top `e'`) is an admission (`MixedSeed.isLowAdmission_lowViaSelf`), and in its completion `o` at
`⊤` puts `z'`, `o'`, `r'` at `⊤` (`MixedSeed.eq_top_of_admittedSelf`).

Not here: the apex and the truncation to the stage (the stage type with the faces `T` and the
twisted donor), and the passage from the scheme of the input with itself to that of the twisted
seed for `CompletionBelowFullGrade` (the schemes are equal, `TwistedDonor.amalgam_seedU`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label CellScheme

/-- **Recognition at a reader**: in a labelling `q` lawful below `(univ, k)` of an admitted field
layer at the grade `k`, over a scheme whose cells have grade at most `k`, if an old cell of grade
`k` is at `⊤`, then `q` on the old cells is the image of an admitted catalogue entry under a
monotone map fixing `⊥` (availability gives a new cell at `⊤`, whose row reads an admitted entry;
locality there, at `⊤`, has its suppressor `⊤` up to the grade `k`). -/
theorem exists_admitted_image {n k : ℕ} {S : Scheme.{u} n} {A : (Fin S.card → Label.{u}) → Prop}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}
    (hA0 : A fun _ ↦ ⊥) (hgr : ∀ d, S.toCellScheme.grade d ≤ k)
    {q : Fin (S.admittedFieldLayer k A hS).card → Label.{u}}
    (hq : (S.admittedFieldLayer k A hS).rows.IsLawfulBelow ((univ : Finset (Fin n)), k)
      (fun x ↦ q x))
    {x₀ : Fin S.card} (hx₀ : S.toCellScheme.grade x₀ = k) (hqx : q (Fin.castAdd _ x₀) = ⊤) :
    ∃ a, S.rows.IsLawful a ∧ A a ∧ ∃ σ : Label.{u} → Label.{u}, Monotone σ ∧ σ ⊥ = ⊥ ∧
      (∀ x, σ (visibilityReplace k k x) = visibilityReplace k k (σ x)) ∧
      ∀ e, q (Fin.castAdd _ e) = σ (a e) := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  obtain ⟨t, ht⟩ := exists_gradedIndex_eq_admittedFieldLayer (hS := hS) hA0
  obtain ⟨u, hu, hle⟩ := havail (Fin.castAdd _ x₀) t ((mem_below _).mpr ht.le)
    (by rw [show (S.admittedFieldLayer k A hS).toCellScheme.scope t = univ from
          congrArg Prod.fst ht]
        exact subset_univ _)
    (by rw [show (S.admittedFieldLayer k A hS).toCellScheme.grade t = k from
          congrArg Prod.snd ht, appendFullCellsScheme_grade_castAdd, hx₀])
  rw [hqx, top_le_iff] at hle
  rw [ht] at hu
  obtain ⟨a, ha, hA, hrow⟩ := exists_admitted_row_admittedFieldLayer hu
  obtain ⟨g, σ, hw, he⟩ := hloc u ((mem_below _).mpr hu.le)
  have hgk : g k = ⊤ := by
    have h := he ⟨u, mem_below_gradedIndex _ u⟩
    simp only [hle, min_self] at h
    have h2 : (S.admittedFieldLayer k A hS).toCellScheme.grade u = k := congrArg Prod.snd hu
    rw [h2] at h
    exact top_le_iff.mp (h ▸ min_le_right _ _)
  refine ⟨a, (mem_catalogue.mp ha).1, hA, σ, hw.monotone, hw.map_bot,
    fun x ↦ hw.visibilityReplace_comm x k (by rw [hgk]; exact le_top) k le_rfl, fun e ↦ ?_⟩
  have hd : Fin.castAdd _ e ∈ (S.admittedFieldLayer k A hS).toCellScheme.below
      ((S.admittedFieldLayer k A hS).toCellScheme.gradedIndex u) := by
    refine (mem_below _).mpr ?_
    rw [hu, appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, hgr e⟩
  have h := he ⟨_, hd⟩
  change min (q (Fin.castAdd _ e)) (q u) =
    min (σ ((S.admittedFieldLayer k A hS).rows.row u ⟨_, hd⟩)) _ at h
  rw [hle, min_top_right] at h
  rw [h, hrow e hd]
  have hge : (S.admittedFieldLayer k A hS).toCellScheme.grade (Fin.castAdd _ e) ≤ k := by
    rw [appendFullCellsScheme_grade_castAdd]; exact hgr e
  have hg' : g ((S.admittedFieldLayer k A hS).toCellScheme.grade (Fin.castAdd _ e)) = ⊤ :=
    top_le_iff.mp (by rw [← hgk]; exact hw.antitone hge)
  exact min_eq_left (le_of_le_of_eq le_top hg'.symm)

end VaughtConjecture.Scheme

namespace VaughtConjecture.MixedSeed

open Finset Label CellScheme StageType SeparationObstruction

variable {α : Ordinal.{u}}

variable (α) in
/-- **The lower layer**: the doubled lower layer of the seed of the input with itself (the copies at
grade `1` of the cell `z`), over the amalgam, whose scheme is also that of the twisted seed. -/
noncomputable abbrev lowerT : Scheme.{u} 3 := (I α).doubledLower (hLR α)

/-- The context copy of a labelling of the lower layer. -/
noncomputable def privT (e : Fin (lowerT α).card → Label.{u}) (z : Fin 5) : Label.{u} :=
  e (Fin.castAdd _ (lc α z))

/-- The donor copy of a labelling of the lower layer. -/
noncomputable def donT (e : Fin (lowerT α).card → Label.{u}) (z : Fin 5) : Label.{u} :=
  e (Fin.castAdd _ (rc α z))

/-! ### Lawful labellings of the input at the grades at most `1` -/

/-- Two lawful labellings of the input with one root value agree at the cells of grade at most
`1`. -/
theorem eq_of_grade_le_one {sL sR : Fin 5 → Label.{u}} (hL : S.{u}.rows.IsLawful sL)
    (hR : S.{u}.rows.IsLawful sR) (hy : sL 0 = sR 0) {c : Fin 5} (hc : cells.grade c ≤ 1) :
    sL c = sR c := by
  obtain ⟨hLe, -, -⟩ := eq_lab_of_isLawful hL
  obtain ⟨hRe, -, -⟩ := eq_lab_of_isLawful hR
  have key : ∀ c : Fin 5, cells.grade c ≤ 1 → c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases key c hc with rfl | rfl | rfl
  · exact hy
  · rw [hLe, hRe]; rfl
  · rw [hLe, hRe]; exact hy

/-- The cell of full scope and grade `1` of the input is `z`. -/
theorem fullCell_one (i : Fin ((I α).nFull 1)) : (I α).left.toScheme.fullCell 1 i = cellT α 2 := by
  have h := Scheme.gradedIndex_fullCell (T := (I α).left.toScheme) 1 i
  generalize (I α).left.toScheme.fullCell 1 i = c at h ⊢
  have key : ∀ c : Fin 5, cells.gradedIndex c = ((univ : Finset (Fin 2)), 1) → c = 2 := by decide
  exact key c h

/-- There is a copy of `z` at grade `1`. -/
theorem exists_nFull_one : Nonempty (Fin ((I α).nFull 1)) := by
  obtain ⟨i, -⟩ := Scheme.exists_fullCell_eq (T := (I α).left.toScheme) (j := 1) (c := cellT α 2)
    (show cells.gradedIndex 2 = ((univ : Finset (Fin 2)), 1) by decide)
  exact ⟨i⟩

/-! ### Gluing on the lower layer -/

/-- **Gluing two lawful labellings of the input on the lower layer**: with one root value, they
glue to a lawful labelling of the lower layer, reading them on the context and donor copies and the
root value at the copies of `z`. -/
theorem exists_glue_lowerT {sL sR : Fin 5 → Label.{u}} (hL : S.{u}.rows.IsLawful sL)
    (hR : S.{u}.rows.IsLawful sR) (hy : sL 0 = sR 0) :
    ∃ g : Fin (lowerT α).card → Label.{u}, (lowerT α).rows.IsLawful g ∧
      privT g = sL ∧ donT g = sR ∧ ∀ i, g (Fin.natAdd _ i) = sL 0 := by
  obtain ⟨w, hw, hwL, hwR⟩ := (I α).exists_isLawful_glue (hLR α) (sL := sL) (sR := sR) hL hR (by
    change ∀ z : Fin 5, Fin.last 1 ∉ cells.scope z → sL z = sR z
    intro z hz
    have h0 : z = 0 := by revert hz; fin_cases z <;> decide
    subst h0
    exact hy)
  have hD := (I α).isDoubling_doubledLower (hLR α)
  -- the pullback of `sL` along the cell map of the lower layer
  have hQ : (lowerT α).rows.IsLawful (sL ∘ (I α).lowerCell (hLR α)) :=
    hD.isLawful_comp (w := sL) hL
  set v : Fin (lowerT α).card → Label.{u} := Fin.append w fun _ ↦ sL 0 with hv
  have hz : sL 2 = sL 0 := by
    obtain ⟨hLe, -, -⟩ := eq_lab_of_isLawful hL
    rw [hLe]; rfl
  -- at the cells of grade at most `1`, `v` is the pullback
  have hvQ (t : Fin (lowerT α).card) (ht : (lowerT α).toCellScheme.grade t ≤ 1) :
      v t = sL ((I α).lowerCell (hLR α) t) := by
    induction t using Fin.addCases with
    | right j =>
      rw [hv, Fin.append_right, Seed.lowerCell, Fin.append_right, fullCell_one]
      exact hz.symm
    | left d =>
      rw [hv, Fin.append_left, Seed.lowerCell, Fin.append_left]
      have hgd : cells.grade ((I α).doublingCell (hLR α) d) ≤ 1 := by
        have := (hD.grade_eq (Fin.castAdd _ d))
        rw [Seed.lowerCell, Fin.append_left] at this
        change cells.grade _ = _ at this
        rw [this]; exact ht
      rcases (I α).eq_faceCell_or (hLR α) d with he | he
      · rw [← he, hwL, (I α).doublingCell_faceCell_left]
      · rw [← he, hwR, (I α).doublingCell_faceCell_right]
        exact (eq_of_grade_le_one hL hR hy hgd).symm
  have hvN (i : Fin ((I α).nFull 1)) : v (Fin.natAdd _ i) = sL 0 := by
    rw [hv, Fin.append_right]
  obtain ⟨i₀⟩ := exists_nFull_one (α := α)
  refine ⟨v, Scheme.isLawful_appendFullCells (h := (I α).not_univ_le 1) ?_ (fun i ↦ ?_)
    (fun i ↦ ?_) (fun s hs ↦ ⟨i₀, ?_⟩), ?_, ?_, hvN⟩
  · convert hw using 1
    funext d
    exact Fin.append_left _ _ d
  · rw [hvN]
    exact hL.orderly 0
  · have h := hQ.locality (Fin.natAdd _ i)
    rw [Scheme.appendFullCells_row_natAdd_eq (h := (I α).not_univ_le 1)] at h
    convert h using 1
    funext t
    have ht : (lowerT α).toCellScheme.grade t.1 ≤ 1 :=
      t.2.2.trans (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)).le
    rw [hvQ t.1 ht, hvQ _ (by rw [Scheme.appendFullCellsScheme_grade_natAdd])]
    rfl
  · rw [hvN]
    rw [hvQ s hs.le]
    have hgs : cells.grade ((I α).lowerCell (hLR α) s) = 1 := (hD.grade_eq s).trans hs
    generalize (I α).lowerCell (hLR α) s = c at hgs ⊢
    obtain ⟨hLe, -, -⟩ := eq_lab_of_isLawful hL
    have key : ∀ c : Fin 5, cells.grade c = 1 → c = 0 ∨ c = 1 ∨ c = 2 := by decide
    rcases key c hgs with rfl | rfl | rfl
    · exact le_rfl
    · rw [hLe]; exact bot_le
    · rw [hz]
  · funext z
    exact (Fin.append_left _ _ _).trans (hwL z)
  · funext z
    exact (Fin.append_left _ _ _).trans (hwR z)

/-! ### The coatom pairs and the cells below them -/

/-- The context coatom pair at the grade `2`. -/
abbrev pairL : Finset (Fin 3) × ℕ := (univ.erase (Fin.last 2), 2)

/-- The donor coatom pair at the grade `2`. -/
abbrev pairR : Finset (Fin 3) × ℕ := (univ.erase (Fin.castSucc (Fin.last 1)), 2)

private theorem not_univ_one_le_erase {x : Fin 3} {g : ℕ} :
    ¬ ((univ : Finset (Fin 3)), 1) ≤ (univ.erase x, g) :=
  fun h ↦ Finset.notMem_erase x univ (h.1 (mem_univ x))

/-- **The context copy of a labelling lawful below the context coatom is lawful on the input.** -/
theorem isLawful_privT {f : Fin (lowerT α).card → Label.{u}}
    (hf : (lowerT α).rows.IsLawfulBelow pairL (fun d ↦ f d)) : S.{u}.rows.IsLawful (privT f) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := (I α).amalgam.toScheme) (k := 1)
    (M := (I α).nFull 1) (r := (I α).lowerRow (hLR α)) (h := (I α).not_univ_le 1)
    not_univ_one_le_erase).mp hf
  have hpair : (pairL : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.left 1)) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, Coatom.univ_map_left]
  have h2 := (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace (I α).restrictFace_left) (univ, 2)
      (fun d ↦ f (Fin.castAdd _ d))).mpr (by rw [← hpair]; exact h1)
  exact h2.isLawful fun d ↦ ⟨subset_univ _, (T α).grade_le d⟩

/-- **The donor copy of a labelling lawful below the donor coatom is lawful on the input.** -/
theorem isLawful_donT {f : Fin (lowerT α).card → Label.{u}}
    (hf : (lowerT α).rows.IsLawfulBelow pairR (fun d ↦ f d)) : S.{u}.rows.IsLawful (donT f) := by
  have h1 := (Scheme.isLawfulBelow_appendFullCells_iff (S := (I α).amalgam.toScheme) (k := 1)
    (M := (I α).nFull 1) (r := (I α).lowerRow (hLR α)) (h := (I α).not_univ_le 1)
    not_univ_one_le_erase).mp hf
  have hpair : (pairR : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.right 1)) id ((univ : Finset (Fin 2)), 2) := by
    simp only [Prod.map, id, Coatom.univ_map_right]
  have h2 := (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace ((I α).restrictFace_right_left (hLR α))) (univ, 2)
      (fun d ↦ f (Fin.castAdd _ d))).mpr (by rw [← hpair]; exact h1)
  exact h2.isLawful fun d ↦ ⟨subset_univ _, (T α).grade_le d⟩

/-- A cell below the context coatom pair is a context copy. -/
theorem exists_left_of_mem_below {d : Fin (lowerT α).card}
    (hd : d ∈ (lowerT α).toCellScheme.below pairL) : ∃ z : Fin 5, d = Fin.castAdd _ (lc α z) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hd.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ (Fin.last 2)))
  | left e =>
    have h : (I α).amalgam.toCellScheme.scope e ⊆ univ.map (Coatom.left 1) := by
      have h' := hd.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [Coatom.univ_map_left]
      exact h'
    exact ⟨(I α).doublingCell (hLR α) e, congrArg _ ((I α).faceCell_left_of_subset (hLR α) h).symm⟩

/-- A cell below the donor coatom pair is a donor copy. -/
theorem exists_right_of_mem_below {d : Fin (lowerT α).card}
    (hd : d ∈ (lowerT α).toCellScheme.below pairR) : ∃ z : Fin 5, d = Fin.castAdd _ (rc α z) := by
  induction d using Fin.addCases with
  | right i =>
    exfalso
    have h := hd.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact Finset.notMem_erase _ univ (h (mem_univ _))
  | left e =>
    have h : (I α).amalgam.toCellScheme.scope e ⊆ univ.map (Coatom.right 1) := by
      have h' := hd.1
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at h'
      rw [Coatom.univ_map_right]
      exact h'
    exact ⟨(I α).doublingCell (hLR α) e, congrArg _ ((I α).faceCell_right_of_subset (hLR α) h).symm⟩

/-- The context copies lie below the context coatom pair. -/
theorem left_mem_below (z : Fin 5) :
    Fin.castAdd _ (lc α z) ∈ (lowerT α).toCellScheme.below pairL := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd, gradedIndex_lc]
  refine ⟨?_, (T α).grade_le z⟩
  exact (map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_left (m := 1)).subset

/-- The donor copies lie below the donor coatom pair. -/
theorem right_mem_below (z : Fin 5) :
    Fin.castAdd _ (rc α z) ∈ (lowerT α).toCellScheme.below pairR := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd, gradedIndex_rc]
  refine ⟨?_, (T α).grade_le z⟩
  exact (map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_right (m := 1)).subset

/-! ### The copies of `z`, and the lifts of the lower layer at the grade `1` -/

theorem grade_pos_lowerT (d : Fin (lowerT α).card) : 0 < (lowerT α).toCellScheme.grade d :=
  (((I α).isWellFormed_doubledLower (hLR α)).isWellFormed.gradedIndex_mem d).2.1

theorem exists_full_lowerT : ∃ a : Fin (lowerT α).card,
    (lowerT α).toCellScheme.gradedIndex a = ((univ : Finset (Fin 3)), 1) := by
  obtain ⟨i₀⟩ := exists_nFull_one (α := α)
  exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

/-- **A lawful labelling of the lower layer takes the root value at the copies of `z`**: the copies
of `z` and the context copy of `z` lie over one cell of the input (symmetry below `(univ, 1)`), and
`z` is `y` on the input. -/
theorem natAdd_eq_privT {a : Fin (lowerT α).card → Label.{u}} (ha : (lowerT α).rows.IsLawful a)
    (i : Fin ((I α).nFull 1)) : a (Fin.natAdd _ i) = privT a 0 := by
  have hD := (I α).isDoubling_doubledLower (hLR α)
  have hmem2 : Fin.castAdd ((I α).nFull 1) (lc α 2) ∈
      (lowerT α).toCellScheme.below ((univ : Finset (Fin 3)), 1) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd, gradedIndex_lc]
    exact ⟨subset_univ _, le_rfl⟩
  have hmemN : Fin.natAdd (I α).amalgam.card i ∈
      (lowerT α).toCellScheme.below ((univ : Finset (Fin 3)), 1) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]
  have h := hD.eq_of_isLawfulBelow (ha.isLawfulBelow ((univ : Finset (Fin 3)), 1))
    (fun d hd ↦ by
      obtain ⟨c, hc⟩ := exists_full_lowerT (α := α)
      exact ⟨c, hc.trans (Prod.ext rfl (le_antisymm hd.2 (grade_pos_lowerT d)).symm)⟩)
    hmemN hmem2 (by
      rw [Seed.lowerCell, Fin.append_right, Fin.append_left, fullCell_one]
      exact ((I α).doublingCell_faceCell_left (hLR α) (cellT α 2)).symm)
  rw [h]
  obtain ⟨hpe, -, -⟩ := eq_lab_of_isLawful (isLawful_privT (ha.isLawfulBelow pairL))
  exact congrFun hpe 2

/-- **The lift of the lower layer at the grade `1` from the context coatom**, by the symmetric
fill. -/
theorem cappedLift_lowerT_left : (lowerT α).rows.CappedLift (X := (univ.erase (Fin.last 2), 1))
    (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  have hL := (I α).restrictFace_left
  have h := ((I α).isDoubling_doubledLower (hLR α)).cappedLift_coatom (f := Coatom.left 1)
    Seed.collapseLast_left (cp := fun z ↦ Fin.castAdd _ (StageType.faceCell hL z))
    (fun z ↦ by rw [Seed.lowerCell, Fin.append_left, (I α).doublingCell_faceCell_left])
    (fun z ↦ by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact Prod.ext (StageType.scope_faceCell hL z) (StageType.grade_faceCell hL z))
    (fun d hd ↦ by
      induction d using Fin.addCases with
      | right i =>
        rw [Scheme.appendFullCellsScheme_scope_natAdd] at hd
        exact absurd (subset_antisymm (subset_univ _) hd) Coatom.univ_map_left_ne
      | left e =>
        rw [Scheme.appendFullCellsScheme_scope_castAdd] at hd
        simp only
        rw [Seed.lowerCell, Fin.append_left, (I α).faceCell_left_of_subset (hLR α) hd])
    (j := 1) (fun i hi hij ↦ by
      obtain ⟨c, hc⟩ := exists_full_lowerT (α := α)
      exact ⟨c, hc.trans (by rw [le_antisymm hij hi])⟩) grade_pos_lowerT
  rw [Coatom.univ_map_left] at h
  exact h

/-- **The lift of the lower layer at the grade `1` from the donor coatom.** -/
theorem cappedLift_lowerT_right :
    (lowerT α).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  have hR := (I α).restrictFace_right_left (hLR α)
  have h := ((I α).isDoubling_doubledLower (hLR α)).cappedLift_coatom (f := Coatom.right 1)
    Seed.collapseLast_right (cp := fun z ↦ Fin.castAdd _ (StageType.faceCell hR z))
    (fun z ↦ by rw [Seed.lowerCell, Fin.append_left, (I α).doublingCell_faceCell_right])
    (fun z ↦ by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
      exact Prod.ext (StageType.scope_faceCell hR z) (StageType.grade_faceCell hR z))
    (fun d hd ↦ by
      induction d using Fin.addCases with
      | right i =>
        rw [Scheme.appendFullCellsScheme_scope_natAdd] at hd
        exact absurd (subset_antisymm (subset_univ _) hd) Coatom.univ_map_right_ne
      | left e =>
        rw [Scheme.appendFullCellsScheme_scope_castAdd] at hd
        simp only
        rw [Seed.lowerCell, Fin.append_left, (I α).faceCell_right_of_subset (hLR α) hd])
    (j := 1) (fun i hi hij ↦ by
      obtain ⟨c, hc⟩ := exists_full_lowerT (α := α)
      exact ⟨c, hc.trans (by rw [le_antisymm hij hi])⟩) grade_pos_lowerT
  rw [Coatom.univ_map_right] at h
  exact h

/-! ### Admissions of states on the lower layer -/

/-- **An admission of states at the seed of the input with itself**: a relation `Adm L R` between
labellings of the context face `L` and of the donor face `R`, holding at `⊥` and at the labels of
the input on both faces, passing to images under monotone maps, with **the lift provisions from
both coatoms at every cap** self-visible at `2` (`⊥` included): from an admitted state of lawful
faces sharing `y` and a lawful face agreeing with one of them capped at `h`, a lawful other face
with the same root, agreeing with the other face of the state capped at `h` and admitted with it.
The owner-as-partner clause `SeparationObstruction.LowVia` (`MixedSeed.isLowAdmission_lowVia`) and
its self-seed form `SeparationObstruction.LowViaSelf` (`MixedSeed.isLowAdmission_lowViaSelf`) are
admissions. -/
structure IsLowAdmission (Adm : (Fin 5 → Label.{u}) → (Fin 5 → Label.{u}) → Prop) : Prop where
  bot : Adm (fun _ ↦ ⊥) (fun _ ↦ ⊥)
  top : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ ⊤)
  comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ0 : σ ⊥ = ⊥)
    (hc : ∀ x, σ (visibilityReplace 2 2 x) = visibilityReplace 2 2 (σ x))
    {L R : Fin 5 → Label.{u}} (h : Adm L R) :
    Adm (fun z ↦ σ (L z)) (fun z ↦ σ (R z))
  context {h : Label.{u}} (hh : IsSelfVisible 2 h) {L R f : Fin 5 → Label.{u}}
    (hL : S.{u}.rows.IsLawful L) (hR : S.{u}.rows.IsLawful R) (hy : L 0 = R 0) (hadm : Adm L R)
    (hf : S.{u}.rows.IsLawful f) (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (R d) h) ∧ Adm f W
  donor {h : Label.{u}} (hh : IsSelfVisible 2 h) {L R f : Fin 5 → Label.{u}}
    (hL : S.{u}.rows.IsLawful L) (hR : S.{u}.rows.IsLawful R) (hy : L 0 = R 0) (hadm : Adm L R)
    (hf : S.{u}.rows.IsLawful f) (hfR : ∀ d, min (f d) h = min (R d) h) :
    ∃ W : Fin 5 → Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (L d) h) ∧ Adm W f

variable {Adm : (Fin 5 → Label.{u}) → (Fin 5 → Label.{u}) → Prop}

variable (α Adm) in
/-- **The admission on labellings of the lower layer**: the context and donor copies are
admitted. -/
def AdmBy (e : Fin (lowerT α).card → Label.{u}) : Prop := Adm (privT e) (donT e)

theorem admBy_bot (hA : IsLowAdmission Adm) : AdmBy α Adm (fun _ ↦ (⊥ : Label.{u})) := hA.bot

theorem grade_lowerT_le (d : Fin (lowerT α).card) : (lowerT α).toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    exact Nat.lt_succ_iff.mp ((I α).grade_lt e)
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega

/-- **The admission passes to the orbit code**: the orbit code of the splice is the orbit map of the
labelling (every cell of the lower layer has grade at most `2`), a monotone map. -/
theorem admBy_code (hA : IsLowAdmission Adm) {W : Fin (lowerT α).card → Label.{u}}
    (hW : AdmBy α Adm W) :
    AdmBy α Adm (orbitCode 2 ((lowerT α).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsp : (lowerT α).toCellScheme.splice 2 (fun _ ↦ ⊥) W = W :=
    funext fun d ↦ CellScheme.splice_of_le (grade_lowerT_le d)
  rw [hsp]
  have hw := isWitness_orbitMap 2 W
  exact hA.comp hw.monotone hw.map_bot (fun x ↦ hw.visibilityReplace_comm x 2
    (by rw [stepSuppressor_of_le le_rfl]; exact le_top) 2 le_rfl) hW

/-- Agreement capped at `h` at every cell, from agreement on the two copies and at the copies of
`z`. -/
theorem min_eq_of_copies {W a : Fin (lowerT α).card → Label.{u}} {h : Label.{u}}
    (hL : ∀ z, min (privT W z) h = min (privT a z) h)
    (hR : ∀ z, min (donT W z) h = min (donT a z) h)
    (hN : ∀ i, min (W (Fin.natAdd _ i)) h = min (a (Fin.natAdd _ i)) h)
    (d : Fin (lowerT α).card) : min (W d) h = min (a d) h := by
  induction d using Fin.addCases with
  | right i => exact hN i
  | left e =>
    rcases (I α).eq_faceCell_or (hLR α) e with he | he
    · rw [← he]; exact hL _
    · rw [← he]; exact hR _

/-! ### The lift provisions on the lower layer -/

theorem isLawful_lab_top : S.{u}.rows.IsLawful (lab ⊤ ⊤ ⊤) :=
  isLawful_lab (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 2) le_rfl rfl

/-- **The provision at the cap `⊥` from the context coatom**: the provision of the admission at the
cap `⊥`, from the labels of the input on both faces. -/
theorem botProvision_left (hA : IsLowAdmission Adm) {f : Fin (lowerT α).card → Label.{u}}
    (hf : (lowerT α).rows.IsLawfulBelow pairL (fun d ↦ f d)) :
    ∃ W : Fin (lowerT α).card → Label.{u},
      (lowerT α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerT α).toCellScheme.below pairL, W d = f d) ∧
      AdmBy α Adm (orbitCode 2 ((lowerT α).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hs := isLawful_privT hf
  obtain ⟨WR, hWR, hWR0, -, hadm⟩ := hA.context (isSelfVisible_bot 2) isLawful_lab_top
    isLawful_lab_top rfl hA.top hs (fun _ ↦ by simp)
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glue_lowerT hs hWR hWR0.symm
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, admBy_code hA ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_below hd
    exact congrFun hgL z
  · rw [AdmBy, hgL, hgR]; exact hadm

/-- **The provision at the cap `⊥` from the donor coatom**: the provision of the admission at the
cap `⊥`, from the labels of the input on both faces. -/
theorem botProvision_right (hA : IsLowAdmission Adm) {f : Fin (lowerT α).card → Label.{u}}
    (hf : (lowerT α).rows.IsLawfulBelow pairR (fun d ↦ f d)) :
    ∃ W : Fin (lowerT α).card → Label.{u},
      (lowerT α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerT α).toCellScheme.below pairR, W d = f d) ∧
      AdmBy α Adm (orbitCode 2 ((lowerT α).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hs := isLawful_donT hf
  obtain ⟨WL, hWL, hWL0, -, hadm⟩ := hA.donor (isSelfVisible_bot 2) isLawful_lab_top
    isLawful_lab_top rfl hA.top hs (fun _ ↦ by simp)
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glue_lowerT hWL hs hWL0
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, admBy_code hA ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_below hd
    exact congrFun hgR z
  · rw [AdmBy, hgL, hgR]; exact hadm

/-- **The provision at a cap from the context coatom** (the provision of the admission on the two
copies, glued). -/
theorem capProvision_left (hA : IsLowAdmission Adm) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {a : Fin (lowerT α).card → Label.{u}} (ha : (lowerT α).rows.IsLawful a) (hAa : AdmBy α Adm a)
    {f : Fin (lowerT α).card → Label.{u}}
    (hf : (lowerT α).rows.IsLawfulBelow pairL (fun d ↦ f d))
    (hfa : ∀ d ∈ (lowerT α).toCellScheme.below pairL, min (f d) h = min (a d) h) :
    ∃ W : Fin (lowerT α).card → Label.{u},
      (lowerT α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerT α).toCellScheme.below pairL, W d = f d) ∧
      (∀ d, (lowerT α).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      AdmBy α Adm (orbitCode 2 ((lowerT α).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hL := isLawful_privT (ha.isLawfulBelow pairL)
  have hR := isLawful_donT (ha.isLawfulBelow pairR)
  have hy : privT a 0 = donT a 0 := by rw [privT, donT, lc_zero]
  have hs := isLawful_privT hf
  have hfL (z : Fin 5) : min (privT f z) h = min (privT a z) h := hfa _ (left_mem_below z)
  obtain ⟨WR, hWR, hWR0, hWRa, hadm⟩ := hA.context hh hL hR hy hAa hs hfL
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glue_lowerT hs hWR hWR0.symm
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ min_eq_of_copies
    (fun z ↦ by rw [hgL]; exact hfL z) (fun z ↦ by rw [hgR]; exact hWRa z)
    (fun i ↦ by rw [hgN, natAdd_eq_privT ha]; exact hfL 0) d, admBy_code hA ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_below hd
    exact congrFun hgL z
  · rw [AdmBy, hgL, hgR]; exact hadm

/-- **The provision at a cap from the donor coatom** (the provision of the admission on the two
copies, glued). -/
theorem capProvision_right (hA : IsLowAdmission Adm) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {a : Fin (lowerT α).card → Label.{u}} (ha : (lowerT α).rows.IsLawful a) (hAa : AdmBy α Adm a)
    {f : Fin (lowerT α).card → Label.{u}}
    (hf : (lowerT α).rows.IsLawfulBelow pairR (fun d ↦ f d))
    (hfa : ∀ d ∈ (lowerT α).toCellScheme.below pairR, min (f d) h = min (a d) h) :
    ∃ W : Fin (lowerT α).card → Label.{u},
      (lowerT α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (lowerT α).toCellScheme.below pairR, W d = f d) ∧
      (∀ d, (lowerT α).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      AdmBy α Adm (orbitCode 2 ((lowerT α).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hL := isLawful_privT (ha.isLawfulBelow pairL)
  have hR := isLawful_donT (ha.isLawfulBelow pairR)
  have hy : privT a 0 = donT a 0 := by rw [privT, donT, lc_zero]
  have hs := isLawful_donT hf
  have hfR (z : Fin 5) : min (donT f z) h = min (donT a z) h := hfa _ (right_mem_below z)
  obtain ⟨WL, hWL, hWL0, hWLa, hadm⟩ := hA.donor hh hL hR hy hAa hs hfR
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glue_lowerT hWL hs hWL0
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ min_eq_of_copies
    (fun z ↦ by rw [hgL]; exact hWLa z) (fun z ↦ by rw [hgR]; exact hfR z)
    (fun i ↦ by rw [hgN, natAdd_eq_privT ha, hWL0, hy]; exact hfR 0) d, admBy_code hA ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_below hd
    exact congrFun hgR z
  · rw [AdmBy, hgL, hgR]; exact hadm

/-! ### The admitted completion: bountiful and legal below the full grade -/

variable (α Adm) in
/-- **The admitted layer at the seed**: the field layer at the grade `2` over the lower layer, on
the catalogue entries satisfying the admission `MixedSeed.AdmBy α Adm`. -/
noncomputable abbrev admittedBy : Scheme.{u} 3 :=
  (lowerT α).admittedFieldLayer 2 (AdmBy α Adm) ((I α).not_univ_two_le_doubledLower (hLR α))

private theorem erase_ne_univ (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

theorem gradedIndex_left_three :
    (lowerT α).toCellScheme.gradedIndex (Fin.castAdd _ (lc α 3)) = pairL := by
  rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, gradedIndex_lc,
    show cells.scope 3 = univ by decide, Coatom.univ_map_left]
  rfl

theorem gradedIndex_right_three :
    (lowerT α).toCellScheme.gradedIndex (Fin.castAdd _ (rc α 3)) = pairR := by
  rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, gradedIndex_rc,
    show cells.scope 3 = univ by decide, Coatom.univ_map_right]
  rfl

/-- **The lift from the context coatom into the admitted layer.** -/
theorem cappedLift_admittedBy_left (hA : IsLowAdmission Adm) :
    (admittedBy α Adm).rows.CappedLift (X := pairL) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := (I α).not_univ_two_le_doubledLower (hLR α))
    ((I α).isConsistent_doubledLower (hLR α) (isLegal_T α)) (admBy_bot hA) (erase_ne_univ _)
    ⟨_, gradedIndex_left_three⟩ cappedLift_lowerT_left (fun _ hf ↦ botProvision_left hA hf)
    (fun _ hh _ _ _ ha hAa _ hf hfa ↦ capProvision_left hA hh ha hAa hf hfa)

/-- **The lift from the donor coatom into the admitted layer.** -/
theorem cappedLift_admittedBy_right (hA : IsLowAdmission Adm) :
    (admittedBy α Adm).rows.CappedLift (X := pairR) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := (I α).not_univ_two_le_doubledLower (hLR α))
    ((I α).isConsistent_doubledLower (hLR α) (isLegal_T α)) (admBy_bot hA) (erase_ne_univ _)
    ⟨_, gradedIndex_right_three⟩ cappedLift_lowerT_right (fun _ hf ↦ botProvision_right hA hf)
    (fun _ hh _ _ _ ha hAa _ hf hfa ↦ capProvision_right hA hh ha hAa hf hfa)

/-- **The admitted layer is bountiful.** -/
theorem isBountiful_admittedBy (hA : IsLowAdmission Adm) : (admittedBy α Adm).rows.IsBountiful :=
  (I α).isBountiful_admittedDoubledLower (hLR α) (A := AdmBy α Adm)
    cappedLift_lowerT_left cappedLift_lowerT_right
    (cappedLift_admittedBy_left hA) (cappedLift_admittedBy_right hA)

/-- **The admitted completion at the seed is legal below the full grade.** -/
theorem isLegalBelowFullGrade_admittedBy (hA : IsLowAdmission Adm) :
    (admittedBy α Adm).IsLegalBelowFullGrade :=
  (I α).isLegalBelowFullGrade_admittedDoubledLower (hLR α) (isLegal_T α) (admBy_bot hA)
    (isBountiful_admittedBy hA)

/-- **Admitted states extend to the admitted completion**: the input on the context copy and
`(⊤, ⊥, ⊤, ⊤, v)` on the donor copy, when admitted, glue to a lawful labelling of the lower layer
whose orbit code is admitted, so they extend to a labelling of the admitted completion lawful below
`(univ, 2)` (every cell of the completion lies below it). -/
theorem exists_isLawful_admittedBy (hA : IsLowAdmission Adm) {v : Label.{u}}
    (hv : IsSelfVisible 2 v) (hst : Adm (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v)) :
    ∃ q : Fin (admittedBy α Adm).card → Label.{u},
      (admittedBy α Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun x ↦ q x) ∧
      (∀ z, q (Fin.castAdd _ (Fin.castAdd _ (lc α z))) = lab ⊤ ⊤ ⊤ z) ∧
      ∀ z, q (Fin.castAdd _ (Fin.castAdd _ (rc α z))) = lab ⊤ ⊤ v z := by
  have hR : S.{u}.rows.IsLawful (lab ⊤ ⊤ v) :=
    isLawful_lab (isSelfVisible_top 1) (isSelfVisible_top 2) hv le_rfl (by simp)
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glue_lowerT isLawful_lab_top hR rfl
  have hAg : AdmBy α Adm g := by
    rw [AdmBy, hgL, hgR]
    exact hst
  obtain ⟨q, hq, hqe⟩ := Scheme.exists_lift_bot_admittedFieldLayer
    (hS := (I α).not_univ_two_le_doubledLower (hLR α)) (hg.isLawfulBelow _) (admBy_code hA hAg)
  refine ⟨q, hq, fun z ↦ ?_, fun z ↦ ?_⟩
  · rw [hqe _ (grade_lowerT_le _)]; exact congrFun hgL z
  · rw [hqe _ (grade_lowerT_le _)]; exact congrFun hgR z

/-! ### The owner-as-partner admission at the twisted seed -/

/-- The LOW clause passes to the image under a monotone map. -/
theorem lowVia_comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) {L R : Fin 5 → Label.{u}}
    (h : LowVia L R) : LowVia (fun z ↦ σ (L z)) (fun z ↦ σ (R z)) := by
  rw [lowVia_iff] at h ⊢
  intro hlt
  have hlt' : max (R 1) (R 4) < L 3 := lt_of_not_ge fun hle ↦ hlt.not_ge (by
    rw [← hσ.map_max]; exact hσ hle)
  exact ⟨hσ (h hlt').1, hσ (h hlt').2⟩

/-- **The owner-as-partner clause is an admission** (`SeparationObstruction.capProvision_context`,
`SeparationObstruction.capProvision_donor`). -/
theorem isLowAdmission_lowVia : IsLowAdmission LowVia.{u} where
  bot := by
    rw [lowVia_iff]
    intro hlt
    exact absurd hlt (by simp)
  top := by
    rw [lowVia_iff]
    exact fun _ ↦ ⟨le_top, le_top⟩
  comp := fun {_} hσ _ _ {_ _} h ↦ lowVia_comp hσ h
  context := capProvision_context
  donor := capProvision_donor

/-- The state of the twisted seed is admitted by the owner-as-partner clause. -/
theorem lowVia_Utop (v : Label.{u}) : LowVia (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v) := by
  rw [lowVia_iff]
  exact fun _ ↦ ⟨le_top, le_top⟩

variable (α) in
/-- **The LOW admission at the twisted seed** on labellings of the lower layer: the context and
donor copies satisfy `SeparationObstruction.LowVia` (the partner the owner; the designated tops
`z'`, `o'`, the designated cells below the top `e'`, `r'`). -/
abbrev AdmU : (Fin (lowerT α).card → Label.{u}) → Prop := AdmBy α LowVia

theorem admU_bot : AdmU α (fun _ ↦ (⊥ : Label.{u})) := admBy_bot isLowAdmission_lowVia

variable (α) in
/-- **The LOW-admitted layer at the twisted seed**. -/
noncomputable abbrev admittedT : Scheme.{u} 3 := admittedBy α LowVia

/-- **The LOW-admitted completion at the twisted seed is legal below the full grade.** -/
theorem isLegalBelowFullGrade_admittedT : (admittedT α).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_admittedBy isLowAdmission_lowVia

/-! ### Determination of `o'` in the LOW-admitted completion -/

/-- **Determination of `o'` in the LOW-admitted completion.**  In every labelling `q` lawful below
`(univ, 2)` (every cell lies below it) with the owner `o` at `⊤` and the donor's `r'` below `⊤`, the
donor's `o'` is `⊤`: by recognition at a reader (`Scheme.exists_admitted_image`), `q` on the old
cells is the image of an admitted entry under a monotone map fixing `⊥`, so it satisfies the LOW
clause (`MixedSeed.lowVia_comp`), whose antecedent holds (`e'` is `⊥`, `r'` is below `⊤ = o`). -/
theorem eq_top_of_admittedT {q : Fin (admittedT α).card → Label.{u}}
    (hq : (admittedT α).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun x ↦ q x))
    (ho : q (Fin.castAdd _ (Fin.castAdd _ (lc α 3))) = ⊤)
    (hr : q (Fin.castAdd _ (Fin.castAdd _ (rc α 4))) < ⊤) :
    q (Fin.castAdd _ (Fin.castAdd _ (rc α 3))) = ⊤ := by
  have hx₀ : (lowerT α).toCellScheme.grade (Fin.castAdd _ (lc α 3)) = 2 :=
    congrArg Prod.snd gradedIndex_left_three
  obtain ⟨a, ha, hA, σ, hσ, hσ0, -, hold⟩ :=
    Scheme.exists_admitted_image (hS := (I α).not_univ_two_le_doubledLower (hLR α))
      (admU_bot (α := α)) grade_lowerT_le hq hx₀ ho
  have hadm := lowVia_comp hσ hA
  rw [lowVia_iff] at hadm
  have hab : (lowerT α).rows.IsLawfulBelow pairR (fun d ↦ a d) := ha.isLawfulBelow pairR
  have hae : donT a 1 = ⊥ := by
    obtain ⟨hde, -, -⟩ := eq_lab_of_isLawful (isLawful_donT hab)
    rw [hde]; rfl
  have h3 := (hadm (by
    rw [hae, hσ0, max_eq_right bot_le]
    change σ (a (Fin.castAdd _ (rc α 4))) < σ (a (Fin.castAdd _ (lc α 3)))
    rw [← hold, ← hold, ho]
    exact hr)).2
  change σ (a (Fin.castAdd _ (lc α 3))) ≤ σ (a (Fin.castAdd _ (rc α 3))) at h3
  rw [← hold, ← hold, ho, top_le_iff] at h3
  exact h3

/-! ### The self-seed admission -/

/-- The self-seed clause passes to the image under a monotone map. -/
theorem lowViaSelf_comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) {L R : Fin 5 → Label.{u}}
    (h : LowViaSelf L R) : LowViaSelf (fun z ↦ σ (L z)) (fun z ↦ σ (R z)) := by
  rw [lowViaSelf_iff] at h ⊢
  intro hlt
  have hlt' : R 1 < L 3 := lt_of_not_ge fun hle ↦ hlt.not_ge (hσ hle)
  exact ⟨hσ (h hlt').1, hσ (h hlt').2.1, hσ (h hlt').2.2⟩

/-- **The self-seed clause is an admission** (`SeparationObstruction.capProvisionSelf_context`,
`SeparationObstruction.capProvisionSelf_donor`). -/
theorem isLowAdmission_lowViaSelf : IsLowAdmission LowViaSelf.{u} where
  bot := by
    rw [lowViaSelf_iff]
    intro hlt
    exact absurd hlt (lt_irrefl _)
  top := lowViaSelf_T
  comp := fun {_} hσ _ _ {_ _} h ↦ lowViaSelf_comp hσ h
  context := capProvisionSelf_context
  donor := capProvisionSelf_donor

/-- **Determination of the donor's tops in the self-admitted completion.**  In every labelling `q`
of the completion admitted by `SeparationObstruction.LowViaSelf`, lawful below `(univ, 2)`, with the
owner `o` at `⊤`, the donor's `z'`, `o'`, `r'` are `⊤`: by recognition at a reader, `q` on the old
cells is the image of an admitted entry under a monotone map fixing `⊥`, whose antecedent holds
(`e'` is `⊥`, below `⊤ = o`). -/
theorem eq_top_of_admittedSelf {q : Fin (admittedBy α LowViaSelf.{u}).card → Label.{u}}
    (hq : (admittedBy α LowViaSelf.{u}).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
      (fun x ↦ q x))
    (ho : q (Fin.castAdd _ (Fin.castAdd _ (lc α 3))) = ⊤) :
    q (Fin.castAdd _ (Fin.castAdd _ (rc α 2))) = ⊤ ∧
      q (Fin.castAdd _ (Fin.castAdd _ (rc α 3))) = ⊤ ∧
      q (Fin.castAdd _ (Fin.castAdd _ (rc α 4))) = ⊤ := by
  have hx₀ : (lowerT α).toCellScheme.grade (Fin.castAdd _ (lc α 3)) = 2 :=
    congrArg Prod.snd gradedIndex_left_three
  obtain ⟨a, ha, hA, σ, hσ, hσ0, -, hold⟩ :=
    Scheme.exists_admitted_image (hS := (I α).not_univ_two_le_doubledLower (hLR α))
      (admBy_bot (α := α) isLowAdmission_lowViaSelf) grade_lowerT_le hq hx₀ ho
  have hadm := lowViaSelf_comp hσ hA
  rw [lowViaSelf_iff] at hadm
  have hab : (lowerT α).rows.IsLawfulBelow pairR (fun d ↦ a d) := ha.isLawfulBelow pairR
  have hae : donT a 1 = ⊥ := by
    obtain ⟨hde, -, -⟩ := eq_lab_of_isLawful (isLawful_donT hab)
    rw [hde]; rfl
  obtain ⟨h2, h3, h4⟩ := hadm (by
    rw [hae, hσ0]
    change ⊥ < σ (a (Fin.castAdd _ (lc α 3)))
    rw [← hold, ho]
    exact bot_lt_top)
  change σ (a (Fin.castAdd _ (lc α 3))) ≤ σ (a (Fin.castAdd _ (rc α 2))) at h2
  change σ (a (Fin.castAdd _ (lc α 3))) ≤ σ (a (Fin.castAdd _ (rc α 3))) at h3
  change σ (a (Fin.castAdd _ (lc α 3))) ≤ σ (a (Fin.castAdd _ (rc α 4))) at h4
  rw [← hold, ← hold, ho, top_le_iff] at h2 h3 h4
  exact ⟨h2, h3, h4⟩

end VaughtConjecture.MixedSeed

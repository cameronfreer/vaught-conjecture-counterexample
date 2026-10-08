/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsFill
import VaughtConjecture.Continuation.TiedRootCapOffsets
import VaughtConjecture.MainTheorem.CutoffCoatomRelabel

/-!
# Cutoff stable recovery from a correct completion

Roadmap, Layer 4, output 3 of higher-stage reconstruction, and Layer 3, 3.3–3.4 ((R4) of the
table of Layer 3: the reading through a proper cap, at the seed of the first coatom).  Each item
below is compiled in this repository (theorem named), unless marked otherwise.

**The seed and the requests** (`StageType.FirstCoatomInput`, `.seed`, `.requests`).  An input of
`StageType.HasCutoffFirstCoatomCompletions` is bundled as `StageType.FirstCoatomInput`; its seed is
the amalgam of `T⁺↓λ_ξ` and `tb↓λ_ξ` over `p↓λ_ξ`.  Cap data (`StageType.MarginCapData`, from the
margin calibration, `StageType.GradedCapMarginCalibration.nonempty_marginCapData`) give requests on
the cells of the amalgam: `T` the new cells of `D` labelled `⊤`, `F` the new cells of `D` labelled
in the block of `λ_ξ` with their references, `Z` empty.  They are graded
(`StageType.FirstCoatomInput.requests_isGraded`) and the glued labelling is correct
(`StageType.FirstCoatomInput.requests_isCorrect_label`: at `λ_ξ` the cap, the marker and the
requested cells reduce to `⊤`).

**The reading** (`StageType.FirstCoatomInput.exists_isCutoffStableRecovery`).  With the cap's grade
`N ≥ 3`, the common face carrying no cell of grade `N` (`hface`) and the fills from the private
coatom at every grade from `N` to the top (`CapRequests.CapFillBotAt`,
`CapRequests.CapFillPosAt`), the completion of `Seed.exists_correctCompletion` with the apex
carries cutoff stable recovery: the old cells of `D` are read through the face `T⁺`, the new cells
labelled `⊥` or below `λ_ξ` through the receiving family, the new cells in the block of `λ_ξ`
exactly from their references and the new top cells above `γ`, through a cell of `(univ, N)`
reached from the cap.

**h4 from the fills** (`StageType.hasCutoffFirstCoatomCompletions_of_capFills`,
`StageType.hasCutoffFirstCoatomCompletions'_of_capFills`).  First-coatom completions follow for the
margin calibration, and for the margin calibration with a floor
(`StageType.GradedCapMarginCalibration'`: `3 ≤ N`, every cell of `D` of grade below `N`, the root's
offsets below `N`; acquisition compiled,
`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin'`), where `3 ≤ N` is discharged.

**Open inputs, each with its obstruction.**
* `hface`: false in general (the common face can carry cells of the cap's grade); without it
  availability pins the cap above the labels of the common face at its grade (argued in
  `VaughtConjecture.Extension.CapRequestsGrade`, not compiled).
* `CapRequests.CapFillPosAt` over a live common face: the dead-face fill does not apply when the
  common face carries a label other than `⊥` (`CapRequests.not_isDeadFace_of_label_ne_bot`), and
  no other fill at the positive caps is compiled.
* `CapRequests.CapFillBotAt`: from `CapRequests.DonorFollowsRoot` when no new cell of `D` lies in
  the block of `λ_ξ` (`StageType.FirstCoatomInput.capFillBotAt_requests_of_donorFollowsRoot`);
  `DonorFollowsRoot` fails across a tie or an inversion of the glued labelling
  (`CapRequests.not_exists_transport_of_tie`, `CapRequests.not_exists_transport_of_inversion`).
  A capped form (agreement only below the prescription at the cap) does not give the fill as
  `CapRequests.capFillBotAt_of_donorFollowsRoot` proves it: the glued fill must agree with the
  prescription exactly on the common face, which the cap does not bound (argued, not compiled).
* The inputs with a new cell of `D` in the block of `λ_ξ` (`F` nonempty): no fill is compiled; the
  fills above ask `F` empty.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

/-! ### The old cells after appending a cell of full scope -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- **A lawful labelling restricts to the old cells**: below a pair not above `(univ, j)`, a
lawful labelling of the scheme with a cell appended is, on the old cells, lawful for `S`. -/
theorem isLawfulBelow_castSucc {ℓ : Fin (S.card + 1) → Label.{u}}
    (hℓ : (S.appendFullCell j r h).rows.IsLawful ℓ) {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), j) ≤ X) :
    S.rows.IsLawfulBelow X fun d ↦ ℓ d.1.castSucc := by
  have hc := CellScheme.Rows.isLawfulBelow_comap_iff (R := (S.appendFullCell j r h).rows)
    (isLowerEmbedding_castSucc j r h) (image_castSucc_below hX) (r := fun z ↦ ℓ z)
  rw [comap_rows_castSucc] at hc
  exact hc.mpr (hℓ.isLawfulBelow X)

end Scheme

/-! ### The cells of the completion along a proper face -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- **The cells of the completion along a proper face** are the old cells of the amalgam along it,
at equal positions. -/
theorem cellMap_completion {k : ℕ} (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    {i : Fin (I.amalgam.toScheme.comap f).card} {z : Fin ((F.completion hα).toScheme.comap f).card}
    (hiz : (i : ℕ) = z) :
    (F.completion hα).toScheme.cellMap f z = (F.embed (I.amalgam.toScheme.cellMap f i)).castSucc :=
  Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme)
    (T := (F.completion hα).toScheme) f (φ := fun d ↦ (F.embed d).castSucc)
    (Fin.strictMono_castSucc.comp F.embed.strictMono)
    (fun d ↦ (Scheme.appendFullCellScheme_scope_castSucc _ _ _).trans (F.scope_embed d))
    (fun z hz ↦ by
      obtain ⟨w, rfl⟩ := StageType.mem_range_castSucc_of_addApex _ _ f hf z hz
      have hne : F.scheme.toCellScheme.scope w ≠ univ := fun he ↦ hf (eq_univ_of_forall fun x ↦ by
        have hx : x ∈ ((F.completion hα).toCellScheme.scope w.castSucc : Set (Fin (m + 2))) := by
          change x ∈
            (Scheme.appendFullCellScheme (F.truncate hα).toScheme (m + 2)).scope w.castSucc
          rw [Scheme.appendFullCellScheme_scope_castSucc,
            show (F.truncate hα).toCellScheme.scope w = univ from he]
          exact mem_univ x
        obtain ⟨y, rfl⟩ := hz hx
        exact mem_map_of_mem _ (mem_univ y))
      obtain ⟨d, rfl⟩ := F.mem_range_embed w hne
      exact ⟨d, rfl⟩)
    hiz

/-- **A lawful labelling of the completed scheme with the apex is lawful on the old cells** below
every pair `(univ, N)` with `N < m + 2`. -/
theorem isLawfulBelow_castSucc {ℓ : Fin (F.completion hα).card → Label.{u}}
    (hℓ : (F.completion hα).rows.IsLawful ℓ) {N : ℕ} (hN : N < m + 2) :
    F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), N) fun z ↦ ℓ z.1.castSucc :=
  Scheme.isLawfulBelow_castSucc (h := F.isLegalBelowFullGrade.not_le) hℓ fun hle ↦
    absurd hle.2 (by simp only; omega)

end CompletionBelowFullGrade

/-! ### The data of a margin calibration with a cap of full scope -/

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- **Cap data for the margin calibration**: a cap of full scope and grade `N` labelled at least
`λ_ξ + N`, with `k < N`, an offset `R < N` with `γ < λ_ξ + R`, a marker labelled `λ_ξ + i` with
`i < N` and grade at most `N`, and, for each cell of `D` labelled an ordinal `μ + n` (`μ` zero or a
limit), the offset `n < N` and a reference cell of grade at most `N` labelled `μ + i'`, `i' < N`. -/
structure MarginCapData (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) where
  /-- The cap. -/
  cap : Fin Tp.card
  /-- The marker. -/
  marker : Fin Tp.card
  /-- The offset of the marker reading. -/
  R : ℕ
  /-- The finite part of the label of the marker. -/
  i : ℕ
  /-- The reference cell of a cell of `D`. -/
  ref : Fin D.card → Fin Tp.card
  /-- The offset of a cell of `D`. -/
  off : Fin D.card → ℕ
  /-- The cap has full scope. -/
  scope_cap : Tp.toCellScheme.scope cap = univ
  /-- The cap is labelled at least `λ_ξ + N`. -/
  le_label_cap :
    ((blockStage ξ + Tp.toCellScheme.grade cap : Ordinal.{u}) : Label.{u}) ≤ Tp.label cap
  /-- The root has fewer points than the grade of the cap. -/
  lt_grade_cap : k < Tp.toCellScheme.grade cap
  /-- The offset is below the grade of the cap. -/
  R_lt : R < Tp.toCellScheme.grade cap
  /-- The margin. -/
  lt_R : γ < blockStage ξ + R
  /-- The finite part of the marker is below the grade of the cap. -/
  i_lt : i < Tp.toCellScheme.grade cap
  /-- The marker has grade at most that of the cap. -/
  grade_marker_le : Tp.toCellScheme.grade marker ≤ Tp.toCellScheme.grade cap
  /-- The marker is labelled `λ_ξ + i`. -/
  label_marker : Tp.label marker = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})
  /-- The references of the ordinal labels of `D`. -/
  ref_spec : ∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
    ∃ (μ : Ordinal.{u}) (i' : ℕ), Order.IsSuccPrelimit μ ∧ o = μ + off j ∧
      off j < Tp.toCellScheme.grade cap ∧ i' < Tp.toCellScheme.grade cap ∧
      Tp.toCellScheme.grade (ref j) ≤ Tp.toCellScheme.grade cap ∧
      Tp.label (ref j) = ((μ + i' : Ordinal.{u}) : Label.{u})

/-- **The margin calibration gives cap data**, for a legal `T⁺`: availability within `T⁺` moves the
cap to a cell of full scope and the same grade, labelled at least the cap. -/
theorem GradedCapMarginCalibration.nonempty_marginCapData
    {Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)} {f : Fin k ↪ Fin (m + 1)}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} (hT : Tp.IsLegal)
    (h : GradedCapMarginCalibration ξ Tp f D γ) : Nonempty (MarginCapData Tp D γ) := by
  classical
  obtain ⟨b, hb, hk, ⟨R, hR, hγ⟩, ⟨a, i, hi, ha, hal⟩, href⟩ := h
  obtain ⟨s, hs⟩ := hT.isComplete ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b)
    ⟨Tp.univ_mem_faces, show 0 < Tp.toCellScheme.grade b by omega, by
      rw [card_univ, Fintype.card_fin]
      exact Tp.grade_le b⟩
  obtain ⟨u, hu, hbu⟩ := Tp.isLawful.availability b s
    (by rw [show Tp.toCellScheme.scope s = univ from congrArg Prod.fst hs]; exact subset_univ _)
    (congrArg Prod.snd hs).symm
  have hus : Tp.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 1))),
      Tp.toCellScheme.grade b) := hu.trans hs
  have hg : Tp.toCellScheme.grade u = Tp.toCellScheme.grade b := congrArg Prod.snd hus
  have hspec (j : Fin D.card) : ∃ (r : Fin Tp.card) (n : ℕ), ∀ o : Ordinal.{u}, D.label j = o →
      ∃ (μ : Ordinal.{u}) (i' : ℕ), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i' < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade r ≤ Tp.toCellScheme.grade b ∧
        Tp.label r = ((μ + i' : Ordinal.{u}) : Label.{u}) := by
    by_cases hj : ∃ o : Ordinal.{u}, D.label j = o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨μ, n, i', r, hμ, hon, hn, hi', hr, hrl⟩ := href j o ho
      refine ⟨r, n, fun o' ho' ↦ ⟨μ, i', hμ, ?_, hn, hi', hr, hrl⟩⟩
      rw [ho] at ho'
      exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hon
    · exact ⟨b, 0, fun o ho ↦ absurd ⟨o, ho⟩ hj⟩
  choose ref off hro using hspec
  exact ⟨{ cap := u, marker := a, R := R, i := i, ref := ref, off := off
           scope_cap := congrArg Prod.fst hus
           le_label_cap := by rw [hg]; exact hb.trans hbu
           lt_grade_cap := by rw [hg]; exact hk
           R_lt := by rw [hg]; exact hR
           lt_R := hγ
           i_lt := by rw [hg]; exact hi
           grade_marker_le := by rw [hg]; exact ha
           label_marker := hal
           ref_spec := fun j o ho ↦ by rw [hg]; exact hro j o ho }⟩

end StageType

/-! ### The seed of the first coatom and the requests of the cap data -/

namespace StageType

variable (ξ : Ordinal.{u}) (m k : ℕ)

/-- **An input at the first coatom**: a legal `T⁺` at `λ_{ξ+1}` on `m + 1` points with face `p`
along the first points, a legal coface `tb` of `p`, an embedding `f` of `k` points into the
coatom with face `P` of `p`, and a coface `D` of `P` that is the face of `tb` along `f` followed by
the new point (the inputs of `StageType.HasCutoffFirstCoatomCompletions`). -/
structure FirstCoatomInput where
  /-- The context. -/
  Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)
  /-- Its face along the first points. -/
  p : StageType.{u} (blockStage (ξ + 1)) m
  /-- The intermediate coface. -/
  tb : StageType.{u} (blockStage (ξ + 1)) (m + 1)
  /-- The root. -/
  f : Fin k ↪ Fin m
  /-- The face of `p` along the root. -/
  P : StageType.{u} (blockStage (ξ + 1)) k
  /-- The donor. -/
  D : StageType.{u} (blockStage (ξ + 1)) (k + 1)
  isLegal_Tp : Tp.IsLegal
  restrictFace_Tp : restrictFace Fin.castSuccEmb Tp = some p
  mem_cofaces_tb : tb ∈ p.cofaces
  restrictFace_p : restrictFace f p = some P
  mem_cofaces_D : D ∈ P.cofaces
  restrictFace_tb : restrictFace (extendByLast f) tb = some D

variable {ξ m k} (X : FirstCoatomInput.{u} ξ m k)

namespace FirstCoatomInput

/-- The face of `T⁺↓λ_ξ` along the first points. -/
theorem restrictFace_reduce_Tp :
    restrictFace (Coatom.face m) (X.Tp.reduce (isSuccPrelimit_blockStage ξ)) =
      some (X.p.reduce (isSuccPrelimit_blockStage ξ)) := by
  rw [restrictFace_reduce, X.restrictFace_Tp, Option.map_some]

/-- The face of `tb↓λ_ξ` along the first points. -/
theorem restrictFace_reduce_tb :
    restrictFace (Coatom.face m) (X.tb.reduce (isSuccPrelimit_blockStage ξ)) =
      some (X.p.reduce (isSuccPrelimit_blockStage ξ)) := by
  rw [restrictFace_reduce, X.mem_cofaces_tb.2, Option.map_some]

/-- **The seed of the first coatom** at `λ_ξ`: the amalgam of `T⁺↓λ_ξ` and `tb↓λ_ξ` over
`p↓λ_ξ`. -/
noncomputable def seed : Seed.{u} (blockStage ξ) m :=
  Seed.ofCoatoms (X.isLegal_Tp.reduce _) (X.mem_cofaces_tb.1.reduce _) X.restrictFace_reduce_Tp
    X.restrictFace_reduce_tb

/-- The first coatom of the seed is `T⁺↓λ_ξ`. -/
theorem seed_left : X.seed.left = X.Tp.reduce (isSuccPrelimit_blockStage ξ) := rfl

/-- The second coatom of the seed is `tb↓λ_ξ`. -/
theorem seed_right : X.seed.right = X.tb.reduce (isSuccPrelimit_blockStage ξ) := rfl

/-- The embedding of the donor's points: the root followed by the new point, into the seed. -/
abbrev donorEmb : Fin (k + 1) ↪ Fin (m + 2) := extendByLast (X.f.trans Fin.castSuccEmb)

/-- The face of the amalgam along the donor's points is `D↓λ_ξ`. -/
theorem restrictFace_amalgam_donor :
    restrictFace X.donorEmb X.seed.amalgam = some (X.D.reduce (isSuccPrelimit_blockStage ξ)) := by
  rw [donorEmb, ← extendByLast_trans,
    ← restrictFace_trans X.seed.amalgam (Coatom.right m) _ X.seed.restrictFace_right, seed_right,
    restrictFace_reduce, X.restrictFace_tb, Option.map_some]

/-- The face of the amalgam along the first points is `T⁺↓λ_ξ`. -/
theorem restrictFace_amalgam_left :
    restrictFace (Coatom.left m) X.seed.amalgam =
      some (X.Tp.reduce (isSuccPrelimit_blockStage ξ)) :=
  X.seed.restrictFace_left

/-- The cell of the amalgam at a cell of `T⁺`. -/
noncomputable def leftCell (b : Fin X.Tp.card) : Fin X.seed.amalgam.card :=
  faceCell X.restrictFace_amalgam_left b

/-- The cell of the amalgam at a cell of `D`. -/
noncomputable def donorCell (j : Fin X.D.card) : Fin X.seed.amalgam.card :=
  faceCell X.restrictFace_amalgam_donor j

theorem grade_leftCell (b : Fin X.Tp.card) :
    X.seed.amalgam.toCellScheme.grade (X.leftCell b) = X.Tp.toCellScheme.grade b :=
  StageType.grade_faceCell X.restrictFace_amalgam_left b

theorem grade_donorCell (j : Fin X.D.card) :
    X.seed.amalgam.toCellScheme.grade (X.donorCell j) = X.D.toCellScheme.grade j :=
  StageType.grade_faceCell X.restrictFace_amalgam_donor j

theorem label_leftCell (b : Fin X.Tp.card) :
    X.seed.amalgam.label (X.leftCell b) = Label.reduce (blockStage ξ) (X.Tp.label b) :=
  StageType.label_faceCell X.restrictFace_amalgam_left b

theorem label_donorCell (j : Fin X.D.card) :
    X.seed.amalgam.label (X.donorCell j) = Label.reduce (blockStage ξ) (X.D.label j) :=
  StageType.label_faceCell X.restrictFace_amalgam_donor j

theorem scope_leftCell (b : Fin X.Tp.card) :
    X.seed.amalgam.toCellScheme.scope (X.leftCell b) =
      (X.Tp.toCellScheme.scope b).map (Coatom.left m) :=
  StageType.scope_faceCell X.restrictFace_amalgam_left b

theorem scope_donorCell (j : Fin X.D.card) :
    X.seed.amalgam.toCellScheme.scope (X.donorCell j) =
      (X.D.toCellScheme.scope j).map X.donorEmb :=
  StageType.scope_faceCell X.restrictFace_amalgam_donor j

theorem donorCell_injective : Function.Injective X.donorCell := fun _ _ h ↦
  Fin.cast_injective _ ((X.seed.amalgam.toScheme.cellMap X.donorEmb).injective h)

variable {γ : Ordinal.{u}} (c : MarginCapData X.Tp X.D γ)

open Classical in
/-- **The requests of the cap data** on the cells of the amalgam: the cap and the marker at their
cells, the threshold the grade of the cap, the offset `R`; `F` the new cells of `D` (those not
visible through its first points) labelled in the block of `λ_ξ`, which reduce to `⊤` at `λ_ξ`,
with the references and offsets of the data; `T` the new cells of `D` labelled `⊤`; `Z` empty.  The
old cells of `D` are read through the face `T⁺`, and the new cells labelled `⊥` or below `λ_ξ`
through the receiving family (`StageType.FirstCoatomInput.exists_isCutoffStableRecovery`). -/
noncomputable def requests : CapRequests (Fin X.seed.amalgam.card) where
  cap := X.leftCell c.cap
  N := X.Tp.toCellScheme.grade c.cap
  R := c.R
  R_lt_N := c.R_lt
  Z := ∅
  F := {d | ∃ j, (∃ n : ℕ, X.D.label j = ((blockStage ξ + n : Ordinal.{u}) : Label.{u})) ∧
    j ∉ X.D.toScheme.visibleCells Fin.castSuccEmb ∧ X.donorCell j = d}
  T := {d | ∃ j, X.D.label j = ⊤ ∧ j ∉ X.D.toScheme.visibleCells Fin.castSuccEmb ∧
    X.donorCell j = d}
  ref d := if h : ∃ j, X.donorCell j = d then X.leftCell (c.ref h.choose) else X.leftCell c.cap
  off d := if h : ∃ j, X.donorCell j = d then c.off h.choose else 0
  marker := X.leftCell c.marker

theorem requests_ref (j : Fin X.D.card) :
    (X.requests c).ref (X.donorCell j) = X.leftCell (c.ref j) := by
  have h : ∃ j', X.donorCell j' = X.donorCell j := ⟨j, rfl⟩
  simp only [requests, h, dite_true]
  rw [X.donorCell_injective h.choose_spec]

theorem requests_off (j : Fin X.D.card) : (X.requests c).off (X.donorCell j) = c.off j := by
  have h : ∃ j', X.donorCell j' = X.donorCell j := ⟨j, rfl⟩
  simp only [requests, h, dite_true]
  rw [X.donorCell_injective h.choose_spec]

/-- The grade of the cell of the cap is the grade of the cap. -/
theorem grade_requests_cap :
    X.seed.amalgam.toCellScheme.grade (X.requests c).cap = X.Tp.toCellScheme.grade c.cap :=
  X.grade_leftCell c.cap

/-- The cells of `D` have grade at most that of the cap. -/
theorem grade_donorCell_le (j : Fin X.D.card) :
    X.seed.amalgam.toCellScheme.grade (X.donorCell j) ≤ X.Tp.toCellScheme.grade c.cap := by
  rw [grade_donorCell]
  have := X.D.grade_le j
  have := c.lt_grade_cap
  omega

/-- **The requests are graded** by the grades of the amalgam. -/
theorem requests_isGraded : (X.requests c).IsGraded X.seed.amalgam.toCellScheme.grade where
  le_grade_cap := (X.grade_requests_cap c).ge
  off_le f hf := by
    obtain ⟨j, ⟨n, hn⟩, -, rfl⟩ := hf
    obtain ⟨μ, i', -, -, hoff, -⟩ := c.ref_spec j _ hn
    rw [requests_off]
    exact hoff.le
  grade_le_of_mem_Z z hz := absurd hz (Set.notMem_empty z)
  grade_le_of_mem_F f hf := by
    obtain ⟨j, -, -, rfl⟩ := hf
    rw [grade_requests_cap]
    exact X.grade_donorCell_le c j
  grade_le_of_mem_T y hy := by
    obtain ⟨j, -, -, rfl⟩ := hy
    rw [grade_requests_cap]
    exact X.grade_donorCell_le c j
  grade_ref_le f hf := by
    obtain ⟨j, ⟨n, hn⟩, -, rfl⟩ := hf
    obtain ⟨μ, i', -, -, -, -, hr, -⟩ := c.ref_spec j _ hn
    rw [requests_ref, grade_requests_cap, grade_leftCell]
    exact hr
  grade_marker_le := by
    rw [grade_requests_cap]
    exact (X.grade_leftCell c.marker).trans_le c.grade_marker_le

/-- **The glued labelling is correct**: at `λ_ξ` the cap and the marker reduce to `⊤`, the cells of
`T` are `⊤`, and the cells of `F` and their references reduce to `⊤`. -/
theorem requests_isCorrect_label : (X.requests c).IsCorrect fun d ↦ X.seed.amalgam.label d := by
  have hlim := isSuccPrelimit_blockStage ξ
  have htop {x : Label.{u}} (hx : ((blockStage ξ : Ordinal.{u}) : Label.{u}) ≤ x) :
      Label.reduce (blockStage ξ) x = ⊤ := Label.reduce_of_le hx
  have hc : X.seed.amalgam.label (X.requests c).cap = ⊤ := by
    change X.seed.amalgam.label (X.leftCell c.cap) = ⊤
    rw [label_leftCell]
    exact htop ((Label.coe_le_coe_add _ _).trans c.le_label_cap)
  have ha : X.seed.amalgam.label (X.requests c).marker = ⊤ := by
    change X.seed.amalgam.label (X.leftCell c.marker) = ⊤
    rw [label_leftCell, c.label_marker]
    exact htop (Label.coe_le_coe_add _ _)
  refine (CapRequests.isCorrect_iff_of_eq_top hc ha).mpr ⟨fun z hz ↦ absurd hz (Set.notMem_empty z),
    fun f hf ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨j, ⟨n, hn⟩, -, rfl⟩ := hf
    obtain ⟨μ, i', hμ, hon, -, -, -, hr⟩ := c.ref_spec j _ hn
    -- the block of the reference is `λ_ξ`: a smaller block would put the label below `λ_ξ`
    have hμle : blockStage ξ ≤ μ := by
      by_contra hlt
      have h1 : μ + c.off j < blockStage ξ := hlim.add_natCast_lt (not_le.mp hlt) _
      rw [← hon] at h1
      exact (self_le_add_right _ _).not_gt h1
    rw [requests_ref, requests_off, label_donorCell, label_leftCell, hn, hr,
      htop (Label.coe_le_coe_add _ _), htop (le_trans (by exact_mod_cast hμle)
        (Label.coe_le_coe_add μ i')), visibilityReplace_top]
  · obtain ⟨j, hj, -, rfl⟩ := hy
    rw [label_donorCell, hj, Label.reduce_top]

/-- **The common face carries no cell of grade at least the cap's**, from the same statement on the
cells of `T⁺` that avoid its last point. -/
theorem requests_hface
    (hface : ∀ x : Fin X.Tp.card, Fin.last m ∉ X.Tp.toCellScheme.scope x →
      X.Tp.toCellScheme.grade x < X.Tp.toCellScheme.grade c.cap) :
    ∀ x ∈ (ProfileTower.Pts : Finset (Fin (m + 2))), x ≠ Fin.last (m + 1) → ∀ d,
      X.seed.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) ∩ univ.erase x →
      X.seed.amalgam.toCellScheme.grade d < X.seed.amalgam.toCellScheme.grade (X.requests c).cap
    := by
  intro x hx hxl d hd
  have hx' : x = Fin.castSucc (Fin.last m) := by
    simp only [ProfileTower.Pts, mem_insert, mem_singleton] at hx
    exact hx.resolve_left hxl
  subst hx'
  have hvis : d ∈ X.seed.amalgam.toScheme.visibleCells (Coatom.left m) := by
    rw [Scheme.mem_visibleCells]
    intro y hy
    have hy' := (hd (mem_coe.mp hy))
    rw [mem_inter, mem_erase, mem_erase] at hy'
    exact ⟨y.castPred hy'.1.1, Fin.castSucc_castPred _ _⟩
  obtain ⟨b₀, rfl⟩ := X.seed.amalgam.toScheme.exists_faceCell_eq
    (comap_toScheme_of_restrictFace X.restrictFace_amalgam_left) hvis
  set b : Fin X.Tp.card := b₀
  change X.seed.amalgam.toCellScheme.grade (X.leftCell b) < _
  change X.seed.amalgam.toCellScheme.scope (X.leftCell b) ⊆ _ at hd
  rw [grade_requests_cap, grade_leftCell]
  refine hface b fun hb ↦ ?_
  have hm : (Fin.last m).castSucc ∈ X.seed.amalgam.toCellScheme.scope (X.leftCell b) := by
    rw [scope_leftCell]
    exact mem_map_of_mem _ hb
  have := hd hm
  simp at this

/-- The root followed by the new point misses the point `m` of the seed. -/
theorem univ_map_donorEmb_ne : univ.map X.donorEmb ≠ univ := fun he ↦ by
  have h := he ▸ mem_univ (Fin.last m).castSucc
  obtain ⟨y, -, hy⟩ := mem_map.mp h
  have hv := congrArg Fin.val hy
  induction y using Fin.lastCases with
  | last => simp at hv
  | cast y =>
    simp only [donorEmb, extendByLast_castSucc, Function.Embedding.trans_apply,
      Fin.coe_castSuccEmb, Fin.val_castSucc, Fin.val_last] at hv
    exact (X.f y).2.ne hv

/-- The face of the completion along the donor's points is `D↓λ_ξ`. -/
theorem restrictFace_completion_donor (F : CompletionBelowFullGrade X.seed) :
    restrictFace X.donorEmb (F.completion (isSuccPrelimit_blockStage ξ)) =
      some (X.D.reduce (isSuccPrelimit_blockStage ξ)) := by
  rw [donorEmb, ← extendByLast_trans, ← restrictFace_trans _ (Coatom.right m) _
    (F.restrictFace_right_completion (isSuccPrelimit_blockStage ξ)), seed_right,
    restrictFace_reduce, X.restrictFace_tb, Option.map_some]

/-- The cap of the requests has scope the private coatom `univ.erase (Fin.last (m + 1))`. -/
theorem scope_requests_cap : X.seed.amalgam.toCellScheme.scope (X.requests c).cap =
    univ.erase (Fin.last (m + 1)) := by
  change X.seed.amalgam.toCellScheme.scope (X.leftCell c.cap) = _
  rw [scope_leftCell, c.scope_cap]
  ext y
  simp only [mem_map, mem_univ, true_and, mem_erase, and_true]
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ Fin.castSucc_ne_last x, fun hy ↦ ⟨y.castPred hy, by simp⟩⟩

/-- **Cutoff stable recovery at the first coatom from the private fills** (the (R4) reading).  Let
`c` be cap data for the input (`StageType.MarginCapData`), with the cap of grade `N ≥ 3`, every cell
of `T⁺` avoiding its last point of grade below `N` (`hface`, so the common face of the seed carries
no cell of grade `N`), and the fills from the private coatom at every grade `N ≤ k' ≤ m + 1`
(`CapRequests.CapFillBotAt`, `CapRequests.CapFillPosAt`, for the requests of the data).  Then the
completion of the seed of `(T⁺↓λ_ξ, tb↓λ_ξ)` with correct rows from the grade `N`
(`Seed.exists_correctCompletion`), with the apex, carries cutoff stable recovery for `T⁺`,
`f.trans Fin.castSuccEmb`, `D` and `γ`, at a cutoff above every label of `D↓λ_ξ` other than `⊤`,
and its face along the second coatom is `tb↓λ_ξ`.  For a stage type `Q'` at `λ_{ξ+1}` on its scheme
with face `T⁺` and `Q'↓λ_ξ` in the receiving family: the old cells of `D` are read through the face
`T⁺` (`StageType.label_eq_of_mem_visibleCells`); the new cells labelled `⊥` or below `λ_ξ` through
the receiving family; those labelled in the block of `λ_ξ` exactly from their references, and those
labelled `⊤` above `γ`, through a cell of `(univ, N)` reached from the cap
(`CompletionBelowFullGrade.label_eq_of_hasAdmittedRows`,
`CompletionBelowFullGrade.lt_label_of_hasAdmittedRows`). -/
theorem exists_isCutoffStableRecovery' (hN3 : 3 ≤ X.Tp.toCellScheme.grade c.cap)
    (hdon : ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
      ProfileTower.BotLiftProvisionOf (X.requests c).IsCorrect k' (Fin.castSucc (Fin.last m)) ∧
        ProfileTower.CapLiftProvisionOf (X.requests c).IsCorrect k' (Fin.castSucc (Fin.last m)))
    (hbot : ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
      CapRequests.CapFillBotAt (X.requests c) (Fin.last (m + 1)) k')
    (hpos : ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
      CapRequests.CapFillPosAt (X.requests c) (Fin.last (m + 1)) k') :
    ∃ (q : StageType.{u} (blockStage ξ) (m + 2)) (δ : Label.{u}),
      restrictFace (extendByLast Fin.castSuccEmb) q =
          some (X.tb.reduce (isSuccPrelimit_blockStage ξ)) ∧
        X.Tp.IsCutoffStableRecovery (X.f.trans Fin.castSuccEmb) X.D γ q δ := by
  classical
  have hα := isSuccPrelimit_blockStage ξ
  have hgr := X.requests_isGraded c
  have hNm : X.Tp.toCellScheme.grade c.cap ≤ m + 1 := X.Tp.grade_le c.cap
  have hm : 2 ≤ m := by omega
  have hxp : Fin.last (m + 1) ∈ (ProfileTower.Pts : Finset (Fin (m + 2))) := by
    simp [ProfileTower.Pts]
  have hN3' : 3 ≤ X.seed.amalgam.toCellScheme.grade (X.requests c).cap := by
    rw [grade_requests_cap]
    exact hN3
  have hlab := ((X.requests_isCorrect_label c).code hgr (m + 1)).hat hgr (m + 1)
  have hdon' : ∀ x ∈ (ProfileTower.Pts : Finset (Fin (m + 2))), x ≠ Fin.last (m + 1) → ∀ k',
      X.seed.amalgam.toCellScheme.grade (X.requests c).cap ≤ k' → k' ≤ m + 1 →
        ProfileTower.BotLiftProvisionOf (X.requests c).IsCorrect k' x ∧
          ProfileTower.CapLiftProvisionOf (X.requests c).IsCorrect k' x := by
    intro x hx hxl k' hk hk'
    have hx' : x = Fin.castSucc (Fin.last m) := by
      simp only [ProfileTower.Pts, mem_insert, mem_singleton] at hx
      exact hx.resolve_left hxl
    subst hx'
    exact hdon k' (by rwa [grade_requests_cap] at hk) hk'
  obtain ⟨F, hF⟩ := X.seed.exists_correctCompletion' hm hgr hN3' hdon'
    (fun k' hk hk' ↦ hbot k' (by rwa [grade_requests_cap] at hk) hk')
    (fun k' hk hk' ↦ hpos k' (by rwa [grade_requests_cap] at hk) hk') hlab
  -- the cutoff: above every label of `D↓λ_ξ` other than `⊤`
  obtain ⟨δ₀, hδ₀, hDδ⟩ := (X.D.reduce hα).exists_lt_forall_label_lt (isSuccLimit_blockStage ξ)
  have hqD := X.restrictFace_completion_donor F
  refine ⟨F.completion hα, ((δ₀ : Ordinal.{u}) : Label.{u}), F.restrictFace_right_completion hα,
    ⟨F.isLegal_completion hα, F.restrictFace_left_completion hα⟩,
    isPermittedCutoff_coe.mpr hδ₀, ?_⟩
  intro Q' hQ' hQ'T
  obtain ⟨S, ℓ, hwf, hcod, hlaw, hat⟩ := Q'
  obtain rfl : S = (F.completion hα).toScheme := hQ'.1
  -- the labels of `Q'` at the old cells
  set w : Fin F.scheme.card → Label.{u} := fun z ↦ ℓ z.castSucc with hw_def
  have hgc := X.grade_requests_cap c
  have hw := F.isLawfulBelow_castSucc hα hlaw
    (N := X.seed.amalgam.toCellScheme.grade (X.requests c).cap) (by omega)
  have hTp (b : Fin X.Tp.card) : w (F.embed (X.leftCell b)) = X.Tp.label b := by
    rw [← label_faceCell hQ'T b]
    exact congrArg ℓ (F.cellMap_completion hα (Coatom.left m) Coatom.univ_map_left_ne rfl).symm
  -- the face of `Q'` along the donor's points
  have hfmem : univ.map X.donorEmb ∈ (F.completion hα).toCellScheme.faces :=
    ((restrictFace_eq_some_iff _ _).mp hqD).1
  set Q'' : StageType.{u} (blockStage (ξ + 1)) (m + 2) :=
    ⟨(F.completion hα).toScheme, ℓ, hwf, hcod, hlaw, hat⟩ with hQ''
  refine ⟨Q''.comap X.donorEmb hfmem, restrictFace_of_mem Q'' X.donorEmb hfmem,
    (comap_toScheme_of_restrictFace hqD :
      (F.completion hα).toScheme.comap X.donorEmb = (X.D.reduce hα).toScheme), fun i j hij ↦ ?_⟩
  have hQl : (Q''.comap X.donorEmb hfmem).label i = w (F.embed (X.donorCell j)) := by
    rw [comap_label]
    exact congrArg ℓ (F.cellMap_completion hα X.donorEmb X.univ_map_donorEmb_ne hij.symm)
  rw [hQl]
  set x := F.embed (X.donorCell j) with hx
  -- the cap and the marker in `Q'`
  have hcap : ((blockStage ξ + X.Tp.toCellScheme.grade c.cap : Ordinal.{u}) : Label.{u}) ≤
      w (F.embed (X.requests c).cap) := by
    change _ ≤ w (F.embed (X.leftCell c.cap))
    rw [hTp]
    exact c.le_label_cap
  have hlt_cap {a : ℕ} (ha : a < X.Tp.toCellScheme.grade c.cap) :
      ((blockStage ξ + a : Ordinal.{u}) : Label.{u}) < w (F.embed (X.requests c).cap) :=
    lt_of_lt_of_le (by exact_mod_cast add_lt_add_right (Nat.cast_lt.mpr ha) _) hcap
  have hjN : X.seed.amalgam.toCellScheme.grade (X.donorCell j) ≤
      X.seed.amalgam.toCellScheme.grade (X.requests c).cap := by
    rw [hgc]
    exact X.grade_donorCell_le c j
  -- the cells of `D` below `λ_ξ`: the receiving family
  have hrecv (hlt : X.D.label j < ((blockStage ξ : Ordinal.{u}) : Label.{u})) :
      w x = X.D.label j := by
    have h := hQ'.2 x.castSucc x.castSucc rfl
    have hq : (F.completion hα).label x.castSucc = X.D.label j := by
      refine (StageType.addApex_label_castSucc (t := F.truncate hα) _ _ x).trans ?_
      rw [hx, F.truncate_label_embed, label_donorCell, Label.reduce_of_lt hlt]
    have hDlt : X.D.label j < ((δ₀ : Ordinal.{u}) : Label.{u}) := by
      have h' := hDδ j
      rw [reduce_label, Label.reduce_of_lt hlt] at h'
      exact h' (ne_top_of_lt hlt)
    rw [hq, min_eq_left hDlt.le] at h
    change min (Label.reduce (blockStage ξ) (w x)) _ = _ at h
    have hr : Label.reduce (blockStage ξ) (w x) = X.D.label j := by
      rcases le_or_gt ((δ₀ : Ordinal.{u}) : Label.{u}) (Label.reduce (blockStage ξ) (w x))
        with hge | hlt'
      · rw [min_eq_right hge] at h
        exact absurd h hDlt.ne'
      · rwa [min_eq_left hlt'.le] at h
    by_cases hle : ((blockStage ξ : Ordinal.{u}) : Label.{u}) ≤ w x
    · rw [Label.reduce_of_le hle] at hr
      exact absurd hr.symm (ne_top_of_lt hlt)
    · rwa [Label.reduce_of_lt (not_le.mp hle)] at hr
  by_cases hvis : j ∈ X.D.toScheme.visibleCells Fin.castSuccEmb
  · -- an old cell: the faces of `Q'` and of `D` along the first points are both `P`
    have hQP : restrictFace Fin.castSuccEmb (Q''.comap X.donorEmb hfmem) = some X.P := by
      rw [restrictFace_trans Q'' X.donorEmb _ (restrictFace_of_mem Q'' X.donorEmb hfmem),
        donorEmb, castSuccEmb_trans_extendByLast, ← restrictFace_trans Q'' _ _ hQ'T,
        ← restrictFace_trans X.Tp _ _ X.restrictFace_Tp, X.restrictFace_p]
    have hold := label_eq_of_mem_visibleCells
      (comap_toScheme_of_restrictFace hqD : (F.completion hα).toScheme.comap X.donorEmb =
        (X.D.reduce hα).toScheme) hQP X.mem_cofaces_D.2 hij hvis
    rw [← hQl, hold]
    exact ⟨fun _ ↦ rfl, fun hj ↦ by rw [hj]; exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)⟩
  refine ⟨fun hne ↦ ?_, fun hj ↦ ?_⟩
  · rcases atStage_iff.mp (X.D.atStage j) with h | ⟨o, ho, h⟩ | h
    · exact hrecv (by rw [h]; exact WithBot.bot_lt_coe _)
    · rcases lt_or_ge o (blockStage ξ) with hlo | hle
      · exact hrecv (by rw [← h]; exact_mod_cast hlo)
      -- the block of `λ_ξ`: read exactly from the reference
      rw [blockStage_add_one] at ho
      obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hle ho
      have hnF : X.D.label j = ((blockStage ξ + n : Ordinal.{u}) : Label.{u}) := by
        rw [← h, hn]
      obtain ⟨μ, i', hμ, hon, hoff, hi', -, hrl⟩ := c.ref_spec j _ hnF
      obtain ⟨rfl, hn'⟩ :=
        (Label.add_natCast_eq_add_natCast_iff (isSuccPrelimit_blockStage ξ) hμ).mp hon
      have href : w (F.embed ((X.requests c).ref (X.donorCell j))) =
          ((blockStage ξ + i' : Ordinal.{u}) : Label.{u}) := by
        rw [requests_ref, hTp, hrl]
      have hres := CompletionBelowFullGrade.label_eq_of_hasAdmittedRows hgr hF hw
        ⟨j, ⟨n, hnF⟩, hvis, rfl⟩ hjN hμ (k := i') hi' href (href ▸ (hlt_cap hi').le)
        (by rw [requests_off]; exact hlt_cap hoff)
      rw [requests_off] at hres
      rw [hres, hnF, hn']
    · exact absurd h hne
  · exact CompletionBelowFullGrade.lt_label_of_hasAdmittedRows hgr hF hw ⟨j, hj, hvis, rfl⟩ hjN
      (isSuccPrelimit_blockStage ξ) (i := c.i) c.i_lt
      (by change w (F.embed (X.leftCell c.marker)) = _; rw [hTp, c.label_marker])
      (by
        change w (F.embed (X.leftCell c.marker)) ≤ _
        rw [hTp, c.label_marker]
        exact (hlt_cap c.i_lt).le)
      (hlt_cap c.R_lt).le (by exact_mod_cast c.lt_R)

/-- **Cutoff stable recovery at the first coatom from the private fills, under `hface`**: every
cell of `T⁺` avoiding its last point has grade below `N`, so the common face of the seed carries no
cell of grade `N` and the lift provisions from the donor coatom hold
(`CapRequests.botLiftProvisionOf_donor_le`, `CapRequests.capLiftProvisionOf_donor_le`). -/
theorem exists_isCutoffStableRecovery (hN3 : 3 ≤ X.Tp.toCellScheme.grade c.cap)
    (hface : ∀ x : Fin X.Tp.card, Fin.last m ∉ X.Tp.toCellScheme.scope x →
      X.Tp.toCellScheme.grade x < X.Tp.toCellScheme.grade c.cap)
    (hbot : ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
      CapRequests.CapFillBotAt (X.requests c) (Fin.last (m + 1)) k')
    (hpos : ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
      CapRequests.CapFillPosAt (X.requests c) (Fin.last (m + 1)) k') :
    ∃ (q : StageType.{u} (blockStage ξ) (m + 2)) (δ : Label.{u}),
      restrictFace (extendByLast Fin.castSuccEmb) q =
          some (X.tb.reduce (isSuccPrelimit_blockStage ξ)) ∧
        X.Tp.IsCutoffStableRecovery (X.f.trans Fin.castSuccEmb) X.D γ q δ := by
  have hNm : X.Tp.toCellScheme.grade c.cap ≤ m + 1 := X.Tp.grade_le c.cap
  have hm : 0 < m := by omega
  have hxp : Fin.last (m + 1) ∈ (ProfileTower.Pts : Finset (Fin (m + 2))) := by
    simp [ProfileTower.Pts]
  have hxd : Fin.castSucc (Fin.last m) ∈ (ProfileTower.Pts : Finset (Fin (m + 2))) := by
    simp [ProfileTower.Pts]
  have hne : Fin.castSucc (Fin.last m) ≠ Fin.last (m + 1) := Fin.castSucc_ne_last _
  have hf := X.requests_hface c hface (Fin.castSucc (Fin.last m)) hxd hne
  refine X.exists_isCutoffStableRecovery' c hN3 (fun k' hk hk' ↦ ?_) hbot hpos
  rw [← grade_requests_cap] at hk
  exact ⟨CapRequests.botLiftProvisionOf_donor_le hm (X.scope_requests_cap c) hk hk' hf hxp hxd
      hne (X.requests_isGraded c),
    CapRequests.capLiftProvisionOf_donor_le hm (X.requests_isGraded c) (X.scope_requests_cap c) hk
      hk' hf hxp hxd hne⟩

/-- **The fill at `⊥` when the donor follows the root**, for the requests of the cap data at a
grade `0 < k' ≤ m + 1`, when no new cell of `D` is labelled in the block of `λ_ξ` (so `F` is
empty): `CapRequests.capFillBotAt_of_donorFollowsRoot`, with the new top cells of `D` off the
private coatom (they contain the new point) and labelled `⊤` in the glued labelling.  The
hypothesis `CapRequests.DonorFollowsRoot` is open. -/
theorem capFillBotAt_requests_of_donorFollowsRoot (hm : 0 < m) {k' : ℕ} (hk : 0 < k')
    (hkm : k' ≤ m + 1)
    (hnoF : ∀ j, j ∉ X.D.toScheme.visibleCells Fin.castSuccEmb → ∀ n : ℕ,
      X.D.label j ≠ ((blockStage ξ + n : Ordinal.{u}) : Label.{u}))
    (hfol : CapRequests.DonorFollowsRoot (X.requests c) (Fin.last (m + 1))
      (Fin.castSucc (Fin.last m)) k') :
    CapRequests.CapFillBotAt (X.requests c) (Fin.last (m + 1)) k' := by
  have hcapC : X.seed.amalgam.toCellScheme.scope (X.requests c).cap ⊆
      univ.erase (Fin.last (m + 1)) := by
    change X.seed.amalgam.toCellScheme.scope (X.leftCell c.cap) ⊆ _
    rw [scope_leftCell]
    intro y hy
    obtain ⟨x, -, rfl⟩ := mem_map.mp hy
    exact mem_erase.mpr ⟨Fin.castSucc_ne_last x, mem_univ _⟩
  refine CapRequests.capFillBotAt_of_donorFollowsRoot (X.requests_isGraded c) hm
    (by simp [ProfileTower.Pts]) (by simp [ProfileTower.Pts]) (Fin.castSucc_ne_last _) hk hkm
    hcapC hfol (fun y hy ↦ ?_) (fun z hz ↦ absurd hz (Set.notMem_empty z)) ?_
  · obtain ⟨j, hj, hvis, rfl⟩ := hy
    refine ⟨by rw [label_donorCell, hj, Label.reduce_top], fun hsub ↦ hvis ?_⟩
    rw [Scheme.mem_visibleCells]
    intro y hy
    have hy' : X.donorEmb y ∈ X.seed.amalgam.toCellScheme.scope (X.donorCell j) := by
      rw [scope_donorCell]
      exact mem_map_of_mem _ hy
    have hne := (mem_erase.mp (hsub hy')).1
    induction y using Fin.lastCases with
    | last => exact absurd (by simp [donorEmb]) hne
    | cast y => exact ⟨y, rfl⟩
  · ext d
    simp only [requests, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    exact fun j ⟨n, hn⟩ hvis _ ↦ hnoF j hvis n hn

end FirstCoatomInput

end StageType

/-! ### (R4) at the first coatom from the private fills -/

namespace StageType

variable {ξ : Ordinal.{u}}

/-- **First-coatom completions for the margin calibration from the private fills** (h4 of the
receiving route, reduced to the fills).  Suppose that at every input at the first coatom
(`StageType.FirstCoatomInput`) satisfying the margin calibration, some cap data
(`StageType.MarginCapData`, which the calibration always gives,
`StageType.GradedCapMarginCalibration.nonempty_marginCapData`) has

* a cap of grade at least `3`;
* every cell of `T⁺` avoiding its last point of grade below that of the cap (`hface`: the common
  face of the seed carries no cell of the cap's grade);
* the fills from the private coatom at every grade from that of the cap to `m + 1`
  (`CapRequests.CapFillBotAt`, `CapRequests.CapFillPosAt`), for the requests of the data.

Then first-coatom completions for the margin calibration hold.  Every hypothesis is explicit; the
correctness of the glued labelling is proved
(`StageType.FirstCoatomInput.requests_isCorrect_label`), and the coatom extension property is not
used.  None of the three conditions is proved here: the
cap's grade and `hface` are conditions on the acquired context, and the fills are the open part of
the construction. -/
theorem hasCutoffFirstCoatomCompletions_of_capFills
    (h : ∀ ⦃m k : ℕ⦄ (X : FirstCoatomInput.{u} ξ m k) (γ : Ordinal.{u}), 0 < k →
      γ < blockStage (ξ + 1) →
      GradedCapMarginCalibration ξ X.Tp (X.f.trans Fin.castSuccEmb) X.D γ →
      ∃ c : MarginCapData X.Tp X.D γ, 3 ≤ X.Tp.toCellScheme.grade c.cap ∧
        (∀ x : Fin X.Tp.card, Fin.last m ∉ X.Tp.toCellScheme.scope x →
          X.Tp.toCellScheme.grade x < X.Tp.toCellScheme.grade c.cap) ∧
        ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
          CapRequests.CapFillBotAt (X.requests c) (Fin.last (m + 1)) k' ∧
            CapRequests.CapFillPosAt (X.requests c) (Fin.last (m + 1)) k') :
    HasCutoffFirstCoatomCompletions ξ (GradedCapMarginCalibration ξ) := by
  intro m k Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC
  let X : FirstCoatomInput.{u} ξ m k := ⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩
  obtain ⟨c, h3, hface, hfill⟩ := h X γ hk hγ hC
  exact X.exists_isCutoffStableRecovery c h3 hface (fun k' h₁ h₂ ↦ (hfill k' h₁ h₂).1)
    fun k' h₁ h₂ ↦ (hfill k' h₁ h₂).2

end StageType

/-! ### The margin calibration with a floor -/

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

variable (ξ) in
/-- The **margin calibration with a floor**: the margin calibration
(`StageType.GradedCapMarginCalibration`) with, for the same cap `b` of grade `N`, moreover
`3 ≤ N`, every cell of `D` of grade below `N` ((M3): `k + 1 < N`), and the offsets of the labels of
the root (the cells of `T⁺` visible through `f`) below `N` (`StageType.RootOffsetsBelow`). -/
def GradedCapMarginCalibration' ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  ∃ b : Fin Tp.card,
    ((blockStage ξ + Tp.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤ Tp.label b ∧
    k + 1 < Tp.toCellScheme.grade b ∧ 3 ≤ Tp.toCellScheme.grade b ∧
    (∃ R : ℕ, R < Tp.toCellScheme.grade b ∧ γ < blockStage ξ + R) ∧
    (∃ (a : Fin Tp.card) (i : ℕ), i < Tp.toCellScheme.grade b ∧
      Tp.toCellScheme.grade a ≤ Tp.toCellScheme.grade b ∧
      Tp.label a = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})) ∧
    (∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
      ∃ (μ : Ordinal.{u}) (n i : ℕ) (a : Fin Tp.card), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade a ≤ Tp.toCellScheme.grade b ∧
        Tp.label a = ((μ + i : Ordinal.{u}) : Label.{u})) ∧
    Tp.RootOffsetsBelow f (Tp.toCellScheme.grade b)

/-- The margin calibration with a floor is a margin calibration. -/
theorem GradedCapMarginCalibration'.gradedCapMarginCalibration
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibration' ξ Tp f D γ) : GradedCapMarginCalibration ξ Tp f D γ :=
  let ⟨b, hb, hk, _, hR, hM, href, _⟩ := h
  ⟨b, hb, by omega, hR, hM, href⟩

/-- **Cap data with a floor**: cap data (`StageType.MarginCapData`) whose cap has grade `N ≥ 3`,
above the grade `k + 1` of every cell of `D`, with the offsets of the root's labels below `N`. -/
structure FloorCapData (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (f : Fin k ↪ Fin (m + 1))
    (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) extends
    MarginCapData Tp D γ where
  /-- The cap has grade at least `3`. -/
  three_le : 3 ≤ Tp.toCellScheme.grade cap
  /-- Every cell of `D` has grade below that of the cap. -/
  succ_lt : k + 1 < Tp.toCellScheme.grade cap
  /-- The offsets of the root's labels lie below the grade of the cap. -/
  rootOffsetsBelow : Tp.RootOffsetsBelow f (Tp.toCellScheme.grade cap)

/-- **The margin calibration with a floor gives cap data with a floor**, for a legal `T⁺`:
availability moves the cap to a cell of full scope and the same grade. -/
theorem GradedCapMarginCalibration'.nonempty_floorCapData
    {Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)} {f : Fin k ↪ Fin (m + 1)}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} (hT : Tp.IsLegal)
    (h : GradedCapMarginCalibration' ξ Tp f D γ) : Nonempty (FloorCapData Tp f D γ) := by
  classical
  obtain ⟨b, hb, hk, h3, ⟨R, hR, hγ⟩, ⟨a, i, hi, ha, hal⟩, href, hoff⟩ := h
  obtain ⟨s, hs⟩ := hT.isComplete ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b)
    ⟨Tp.univ_mem_faces, show 0 < Tp.toCellScheme.grade b by omega, by
      rw [card_univ, Fintype.card_fin]
      exact Tp.grade_le b⟩
  obtain ⟨u, hu, hbu⟩ := Tp.isLawful.availability b s
    (by rw [show Tp.toCellScheme.scope s = univ from congrArg Prod.fst hs]; exact subset_univ _)
    (congrArg Prod.snd hs).symm
  have hus : Tp.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 1))),
      Tp.toCellScheme.grade b) := hu.trans hs
  have hg : Tp.toCellScheme.grade u = Tp.toCellScheme.grade b := congrArg Prod.snd hus
  have hspec (j : Fin D.card) : ∃ (r : Fin Tp.card) (n : ℕ), ∀ o : Ordinal.{u}, D.label j = o →
      ∃ (μ : Ordinal.{u}) (i' : ℕ), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i' < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade r ≤ Tp.toCellScheme.grade b ∧
        Tp.label r = ((μ + i' : Ordinal.{u}) : Label.{u}) := by
    by_cases hj : ∃ o : Ordinal.{u}, D.label j = o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨μ, n, i', r, hμ, hon, hn, hi', hr, hrl⟩ := href j o ho
      refine ⟨r, n, fun o' ho' ↦ ⟨μ, i', hμ, ?_, hn, hi', hr, hrl⟩⟩
      rw [ho] at ho'
      exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hon
    · exact ⟨b, 0, fun o ho ↦ absurd ⟨o, ho⟩ hj⟩
  choose ref off hro using hspec
  exact ⟨{ cap := u, marker := a, R := R, i := i, ref := ref, off := off
           scope_cap := congrArg Prod.fst hus
           le_label_cap := by rw [hg]; exact hb.trans hbu
           lt_grade_cap := by rw [hg]; omega
           R_lt := by rw [hg]; exact hR
           lt_R := hγ
           i_lt := by rw [hg]; exact hi
           grade_marker_le := by rw [hg]; exact ha
           label_marker := hal
           ref_spec := fun j o ho ↦ by rw [hg]; exact hro j o ho
           three_le := by rw [hg]; exact h3
           succ_lt := by rw [hg]; exact hk
           rootOffsetsBelow := by rw [hg]; exact hoff }⟩

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Acquisition of the margin calibration with a floor**: a model `R` at `λ_ξ` that is not
cover-hollow and has top-grade supremum `⊤` acquires calibrated contexts for it.  The margin
calibration is acquired at `max γ (λ_ξ + M)` with `M` above the arity of the root plus `2` and above
every offset of the root's labels (`StageType.exists_offset_bound`): its offset `R` with
`λ_ξ + M < λ_ξ + R` gives `M < R < N`; the root's labels are those of the type of the root, by
exact consistency of the candidate. -/
theorem IsModel.acquiresCalibratedContexts_gradedCapMargin' (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapMarginCalibration' ξ) R hR.isStablyLawful := by
  intro x hx D hD γ hγ
  obtain ⟨Koff, hKoff⟩ := StageType.exists_offset_bound x.type
  set M : ℕ := x.arity + 3 + Koff with hM
  have hγ' : max γ (blockStage ξ + M) < blockStage (ξ + 1) := by
    refine max_lt hγ ?_
    rw [blockStage_add_one]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 M) _
  obtain ⟨w, f, hf, b, hb, hk, ⟨R', hR', hγR⟩, hM2, href⟩ :=
    hR.acquiresCalibratedContexts_gradedCapMargin hnh hgrow x hx D hD _ hγ'
  have hMR : M < R' := by
    have h1 : blockStage ξ + (M : Ordinal.{u}) < blockStage ξ + R' :=
      (le_max_right _ _).trans_lt hγR
    exact_mod_cast (add_lt_add_iff_left _).mp h1
  have hface : StageType.restrictFace f
      (R.stableType hR.isStablyLawful w.tuple w.type w.eval_tuple) = some x.type := by
    rw [← isConsistent_stableCandidate hR.isConsistent hR.isCovering w.tuple _ f
      (stableCandidate_eval_of_eval w.eval_tuple), hf]
    exact x.eval_tuple
  refine ⟨w, f, hf, b, hb, by omega, by omega, ⟨R', hR', (le_max_left _ _).trans_lt hγR⟩, hM2,
    href, fun y hy μ f' hμ hl ↦ ?_⟩
  obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq (StageType.comap_toScheme_of_restrictFace hface) hy
  have hl' : x.type.label i = ((μ + f' : Ordinal.{u}) : Label.{u}) :=
    (StageType.label_faceCell hface i).symm.trans hl
  have := hKoff i μ f' hμ hl'
  omega

end Realization

namespace StageType

variable {ξ : Ordinal.{u}}

/-- **First-coatom completions for the margin calibration with a floor from the private fills**:
the statement of `StageType.hasCutoffFirstCoatomCompletions_of_capFills` at the calibration with a
floor (`StageType.GradedCapMarginCalibration'`), whose acquisition is compiled
(`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin'`), with the grade bound `3 ≤ N`
discharged: it is part of the cap data with a floor that the calibration gives
(`StageType.GradedCapMarginCalibration'.nonempty_floorCapData`).  The hypothesis asks, at every
calibrated input and for every cap data with a floor, the common face condition (`hface`) and the
fills from the private coatom; none is proved here. -/
theorem hasCutoffFirstCoatomCompletions'_of_capFills
    (h : ∀ ⦃m k : ℕ⦄ (X : FirstCoatomInput.{u} ξ m k) (γ : Ordinal.{u}), 0 < k →
      γ < blockStage (ξ + 1) →
      GradedCapMarginCalibration' ξ X.Tp (X.f.trans Fin.castSuccEmb) X.D γ →
      ∀ c : FloorCapData X.Tp (X.f.trans Fin.castSuccEmb) X.D γ,
        (∀ x : Fin X.Tp.card, Fin.last m ∉ X.Tp.toCellScheme.scope x →
          X.Tp.toCellScheme.grade x < X.Tp.toCellScheme.grade c.cap) ∧
        ∀ k', X.Tp.toCellScheme.grade c.cap ≤ k' → k' ≤ m + 1 →
          CapRequests.CapFillBotAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) k' ∧
            CapRequests.CapFillPosAt (X.requests c.toMarginCapData) (Fin.last (m + 1)) k') :
    HasCutoffFirstCoatomCompletions ξ (GradedCapMarginCalibration' ξ) := by
  intro m k Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC
  let X : FirstCoatomInput.{u} ξ m k := ⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩
  obtain ⟨c⟩ := hC.nonempty_floorCapData hT
  obtain ⟨hface, hfill⟩ := h X γ hk hγ hC c
  exact X.exists_isCutoffStableRecovery c.toMarginCapData c.three_le hface
    (fun k' h₁ h₂ ↦ (hfill k' h₁ h₂).1) fun k' h₁ h₂ ↦ (hfill k' h₁ h₂).2

end StageType

end VaughtConjecture

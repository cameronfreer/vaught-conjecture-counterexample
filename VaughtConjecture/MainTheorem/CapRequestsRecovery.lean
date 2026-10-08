/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsGrade
import VaughtConjecture.MainTheorem.CutoffCoatomRelabel

/-!
# Cutoff stable recovery from a correct completion

Roadmap, Layer 4, output 3 of higher-stage reconstruction, and Layer 3, 3.3–3.4 ((R4) of the
table of Layer 3: the reading through a proper cap, at the seed of the first coatom).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

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

theorem donorCell_injective : Function.Injective X.donorCell := fun _ _ h ↦
  Fin.cast_injective _ ((X.seed.amalgam.toScheme.cellMap X.donorEmb).injective h)

variable {γ : Ordinal.{u}} (c : MarginCapData X.Tp X.D γ)

open Classical in
/-- **The requests of the cap data** on the cells of the amalgam: the cap and the marker at their
cells, the threshold the grade of the cap, the offset `R`; `F` the cells of `D` labelled in the
block of `λ_ξ` (they reduce to `⊤` at `λ_ξ`), with the references and offsets of the data; `T` the
cells of `D` labelled `⊤`; `Z` empty.  The cells of `D` labelled `⊥` or below `λ_ξ` are read through
the receiving family instead (`StageType.FirstCoatomInput.exists_isCutoffStableRecovery`). -/
noncomputable def requests : CapRequests (Fin X.seed.amalgam.card) where
  cap := X.leftCell c.cap
  N := X.Tp.toCellScheme.grade c.cap
  R := c.R
  R_lt_N := c.R_lt
  Z := ∅
  F := {d | ∃ j, (∃ n : ℕ, X.D.label j = ((blockStage ξ + n : Ordinal.{u}) : Label.{u})) ∧
    X.donorCell j = d}
  T := {d | ∃ j, X.D.label j = ⊤ ∧ X.donorCell j = d}
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
    obtain ⟨j, ⟨n, hn⟩, rfl⟩ := hf
    obtain ⟨μ, i', -, -, hoff, -⟩ := c.ref_spec j _ hn
    rw [requests_off]
    exact hoff.le
  grade_le_of_mem_Z z hz := absurd hz (Set.notMem_empty z)
  grade_le_of_mem_F f hf := by
    obtain ⟨j, -, rfl⟩ := hf
    rw [grade_requests_cap]
    exact X.grade_donorCell_le c j
  grade_le_of_mem_T y hy := by
    obtain ⟨j, -, rfl⟩ := hy
    rw [grade_requests_cap]
    exact X.grade_donorCell_le c j
  grade_ref_le f hf := by
    obtain ⟨j, ⟨n, hn⟩, rfl⟩ := hf
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
  · obtain ⟨j, ⟨n, hn⟩, rfl⟩ := hf
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
  · obtain ⟨j, hj, rfl⟩ := hy
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

end FirstCoatomInput

end StageType

end VaughtConjecture

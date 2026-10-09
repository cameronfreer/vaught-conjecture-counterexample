/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeDecoder
import VaughtConjecture.Continuation.AvailableTopDeterminationCounterexample

/-!
# A seed on three points with an apex: a test below the top grade

Roadmap, Layer 3 ((R3) and (R4), the context lift at a grade below the top grade), a second test
input beside `VaughtConjecture.MainTheorem.ReplicatedTieInstance` (whose grade `2` is the top
grade `m + 1`).

**The input** (namespace `ApexInstance`): at a limit stage `α`, the legal type
`AvailableTopDeterminationCounterexample.topType α` on three points (`m = 2`), whose apex, of
graded index `(univ, 3)`, is labelled `⊤`; its face on `{0, 1}` is `pairFace α`
(`topType_mem_cofaces`); the root `{0}` (`Fin.castSuccEmb : Fin 1 ↪ Fin 2`), with the face
`pointFace α`; the donor `pairFace α`, a legal coface of it (`pairFace_mem_cofaces`).  The seed
exists by `StageType.exists_growthSeed_of_isSuccLimit` (`ApexInstance.exists_seed`).

**The test at the grade `2 < m + 1 = 3`** (`ApexInstance.not_isLawful_orbitCode_two`): the
compressed labelling of the attachment is lawful and positive at the apex, of grade `3`; its orbit
code at the grade `2` is not lawful (`Seed.not_isLawful_orbitCode_of_grade_lt`).  So the rendering
lemma, which asks full lawfulness of the coded state, does not apply to orbit codes below the top
grade at this input, while at the top grade it does (`Seed.isLawful_orbitCode_top`).

**Requests below the top grade** (`ApexInstance.req`): over the donor labelled `⊥`
(`ApexInstance.bareDonor`, the scheme of `pairFace α`, a legal coface of `pointFace α`, which is
labelled `⊥`; its seed exists, `ApexInstance.exists_seed_bare`), the cap and the marker are the
cell of `topType α` at `(univ, 2)`, labelled `⊤`, so the threshold is `2 < m + 1 = 3`; every donor
cell is a bottom request.  The labels pair is admitted (`correctAt_req`), the requests are
calibrated on the class (`classCalibrated_req`; the root cells have grade `1`), and the relative
lift on the exact class holds (`hasRelativeLiftOnClass_req`, by
`StageType.GrowthRequests.hasRelativeLiftOnClass_of_bottoms`; the root cells are labelled `⊥`).
The donor `pairFace α` itself carries `⊤` at its cell `({0, 1}, 2)`, which a bottom request under
the cap `⊤` excludes.

## References

Lawful sections are [Kni26, Definition 2.5.4]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType AvailableTopDeterminationCounterexample

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- **The seed position of the input exists**: a seed with first coatom type `topType α` whose
donor face along the root followed by the new point is `pairFace α`. -/
theorem exists_seed {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) :
    ∃ I : Seed.{u} α 2, I.left = topType α ∧
      restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam = some (pairFace α) :=
  exists_growthSeed_of_isSuccLimit hα isLegal_topType topType_mem_cofaces.2 restrictFace_pairFace
    pairFace_mem_cofaces

/-- The apex of `topType α`: a cell of graded index `(univ, 3)` labelled `⊤`. -/
theorem exists_apex (α : Ordinal.{u}) : ∃ d : Fin (topType α).card,
    (topType α).toCellScheme.gradedIndex d = ((univ : Finset (Fin 3)), 3) ∧
      (topType α).label d = ⊤ := by
  obtain ⟨d, hd, hmax⟩ : ∃ d, (topType α).toCellScheme.gradedIndex d =
      ((univ : Finset (Fin 3)), 3) ∧ ∀ e, (topType α).label e ≤ (topType α).label d :=
    exists_apex_addApex _ _
  refine ⟨d, hd, top_le_iff.mp ?_⟩
  have := hmax (Fin.last _)
  exact (addApex_label_last _ _ : (topType α).label (Fin.last _) = ⊤) ▸ this

/-- The test below the top grade, for the first coatom type given up to equality. -/
theorem not_isLawful_orbitCode_two_aux {α : Ordinal.{u}} {I : Seed.{u} α 2}
    {t' : StageType.{u} α 3} (hI : I.left = t') {d : Fin t'.card}
    (hd : t'.toCellScheme.gradedIndex d = ((univ : Finset (Fin 3)), 3)) (hl : t'.label d = ⊤) :
    (I.attachment 𝕘).rows.IsLawful (I.compressedLabel 𝕘) ∧
      ¬ (I.attachment 𝕘).rows.IsLawful (orbitCode 2 (I.compressedLabel 𝕘)) := by
  subst hI
  refine ⟨Seed.isLawful_compressedLabel (I := I) (g := 𝕘), Seed.not_isLawful_orbitCode_of_grade_lt
    (d := I.attachCtxCell 𝕘 d) ?_ ?_⟩
  · rw [Seed.grade_attachCtxCell, show I.left.toCellScheme.grade d = 3 from
      congrArg Prod.snd hd]
    omega
  · have hmem := Seed.label_mem_attachLabels (I := I) (g := 𝕘) (I.attachCtxCell 𝕘 d)
    intro h
    have h0 := (blockCompress_eq_bot_iff hmem (2 + 2)).mp h
    have hl' : (I.attachmentType 𝕘).label (I.attachCtxCell 𝕘 d) = ⊤ :=
      (label_faceCell (I.restrictFace_left_attachmentType 𝕘) d).trans hl
    rw [hl'] at h0
    exact top_ne_bot h0

/-- **The orbit code at the grade `2` is not lawful at this input** (`m = 2`, so `2 < m + 1`): at
every seed of the input the compressed labelling of the attachment is lawful, positive at the
apex of grade `3`, and its orbit code at `2` is not lawful. -/
theorem not_isLawful_orbitCode_two {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α) :
    (I.attachment 𝕘).rows.IsLawful (I.compressedLabel 𝕘) ∧
      ¬ (I.attachment 𝕘).rows.IsLawful (orbitCode 2 (I.compressedLabel 𝕘)) := by
  obtain ⟨d, hd, hl⟩ := exists_apex α
  exact not_isLawful_orbitCode_two_aux hI hd hl

/-! ### Bottom requests with the cap at a cell of grade `2` -/

/-- **The donor labelled `⊥`**: the face on `{0, 1}` with every label `⊥`. -/
noncomputable def bareDonor (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := (pairFace α).toScheme
  label _ := ⊥
  isWellFormed := (pairFace α).isWellFormed
  isCoded := (pairFace α).isCoded
  isLawful := CellScheme.Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- The donor labelled `⊥` is a legal coface of the face on `{0}`: that face is labelled `⊥`. -/
theorem bareDonor_mem_cofaces {α : Ordinal.{u}} : bareDonor α ∈ (pointFace α).cofaces := by
  refine ⟨isLegal_pairFace, ?_⟩
  rw [← restrictFace_pairFace]
  refine restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨y, rfl⟩ := exists_faceCell_eq (restrictFace_pairFace (α := α)) hi
  exact (label_pointFace y).symm.trans (label_faceCell _ y).symm

/-- The root face of `topType α` along `{0}` is the face on `{0}`. -/
theorem restrictFace_root {α : Ordinal.{u}} :
    restrictFace ((𝕘).trans Fin.castSuccEmb) (topType α) = some (pointFace α) :=
  (restrictFace_trans (topType α) _ _ topType_mem_cofaces.2).symm.trans restrictFace_pairFace

/-- **The seed position with the donor labelled `⊥` exists**: a seed with first coatom type
`topType α` whose donor face along the root followed by the new point is `bareDonor α`. -/
theorem exists_seed_bare {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) :
    ∃ I : Seed.{u} α 2, I.left = topType α ∧
      restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam = some (bareDonor α) :=
  exists_growthSeed_of_isSuccLimit hα isLegal_topType topType_mem_cofaces.2 restrictFace_pairFace
    bareDonor_mem_cofaces

variable (α : Ordinal.{u})

/-- **The bottom requests** with the cap and the marker at the cell of `topType α` at
`(univ, 2)`, labelled `⊤`: the threshold is `2`, below the top grade `3`. -/
noncomputable def req : GrowthRequests (topType α) (bareDonor α).toScheme where
  cap := fullTwoCell α
  marker := fullTwoCell α
  markerOffset := 0
  bottoms := Set.univ
  exacts := ∅
  highs := ∅
  ref _ := fullTwoCell α
  offset _ := 0

theorem threshold_req : (req α).threshold = 2 :=
  congrArg Prod.snd (gradedIndex_fullTwoCell (α := α))

theorem correctAt_req (j : Fin (bareDonor α).card) :
    (req α).CorrectAt (topType α).label j ((bareDonor α).label j) :=
  ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (Set.notMem_empty _),
    fun h ↦ absurd h (Set.notMem_empty _)⟩

theorem classCalibrated_req : (req α).ClassCalibrated (restrictFace_root (α := α)) where
  cover _ := .inl (Set.mem_univ _)
  scope_cap := congrArg Prod.fst (gradedIndex_fullTwoCell (α := α))
  label_cap := by
    rw [show (req α).cap = fullTwoCell α from rfl, label_fullTwoCell]; exact top_ne_bot
  ref _ h := absurd h (Set.notMem_empty _)
  marker := ⟨(threshold_req α).ge, Nat.zero_le _, by
    rw [show (req α).marker = fullTwoCell α from rfl, label_fullTwoCell]; exact top_ne_bot⟩
  root i := by
    rw [grade_faceCell, threshold_req]
    exact ((pointFace α).grade_le i).trans (by omega)
  arity := (threshold_req α).ge

/-- The context is `⊥` at the root cells: the face on `{0}` is labelled `⊥`. -/
theorem label_root (i : Fin (pointFace α).card) :
    (topType α).label ((topType α).faceCell (restrictFace_root (α := α)) i) = ⊥ :=
  (label_faceCell _ i).trans (label_pointFace i)

theorem hasRelativeLiftOnClass_req :
    (req α).HasRelativeLiftOnClass (restrictFace_root (α := α)) bareDonor_mem_cofaces.2 :=
  GrowthRequests.hasRelativeLiftOnClass_of_bottoms _ _ (classCalibrated_req α)
    (fun _ ↦ Set.mem_univ _) (fun _ h ↦ Set.notMem_empty _ h) (fun _ h ↦ Set.notMem_empty _ h)
    (label_root α) isLegal_pairFace Nat.one_pos

end ApexInstance

end VaughtConjecture

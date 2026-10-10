/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelSupport
import VaughtConjecture.Extension.PartBelowFullGrade

/-!
# The re-rendered levels at an input on four points, below its top grade

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**Cells of full scope at every grade** (`StageType.exists_gradedIndex_univ_of_isLegal`): a legal
stage type on `n` points has a cell of graded index `(univ, k)` for every `1 ≤ k ≤ n`
(completeness).  So the hypothesis `hX` of `Seed.lvLevel_cappedLift` holds at every seed, its
first coatom type being legal (`Seed.exists_gradedIndex_univ_left`), and the chain lemma asks no
relation between the threshold and the grades (`Seed.lvLevel_cappedLift'`).  Its premises at the
seed position stay explicit until their proof is composed there: requests calibrated on the class
(`hQ`), the labels pair correct (`hpair`), the relative lift on the class (`hrel`), a legal donor
(`hdL`) and `0 < n`.

**The input** (namespace `QuadInstance`, at a limit stage `α`, `m = 3`):
* the first coatom type `quadType hα` on four points: a legal one-point extension of
  `AvailableTopDeterminationCounterexample.topType α` (with face `topType α` along its first three
  points; `StageType.exists_pinned_extension_of_isSuccPrelimit`), cut below its full grade and
  with the apex added (`StageType.addApex`): legal, with face `topType α` along the first three
  points, and its apex of graded index `(univ, 4)` labelled `⊤`;
* the root `{0}` (the face `pointFace α`), the donor `ApexInstance.bareDonor α` labelled `⊥`; the
  seed exists (`QuadInstance.exists_seed`);
* the bottom requests `QuadInstance.req hα` with the cap and the marker at the apex: threshold
  `4 = m + 1`, the top grade.

**The test below the top grade** (`QuadInstance.lvLevel_cappedLift_quad`): at every seed of the
input, the level at every grade `j + 1 ≤ 4` lifts capped from the context coatom into
`(univ, j + 1)`.  At the grade `3` the composition runs with the threshold `4` strictly above the
grade (`QuadInstance.lvLevel_cappedLift_grade_three`).

**Grades above the threshold.**  With the cap at a cell of `quadType hα` at `(univ, 3)` labelled
`⊤` (`QuadInstance.reqLow`, threshold `3`), the level at every grade `j + 1 ≤ 4` lifts, the grade
`4` above the threshold (`QuadInstance.lvLevel_cappedLift_reqLow`); likewise at the apex input
with the cap at `(univ, 2)` (`ApexInstance.req`, threshold `2`) at every grade `j + 1 ≤ 3`
(`ApexInstance.lvLevel_cappedLift_req`).

## References

Lawful sections and bountifulness are [Kni26, Definitions 2.5.4 and 2.5.14]; the growth
construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType AvailableTopDeterminationCounterexample

/-- The chain lemma for a first coatom type given up to equality. -/
theorem Seed.lvLevel_cappedLift_of_eq {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m}
    {t' : StageType.{u} α (m + 1)} (hI : I.left = t') {g : Fin n ↪ Fin m}
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p₀}
    {d : StageType.{u} α (n + 1)} (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hdL : d.IsLegal) (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ y, Q.CorrectAt t'.label y (d.label y))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp) {H B : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 1 → (I.lvLevel g H B hdA (hI ▸ Q) j).S.rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j + 1)) (Y := ((univ : Finset (Fin (m + 2))), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  subst hI
  exact Seed.lvLevel_cappedLift' hH hcard hte hdp hdL hn hdA hQ hpair hrel hB

namespace QuadInstance

/-- The root of the input, the point `0` of the first three points. -/
abbrev root : Fin 1 ↪ Fin 3 := (Fin.castSuccEmb : Fin 1 ↪ Fin 2).trans Fin.castSuccEmb

/-- The root of the input. -/
local notation "𝕘" => root

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

include hα in
/-- A legal one-point extension of `topType α` with face `topType α` along its first three
points. -/
theorem exists_base : ∃ Q : StageType.{u} α 4, Q.IsLegal ∧
    restrictFace Fin.castSuccEmb Q = some (topType α) := by
  obtain ⟨Q, hQ, hQP, -⟩ := StageType.exists_pinned_extension_of_isSuccPrelimit hα.isSuccPrelimit
    isLegal_topType (f := (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) topType_mem_cofaces.2
    isLegal_topType topType_mem_cofaces.2
  exact ⟨Q, hQ, hQP⟩

/-- The extension of `topType α` on four points. -/
noncomputable def base : StageType.{u} α 4 := (exists_base hα).choose

theorem isLegal_base : (base hα).IsLegal := (exists_base hα).choose_spec.1

/-- **The first coatom type of the input**: the extension cut below its full grade, with the
apex added. -/
noncomputable def quadType : StageType.{u} α 4 :=
  (base hα).partBelowFullGrade.addApex
    ((isLegal_base hα).isLegalBelowFullGrade_partBelowFullGrade) (by omega)

theorem isLegal_quadType : (quadType hα).IsLegal := isLegal_addApex _ _

/-- The first three points do not cover the four points. -/
theorem map_castSuccEmb_ne_univ' :
    univ.map (Fin.castSuccEmb : Fin 3 ↪ Fin 4) ≠ univ := fun h ↦ by
  have h' := mem_univ (Fin.last 3)
  rw [← h, mem_map] at h'
  obtain ⟨i, -, hi⟩ := h'
  exact (Fin.castSucc_lt_last i).ne hi

/-- The face of `quadType hα` along its first three points is `topType α`. -/
theorem restrictFace_quadType :
    restrictFace Fin.castSuccEmb (quadType hα) = some (topType α) := by
  rw [quadType, restrictFace_addApex _ _ _ map_castSuccEmb_ne_univ',
    restrictFace_partBelowFullGrade _ _ map_castSuccEmb_ne_univ']
  exact (exists_base hα).choose_spec.2

/-- The root face of `quadType hα` is the face on `{0}`. -/
theorem restrictFace_root_quad :
    restrictFace ((𝕘).trans Fin.castSuccEmb) (quadType hα) = some (pointFace α) :=
  (restrictFace_trans _ _ _ (restrictFace_quadType hα)).symm.trans ApexInstance.restrictFace_root

/-- **The seed position of the input exists**: a seed with first coatom type `quadType hα` whose
donor face along the root followed by the new point is the donor labelled `⊥`. -/
theorem exists_seed : ∃ I : Seed.{u} α 3, I.left = quadType hα ∧
    restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α) :=
  exists_growthSeed_of_isSuccLimit hα (isLegal_quadType hα) (restrictFace_quadType hα)
    ApexInstance.restrictFace_root ApexInstance.bareDonor_mem_cofaces

/-- The apex of `quadType hα`. -/
noncomputable def apex : Fin (quadType hα).card := Fin.last _

theorem gradedIndex_apex :
    (quadType hα).toCellScheme.gradedIndex (apex hα) = ((univ : Finset (Fin 4)), 4) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

theorem label_apex : (quadType hα).label (apex hα) = ⊤ := addApex_label_last _ _

/-- **The bottom requests with the cap at the apex**: threshold `4 = m + 1`, the top grade. -/
noncomputable def req : GrowthRequests (quadType hα) (ApexInstance.bareDonor α).toScheme where
  cap := apex hα
  marker := apex hα
  markerOffset := 0
  bottoms := Set.univ
  exacts := ∅
  highs := ∅
  ref _ := apex hα
  offset _ := 0

theorem threshold_req : (req hα).threshold = 4 :=
  congrArg Prod.snd (gradedIndex_apex hα)

theorem correctAt_req (j : Fin (ApexInstance.bareDonor α).card) :
    (req hα).CorrectAt (quadType hα).label j ((ApexInstance.bareDonor α).label j) :=
  ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (Set.notMem_empty _),
    fun h ↦ absurd h (Set.notMem_empty _)⟩

theorem classCalibrated_req : (req hα).ClassCalibrated (restrictFace_root_quad hα) where
  cover _ := .inl (Set.mem_univ _)
  scope_cap := congrArg Prod.fst (gradedIndex_apex hα)
  label_cap := by
    rw [show (req hα).cap = apex hα from rfl, label_apex]; exact top_ne_bot
  ref _ h := absurd h (Set.notMem_empty _)
  marker := ⟨le_rfl, Nat.zero_le _, by
    rw [show (req hα).marker = apex hα from rfl, label_apex]; exact top_ne_bot⟩
  root i := by
    rw [grade_faceCell, threshold_req]
    exact ((pointFace α).grade_le i).trans (by omega)
  arity := by rw [threshold_req]; omega

/-- The context is `⊥` at the root cells: the face on `{0}` is labelled `⊥`. -/
theorem label_root (i : Fin (pointFace α).card) :
    (quadType hα).label ((quadType hα).faceCell (restrictFace_root_quad hα) i) = ⊥ :=
  (label_faceCell _ i).trans (label_pointFace i)

theorem hasRelativeLiftOnClass_req :
    (req hα).HasRelativeLiftOnClass (restrictFace_root_quad hα)
      ApexInstance.bareDonor_mem_cofaces.2 :=
  GrowthRequests.hasRelativeLiftOnClass_of_bottoms _ _ (classCalibrated_req hα)
    (fun _ ↦ Set.mem_univ _) (fun _ h ↦ Set.notMem_empty _ h) (fun _ h ↦ Set.notMem_empty _ h)
    (label_root hα) isLegal_pairFace Nat.one_pos

/-- **The context lift of the re-rendered levels at the input on four points**: at every seed of
the input, for the requests `req hα` (threshold `4 = m + 1`) and every height `H` and block bound
`B` with `2 · #cells ≤ B`, the level at the grade `j + 1 ≤ 4` lifts capped from the context
coatom into `(univ, j + 1)`. -/
theorem lvLevel_cappedLift_quad (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∀ j, j + 1 ≤ 4 → (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) j).S.rows.CappedLift
      (X := (univ.erase (Fin.last 4), j + 1)) (Y := ((univ : Finset (Fin 5)), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ :=
  Seed.lvLevel_cappedLift_of_eq hI (hte := restrictFace_root_quad hα)
    ApexInstance.bareDonor_mem_cofaces.2 ApexInstance.bareDonor_mem_cofaces.1 Nat.one_pos hdA
    (correctAt_req hα) (classCalibrated_req hα) (hasRelativeLiftOnClass_req hα) hH hcard hB

/-- **The grade `3` below the top grade `4`**: at every seed of the input, the level at the grade
`3` lifts capped from the context coatom into `(univ, 3)`, the threshold `4` lying strictly above
the grade. -/
theorem lvLevel_cappedLift_grade_three (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    (req hα).threshold = 4 ∧ (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 2).S.rows.CappedLift
      (X := (univ.erase (Fin.last 4), 3)) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨erase_subset _ _, le_rfl⟩ :=
  ⟨threshold_req hα, lvLevel_cappedLift_quad hα I hI hdA hH hcard hB 2 (by omega)⟩

/-! ### A lower cap at the input on four points -/

/-- A cell of `quadType hα` of graded index `(univ, 3)` labelled `⊤`: above the apex of
`topType α`, a face cell of grade `3` labelled `⊤` (completeness and availability,
`StageType.exists_gradedIndex_univ_le_label`). -/
theorem exists_capLow : ∃ c : Fin (quadType hα).card,
    (quadType hα).toCellScheme.gradedIndex c = ((univ : Finset (Fin 4)), 3) ∧
      (quadType hα).label c = ⊤ := by
  obtain ⟨c, hc, hle⟩ := exists_gradedIndex_univ_le_label (isLegal_quadType hα)
    ((quadType hα).faceCell (restrictFace_quadType hα) (ApexInstance.apex α))
  rw [label_faceCell, ApexInstance.label_apex] at hle
  refine ⟨c, ?_, top_le_iff.mp hle⟩
  rw [hc, grade_faceCell]
  exact congrArg (Prod.mk _) (congrArg Prod.snd (ApexInstance.gradedIndex_apex α))

/-- The cell of `quadType hα` at `(univ, 3)` labelled `⊤`. -/
noncomputable def capLow : Fin (quadType hα).card := (exists_capLow hα).choose

/-- **The bottom requests with a lower cap**: cap and marker at `capLow hα`, threshold `3`, below
the top grade `4`. -/
noncomputable def reqLow : GrowthRequests (quadType hα) (ApexInstance.bareDonor α).toScheme where
  cap := capLow hα
  marker := capLow hα
  markerOffset := 0
  bottoms := Set.univ
  exacts := ∅
  highs := ∅
  ref _ := capLow hα
  offset _ := 0

theorem threshold_reqLow : (reqLow hα).threshold = 3 :=
  congrArg Prod.snd (exists_capLow hα).choose_spec.1

theorem correctAt_reqLow (j : Fin (ApexInstance.bareDonor α).card) :
    (reqLow hα).CorrectAt (quadType hα).label j ((ApexInstance.bareDonor α).label j) :=
  ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (Set.notMem_empty _),
    fun h ↦ absurd h (Set.notMem_empty _)⟩

theorem classCalibrated_reqLow : (reqLow hα).ClassCalibrated (restrictFace_root_quad hα) where
  cover _ := .inl (Set.mem_univ _)
  scope_cap := congrArg Prod.fst (exists_capLow hα).choose_spec.1
  label_cap := by
    rw [show (reqLow hα).cap = capLow hα from rfl, capLow, (exists_capLow hα).choose_spec.2]
    exact top_ne_bot
  ref _ h := absurd h (Set.notMem_empty _)
  marker := ⟨le_rfl, Nat.zero_le _, by
    rw [show (reqLow hα).marker = capLow hα from rfl, capLow, (exists_capLow hα).choose_spec.2]
    exact top_ne_bot⟩
  root i := by
    rw [grade_faceCell, threshold_reqLow]
    exact ((pointFace α).grade_le i).trans (by omega)
  arity := by rw [threshold_reqLow]; omega

theorem hasRelativeLiftOnClass_reqLow :
    (reqLow hα).HasRelativeLiftOnClass (restrictFace_root_quad hα)
      ApexInstance.bareDonor_mem_cofaces.2 :=
  GrowthRequests.hasRelativeLiftOnClass_of_bottoms _ _ (classCalibrated_reqLow hα)
    (fun _ ↦ Set.mem_univ _) (fun _ h ↦ Set.notMem_empty _ h) (fun _ h ↦ Set.notMem_empty _ h)
    (label_root hα) isLegal_pairFace Nat.one_pos

/-- **Grades above the threshold at the input on four points**: for the requests `reqLow hα`
(threshold `3`), at every seed of the input the level at every grade `j + 1 ≤ 4` lifts capped
from the context coatom into `(univ, j + 1)`; at the grade `4` the grade lies above the
threshold. -/
theorem lvLevel_cappedLift_reqLow (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    (reqLow hα).threshold = 3 ∧ ∀ j, j + 1 ≤ 4 →
      (I.lvLevel 𝕘 H B hdA (hI ▸ reqLow hα) j).S.rows.CappedLift
        (X := (univ.erase (Fin.last 4), j + 1)) (Y := ((univ : Finset (Fin 5)), j + 1))
        ⟨erase_subset _ _, le_rfl⟩ :=
  ⟨threshold_reqLow hα, Seed.lvLevel_cappedLift_of_eq hI (hte := restrictFace_root_quad hα)
    ApexInstance.bareDonor_mem_cofaces.2 ApexInstance.bareDonor_mem_cofaces.1 Nat.one_pos hdA
    (correctAt_reqLow hα) (classCalibrated_reqLow hα) (hasRelativeLiftOnClass_reqLow hα) hH hcard
    hB⟩

/-- **The grade `4` strictly above the threshold `3`** at the input on four points. -/
theorem lvLevel_cappedLift_reqLow_four (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    (reqLow hα).threshold < 4 ∧ (I.lvLevel 𝕘 H B hdA (hI ▸ reqLow hα) 3).S.rows.CappedLift
      (X := (univ.erase (Fin.last 4), 4)) (Y := ((univ : Finset (Fin 5)), 4))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨h3, hl⟩ := lvLevel_cappedLift_reqLow hα I hI hdA hH hcard hB
  exact ⟨by omega, hl 3 le_rfl⟩

end QuadInstance

namespace ApexInstance

/-- **Grades above the threshold at the apex input**: for the requests `req α` with the cap at
the cell of `topType α` at `(univ, 2)` (threshold `2`, below the top grade `3`), at every seed of
the input the level at every grade `j + 1 ≤ 3` lifts capped from the context coatom into
`(univ, j + 1)`; at the grade `3` the grade lies above the threshold. -/
theorem lvLevel_cappedLift_req {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast (((Fin.castSuccEmb : Fin 1 ↪ Fin 2)).trans
      Fin.castSuccEmb)) I.amalgam = some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase Fin.castSuccEmb).S.card ≤ H)
    (hB : 2 * (I.attachment (Fin.castSuccEmb : Fin 1 ↪ Fin 2)).card ≤ B) :
    (req α).threshold = 2 ∧ ∀ j, j + 1 ≤ 3 →
      (I.lvLevel Fin.castSuccEmb H B hdA (hI ▸ req α) j).S.rows.CappedLift
        (X := (univ.erase (Fin.last 3), j + 1)) (Y := ((univ : Finset (Fin 4)), j + 1))
        ⟨erase_subset _ _, le_rfl⟩ :=
  ⟨threshold_req α, Seed.lvLevel_cappedLift_of_eq hI (hte := restrictFace_root)
    bareDonor_mem_cofaces.2 bareDonor_mem_cofaces.1 Nat.one_pos hdA (correctAt_req α)
    (classCalibrated_req α) (hasRelativeLiftOnClass_req α) hH hcard hB⟩

/-- **The grade `3` strictly above the threshold `2`** at the apex input. -/
theorem lvLevel_cappedLift_req_three {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast (((Fin.castSuccEmb : Fin 1 ↪ Fin 2)).trans
      Fin.castSuccEmb)) I.amalgam = some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase Fin.castSuccEmb).S.card ≤ H)
    (hB : 2 * (I.attachment (Fin.castSuccEmb : Fin 1 ↪ Fin 2)).card ≤ B) :
    (req α).threshold < 3 ∧ (I.lvLevel Fin.castSuccEmb H B hdA (hI ▸ req α) 2).S.rows.CappedLift
      (X := (univ.erase (Fin.last 3), 3)) (Y := ((univ : Finset (Fin 4)), 3))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨h2, hl⟩ := lvLevel_cappedLift_req I hI hdA hH hcard hB
  exact ⟨by omega, hl 2 le_rfl⟩

end ApexInstance

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelChain
import VaughtConjecture.MainTheorem.ReplicatedApexInstance

/-!
# The re-rendered levels at the two test inputs

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

* **The apex input at its top grade `3`** (`ApexInstance.lvLevel_cappedLift_three`): with the
  requests `ApexInstance.reqTop` (cap and marker at the apex of `topType α`, of graded index
  `(univ, 3)`, labelled `⊤`; every donor cell a bottom request over the donor labelled `⊥`;
  threshold `3 = m + 1`, above the arity `n + 1 = 2`), the level at the grade `3` lifts capped from
  the context coatom into `(univ, 3)`, and so does the level at the grade `2` into `(univ, 2)`
  (`Seed.lvLevel_cappedLift`, the context cells at `(univ, 2)` and `(univ, 3)` being
  `fullTwoCell α` and the apex).
* **The tie input at its top grade `2`** (`TieInstance.lvLevel_cappedLift_two`): with the requests
  `req ω` (threshold `2 = n + 1 = m + 1`, the equality boundary), the level at the grade `2` lifts
  capped from the context coatom into `(univ, 2)`.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType AvailableTopDeterminationCounterexample
open scoped Ordinal

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- The apex of `topType α`. -/
noncomputable def apex (α : Ordinal.{u}) : Fin (topType α).card := (exists_apex α).choose

theorem gradedIndex_apex (α : Ordinal.{u}) :
    (topType α).toCellScheme.gradedIndex (apex α) = ((univ : Finset (Fin 3)), 3) :=
  (exists_apex α).choose_spec.1

theorem label_apex (α : Ordinal.{u}) : (topType α).label (apex α) = ⊤ :=
  (exists_apex α).choose_spec.2

variable (α : Ordinal.{u})

/-- **The bottom requests with the cap at the apex**: threshold `3`, the top grade. -/
noncomputable def reqTop : GrowthRequests (topType α) (bareDonor α).toScheme where
  cap := apex α
  marker := apex α
  markerOffset := 0
  bottoms := Set.univ
  exacts := ∅
  highs := ∅
  ref _ := apex α
  offset _ := 0

theorem threshold_reqTop : (reqTop α).threshold = 3 :=
  congrArg Prod.snd (gradedIndex_apex α)

theorem correctAt_reqTop (j : Fin (bareDonor α).card) :
    (reqTop α).CorrectAt (topType α).label j ((bareDonor α).label j) :=
  ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (Set.notMem_empty _),
    fun h ↦ absurd h (Set.notMem_empty _)⟩

theorem classCalibrated_reqTop : (reqTop α).ClassCalibrated (restrictFace_root (α := α)) where
  cover _ := .inl (Set.mem_univ _)
  scope_cap := congrArg Prod.fst (gradedIndex_apex α)
  label_cap := by
    rw [show (reqTop α).cap = apex α from rfl, label_apex]; exact top_ne_bot
  ref _ h := absurd h (Set.notMem_empty _)
  marker := ⟨le_rfl, Nat.zero_le _, by
    rw [show (reqTop α).marker = apex α from rfl, label_apex]; exact top_ne_bot⟩
  root i := by
    rw [grade_faceCell, threshold_reqTop]
    exact ((pointFace α).grade_le i).trans (by omega)
  arity := by rw [threshold_reqTop]; omega

theorem hasRelativeLiftOnClass_reqTop :
    (reqTop α).HasRelativeLiftOnClass (restrictFace_root (α := α)) bareDonor_mem_cofaces.2 :=
  GrowthRequests.hasRelativeLiftOnClass_of_bottoms _ _ (classCalibrated_reqTop α)
    (fun _ ↦ Set.mem_univ _) (fun _ h ↦ Set.notMem_empty _ h) (fun _ h ↦ Set.notMem_empty _ h)
    (label_root α) isLegal_pairFace Nat.one_pos

/-- The context lift of the levels at the input, for the first coatom type given up to equality. -/
theorem lvLevel_cappedLift_aux {I : Seed.{u} α 2} {t' : StageType.{u} α 3} (hI : I.left = t')
    {p : StageType.{u} α 1} {hte : restrictFace ((𝕘).trans Fin.castSuccEmb) t' = some p}
    {d : StageType.{u} α 2} (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B)
    (hX : ∀ k, 2 ≤ k → k ≤ 3 → ∃ x : Fin t'.card,
      t'.toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), k)) :
    ∀ j, j + 1 ≤ 3 → (I.lvLevel 𝕘 H B hdA (hI ▸ Q) j).S.rows.CappedLift
      (X := (univ.erase (Fin.last 3), j + 1)) (Y := ((univ : Finset (Fin 4)), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  subst hI
  exact Seed.lvLevel_cappedLift hH hcard hte hdp hdL Nat.one_pos hdA hQ hpair hrel hB hX

/-- **The context lift of the re-rendered levels at the apex input** (top grade `3`): at every
seed of the input, for the requests `reqTop α` and every height `H` and block bound `B` with
`2 · #cells ≤ B`, the level at the grade `j + 1` lifts capped from the context coatom into
`(univ, j + 1)`, for `j + 1 ≤ 3`; in particular at the grade `3`. -/
theorem lvLevel_cappedLift_three {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∀ j, j + 1 ≤ 3 → (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) j).S.rows.CappedLift
      (X := (univ.erase (Fin.last 3), j + 1)) (Y := ((univ : Finset (Fin 4)), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ :=
  lvLevel_cappedLift_aux α hI (hte := restrictFace_root) bareDonor_mem_cofaces.2
    bareDonor_mem_cofaces.1 hdA (correctAt_reqTop α) (classCalibrated_reqTop α)
    (hasRelativeLiftOnClass_reqTop α) hH hcard hB fun k hk2 hk3 ↦ by
      obtain rfl | rfl : k = 2 ∨ k = 3 := by omega
      · exact ⟨fullTwoCell α, gradedIndex_fullTwoCell⟩
      · exact ⟨apex α, gradedIndex_apex α⟩

end ApexInstance

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- The context lift of the levels at the input, for the first coatom type given up to equality. -/
theorem lvLevel_cappedLift_aux {α : Ordinal.{u}} {I : Seed.{u} α 1} {t' : StageType.{u} α 2}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕣).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B)
    (hX : ∃ x : Fin t'.card, t'.toCellScheme.gradedIndex x = ((univ : Finset (Fin 2)), 2)) :
    ∀ j, j + 1 ≤ 2 → (I.lvLevel 𝕣 H B hdA (hI ▸ Q) j).S.rows.CappedLift
      (X := (univ.erase (Fin.last 2), j + 1)) (Y := ((univ : Finset (Fin 3)), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  subst hI
  exact Seed.lvLevel_cappedLift hH hcard hte hdp hdL Nat.one_pos hdA hQ hpair hrel hB
    fun k hk2 hk ↦ by obtain rfl : k = 2 := by omega
                      exact hX

/-- **The context lift of the re-rendered levels at the tie input** (top grade `2`, threshold
`2 = n + 1`): at every seed of the input, the level at the grade `2` lifts capped from the
context coatom into `(univ, 2)`. -/
theorem lvLevel_cappedLift_two (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B) :
    ∀ j, j + 1 ≤ 2 → (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) j).S.rows.CappedLift
      (X := (univ.erase (Fin.last 2), j + 1)) (Y := ((univ : Finset (Fin 3)), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ :=
  lvLevel_cappedLift_aux hI (hte := restrictFace_ctx_root ω) (don_mem_cofaces ω).2
    (don_mem_cofaces ω).1 hdA (correctAt_req ω) (classCalibrated_req ω)
    (hasRelativeLiftOnClass_req ω) hH hcard hB ⟨cellR.{u} ω, rfl⟩

end TieInstance

end VaughtConjecture

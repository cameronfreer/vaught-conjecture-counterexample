/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedAssembly
import VaughtConjecture.Extension.ReplicatedTieReading
import VaughtConjecture.Continuation.SourceGapSeparationObstruction

/-!
# The context lift at the seed position fails at a legal two-point context

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme at the seed position).

`StageType.HasContextLiftAtSeed H Γ B'` asks the context lift at EVERY seed position, so one seed
position refutes it.  **Generically** (`StageType.not_hasContextLiftAtSeed_of_pair`): at one seed
position, for a choice meeting the side conditions there (`0 < H`, `#cells ≤ H`,
`Γ ≤ gridPoint 2 B'`, the code set inside `Γ`), a lawful section of the context with two positive
values `⊥ < u' x₂ < u' x₁` at cells of one grade `2 ≤ k ≤ m + 1` refutes it
(`Seed.not_cappedLift_context_of_section_pair`).

**The relative lift for bottom requests**
(`StageType.GrowthRequests.hasRelativeLiftOnClass_of_bottoms`): requests with every donor cell a
bottom request, no exact or high request, and the context labelled `⊥` at the root cells have the
relative lift on the exact class over a legal donor with a nonempty root.

**The instance** (namespace `TieInstance`), at the stage `ω`, `m = n = 1`:

* the context `ctx`: the legal scheme `SeparationObstruction.S` on two points (cells `y` at
  `({0}, 1)`, `e` at `({1}, 1)`, `z` at `(univ, 1)`, `o` and `r` at `(univ, 2)`), labelled `⊤` at
  `r` and `⊥` elsewhere (lawful by `SeparationObstruction.isLawful_lab`); its first coatom face
  `pt` on the point `0`; the root `Function.Embedding.refl (Fin 1)`, with the same face;
* the donor `don`: the same scheme labelled `⊥`, a legal coface of `pt` (`don_mem_cofaces`, the
  labels agree at the cells visible on the point `0`);
* the requests `req`: cap and marker `r`, every donor cell a bottom request; the labels pair is
  admitted (`correctAt_req`), they are calibrated on the class (`classCalibrated_req`, threshold
  `2 = n + 1`), with the relative lift on the exact class (`hasRelativeLiftOnClass_req`);
* the section `sep`: `ω + 3` at `y`, `z`, `o` and `3` at `r`, lawful.

The seed is that of `StageType.exists_growthSeed_of_isSuccLimit`.  **Conclusions**
(`StageType.not_hasContextLiftAtSeed_seedChoice`, `StageType.not_towerExtensionAtSeed_seedChoice`,
`StageType.not_towerExtensionPosAtSeed_seedChoice`): at the choice of the assembly
(`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`) the context lift, the extension over
the tower and its case at a positive cap at the seed position are false, in every universe.  So
the hypotheses `hctx` of `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_seedLifts` and
`hE` of `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_towerExtension` and
`…_of_towerExtensionPos` are false.  This says nothing about the main theorem or about
`StageType.HasReplicatedInputsAtSeed` (some seed and some choice per seed position).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace StageType.GrowthRequests

variable {α : Ordinal.{u}} {n k : ℕ} {t' : StageType.{u} α k} {p : StageType.{u} α n}
  {e : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
  (hte : restrictFace e t' = some p) (hdp : restrictFace Fin.castSuccEmb d = some p)

/-- **The relative lift on the exact class for bottom requests**: if every donor cell is a bottom
request and none is an exact or a high request, and the context is labelled `⊥` at the root cells,
then requests calibrated on the class over a legal donor with a nonempty root have the relative
lift on the exact class.  On the class the root cells are `⊥` (they lie below the cap), so the
bottom donor section is allowed, and it keeps every old donor section at the cap (on the class at
a positive cap the old section is `⊥`); off the class the root lift suffices. -/
theorem hasRelativeLiftOnClass_of_bottoms {Q : GrowthRequests t' d.toScheme}
    (hQ : Q.ClassCalibrated hte) (hb : ∀ j, j ∈ Q.bottoms) (hex : ∀ j, j ∉ Q.exacts)
    (hhi : ∀ j, j ∉ Q.highs) (hroot : ∀ i, t'.label (t'.faceCell hte i) = ⊥) (hd : d.IsLegal)
    (hn : 0 < n) : Q.HasRelativeLiftOnClass hte hdp := by
  intro u u' v γ hall hu' hγ hag
  obtain ⟨hu, hv, hroot', hadm⟩ := hall
  by_cases hin : (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      u' x = ⊥ ↔ t'.label x = ⊥) ∧ u' Q.cap ≠ ⊥
  swap
  · obtain ⟨v', hv', hv'r, hv'c⟩ := StageType.IsLegal.exists_rootLift hd hn hdp hv
      (isLawful_root hte hu') (hγ.mono hQ.arity) (fun i ↦ by rw [hroot' i, hag])
    exact ⟨v', ⟨hu', hv', hv'r, fun h hc ↦ absurd ⟨h, hc⟩ hin⟩, hv'c⟩
  obtain ⟨hcls, hcb⟩ := hin
  have hcorr (s : Fin t'.card → Label.{u}) (j : Fin d.card) : Q.CorrectAt s j ⊥ :=
    ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (hex j), fun h ↦ absurd h (hhi j)⟩
  refine ⟨fun _ ↦ ⊥, ⟨hu', CellScheme.Rows.isLawful_const_bot, fun i ↦ ?_,
    fun _ _ j ↦ hcorr u' j⟩, fun j ↦ ?_⟩
  · exact ((hcls _ (Q.mem_below_cap hQ.scope_cap (hQ.root i))).mpr (hroot i)).symm
  · by_cases hγb : γ = ⊥
    · rw [hγb, min_bot_right, min_bot_right]
    · have hcor := hadm (fun x hx ↦ (eq_bot_iff_of_min_eq (hag x) hγb).symm.trans (hcls x hx))
        (fun h0 ↦ hcb ((eq_bot_iff_of_min_eq (hag Q.cap) hγb).mpr h0)) j
      have hc0 : u Q.cap ≠ ⊥ := fun h0 ↦ hcb ((eq_bot_iff_of_min_eq (hag Q.cap) hγb).mpr h0)
      rw [eq_bot_of_correctAt hcor (hb j) hc0]

end StageType.GrowthRequests

namespace StageType

/-- **The context lift at the seed position fails at a lawful context section with two values at
one grade**: for a choice `H`, `Γ`, `B'` meeting the side conditions at ONE seed position (a limit
stage, a seed with the context as its first coatom type, a root, a legal coface, requests with the
labels pair admitted, calibrated on the class and with the relative lift on the exact class), a
lawful section `u'` of the context with `⊥ < u' x₂ < u' x₁` at two cells of one grade
`2 ≤ k ≤ m + 1` refutes `StageType.HasContextLiftAtSeed H Γ B'`
(`Seed.not_cappedLift_context_of_section_pair` at the grade `k`). -/
theorem not_hasContextLiftAtSeed_of_pair
    {H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u}}
    {B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) {n m : ℕ} (I : Seed.{u} α m)
    (g : Fin n ↪ Fin m) {t' : StageType.{u} α (m + 1)} (hI : I.left = t')
    {p' : StageType.{u} α m} (hp' : restrictFace Fin.castSuccEmb t' = some p')
    {p : StageType.{u} α n} (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ p.cofaces)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (hn : 0 < n) {Q : GrowthRequests t' d.toScheme}
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2)
    (hH : 0 < H I g) (hcard : (I.attachmentBase g).S.card ≤ H I g)
    (hΓ : ∀ x ∈ Γ I g, x ≤ gridPoint 2 (B' I g))
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ I g)
    {u' : Fin t'.card → Label.{u}} (hu' : t'.rows.IsLawful u') {k : ℕ} (hk2 : 2 ≤ k)
    (hkm : k ≤ m + 1) {x₁ x₂ : Fin t'.card} (hx₁ : t'.toCellScheme.grade x₁ = k)
    (hx₂ : t'.toCellScheme.grade x₂ = k) (h20 : u' x₂ ≠ ⊥) (h21 : u' x₂ < u' x₁) :
    ¬ HasContextLiftAtSeed.{u} H Γ B' := by
  intro h
  subst hI
  exact Seed.not_cappedLift_context_of_section_pair hH hcard hΓ hΓc hte hd.2 hdA hQ hpair hrel hu'
    hk2 hkm hx₁ hx₂ h20 h21
    (h I g p' hα I.isLegal_left hp' p hte d hd hdA hn Q hpair hQ hrel k hk2 hkm)

end StageType

namespace TieInstance

open SeparationObstruction

/-- The label `β + n`. -/
noncomputable abbrev labelAdd (β : Ordinal.{u}) (n : ℕ) : Label.{u} :=
  ((β + (n : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

variable (α : Ordinal.{u})

/-- **The context**: the legal scheme `SeparationObstruction.S` on two points labelled `⊥` except
at the cell `r` of graded index `(univ, 2)`, labelled `⊤`. -/
noncomputable def ctx : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊥ ⊥ ⊤
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_bot 1) (isSelfVisible_bot 2) (isSelfVisible_top 2)
    le_rfl rfl
  atStage d := by fin_cases d <;> simp [lab]

/-- **The donor**: the same scheme labelled `⊥`. -/
noncomputable def don : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊥ ⊥ ⊥
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_bot 1) (isSelfVisible_bot 2) (isSelfVisible_bot 2)
    le_rfl rfl
  atStage d := by fin_cases d <;> simp [lab]

theorem map_castSuccEmb_mem_faces :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (ctx α).toCellScheme.faces := by
  change univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ cells.faces
  decide

/-- The face of the context on the point `0`. -/
noncomputable def pt : StageType.{u} α 1 := (ctx α).comap _ (map_castSuccEmb_mem_faces α)

theorem restrictFace_ctx : restrictFace Fin.castSuccEmb (ctx α) = some (pt α) :=
  restrictFace_of_mem _ _ _

theorem refl_trans_castSuccEmb :
    (Function.Embedding.refl (Fin 1)).trans (Fin.castSuccEmb : Fin 1 ↪ Fin 2) =
      Fin.castSuccEmb := by
  ext; rfl

theorem restrictFace_ctx_root :
    restrictFace ((Function.Embedding.refl (Fin 1)).trans Fin.castSuccEmb) (ctx α) =
      some (pt α) := by
  rw [refl_trans_castSuccEmb]; exact restrictFace_ctx α

/-- The donor is a legal coface of the face on the point `0`: its labels agree with those of the
context at the cells visible on that point. -/
theorem don_mem_cofaces : don α ∈ (pt α).cofaces := by
  refine ⟨isLegal_S, ?_⟩
  rw [← restrictFace_ctx α]
  refine restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  have hvis : ∀ i : Fin 5, i ∈ S.{u}.visibleCells (Fin.castSuccEmb : Fin 1 ↪ Fin 2) → i ≠ 4 := by
    decide
  have h4 := hvis i hi
  fin_cases i <;> first | exact absurd rfl h4 | rfl

/-- The cell `r`. -/
abbrev cellR : Fin (ctx α).card := ⟨4, show 4 < 5 by omega⟩

/-- The cell `o`. -/
abbrev cellO : Fin (ctx α).card := ⟨3, show 3 < 5 by omega⟩

/-- **The bottom requests** with the cap and the marker at `r`. -/
noncomputable def req : GrowthRequests (ctx α) (don α).toScheme where
  cap := cellR α
  marker := cellR α
  markerOffset := 0
  bottoms := Set.univ
  exacts := ∅
  highs := ∅
  ref _ := cellR α
  offset _ := 0

theorem threshold_req : (req α).threshold = 2 := rfl

theorem label_cellR : (ctx α).label (cellR α) = ⊤ := rfl

theorem correctAt_req (j : Fin (don α).card) :
    (req α).CorrectAt (ctx α).label j ((don α).label j) := by
  have h : (don α).label j = ⊥ := by
    change lab ⊥ ⊥ ⊥ j = ⊥
    fin_cases j <;> rfl
  rw [h]
  exact ⟨fun _ ↦ min_eq_left bot_le, fun h ↦ absurd h (Set.notMem_empty _),
    fun h ↦ absurd h (Set.notMem_empty _)⟩

theorem classCalibrated_req : (req α).ClassCalibrated (restrictFace_ctx_root α) where
  cover _ := .inl (Set.mem_univ _)
  scope_cap := rfl
  label_cap := by rw [show (req α).cap = cellR α from rfl, label_cellR]; exact top_ne_bot
  ref _ h := absurd h (Set.notMem_empty _)
  marker := ⟨le_rfl, Nat.zero_le _, by
    rw [show (req α).marker = cellR α from rfl, label_cellR]; exact top_ne_bot⟩
  root _ := (ctx α).grade_le _
  arity := le_rfl

/-- The context is `⊥` at the root cells: they have scope inside `{0}`, so they are not `r`. -/
theorem label_root (i : Fin (pt α).card) :
    (ctx α).label ((ctx α).faceCell (restrictFace_ctx_root α) i) = ⊥ := by
  have hs := (ctx α).scope_faceCell (restrictFace_ctx_root α) i
  generalize (ctx α).faceCell (restrictFace_ctx_root α) i = c at hs ⊢
  have hsub : (ctx α).toCellScheme.scope c ≠ univ := by
    rw [hs, refl_trans_castSuccEmb]
    intro h
    have h1 := h ▸ mem_univ (1 : Fin 2)
    obtain ⟨a, -, ha⟩ := mem_map.mp h1
    exact absurd ha (by decide +revert)
  have key : ∀ c : Fin 5, cells.scope c ≠ univ → c ≠ 3 ∧ c ≠ 4 := by decide
  obtain ⟨h3, h4⟩ := key c hsub
  change lab ⊥ ⊥ ⊤ c = ⊥
  fin_cases c <;> first | exact absurd rfl h3 | exact absurd rfl h4 | rfl

theorem hasRelativeLiftOnClass_req :
    (req α).HasRelativeLiftOnClass (restrictFace_ctx_root α) (don_mem_cofaces α).2 :=
  GrowthRequests.hasRelativeLiftOnClass_of_bottoms _ _ (classCalibrated_req α)
    (fun _ ↦ Set.mem_univ _) (fun _ h ↦ Set.notMem_empty _ h) (fun _ h ↦ Set.notMem_empty _ h)
    (label_root α) isLegal_S Nat.one_pos

/-- **The section separating `o` and `r`**: `ω + 3` at the cells `y`, `z`, `o` and `3` at `r`. -/
noncomputable def sep : Fin (ctx α).card → Label.{u} :=
  lab (labelAdd ω 3) (labelAdd ω 3) (labelAdd 0 3)

theorem isLawful_sep : (ctx α).rows.IsLawful (sep α) :=
  isLawful_lab (isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega))
    (isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega))
    (isSelfVisible_coe_add Order.isSuccPrelimit_bot (by omega)) le_rfl rfl

end TieInstance

namespace StageType

open TieInstance

/-- **The context lift at the seed position fails at the choice of the assembly**
(`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`): at the stage `ω`, the seed of
`StageType.exists_growthSeed_of_isSuccLimit` over the context `TieInstance.ctx` (the legal
two-point scheme `SeparationObstruction.S`, labelled `⊤` at one cell of graded index `(univ, 2)`
and `⊥` elsewhere), the root `{0}`, the donor `TieInstance.don` (the same scheme labelled `⊥`),
and the bottom requests `TieInstance.req`, together with the lawful section `TieInstance.sep`
(`ω + 3` and `3` at the two cells of graded index `(univ, 2)`), refute it
(`StageType.not_hasContextLiftAtSeed_of_pair`). -/
theorem not_hasContextLiftAtSeed_seedChoice :
    ¬ HasContextLiftAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound := by
  have hα : Order.IsSuccLimit (ω : Ordinal.{u}) := Ordinal.isSuccLimit_omega0
  have hp : restrictFace (Function.Embedding.refl (Fin 1)) (pt ω) = some (pt ω) :=
    (restrictFace_trans (ctx ω) _ _ (restrictFace_ctx ω)).trans (restrictFace_ctx_root ω)
  obtain ⟨I, hI, hdA⟩ := exists_growthSeed_of_isSuccLimit hα (t' := ctx ω)
    SeparationObstruction.isLegal_S
    (restrictFace_ctx ω) hp (don_mem_cofaces ω)
  refine not_hasContextLiftAtSeed_of_pair hα I (Function.Embedding.refl (Fin 1)) hI
    (restrictFace_ctx ω) (restrictFace_ctx_root ω) (don_mem_cofaces ω) hdA Nat.one_pos
    (correctAt_req ω) (classCalibrated_req ω) (hasRelativeLiftOnClass_req ω)
    (I.seedHeight_pos _) (I.card_le_seedHeight _) (fun _ hx ↦ I.le_gridPoint_of_mem_seedValues _ hx)
    (I.codeSet_subset_seedValues _) (isLawful_sep ω) le_rfl le_rfl (x₁ := cellO.{u} ω)
    (x₂ := cellR.{u} ω) rfl rfl WithBot.coe_ne_bot ?_
  change labelAdd 0 3 < labelAdd ω 3
  rw [labelAdd, labelAdd, zero_add, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  exact (Ordinal.natCast_lt_omega0 3).trans_le le_self_add

/-- **The extension over the tower at the seed position fails at the choice of the assembly**: it
gives the context lift (`StageType.hasContextLiftAtSeed_of_towerExtension`). -/
theorem not_towerExtensionAtSeed_seedChoice :
    ¬ TowerExtensionAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound := fun hE ↦
  not_hasContextLiftAtSeed_seedChoice (hasContextLiftAtSeed_of_towerExtension
    Seed.seedHeight_pos Seed.card_le_seedHeight Seed.bot_mem_seedValues hE)

/-- **The extension over the tower at a positive cap at the seed position fails at the choice of
the assembly**: it gives the extension (`StageType.towerExtensionAtSeed_of_pos`). -/
theorem not_towerExtensionPosAtSeed_seedChoice :
    ¬ TowerExtensionPosAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound := fun hE ↦
  not_towerExtensionAtSeed_seedChoice (towerExtensionAtSeed_of_pos Seed.seedHeight_pos
    Seed.card_le_seedHeight (fun I g _ hx ↦ I.le_gridPoint_of_mem_seedValues g hx)
    Seed.codeSet_subset_seedValues hE)

end StageType

end VaughtConjecture

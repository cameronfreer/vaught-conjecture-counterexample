/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedAssembly
import VaughtConjecture.Extension.ReplicatedTieReading
import VaughtConjecture.Extension.RepairedTieLift
import VaughtConjecture.Continuation.SourceGapSeparationObstruction

/-!
# The tie input at the seed position: a standing test of the agreement heights

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme at the seed position).

**The input** (namespace `TieInstance`; stage `ω`, `m = n = 1`, every premise of
`StageType.HasContextLiftAtSeed` instantiated):

* the stage `ω`, a limit (`Ordinal.isSuccLimit_omega0`);
* the first coatom type `ctx ω`: the legal scheme `SeparationObstruction.S` on two points (cells
  `y` at `({0}, 1)`, `e` at `({1}, 1)`, `z` at `(univ, 1)`, `o` and `r` at `(univ, 2)`), labelled
  `⊤` at `r` and `⊥` elsewhere; its face on the point `0` is `pt ω` (`restrictFace_ctx`);
* the root `Function.Embedding.refl (Fin 1)`, with the face `pt ω` (`restrictFace_ctx_root`);
* the donor `don ω`: the same scheme labelled `⊥`, a legal coface of `pt ω`
  (`don_mem_cofaces`), the face of the amalgam of the seed (`exists_seed`, from
  `StageType.exists_growthSeed_of_isSuccLimit`);
* `0 < n = 1`;
* the requests `req ω`: cap and marker `r`, every donor cell a bottom request; the labels pair is
  admitted (`correctAt_req`), they are calibrated on the class (`classCalibrated_req`, threshold
  `2 = n + 1`), with the relative lift on the exact class (`hasRelativeLiftOnClass_req`, by
  `StageType.GrowthRequests.hasRelativeLiftOnClass_of_bottoms`);
* the grade `2 ∈ [2, m + 1]`; the lawful context section `sep ω` (`ω + 3` at `y`, `z`, `o`, `3`
  at `r`).  In the refutation over the grid alone (below) the positive cap was `3` (self-visible at
  `2`), the prescription the decoded writing of the code of the admitted completion of `sep ω`
  shifted by one block, the ambient the writing of the positive constant `3` on its support, with
  the capped agreement below the context coatom.

`repairedContextLift_of_hasContextLiftAtSeed` compiles the instantiation: the context lift at
the seed position, at the choice of the assembly, gives the lift at this input.

**Old scheme (agreement heights in the grid alone): refuted.**  At commit `86a30a0` (branch
`research/port-growth-pos-test`) this module compiled, with the tower of that commit,

    theorem StageType.not_hasContextLiftAtSeed_seedChoice :
        ¬ HasContextLiftAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound

(and `not_towerExtensionAtSeed_seedChoice`, `not_towerExtensionPosAtSeed_seedChoice`), by the tie
of `o` and `r` at the code value `3`, strictly inside the block `0` of the grid at `2`.  The base
lane replaced the grid by the height set in `Scheme.LadderBaseData.ladderTower` itself
(`Scheme.heightSet`, research/port-growth `5edcc2e`); the grid-only tower is no longer a value of
the definitions (the height set is not a parameter of the tower, of `Seed.attachTower` or of
`Seed.replicated`), so the old refutation is not restated here.  Making both reachable side by
side needs one parameter (the height function) threaded through the ladder tower, the attachment
tower and the replicated scheme; that is a change to the base files, left to the base lane.

**The old counterexample mechanism is eliminated** (`TieInstance.not_pin_cellR`, from
`Seed.not_pin_of_grade`): the tied value is a value of a state of the catalogue at a cell of grade
`2`, hence self-visible at `2` and a height of the repaired scheme; no cell of grade `2` is pinned
below it.

**The repaired lift at the old input: proved** (`TieInstance.exists_lift_of_tie`, from
`Seed.exists_lift_of_tie`): at every seed of the input, at the choice of the assembly, for every
complete lawful admitted state (the admitted completion of `sep ω` among them), the cap `3`, the
tie ambient and every code of the shifted state as prescription, a lift below `(univ, 2)` exists.
The two steps asked first: **separation** (`TieInstance.tieValue_mem_heightSet`,
`TieInstance.exists_cell_le_tieValue`: the cap `3` is a height at the grade `2`, and the cell of
the reading state at `(univ, 2)` carries the tie's writing at a value at least `3`) and
**compatibility** (`TieInstance.ladderTower_lawful_isCoded`: the tower with the height sets is
consistent, lawful on the catalogue and coded at the choice).  The cap is the code value `3` of
`Γ`: no value outside the values of the choice is used.

**The repaired context lift at every input of the seed: open** (`TieInstance.RepairedContextLift`,
a `Prop`): the context lift at the grade `2` at every seed of this input, at the choice of the
assembly, for every cap, prescription and ambient.  It is the extension over the tower at a
positive cap at the grades `1` and `2` for this seed (`Seed.TowerExtensionPos`), the general open
step specialized to `m = n = 1`; not proved here.

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

/-- **The context lift at the seed position read at one seed position**, with the first coatom
type given up to equality (the requests transported along it). -/
theorem cappedLift_of_hasContextLiftAtSeed
    {H : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    {Γ : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → Finset Label.{u}}
    {B' : ∀ {α : Ordinal.{u}} {m n : ℕ}, Seed.{u} α m → (Fin n ↪ Fin m) → ℕ}
    (h : HasContextLiftAtSeed.{u} H Γ B') {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) {n m : ℕ}
    (I : Seed.{u} α m) (g : Fin n ↪ Fin m) {t' : StageType.{u} α (m + 1)} (hI : I.left = t')
    {p' : StageType.{u} α m} (hp' : restrictFace Fin.castSuccEmb t' = some p')
    {p : StageType.{u} α n} (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ p.cofaces)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) (j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m + 1) :
    (I.replicated g (H I g) (Γ I g) (I.attachAdmits g hdA (hI ▸ Q)) (B' I g)).rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨erase_subset _ _, le_rfl⟩ := by
  subst hI
  exact h I g p' hα I.isLegal_left hp' p hte d hd hdA hn Q hpair hQ hrel j hj hjm

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


namespace TieInstance

/-- **The seed position of the input exists**: a seed with first coatom type `ctx ω` whose donor
face along the root followed by the new point is `don ω`
(`StageType.exists_growthSeed_of_isSuccLimit`). -/
theorem exists_seed :
    ∃ I : Seed.{u} ω 1, I.left = ctx ω ∧
      restrictFace (extendByLast ((Function.Embedding.refl (Fin 1)).trans Fin.castSuccEmb))
        I.amalgam = some (don ω) :=
  exists_growthSeed_of_isSuccLimit Ordinal.isSuccLimit_omega0 (t' := ctx ω)
    SeparationObstruction.isLegal_S
    (restrictFace_ctx ω) ((restrictFace_trans (ctx ω) _ _ (restrictFace_ctx ω)).trans
      (restrictFace_ctx_root ω)) (don_mem_cofaces ω)

/-- **The context lift of the repaired scheme at the input** (open; the statement to be proved,
the local check of the repair): at every seed with first coatom type `ctx ω` and donor `don ω`,
with the root `{0}` and the requests `req`, the replicated scheme at the choice of the assembly
(`Seed.seedHeight`, `Seed.seedValues`, `Seed.seedGridBound`; agreement heights in
`Scheme.heightSet`) lifts capped from the context coatom into the full face at the grade `2`. -/
def RepairedContextLift : Prop :=
  ∀ (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((Function.Embedding.refl (Fin 1)).trans Fin.castSuccEmb))
      I.amalgam = some (don ω)),
    (I.replicated (Function.Embedding.refl (Fin 1))
        (I.seedHeight (Function.Embedding.refl (Fin 1)))
        (I.seedValues (Function.Embedding.refl (Fin 1)))
        (I.attachAdmits (Function.Embedding.refl (Fin 1)) hdA (hI ▸ req ω))
        (I.seedGridBound (Function.Embedding.refl (Fin 1)))).rows.CappedLift
      (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩

/-- **Every premise of the context lift at the seed position is instantiated by the input**: the
context lift at the seed position at the choice of the assembly gives the context lift of the
repaired scheme at the input (stage `ω` a limit, the first coatom type legal with its face on the
point `0`, the root with that face, the donor a legal coface of it and the face of the amalgam,
`0 < n`, the labels pair admitted, calibration on the class, the relative lift on the exact class,
the grade `2` in `[2, m + 1]`). -/
theorem repairedContextLift_of_hasContextLiftAtSeed
    (h : HasContextLiftAtSeed.{u} Seed.seedHeight Seed.seedValues Seed.seedGridBound) :
    RepairedContextLift.{u} := fun I hI hdA ↦
  cappedLift_of_hasContextLiftAtSeed h Ordinal.isSuccLimit_omega0 I _ hI (restrictFace_ctx ω)
    (restrictFace_ctx_root ω) (don_mem_cofaces ω) hdA Nat.one_pos (req ω) (correctAt_req ω)
    (classCalibrated_req ω) (hasRelativeLiftOnClass_req ω) 2 le_rfl le_rfl

/-- **The old tie is no pin of the repaired scheme**: the ambient of the refutation over the grid
alone tied the cells `o` and `r`, of the grade `2`, at a value of the catalogue; every such value is
self-visible at `2`, a height, so no cell at `(univ, 2)` is pinned below it
(`Seed.not_pin_of_grade`). -/
theorem not_pin_cellR {I : Seed.{u} ω 1} {Γ : Finset Label.{u}} {B' : ℕ}
    {A : ℕ → (Fin (I.attachmentBase (Function.Embedding.refl (Fin 1))).S.card → Label.{u}) → Prop}
    {K : ℕ} {R' : Fin (I.attachment (Function.Embedding.refl (Fin 1))).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase (Function.Embedding.refl (Fin 1))).towerCat Γ A K)
    {a : Fin (I.attachment (Function.Embedding.refl (Fin 1))).card}
    (ha : (I.attachment (Function.Embedding.refl (Fin 1))).toCellScheme.grade a = 2)
    {σ : Label.{u} → Label.{u}} {c : Label.{u}} (hc : c ≤ σ (R' a)) :
    ¬ ∀ x ∈ Scheme.heightSet Γ B' 2, c ≤ σ x → R' a < x :=
  Seed.not_pin_of_grade hR' ha hc

/-! ### The repaired scheme at the tie input -/

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- **Separation at the input** (the cap is a height): the cap `3 = Seed.tieValue 1` of the tie
input lies in the code set, so in the values of the choice, and is self-visible at `2`; it is a
height at the grade `2`. -/
theorem tieValue_mem_heightSet (I : Seed.{u} ω 1) :
    Seed.tieValue.{u} 1 ∈ Scheme.heightSet (I.seedValues 𝕣) (I.seedGridBound 𝕣) 2 :=
  Scheme.mem_heightSet.mpr (.inr ⟨I.codeSet_subset_seedValues 𝕣 (Seed.tieValue_mem_codeSet _ 1),
    (Seed.isSelfVisible_tieValue 1).mono (by omega)⟩)

/-- **Separation at the input** (the stopping cell): for a state `R` of the catalogue at the
grade `2` and a lawful state `R'` agreeing with it capped at the cap `3`, some cell of the ladder
tower at `(univ, 2)` reads `R` on the cells of the attachment of grade at most `2` and carries the
writing of `R'` at a value at least `3` (`Scheme.LadderBaseData.exists_cell_le_v_of_capAgree`).
This is the step the refutation over the grid alone could not take. -/
theorem exists_cell_le_tieValue (I : Seed.{u} ω 1)
    {A : ℕ → (Fin (I.attachmentBase 𝕣).S.card → Label.{u}) → Prop}
    {R R' : Fin (I.attachmentBase 𝕣).S.card → Label.{u}}
    (hRC : R ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) A 2)
    (hR' : (I.attachmentBase 𝕣).S.rows.IsLawful R')
    (hag : ∀ d, min (R' d) (Seed.tieValue 1) = min (R d) (Seed.tieValue 1)) :
    ∃ u : Fin ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
        (I.seedGridBound 𝕣) 1).S.card,
      ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
        (I.seedGridBound 𝕣) 1).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2) ∧
      (∀ d : Fin (I.attachmentBase 𝕣).S.card, (I.attachmentBase 𝕣).S.toCellScheme.grade d ≤ 2 →
        ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
          (I.seedGridBound 𝕣) 1).S.rowAt u
          ((I.attachmentBase 𝕣).towerEmb (H := I.seedHeight 𝕣) (Γ := I.seedValues 𝕣) (A := A)
            (B' := I.seedGridBound 𝕣) 1 (Fin.castAdd _ d)) = R d) ∧
      Seed.tieValue 1 ≤ ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
        (I.seedGridBound 𝕣) 1).v R' u := by
  obtain ⟨u, -, hu, hrow, -, hv⟩ := Scheme.LadderBaseData.exists_cell_le_v_of_capAgree
    (B' := I.seedGridBound 𝕣) (I.card_le_seedHeight 𝕣) (k := 0) (K := 1) le_rfl
    (I.codeSet_subset_seedValues 𝕣 (Seed.tieValue_mem_codeSet _ 1)) (Seed.tieValue_ne_bot 1)
    ((Seed.isSelfVisible_tieValue 1).mono (by omega)) hRC hR' hag
  exact ⟨u, hu, hrow, hv⟩

/-- **Compatibility at the input**: at the choice of the assembly the ladder tower with agreement
heights in the height set is consistent, the writing of every state of the catalogue is lawful and
at most the grid point, and the tower is coded (`Scheme.LadderBaseData.ladderTower_lawful`,
`Scheme.LadderBaseData.isCoded_ladderTower`, the values of the choice below the grid point at `2`
and below `ω ^ 2`). -/
theorem ladderTower_lawful_isCoded (I : Seed.{u} ω 1)
    {A : ℕ → (Fin (I.attachmentBase 𝕣).S.card → Label.{u}) → Prop}
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k : ℕ) :
    (((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
        (I.seedGridBound 𝕣) k).S.rows.IsConsistent ∧
      ∀ R ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) A (k + 2),
        ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
          (I.seedGridBound 𝕣) k).S.rows.IsLawful
          (((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
            (I.seedGridBound 𝕣) k).v R) ∧
        ∀ x, ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
          (I.seedGridBound 𝕣) k).v R x ≤ gridPoint (k + 2) (I.seedGridBound 𝕣)) ∧
      ((I.attachmentBase 𝕣).ladderTower (I.seedHeight 𝕣) (I.seedValues 𝕣) A
        (I.seedGridBound 𝕣) k).S.IsCoded :=
  ⟨Scheme.LadderBaseData.ladderTower_lawful (I.seedHeight_pos 𝕣) (I.card_le_seedHeight 𝕣)
      (fun _ hx ↦ I.le_gridPoint_of_mem_seedValues 𝕣 hx) hA k,
    Scheme.LadderBaseData.isCoded_ladderTower (I.card_le_seedHeight 𝕣)
      (fun _ hx ↦ I.lt_omega0_sq_of_mem_seedValues 𝕣 hx) hA k⟩

/-- The lift at the tie input, for the first coatom type given up to equality. -/
theorem exists_lift_of_tie_aux {I : Seed.{u} ω 1} {t' : StageType.{u} ω 2} (hI : I.left = t')
    {p : StageType.{u} ω 1} {hte : restrictFace ((𝕣).trans Fin.castSuccEmb) t' = some p}
    {d : StageType.{u} ω 2}
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte)
    {P₀ : Fin (I.attachment 𝕣).card → Label.{u}} (hP₀ : (I.attachment 𝕣).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits 𝕣 hdA (hI ▸ Q) (1 + 2) P₀) {RP : Fin (I.attachment 𝕣).card → Label.{u}}
    (hRP : RP ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q))
      (1 + 2))
    {σ : Label.{u} → Label.{u}} (hσR : ∀ a, σ (RP a) = Label.omegaShift (P₀ a)) :
    ∃ q' : (I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q))
        (I.seedGridBound 𝕣)).toCellScheme.below ((univ : Finset (Fin 3)), 2) → Label.{u},
      (I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q))
        (I.seedGridBound 𝕣)).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) q' ∧
      (∀ e, min (q' e) (Seed.tieValue 1) = min (I.replicatedWriting 𝕣 (I.seedHeight 𝕣)
        (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q)) (I.seedGridBound 𝕣)
        (Label.posConst (Seed.tieValue 1) ∘ P₀) e.1) (Seed.tieValue 1)) ∧
      ∀ e : (I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ Q))
          (I.seedGridBound 𝕣)).toCellScheme.below (univ.erase (Fin.last 2), 2),
        q' (Set.inclusion ((I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣)
          (I.attachAdmits 𝕣 hdA (hI ▸ Q)) (I.seedGridBound 𝕣)).toCellScheme.below_mono
          (show ((univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤
            ((univ : Finset (Fin 3)), 2) from ⟨erase_subset _ _, le_rfl⟩)) e) =
          σ (I.replicatedWriting 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣)
            (I.attachAdmits 𝕣 hdA (hI ▸ Q)) (I.seedGridBound 𝕣) RP e.1) := by
  subst hI
  exact Seed.exists_lift_of_tie (I.seedHeight_pos 𝕣) (I.card_le_seedHeight 𝕣)
    (fun _ hx ↦ I.le_gridPoint_of_mem_seedValues 𝕣 hx) (I.codeSet_subset_seedValues 𝕣) hdA hQ
    le_rfl hP₀ hP₀A hRP hσR

/-- **The repaired scheme lifts at the tie input** (the input of the refutation over the grid
alone): at every seed of the input, at the choice of the assembly, for every complete lawful
admitted state `P₀` of the attachment (the admitted completion of `sep ω` among them), the cap
`3`, the ambient the writing of the positive constant `3` on the support of `P₀`, and the
prescription the decoded writing of any code `(RP, σ)` of `P₀` shifted by one block, some
labelling lawful below `(univ, 2)` keeps the ambient at `3` and is the prescription below the
context coatom (`Seed.exists_lift_of_tie`).  This is the lift at one input; the context lift at
every input (`TieInstance.RepairedContextLift`) is not proved here. -/
theorem exists_lift_of_tie (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {P₀ : Fin (I.attachment 𝕣).card → Label.{u}} (hP₀ : (I.attachment 𝕣).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits 𝕣 hdA (hI ▸ req ω) (1 + 2) P₀)
    {RP : Fin (I.attachment 𝕣).card → Label.{u}}
    (hRP : RP ∈ (I.attachmentBase 𝕣).towerCat (I.seedValues 𝕣)
      (I.attachAdmits 𝕣 hdA (hI ▸ req ω)) (1 + 2))
    {σ : Label.{u} → Label.{u}} (hσR : ∀ a, σ (RP a) = Label.omegaShift (P₀ a)) :
    ∃ q' : (I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣)
        (I.attachAdmits 𝕣 hdA (hI ▸ req ω)) (I.seedGridBound 𝕣)).toCellScheme.below
          ((univ : Finset (Fin 3)), 2) → Label.{u},
      (I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ req ω))
        (I.seedGridBound 𝕣)).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) q' ∧
      (∀ e, min (q' e) (Seed.tieValue 1) = min (I.replicatedWriting 𝕣 (I.seedHeight 𝕣)
        (I.seedValues 𝕣) (I.attachAdmits 𝕣 hdA (hI ▸ req ω)) (I.seedGridBound 𝕣)
        (Label.posConst (Seed.tieValue 1) ∘ P₀) e.1) (Seed.tieValue 1)) ∧
      ∀ e : (I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣)
          (I.attachAdmits 𝕣 hdA (hI ▸ req ω)) (I.seedGridBound 𝕣)).toCellScheme.below
            (univ.erase (Fin.last 2), 2),
        q' (Set.inclusion ((I.replicated 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣)
          (I.attachAdmits 𝕣 hdA (hI ▸ req ω)) (I.seedGridBound 𝕣)).toCellScheme.below_mono
          (show ((univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤
            ((univ : Finset (Fin 3)), 2) from ⟨erase_subset _ _, le_rfl⟩)) e) =
          σ (I.replicatedWriting 𝕣 (I.seedHeight 𝕣) (I.seedValues 𝕣)
            (I.attachAdmits 𝕣 hdA (hI ▸ req ω)) (I.seedGridBound 𝕣) RP e.1) :=
  exists_lift_of_tie_aux hI (hte := restrictFace_ctx_root ω) hdA (classCalibrated_req ω) hP₀
    hP₀A hRP hσR

end TieInstance

end VaughtConjecture

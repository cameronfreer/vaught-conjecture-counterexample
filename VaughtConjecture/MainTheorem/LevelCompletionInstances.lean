/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrier
import VaughtConjecture.MainTheorem.ReplicatedLevelQuad
import VaughtConjecture.MainTheorem.ReplicatedGradeTwoLift
import VaughtConjecture.MainTheorem.LevelExtendingLabel

/-!
# The completion of the replicated top level at three inputs

Roadmap, Layer 3 ((R3) and (R4), recognition on the completion of the levels re-rendered per
grade).

**The reading with the extending labelling** (`Seed.exists_lvRepCompletion_reading`): for every
legality below the full grade of the replicated top level, the lawful labelling extending the labels
of the attachment (`Seed.hasExtendingLabelLevel_rep`) gives a completion in which the apex is not at
the threshold, every cell at the threshold is a cell of the level storing an admitted state
(`Seed.lvRepCompletion_ladderController`), and the cell of every context cell carries the label of
the context (`Seed.lvRepCompletion_label_attachCtxCell`).

**Three inputs** (`TieInstance.lvRepCompletion_reading_tie`,
`ApexInstance.lvRepCompletion_reading_apex`, `QuadInstance.lvRepCompletion_reading_quad`): at each
the apex is not at the threshold (`2`, `3`, `4`), every cell at the threshold is a cell of the
level, and the completion carries `⊤` at the cell of a context cell labelled `⊤`.

**Scope.**  Instances and test inputs of the levels re-rendered per grade; not used by the main
theorem through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`).

## References

The completion of [Kni26, Definition 4.3.14]; the controllers of the growth step are those of
[Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

section Instance

variable (hα : Order.IsSuccPrelimit α)

/-- **The completion of the replicated top level carries the label of the context** at the cell of
a context cell, for a lawful labelling extending the labels of the attachment. -/
theorem lvRepCompletion_label_attachCtxCell (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q))
    (hL : hNm.rep.IsLegalBelowFullGrade) {q : Fin hNm.rep.card → Label.{u}}
    (hq : hNm.rep.rows.IsLawful q)
    (hqe : ∀ c, q (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb c)) =
      (I.attachmentType g).label c) (x : Fin I.left.card) :
    (lvRepCompletion hα hNm hL hq).label
        (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
          Fin hNm.rep.card).castSucc = I.left.label x :=
  label_addApex_attachCtxCell_of_levelShape (t := lvRepType hα hNm hL hq) hL (Nat.succ_pos _)
    (κ := Fin.castAdd _) (q := q) (fun _ ↦ rfl) hqe x

/-- **The completion of the replicated top level, read with the extending labelling**
(`Seed.hasExtendingLabelLevel_rep`): for every legality below the full grade of the replicated top
level, some lawful labelling gives a completion in which the apex is not at the threshold, every
cell at the threshold is old and stores an admitted state, and the cell of every context cell
carries the label of the context. -/
theorem exists_lvRepCompletion_reading (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin (m + 2))), Q.threshold) ∧
        (∀ u, (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin (m + 2))), Q.threshold) →
          ∃ u' : Fin (I.lvLevel g H B hd Q m).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc ∧
            Q.AdmitsOnClass
              (fun x ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
                  Fin hNm.rep.card).castSucc)
              (fun y ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachDonCell g hd y)) :
                  Fin hNm.rep.card).castSucc)) ∧
        ∀ x, (lvRepCompletion hα hNm hL hq).label
          (Fin.castAdd _ ((I.lvLevel g H B hd Q m).attEmb (I.attachCtxCell g x)) :
            Fin hNm.rep.card).castSucc = I.left.label x := by
  obtain ⟨q, hq, hqe⟩ := hasExtendingLabelLevel_rep (hd := hd) hH hcard hQ hpair hB m (by omega)
  refine ⟨q, hq, StageType.gradedIndex_addApex_last_ne_threshold Q hL _, fun u hu ↦ ?_,
    lvRepCompletion_label_attachCtxCell hα hNm hL hq hqe⟩
  obtain ⟨u', hu', a, F, hadm, -⟩ :=
    lvRepCompletion_ladderController hα hH hcard hQ hB hN2 hNm hL hq u hu
  exact ⟨u', hu', hadm⟩

/-- `Seed.exists_lvRepCompletion_reading` for the first coatom type given up to equality. -/
theorem exists_lvRepCompletion_reading_of_eq {t' : StageType.{u} α (m + 1)} (hI : I.left = t')
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p₀}
    {d : StageType.{u} α (n + 1)}
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ y, Q.CorrectAt t'.label y (d.label y))
    (hQ : Q.ClassCalibrated hte) (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.lvLevel g H B hdA (hI ▸ Q) m).Good B (lvAdm hdA (hI ▸ Q)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin (m + 2))), Q.threshold) ∧
        (∀ u, (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin (m + 2))), Q.threshold) →
          ∃ u' : Fin (I.lvLevel g H B hdA (hI ▸ Q) m).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc ∧
            (hI ▸ Q).AdmitsOnClass
              (fun x ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _ ((I.lvLevel g H B hdA (hI ▸ Q) m).attEmb (I.attachCtxCell g x)) :
                  Fin hNm.rep.card).castSucc)
              (fun y ↦ (lvRepCompletion hα hNm hL hq).toScheme.rowAt u
                (Fin.castAdd _
                  ((I.lvLevel g H B hdA (hI ▸ Q) m).attEmb (I.attachDonCell g hdA y)) :
                  Fin hNm.rep.card).castSucc)) ∧
        ∀ x, (lvRepCompletion hα hNm hL hq).label
          (Fin.castAdd _ ((I.lvLevel g H B hdA (hI ▸ Q) m).attEmb (I.attachCtxCell g x)) :
            Fin hNm.rep.card).castSucc = I.left.label x := by
  subst hI
  exact exists_lvRepCompletion_reading hα hH hcard hQ hpair hB hN2 hNm hL

end Instance

end Seed

/-! ### The test inputs -/

open Seed AvailableTopDeterminationCounterexample
open scoped Ordinal

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- **The completion at the tie input** (requests `req ω`, threshold `2`): for every legality
below the full grade of the replicated top level, with the extending labelling, the apex is not at
`(univ, 2)`, every cell at `(univ, 2)` is a cell of the level storing an admitted state, and the
cell of a context cell labelled `⊤` carries `⊤`. -/
theorem lvRepCompletion_reading_tie (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B)
    (hNm : (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) 1).Good B (lvAdm hdA (hI ▸ req ω)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion Ordinal.isSuccLimit_omega0.isSuccPrelimit hNm hL hq).toCellScheme.gradedIndex
          (Fin.last _) ≠ ((univ : Finset (Fin 3)), 2) ∧
        (∀ u, (lvRepCompletion Ordinal.isSuccLimit_omega0.isSuccPrelimit hNm hL
          hq).toCellScheme.gradedIndex u = ((univ : Finset (Fin 3)), 2) →
          ∃ u' : Fin (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) 1).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc) ∧
        ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
          (lvRepCompletion Ordinal.isSuccLimit_omega0.isSuccPrelimit hNm hL hq).label
            (Fin.castAdd _ ((I.lvLevel 𝕣 H B hdA (hI ▸ req ω) 1).attEmb (I.attachCtxCell 𝕣 x)) :
              Fin hNm.rep.card).castSucc = ⊤ := by
  obtain ⟨q, hq, hapex, hold, hlab⟩ := Seed.exists_lvRepCompletion_reading_of_eq
    Ordinal.isSuccLimit_omega0.isSuccPrelimit hI (hte := restrictFace_ctx_root ω) hdA
    (correctAt_req ω) (classCalibrated_req ω) hH hcard hB
    (by have := threshold_req.{u} ω; omega) hNm hL
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨cellR.{u} ω, label_cellR ω⟩
  have e := congrArg (Prod.mk (univ : Finset (Fin 3))) (threshold_req.{u} ω).symm
  refine ⟨q, hq, fun h ↦ hapex (h.trans e), fun u hu ↦ ?_, x, hx, (hlab x).trans hx⟩
  obtain ⟨u', hu', -⟩ := hold u (hu.trans e)
  exact ⟨u', hu'⟩

end TieInstance

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- **The completion at the apex input** (requests `reqTop α`, threshold `3`, the top grade of the
context): at a stage that is zero or a limit, for every legality below the full grade of the
replicated top level, with the extending labelling, the apex of the completion (grade `4`) is not at
`(univ, 3)`, every cell at `(univ, 3)` is a cell of the level, and the cell of the context apex
(labelled `⊤`) carries `⊤`. -/
theorem lvRepCompletion_reading_apex {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α)
    (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B)
    (hNm : (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) 2).Good B (lvAdm hdA (hI ▸ reqTop α)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin 4)), 3) ∧
        (∀ u, (lvRepCompletion hα hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin 4)), 3) →
          ∃ u' : Fin (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) 2).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc) ∧
        ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
          (lvRepCompletion hα hNm hL hq).label
            (Fin.castAdd _
              ((I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) 2).attEmb (I.attachCtxCell 𝕘 x)) :
              Fin hNm.rep.card).castSucc = ⊤ := by
  obtain ⟨q, hq, hapex, hold, hlab⟩ := Seed.exists_lvRepCompletion_reading_of_eq hα hI
    (hte := restrictFace_root) hdA (correctAt_reqTop α) (classCalibrated_reqTop α) hH hcard hB
    (by have := threshold_reqTop.{u} α; omega) hNm hL
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨apex α, label_apex α⟩
  have e := congrArg (Prod.mk (univ : Finset (Fin 4))) (threshold_reqTop.{u} α).symm
  refine ⟨q, hq, fun h ↦ hapex (h.trans e), fun u hu ↦ ?_, x, hx, (hlab x).trans hx⟩
  obtain ⟨u', hu', -⟩ := hold u (hu.trans e)
  exact ⟨u', hu'⟩

end ApexInstance

namespace QuadInstance

/-- The root of the input. -/
local notation "𝕘" => root

/-- **The completion at the input on four points** (requests `req hα`, threshold `4`, the top
grade of the context): for every legality below the full grade of the replicated top level, with
the extending labelling, the apex of the completion (grade `5`) is not at `(univ, 4)`, every cell
at `(univ, 4)` is a cell of the level, and the cell of the context apex (labelled `⊤`) carries
`⊤`. -/
theorem lvRepCompletion_reading_quad {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B)
    (hNm : (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 3).Good B (lvAdm hdA (hI ▸ req hα)))
    (hL : hNm.rep.IsLegalBelowFullGrade) :
    ∃ (q : Fin hNm.rep.card → Label.{u}) (hq : hNm.rep.rows.IsLawful q),
      (lvRepCompletion hα.isSuccPrelimit hNm hL hq).toCellScheme.gradedIndex (Fin.last _) ≠
          ((univ : Finset (Fin 5)), 4) ∧
        (∀ u, (lvRepCompletion hα.isSuccPrelimit hNm hL hq).toCellScheme.gradedIndex u =
          ((univ : Finset (Fin 5)), 4) →
          ∃ u' : Fin (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 3).S.card,
            u = (Fin.castAdd _ u' : Fin hNm.rep.card).castSucc) ∧
        ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
          (lvRepCompletion hα.isSuccPrelimit hNm hL hq).label
            (Fin.castAdd _
              ((I.lvLevel 𝕘 H B hdA (hI ▸ req hα) 3).attEmb (I.attachCtxCell 𝕘 x)) :
              Fin hNm.rep.card).castSucc = ⊤ := by
  obtain ⟨q, hq, hapex, hold, hlab⟩ := Seed.exists_lvRepCompletion_reading_of_eq
    hα.isSuccPrelimit hI (hte := restrictFace_root_quad hα) hdA (correctAt_req hα)
    (classCalibrated_req hα) hH hcard hB (by have := threshold_req hα; omega) hNm hL
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ :=
    hI ▸ ⟨apex hα, label_apex hα⟩
  have e := congrArg (Prod.mk (univ : Finset (Fin 5))) (threshold_req hα).symm
  refine ⟨q, hq, fun h ↦ hapex (h.trans e), fun u hu ↦ ?_, x, hx, (hlab x).trans hx⟩
  obtain ⟨u', hu', -⟩ := hold u (hu.trans e)
  exact ⟨u', hu'⟩

end QuadInstance

/-! ### The levels at the three inputs -/

open Finset Label CellScheme StageType

namespace TieInstance

/-- The root of the input. -/
local notation "𝕣" => Function.Embedding.refl (Fin 1)

/-- The state step at the input, for the first coatom type given up to equality. -/
theorem exists_stateStep_two_aux {α : Ordinal.{u}} {I : Seed.{u} α 1} {t' : StageType.{u} α 2}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕣).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp) (hth : Q.threshold = 2)
    {R₀ : Fin (I.attachment 𝕣).card → Label.{u}} (hR₀ : (I.attachment 𝕣).rows.IsLawful R₀)
    (hR₀A : I.attachAdmits 𝕣 hdA (hI ▸ Q) 2 R₀) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 2 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕣 x)) h) :
    ∃ W : Fin (I.attachment 𝕣).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 2 → W (I.attachCtxCell 𝕣 x) = w x) ∧
      (I.attachment 𝕣).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun a ↦ W a) ∧
      I.attachAdmits 𝕣 hdA (hI ▸ Q) 2 W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  subst hI
  exact Seed.exists_stateStep_threshold hte hdp hdL Nat.one_pos hdA hQ hpair hrel hth
    (by omega) hR₀ hR₀A hh hw hwR

/-- **The state step at the top grade `2` of the tie input**: every lawful anchor admitted at `2`
and every context prescription lawful below `(univ, 2)` agreeing with it capped at a cut `h`
self-visible at `2` give a state of the attachment literal on the context, lawful below
`(univ, 2)`, admitted at `2`, and agreeing with the anchor capped at `h`.  The threshold of the
requests is `2`, so the premise on the anchor's truncation holds. -/
theorem exists_stateStep_two (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {R₀ : Fin (I.attachment 𝕣).card → Label.{u}} (hR₀ : (I.attachment 𝕣).rows.IsLawful R₀)
    (hR₀A : I.attachAdmits 𝕣 hdA (hI ▸ req ω) 2 R₀) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 2 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕣 x)) h) :
    ∃ W : Fin (I.attachment 𝕣).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 2 → W (I.attachCtxCell 𝕣 x) = w x) ∧
      (I.attachment 𝕣).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun a ↦ W a) ∧
      I.attachAdmits 𝕣 hdA (hI ▸ req ω) 2 W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep_two_aux hI (hte := restrictFace_ctx_root ω) (don_mem_cofaces ω).2
    (don_mem_cofaces ω).1 hdA (correctAt_req ω) (classCalibrated_req ω)
    (hasRelativeLiftOnClass_req ω) (threshold_req ω) hR₀ hR₀A hh hw hwR

/-- **The extending labelling at the tie input**: at every seed of the input, for the requests
`req ω`, every level up to the grade `3` has a lawful labelling extending the labels of the
attachment, and at the cell of the attachment at `cellR ω` (labelled `⊤`) it reads `⊤`. -/
theorem hasExtendingLabelLevel_tie (I : Seed.{u} ω 1) (hI : I.left = ctx ω)
    (hdA : restrictFace (extendByLast ((𝕣).trans Fin.castSuccEmb)) I.amalgam = some (don ω))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕣).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕣).card ≤ B) :
    ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
      ∀ j, j + 1 ≤ 3 → I.HasExtendingLabelLevel 𝕣 H B hdA (hI ▸ req ω) j ∧
        (I.lvLevel 𝕣 H B hdA (hI ▸ req ω) j).extLabel
          ((I.lvLevel 𝕣 H B hdA (hI ▸ req ω) j).attEmb (I.attachCtxCell 𝕣 x)) = ⊤ := by
  have h := Seed.hasExtendingLabelLevel_of_eq hI (hte := restrictFace_ctx_root ω) hdA
    (correctAt_req ω) (classCalibrated_req ω) hH hcard hB
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨cellR.{u} ω, label_cellR ω⟩
  exact ⟨x, hx, fun j hj ↦ ⟨(h j hj).1, ((h j hj).2 x).trans hx⟩⟩

/-- **The level at the top grade `2` of the tie input**: the orbit code at `2` of the compressed
labelling is lawful below `(univ, 2)`, and so is its extension with the rank member from the grade
one. -/
theorem isLawfulBelow_stateExtOf_two {α : Ordinal.{u}} (I : Seed.{u} α 1) :
    ∃ hP : (I.attachment 𝕣).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun d ↦ orbitCode 2 (I.compressedLabel 𝕣) d),
      (I.attachmentBase 𝕣).ladderBase (I.seedHeight 𝕣) |>.rows.IsLawfulBelow
        ((univ : Finset (Fin 3)), 2) fun t ↦ (I.attachmentBase 𝕣).stateExtOf
          (orbitCode 2 (I.compressedLabel 𝕣))
          (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase 𝕣).wf (I.card_le_seedHeight 𝕣)
            (hP.mono (show ((univ : Finset (Fin 3)), 1) ≤ ((univ : Finset (Fin 3)), 2) from
              ⟨subset_rfl, by omega⟩))) t :=
  Seed.isLawfulBelow_stateExtOf_orbitCode (I.seedHeight_pos 𝕣) (I.card_le_seedHeight 𝕣)
    (by omega) (Seed.isLawful_compressedLabel (I := I) (g := 𝕣))

end TieInstance

namespace ApexInstance

/-- The root of the input. -/
local notation "𝕘" => (Fin.castSuccEmb : Fin 1 ↪ Fin 2)

/-- The state step at the input, for the first coatom type given up to equality: at the grade `2`
from the threshold `2`, and at every grade from an anchor in the catalogue. -/
theorem exists_stateStep_aux {α : Ordinal.{u}} {I : Seed.{u} α 2} {t' : StageType.{u} α 3}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕘).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hdL : d.IsLegal)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hdp) {k : ℕ}
    (hk : 1 ≤ k) {R₀ : Fin (I.attachment 𝕘).card → Label.{u}}
    (hR₀ : (I.attachment 𝕘).rows.IsLawful R₀) {h : Label.{u}} (hh : IsSelfVisible k h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 3)), k) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ k →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕘 x)) h)
    (hadm : (Q.threshold = k ∧ I.attachAdmits 𝕘 hdA (hI ▸ Q) k R₀) ∨
      ∃ (H : ℕ) (Γ : Finset Label.{u}) (B' : ℕ), 0 < H ∧ (I.attachmentBase 𝕘).S.card ≤ H ∧
        ⊥ ∈ Γ ∧ (∀ x ∈ Γ, x ≤ gridPoint 2 B') ∧
        R₀ ∈ (I.attachmentBase 𝕘).towerCat Γ (I.attachAdmits 𝕘 hdA (hI ▸ Q)) 4) :
    ∃ W : Fin (I.attachment 𝕘).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ k → W (I.attachCtxCell 𝕘 x) = w x) ∧
      (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), k) (fun a ↦ W a) ∧
      I.attachAdmits 𝕘 hdA (hI ▸ Q) k W ∧
      ∀ a, min (W a) h = min (R₀ a) h := by
  subst hI
  rcases hadm with ⟨hth, hR₀A⟩ | ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hR₀C⟩
  · exact Seed.exists_stateStep_threshold hte hdp hdL Nat.one_pos hdA hQ hpair hrel hth hk hR₀
      hR₀A hh hw hwR
  · exact Seed.exists_stateStep_of_mem_towerCat hH hcard hΓ0 hΓ hte hdp hdL Nat.one_pos hdA hQ
      hpair hrel hk hR₀C hh hw hwR

/-- **The state step at the top grade `3` of the apex input, above the threshold `2`**: for an
anchor in the catalogue (values `Γ` containing `⊥` and below the grid point at `2`, height bound
`H` at least the card of the attachment base), the admission of the anchor's truncation at `3` is
the ambient admission of its writing, and the state step holds at `3`. -/
theorem exists_stateStep_three {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H : ℕ} {Γ : Finset Label.{u}} {B' : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') {R₀ : Fin (I.attachment 𝕘).card → Label.{u}}
    (hR₀ : R₀ ∈ (I.attachmentBase 𝕘).towerCat Γ (I.attachAdmits 𝕘 hdA (hI ▸ req α)) 4)
    {h : Label.{u}} (hh : IsSelfVisible 3 h) {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 3) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 3 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕘 x)) h) :
    ∃ W : Fin (I.attachment 𝕘).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 3 → W (I.attachCtxCell 𝕘 x) = w x) ∧
      (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun a ↦ W a) ∧
      I.attachAdmits 𝕘 hdA (hI ▸ req α) 3 W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep_aux hI (hte := restrictFace_root) bareDonor_mem_cofaces.2
    bareDonor_mem_cofaces.1 hdA (correctAt_req α) (classCalibrated_req α)
    (hasRelativeLiftOnClass_req α) (by omega)
    (Scheme.LadderBaseData.mem_towerCat.mp hR₀).2.1 hh hw hwR
    (.inr ⟨H, Γ, B', hH, hcard, hΓ0, hΓ, hR₀⟩)

/-- **The state step at the grade `2` of the apex input, below its top grade `3`**: with the
bottom requests `req α` (threshold `2`) over the donor labelled `⊥`, every lawful anchor admitted
at `2` and every context prescription lawful below `(univ, 2)` agreeing with it capped at a cut
`h` self-visible at `2` give a state of the attachment literal on the context, lawful below
`(univ, 2)`, admitted at `2`, and agreeing with the anchor capped at `h`. -/
theorem exists_stateStep_two {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {R₀ : Fin (I.attachment 𝕘).card → Label.{u}} (hR₀ : (I.attachment 𝕘).rows.IsLawful R₀)
    (hR₀A : I.attachAdmits 𝕘 hdA (hI ▸ req α) 2 R₀) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    {w : Fin I.left.card → Label.{u}}
    (hw : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) fun x ↦ w x)
    (hwR : ∀ x, I.left.toCellScheme.grade x ≤ 2 →
      min (w x) h = min (R₀ (I.attachCtxCell 𝕘 x)) h) :
    ∃ W : Fin (I.attachment 𝕘).card → Label.{u},
      (∀ x, I.left.toCellScheme.grade x ≤ 2 → W (I.attachCtxCell 𝕘 x) = w x) ∧
      (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) (fun a ↦ W a) ∧
      I.attachAdmits 𝕘 hdA (hI ▸ req α) 2 W ∧
      ∀ a, min (W a) h = min (R₀ a) h :=
  exists_stateStep_aux hI (hte := restrictFace_root) bareDonor_mem_cofaces.2
    bareDonor_mem_cofaces.1 hdA (correctAt_req α) (classCalibrated_req α)
    (hasRelativeLiftOnClass_req α) (by omega) hR₀ hh hw hwR (.inl ⟨threshold_req α, hR₀A⟩)

/-- The levels at the input are good, for the first coatom type given up to equality. -/
theorem lvLevel_good_aux {α : Ordinal.{u}} {I : Seed.{u} α 2} {t' : StageType.{u} α 3}
    (hI : I.left = t') {p : StageType.{u} α 1}
    {hte : restrictFace ((𝕘).trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α 2}
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte) {H B : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase 𝕘).S.card ≤ H) (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∀ j, j + 1 ≤ 4 →
      (I.lvLevel 𝕘 H B hdA (hI ▸ Q) j).Good B (Seed.lvAdm hdA (hI ▸ Q)) := by
  subst hI
  exact Seed.lvLevel_good hH hcard hQ hB

/-- **The levels at the apex input are good** up to the grade `4 = m + 2`, for the requests
`reqTop α`. -/
theorem lvLevel_good_apex {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∀ j, j + 1 ≤ 4 →
      (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) j).Good B (Seed.lvAdm hdA (hI ▸ reqTop α)) :=
  lvLevel_good_aux hI (hte := restrictFace_root) hdA (classCalibrated_reqTop α) hH hcard hB

/-- **The replicated levels at the apex input lift from the context coatom** (top grade `3`):
the level at the grade `j + 1 ≤ 3` with its copies at the mixed faces is well formed, consistent,
and lifts capped from the context coatom into `(univ, j + 1)`; in particular at the grade `3`. -/
theorem lvRep_cappedLift_three {α : Ordinal.{u}} (I : Seed.{u} α 2) (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) (j : ℕ) (hj : j + 1 ≤ 3) :
    (lvLevel_good_apex I hI hdA hH hcard hB j (by omega)).rep.IsWellFormed ∧
      (lvLevel_good_apex I hI hdA hH hcard hB j (by omega)).rep.rows.IsConsistent ∧
      (lvLevel_good_apex I hI hdA hH hcard hB j (by omega)).rep.rows.CappedLift
        (X := (univ.erase (Fin.last 3), j + 1)) (Y := ((univ : Finset (Fin 4)), j + 1))
        ⟨erase_subset _ _, le_rfl⟩ :=
  ⟨Seed.ALvl.Good.isWellFormed_rep _ (Seed.faces_lvLevel j), Seed.ALvl.Good.isConsistent_rep _,
    Seed.ALvl.Good.cappedLift_rep _ _ rfl subset_rfl
      (lvLevel_cappedLift_three I hI hdA hH hcard hB j hj)⟩

/-- **The extending labelling at the apex input**: at every seed of the input, for the requests
`reqTop α`, every level up to the grade `4` has a lawful labelling extending the labels of the
attachment, and at the cell of the attachment at the apex (labelled `⊤`) it reads `⊤`. -/
theorem hasExtendingLabelLevel_apex {α : Ordinal.{u}} (I : Seed.{u} α 2)
    (hI : I.left = topType α)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
      ∀ j, j + 1 ≤ 4 → I.HasExtendingLabelLevel 𝕘 H B hdA (hI ▸ reqTop α) j ∧
        (I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) j).extLabel
          ((I.lvLevel 𝕘 H B hdA (hI ▸ reqTop α) j).attEmb (I.attachCtxCell 𝕘 x)) = ⊤ := by
  have h := Seed.hasExtendingLabelLevel_of_eq hI (hte := restrictFace_root) hdA
    (correctAt_reqTop α) (classCalibrated_reqTop α) hH hcard hB
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ := hI ▸ ⟨apex α, label_apex α⟩
  exact ⟨x, hx, fun j hj ↦ ⟨(h j hj).1, ((h j hj).2 x).trans hx⟩⟩

/-- **The level at the grade `2 < 3` of the input with an apex**: the orbit code at `2` of the
compressed labelling, not lawful (`ApexInstance.not_isLawful_orbitCode_two`), is lawful below
`(univ, 2)`, and so is its extension with the rank member from the grade one. -/
theorem isLawfulBelow_stateExtOf_two {α : Ordinal.{u}} (I : Seed.{u} α 2) :
    ∃ hP : (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2)
        (fun d ↦ orbitCode 2 (I.compressedLabel 𝕘) d),
      (I.attachmentBase 𝕘).ladderBase (I.seedHeight 𝕘) |>.rows.IsLawfulBelow
        ((univ : Finset (Fin 4)), 2) fun t ↦ (I.attachmentBase 𝕘).stateExtOf
          (orbitCode 2 (I.compressedLabel 𝕘))
          (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase 𝕘).wf (I.card_le_seedHeight 𝕘)
            (hP.mono (show ((univ : Finset (Fin 4)), 1) ≤ ((univ : Finset (Fin 4)), 2) from
              ⟨subset_rfl, by omega⟩))) t :=
  Seed.isLawfulBelow_stateExtOf_orbitCode (I.seedHeight_pos 𝕘) (I.card_le_seedHeight 𝕘)
    (by omega) (Seed.isLawful_compressedLabel (I := I) (g := 𝕘))

/-- **At the three-point seed with an apex, the orbit code at the grade `2` of the lawful
compressed labelling has a rank member**, though it is not lawful
(`ApexInstance.not_isLawful_orbitCode_two`): it is lawful below `(univ, 2)`, hence below
`(univ, 1)`. -/
theorem exists_rankMember_orbitCode_two {α : Ordinal.{u}} (I : Seed.{u} α 2) :
    ∃ a : Scheme.RankMember (I.attachmentBase 𝕘).S (I.seedHeight 𝕘),
      ∀ d, (a.1 d : ℕ) = rankVector (orbitCode 2 (I.compressedLabel 𝕘)) d := by
  have h2 : (I.attachment 𝕘).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2)
      fun d ↦ orbitCode 2 (I.compressedLabel 𝕘) d :=
    (Seed.isLawful_compressedLabel (I := I) (g := 𝕘)).isLawfulBelow _ |>.orbitCode fun d ↦ d.2.2
  have h1 := h2.mono (show ((univ : Finset (Fin 4)), 1) ≤ ((univ : Finset (Fin 4)), 2) from
    ⟨subset_rfl, by omega⟩)
  exact ⟨Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase 𝕘).wf (I.card_le_seedHeight 𝕘) h1,
    fun _ ↦ rfl⟩

end ApexInstance

namespace QuadInstance

/-- The root of the input. -/
local notation "𝕘" => root

/-- **The extending labelling at the input on four points**: at every seed of the input, for the
requests `req hα`, every level up to the grade `5` has a lawful labelling extending the labels of
the attachment, and at the cell of the attachment at the apex (labelled `⊤`) it reads `⊤`. -/
theorem hasExtendingLabelLevel_quad {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    (I : Seed.{u} α 3) (hI : I.left = quadType hα)
    (hdA : restrictFace (extendByLast ((𝕘).trans Fin.castSuccEmb)) I.amalgam =
      some (ApexInstance.bareDonor α))
    {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase 𝕘).S.card ≤ H)
    (hB : 2 * (I.attachment 𝕘).card ≤ B) :
    ∃ x : Fin I.left.card, I.left.label x = ⊤ ∧
      ∀ j, j + 1 ≤ 5 → I.HasExtendingLabelLevel 𝕘 H B hdA (hI ▸ req hα) j ∧
        (I.lvLevel 𝕘 H B hdA (hI ▸ req hα) j).extLabel
          ((I.lvLevel 𝕘 H B hdA (hI ▸ req hα) j).attEmb (I.attachCtxCell 𝕘 x)) = ⊤ := by
  have h := Seed.hasExtendingLabelLevel_of_eq hI (hte := restrictFace_root_quad hα) hdA
    (correctAt_req hα) (classCalibrated_req hα) hH hcard hB
  obtain ⟨x, hx⟩ : ∃ x : Fin I.left.card, I.left.label x = ⊤ :=
    hI ▸ ⟨apex hα, label_apex hα⟩
  exact ⟨x, hx, fun j hj ↦ ⟨(h j hj).1, ((h j hj).2 x).trans hx⟩⟩

end QuadInstance

end VaughtConjecture

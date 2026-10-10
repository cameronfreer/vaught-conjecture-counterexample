/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrier

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

end VaughtConjecture

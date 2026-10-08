/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3RaiseCoface
import VaughtConjecture.MainTheorem.H3Small

/-!
# The open inputs of `h3` and the assembly (work file)

Work file (placement later).  The assembly of `h3` through the rows admitted in the bottom class
(`VaughtConjecture.MainTheorem.H3Class`), with the open inputs as marked SCAFFOLD (`sorry`).

* `H3.DonorTopsDominate`: the tops of the donor dominate the common face at a grade (assumed: a
  named condition, the hypothesis under which the donor lift provisions in the class form are
  compiled).
* `H3.exists_raiseCoface_gluing` (compiled in this repository): over a gluing coface the donor
  raise in the class form holds at every grade at which every prescription has a witness at the
  root (`H3.RootWitness`).
* `H3.exists_raiseCoface` (SCAFFOLD, (S2)): a donor coface with the raise in the class form and
  with its tops dominating the common face.
* `H3.exists_coface_classCompletion` (SCAFFOLD, (S1), (S4)) and the assembly.
-/

universe u w

namespace VaughtConjecture

open Finset Label StageType

namespace H3

open ProfileTower in
/-- **The tops of the donor dominate the common face** at the grade `k` (assumed, a named
condition): every labelling lawful below the donor coatom and not `⊥` on `B` has a label `h`,
self-visible at `k`, at least its values at the cells of the common face of grade at least the
grade of the cap, and at most its values at the cells of `T`. -/
def DonorTopsDominate {β : Ordinal.{u}} {m : ℕ} {I : Seed.{u} β m}
    (r : CapRequests (Fin I.amalgam.card)) (B : Set (Fin I.amalgam.card)) (xp xd : Fin (m + 2))
    (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ f d) →
    (∀ d ∈ B, f d ≠ ⊥) →
    ∃ h : Label.{u}, IsSelfVisible k h ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k),
        I.amalgam.toCellScheme.scope d ⊆ univ.erase xp →
        I.amalgam.toCellScheme.grade r.cap ≤ I.amalgam.toCellScheme.grade d → f d ≤ h) ∧
      ∀ y ∈ r.T, h ≤ f y

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **The donor raise over a gluing coface** (`H3.exists_gluingCoface`,
`H3.donorRaiseBotAtIn_of_gluesAt`): some coface `tb` of `p` with face `d` has the donor raise in
the class form at every grade `N ≤ k' ≤ k + 1` at which every prescription not `⊥` at the cap
and in the class has a witness at the root at a cap self-visible at `n + 1` and at least its
marker value. -/
theorem exists_raiseCoface_gluing (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∃ hpt : restrictFace g p = some t,
      ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        (∀ f : ProfileTower.Prof (seed ht' hp htb),
          (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k')
            (fun e ↦ f e) →
          f (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)).cap ≠ ⊥ →
          (∀ e ∈ classCells ht' hp htb htbd, e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
            (univ.erase (Fin.last (k + 1)), k') → f e ≠ ⊥) →
          ∃ θ : Label.{u}, IsSelfVisible (n + 1) θ ∧
            (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)).markerValue f ≤ θ ∧
            RootWitness hd.2 (fun x ↦ f (rootCell ht' hp htb hpt x)) θ) →
        CapRequests.DonorRaiseBotAtIn
          (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' := by
  have hpt : restrictFace g p = some t := (restrictFace_trans t' _ g hp).trans ht
  obtain ⟨tb, htb, htbd, hgl⟩ := exists_gluingCoface hα ht' hp hpt hd
  exact ⟨tb, htb, htbd, hpt, fun k' hk' hkm hwit ↦
    donorRaiseBotAtIn_of_gluesAt ht' hp htb hpt hd htbd _ hgl
      (by have := hctx.2.2.1; omega) hkm _ hwit⟩

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`), (S2): a donor coface with the raise and dominating tops.**  At an
acquired context, every coface `d` of the root face has a coface `tb` of the coatom face `p` with
face `d` along `extendByLast g` such that, at every grade from the grade of the cap, the donor
raise in the class form holds and the tops of the donor dominate the common face
(`H3.DonorTopsDominate`, assumed). -/
theorem exists_raiseCoface (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        CapRequests.DonorRaiseBotAtIn
          (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' ∧
        DonorTopsDominate (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' := by
  sorry

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`)**: at an acquired context, every coface `d` of the root face has a coface
`tb` of `p` with face `d` and a completion of the seed of `t'` and `tb` whose rows of full scope
from the grade of the cap are admitted in the class.  Through `H3.exists_raiseCoface` (S2) and
`H3.exists_classCompletion_of_fills₀` (every grade of the cap), with two `sorry`s: (S1) the lift
provisions from the donor coatom for the admitted states at a cap of grade at most `k` (from the
dominating tops, assumed; at a cap of top grade they are `H3.donorLiftProvisions_of_lt`), and (S4)
the band of the fill at the positive caps. -/
theorem exists_coface_classCompletion (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
        F.HasAdmittedRows (t'.toCellScheme.grade c)
          ((requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)).Admits
            (classCells ht' hp htb htbd) ∅) := by
  obtain ⟨tb, htb, htbd, hraise⟩ := exists_raiseCoface hα ht' hp ht hd hctx hoff hbot
  refine ⟨tb, htb, htbd, exists_classCompletion_of_fills₀ ht' hp htb htbd hctx ?_
    (fun k' hk' hkm ↦ (hraise k' hk' hkm).1) ?_⟩
  · by_cases hkN : k < t'.toCellScheme.grade c
    · exact donorLiftProvisions_of_lt ht' hp htb htbd hctx hkN
    · -- (S1) the lift provisions from the donor coatom for the admitted states at a cap of
      -- grade at most `k`, from the dominating tops `(hraise k' _ _).2` (assumed)
      sorry
  · -- (S4) the band of the fill at the positive caps
    sorry

/-- **The existential coatom form at the contexts respecting the root bottoms** (through the
SCAFFOLD `H3.exists_coface_classCompletion`). -/
theorem hollowCoatomCutoffDeterminationExists :
    Realization.HollowCoatomCutoffDeterminationExists.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) where
  exists_coface α n k t' g p hα ht' hP hp t ht d hd := by
    obtain ⟨c, r, hctx, hoff, hbot⟩ := hP
    obtain ⟨tb, htb, htbd, F, hF⟩ := exists_coface_classCompletion hα ht' hp ht hd hctx hoff hbot
    obtain ⟨δ, hδ, hdet⟩ := isDeterminedWithin_of_classRows ht' hp htb hα htbd hctx.1
      hctx.2.1 hctx.2.2.1 F hF
    exact ⟨tb, htb, htbd, F.completion hα.isSuccPrelimit,
      ⟨F.isLegal_completion _, F.restrictFace_left_completion _⟩,
      F.restrictFace_right_completion _, δ, hδ, hdet⟩

/-- **(R3) for receiving models** through the existential coatom form (SCAFFOLD). -/
theorem receivingHollowReceiving :
    Realization.HollowReceiving.{u, w} Realization.IsReceivingCoverHollowAtBlock :=
  Realization.receivingHollowReceiving_of_markedCapContextBelow'
    (hollowCoatomCutoffDeterminationExists.hollowCutoffDetermination
      (Realization.markedCapContextBelow'_routeInputs.{u, w}).2.1
      (Realization.markedCapContextBelow'_routeInputs.{u, w}).2.2)

end H3

end VaughtConjecture

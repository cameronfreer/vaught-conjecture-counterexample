/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthAdmittedStep
import VaughtConjecture.Continuation.GrowthControllerRecovery

/-!
# What admitted controllers ask of every face of a growth carrier

Roadmap, Layer 3 ((R3) and (R4), the shape of the growth carrier).

Let `G` be a growth carrier for a context `t'` and a donor `D` with a cell of full scope at the
threshold of requests `Q`, every such cell a controller admitted on the class
(`GrowthCarrier.IsClassAdmittedController`).  Then:

* **Every lawful section of the carrier is admitted** (`GrowthCarrier.admits_of_isLawful`): read on
  the context face and on the donor face, it satisfies the requests whenever its context part is
  in the bottom class below the cap with a cap value other than `⊥`
  (`GrowthCarrier.recovers_of_classAdmittedControllers`).
* **Every face has admitted completions in every capped ball**
  (`GrowthCarrier.exists_admits_extend`): a lawful section of any closed face, agreeing capped at a
  cap self-visible at the arity with a lawful section of the carrier, extends to a lawful section
  of the carrier agreeing with it capped there, and admitted.  This is legality of the carrier
  (`Scheme.IsLegal.exists_isLawful_extend`) combined with the first point.
* **The donor face lies in a second coatom** (`GrowthCarrier.exists_donorCoatom`): when the root
  misses a point of the context, the donor face is a closed face other than the ground set, so in
  the convex geometry of the faces it lies in a coatom `univ.erase y` with `y` extreme, and `y` is
  not the new point.  So the carrier has at least two coatoms, the context and `univ.erase y`.

Together: on the second coatom, which carries the donor and the cells of the context not involving
`y`, every lawful section must have a completion over the context, in every capped ball, under whose
reads (through the cap, a cell of full scope of the context and so outside the coatom) the donor
values it already carries are correct.  The relative lift on the donor
(`StageType.GrowthRequests.HasRelativeLift`) is the lift from the context coatom; this is the
condition at the second coatom, and it is a property the restriction of the carrier to that coatom
must have.

## References

The controllers of the growth step are those of [Kni26, §4]; bountifulness is
[Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier t'.toScheme D e) (Q : StageType.GrowthRequests t' D)

/-- **Recovery at a lawful section**: a recovered relation holds at the donor cells of every lawful
section of the carrier that is `σ` on the context cells. -/
theorem Recovers.apply {σ : Fin t'.card → Label.{u}} {ρ : Fin D.card → Label.{u} → Prop}
    (h : G.Recovers σ ρ) {v : Fin G.scheme.card → Label.{u}} (hv : G.scheme.rows.IsLawful v)
    (hctx : ∀ x, v (G.contextCell x) = σ x) (j : Fin D.card) : ρ j (v (G.donorCell j)) :=
  h v hv (fun i x hix ↦ by
    rw [← hctx x, contextCell, Scheme.faceCell]
    congr 2
    exact Fin.ext hix) _ j rfl

/-- **Every lawful section of a carrier with admitted controllers is admitted**: read on the
context face and on the donor face it is admitted by the requests. -/
theorem admits_of_isLawful
    (hfull : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hadm : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      G.IsClassAdmittedController Q u)
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold)
    {v : Fin G.scheme.card → Label.{u}} (hv : G.scheme.rows.IsLawful v) :
    Q.Admits (fun x ↦ v (G.contextCell x)) (fun j ↦ v (G.donorCell j)) := fun hclass hcap j ↦
  (G.recovers_of_classAdmittedControllers Q hfull hadm hdon href hmk hclass hcap).apply G hv
    (fun _ ↦ rfl) j

/-- **Every face of a carrier with admitted controllers has admitted completions in every capped
ball**: a lawful section `ℓ` of a closed face, agreeing capped at `c` (self-visible at the arity)
with a lawful section `P` of the carrier, extends to a lawful section of the carrier agreeing with
`P` capped at `c` and admitted by the requests. -/
theorem exists_admits_extend
    (hfull : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hadm : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      G.IsClassAdmittedController Q u)
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold)
    {m : ℕ} {f : Fin m ↪ Fin (J + 1)} (hf : univ.map f ∈ G.scheme.toCellScheme.faces)
    {c : Label.{u}} (hc : IsSelfVisible (J + 1) c)
    {ℓ : Fin (G.scheme.comap f).card → Label.{u}} (hℓ : (G.scheme.comap f).rows.IsLawful ℓ)
    {P : Fin G.scheme.card → Label.{u}} (hP : G.scheme.rows.IsLawful P)
    (hPℓ : ∀ i, min (P (G.scheme.cellMap f i)) c = min (ℓ i) c) :
    ∃ r : Fin G.scheme.card → Label.{u}, G.scheme.rows.IsLawful r ∧
      (∀ z, min (r z) c = min (P z) c) ∧ (∀ i, r (G.scheme.cellMap f i) = ℓ i) ∧
      Q.Admits (fun x ↦ r (G.contextCell x)) (fun j ↦ r (G.donorCell j)) := by
  obtain ⟨r, hr, hrc, hrℓ⟩ := G.isLegal.exists_isLawful_extend hf hc hℓ hP hPℓ
  exact ⟨r, hr, hrc, hrℓ, G.admits_of_isLawful Q hfull hadm hdon href hmk hr⟩

/-- **The donor face lies in a second coatom**: if the root misses a point of the context, some
point `y` other than the new point is extreme in the faces of the carrier, and the coatom
`univ.erase y` contains the donor face. -/
theorem exists_donorCoatom (he : n < J) :
    ∃ y : Fin (J + 1), y ≠ Fin.last J ∧ univ.erase y ∈ G.scheme.toCellScheme.faces ∧
      univ.map (extendByLast e) ⊆ univ.erase y := by
  have hne : univ.map (extendByLast e) ≠ (univ : Finset (Fin (J + 1))) := by
    intro h
    have h1 := congrArg Finset.card h
    simp only [card_map, card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨y, hy, hsub⟩ := G.isLegal.isWellFormed.isPlan.isConvexGeometry.exists_coatom
    G.donor_mem hne
  refine ⟨y, fun hyl ↦ ?_, (Geometry.mem_extremes.mp hy).2, hsub⟩
  have hl : Fin.last J ∈ univ.map (extendByLast e) :=
    mem_map.mpr ⟨Fin.last n, mem_univ _, by simp⟩
  have := hsub hl
  rw [hyl] at this
  simp at this

end GrowthCarrier

namespace Scheme

variable {β : Ordinal.{u}} {M J n : ℕ} {S : Scheme.{u} M} {t' : StageType.{u} β J}
  {D : Scheme.{u} (n + 1)}

/-- **Admission below the threshold**: in a consistent scheme `S` carrying the cells of a context
`t'` (through `κ`, at their grades) and of a donor `D` (through `δ`, at grades at most the
threshold), with a cell of full scope at the threshold, every such cell a controller admitted on
the class, every labelling lawful below the full face at the threshold is admitted by the requests.
Only the cells below `(univ, N)` are used: availability at the cap gives an admitted controller,
whose row transfers (`Scheme.exists_controllerRead`). -/
theorem admits_of_isLawfulBelow (hcons : S.rows.IsConsistent)
    (Q : StageType.GrowthRequests t' D) (κ : Fin t'.card → Fin S.card)
    (δ : Fin D.card → Fin S.card)
    (hκ : ∀ x, S.toCellScheme.grade (κ x) = t'.toCellScheme.grade x)
    (hδ : ∀ j, S.toCellScheme.grade (δ j) ≤ Q.threshold)
    (hfull : ∃ w, S.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hadm : ∀ u, S.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
        S.rowAt u (κ x) = ⊥ → t'.label x = ⊥) → S.rowAt u (κ Q.cap) ≠ ⊥ →
      ∀ j, Q.CorrectAt (fun x ↦ S.rowAt u (κ x)) j (S.rowAt u (δ j)))
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold)
    {v : Fin S.card → Label.{u}}
    (hv : S.rows.IsLawfulBelow ((univ : Finset (Fin M)), Q.threshold) fun z ↦ v z) :
    Q.Admits (fun x ↦ v (κ x)) (fun j ↦ v (δ j)) := by
  intro hclass hcap j
  obtain ⟨hord, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hv
  obtain ⟨w, hw⟩ := hfull
  have hcN : S.toCellScheme.grade (κ Q.cap) = Q.threshold := hκ Q.cap
  have hbelowN (z : Fin S.card) (hz : S.toCellScheme.grade z ≤ Q.threshold) :
      z ∈ S.toCellScheme.below ((univ : Finset (Fin M)), Q.threshold) := by
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff]
    exact ⟨subset_univ _, hz⟩
  have hwb : w ∈ S.toCellScheme.below ((univ : Finset (Fin M)), Q.threshold) := by
    rw [CellScheme.mem_below, hw]
  obtain ⟨u', hu'g, hle⟩ := havail (κ Q.cap) w hwb
    (by rw [show S.toCellScheme.scope w = univ from congrArg Prod.fst hw]; exact subset_univ _)
    (hcN.trans (congrArg Prod.snd hw).symm)
  have hu' : S.toCellScheme.gradedIndex u' = (univ, Q.threshold) := hu'g.trans hw
  have hl := hloc u' (by rw [CellScheme.mem_below, hu'])
  have hvc : IsSelfVisible Q.threshold (v (κ Q.cap)) := hcN ▸ hord _ (hbelowN _ hcN.le)
  obtain ⟨Φ, -, hΦb, -, hΦ⟩ := exists_controllerRead hl
    (mem_below_of_gradedIndex_eq hu' hcN.le) hcN hle
  -- the row of the controller is in the class
  have hrow : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      S.rowAt u' (κ x) = ⊥ → t'.label x = ⊥ := by
    intro x hx hr
    have hxN : S.toCellScheme.grade (κ x) ≤ Q.threshold := by
      rw [hκ]
      exact hx.2
    have h := hΦ _ (mem_below_of_gradedIndex_eq hu' hxN) hxN
    rw [hr, min_eq_left bot_le, hΦb] at h
    refine hclass x hx ?_
    rcases min_eq_bot.mp h with h' | h'
    · exact h'
    · exact absurd h' hcap
  have hrc : S.rowAt u' (κ Q.cap) ≠ ⊥ := by
    intro hr
    have h := hΦ _ (mem_below_of_gradedIndex_eq hu' hcN.le) hcN.le
    rw [min_self, hr, min_self, hΦb] at h
    exact hcap h
  have hA := hadm u' hu' hrow hrc j
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · exact min_eq_bot_of_controller hl hcN hle hu' (hδ j) (hA.1 hz)
  · rw [StageType.GrowthRequests.readExact]
    have hr := href j hf
    exact min_eq_visibilityReplace_of_controller hcons hl hvc hcN hle hu' hr.2 (hδ j)
      ((hκ _).trans_le hr.1) (hA.2.1 hf)
  · rw [StageType.GrowthRequests.readMarker]
    exact visibilityReplace_le_of_controller hcons hl hvc hcN hle hu' hmk.2
      ((hκ _).trans_le hmk.1) (hδ j) (hA.2.2 hy)

end Scheme

end VaughtConjecture

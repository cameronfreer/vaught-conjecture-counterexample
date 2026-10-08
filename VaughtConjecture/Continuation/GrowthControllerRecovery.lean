/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRequests

/-!
# Recovery through an admitted controller at the activation grade

Roadmap, Layer 3 ((R3) and (R4), the recovery of the growth carrier).  Let `u` be a cell of a
scheme with consistent rows, and `v` a lawful section with `v c ≤ v u` at a cell `c` of grade `N`
below `u`.  Locality at `u` gives a witness `(g, σ)` with `min (v d) (v u) = min (σ (row_u d))
(g (grade d))`; capping at `v c` gives, at every cell `d` below `u` of grade at most `N`,

  `min (v d) (v c) = Φ (min (row_u d) (row_u c))`,  `Φ x = min (σ x) (g N)`

(`Scheme.exists_controllerRead`), and `Φ` is monotone, fixes `⊥`, and commutes with visibility
replacement at the threshold `N` with every value `i ≤ N` (the commutation law of the witness
below the suppressor at `N`, and `Label.IsWitness.lt_apply_visibilityReplace` above it).  So
every relation of the form of the requests (`StageType.GrowthRequests.CorrectAt`) that the row of
`u` satisfies, the section `v` satisfies:
bottom requests, exact requests read through a reference at an offset `≤ N`, and high requests
read through a marker at an offset `≤ N` (`Scheme.min_eq_bot_of_controller`,
`Scheme.min_eq_readExact_of_controller`, `Scheme.readMarker_le_of_controller`).

**The admitted-controller recovery** (`GrowthCarrier.recovers_of_admittedControllers`).  If every
cell of a growth carrier at the **activation index** `(univ, N)`, `N` the grade of the cap, has a
row that satisfies the requests (an **admitted controller**), if some cell has that index, and if
the request cells (the donor cells, the references, the marker) have grade at most `N`, then the
carrier recovers the relation of the requests from **every** context section: availability at the
image of the cap gives an admitted controller `u` with `v c ≤ v u`.  This is the recovery of the
growth construction, compiled for native rows with no coding hypothesis; what it asks of the
carrier is structural (its cells at the activation index), and constructing a **bountiful**
carrier with only admitted controllers there is the open part of the construction.

## References

Locality and witnesses are [Kni26, Definition 2.3.9 and Definition 2.5.12]; the reading of a cell
through the row of a controller is the growth step of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {m : ℕ} {S : Scheme.{u} m}

/-- The rows of a consistent scheme are self-visible at the grades of the cells they read. -/
theorem isSelfVisible_rowAt (hcons : S.rows.IsConsistent) {u x : Fin S.card}
    (hx : x ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u)) :
    IsSelfVisible (S.toCellScheme.grade x) (S.rowAt u x) := by
  rw [rowAt_of_mem hx]
  exact (hcons u).orderly ⟨x, hx⟩

/-- **The capped controller map commutes with visibility replacement**: for a witness `(g, σ)`,
`x ↦ min (σ x) (g N)` commutes with visibility replacement at `N` with every value `i ≤ N`. -/
theorem _root_.VaughtConjecture.Label.IsWitness.min_visibilityReplace {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ) {N i : ℕ} (hi : i ≤ N) (x : Label.{u}) :
    min (σ (visibilityReplace N i x)) (g N) = visibilityReplace N i (min (σ x) (g N)) := by
  by_cases hx : σ x ≤ g N
  · rw [hw.visibilityReplace_comm x N hx i hi, min_eq_left hx,
      min_eq_left (visibilityReplace_le_of_le hi (hw.isSelfVisible N) hx)]
  · have hlt := hw.lt_apply_visibilityReplace (not_le.mp hx) hi
    rw [min_eq_right hlt.le, min_eq_right (not_le.mp hx).le,
      (hw.isSelfVisible N).visibilityReplace_eq]

/-- **The controller read**: under a lawful section `v` with `v c ≤ v u`, `c` of grade `N` below
`u`, some monotone map `Φ` fixing `⊥` and commuting with visibility replacement at `N` (values
`≤ N`) reads `min (v d) (v c)` off the row of `u` capped at `c`, at every cell `d` below `u` of
grade at most `N`. -/
theorem exists_controllerRead {v : Fin S.card → Label.{u}} (hv : S.rows.IsLawful v)
    {u c : Fin S.card} {N : ℕ} (hc : c ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (hcN : S.toCellScheme.grade c = N) (hcu : v c ≤ v u) :
    ∃ Φ : Label.{u} → Label.{u}, Monotone Φ ∧ Φ ⊥ = ⊥ ∧
      (∀ i ≤ N, ∀ x, Φ (visibilityReplace N i x) = visibilityReplace N i (Φ x)) ∧
      ∀ d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u), S.toCellScheme.grade d ≤ N →
        min (v d) (v c) = Φ (min (S.rowAt u d) (S.rowAt u c)) := by
  obtain ⟨g, σ, hw, hq⟩ := hv.locality u
  refine ⟨fun x ↦ min (σ x) (g N), fun x y hxy ↦ min_le_min_right _ (hw.monotone hxy),
    by simp [hw.map_bot], fun i hi x ↦ hw.min_visibilityReplace hi x, fun d hd hdN ↦ ?_⟩
  have hqd := hq ⟨d, hd⟩
  have hqc := hq ⟨c, hc⟩
  simp only at hqd hqc
  rw [← rowAt_of_mem hd] at hqd
  rw [← rowAt_of_mem hc, hcN] at hqc
  have hgd : g N ≤ g (S.toCellScheme.grade d) := hw.antitone hdN
  have hvc : v c = min (σ (S.rowAt u c)) (g N) := by rw [← hqc, min_eq_left hcu]
  calc min (v d) (v c) = min (min (v d) (v u)) (v c) := by
        rw [min_assoc, min_eq_right hcu]
    _ = min (min (σ (S.rowAt u d)) (g (S.toCellScheme.grade d)))
          (min (σ (S.rowAt u c)) (g N)) := by rw [hqd, ← hvc]
    _ = min (min (σ (S.rowAt u d)) (σ (S.rowAt u c))) (g N) := by
        rw [min_min_min_comm, min_eq_right hgd]
    _ = min (σ (min (S.rowAt u d) (S.rowAt u c))) (g N) := by
        rw [hw.monotone.map_min]

/-- A cell has grade at most `N` exactly when it lies below a controller of full scope and grade
`N`. -/
theorem mem_below_of_gradedIndex_eq {N : ℕ} {u d : Fin S.card}
    (hu : S.toCellScheme.gradedIndex u = (univ, N)) (hd : S.toCellScheme.grade d ≤ N) :
    d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u) := by
  rw [CellScheme.mem_below, hu, CellScheme.gradedIndex_le_iff]
  exact ⟨subset_univ _, hd⟩

section Transfer

variable (hcons : S.rows.IsConsistent) {v : Fin S.card → Label.{u}} (hv : S.rows.IsLawful v)
  {u c : Fin S.card} {N : ℕ} (hcN : S.toCellScheme.grade c = N) (hcu : v c ≤ v u)
include hv hcN hcu

variable (hu : S.toCellScheme.gradedIndex u = (univ, N))
include hu

/-- **A bottom request transfers** from the row of a controller to a lawful section. -/
theorem min_eq_bot_of_controller {z : Fin S.card} (hz : S.toCellScheme.grade z ≤ N)
    (h : min (S.rowAt u z) (S.rowAt u c) = ⊥) : min (v z) (v c) = ⊥ := by
  obtain ⟨Φ, -, hΦb, -, hΦ⟩ := exists_controllerRead hv
    (mem_below_of_gradedIndex_eq hu hcN.le) hcN hcu
  rw [hΦ z (mem_below_of_gradedIndex_eq hu hz) hz, h, hΦb]

include hcons in
/-- **An exact request transfers** from the row of a controller to a lawful section: a read
through a reference at an offset `i ≤ N`. -/
theorem min_eq_visibilityReplace_of_controller {x y : Fin S.card} {i : ℕ} (hi : i ≤ N)
    (hx : S.toCellScheme.grade x ≤ N) (hy : S.toCellScheme.grade y ≤ N)
    (h : min (S.rowAt u x) (S.rowAt u c) =
      min (visibilityReplace N i (S.rowAt u y)) (S.rowAt u c)) :
    min (v x) (v c) = min (visibilityReplace N i (v y)) (v c) := by
  have hcb := mem_below_of_gradedIndex_eq hu hcN.le
  obtain ⟨Φ, -, -, hΦv, hΦ⟩ := exists_controllerRead hv hcb hcN hcu
  have hrc : IsSelfVisible N (S.rowAt u c) := hcN ▸ isSelfVisible_rowAt hcons hcb
  have hvc : IsSelfVisible N (v c) := hcN ▸ hv.orderly c
  rw [hΦ x (mem_below_of_gradedIndex_eq hu hx) hx, h,
    ← visibilityReplace_min_of_isSelfVisible hi hrc, hΦv i hi,
    ← hΦ y (mem_below_of_gradedIndex_eq hu hy) hy, visibilityReplace_min_of_isSelfVisible hi hvc]

include hcons in
/-- **A high request transfers** from the row of a controller to a lawful section: a read through
a marker at an offset `i ≤ N`. -/
theorem visibilityReplace_le_of_controller {a y : Fin S.card} {i : ℕ} (hi : i ≤ N)
    (ha : S.toCellScheme.grade a ≤ N) (hy : S.toCellScheme.grade y ≤ N)
    (h : min (visibilityReplace N i (S.rowAt u a)) (S.rowAt u c) ≤
      min (S.rowAt u y) (S.rowAt u c)) :
    min (visibilityReplace N i (v a)) (v c) ≤ min (v y) (v c) := by
  have hcb := mem_below_of_gradedIndex_eq hu hcN.le
  obtain ⟨Φ, hΦm, -, hΦv, hΦ⟩ := exists_controllerRead hv hcb hcN hcu
  have hrc : IsSelfVisible N (S.rowAt u c) := hcN ▸ isSelfVisible_rowAt hcons hcb
  have hvc : IsSelfVisible N (v c) := hcN ▸ hv.orderly c
  rw [hΦ y (mem_below_of_gradedIndex_eq hu hy) hy, ← visibilityReplace_min_of_isSelfVisible hi hvc,
    hΦ a (mem_below_of_gradedIndex_eq hu ha) ha, ← hΦv i hi]
  rw [← visibilityReplace_min_of_isSelfVisible hi hrc] at h
  exact hΦm h

end Transfer

end Scheme

/-! ### The admitted-controller recovery of a growth carrier -/

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier t'.toScheme D e) (Q : StageType.GrowthRequests t' D)

/-- The cell of the carrier at a cell of the context, along the context face. -/
noncomputable def contextCell (x : Fin t'.card) : Fin G.scheme.card :=
  G.scheme.faceCell Fin.castSuccEmb G.comap_context x

/-- The cell of the carrier at a cell of the donor, along the donor face. -/
noncomputable def donorCell (j : Fin D.card) : Fin G.scheme.card :=
  G.scheme.faceCell (extendByLast e) G.comap_donor j

/-- An **admitted controller**: a cell of the carrier whose row, read on the context face and on
the donor face, satisfies the requests. -/
def IsAdmittedController (u : Fin G.scheme.card) : Prop :=
  ∀ j, Q.CorrectAt (fun x ↦ G.scheme.rowAt u (G.contextCell x)) j
    (G.scheme.rowAt u (G.donorCell j))

/-- **The admitted-controller recovery**: if the carrier has a cell of full scope at the grade `N`
of the cap, every such cell is an admitted controller, the donor cells have grade at most `N`, and
the references, the marker and their offsets are at most `N`, then the carrier recovers the
relation of the requests from every section of the context.  Availability at the cap gives an
admitted controller above it, and its row transfers to every lawful section
(`Scheme.min_eq_bot_of_controller`, `Scheme.min_eq_visibilityReplace_of_controller`,
`Scheme.visibilityReplace_le_of_controller`).  No coding hypothesis is used. -/
theorem recovers_of_admittedControllers
    (hfull : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hadm : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      G.IsAdmittedController Q u)
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold)
    (σ : Fin t'.card → Label.{u}) : G.Recovers σ (Q.CorrectAt σ) := by
  intro v hv hctx i j hij
  have hcons : G.scheme.rows.IsConsistent := G.isLegal.isConsistent
  have hvσ (x : Fin t'.card) : v (G.contextCell x) = σ x := hctx _ x rfl
  have hgc (x : Fin t'.card) :
      G.scheme.toCellScheme.grade (G.contextCell x) = t'.toCellScheme.grade x :=
    G.scheme.grade_faceCell G.comap_context x
  have hdj : G.scheme.cellMap (extendByLast e) i = G.donorCell j :=
    congrArg (G.scheme.cellMap (extendByLast e)) (Fin.ext hij)
  rw [hdj]
  obtain ⟨w, hw⟩ := hfull
  have hcN : G.scheme.toCellScheme.grade (G.contextCell Q.cap) = Q.threshold := hgc Q.cap
  obtain ⟨u', hu'g, hle⟩ := hv.availability (G.contextCell Q.cap) w
    (by rw [show G.scheme.toCellScheme.scope w = univ from congrArg Prod.fst hw]
        exact subset_univ _)
    (hcN.trans (congrArg Prod.snd hw).symm)
  have hu' : G.scheme.toCellScheme.gradedIndex u' = (univ, Q.threshold) := hu'g.trans hw
  have hA := hadm u' hu' j
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [← hvσ]
    exact Scheme.min_eq_bot_of_controller hv hcN hle hu' (hdon j) (hA.1 hz)
  · rw [StageType.GrowthRequests.readExact, ← hvσ, ← hvσ]
    have hr := href j hf
    exact Scheme.min_eq_visibilityReplace_of_controller hcons hv hcN hle hu' hr.2 (hdon j)
      ((hgc _).trans_le hr.1) (hA.2.1 hf)
  · rw [StageType.GrowthRequests.readMarker, ← hvσ, ← hvσ]
    exact Scheme.visibilityReplace_le_of_controller hcons hv hcN hle hu' hmk.2
      ((hgc _).trans_le hmk.1) (hdon j) (hA.2.2 hy)

/-- A **controller admitted on the class** of `t'` below the cap: a cell whose row satisfies the
requests whenever its row reads no cell of `t'` below the cap as `⊥` unless `t'` does, and reads
the cap above `⊥`.  This asks correctness of fewer rows than `IsAdmittedController`. -/
def IsClassAdmittedController (u : Fin G.scheme.card) : Prop :=
  (∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      G.scheme.rowAt u (G.contextCell x) = ⊥ → t'.label x = ⊥) →
    G.scheme.rowAt u (G.contextCell Q.cap) ≠ ⊥ → G.IsAdmittedController Q u

/-- **The admitted-controller recovery on the class**: as `recovers_of_admittedControllers`, with
controllers admitted only on the class, for every context section `σ` with the bottom pattern of
`t'` below the cap and a cap value other than `⊥`.  The bottom pattern transfers from `σ` to the
row of the controller in one direction: a row value `⊥` is read as `⊥` (the map `Φ` of
`Scheme.exists_controllerRead` fixes `⊥`), while a positive row value may be read as `⊥`. -/
theorem recovers_of_classAdmittedControllers
    (hfull : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hadm : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      G.IsClassAdmittedController Q u)
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold)
    {σ : Fin t'.card → Label.{u}}
    (hclass : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      σ x = ⊥ → t'.label x = ⊥)
    (hcap : σ Q.cap ≠ ⊥) : G.Recovers σ (Q.CorrectAt σ) := by
  intro v hv hctx i j hij
  have hcons : G.scheme.rows.IsConsistent := G.isLegal.isConsistent
  have hvσ (x : Fin t'.card) : v (G.contextCell x) = σ x := hctx _ x rfl
  have hgc (x : Fin t'.card) :
      G.scheme.toCellScheme.grade (G.contextCell x) = t'.toCellScheme.grade x :=
    G.scheme.grade_faceCell G.comap_context x
  have hdj : G.scheme.cellMap (extendByLast e) i = G.donorCell j :=
    congrArg (G.scheme.cellMap (extendByLast e)) (Fin.ext hij)
  rw [hdj]
  obtain ⟨w, hw⟩ := hfull
  have hcN : G.scheme.toCellScheme.grade (G.contextCell Q.cap) = Q.threshold := hgc Q.cap
  obtain ⟨u', hu'g, hle⟩ := hv.availability (G.contextCell Q.cap) w
    (by rw [show G.scheme.toCellScheme.scope w = univ from congrArg Prod.fst hw]
        exact subset_univ _)
    (hcN.trans (congrArg Prod.snd hw).symm)
  have hu' : G.scheme.toCellScheme.gradedIndex u' = (univ, Q.threshold) := hu'g.trans hw
  obtain ⟨Φ, -, hΦb, -, hΦ⟩ := Scheme.exists_controllerRead hv
    (Scheme.mem_below_of_gradedIndex_eq hu' hcN.le) hcN hle
  have hvc : v (G.contextCell Q.cap) ≠ ⊥ := by rw [hvσ]; exact hcap
  -- the row of the controller is in the class
  have hrow : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      G.scheme.rowAt u' (G.contextCell x) = ⊥ → t'.label x = ⊥ := by
    intro x hx hr
    have hxN : G.scheme.toCellScheme.grade (G.contextCell x) ≤ Q.threshold := by
      rw [hgc]
      exact hx.2
    have h := hΦ _ (Scheme.mem_below_of_gradedIndex_eq hu' hxN) hxN
    rw [hr, min_eq_left bot_le, hΦb] at h
    refine hclass x hx ?_
    rw [← hvσ]
    rcases min_eq_bot.mp h with h' | h'
    · exact h'
    · exact absurd h' hvc
  have hrc : G.scheme.rowAt u' (G.contextCell Q.cap) ≠ ⊥ := by
    intro hr
    have h := hΦ _ (Scheme.mem_below_of_gradedIndex_eq hu' hcN.le) hcN.le
    rw [min_self, hr, min_self, hΦb] at h
    exact hvc h
  have hA := hadm u' hu' hrow hrc j
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · rw [← hvσ]
    exact Scheme.min_eq_bot_of_controller hv hcN hle hu' (hdon j) (hA.1 hz)
  · rw [StageType.GrowthRequests.readExact, ← hvσ, ← hvσ]
    have hr := href j hf
    exact Scheme.min_eq_visibilityReplace_of_controller hcons hv hcN hle hu' hr.2 (hdon j)
      ((hgc _).trans_le hr.1) (hA.2.1 hf)
  · rw [StageType.GrowthRequests.readMarker, ← hvσ, ← hvσ]
    exact Scheme.visibilityReplace_le_of_controller hcons hv hcN hle hu' hmk.2
      ((hgc _).trans_le hmk.1) (hdon j) (hA.2.2 hy)

end GrowthCarrier

end VaughtConjecture

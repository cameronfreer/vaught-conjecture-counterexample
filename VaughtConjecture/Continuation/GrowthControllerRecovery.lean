/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRequests
import VaughtConjecture.Extension.CappedDecoder

/-!
# Recovery through an admitted controller at the activation grade

Roadmap, Layer 3 ((R3) and (R4), the recovery of the growth carrier).  Let `u` be a cell of a
scheme with consistent rows, and `v` a lawful section with `v c ≤ v u` at a cell `c` of grade `N`
below `u`.  Locality at `u` gives a witness `(g, σ)` with `min (v d) (v u) = min (σ (row_u d))
(g (grade d))`; capping at `v c` gives, at every cell `d` below `u` of grade at most `N`,

  `min (v d) (v c) = Φ (min (row_u d) (row_u c))`,  `Φ x = min (σ x) (g N)`

(`Scheme.exists_controllerRead`), and `Φ` is monotone, fixes `⊥`, and commutes with visibility
replacement at the threshold `N` with every value `i ≤ N` (the commutation law of the witness
below the suppressor at `N`, and `Label.IsWitness.lt_apply_visibilityReplace` above it;
`Label.IsWitness.min_visibilityReplace`).  So
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

/-- **The controller read**: under a section `v` local at `u` (as a lawful section is), with
`v c ≤ v u`, `c` of grade `N` below
`u`, some monotone map `Φ` fixing `⊥` and commuting with visibility replacement at `N` (values
`≤ N`) reads `min (v d) (v c)` off the row of `u` capped at `c`, at every cell `d` below `u` of
grade at most `N`. -/
theorem exists_controllerRead {v : Fin S.card → Label.{u}} {u c : Fin S.card}
    (hloc : TransformsTo (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex u) ↦
      S.toCellScheme.grade d) (S.rows.row u) fun d ↦ min (v d) (v u))
    {N : ℕ} (hc : c ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (hcN : S.toCellScheme.grade c = N) (hcu : v c ≤ v u) :
    ∃ Φ : Label.{u} → Label.{u}, Monotone Φ ∧ Φ ⊥ = ⊥ ∧
      (∀ i ≤ N, ∀ x, Φ (visibilityReplace N i x) = visibilityReplace N i (Φ x)) ∧
      ∀ d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u), S.toCellScheme.grade d ≤ N →
        min (v d) (v c) = Φ (min (S.rowAt u d) (S.rowAt u c)) := by
  obtain ⟨g, σ, hw, hq⟩ := hloc
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

variable (hcons : S.rows.IsConsistent) {v : Fin S.card → Label.{u}} {u c : Fin S.card}
  (hloc : TransformsTo (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex u) ↦
    S.toCellScheme.grade d) (S.rows.row u) fun d ↦ min (v d) (v u))
  {N : ℕ} (hvc : IsSelfVisible N (v c)) (hcN : S.toCellScheme.grade c = N) (hcu : v c ≤ v u)
include hloc hcN hcu

variable (hu : S.toCellScheme.gradedIndex u = (univ, N))
include hu

/-- **A bottom request transfers** from the row of a controller to a lawful section. -/
theorem min_eq_bot_of_controller {z : Fin S.card} (hz : S.toCellScheme.grade z ≤ N)
    (h : min (S.rowAt u z) (S.rowAt u c) = ⊥) : min (v z) (v c) = ⊥ := by
  obtain ⟨Φ, -, hΦb, -, hΦ⟩ := exists_controllerRead hloc
    (mem_below_of_gradedIndex_eq hu hcN.le) hcN hcu
  rw [hΦ z (mem_below_of_gradedIndex_eq hu hz) hz, h, hΦb]

include hcons hvc in
/-- **An exact request transfers** from the row of a controller to a lawful section: a read
through a reference at an offset `i ≤ N`. -/
theorem min_eq_visibilityReplace_of_controller {x y : Fin S.card} {i : ℕ} (hi : i ≤ N)
    (hx : S.toCellScheme.grade x ≤ N) (hy : S.toCellScheme.grade y ≤ N)
    (h : min (S.rowAt u x) (S.rowAt u c) =
      min (visibilityReplace N i (S.rowAt u y)) (S.rowAt u c)) :
    min (v x) (v c) = min (visibilityReplace N i (v y)) (v c) := by
  have hcb := mem_below_of_gradedIndex_eq hu hcN.le
  obtain ⟨Φ, -, -, hΦv, hΦ⟩ := exists_controllerRead hloc hcb hcN hcu
  have hrc : IsSelfVisible N (S.rowAt u c) := hcN ▸ isSelfVisible_rowAt hcons hcb
  rw [hΦ x (mem_below_of_gradedIndex_eq hu hx) hx, h,
    ← visibilityReplace_min_of_isSelfVisible hi hrc, hΦv i hi,
    ← hΦ y (mem_below_of_gradedIndex_eq hu hy) hy, visibilityReplace_min_of_isSelfVisible hi hvc]

include hcons hvc in
/-- **A high request transfers** from the row of a controller to a lawful section: a read through
a marker at an offset `i ≤ N`. -/
theorem visibilityReplace_le_of_controller {a y : Fin S.card} {i : ℕ} (hi : i ≤ N)
    (ha : S.toCellScheme.grade a ≤ N) (hy : S.toCellScheme.grade y ≤ N)
    (h : min (visibilityReplace N i (S.rowAt u a)) (S.rowAt u c) ≤
      min (S.rowAt u y) (S.rowAt u c)) :
    min (visibilityReplace N i (v a)) (v c) ≤ min (v y) (v c) := by
  have hcb := mem_below_of_gradedIndex_eq hu hcN.le
  obtain ⟨Φ, hΦm, -, hΦv, hΦ⟩ := exists_controllerRead hloc hcb hcN hcu
  have hrc : IsSelfVisible N (S.rowAt u c) := hcN ▸ isSelfVisible_rowAt hcons hcb
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
    exact Scheme.min_eq_bot_of_controller (hv.locality u') hcN hle hu' (hdon j) (hA.1 hz)
  · rw [StageType.GrowthRequests.readExact, ← hvσ, ← hvσ]
    have hr := href j hf
    exact Scheme.min_eq_visibilityReplace_of_controller hcons (hv.locality u')
      (hcN ▸ hv.orderly _) hcN hle hu' hr.2 (hdon j)
      ((hgc _).trans_le hr.1) (hA.2.1 hf)
  · rw [StageType.GrowthRequests.readMarker, ← hvσ, ← hvσ]
    exact Scheme.visibilityReplace_le_of_controller hcons (hv.locality u')
      (hcN ▸ hv.orderly _) hcN hle hu' hmk.2
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
  obtain ⟨Φ, -, hΦb, -, hΦ⟩ := Scheme.exists_controllerRead (hv.locality u')
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
    exact Scheme.min_eq_bot_of_controller (hv.locality u') hcN hle hu' (hdon j) (hA.1 hz)
  · rw [StageType.GrowthRequests.readExact, ← hvσ, ← hvσ]
    have hr := href j hf
    exact Scheme.min_eq_visibilityReplace_of_controller hcons (hv.locality u')
      (hcN ▸ hv.orderly _) hcN hle hu' hr.2 (hdon j)
      ((hgc _).trans_le hr.1) (hA.2.1 hf)
  · rw [StageType.GrowthRequests.readMarker, ← hvσ, ← hvσ]
    exact Scheme.visibilityReplace_le_of_controller hcons (hv.locality u')
      (hcN ▸ hv.orderly _) hcN hle hu' hmk.2
      ((hgc _).trans_le hmk.1) (hdon j) (hA.2.2 hy)

/-! ### What bountifulness at the activation grade asks of the requests -/

/-- The **context face at the grade `N`**: the graded pair of the first points at `N`. -/
def contextIndex (N : ℕ) : Finset (Fin (J + 1)) × ℕ := (univ.map Fin.castSuccEmb, N)

theorem contextIndex_le (N : ℕ) :
    contextIndex (J := J) N ≤ ((univ : Finset (Fin (J + 1))), N) :=
  ⟨subset_univ _, le_rfl⟩

/-- A cell of the context of grade at most `N` lies below the context face at `N`. -/
theorem contextCell_mem_below {N : ℕ} {x : Fin t'.card} (hx : t'.toCellScheme.grade x ≤ N) :
    G.contextCell x ∈ G.scheme.toCellScheme.below (contextIndex N) := by
  rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff, contextCell,
    G.scheme.scope_faceCell, G.scheme.grade_faceCell]
  exact ⟨map_subset_map.mpr (subset_univ _), hx⟩

/-- **Bountifulness at the activation grade forces the capped request lift.**  Let the rows of
the carrier lift capped from the context face at `N` to `(univ, N)`, every cell at `(univ, N)` be
a controller admitted on the class, and the request cells have grade at most `N`.  Then for every
labelling `w` lawful below `(univ, N)`, every cap `γ` self-visible at `N`, and every labelling `s`
lawful below the context face that agrees with `w` capped at `γ`, has the bottom class of `t'`
below the cap, and a cap value other than `⊥`, some `w'` lawful below `(univ, N)` agrees with `w`
capped at `γ`, is `s` on the context face, and reads the requests from `s` on the donor face.

So every lawful section of the context in the cap ball of a lawful section below `(univ, N)`,
read through the requests, is the donor face of a lawful section; a context and a donor where
this fails obstruct every bountiful carrier with admitted controllers at the activation grade. -/
theorem exists_requestLift_of_cappedLift
    (hlift : G.scheme.rows.CappedLift (contextIndex_le (J := J) Q.threshold))
    (hfull : ∃ w₀, G.scheme.toCellScheme.gradedIndex w₀ = (univ, Q.threshold))
    (hadm : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      G.IsClassAdmittedController Q u)
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    (href : ∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
      Q.offset j ≤ Q.threshold)
    (hmk : t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold)
    {w s : Fin G.scheme.card → Label.{u}}
    (hw : G.scheme.rows.IsLawfulBelow (univ, Q.threshold) fun d ↦ w d)
    (hs : G.scheme.rows.IsLawfulBelow (contextIndex Q.threshold) fun d ↦ s d)
    {γ : Label.{u}} (hγ : IsSelfVisible Q.threshold γ)
    (hag : ∀ d ∈ G.scheme.toCellScheme.below (contextIndex Q.threshold),
      min (s d) γ = min (w d) γ)
    (hclass : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      s (G.contextCell x) = ⊥ → t'.label x = ⊥)
    (hcap : s (G.contextCell Q.cap) ≠ ⊥) :
    ∃ w' : Fin G.scheme.card → Label.{u},
      G.scheme.rows.IsLawfulBelow (univ, Q.threshold) (fun d ↦ w' d) ∧
      (∀ d ∈ G.scheme.toCellScheme.below (univ, Q.threshold), min (w' d) γ = min (w d) γ) ∧
      (∀ d ∈ G.scheme.toCellScheme.below (contextIndex Q.threshold), w' d = s d) ∧
      ∀ j, Q.CorrectAt (fun x ↦ s (G.contextCell x)) j (w' (G.donorCell j)) := by
  classical
  set N := Q.threshold
  obtain ⟨q', ⟨hq', hq'cap⟩, hq'eq⟩ := hlift γ hγ (fun d ↦ w d) hw
    ⟨hs, fun d ↦ hag d.1 d.2⟩
  let w' : Fin G.scheme.card → Label.{u} := fun d ↦
    if h : d ∈ G.scheme.toCellScheme.below (univ, N) then q' ⟨d, h⟩ else ⊥
  have hw'q : (fun d : G.scheme.toCellScheme.below (univ, N) ↦ w' d) = q' := by
    funext d
    simp only [w']
    exact dite_eq_left_of_eq_true (eq_true d.2)
  have hbelow (d : Fin G.scheme.card) (hd : G.scheme.toCellScheme.grade d ≤ N) :
      d ∈ G.scheme.toCellScheme.below (univ, N) := by
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff]
    exact ⟨subset_univ _, hd⟩
  have hctxw (d) (hd : d ∈ G.scheme.toCellScheme.below (contextIndex N)) : w' d = s d := by
    have h1 := congrFun hq'eq ⟨d, hd⟩
    have hdN : d ∈ G.scheme.toCellScheme.below (univ, N) :=
      G.scheme.toCellScheme.below_mono (contextIndex_le N) hd
    simp only [Function.comp_apply, Set.inclusion] at h1
    simp only [w', hdN, dite_true]
    exact h1
  have hlaw : G.scheme.rows.IsLawfulBelow (univ, N) (fun d ↦ w' d) := by
    rw [hw'q]; exact hq'
  refine ⟨w', hlaw, fun d hd ↦ ?_, hctxw, ?_⟩
  · have h1 := hq'cap ⟨d, hd⟩
    simp only [w', hd, dite_true]
    exact h1
  -- the recovery, below `(univ, N)`
  obtain ⟨hord, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hlaw
  have hcons : G.scheme.rows.IsConsistent := G.isLegal.isConsistent
  have hgc (x : Fin t'.card) :
      G.scheme.toCellScheme.grade (G.contextCell x) = t'.toCellScheme.grade x :=
    G.scheme.grade_faceCell G.comap_context x
  have hcN : G.scheme.toCellScheme.grade (G.contextCell Q.cap) = N := hgc Q.cap
  have hsx (x : Fin t'.card) (hx : t'.toCellScheme.grade x ≤ N) :
      w' (G.contextCell x) = s (G.contextCell x) :=
    hctxw _ (G.contextCell_mem_below hx)
  obtain ⟨w₀, hw₀⟩ := hfull
  obtain ⟨u', hu'g, hle⟩ := havail (G.contextCell Q.cap) w₀ (hbelow w₀ (by
      rw [show G.scheme.toCellScheme.grade w₀ = N from congrArg Prod.snd hw₀]))
    (by rw [show G.scheme.toCellScheme.scope w₀ = univ from congrArg Prod.fst hw₀]
        exact subset_univ _)
    (hcN.trans (congrArg Prod.snd hw₀).symm)
  have hu' : G.scheme.toCellScheme.gradedIndex u' = (univ, N) := hu'g.trans hw₀
  have hu'b : u' ∈ G.scheme.toCellScheme.below (univ, N) := by
    rw [CellScheme.mem_below, hu']
  have hloc' := hloc u' hu'b
  have hvc : IsSelfVisible N (w' (G.contextCell Q.cap)) :=
    hcN ▸ hord _ (hbelow _ hcN.le)
  obtain ⟨Φ, -, hΦb, -, hΦ⟩ := Scheme.exists_controllerRead hloc'
    (Scheme.mem_below_of_gradedIndex_eq hu' hcN.le) hcN hle
  have hcap' : w' (G.contextCell Q.cap) ≠ ⊥ := by rw [hsx _ le_rfl]; exact hcap
  have hrow : ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      G.scheme.rowAt u' (G.contextCell x) = ⊥ → t'.label x = ⊥ := by
    intro x hx hr
    have hxN : G.scheme.toCellScheme.grade (G.contextCell x) ≤ N := by
      rw [hgc]; exact hx.2
    have h := hΦ _ (Scheme.mem_below_of_gradedIndex_eq hu' hxN) hxN
    rw [hr, min_eq_left bot_le, hΦb] at h
    refine hclass x hx ?_
    rw [← hsx x (by rw [← hgc]; exact hxN)]
    rcases min_eq_bot.mp h with h' | h'
    · exact h'
    · exact absurd h' hcap'
  have hrc : G.scheme.rowAt u' (G.contextCell Q.cap) ≠ ⊥ := by
    intro hr
    have h := hΦ _ (Scheme.mem_below_of_gradedIndex_eq hu' hcN.le) hcN.le
    rw [min_self, hr, min_self, hΦb] at h
    exact hcap' h
  intro j
  have hA := hadm u' hu' hrow hrc j
  refine ⟨fun hz ↦ ?_, fun hf ↦ ?_, fun hy ↦ ?_⟩
  · beta_reduce
    rw [← hsx _ le_rfl]
    exact Scheme.min_eq_bot_of_controller hloc' hcN hle hu' (hdon j) (hA.1 hz)
  · beta_reduce
    rw [StageType.GrowthRequests.readExact, ← hsx _ le_rfl, ← hsx _ (href j hf).1]
    exact Scheme.min_eq_visibilityReplace_of_controller hcons hloc' hvc hcN hle hu'
      (href j hf).2 (hdon j) ((hgc _).trans_le (href j hf).1) (hA.2.1 hf)
  · beta_reduce
    rw [StageType.GrowthRequests.readMarker, ← hsx _ le_rfl, ← hsx _ hmk.1]
    exact Scheme.visibilityReplace_le_of_controller hcons hloc' hvc hcN hle hu' hmk.2
      ((hgc _).trans_le hmk.1) (hdon j) (hA.2.2 hy)

end GrowthCarrier

end VaughtConjecture

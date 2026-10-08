/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRecognition
import VaughtConjecture.Label.FieldLadder

/-!
# Recognition from the field ladder

Roadmap, Layer 3 ((R3) and (R4), the recognition of admitted states in a growth carrier).

A growth carrier **carries a field ladder** when it has, for each member `a` of a finite family,
rungs `r a i` (`i < H`) of scope the ground set and grade `1`, whose rows read the diagonal code at
the rung itself and the code of the preceding rank at the preceding rung
(`Label.ladderSource`, `Label.ladderSource_diag`).  Its controllers at the threshold are **ladder
controllers** (`GrowthCarrier.IsLadderController`) when the row of each stores, on the context and
donor cells, a state admitted on the exact class, reads the rungs of its member `a` as a table
`F (i + 1)`, reads the top rung of `a` as itself, and every positive context value it stores below
the cap is a value of the table.

**Recognition from the ladder** (`GrowthCarrier.recognizes_of_ladder`).  Let `v` be a lawful
section with a positive cap value and `u` a controller above the cap (availability).  The chart of
the locality of `v` at `u`, capped at the cap, reads the stored state as `v` capped at its cap value
(the controller read).  The top rung of the member of `u` is read as `u` itself, so `v` there is at
least `v u > ⊥`; the predecessor steps of the ladder (`Label.eq_bot_of_ladder_predecessor`) make
every rung positive, so the chart is positive at every value of the table, hence at every positive
stored context value: it reflects `⊥`.  So the carrier recognizes admitted states
(`GrowthCarrier.Recognizes`), and recovers by recognition (`GrowthCarrier.recovers_of_recognizes`).

What remains of the construction is to install such a ladder and such controllers: the field
ladder as cells of grade one, and the controllers' rows reading it as their members' tables.

## References

The controllers and the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier t'.toScheme D e) (Q : StageType.GrowthRequests t' D)

/-- A **ladder controller** for the member `a` with the table `F`: a cell whose row stores, on the
context and donor cells, a state admitted on the exact class, reads the rung `r a i` as `F (i + 1)`
and the top rung `r a (H - 1)` as itself, and stores below the cap only positive context values
that are values of the table. -/
def IsLadderController {Mb : Type*} {H : ℕ} (r : Mb → ℕ → Fin G.scheme.card)
    (u : Fin G.scheme.card) (a : Mb) (F : ℕ → Label.{u}) : Prop :=
  Q.AdmitsOnClass (fun x ↦ G.scheme.rowAt u (G.contextCell x))
      (fun j ↦ G.scheme.rowAt u (G.donorCell j)) ∧
    G.scheme.rowAt u (r a (H - 1)) = G.scheme.rowAt u u ∧
    (∀ i < H, G.scheme.rowAt u (r a i) = F (i + 1)) ∧
    ∀ x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap),
      G.scheme.rowAt u (G.contextCell x) ≠ ⊥ →
        ∃ i < H, G.scheme.rowAt u (G.contextCell x) = F (i + 1)

/-- **Recognition from the field ladder**: a carrier with a ladder of height `H ≥ 1` (rungs of
graded index `(univ, 1)` whose rows read the diagonal and the preceding rank), a cell of full scope
at the threshold `≥ 1`, every such cell a ladder controller, and donor cells of grade at most the
threshold, recognizes admitted states. -/
theorem recognizes_of_ladder (hthr : 1 ≤ Q.threshold)
    (hfull : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    {Mb : Type*} {H : ℕ} (hH : 0 < H) (r : Mb → ℕ → Fin G.scheme.card)
    (hr : ∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1))
    (hrd : ∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = ladderSource (i + 1) (i + 1))
    (hrp : ∀ a, ∀ i < H, 0 < i → G.scheme.rowAt (r a i) (r a (i - 1)) = ladderSource (i + 1) i)
    (hctrl : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F) :
    G.Recognizes Q := by
  intro v hv
  have hcons : G.scheme.rows.IsConsistent := G.isLegal.isConsistent
  have hgc (x : Fin t'.card) :
      G.scheme.toCellScheme.grade (G.contextCell x) = t'.toCellScheme.grade x :=
    G.scheme.grade_faceCell G.comap_context x
  have hcN : G.scheme.toCellScheme.grade (G.contextCell Q.cap) = Q.threshold := hgc Q.cap
  by_cases hc0 : v (G.contextCell Q.cap) = ⊥
  · -- the zero state
    refine ⟨fun _ ↦ ⊥, fun _ ↦ ⊥, id, ⊥, fun _ hcap ↦ absurd rfl hcap, monotone_id, rfl,
      fun _ _ _ ↦ by simp, isSelfVisible_bot _, le_of_eq hc0, fun _ _ h ↦ h,
      fun _ _ ↦ by simp, fun _ ↦ by simp⟩
  -- a controller above the cap
  obtain ⟨w, hw⟩ := hfull
  obtain ⟨u, hug, hle⟩ := hv.availability (G.contextCell Q.cap) w
    (by rw [show G.scheme.toCellScheme.scope w = univ from congrArg Prod.fst hw]
        exact subset_univ _)
    (hcN.trans (congrArg Prod.snd hw).symm)
  have hu : G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) := hug.trans hw
  obtain ⟨a, F, hadm, htop, hrung, hval⟩ := hctrl u hu
  have hub (z : Fin G.scheme.card) (hz : G.scheme.toCellScheme.grade z ≤ Q.threshold) :
      z ∈ G.scheme.toCellScheme.below (G.scheme.toCellScheme.gradedIndex u) :=
    Scheme.mem_below_of_gradedIndex_eq hu hz
  -- the witness of the locality at `u`
  obtain ⟨g, σ, hwit, hq⟩ := hv.locality u
  have hq' (z : Fin G.scheme.card) (hz : G.scheme.toCellScheme.grade z ≤ Q.threshold) :
      min (v z) (v u) = min (σ (G.scheme.rowAt u z)) (g (G.scheme.toCellScheme.grade z)) := by
    have h := hq ⟨z, hub z hz⟩
    simp only at h
    rw [← Scheme.rowAt_of_mem (hub z hz)] at h
    exact h
  set c := G.contextCell Q.cap with hcdef
  set sc := G.scheme.rowAt u c with hsc
  have hgN : g Q.threshold ≤ g 1 := hwit.antitone hthr
  -- the read at the cap
  have hvc : v c = min (σ sc) (g Q.threshold) := by
    have h := hq' c hcN.le
    rw [hcN, min_eq_left hle] at h
    exact h
  have hread (z : Fin G.scheme.card) (hz : G.scheme.toCellScheme.grade z ≤ Q.threshold) :
      min (v z) (v c) = min (σ (min (G.scheme.rowAt u z) sc)) (g Q.threshold) := by
    have hgz : g Q.threshold ≤ g (G.scheme.toCellScheme.grade z) := hwit.antitone hz
    calc min (v z) (v c) = min (min (v z) (v u)) (v c) := by rw [min_assoc, min_eq_right hle]
      _ = min (min (σ (G.scheme.rowAt u z)) (g (G.scheme.toCellScheme.grade z)))
            (min (σ sc) (g Q.threshold)) := by rw [hq' z hz, ← hvc]
      _ = min (min (σ (G.scheme.rowAt u z)) (σ sc)) (g Q.threshold) := by
          rw [min_min_min_comm, min_eq_right hgz]
      _ = min (σ (min (G.scheme.rowAt u z) sc)) (g Q.threshold) := by
          rw [hwit.monotone.map_min]
  -- the value at `u` is positive, so is the suppressor at the threshold
  have huN : G.scheme.toCellScheme.grade u = Q.threshold := congrArg Prod.snd hu
  have hvu : v u = min (σ (G.scheme.rowAt u u)) (g Q.threshold) := by
    have h := hq' u huN.le
    rw [min_self, huN] at h
    exact h
  have hvu0 : v u ≠ ⊥ := fun h0 ↦ hc0 (le_bot_iff.mp (h0 ▸ hle))
  have hg0 : g Q.threshold ≠ ⊥ := fun h0 ↦ hvu0 (by rw [hvu, h0, min_bot_right])
  -- the ladder: the top rung of `a` is positive
  have hrg (i : ℕ) (hi : i < H) : G.scheme.toCellScheme.grade (r a i) = 1 :=
    congrArg Prod.snd (hr a i hi)
  have htop0 : v (r a (H - 1)) ≠ ⊥ := by
    have h := hq' (r a (H - 1)) ((hrg _ (by omega)).trans_le hthr)
    rw [hrg _ (by omega), htop] at h
    have h1 : v u ≤ min (v (r a (H - 1))) (v u) := by
      rw [h, hvu]
      exact min_le_min_left _ hgN
    intro h0
    rw [h0, min_eq_left bot_le, le_bot_iff] at h1
    exact hvu0 h1
  -- every rung of `a` is positive
  have hall1 (z : Fin G.scheme.card) (i : ℕ) (hi : i < H)
      (hz : z ∈ G.scheme.toCellScheme.below (G.scheme.toCellScheme.gradedIndex (r a i))) :
      G.scheme.toCellScheme.grade z = 1 := by
    have h1 : G.scheme.toCellScheme.grade z ≤ 1 := by
      have := hz.2
      rw [hr a i hi] at this
      exact this
    have h2 := G.isLegal.isWellFormed.isWellFormed.grade_pos z
    omega
  have hrungs : ∀ i < H, v (r a i) ≠ ⊥ := by
    intro i hi h0
    have key : ∀ k, i + k < H → v (r a (i + k)) = ⊥ := by
      intro k
      induction k with
      | zero => intro _; simpa using h0
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        set c' := r a (i + (k + 1))
        have hmem (z : Fin G.scheme.card) (hz : G.scheme.toCellScheme.grade z ≤ 1)
            (hzs : G.scheme.toCellScheme.scope z ⊆ univ) :
            z ∈ G.scheme.toCellScheme.below (G.scheme.toCellScheme.gradedIndex c') := by
          rw [CellScheme.mem_below, hr a _ hk, CellScheme.gradedIndex_le_iff]
          exact ⟨hzs, hz⟩
        have hloc := hv.locality c'
        have hloc' : TransformsTo (fun _ : G.scheme.toCellScheme.below
            (G.scheme.toCellScheme.gradedIndex c') ↦ 1) (G.scheme.rows.row c')
            (fun z ↦ min (v z) (v c')) := by
          convert hloc using 2 with z
          exact (hall1 z.1 _ hk z.2).symm
        have hcm := hmem c' (hrg _ hk).le (subset_univ _)
        have hdm := hmem (r a (i + k)) (hrg _ (by omega)).le (subset_univ _)
        have := eq_bot_of_ladder_predecessor
          (D := G.scheme.toCellScheme.below (G.scheme.toCellScheme.gradedIndex c'))
          (t := i + (k + 1) + 1) (by omega) hloc'
          (c := ⟨c', hcm⟩) (d := ⟨r a (i + k), hdm⟩)
          (by rw [← Scheme.rowAt_of_mem hcm]; exact hrd a _ hk)
          (by
            rw [← Scheme.rowAt_of_mem hdm]
            have h2 := hrp a _ hk (by omega)
            rw [show i + (k + 1) - 1 = i + k by omega] at h2
            rw [h2]
            congr 1)
          hprev
        exact this
    apply htop0
    have := key (H - 1 - i) (by omega)
    rwa [show i + (H - 1 - i) = H - 1 by omega] at this
  -- the chart is positive at the table
  have hσF (i : ℕ) (hi : i < H) : σ (F (i + 1)) ≠ ⊥ := by
    intro h0
    have h := hq' (r a i) ((hrg i hi).trans_le hthr)
    rw [hrung i hi, h0, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h with h' | h'
    · exact hrungs i hi h'
    · exact hvu0 h'
  -- the recognized state and map
  have hscvis : IsSelfVisible Q.threshold sc :=
    hcN ▸ Scheme.isSelfVisible_rowAt hcons (hub c hcN.le)
  refine ⟨fun x ↦ G.scheme.rowAt u (G.contextCell x), fun j ↦ G.scheme.rowAt u (G.donorCell j),
    fun y ↦ min (σ (min y sc)) (g Q.threshold), v c, hadm,
    fun x y hxy ↦ min_le_min_right _ (hwit.monotone (min_le_min_right _ hxy)),
    by simp [hwit.map_bot], fun i hi y ↦ ?_, hcN ▸ hv.orderly c, le_rfl, fun x hx h0 ↦ ?_,
    fun x hx ↦ (hread _ ((hgc x).trans_le hx.2)).symm, fun j ↦ (hread _ (hdon j)).symm⟩
  · beta_reduce
    rw [← visibilityReplace_min_of_isSelfVisible hi hscvis, hwit.min_visibilityReplace hi]
  · -- reflection of `⊥` on the stored context values below the cap
    by_contra hx0
    have hsc0 : sc ≠ ⊥ := by
      intro h1
      apply hc0
      have h := hread c hcN.le
      rw [min_self] at h
      rw [h, h1, min_bot_right, hwit.map_bot, min_eq_left bot_le]
    have hcb : Q.cap ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex Q.cap) :=
      CellScheme.mem_below_gradedIndex _ _
    obtain ⟨i, hi, hiF⟩ : ∃ i < H, min (G.scheme.rowAt u (G.contextCell x)) sc = F (i + 1) := by
      rcases min_choice (G.scheme.rowAt u (G.contextCell x)) sc with h | h <;> rw [h]
      · exact hval x hx hx0
      · exact hval Q.cap hcb hsc0
    beta_reduce at h0
    rw [hiF] at h0
    rcases min_eq_bot.mp h0 with h | h
    · exact hσF i hi h
    · exact hg0 h

end GrowthCarrier

end VaughtConjecture

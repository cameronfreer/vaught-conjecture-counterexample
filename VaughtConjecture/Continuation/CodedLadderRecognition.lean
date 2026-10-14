/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthLadderRecognition
import VaughtConjecture.Extension.CodedLadderSource

/-!
# The coded rung contract and recognition from the coded ladder

Roadmap, Layer 3 ((R3) and (R4), the recognition of admitted states in a growth carrier) and
Correspondence, item 1 (the strongly coded legal stage types).  All results here are native
constructions of this repository.

The rung clauses of the ladder contract ask the diagonal of the rung `i` to be
`Label.ladderSource (i + 1) (i + 1)`, of finite part `3` for `i ≥ 1`, which no strongly coded
scheme has at grade one (`Scheme.not_isStronglyCoded_of_secondRung`).  The **coded rung contract**
states the same clauses with the coded ladder source (`Label.codedLadderSource`, finite parts `1`
and `2`):

* `Scheme.CodedLadderRungs`: rungs `r a i` (`i < H`, `H ≥ 1`) of graded index `(univ, 1)`, the
  rung `i` reading itself at `codedLadderSource (i + 1) (i + 1)` and the rung `i - 1` at
  `codedLadderSource (i + 1) i`.
* `GrowthCarrier.CodedLadder`: a growth carrier with a cell of full scope at the threshold, coded
  rungs, every cell of full scope at the threshold a ladder controller
  (`GrowthCarrier.IsLadderController`, which does not mention the codes), and strongly coded rows.
* `GrowthCarrier.CodedLadder.isStronglyCoded_context`,
  `GrowthCarrier.CodedLadder.isStronglyCoded_donor`: a coded ladder carrier has a strongly
  coded context and donor (its literal faces), so a contract asking for one must assume both
  strongly coded.

The old equations are not kept: the coded clauses replace them.  **Recognition from the coded
ladder** (`GrowthCarrier.recognizes_of_codedLadder`) is the proof of
`GrowthCarrier.recognizes_of_ladder` with the predecessor step of the coded ladder
(`Label.eq_bot_of_codedLadder_predecessor`, through the shared block of the diagonal at the
threshold `2`); strong coding is not used by it.

## References

The controllers and the growth step are those of [Kni26, §4]; strong coding is the range of
[Kni26, Lemma 2.5.13].

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ}

/-- **Coded rungs** (native construction): the rung clauses of the ladder contract with the coded
ladder source.  For a family of members `Mb` and a height `H`, the cells `r a i` (`i < H`) are the
rungs of the member `a`. -/
structure CodedLadderRungs (S : Scheme.{u} n) {Mb : Type*} (H : ℕ) (r : Mb → ℕ → Fin S.card) :
    Prop where
  /-- The ladder has at least one rung per member; the top rung is `r a (H - 1)`. -/
  height_pos : 0 < H
  /-- Every rung is a cell of full scope and grade one: it reads every cell of grade one. -/
  gradedIndex_rung : ∀ a, ∀ i < H, S.toCellScheme.gradedIndex (r a i) = (univ, 1)
  /-- The diagonal of the rung `i` is the coded ladder source at its ceiling `i + 1`; for `i ≥ 1`
  it is `ω · i + 2`, strongly coded at grade one. -/
  rowAt_diag : ∀ a, ∀ i < H, S.rowAt (r a i) (r a i) = codedLadderSource (i + 1) (i + 1)
  /-- The rung `i ≥ 1` reads the rung `i - 1` at `ω · i + 1`, in the block of its diagonal: the
  predecessor step of the reflection of the bottom label
  (`Label.eq_bot_of_codedLadder_predecessor`). -/
  rowAt_pred : ∀ a, ∀ i < H, 0 < i →
    S.rowAt (r a i) (r a (i - 1)) = codedLadderSource (i + 1) i

end Scheme

namespace GrowthCarrier

variable {α : Ordinal.{u}} {J n : ℕ} {t' : StageType.{u} α J} {D : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J} (G : GrowthCarrier t'.toScheme D e) (Q : StageType.GrowthRequests t' D)

/-- **A coded ladder carrier** (native construction): the coded rung contract for the growth
carrier `G` and the requests `Q`, with the members `Mb`, the height `H` and the rungs `r`. -/
structure CodedLadder {Mb : Type*} (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card) : Prop where
  /-- A cell of full scope at the threshold: availability finds a controller above the cap. -/
  fullCell : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)
  /-- The coded rungs: they reflect the bottom label along each member. -/
  rungs : G.scheme.CodedLadderRungs H r
  /-- Every cell of full scope at the threshold is a ladder controller: it stores an admitted
  state and reads the rungs of its member as a table. -/
  controller : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
    ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F
  /-- The rows of the carrier are strongly coded: the target of the strongly coded recovery. -/
  stronglyCoded : G.scheme.rows.IsStronglyCoded

/-- **A strongly coded carrier has a strongly coded context** (native construction): the context
type is the restriction of the carrier scheme to the context face (`GrowthCarrier.comap_context`),
and strong coding passes to restrictions.  So a coded ladder carrier exists only over a strongly
coded context. -/
theorem CodedLadder.isStronglyCoded_context {Mb : Type*} {H : ℕ} {r : Mb → ℕ → Fin G.scheme.card}
    (hL : G.CodedLadder Q H r) : t'.rows.IsStronglyCoded := by
  have h : (G.scheme.comap Fin.castSuccEmb).rows.IsStronglyCoded :=
    hL.stronglyCoded.comap (G.scheme.isLowerEmbedding_comap _)
  rw [G.comap_context] at h
  exact h

/-- **A strongly coded carrier has a strongly coded donor** (native construction): the donor is
the restriction of the carrier scheme to the donor face (`GrowthCarrier.comap_donor`).  So a coded
ladder carrier exists only over a strongly coded donor. -/
theorem CodedLadder.isStronglyCoded_donor {Mb : Type*} {H : ℕ} {r : Mb → ℕ → Fin G.scheme.card}
    (hL : G.CodedLadder Q H r) : D.rows.IsStronglyCoded := by
  have h : (G.scheme.comap (extendByLast e)).rows.IsStronglyCoded :=
    hL.stronglyCoded.comap (G.scheme.isLowerEmbedding_comap _)
  rw [G.comap_donor] at h
  exact h

/-- **Recognition from the coded ladder** (native construction): a coded ladder carrier, at a
threshold `≥ 1` and with donor cells of grade at most the threshold, recognizes admitted states.
Strong coding is not used. -/
theorem recognizes_of_codedLadder (hthr : 1 ≤ Q.threshold)
    (hdon : ∀ j, G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold)
    {Mb : Type*} {H : ℕ} {r : Mb → ℕ → Fin G.scheme.card} (hL : G.CodedLadder Q H r) :
    G.Recognizes Q := by
  have hfull := hL.fullCell
  have hH := hL.rungs.height_pos
  have hr := hL.rungs.gradedIndex_rung
  have hrd := hL.rungs.rowAt_diag
  have hrp := hL.rungs.rowAt_pred
  have hctrl := hL.controller
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
    rw [hrg _ (by omega)] at h
    have h1 : v c ≤ min (v (r a (H - 1))) (v u) := by
      rw [h, hvc]
      exact min_le_min (hwit.monotone htop) hgN
    intro h0
    rw [h0, min_eq_left bot_le, le_bot_iff] at h1
    exact hc0 h1
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
        have := eq_bot_of_codedLadder_predecessor
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

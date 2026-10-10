/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayLayer
import VaughtConjecture.Continuation.LowStateStepAbove

/-!
# The LOW step for states over the proper donor fields of every grade

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the layers of states
above the controllers); semantic contract, items 3, 4 and 8.

The LOW clause of the state catalogues (`ProfileTower.lowPred`) takes its donor maximum over a set
of proper donor fields.  Over the proper donor fields of grade at most `K` (`ProfileTower.lowN`)
the step for states above `K` meets the rigid and the held readings of
`VaughtConjecture.Continuation.LowStateContract`.  This file takes the donor maximum over the
proper donor fields of **every** grade (`ProfileTower.lowNAll`), as the display itself does
(`StageType.properDonorFields`).

**The orbit code keeps the clause** (`ProfileTower.lowPred_orbitCode`, compiled in this
repository): the orbit map over all fields is a witness with suppressor `⊤` at `K`, whatever the
fields of the donor maximum.  The state code of the state tower (`ProfileTower.scode`) splices
the fields above its grade to `⊥` first, and that splice does not keep the clause
(`ProfileTower.not_lowPred_scode_of_high`); a tower whose code is the orbit code of the state
itself keeps it.

**The root above the donor maximum is excluded** (`ProfileTower.not_donorMax_lt_of_subset_coatD`,
compiled in this repository; not used by the step).  Both the rigid and the held configurations
ask a copy `u` of a cell below both coatoms, of the grade of the layer, read above the donor
maximum of the serving state.  Over every grade such a cell above the top grade of the donor is a
proper donor field (`ProfileTower.mem_lowNAll_of_subset_coatD`); capped agreement with a state
active below the cap reads it at the value of the state, at most the donor maximum.

**The step from the repair at `K`** (`ProfileTower.LowStateRepair.of_subset`,
`ProfileTower.lowStateRaise_of_repair`, compiled in this repository).  A repair of the failure mode
at `K` for a smaller set of proper donor fields is one for a larger set: the serving state is
active over the larger set, so its donor tops are at least its cutoff and its frontier, and its
cutoff lowered to the cap makes it LOW over the smaller set.  The failure mode at a grade `j ≥ K`
is then repaired by the repair at `K` on the profile cut at `K`, lifted on the other coatom from
`K` to `j` at the cap (bountifulness of the amalgam), the cells below both coatoms of grade in
`(K, j]` being proper donor fields below the cap and so fixed by the cap.  Every cell of grade at
most `K` carries the repair at `K`: the frontier and the donor tops are those of the repair.

**The step for the seed at every grade from `K` on** (`ProfileTower.stateCatStep_lowAll_seed`,
compiled in this repository): for the LOW designations of a seed whose private context is a
source-gap context of grade `K = g + 1 ≤ m` with the lost point last and whose donor has top grade
at most `K`, the step for states (`ProfileTower.StateCatStep`) holds at every grade
`j ∈ [K, m]` from both coatoms, for the clause over the proper donor fields of every grade, with
no hypothesis: the repairs at `K` are `ProfileTower.lowStateRaise_private` and
`ProfileTower.lowStateRaise_donor`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The orbit code keeps the clause -/

/-- **The orbit code over all fields keeps the LOW clause** at every grade `j ≥ K`, for every set
of proper donor fields. -/
theorem lowPred_orbitCode {K j : ℕ} (hj : K ≤ j) {N : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {P : CProf I}
    (h : lowPred K N T o r P) : lowPred K N T o r (orbitCode j P) :=
  h.map (isWitness_orbitMap j P) (stepSuppressor_of_le hj)

/-! ### The root above the donor maximum is excluded -/

/-- **A proper donor field below the cap is read at the state**: for a state `P` with donor
maximum below the cap `h`, every labelling agreeing with `P` capped at `h` at a proper donor field
`u` reads it at most at the donor maximum.  Not used by the step for states; the form of the
exclusion is `ProfileTower.not_donorMax_lt_of_subset_coatD`. -/
theorem not_donorMax_lt_of_mem {N : Finset (Fin I.amalgam.card ⊕ Unit)} {P : CProf I}
    {h : Label.{u}} (hMh : donorMax N P < h) {a : Prof I} {u : Fin I.amalgam.card}
    (hu : Sum.inl u ∈ N) (hau : min (a u) h = min (P (Sum.inl u)) h) :
    ¬ donorMax N P < a u := by
  have hPu : P (Sum.inl u) ≤ donorMax N P := le_donorMax hu
  have hau' : a u = P (Sum.inl u) := eq_of_min_eq_of_lt hau.symm (hPu.trans_lt hMh)
  rw [hau']
  exact not_lt.mpr hPu

/-- **A cell on the donor coatom above the top grade of the donor is a proper donor field of the
seed.** -/
theorem mem_lowNAll_of_subset_coatD {K : ℕ} (htb : I.right.topGrade ≤ K) {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.scope d ⊆ coatD) (hK : K < I.amalgam.toCellScheme.grade d) :
    Sum.inl d ∈ lowNAll I := by
  classical
  obtain ⟨t, rfl⟩ := StageType.exists_faceCell_eq I.restrictFace_right
    (Scheme.mem_visibleCells.mpr fun z hz ↦ by
      obtain ⟨a, -, ha⟩ := mem_map.mp (Coatom.univ_map_right.ge (hd hz))
      exact ⟨a, ha⟩)
  refine mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, fun ht ↦ ?_⟩, rfl⟩
  have := StageType.topGrade_le_iff.mp htb t ht
  rw [StageType.grade_faceCell] at hK
  omega

/-- **The rigid and held configurations are excluded over every grade**: for a state `P` with
donor maximum over the proper donor fields of every grade below the cap `h`, no labelling agreeing
with `P` capped at `h` reads a cell on the donor coatom above the top grade of the donor (in
particular a cell below both coatoms at a grade above `K`) above that donor maximum.  This is the
hypothesis `donorMax Nf P < a u` of `ProfileTower.SLvl.Good.not_cappedLift_sS_of_rigid` and
`ProfileTower.SLvl.Good.not_cappedLift_sS_of_held` over every grade; it is not used by the step
for states, which needs only `ProfileTower.mem_lowNAll_of_subset_coatD`. -/
theorem not_donorMax_lt_of_subset_coatD {K : ℕ} (htb : I.right.topGrade ≤ K) {P : CProf I}
    {h : Label.{u}} (hMh : donorMax (lowNAll I) P < h) {a : Prof I} {u : Fin I.amalgam.card}
    (hu : I.amalgam.toCellScheme.scope u ⊆ coatD) (hK : K < I.amalgam.toCellScheme.grade u)
    (hau : min (a u) h = min (P (Sum.inl u)) h) : ¬ donorMax (lowNAll I) P < a u :=
  not_donorMax_lt_of_mem hMh (mem_lowNAll_of_subset_coatD htb hu hK) hau

/-! ### The repair over a larger set of proper donor fields -/

variable {K j : ℕ} {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}

/-- **A repair at `(K, j)` over a set of proper donor fields is one over every larger set**, the
donor tops and the fields amalgam cells: the serving state, active over the larger set, has its
donor tops at least its cutoff and its frontier; with its cutoff lowered to the cap it is LOW over
the smaller set. -/
theorem LowStateRepair.of_subset {N N' : Finset (Fin I.amalgam.card ⊕ Unit)} {x : Fin (m + 2)}
    (hNN : N ⊆ N') (hN' : Sum.inr () ∉ N') (hT : ∀ y ∈ T, ∃ d, y = Sum.inl d)
    (h : LowStateRepair I K j N T o r x) : LowStateRepair I K j N' T o r x := by
  intro P hPC hPlow c hc hb W₀ hW₀ hW₀P hact hfh
  set P' : CProf I := withCut (camal P) (min (P (Sum.inr ())) c) with hP'
  have hag : ∀ f ∈ N', min (withCut W₀ ⊥ f) c = min (P f) c := by
    rintro (d | z) hf
    · exact hW₀P d
    · cases z; exact absurd hf hN'
  have hMh : donorMax N' (withCut W₀ ⊥) < c := hact.trans_le (min_le_right _ _)
  have hPact : donorMax N' P < P (Sum.inr ()) := by
    rw [← donorMax_eq_of_min_eq hag hMh]
    exact hact.trans_le (min_le_left _ _)
  have hP'low : lowPred K N T o r P' := by
    intro _ y hy
    obtain ⟨d, rfl⟩ := hT y hy
    exact le_trans (max_le_max (min_le_left _ _) le_rfl) (hPlow hPact (Sum.inl d) hy)
  have hle : donorMax N (withCut W₀ ⊥) ≤ donorMax N' (withCut W₀ ⊥) := Finset.sup_mono hNN
  have hact' : donorMax N (withCut W₀ ⊥) < min (P' (Sum.inr ())) c := by
    -- the cutoff of the lowered state is `min (P cutoff) c`
    change _ < min (min (P (Sum.inr ())) c) c
    rw [min_assoc, min_self]
    exact hle.trans_lt hact
  exact h P' hPC hP'low c hc hb W₀ hW₀ hW₀P hact' hfh

/-! ### The repair at a grade `j ≥ K` from the repair at `K` -/

/-- **The failure mode at a grade `j ≥ K` from the repair at `K`.**  Let the owner, the lost top
and the donor tops be amalgam cells of grade at most `K`, and every cell below both coatoms of
grade in `(K, j]` a proper donor field.  The repair at `K` from the coatom `univ.erase x`
(`ProfileTower.LowStateRepair` at `(K, K)`) repairs the failure mode at `j`
(`ProfileTower.LowStateRaise`): the repair `WK` of the profile cut at `K`, the profile `W₀` below
the coatom `univ.erase x`, and on the other coatom the lift of `WK` from `K` to `j` in the cap ball
of `W₀` at the cap (bountifulness of the amalgam).  Below both coatoms the lift is `W₀`: at the
grades at most `K` the repair is literal on the coatom, above `K` the cells are proper donor fields
of `W₀`, below the cap, which the cap keeps.  At every cell of grade at most `K` the result is
`WK`, so its frontier and its donor tops are those of the repair. -/
theorem lowStateRaise_of_repair {N : Finset (Fin I.amalgam.card ⊕ Unit)} (hK0 : 0 < K)
    (hKj : K ≤ j) (hjm : j ≤ m) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hoK : I.amalgam.toCellScheme.grade o ≤ K) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hTK : ∀ y ∈ T, ∃ d, y = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K)
    (hshield : ∀ d, I.amalgam.toCellScheme.scope d ⊆ coatC →
      I.amalgam.toCellScheme.scope d ⊆ coatD → K < I.amalgam.toCellScheme.grade d →
        Sum.inl d ∈ N)
    (hrep : LowStateRepair I K K N T o r x) : LowStateRaise I K j N T o r x := by
  classical
  intro P _ hPC hPlow h hh _ hb W₀ hW₀ hW₀P hact hfh
  obtain ⟨WK, hWK, hWKW₀, hWKP, hWKfr⟩ := hrep P (hPC.mono' hKj) hPlow h (hh.mono hKj) hb W₀
    (hW₀.mono' hKj) hW₀P hact hfh
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  have hXY : ((univ.erase y, K) : Finset (Fin (m + 2)) × ℕ) ≤ (univ.erase y, j) :=
    ⟨subset_rfl, hKj⟩
  have hlift : I.amalgam.rows.CappedLift hXY := I.isBountiful
    ⟨I.erase_mem_faces hy, hK0, show K ≤ #(univ.erase y) by rw [hcard]; omega⟩
    ⟨I.erase_mem_faces hy, hK0.trans_le hKj, show j ≤ #(univ.erase y) by rw [hcard]; omega⟩ hXY
  obtain ⟨q', hq', hq'W₀, hq'WK⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp hlift h hh
    (fun d ↦ WK d) (fun d ↦ W₀ d) (hWK.isLawfulBelow_erase hy) (hW₀.isLawfulBelow_erase hy)
    fun d ↦ (hW₀P d.1).trans (hWKP d.1).symm
  -- the donor maximum of `W₀` lies below the cap
  have hMh : donorMax N (withCut W₀ ⊥) < h := hact.trans_le (min_le_right _ _)
  -- below both coatoms the lift is `W₀`
  have hboth (d : Fin I.amalgam.card) (hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
      (hdy : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j)) : q' ⟨d, hdy⟩ = W₀ d := by
    by_cases hdK : I.amalgam.toCellScheme.grade d ≤ K
    · have h1 := hq'WK ⟨d, ⟨hdy.1, hdK⟩⟩
      -- the lift at the inclusion of a cell below `(univ.erase y, K)` is the lift at that cell
      change q' ⟨d, hdy⟩ = WK d at h1
      rw [h1]
      exact hWKW₀ d ⟨hdx.1, hdK⟩
    · have hsub : I.amalgam.toCellScheme.scope d ⊆ coatC ∧
          I.amalgam.toCellScheme.scope d ⊆ coatD := by
        rcases Seed.pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [⟨hdx.1, hdy.1⟩, ⟨hdy.1, hdx.1⟩]
      have hdN := hshield d hsub.1 hsub.2 (not_le.mp hdK)
      have hW₀d : W₀ d < h :=
        (le_donorMax (a := withCut W₀ ⊥) hdN).trans_lt hMh
      exact eq_of_min_eq_of_lt (hq'W₀ ⟨d, hdy⟩).symm hW₀d
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase x, j) then W₀ d
    else if hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j) then q' ⟨d, hd⟩
    else W₀ d with hW
  have hWx (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)) :
      W d = W₀ d := ite_eq_left hd
  have hWy (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j)) :
      W d = q' ⟨d, hd⟩ := by
    by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)
    · rw [hWx d hdx]; exact (hboth d hdx hd).symm
    · exact (ite_eq_right hdx).trans (dite_eq_left hd)
  have hWo (d : Fin I.amalgam.card) (hdx : d ∉ I.amalgam.toCellScheme.below (univ.erase x, j))
      (hdy : d ∉ I.amalgam.toCellScheme.below (univ.erase y, j)) : W d = W₀ d :=
    (ite_eq_right hdx).trans (dite_eq_right hdy)
  -- `W` is the repair at the cells of grade at most `K`
  have hWK' (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ K) : W d = WK d := by
    rcases I.scope_subset_or hx hy hxy d with hsx | hsy
    · rw [hWx d ⟨hsx, hd.trans hKj⟩]
      exact (hWKW₀ d ⟨hsx, hd⟩).symm
    · rw [hWy d ⟨hsy, hd.trans hKj⟩]
      exact hq'WK ⟨d, ⟨hsy, hd⟩⟩
  have hWlx : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hWx d hd).symm).mp (hW₀.isLawfulBelow_erase hx)
  have hWly : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) fun d ↦ W d := by
    convert hq' using 1
    funext d
    exact hWy d.1 d.2
  refine ⟨W, lawful_pair hx hy hxy hWlx hWly, hWx, fun d ↦ ?_, fun z hz ↦ ?_⟩
  · by_cases hdx : d ∈ I.amalgam.toCellScheme.below (univ.erase x, j)
    · rw [hWx d hdx]; exact hW₀P d
    · by_cases hdy : d ∈ I.amalgam.toCellScheme.below (univ.erase y, j)
      · rw [hWy d hdy, hq'W₀ ⟨d, hdy⟩]; exact hW₀P d
      · rw [hWo d hdx hdy]; exact hW₀P d
  · obtain ⟨e, rfl, he⟩ := hTK z hz
    have hfr : frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) =
        frontier K (Sum.inl o) (Sum.inl r) (withCut WK ⊥) := by
      unfold Label.frontier
      -- the frontier reads the owner and the lost top
      change min (W o) (visibilityReplace K K (W r)) = min (WK o) (visibilityReplace K K (WK r))
      rw [hWK' o hoK, hWK' r hrK]
    rw [hfr]
    -- the donor top of the state of `W` is the label of `W` at its cell
    change _ ≤ W e
    rw [hWK' e he]
    exact hWKfr _ hz

/-! ### The step for the seed over every grade -/

variable {g : ℕ}

/-- **The step for states at every grade `j ∈ [K, m]` for the LOW designations of a seed, over
the proper donor fields of every grade**, when the private context is a source-gap context of
grade `K = g + 1 ≤ m` with the lost point last and the donor has top grade at most `K`: from both
coatoms, with no hypothesis (`ProfileTower.stateCatStep_low_of_raise`,
`ProfileTower.lowStateRaise_of_repair`, `ProfileTower.LowStateRepair.of_subset`,
`ProfileTower.lowStateRepair_seed`). -/
theorem stateCatStep_lowAll_seed {j : ℕ} (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) (hKj : g + 1 ≤ j) (hjm : j ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    StateCatStep I j (lowPred (g + 1) (lowNAll I) (lowT I)
      (StageType.faceCell I.restrictFace_left o') (StageType.faceCell I.restrictFace_left r'))
      x := by
  have hTQ : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ g + 1 := by
    rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, by
      rw [StageType.grade_faceCell]; exact StageType.topGrade_le_iff.mp htb t ht⟩
  have hT : Sum.inr () ∉ lowT I := fun hf ↦ by obtain ⟨d, hd, -⟩ := hTQ _ hf; cases hd
  have hoK : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left o') ≤ g + 1 := by
    rw [StageType.grade_faceCell]; exact hs.grade_owner.le
  have hrK : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left r') ≤ g + 1 := by
    rw [StageType.grade_faceCell]
    exact hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost
  refine stateCatStep_low_of_raise (by omega) hjm hKj inr_notMem_lowNAll hT hx
    (lowStateRaise_of_repair (Nat.succ_pos g) hKj hjm hx hoK hrK hTQ
      (fun d _ hdD hdK ↦ mem_lowNAll_of_subset_coatD htb hdD hdK)
      ((lowStateRepair_seed hgm hs htb hx).of_subset (lowN_subset_lowNAll _) inr_notMem_lowNAll
        fun y hy ↦ by obtain ⟨d, rfl, -⟩ := hTQ y hy; exact ⟨d, rfl⟩))

end VaughtConjecture.ProfileTower

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStepBase

/-!
# The LOW step for states above the controllers, below the cap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the layers of states
above the controllers); semantic contract, items 3, 4 and 8.

The LOW clause reads only fields of grade at most `K` (the owner, the lost top, the proper donor
fields, the donor tops).  At a grade `j > K` the failure mode of the LOW step for states
(`ProfileTower.LowStateRaise`) is repaired at the grade `K` and kept above `K`, provided the
cells of grade in `(K, j]` carry labels at most the cap.

**Splicing above a grade, below the cap** (`CellScheme.Rows.isLawfulBelow_splice_of_le_cap`,
compiled in this repository).  Let `V` be lawful below `(B, j)` and `h` a label with `V`
at most `h` at every cell below `(B, j)` of grade in `(K, j]`.  A labelling `U` lawful below
`(B, K)`, equal to `V` where `V` is below `h` and at least `h` where `V` is at least `h`, spliced
with `V` above `K`, is lawful below `(B, j)`.  At a cell `s` of grade in `(K, j]` the locality is
that of `V`: `V s ≤ h`, and capping at `V s` erases every change (a changed cell carries labels at
least `h` in both).  The order and availability laws hold grade by grade.  (The strict form at the
faces is `H2.lawfulAt_raise_below`; here the gap may be attained, `V s ≤ h`.)

**The repair above the controllers below the cap** (`ProfileTower.lowStateRepair_of_le_cap`,
compiled in this repository).  At a grade `j ≥ K`, with the designated fields of grade at most `K`:
given the repair at `K` (`ProfileTower.LowStateRepair` at `(K, K)`, compiled for the LOW
designations of a seed in `VaughtConjecture.Continuation.LowStateStepBase`), every instance of the
failure mode at `j` whose profile `W₀` is at most the cap at every cell of grade in `(K, j]` is
repaired: the repair of the truncation at `K`, spliced with `W₀` above `K`.  It agrees with the
state capped at the cap (the repair does at grades at most `K`, `W₀` above), equals `W₀` below the
coatom, and its frontier and donor tops are those of the repair.

**Not claimed.**  The failure mode at `j > K` when `W₀` has a cell of grade in `(K, j]` above the
cap is open: a cell of grade in `(K, j]` read above the cap may read a donor top below its own
label, so the tops cannot be raised without moving it, and the frontier is self-visible at `K`,
not at `j`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}

/-- **Splicing above a grade, below the cap.**  For `V` lawful below `(B, j)` and at
most `h` at every cell below `(B, j)` of grade in `(K, j]`, and `U` lawful below `(B, K)`, equal to
`V` at every cell below `(B, K)` that `V` reads below `h`, and at least `h` at every cell below
`(B, K)` that `V` reads at least at `h`: the labelling equal to `U` at the cells of grade at most
`K` and to `V` at the others is lawful below `(B, j)`.  Locality at a cell `s` of grade in
`(K, j]`: `V s ≤ h`, and at a cell `d` below `s` with `V d ≥ h` both `U d` and `V d` are at least
`h ≥ V s`, so both minima are `V s`. -/
theorem isLawfulBelow_splice_of_le_cap {B : Finset β} {K j : ℕ} {h : Label.{u}}
    {U V : ι → Label.{u}} (hU : R.IsLawfulBelow (B, K) fun d ↦ U d)
    (hV : R.IsLawfulBelow (B, j) fun d ↦ V d)
    (hmid : ∀ d ∈ D.below (B, j), K < D.grade d → V d ≤ h)
    (hlo : ∀ d ∈ D.below (B, K), V d < h → U d = V d)
    (hhi : ∀ d ∈ D.below (B, K), h ≤ V d → h ≤ U d) :
    R.IsLawfulBelow (B, j) fun d ↦ if D.grade d ≤ K then U d else V d := by
  classical
  obtain ⟨hUo, hUl, hUa⟩ := isLawfulBelow_iff_forall.mp hU
  obtain ⟨hVo, hVl, hVa⟩ := isLawfulBelow_iff_forall.mp hV
  have hmemK {d : ι} (hd : d ∈ D.below (B, j)) (hdK : D.grade d ≤ K) : d ∈ D.below (B, K) :=
    ⟨hd.1, hdK⟩
  refine (isLawfulBelow_iff_forall (w := fun d ↦ if D.grade d ≤ K then U d else V d)).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s u hu hsu hg ↦ ?_⟩
  · split_ifs with hdK
    · exact hUo d (hmemK hd hdK)
    · exact hVo d hd
  · by_cases hsK : D.grade s ≤ K
    · have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if D.grade d.1 ≤ K then U d.1 else V d.1) (if D.grade s ≤ K then U s else V s)) =
          fun d ↦ min (U d.1) (U s) := by
        funext d
        have hdK : D.grade d.1 ≤ K := d.2.2.trans hsK
        rw [ite_eq_left hdK, ite_eq_left hsK]
      rw [he]
      exact hUl s (hmemK hs hsK)
    · have hVs : V s ≤ h := hmid s hs (not_le.mp hsK)
      have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if D.grade d.1 ≤ K then U d.1 else V d.1) (if D.grade s ≤ K then U s else V s)) =
          fun d ↦ min (V d.1) (V s) := by
        funext d
        rw [ite_eq_right hsK]
        split_ifs with hdK
        · have hdB : d.1 ∈ D.below (B, K) := hmemK (mem_below_of_le d.2 hs) hdK
          rcases lt_or_ge (V d.1) h with hd | hd
          · rw [hlo d.1 hdB hd]
          · rw [min_eq_right (hVs.trans (hhi d.1 hdB hd)), min_eq_right (hVs.trans hd)]
        · rfl
      rw [he]
      exact hVl s hs
  · have hgv (v : ι) (hv : D.gradedIndex v = D.gradedIndex u) : D.grade v = D.grade u :=
      congrArg Prod.snd hv
    by_cases huK : D.grade u ≤ K
    · obtain ⟨v, hv, hle⟩ := hUa s u (hmemK hu huK) hsu hg
      refine ⟨v, hv, ?_⟩
      rw [ite_eq_left (hg ▸ huK), ite_eq_left ((hgv v hv).trans_le huK)]
      exact hle
    · obtain ⟨v, hv, hle⟩ := hVa s u hu hsu hg
      refine ⟨v, hv, ?_⟩
      rw [ite_eq_right (hg ▸ huK), ite_eq_right (by rw [hgv v hv]; exact huK)]
      exact hle

end VaughtConjecture.CellScheme.Rows

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- A profile lawful on the grade-`j` cut is lawful on the grade-`K` cut, `K ≤ j`. -/
theorem IsCutLawful.mono' {K j : ℕ} (hKj : K ≤ j) {W : Prof I} (hW : IsCutLawful I j W) :
    IsCutLawful I K W :=
  ⟨hW.1.mono (X := (coatC, K)) ⟨subset_rfl, hKj⟩, hW.2.mono (X := (coatD, K)) ⟨subset_rfl, hKj⟩⟩

variable {K j : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The repair above the controllers, below the cap.**  For `K ≤ j`, the owner, the lost top
and the donor tops amalgam cells of grade at most `K`, and the repair at `K` from the coatom
`univ.erase x` (`ProfileTower.LowStateRepair` at `(K, K)`): every instance of the failure mode at
`j` (a state `P` lawful on the grade-`j` cut and LOW, a cap `h` self-visible at `K`, a profile `W₀`
lawful on the grade-`j` cut agreeing with `P` capped at `h`, active below the cap, with frontier
above the cap) whose profile `W₀` is at most `h` at every cell of grade in `(K, j]` is repaired at
`j`: the repair of the truncation at `K`, spliced with `W₀` above `K`
(`CellScheme.Rows.isLawfulBelow_splice_of_le_cap` on both coatoms). -/
theorem lowStateRepair_of_le_cap (hKj : K ≤ j) {x : Fin (m + 2)}
    (hoK : I.amalgam.toCellScheme.grade o ≤ K) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hTK : ∀ y ∈ T, ∃ d, y = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K)
    (hrep : LowStateRepair I K K N T o r x) {P : CProf I} (hPC : IsCutLawful I j (camal P))
    (hPlow : lowPred K N T o r P) {h : Label.{u}} (hh : IsSelfVisible K h) (hb : ⊥ < h)
    {W₀ : Prof I} (hW₀ : IsCutLawful I j W₀) (hW₀P : ∀ d, min (W₀ d) h = min (P (Sum.inl d)) h)
    (hact : donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h)
    (hfh : h < frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥))
    (hle : ∀ d, K < I.amalgam.toCellScheme.grade d → I.amalgam.toCellScheme.grade d ≤ j →
      W₀ d ≤ h) :
    ∃ W : Prof I, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = W₀ d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
      ∀ y ∈ T, frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y := by
  classical
  obtain ⟨WK, hWK, hWKW₀, hWKP, hWKfr⟩ := hrep P (hPC.mono' hKj) hPlow h hh hb W₀
    (hW₀.mono' hKj) hW₀P hact hfh
  set W : Prof I := fun d ↦ if I.amalgam.toCellScheme.grade d ≤ K then WK d else W₀ d with hW
  have hWle (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ K) : W d = WK d :=
    ite_eq_left hd
  have hWgt (d : Fin I.amalgam.card) (hd : ¬ I.amalgam.toCellScheme.grade d ≤ K) : W d = W₀ d :=
    ite_eq_right hd
  -- `WK` and `W₀` agree capped at `h`
  have hag (d : Fin I.amalgam.card) : min (WK d) h = min (W₀ d) h := (hWKP d).trans (hW₀P d).symm
  have hlo (d : Fin I.amalgam.card) (hd : W₀ d < h) : WK d = W₀ d :=
    eq_of_min_eq_of_lt (hag d).symm hd
  have hhi (d : Fin I.amalgam.card) (hd : h ≤ W₀ d) : h ≤ WK d := by
    have h1 := hag d
    rw [min_eq_right hd] at h1
    exact min_eq_right_iff.mp h1
  have hcut (B : Finset (Fin (m + 2))) (hWKB : I.amalgam.rows.IsLawfulBelow (B, K) fun d ↦ WK d)
      (hW₀B : I.amalgam.rows.IsLawfulBelow (B, j) fun d ↦ W₀ d) :
      I.amalgam.rows.IsLawfulBelow (B, j) fun d ↦ W d :=
    Rows.isLawfulBelow_splice_of_le_cap hWKB hW₀B (fun d hd hKd ↦ hle d hKd hd.2)
      (fun d _ hd ↦ hlo d hd) fun d _ hd ↦ hhi d hd
  refine ⟨W, ⟨hcut _ hWK.1 hW₀.1, hcut _ hWK.2 hW₀.2⟩, fun d hd ↦ ?_, fun d ↦ ?_, ?_⟩
  · by_cases hdK : I.amalgam.toCellScheme.grade d ≤ K
    · rw [hWle d hdK]; exact hWKW₀ d ⟨hd.1, hdK⟩
    · exact hWgt d hdK
  · by_cases hdK : I.amalgam.toCellScheme.grade d ≤ K
    · rw [hWle d hdK]; exact hWKP d
    · rw [hWgt d hdK]; exact hW₀P d
  · intro y hy
    have hfr : frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) =
        frontier K (Sum.inl o) (Sum.inl r) (withCut WK ⊥) := by
      unfold Label.frontier
      change min (W o) (visibilityReplace K K (W r)) = min (WK o) (visibilityReplace K K (WK r))
      rw [hWle o hoK, hWle r hrK]
    obtain ⟨d, rfl, hdK⟩ := hTK y hy
    rw [hfr]
    change _ ≤ W d
    rw [hWle d hdK]
    exact hWKfr _ hy

/-- **The LOW step for states at a grade `j ≥ K`, for the states below the cap above `K`.**  For
`0 < j ≤ m`, `K ≤ j`, the designated fields amalgam cells (`Sum.inr ()` neither a proper donor field
nor a donor top) with the owner, the lost top and the donor tops of grade at most `K`, and the
repair at `K` from the coatom `univ.erase x`: the conclusion of `ProfileTower.StateCatStep` at `j`
holds at every state `P` whose labels at the cells of grade in `(K, j]` are below the cap `h`.
The glued profile `W₀` (`ProfileTower.exists_cutLawful_of_coatom_cap'`) then equals `P` there,
so the failure mode is repaired by `ProfileTower.lowStateRepair_of_le_cap`; the rest is the proof
of `ProfileTower.stateCatStep_low_of_raise`. -/
theorem stateCatStep_low_of_lt_cap (hj0 : 0 < j) (hjm : j ≤ m) (hKj : K ≤ j)
    (hN : Sum.inr () ∉ N) (hT : Sum.inr () ∉ T) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hoK : I.amalgam.toCellScheme.grade o ≤ K) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hTK : ∀ y ∈ T, ∃ d, y = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K)
    (hrep : LowStateRepair I K K N T o r x) (P : CProf I) (hPB : ∀ f, P f ∈ codeGrid j (bound I))
    (hPC : IsCutLawful I j (camal P)) (hPlow : lowPred K N T o r P) (h : Label.{u})
    (hh : IsSelfVisible j h) (hs : IsShort j h) (hb : ⊥ < h)
    (hPh : ∀ d, K < I.amalgam.toCellScheme.grade d → I.amalgam.toCellScheme.grade d ≤ j →
      P (Sum.inl d) < h)
    (a : Prof I) (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun d ↦ a d))
    (haP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
      min (a d) h = min (P (Sum.inl d)) h) :
    ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = a d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid j (bound I) ∧
      min β h = min (P (Sum.inr ())) h ∧ lowPred K N T o r (withCut W β) := by
  obtain ⟨W₀, hW₀, hW₀a, hW₀P⟩ := exists_cutLawful_of_coatom_cap' hj0 hjm hx hPC hh ha haP
  have hhK : IsSelfVisible K h := hh.mono hKj
  obtain ⟨W, hW, hWa, hWP, hfr⟩ : ∃ W : Prof I, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = a d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
      (donorMax N (withCut W ⊥) < min (P (Sum.inr ())) h →
        ∀ y ∈ T, frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y) := by
    by_cases hact : donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h
    swap
    · exact ⟨W₀, hW₀, hW₀a, hW₀P, fun h' ↦ absurd h' hact⟩
    by_cases hfh : frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) ≤ h
    · refine ⟨W₀, hW₀, hW₀a, hW₀P, fun _ y hy ↦ ?_⟩
      have hag : ∀ f ∈ N, min (withCut W₀ ⊥ f) h = min (P f) h := by
        rintro (d | z) hf
        · exact hW₀P d
        · cases z; exact absurd hf hN
      have hMh : donorMax N (withCut W₀ ⊥) < h := hact.trans_le (min_le_right _ _)
      have hPact : donorMax N P < P (Sum.inr ()) := by
        rw [← donorMax_eq_of_min_eq hag hMh]
        exact hact.trans_le (min_le_left _ _)
      have hgap := min_frontier_le_of_isLowAt (f := withCut W₀ ⊥) hPlow hPact hhK (hW₀P o)
        (hW₀P r) y hy
      rw [min_eq_left hfh] at hgap
      rcases y with y | z
      · have h2 : frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) ≤ min (W₀ y) h := by
          rw [hW₀P y]; exact le_min hgap hfh
        exact h2.trans (min_le_left _ _)
      · cases z; exact absurd hy hT
    -- above `K` the glued profile is the state, below the cap
    have hle (d : Fin I.amalgam.card) (hKd : K < I.amalgam.toCellScheme.grade d)
        (hdj : I.amalgam.toCellScheme.grade d ≤ j) : W₀ d ≤ h :=
      (eq_of_min_eq_of_lt (hW₀P d).symm (hPh d hKd hdj)).le.trans (hPh d hKd hdj).le
    obtain ⟨W, hW, hWW₀, hWP, hfr⟩ := lowStateRepair_of_le_cap hKj hoK hrK hTK hrep hPC hPlow
      hhK hb hW₀ hW₀P hact (not_le.mp hfh) hle
    exact ⟨W, hW, fun d hd ↦ (hWW₀ d hd).trans (hW₀a d hd), hWP, fun _ ↦ hfr⟩
  refine ⟨W, min (P (Sum.inr ())) h, hW, hWa, hWP, ?_, by rw [min_assoc, min_self],
    lowPred_withCut_of_frontier hN hT hPlow hWP hfr⟩
  rcases le_total (P (Sum.inr ())) h with hle | hle
  · rw [min_eq_left hle]; exact hPB _
  · rw [min_eq_right hle]; exact mem_codeGrid_of_le hh hs (hPB _) hle

/-- **The LOW step for states at every grade `j ∈ [K, m]` for the LOW designations of a seed, for
the states below the cap above `K`**: `ProfileTower.stateCatStep_low_of_lt_cap` with the repair
at `K = g + 1` from both coatoms (`ProfileTower.lowStateRaise_private`,
`ProfileTower.lowStateRaise_donor`), when the private context is a source-gap context of grade
`g + 1 ≤ m` with the lost point last and the donor has top grade at most `g + 1`. -/
theorem stateCatStep_low_seed_of_lt_cap {g : ℕ} (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) (hKj : g + 1 ≤ j) (hjm : j ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (P : CProf I)
    (hPB : ∀ f, P f ∈ codeGrid j (bound I)) (hPC : IsCutLawful I j (camal P))
    (hPlow : lowPred (g + 1) (lowN I (g + 1)) (lowT I) (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r') P) (h : Label.{u})
    (hh : IsSelfVisible j h) (hsh : IsShort j h) (hb : ⊥ < h)
    (hPh : ∀ d, g + 1 < I.amalgam.toCellScheme.grade d → I.amalgam.toCellScheme.grade d ≤ j →
      P (Sum.inl d) < h)
    (a : Prof I) (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun d ↦ a d))
    (haP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
      min (a d) h = min (P (Sum.inl d)) h) :
    ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, j), W d = a d) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid j (bound I) ∧
      min β h = min (P (Sum.inr ())) h ∧
      lowPred (g + 1) (lowN I (g + 1)) (lowT I) (StageType.faceCell I.restrictFace_left o')
        (StageType.faceCell I.restrictFace_left r') (withCut W β) := by
  classical
  have hNQ : ∀ f ∈ lowN I (g + 1), ∃ d, f = Sum.inl d ∧
      d ∈ I.amalgam.toCellScheme.below (coatD, g + 1) := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, faceCell_right_mem_below (mem_filter.mp ht).2.2⟩
  have hTQ : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d ∧
      d ∈ I.amalgam.toCellScheme.below (coatD, g + 1) := by
    rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, faceCell_right_mem_below (StageType.topGrade_le_iff.mp htb t ht)⟩
  have hNroot : ∀ i, I.left.toCellScheme.grade i ≤ g + 1 →
      Fin.last m ∉ I.left.toCellScheme.scope i → I.left.label i ≠ ⊤ →
        Sum.inl (StageType.faceCell I.restrictFace_left i) ∈ lowN I (g + 1) := by
    intro i hi hl hit
    obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hl
    rw [StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right y]
    refine mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_left y]
      exact hit
    · rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_left y]
      exact hi
  have hN : Sum.inr () ∉ lowN I (g + 1) := fun hf ↦ by obtain ⟨d, hd, -⟩ := hNQ _ hf; cases hd
  have hT : Sum.inr () ∉ lowT I := fun hf ↦ by obtain ⟨d, hd, -⟩ := hTQ _ hf; cases hd
  have hoK : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left o') ≤ g + 1 := by
    rw [StageType.grade_faceCell]; exact hs.grade_owner.le
  have hrK : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left r') ≤ g + 1 := by
    rw [StageType.grade_faceCell]
    exact hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost
  have hTK : ∀ y ∈ lowT I, ∃ d, y = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ g + 1 :=
    fun y hy ↦ by
      obtain ⟨d, rfl, hd⟩ := hTQ y hy
      exact ⟨d, rfl, hd.2⟩
  have hrep : LowStateRepair I (g + 1) (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r') x := by
    simp only [Pts, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact lowStateRaise_private hs htb rfl rfl hNQ (fun f hf ↦ hf) (fun t ht ↦ ⟨t, ht, rfl⟩)
        fun t ht htK ↦ mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht, htK⟩, rfl⟩
    · exact lowStateRaise_donor hgm hs rfl rfl hNQ hTQ hNroot
  exact stateCatStep_low_of_lt_cap (by omega) hjm hKj hN hT hx hoK hrK hTK hrep P hPB hPC hPlow h
    hh hsh hb hPh a ha haP

end VaughtConjecture.ProfileTower

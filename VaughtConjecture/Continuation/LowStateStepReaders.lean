/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStepPin

/-!
# The LOW step for states above the controllers away from readers above the cap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the layers of states
above the controllers); semantic contract, items 3, 4 and 8.

The repair of the failure mode of the LOW step for states at the grade `K` of the controllers
(`ProfileTower.LowStateRepair`, compiled for the LOW designations of a seed) changes only cells of
grade at most `K` read at least at the cap.  Above `K` it is kept by splicing whenever no cell of
grade in `(K, j]` read above the cap reads such a cell.  The owner and the frontier play no role
above `K`: in particular a frontier not self-visible at `j`, or a prescribed owner strictly
between the cap and the replacement of the frontier at `j`, is no obstruction.

**Splicing along the changed cells** (`CellScheme.Rows.isLawfulBelow_splice_of_readers`, compiled
in this repository).  Let `V` be lawful below `(B, j)` and `U` lawful below `(B, K)`.  If every cell
`s` below `(B, j)` of grade above `K` is at most both labels of every cell below it of grade at most
`K` where `U` and `V` differ, then the labelling equal to `U` at the cells of grade at most `K` and
to `V` at the others is lawful below `(B, j)`: at such a cell `s` the locality is that of `V`, since
capping at `V s` erases every change.  (`CellScheme.Rows.isLawfulBelow_splice_of_le_cap` is the
case where every cell above `K` is at most the cap.)

**The repair above the controllers away from readers above the cap**
(`ProfileTower.lowStateRepair_of_readers`, compiled in this repository): with the designated fields
of grade at most `K` and the repair at `K`, every instance of the failure mode at `j ≥ K` in which
each cell of grade in `(K, j]` reading a cell of grade at most `K` at least at the cap is itself at
most the cap is repaired at `j`.  The repair at `K` agrees with `W₀` capped at the cap, so a changed
cell carries labels at least the cap in both.

**The LOW step for states away from readers above the cap**
(`ProfileTower.stateCatStep_low_of_readers`, `ProfileTower.stateCatStep_low_seed_of_readers`,
compiled in this repository): the conclusion of the step for states at `j ∈ [K, m]` at every state
`P` such that every cell of grade in `(K, j]` reading a cell of grade at most `K` labelled at least
the cap is labelled below the cap.  This contains `ProfileTower.stateCatStep_low_seed_of_lt_cap`.

**The two sides.**  The step can fail only at a cell of grade in `(K, j]` read above the cap that
reads a cell of grade at most `K` read at least at the cap.  When every cell at its graded index
reads a donor top at the replacement at `j` of its reading of a proper donor field (a pin), and a
prescribed cell inside it is above the cap, the step fails (`ProfileTower.not_stateCatStep_of_pin`).
A reader above the cap without such a tie is not decided here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}

/-- **Splicing along the changed cells.**  For `V` lawful below `(B, j)` and `U` lawful below
`(B, K)`: if every cell `s` below `(B, j)` of grade above `K` is at most `U d` and `V d` at every
cell `d` below it of grade at most `K` with `U d ≠ V d`, the labelling equal to `U` at the cells of
grade at most `K` and to `V` at the others is lawful below `(B, j)`. -/
theorem isLawfulBelow_splice_of_readers {B : Finset β} {K j : ℕ} {U V : ι → Label.{u}}
    (hU : R.IsLawfulBelow (B, K) fun d ↦ U d) (hV : R.IsLawfulBelow (B, j) fun d ↦ V d)
    (hread : ∀ s ∈ D.below (B, j), K < D.grade s → ∀ d ∈ D.below (D.gradedIndex s),
      D.grade d ≤ K → U d ≠ V d → V s ≤ U d ∧ V s ≤ V d) :
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
    · have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if D.grade d.1 ≤ K then U d.1 else V d.1) (if D.grade s ≤ K then U s else V s)) =
          fun d ↦ min (V d.1) (V s) := by
        funext d
        rw [ite_eq_right hsK]
        split_ifs with hdK
        · by_cases hUV : U d.1 = V d.1
          · rw [hUV]
          · obtain ⟨h1, h2⟩ := hread s hs (not_le.mp hsK) d.1 d.2 hdK hUV
            rw [min_eq_right h1, min_eq_right h2]
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

variable {K j : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The repair above the controllers away from readers above the cap.**  As
`ProfileTower.lowStateRepair_of_le_cap`, with the hypothesis that `W₀` is at most `h` at the cells
of grade in `(K, j]` weakened to: every cell of grade in `(K, j]` with a cell of grade at most `K`
below it read by `W₀` at least at `h` is read by `W₀` at most at `h`
(`CellScheme.Rows.isLawfulBelow_splice_of_readers`; a cell changed by the repair at `K` carries
labels at least `h` in both, by the capped agreement). -/
theorem lowStateRepair_of_readers (hKj : K ≤ j) {x : Fin (m + 2)}
    (hoK : I.amalgam.toCellScheme.grade o ≤ K) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hTK : ∀ y ∈ T, ∃ d, y = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K)
    (hrep : LowStateRepair I K K N T o r x) {P : CProf I} (hPC : IsCutLawful I j (camal P))
    (hPlow : lowPred K N T o r P) {h : Label.{u}} (hh : IsSelfVisible K h) (hb : ⊥ < h)
    {W₀ : Prof I} (hW₀ : IsCutLawful I j W₀) (hW₀P : ∀ d, min (W₀ d) h = min (P (Sum.inl d)) h)
    (hact : donorMax N (withCut W₀ ⊥) < min (P (Sum.inr ())) h)
    (hfh : h < frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥))
    (hread : ∀ s, K < I.amalgam.toCellScheme.grade s → I.amalgam.toCellScheme.grade s ≤ j →
      ∀ d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s),
        I.amalgam.toCellScheme.grade d ≤ K → h ≤ W₀ d → W₀ s ≤ h) :
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
  have hag (d : Fin I.amalgam.card) : min (WK d) h = min (W₀ d) h := (hWKP d).trans (hW₀P d).symm
  -- a changed cell carries labels at least `h` in both
  have hchg (d : Fin I.amalgam.card) (hne : WK d ≠ W₀ d) : h ≤ WK d ∧ h ≤ W₀ d := by
    by_cases h1 : W₀ d < h
    · exact absurd (eq_of_min_eq_of_lt (hag d).symm h1) hne
    have h2 : h ≤ W₀ d := not_lt.mp h1
    have h3 := hag d
    rw [min_eq_right h2] at h3
    exact ⟨min_eq_right_iff.mp h3, h2⟩
  have hcut (B : Finset (Fin (m + 2))) (hWKB : I.amalgam.rows.IsLawfulBelow (B, K) fun d ↦ WK d)
      (hW₀B : I.amalgam.rows.IsLawfulBelow (B, j) fun d ↦ W₀ d) :
      I.amalgam.rows.IsLawfulBelow (B, j) fun d ↦ W d :=
    Rows.isLawfulBelow_splice_of_readers hWKB hW₀B fun s hs hKs d hd hdK hne ↦ by
      obtain ⟨h1, h2⟩ := hchg d hne
      have hsh := hread s hKs hs.2 d hd hdK h2
      exact ⟨hsh.trans h1, hsh.trans h2⟩
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

/-- **The LOW step for states away from readers above the cap.**  As
`ProfileTower.stateCatStep_low_of_lt_cap`, with the hypothesis on `P` weakened to: every cell of
grade in `(K, j]` with a cell of grade at most `K` below it labelled by `P` at least at `h` is
labelled by `P` below `h`.  The glued profile `W₀` agrees with `P` capped at `h`, so it satisfies
the hypothesis of `ProfileTower.lowStateRepair_of_readers`. -/
theorem stateCatStep_low_of_readers (hj0 : 0 < j) (hjm : j ≤ m) (hKj : K ≤ j)
    (hN : Sum.inr () ∉ N) (hT : Sum.inr () ∉ T) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hoK : I.amalgam.toCellScheme.grade o ≤ K) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hTK : ∀ y ∈ T, ∃ d, y = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K)
    (hrep : LowStateRepair I K K N T o r x) (P : CProf I) (hPB : ∀ f, P f ∈ codeGrid j (bound I))
    (hPC : IsCutLawful I j (camal P)) (hPlow : lowPred K N T o r P) (h : Label.{u})
    (hh : IsSelfVisible j h) (hs : IsShort j h) (hb : ⊥ < h)
    (hPread : ∀ s, K < I.amalgam.toCellScheme.grade s → I.amalgam.toCellScheme.grade s ≤ j →
      ∀ d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s),
        I.amalgam.toCellScheme.grade d ≤ K → h ≤ P (Sum.inl d) → P (Sum.inl s) < h)
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
    -- the readers of grade in `(K, j]` above the cap read no cell at the cap or above
    have hread (s : Fin I.amalgam.card) (hKs : K < I.amalgam.toCellScheme.grade s)
        (hsj : I.amalgam.toCellScheme.grade s ≤ j) (d : Fin I.amalgam.card)
        (hd : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s))
        (hdK : I.amalgam.toCellScheme.grade d ≤ K) (hWd : h ≤ W₀ d) : W₀ s ≤ h := by
      have hPd : h ≤ P (Sum.inl d) := by
        have := hW₀P d
        rw [min_eq_right hWd] at this
        exact min_eq_right_iff.mp this.symm
      have hPs := hPread s hKs hsj d hd hdK hPd
      exact (eq_of_min_eq_of_lt (hW₀P s).symm hPs).le.trans hPs.le
    obtain ⟨W, hW, hWW₀, hWP, hfr⟩ := lowStateRepair_of_readers hKj hoK hrK hTK hrep hPC hPlow
      hhK hb hW₀ hW₀P hact (not_le.mp hfh) hread
    exact ⟨W, hW, fun d hd ↦ (hWW₀ d hd).trans (hW₀a d hd), hWP, fun _ ↦ hfr⟩
  refine ⟨W, min (P (Sum.inr ())) h, hW, hWa, hWP, ?_, by rw [min_assoc, min_self],
    lowPred_withCut_of_frontier hN hT hPlow hWP hfr⟩
  rcases le_total (P (Sum.inr ())) h with hle | hle
  · rw [min_eq_left hle]; exact hPB _
  · rw [min_eq_right hle]; exact mem_codeGrid_of_le hh hs (hPB _) hle

/-- **The LOW step for states at every grade `j ∈ [K, m]` for the LOW designations of a seed, away
from readers above the cap**: `ProfileTower.stateCatStep_low_of_readers` with the repair
at `K = g + 1` from both coatoms (`ProfileTower.lowStateRaise_private`,
`ProfileTower.lowStateRaise_donor`), when the private context is a source-gap context of grade
`g + 1 ≤ m` with the lost point last and the donor has top grade at most `g + 1`. -/
theorem stateCatStep_low_seed_of_readers {g : ℕ} (hgm : g + 1 ≤ m) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) (hKj : g + 1 ≤ j) (hjm : j ≤ m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (P : CProf I)
    (hPB : ∀ f, P f ∈ codeGrid j (bound I)) (hPC : IsCutLawful I j (camal P))
    (hPlow : lowPred (g + 1) (lowN I (g + 1)) (lowT I) (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r') P) (h : Label.{u})
    (hh : IsSelfVisible j h) (hsh : IsShort j h) (hb : ⊥ < h)
    (hPread : ∀ s, g + 1 < I.amalgam.toCellScheme.grade s → I.amalgam.toCellScheme.grade s ≤ j →
      ∀ d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s),
        I.amalgam.toCellScheme.grade d ≤ g + 1 → h ≤ P (Sum.inl d) → P (Sum.inl s) < h)
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
  exact stateCatStep_low_of_readers (by omega) hjm hKj hN hT hx hoK hrK hTK hrep P hPB hPC hPlow h
    hh hsh hb hPread a ha haP


end VaughtConjecture.ProfileTower

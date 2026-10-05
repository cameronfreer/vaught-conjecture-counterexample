/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ForcingDonors

/-!
# Special cases of the tied apex and of forcing donors

Roadmap, Layer 3 (the finite construction for forcing donors), for Layer 4, output 2.

* **The block index `η = 0`** (`λ_0 = ω`, `λ_1 = ω + ω`): every one-point legal type at `ω + ω`
  with a cell labelled at least `ω + n`, `n ≤ 4`, has a forcing donor.
* **The threshold `4` at a one-point type**: the one-point type labelled `λ_η + 4` has a donor,
  and every donor for it has at least `4` points; a one-point type does not force `2` by itself.
* **The formal top**: when the tied cell is labelled the formal top, the tie needs no hypothesis,
  and the donor of a type legal below the full grade forces its number of points.
* **The tied apex** carries the label of the tied cell, and its row takes the same value at the
  new cell and at the tied cell.

The five-cell twin type of `Continuation.CandidateCounterexamples` is not instantiated: its scheme
is private there.  Its cell `0` (label `β + 2`, threshold `2`) is an instance of
`forcingDonors_twoPoint_face`; its twin labelled `β + 1` needs only the threshold `1`, its grade
(the order law); its twin labelled `β + 2` at the threshold `2` is a residual input, for which a
donor with a single tie cell at the graded index `({0, 1, 2}, 2)` is argued, not compiled.
-/

universe u

namespace VaughtConjecture.ForcingDonorsExamples

open Finset Ordinal

/-- The block stages at `η = 0`: `λ_1 = ω + ω`. -/
example : blockStage (0 + 1 : Ordinal.{u}) = ω + ω := by
  rw [blockStage_add_one, blockStage_zero]

/-- **One-point inputs at `η = 0`**, thresholds up to `4`. -/
example (t : StageType.{u} (blockStage (0 + 1)) 1) (ht : t.IsLegal) (d : Fin t.card)
    (hd : (t.reduce (isSuccPrelimit_blockStage 0)).label d = ⊤) (n : ℕ) (hn4 : n ≤ 4)
    (hn : ((ω + n : Ordinal.{u}) : Label.{u}) ≤ t.label d) :
    ∃ (m : ℕ) (D : StageType.{u} (blockStage (0 + 1)) m) (g : Fin 1 ↪ Fin m),
      D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0)
        (D.reduce (isSuccPrelimit_blockStage 0)) g (t.reduce (isSuccPrelimit_blockStage 0)) d n :=
  forcingDonors_onePoint t ht d hd n (by rwa [blockStage_zero]) hn4

/-- **The threshold `4` at a one-point type**: some legal one-point type at `λ_{η+1}` labelled at
least `λ_η + 4` has a forcing donor at the threshold `4`, and every donor for it has at least `4`
points. -/
example {η : Ordinal.{u}} :
    ∃ t : StageType.{u} (blockStage (η + 1)) 1, t.IsLegal ∧ ∃ d : Fin t.card,
      (∃ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 1 ↪ Fin m),
        D.IsLegal ∧ StageType.restrictFace g D = some t ∧
        StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
          (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
          d 4) ∧
      ∀ (m : ℕ) (D : StageType.{u} (blockStage (η + 1)) m) (g : Fin 1 ↪ Fin m),
        StageType.restrictFace g D = some t →
        StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η)
          (D.reduce (isSuccPrelimit_blockStage η)) g (t.reduce (isSuccPrelimit_blockStage η))
          d 4 → 4 ≤ m := by
  obtain ⟨t, ht, d, hd, hn, hall⟩ := OnePoint.le_of_forcingDonor (η := η) (j := 4) (by omega)
  exact ⟨t, ht, d, forcingDonors_onePoint t ht d hd 4 hn le_rfl, hall⟩

/-- **A one-point type does not force `2` by itself**: its only cell has grade `1`. -/
example {η : Ordinal.{u}} (t : StageType.{u} (blockStage η) 1) (d : Fin t.card)
    (hd : t.label d = ⊤) :
    ¬ StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) t
      (Function.Embedding.refl _) t d 2 := by
  refine StageType.not_forcesThreshold_of_grade_le (K := 1) ?_ (fun c ↦ t.grade_le c)
    (StageType.restrictFace_refl t) hd
  rw [blockStage_add_one]
  exact (add_lt_add_iff_left _).mpr (natCast_lt_omega0 1)

/-- **The formal top**: a type legal below the full grade on `N > 0` points with `t` as a proper
face gives a donor forcing `N` at every cell of `t` labelled the formal top; the tie needs no
self-visibility hypothesis. -/
example {α β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) {N k : ℕ} {T : StageType.{u} α N}
    {t : StageType.{u} α k} (hT : T.IsLegalBelowFullGrade) (hN : 0 < N) {g : Fin k ↪ Fin N}
    (hg : Finset.univ.map g ≠ Finset.univ) (hgt : StageType.restrictFace g T = some t)
    {d : Fin t.card} (hd : t.label d = ⊤) :
    ∃ D : StageType.{u} α N, D.IsLegal ∧ StageType.restrictFace g D = some t ∧
      StageType.ForcesThreshold α hβ (D.reduce hβ) g (t.reduce hβ) d N :=
  StageType.exists_donor_of_isLegalBelowFullGrade hβ hT hN hg hgt (hd ▸ le_top)
    (hd ▸ Label.isSelfVisible_top N)

/-- **The tied apex carries the label of the tied cell**, and its row takes the same value at the
new cell and at the tied cell. -/
example {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
    {e : Fin t.card} (he : Label.IsSelfVisible n (t.label e)) (hn : 0 < n) :
    (t.addTiedApex ht he hn).label (Fin.last _) = t.label e ∧
      StageType.tiedApexRow ht e (Fin.last _) = StageType.tiedApexRow ht e e.castSucc := by
  refine ⟨StageType.tiedApexLabel_last e, ?_⟩
  rw [StageType.tiedApexRow_last, StageType.tiedApexRow_castSucc]

end VaughtConjecture.ForcingDonorsExamples

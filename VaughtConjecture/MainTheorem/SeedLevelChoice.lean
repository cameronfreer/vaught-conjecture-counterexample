/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLabel
import VaughtConjecture.MainTheorem.ReplicatedLevelChain
import VaughtConjecture.MainTheorem.ReplicatedLevelMirror

/-!
# The re-rendered levels at the seed position, at one choice of height and block bound

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**The choice** (`Seed.seedHeightLevel`, `Seed.seedBlockBound'`), functions of the seed and the root
only (not of a state, an ambient labelling or a cap):
* the height `H = #attachment + 1` (the number of cells of the attachment as ladder base data plus
  one);
* the block bound `B = max (2 * #attachment + 1) (Seed.seedGridBound)`: above twice the number of
  cells of the attachment, strictly (`Seed.two_mul_card_lt_seedBlockBound'`, as the twins of the
  mixed lifts ask), and at least the grid bound `Seed.seedGridBound`.
Every side condition of the levels holds at every seed and root (`Seed.seedHeightLevel_pos`,
`Seed.card_attachmentBase_le_seedHeightLevel`, `Seed.two_mul_card_le_seedBlockBound'`).

**Lifts below a level pass to the higher levels** (`Seed.lvLevel_cappedLift_iff_of_le`): the next
levels add cells at the grade above only.  **The copies** never lie inside the donor face, so the
replicated level lifts from a pair inside the donor face wherever the level does
(`Seed.ALvl.Good.cappedLift_rep_donor`).

**The onto root.**  At the seed position the root `g : Fin n ↪ Fin m` may be onto; then the
threshold is `n + 1 = m + 1` (`StageType.GrowthRequests.ClassCalibrated.threshold_eq_of_surjective`)
and the second coatom is the donor face (`Seed.donorFace_eq_coatom_of_surjective`, a statement about
finite sets of points only).

The lifts at the seed choice are in `VaughtConjecture.MainTheorem.SeedLevelStrictChoice`.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-! ### The choice of the height and the block bound -/

/-- **The height of the levels at a seed**: the number of cells of the attachment as ladder base
data plus one. -/
noncomputable def seedHeightLevel : ℕ := (I.attachmentBase g).S.card + 1

theorem seedHeightLevel_pos : 0 < I.seedHeightLevel g := Nat.succ_pos _

theorem card_attachmentBase_le_seedHeightLevel :
    (I.attachmentBase g).S.card ≤ I.seedHeightLevel g :=
  Nat.le_succ _

/-! ### The block bound -/

/-- **The block bound of the levels at a seed**: the larger of twice the number of cells of the
attachment plus one and the grid bound `Seed.seedGridBound`; it exceeds twice the number of cells
strictly. -/
noncomputable def seedBlockBound' : ℕ :=
  max (2 * (I.attachment g).card + 1) (I.seedGridBound g)

theorem two_mul_card_lt_seedBlockBound' : 2 * (I.attachment g).card < I.seedBlockBound' g :=
  Nat.lt_of_succ_le (le_max_left _ _)

theorem two_mul_card_le_seedBlockBound' : 2 * (I.attachment g).card ≤ I.seedBlockBound' g :=
  (two_mul_card_lt_seedBlockBound' I g).le

theorem seedGridBound_le_seedBlockBound' : I.seedGridBound g ≤ I.seedBlockBound' g :=
  le_max_right _ _

variable {I g}

/-! ### Lifts below a level pass to the higher levels -/

/-- **A lift into a pair of grade at most `i + 1` is the same in every level from the grade
`i + 1` on**: the next levels add cells at the grade above only. -/
theorem lvLevel_cappedLift_iff_of_le {H B : ℕ} {d : StageType.{u} α (n + 1)}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} {i : ℕ} {X : Finset (Fin (m + 2)) × ℕ} {k : ℕ}
    (hki : k ≤ i + 1) (h : X ≤ ((univ : Finset (Fin (m + 2))), k)) :
    ∀ J, i ≤ J → ((I.lvLevel g H B hd Q J).S.rows.CappedLift h ↔
      (I.lvLevel g H B hd Q i).S.rows.CappedLift h)
  | J, hJ => by
    induction J, hJ using Nat.le_induction with
    | base => exact Iff.rfl
    | succ J hiJ ih =>
      exact (ALvl.cappedLift_nS_iff (B := B) (I.lvLevel g H B hd Q J)
        (I.lvCat g B hd Q (J + 2)) h fun h' ↦ absurd h'.2 (by simp only; omega)).trans ih

/-! ### The replicated levels -/

/-- **The replicated level lifts from a pair inside the donor face** into a pair of full scope
wherever the level does: the copies have mixed scope, never inside the donor face. -/
theorem ALvl.Good.cappedLift_rep_donor {H B j : ℕ}
    {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop} {N : I.ALvl g H j}
    (hN : N.Good B A) {X Y : Finset (Fin (m + 2)) × ℕ} (h : X ≤ Y) (hY : Y.1 = univ)
    (hX : X.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)))
    (hT : N.S.rows.CappedLift h) : hN.rep.rows.CappedLift h :=
  Scheme.cappedLift_mirror_of (fun _ hU ↦ ne_univ_of_mem_mixedFaces hU) h hY
    (fun _ hU hsub ↦ ((I.mem_mixedFaces g).mp hU).2.2.2 (hsub.trans hX)) hT

end Seed

namespace StageType

namespace GrowthRequests

/-- **At an onto root the threshold is the arity of the donor**: requests calibrated on the class
have `n + 1 ≤` threshold, the threshold is the grade of a cell of the context on `m + 1` points,
and an onto root `Fin n ↪ Fin m` has `m ≤ n`; so `n = m` and the threshold is `n + 1`. -/
theorem ClassCalibrated.threshold_eq_of_surjective {α : Ordinal.{u}} {n m : ℕ}
    {t' : StageType.{u} α (m + 1)} {g : Fin n ↪ Fin m} {p : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) : n = m ∧ Q.threshold = n + 1 := by
  have hnm : m ≤ n := by simpa using Fintype.card_le_of_surjective g hg
  have hmn : n ≤ m := by simpa using Fintype.card_le_of_embedding g
  have h1 := hQ.arity
  have h2 := t'.grade_le Q.cap
  unfold threshold at h1 ⊢
  omega

end GrowthRequests

end StageType

end VaughtConjecture

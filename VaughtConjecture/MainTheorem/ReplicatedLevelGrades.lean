/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevel

/-!
# The levels of every grade, and their ladder base

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**The levels** (`Seed.lvLevel`): the first level, then the next level on the catalogue of each
grade (`Seed.ALvl.next`, `Seed.lvCat`).  Each is good (`Seed.lvLevel_good`, from
`Seed.lvLevel1_good` and `Seed.ALvl.Good.next`).

**The ladder base is recovered at every level** (`Seed.lvLevel_σ_embed`): at a state lawful below
`(univ, 1)`, with values self-visible at `1` and some value other than `⊥`, the section of every
level reads the cells of the ladder base as the first level does, ranks included: each level
decodes the ladder base of the code of the state as the ladder base of the state
(`Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne`).

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ}

variable (I : Seed.{u} α m) (g : Fin n ↪ Fin m) (H B : ℕ) {d : StageType.{u} α (n + 1)}
  (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
  (Q : GrowthRequests I.left d.toScheme)

/-- **The level at the grade `j + 1`**: the first level, then the next level on the catalogue of
each grade. -/
noncomputable def lvLevel : (j : ℕ) → I.ALvl g H (j + 1)
  | 0 => I.lvLevel1 g H
  | j + 1 => (lvLevel j).next B (I.lvCat g B hd Q (j + 2))

variable {I g H B hd Q}

theorem lvLevel_zero : I.lvLevel g H B hd Q 0 = I.lvLevel1 g H := rfl

theorem lvLevel_succ (j : ℕ) :
    I.lvLevel g H B hd Q (j + 1) = (I.lvLevel g H B hd Q j).next B (I.lvCat g B hd Q (j + 2)) :=
  rfl

/-- **Every level up to the number of points is good.** -/
theorem lvLevel_good (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 2 → (I.lvLevel g H B hd Q j).Good B (lvAdm hd Q)
  | 0, _ => lvLevel1_good hH hcard _
  | j + 1, hj => (lvLevel_good hH hcard hQ hB j (by omega)).next hQ hj hB

/-- **The ladder base is recovered at every level**: at a state lawful below `(univ, 1)` with
values self-visible at `1` and some value other than `⊥`, the section of every level reads the
cells of the ladder base as the first level does. -/
theorem lvLevel_σ_embed (hcard : (I.attachmentBase g).S.card ≤ H) :
    ∀ (j : ℕ) (P : Fin (I.attachment g).card → Label.{u}),
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun e ↦ P e) →
      (∀ e, IsSelfVisible 1 (P e)) → (∃ e, P e ≠ ⊥) →
      ∀ t, (I.lvLevel g H B hd Q j).σ P ((I.lvLevel g H B hd Q j).embed t) = I.lvBaseSec g H P t
  | 0, _, _, _, _, _ => rfl
  | j + 1, P, hP1, hv, hpos, t => by
    have hC1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ orbitCode (j + 2) P e) := hP1.orbitCode fun e ↦ e.2.2.trans (by omega)
    have hCv (e : Fin (I.attachment g).card) : IsSelfVisible 1 (orbitCode (j + 2) P e) :=
      isSelfVisible_one_orbitCode (by omega) (hv e)
    have hCpos : ∃ e, orbitCode (j + 2) P e ≠ ⊥ := by
      obtain ⟨e, he⟩ := hpos
      exact ⟨e, fun h ↦ he (orbitCode_eq_bot_iff.mp h)⟩
    change upperDecoderAt (j + 2) (j + 3) B P
      ((I.lvLevel g H B hd Q j).Φ B (I.lvCat g B hd Q (j + 2)) (orbitCode (j + 2) P)
        (Fin.castAdd _ ((I.lvLevel g H B hd Q j).embed t))) = I.lvBaseSec g H P t
    rw [ALvl.Φ_castAdd, lvLevel_σ_embed hcard j _ hC1 hCv hCpos t,
      lvBaseSec_of_isLawfulBelow hcard hC1, lvBaseSec_of_isLawfulBelow hcard hP1]
    exact Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne hcard
      (by omega) hP1 hC1 hv hpos t

end Seed

end VaughtConjecture

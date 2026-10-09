/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStep

/-!
# The step for states above the controllers: a rigid reading refutes it

Roadmap, Layer 3 ((R2), the state tower of the LOW construction; the step for states above the
controllers, `StageType.StateStepsAbove`).

The step for states (`ProfileTower.StateCatStep I j A x`) at a grade `j` above the grade `K` of the
controllers asks, for a state `P` of the LOW clause and a prescription `a` below the coatom
`univ.erase x` agreeing with `P` capped at `h`, a profile `W` lawful on the cut, literal on the
coatom, agreeing with `P` capped at `h`, with a cutoff `β` keeping the LOW clause.  The failure
mode is a state active below the cap whose prescribed frontier `c` lies above the cap: the donor
tops must then be raised to at least `c`.

**Rigidity of a reading** (`Scheme.min_le_visibilityReplace_of_rowAt_eq`).  If the row of a cell
`w` of grade `k` reads a cell `t` as the replacement at `k` of its reading of a cell `d`
(`rowAt w t = visibilityReplace k k (rowAt w d)`), then every labelling lawful at `w` with
`W d < W w` has `min (W t) (W w) ≤ visibilityReplace k k (W d)`: the witness of the locality of
`w` sends the reading of `d` to `W d` and commutes with the replacement at `k`.  So `t` cannot be
raised above `visibilityReplace k k (W d)` while `w` stays above it.

**The negative** (`ProfileTower.not_stateCatStep_of_rigid`).  Let every cell of graded index
`(univ.erase y, j)` read a donor top `t` rigidly through a cell `d` labelled below the cap by the
state, let a cell `u` below both coatoms at the grade `j` be prescribed above
`θ = visibilityReplace j j (P d)`, and let the state be active below the cap with its proper donor
fields below the cap and the prescribed frontier above `θ`.  Then the step for states fails from
the coatom `univ.erase x`: availability puts a cell of graded index `(univ.erase y, j)` above the
prescribed `u`, rigidity keeps `t` at most `θ`, the cutoff keeps the clause active, and the clause
asks `t` at least the frontier, above `θ`.  In a legal instance `θ` is the cap itself (`P d` and
`h` in one block, `P d` of finite part below `j`, `h` of finite part `j`): with `θ` below the cap
the state could not be active, by the same rigidity applied to it.

This is a statement about `ProfileTower.StateCatStep` (the hypothesis form of
`StageType.StateStepsAbove`), not about the lifts of the state tower themselves; whether a legal
family realizes the configuration is not compiled here.

## References

The LOW construction is that of [AFK26]; the rows and their locality are [Kni26, Definition
2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Rigidity of a reading -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **Rigidity of a reading.**  Let `W` be lawful below a pair `X` containing the cell `w` of grade
`k`, whose row reads `t` as the replacement at `k` of its reading of `d`, both below `w`.  If
`W d < W w`, then `min (W t) (W w) ≤ visibilityReplace k k (W d)`. -/
theorem min_le_visibilityReplace_of_rowAt_eq {X : Finset (Fin n) × ℕ} {W : Fin S.card → Label.{u}}
    (hW : S.rows.IsLawfulBelow X fun e ↦ W e) {w t d : Fin S.card}
    (hw : w ∈ S.toCellScheme.below X)
    (ht : t ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex w))
    (hd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex w))
    (hrow : S.rowAt w t = visibilityReplace (S.toCellScheme.grade w) (S.toCellScheme.grade w)
      (S.rowAt w d))
    (hdw : W d < W w) :
    min (W t) (W w) ≤
      visibilityReplace (S.toCellScheme.grade w) (S.toCellScheme.grade w) (W d) := by
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  obtain ⟨g, σ, hσ, heq⟩ := hloc w hw
  set k := S.toCellScheme.grade w with hk
  have hww : w ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex w) :=
    S.toCellScheme.mem_below_gradedIndex w
  -- the value at `w` is at most the suppressor at `k`
  have hgk : W w ≤ g k := by
    have h1 : min (W w) (W w) = min (σ (S.rows.row w ⟨w, hww⟩)) (g k) := heq ⟨w, hww⟩
    rw [min_self] at h1
    rw [h1]
    exact min_le_right _ _
  -- the witness reads `d` as `W d`
  have hgd : g k ≤ g (S.toCellScheme.grade d) := hσ.antitone hd.2
  have hσd : σ (S.rowAt w d) = W d := by
    have h1 : min (W d) (W w) = min (σ (S.rows.row w ⟨d, hd⟩)) (g (S.toCellScheme.grade d)) :=
      heq ⟨d, hd⟩
    rw [min_eq_left hdw.le, ← Scheme.rowAt_of_mem hd] at h1
    have hlt : W d < g (S.toCellScheme.grade d) := hdw.trans_le (hgk.trans hgd)
    rcases le_total (σ (S.rowAt w d)) (g (S.toCellScheme.grade d)) with hle | hle
    · rw [min_eq_left hle] at h1; exact h1.symm
    · rw [min_eq_right hle] at h1; exact absurd h1 hlt.ne
  -- the witness commutes with the replacement at `k`
  have hσt : σ (S.rowAt w t) = visibilityReplace k k (W d) := by
    rw [hrow, hσ.visibilityReplace_comm _ k (by rw [hσd]; exact hdw.le.trans hgk) k le_rfl, hσd]
  have h1 : min (W t) (W w) = min (σ (S.rows.row w ⟨t, ht⟩)) (g (S.toCellScheme.grade t)) :=
    heq ⟨t, ht⟩
  rw [h1, ← Scheme.rowAt_of_mem ht, hσt]
  exact min_le_left _ _

end Scheme

/-! ### The step for states fails at a rigid reading -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The step for states fails at a rigid reading** of a donor top above the controllers.  Let
`x, y` be the two coatoms, `j` a grade, and let every cell `w` of graded index
`(univ.erase y, j)` (there is one, `w₀`) read the donor top `t` (a field of `T`) as the replacement
at `j` of its reading of the cell `d`.  Let `P` be a state of the LOW clause at `K` (in the code
grid, lawful on the cut, LOW), active below the cap `h` (its proper donor fields below `h`, its
donor maximum below its cutoff and below `h`), with `P d < h`.  Let the prescription `a`, lawful
below `(univ.erase x, j)` and agreeing there with `P` capped at `h`, have a cell `u` below both
coatoms at the grade `j` above `θ = visibilityReplace j j (P d)`, and its frontier (owner and lost
top below the coatom) above `θ`.  Then the step for states fails from `univ.erase x`. -/
theorem not_stateCatStep_of_rigid {K j : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {x y : Fin (m + 2)}
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, j))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, j) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace j j (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y) (hug : I.amalgam.toCellScheme.grade u = j)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    {P : CProf I} (hPB : ∀ f, P f ∈ codeGrid j (bound I)) (hPC : IsCutLawful I j (camal P))
    (hPA : lowPred K N T o r P) {h : Label.{u}} (hh : IsSelfVisible j h) (hsh : IsShort j h)
    (hb : ⊥ < h)
    (hN : ∀ f ∈ N, ∃ e, f = Sum.inl e ∧ P (Sum.inl e) < h)
    (hact : donorMax N P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
      min (a e) h = min (P (Sum.inl e)) h)
    (hau : visibilityReplace j j (P (Sum.inl d)) < a u)
    (hfr : visibilityReplace j j (P (Sum.inl d)) < min (a o) (visibilityReplace K K (a r))) :
    ¬ StateCatStep I j (lowPred K N T o r) x := by
  intro hstep
  obtain ⟨W, β, hW, hWa, hWP, -, hβ, hA⟩ := hstep P hPB hPC hPA h hh hsh hb a ha haP
  set θ := visibilityReplace j j (P (Sum.inl d)) with hθ
  -- `W` reads `d` as `P` does
  have hWd : W d = P (Sum.inl d) := by
    have h1 := hWP d
    rw [min_eq_left hd.le] at h1
    rcases le_total (W d) h with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1; exact absurd h1.symm hd.ne
  -- availability below the other coatom puts a cell of graded index `(univ.erase y, j)` above `u`
  have hWy : I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun e ↦ W e) :=
    hW.isLawfulBelow_erase hy
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hWy
  have hw₀b : w₀ ∈ I.amalgam.toCellScheme.below (univ.erase y, j) := by
    rw [CellScheme.mem_below, hw₀]
  obtain ⟨w, hw, huw⟩ := havail u w₀ hw₀b
    (by rw [show I.amalgam.toCellScheme.scope w₀ = univ.erase y from congrArg Prod.fst hw₀]
        exact huy)
    (by rw [hug, show I.amalgam.toCellScheme.grade w₀ = j from congrArg Prod.snd hw₀])
  have hwg : I.amalgam.toCellScheme.grade w = j := congrArg Prod.snd (hw.trans hw₀)
  have hwb : w ∈ I.amalgam.toCellScheme.below (univ.erase y, j) := by
    rw [CellScheme.mem_below, hw, hw₀]
  obtain ⟨htw, hdw, hrow⟩ := hrigid w (hw.trans hw₀)
  -- `w` lies above `θ`
  have hWu : W u = a u := hWa u hux
  have hθw : θ < W w := hau.trans_le (hWu ▸ huw)
  have hdθ : P (Sum.inl d) ≤ θ := le_visibilityReplace (by omega) _
  -- rigidity keeps `t` at most `θ`
  have hrig := Scheme.min_le_visibilityReplace_of_rowAt_eq hWy hwb htw hdw
    (by rw [hwg]; exact hrow) (by rw [hWd]; exact hdθ.trans_lt hθw)
  rw [hwg, hWd] at hrig
  have hWt : W t ≤ θ := by
    rcases le_total (W t) (W w) with hle | hle
    · rwa [min_eq_left hle] at hrig
    · rw [min_eq_right hle] at hrig; exact absurd hrig (not_le.mpr hθw)
  -- the clause is active
  have hdm : donorMax N (withCut W β) = donorMax N P := by
    refine Finset.sup_congr rfl fun f hf ↦ ?_
    obtain ⟨e, rfl, he⟩ := hN f hf
    change W e = P (Sum.inl e)
    have h1 := hWP e
    rw [min_eq_left he.le] at h1
    rcases le_total (W e) h with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1; exact absurd h1.symm he.ne
  have hactW : donorMax N (withCut W β) < (withCut W β) (Sum.inr ()) := by
    rw [hdm]
    change donorMax N P < β
    exact hact.trans_le (by rw [← hβ]; exact min_le_left _ _)
  have hlow := hA hactW _ ht
  -- the frontier of `W` is that of the prescription
  have hfW : frontier K (Sum.inl o) (Sum.inl r) (withCut W β) =
      min (a o) (visibilityReplace K K (a r)) := by
    change min (W o) (visibilityReplace K K (W r)) = _
    rw [hWa o ho, hWa r hr]
  have h2 : min (a o) (visibilityReplace K K (a r)) ≤ W t := by
    rw [← hfW]
    exact (le_max_right _ _).trans hlow
  exact absurd (hfr.trans_le (h2.trans hWt)) (lt_irrefl _)

end ProfileTower

end VaughtConjecture

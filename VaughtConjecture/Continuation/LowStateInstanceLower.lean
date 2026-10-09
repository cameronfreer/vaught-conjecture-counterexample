/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateClauseAll

/-!
# A donor top prescribed at the cap below a held frontier

Roadmap, Layer 3 ((R2), the state tower of the LOW construction: the step for states above the
controllers under the clause of the layer).

Under the clause of the layer (`ProfileTower.lowPred_scode_of_le`: the donor maximum over the
proper donor fields of grade at most the layer's grade `j`) the rigid reading of a donor top is
excluded (`ProfileTower.not_active_of_mem_fields`).  Its mirror on the private side is not: the
fields of the clause are donor fields, while the owner and the lost top are private cells.

**A monotone reading bounds from below** (`Scheme.le_of_rowAt_le_of_lt`).  If the row of a cell
`w` reads `e` at least as it reads `d`, and `W d < W w`, then `W d ≤ W e`: the witness of the
locality of `w` reads `d` as `W d` and is monotone.

**The negative** (`ProfileTower.not_stateCatStep_of_held`).  Let the prescription be on the coatom
`univ.erase x`, with a donor top `t` prescribed below the frontier lower bound
`min (a d₁) (visibilityReplace K K (a d₂))`, the cells `d₁`, `d₂` prescribed, and let every cell of
graded index `(univ.erase y, j)` (the other coatom) read the owner at least as `d₁` and the lost
top at least as `d₂`, with a prescribed cell `u` below both coatoms at the grade `j` above `a d₁`
and `a d₂`.  Then at a state active below the cap the step for states fails: availability puts a
cell of graded index `(univ.erase y, j)` above `u`, which holds the owner at least at `a d₁` and the
lost top at least at `a d₂`, so the frontier stays above the prescribed donor top.  In an instance
the donor top is prescribed exactly at the cap (`P t ≥ h`, `a t = h`), with `d₁`, `d₂` root cells
prescribed above the cap: the case of a donor top at the cap of `ProfileTower.lowStateFail_raise`.
The clause of the layer does not exclude it.  Whether a legal family realizes it is not compiled.

## References

The LOW construction is that of [AFK26]; the rows and their locality are [Kni26, Definition
2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **A monotone reading bounds from below.**  Let `W` be lawful below a pair `X` containing the
cell `w`, whose row reads `e` at least as it reads `d`, both below `w`.  If `W d < W w`, then
`W d ≤ W e`. -/
theorem le_of_rowAt_le_of_lt {X : Finset (Fin n) × ℕ} {W : Fin S.card → Label.{u}}
    (hW : S.rows.IsLawfulBelow X fun e ↦ W e) {w d e : Fin S.card}
    (hw : w ∈ S.toCellScheme.below X)
    (hd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex w))
    (he : e ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex w))
    (hrow : S.rowAt w d ≤ S.rowAt w e) (hdw : W d < W w) : W d ≤ W e := by
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  obtain ⟨g, σ, hσ, heq⟩ := hloc w hw
  have hww : w ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex w) :=
    S.toCellScheme.mem_below_gradedIndex w
  have hgk : W w ≤ g (S.toCellScheme.grade w) := by
    have h1 : min (W w) (W w) =
        min (σ (S.rows.row w ⟨w, hww⟩)) (g (S.toCellScheme.grade w)) := heq ⟨w, hww⟩
    rw [min_self] at h1
    rw [h1]
    exact min_le_right _ _
  have hσd : σ (S.rowAt w d) = W d := by
    have h1 : min (W d) (W w) = min (σ (S.rows.row w ⟨d, hd⟩)) (g (S.toCellScheme.grade d)) :=
      heq ⟨d, hd⟩
    rw [min_eq_left hdw.le, ← Scheme.rowAt_of_mem hd] at h1
    have hlt : W d < g (S.toCellScheme.grade d) :=
      hdw.trans_le (hgk.trans (hσ.antitone hd.2))
    rcases le_total (σ (S.rowAt w d)) (g (S.toCellScheme.grade d)) with hle | hle
    · rw [min_eq_left hle] at h1; exact h1.symm
    · rw [min_eq_right hle] at h1; exact absurd h1 hlt.ne
  have h1 : min (W e) (W w) = min (σ (S.rows.row w ⟨e, he⟩)) (g (S.toCellScheme.grade e)) :=
    heq ⟨e, he⟩
  rw [← Scheme.rowAt_of_mem he] at h1
  have h2 : W d ≤ min (W e) (W w) := by
    rw [h1, ← hσd]
    exact le_min (hσ.monotone hrow) (hσd ▸ hdw.le.trans (hgk.trans (hσ.antitone he.2)))
  exact h2.trans (min_le_left _ _)

end Scheme

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **A donor top prescribed below a held frontier refutes the step for states.**  Let the
prescription `a` on `univ.erase x` (lawful, agreeing with the state `P` capped at `h`) put the donor
top `t` below `min (a d₁) (visibilityReplace K K (a d₂))`, and a cell `u` below both coatoms at the
grade `j` above `a d₁` and `a d₂`; let every cell of graded index `(univ.erase y, j)` (there is one,
`w₀`) read the owner `o` at least as `d₁` and the lost top `r` at least as `d₂`.  At a state active
below the cap (its fields below `h`, its donor maximum below its cutoff and below `h`), the step for
states fails from `univ.erase x`. -/
theorem not_stateCatStep_of_held {K j : ℕ} {Nf : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card} {x y : Fin (m + 2)}
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) {t d₁ d₂ u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, j))
    (hheld : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, j) →
      o ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      r ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₁ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₂ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w d₁ ≤ I.amalgam.rowAt w o ∧ I.amalgam.rowAt w d₂ ≤ I.amalgam.rowAt w r)
    (ht : Sum.inl t ∈ T) (htx : t ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, j))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y) (hug : I.amalgam.toCellScheme.grade u = j)
    {P : CProf I} (hPB : ∀ f, P f ∈ codeGrid j (bound I)) (hPC : IsCutLawful I j (camal P))
    (hPA : lowPred K Nf T o r P) {h : Label.{u}} (hh : IsSelfVisible j h) (hsh : IsShort j h)
    (hb : ⊥ < h) (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, j) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, j),
      min (a e) h = min (P (Sum.inl e)) h)
    (hu₁ : a d₁ < a u) (hu₂ : a d₂ < a u)
    (hat : a t < min (a d₁) (visibilityReplace K K (a d₂))) :
    ¬ StateCatStep I j (lowPred K Nf T o r) x := by
  intro hstep
  obtain ⟨W, β, hW, hWa, hWP, -, hβ, hA⟩ := hstep P hPB hPC hPA h hh hsh hb a ha haP
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
  have hwb : w ∈ I.amalgam.toCellScheme.below (univ.erase y, j) := by
    rw [CellScheme.mem_below, hw, hw₀]
  obtain ⟨how, hrw, hd₁w, hd₂w, hrow₁, hrow₂⟩ := hheld w (hw.trans hw₀)
  have hWu : W u = a u := hWa u hux
  -- the owner and the lost top are held
  have hWo : a d₁ ≤ W o := by
    have h1 := Scheme.le_of_rowAt_le_of_lt hWy hwb hd₁w how hrow₁
      (by rw [hWa d₁ hd₁]; exact hu₁.trans_le (hWu ▸ huw))
    rwa [hWa d₁ hd₁] at h1
  have hWr : a d₂ ≤ W r := by
    have h1 := Scheme.le_of_rowAt_le_of_lt hWy hwb hd₂w hrw hrow₂
      (by rw [hWa d₂ hd₂]; exact hu₂.trans_le (hWu ▸ huw))
    rwa [hWa d₂ hd₂] at h1
  -- the clause is active
  have hdm : donorMax Nf (withCut W β) = donorMax Nf P := by
    refine Finset.sup_congr rfl fun f hf ↦ ?_
    obtain ⟨e, rfl, he⟩ := hNf f hf
    change W e = P (Sum.inl e)
    have h1 := hWP e
    rw [min_eq_left he.le] at h1
    rcases le_total (W e) h with hle | hle
    · rwa [min_eq_left hle] at h1
    · rw [min_eq_right hle] at h1; exact absurd h1.symm he.ne
  have hactW : donorMax Nf (withCut W β) < (withCut W β) (Sum.inr ()) := by
    rw [hdm]
    change donorMax Nf P < β
    exact hact.trans_le (by rw [← hβ]; exact min_le_left _ _)
  have hlow := hA hactW _ ht
  have hfr : min (a d₁) (visibilityReplace K K (a d₂)) ≤
      Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W β) :=
    min_le_min hWo (monotone_visibilityReplace le_rfl hWr)
  have h2 : min (a d₁) (visibilityReplace K K (a d₂)) ≤ W t :=
    hfr.trans ((le_max_right _ _).trans hlow)
  rw [hWa t htx] at h2
  exact absurd (hat.trans_le h2) (lt_irrefl _)

end ProfileTower

end VaughtConjecture

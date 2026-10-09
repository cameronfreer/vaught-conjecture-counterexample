/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateInstanceNormal

/-!
# The admission clause of the state catalogue with the donor maximum over more fields

Roadmap, Layer 3 ((R2), the state tower of the LOW construction: its admission clause).

**The decision recorded.**  The LOW clause of the state catalogue was to take its donor maximum over
the proper donor fields of the grades of the current layer, not only over those of grade at most
`K`.  This is a change of the construction's admission clause, not of the class of models: the
reason is
`ProfileTower.not_sCatStep_of_rigid_state` (with the maximum over the fields of grade at most `K`,
the rigid reading refutes the state step of the tower at a normalized state), and
`ProfileTower.not_active_of_mem_fields` (with the cells of the rigid reading among the fields, the
configuration is excluded).

**One fixed predicate over all grades is not kept by the state codes**
(`ProfileTower.not_lowPred_scode_of_high`).  The state tower asks its predicate to be kept by the
state code at every grade of its layers (`ProfileTower.sTower_good`, hypothesis `hAc`).  The state
code at a grade `j` first splices the state at `j` (`ProfileTower.hatS`), erasing the fields of
grade above `j`.  With the donor maximum over all proper donor fields (`ProfileTower.lowNAll`), a
state inactive only through a field of grade above `j` becomes active after the splice, and its
donor top below the frontier then violates the clause; the orbit code reads the violation back
(`Label.orbitCode_lt_orbitCode`).  So `lowPred K lowNAll …` cannot replace `lowPred K (lowN K) …`
in the tower as it stands.

**The clause of the layer** (`ProfileTower.lowPred_scode_of_le`).  A clause whose fields, tops,
owner and lost top have grade at most `j₀` is kept by the state code at every grade `j ≥ j₀`, so
the clause `lowPred K (lowN I j) (lowT I) o r` of the layer of grade `j` is kept by the codes of
that layer.  **It does not fit the tower either**: the row of a controller of the layer `g + 1`
reads the section of the level at `g` of its state (`ProfileTower.SLvl.Good.isLawfulBelow_Φs` uses
`SLvl.Good.lawful` of that level, which asks the level's predicate of the state), so a state
admitted at the layer `g + 1` must be admitted at every layer below, and the clauses accumulate down
to the clause of grade `K`.  A state admitted by the clause of `g + 1` only through a field of grade
`g + 1` is not admitted at `g` (`ProfileTower.not_lowPred_scode_of_high` with `lowN I (g + 1)` and
the splice at `g`).  The cumulative clause contains the clause of grade `K`, at which the rigid
reading refutes the step (`ProfileTower.not_sCatStep_of_rigid_state`).  So no weakening of the
admission clause by layers keeps the tower as it stands.

## References

The LOW construction is that of [AFK26].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {K : ℕ}
  {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **A fixed clause over fields of all grades is not kept by the state code** at a grade `j`: a
state inactive only through a field `e` of grade above `j` (its value at least the cutoff, every
other field of grade at most `j` below the cutoff, so that `e` has grade above `j`), with a donor
top `x` of grade at most `j` below its owner and its lost top (of grade at most `j`), satisfies the
clause, while its state code at `j` does not. -/
theorem not_lowPred_scode_of_high {j : ℕ} {P : CProf I} {e x : Fin I.amalgam.card}
    (he : Sum.inl e ∈ N) (hPe : P (Sum.inr ()) ≤ P (Sum.inl e))
    (hlow : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧
      (I.amalgam.toCellScheme.grade d ≤ j → P (Sum.inl d) < P (Sum.inr ())))
    (hcut : ⊥ < P (Sum.inr ())) (hx : Sum.inl x ∈ T) (hxj : I.amalgam.toCellScheme.grade x ≤ j)
    (hoj : I.amalgam.toCellScheme.grade o ≤ j) (hrj : I.amalgam.toCellScheme.grade r ≤ j)
    (hxo : P (Sum.inl x) < P (Sum.inl o)) (hxr : P (Sum.inl x) < P (Sum.inl r)) :
    lowPred K N T o r P ∧ ¬ lowPred K N T o r (scode j P) := by
  refine ⟨fun hact ↦ absurd (hact.trans_le (hPe.trans (le_donorMax he))) (lt_irrefl _), ?_⟩
  intro hlowc
  set Q := hatS j P with hQ
  have hQd (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ j) :
      Q (Sum.inl d) = P (Sum.inl d) := hat_of_le hd
  -- the splice is active
  have hQact : donorMax N Q < Q (Sum.inr ()) := by
    change N.sup Q < P (Sum.inr ())
    refine (Finset.sup_lt_iff hcut).mpr fun f hf ↦ ?_
    obtain ⟨d, rfl, hd⟩ := hlow f hf
    by_cases hdj : I.amalgam.toCellScheme.grade d ≤ j
    · rw [hQd d hdj]; exact hd hdj
    · change hat I j (camal P) d < _
      rw [hat_of_lt (not_le.mp hdj)]; exact hcut
  -- the clause of the code reads back on the values of the splice
  have h1 := hlowc (donorMax_orbitCode_lt hQact) _ hx
  have h2 := (le_max_right _ _).trans h1
  unfold Label.frontier at h2
  have h3 : min (orbitCode j Q (Sum.inl o)) (orbitCode j Q (Sum.inl r)) ≤
      orbitCode j Q (Sum.inl x) :=
    (min_le_min_left _ (le_visibilityReplace (by omega) _)).trans h2
  rcases min_le_iff.mp h3 with h4 | h4
  · have h5 := le_of_orbitCode_le h4
    rw [hQd o hoj, hQd x hxj] at h5
    exact absurd hxo (not_lt.mpr h5)
  · have h5 := le_of_orbitCode_le h4
    rw [hQd r hrj, hQd x hxj] at h5
    exact absurd hxr (not_lt.mpr h5)

/-- **The clause of a layer is kept by the state codes above it**: if the fields, the tops, the
owner and the lost top of the clause have grade at most `j₀`, the clause is kept by the state code
at every grade `j ≥ j₀` (`j₀ ≥ K`). -/
theorem lowPred_scode_of_le {j₀ j : ℕ} (hKj₀ : K ≤ j₀) (hj : j₀ ≤ j)
    (hN : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ j₀)
    (hT : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ j₀)
    (ho : I.amalgam.toCellScheme.grade o ≤ j₀) (hr : I.amalgam.toCellScheme.grade r ≤ j₀)
    {P : CProf I} (h : lowPred K N T o r P) : lowPred K N T o r (scode j P) := by
  have hhat : ∀ d, I.amalgam.toCellScheme.grade d ≤ j₀ → hatS j P (Sum.inl d) = P (Sum.inl d) :=
    fun d hd ↦ hat_of_le (hd.trans hj)
  have h1 : lowPred K N T o r (hatS j P) := by
    intro hlt x hx
    have hdm : donorMax N (hatS j P) = donorMax N P := donorMax_congr fun f hf ↦ by
      obtain ⟨d, rfl, hd⟩ := hN f hf
      exact hhat d hd
    have hfr : Label.frontier K (Sum.inl o) (Sum.inl r) (hatS j P) =
        Label.frontier K (Sum.inl o) (Sum.inl r) P := by
      unfold Label.frontier
      rw [hhat o ho, hhat r hr]
    obtain ⟨d, rfl, hd⟩ := hT x hx
    rw [hdm] at hlt
    have := h hlt _ hx
    rw [hfr, hhat d hd]
    exact this
  exact h1.map (isWitness_orbitMap j (hatS j P)) (stepSuppressor_of_le (hKj₀.trans hj))

end VaughtConjecture.ProfileTower

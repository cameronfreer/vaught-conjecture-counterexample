/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateInstanceLower
import VaughtConjecture.Continuation.LowStateTower

/-!
# The lift of a state layer through the contract: a realized state is active

Roadmap, Layer 3 ((R2), the state tower of the LOW construction: the lift of a layer of states from
a coatom, `ProfileTower.STowerLifts`); semantic contract, items 3, 4 and 8.

**Scope.**  A conditional obstruction to the state tower of
`VaughtConjecture.Continuation.LowStateTower` (whose code splices the fields above each layer and
whose LOW clause reads the proper donor fields of grade at most `K`), stated under the hypotheses
named in each theorem.  It is not on the proof of LOW displays: `StageType.hasLowDisplays_of_padded`
goes through the padded tower (`VaughtConjecture.Continuation.LowPaddedTower`), whose clause over
the proper donor fields of every grade excludes the configuration
(`ProfileTower.not_donorMax_lt_of_subset_coatD`).

The lift of the layer of a state catalogue `N.sS C` over a state level `N` at the grade `g` from a
coatom `(univ.erase x, g + 1)` to `(univ, g + 1)` is the contract `CellScheme.Rows.CappedLift`:
every prescription lawful below the coatom, agreeing with the ambient capped at the cap, extends
literally to a labelling lawful on the whole layer agreeing with the ambient capped at the cap.
The step for states (`ProfileTower.StateCatStep`) is a sufficient condition for it, refuted at a
rigid reading (`ProfileTower.not_stateCatStep_of_rigid`).  This file asks the contract itself.

**The reading of a lawful labelling at a cell** (`Scheme.exists_reading`).  A labelling `W`
lawful below a pair reads, at a cell `v` below it, the row of `v` through a witness `(g, σ)`:
`min (W e) (W v) = min (σ (rowAt v e)) (g (grade e))` at every cell `e` below `v`, with
`W v ≤ g (grade v)`.  Below `W v` the reading is exact (`Label.eq_of_min_eq_min_of_lt`).

**A realized state is active** (`ProfileTower.SLvl.Good.donorMax_lt_of_isLawfulBelow_sS`).  Let
`w` be lawful on the layer and agree capped at `h` with the row of an active state `P` of `C` in
the code grid (its donor maximum `D` below its cutoff and below `h`, its proper donor fields
amalgam cells of grade at most `g + 1`).  Every new cell `v` (of the state `Q`) with `D < w v` is
**active**: `D` is the donor maximum of `Q` and lies below its cutoff.  The row of `v` reads the
cell of `P` as the agreement height `κ` of `Q` and `P`, which `w` labels above `D` (the cell of
`P` reads `P` itself at the ceiling of the grid); the row of `v` reads the proper donor fields as
`Q` does, and `w` labels them as `P` does; so `κ` lies above `D`, where `Q` and `P` agree on the
proper donor fields and on the cutoff.  No orbit code, splice, or clause enters: the conclusion
is a statement about the rows of the layer.

**The contract fails at the rigid reading** (`ProfileTower.SLvl.Good.not_lawful_sS_of_rigid`,
`ProfileTower.SLvl.Good.not_cappedLift_sS_of_rigid`,
`ProfileTower.SLvl.Good.not_hasOwnerCappedLifts_sS_of_rigid`).  In the configuration of
`ProfileTower.not_stateCatStep_of_rigid` at the grade `j = g + 1`, with the state `P` a member of
the state catalogue `sCat I (g + 1) (lowPred K N T o r)` of the LOW clause: every cell of graded
index `(univ.erase y, j)` reads a donor top `t` rigidly through `d`; `u`, below both coatoms at
`j`, carries a label above `θ = visibilityReplace j j (P d)` and above the donor maximum; the
owner and the lost top carry a frontier above `θ`.  Then no labelling lawful on the layer agrees
with the row of `P` capped at `h` and carries these labels at `u`, `o` and `r`: availability
puts a new cell `v` above `u`, whose state is active (above) and LOW (a member of the catalogue),
so its witness reads the donor top at least at the frontier, above `θ`; rigidity on the amalgam
keeps the donor top at most `θ`.  Hence the layer does not lift capped from the coatom
`univ.erase x`, and it has no owner-capped lift at the cap `h` for an owner above the cap.  The
step for states and the contract fail together here: the slack between them (a lift realized by
an inactive state) does not exist.

**The held frontier** (`ProfileTower.SLvl.Good.not_lawful_sS_of_held`,
`ProfileTower.SLvl.Good.not_cappedLift_sS_of_held`).  The same holds in the configuration of
`ProfileTower.not_stateCatStep_of_held`: the private coatom holds the owner and the lost top above
`d₁` and `d₂` (monotone readings), and the donor top is prescribed below
`min (a d₁) (visibilityReplace K K (a d₂))`; the witness of the realized cell reads the frontier of
its LOW state at most at the donor top, and commutes with the replacement at `K` there.

**The lifts of the state tower** (`ProfileTower.not_sTowerLifts_of_rigid`,
`ProfileTower.not_sTowerLifts_of_held`, through `ProfileTower.not_sTowerLifts_of_layer`).  If
either configuration occurs at a member of the catalogue of some layer `J < J₀` of the state tower
of the LOW clause, the tower does not lift (`ProfileTower.STowerLifts`): the lifts below that
layer make its level good (`ProfileTower.sTower_good`), and its layer does not lift capped.

**Where a slack would have to come from.**  The activity of the realized state uses only that the
proper donor fields are cells of grade at most `g + 1`, read by the row of the realized cell; the
splice of the state code (`ProfileTower.hatS`) does not enter.  A clause whose donor maximum also
ranges over fields above the grade of the layer could be met by an inactive realized state (a
field the layer does not read may carry the maximum), but such a clause is not kept by the state
code, whose splice erases those fields (`ProfileTower.not_lowPred_scode_of_high`).

Whether a legal family realizes the configuration is not compiled here.  The negatives are
conditional obstructions to the state tower (whose code splices the fields above each layer and
whose clause reads the proper donor fields of grade at most `K`); the padded tower of
`VaughtConjecture.Continuation.LowPaddedTower` avoids them (the clause over every grade excludes
their hypothesis, `ProfileTower.not_donorMax_lt_of_subset_coatD`), and `StageType.HasLowDisplays`
is proved through it (`StageType.hasLowDisplays_of_padded`).

## References

The LOW construction is that of [AFK26]; the rows and their locality are [Kni26, Definition
2.5.4]; bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Reading a lawful labelling at a cell -/

/-- **A reading is exact below the value of the reading cell**: if `min a b = min x y` with
`a < b ≤ y`, then `x = a`. -/
theorem Label.eq_of_min_eq_min_of_lt {a b x y : Label.{u}} (h : min a b = min x y) (hab : a < b)
    (hby : b ≤ y) : x = a := by
  rw [min_eq_left hab.le] at h
  rcases le_total x y with hle | hle
  · rw [min_eq_left hle] at h; exact h.symm
  · rw [min_eq_right hle] at h; exact absurd (h ▸ hab.trans_le hby) (lt_irrefl _)

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **The reading of a lawful labelling at a cell.**  A labelling `W` lawful below `X` reads, at a
cell `v` below `X`, the row of `v` through a witness `(g, σ)`: at every cell `e` below `v`,
`min (W e) (W v) = min (σ (rowAt v e)) (g (grade e))`, and `W v ≤ g (grade v)`. -/
theorem exists_reading {X : Finset (Fin n) × ℕ} {W : Fin S.card → Label.{u}}
    (hW : S.rows.IsLawfulBelow X fun e ↦ W e) {v : Fin S.card}
    (hv : v ∈ S.toCellScheme.below X) :
    ∃ g σ, IsWitness g σ ∧ W v ≤ g (S.toCellScheme.grade v) ∧
      ∀ e ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex v),
        min (W e) (W v) = min (σ (S.rowAt v e)) (g (S.toCellScheme.grade e)) := by
  obtain ⟨-, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  obtain ⟨g, σ, hσ, heq⟩ := hloc v hv
  have hvv : v ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex v) :=
    S.toCellScheme.mem_below_gradedIndex v
  refine ⟨g, σ, hσ, ?_, fun e he ↦ ?_⟩
  · have h1 : min (W v) (W v) = min (σ (S.rows.row v ⟨v, hvv⟩)) (g (S.toCellScheme.grade v)) :=
      heq ⟨v, hvv⟩
    rw [min_self] at h1
    rw [h1]
    exact min_le_right _ _
  · rw [Scheme.rowAt_of_mem he]
    exact heq ⟨e, he⟩

end Scheme

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {N : SLvl I g}
  {A : CProf I → Prop} {C : Finset (CProf I)}

/-! ### The cells of a state layer -/

/-- An old amalgam cell of the layer keeps its graded index. -/
theorem SLvl.Good.gradedIndex_sS_embed (hN : N.Good A) (d : Fin I.amalgam.card) :
    (N.sS C).toCellScheme.gradedIndex (Fin.castAdd C.card (N.embed d)) =
      I.amalgam.toCellScheme.gradedIndex d := by
  rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  exact Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)

/-- An amalgam cell of grade at most `g + 1` lies below `(univ, g + 1)` in the layer. -/
theorem SLvl.Good.embed_mem_below_sS (hN : N.Good A) {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
    Fin.castAdd C.card (N.embed d) ∈
      (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
  rw [CellScheme.mem_below, hN.gradedIndex_sS_embed]
  exact ⟨subset_univ _, hd⟩

/-- A new cell of the layer lies below `(univ, g + 1)`. -/
theorem SLvl.natAdd_mem_below_sS (i : Fin C.card) :
    Fin.natAdd N.S.card i ∈
      (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
  rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]

/-- The row of a new cell reads an amalgam cell of grade at most `g + 1` as its state does. -/
theorem SLvl.Good.rowAt_sS_natAdd_embed (hN : N.Good A) (i : Fin C.card)
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
    (N.sS C).rowAt (Fin.natAdd N.S.card i) (Fin.castAdd C.card (N.embed d)) =
      (C.equivFin.symm i).1 (Sum.inl d) := by
  have hmem : Fin.castAdd C.card (N.embed d) ∈ (N.sS C).toCellScheme.below
      ((N.sS C).toCellScheme.gradedIndex (Fin.natAdd N.S.card i)) := by
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact hN.embed_mem_below_sS hd
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, SLvl.Φs_castAdd, hN.literal]

/-- The row of a new cell reads a new cell as the agreement height of their states. -/
theorem SLvl.rowAt_sS_natAdd_natAdd (i i' : Fin C.card) :
    (N.sS C).rowAt (Fin.natAdd N.S.card i) (Fin.natAdd N.S.card i') =
      agreementHeight (grid (g + 1) (bound I)) (C.equivFin.symm i).1 (C.equivFin.symm i').1 := by
  have hmem : Fin.natAdd N.S.card i' ∈ (N.sS C).toCellScheme.below
      ((N.sS C).toCellScheme.gradedIndex (Fin.natAdd N.S.card i)) := by
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact SLvl.natAdd_mem_below_sS i'
  rw [Scheme.rowAt_of_mem hmem, Scheme.appendFullCells_row_natAdd, SLvl.Φs_natAdd]

/-- A cell of the layer below a pair off the ground set is an old amalgam cell below the pair. -/
theorem SLvl.Good.exists_embed_of_mem_below_sS (hN : N.Good A) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {z : Fin (N.S.card + C.card)} (hz : z ∈ (N.sS C).toCellScheme.below X) :
    ∃ d, z = Fin.castAdd C.card (N.embed d) ∧ d ∈ I.amalgam.toCellScheme.below X := by
  have hXu : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ X := fun h ↦ hX (univ_subset_iff.mp h.1)
  have hlt := Scheme.lt_card_of_mem_below hXu hz
  set e : Fin N.S.card := ⟨z, hlt⟩
  have hze : z = Fin.castAdd C.card e := Fin.ext rfl
  rw [hze, CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hz
  obtain ⟨d, hd⟩ := hN.mem_range e fun he ↦ hX (univ_subset_iff.mp (he ▸ hz.1))
  refine ⟨d, hze.trans (by rw [hd]), ?_⟩
  rw [CellScheme.mem_below, ← hN.gradedIndex_sS_embed (C := C) d,
    Scheme.appendFullCellsScheme_gradedIndex_castAdd, hd]
  exact hz

/-- **Lawfulness below a pair off the ground set** in the layer is lawfulness on the amalgam. -/
theorem SLvl.Good.isLawfulBelow_sS_iff (hN : N.Good A) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {w : Fin (N.S.card + C.card) → Label.{u}} :
    (N.sS C).rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (Fin.castAdd C.card (N.embed d))) :=
  (Scheme.isLawfulBelow_appendFullCells_iff fun h ↦ hX (univ_subset_iff.mp h.1)).trans
    (hN.isLawfulBelow_old_iff (w := fun e ↦ w (Fin.castAdd C.card e)) hX)

/-! ### A realized state is active -/

/-- **A state realized above the donor maximum is active.**  Let `P ∈ C` be in the code grid and
active below the cap `h` (donor maximum `D` below its cutoff and below `h`), its proper donor
fields amalgam cells of grade at most `g + 1` labelled below `h`.  Let `w` be lawful below
`(univ, g + 1)` in the layer and agree with the row of `P` capped at `h` there.  Then the state of
every new cell `v` with `D < w v` is active: its donor maximum lies below its cutoff. -/
theorem SLvl.Good.donorMax_lt_of_isLawfulBelow_sS (hN : N.Good A)
    {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {P : CProf I} (hPC : P ∈ C)
    (hPB : ∀ f, P f ∈ codeGrid (g + 1) (bound I)) {h : Label.{u}}
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h)
    {w : Fin (N.S.card + C.card) → Label.{u}}
    (hw : (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ w z)
    (hwP : ∀ z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1),
      min (w z) h = min (N.Φs C P z) h)
    (i : Fin C.card) (hi : donorMax Nf P < w (Fin.natAdd N.S.card i)) :
    donorMax Nf (C.equivFin.symm i).1 < (C.equivFin.symm i).1 (Sum.inr ()) := by
  classical
  set Q : CProf I := (C.equivFin.symm i).1 with hQ
  set v : Fin (N.S.card + C.card) := Fin.natAdd N.S.card i with hv
  set D := donorMax Nf P with hD
  set G : Finset Label.{u} := grid (g + 1) (bound I) with hG
  have hvb : v ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) :=
    SLvl.natAdd_mem_below_sS i
  obtain ⟨gg, σ, hσ, hgv, hread⟩ := Scheme.exists_reading hw hvb
  have hgradev : (N.sS C).toCellScheme.grade v = g + 1 :=
    Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i
  have hbelowv {z : Fin (N.S.card + C.card)}
      (hz : z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      z ∈ (N.sS C).toCellScheme.below ((N.sS C).toCellScheme.gradedIndex v) := by
    rw [hv, Scheme.appendFullCellsScheme_gradedIndex_natAdd]; exact hz
  have hgz {z : Fin (N.S.card + C.card)}
      (hz : z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      w v ≤ gg ((N.sS C).toCellScheme.grade z) :=
    hgv.trans (hσ.antitone (hgradev ▸ hz.2))
  -- the cell of `P`, labelled above `D`
  obtain ⟨iP, hiP⟩ := exists_equivFin_eq hPC
  have hDcut : D < P (Sum.inr ()) := hact.trans_le (min_le_left _ _)
  have hDh : D < h := hact.trans_le (min_le_right _ _)
  have huP : D < w (Fin.natAdd N.S.card iP) := by
    have h1 := hwP _ (SLvl.natAdd_mem_below_sS iP)
    rw [SLvl.Φs_natAdd, hiP, agreementHeight_self (gridPoint_mem_grid le_rfl)
      (fun _ hx ↦ le_gridPoint_of_mem_grid hx)] at h1
    have h2 : D < min (gridPoint (g + 1) (bound I)) h :=
      lt_min (hDcut.trans_le (le_gridPoint_of_mem_codeGrid (hPB _))) hDh
    rw [← h1] at h2
    exact h2.trans_le (min_le_left _ _)
  -- the row of `v` reads the cell of `P` as the agreement height `κ` of `Q` and `P`
  set κ := agreementHeight G Q P with hκ
  have hσκ : D < σ κ := by
    have h1 := hread _ (hbelowv (SLvl.natAdd_mem_below_sS iP))
    rw [SLvl.rowAt_sS_natAdd_natAdd, hiP] at h1
    have h2 : D < min (w (Fin.natAdd N.S.card iP)) (w v) := lt_min huP hi
    rw [h1] at h2
    exact h2.trans_le (min_le_left _ _)
  -- the row of `v` reads the proper donor fields as `w` labels them, that is as `P`
  have hσN (f : Fin I.amalgam.card ⊕ Unit) (hf : f ∈ Nf) : σ (Q f) = P f := by
    obtain ⟨e, rfl, he, heh⟩ := hNf f hf
    have hzb := hN.embed_mem_below_sS (C := C) he
    have hwe : w (Fin.castAdd C.card (N.embed e)) = P (Sum.inl e) := by
      have h1 := hwP _ hzb
      rw [SLvl.Φs_castAdd, hN.literal] at h1
      exact Label.eq_of_min_eq_of_lt h1.symm heh
    have h1 := hread _ (hbelowv hzb)
    rw [hN.rowAt_sS_natAdd_embed i he, hwe] at h1
    exact Label.eq_of_min_eq_min_of_lt h1 ((le_donorMax hf).trans_lt hi) (hgz hzb)
  have hspec := (agreementHeight_spec (bot_mem_grid (g + 1) (bound I)) Q P).2
  -- the agreement height lies above `D`
  have hDκ : D < κ := by
    by_contra hκD
    rw [not_lt] at hκD
    have hσle : σ κ ≤ D := by
      rcases Nf.eq_empty_or_nonempty with hNe | hNe
      · have hD0 : D = ⊥ := by rw [hD, donorMax, hNe, Finset.sup_empty]
        rw [hD0] at hκD ⊢
        rw [le_bot_iff.mp hκD, hσ.map_bot]
      · obtain ⟨f, hf, hfD⟩ := Finset.exists_mem_eq_sup Nf hNe P
        have hκQ : κ ≤ Q f := by
          have h1 := hspec f
          rw [min_eq_right (hκD.trans hfD.le)] at h1
          rw [← h1]; exact min_le_left _ _
        calc σ κ ≤ σ (Q f) := hσ.monotone hκQ
          _ = P f := hσN f hf
          _ = D := hfD.symm
    exact absurd (hσκ.trans_le hσle) (lt_irrefl _)
  -- `Q` agrees with `P` on the proper donor fields and has its cutoff above `D`
  have hQN (f : Fin I.amalgam.card ⊕ Unit) (hf : f ∈ Nf) : Q f = P f := by
    exact Label.eq_of_min_eq_of_lt (hspec f).symm ((le_donorMax hf).trans_lt hDκ)
  have hDQ : donorMax Nf Q = D := donorMax_congr hQN
  rw [hDQ]
  have h1 := hspec (Sum.inr ())
  have h2 : D < min (P (Sum.inr ())) κ := lt_min hDcut hDκ
  rw [← h1] at h2
  exact h2.trans_le (min_le_left _ _)

/-! ### The contract fails at a rigid reading -/

/-- **No lawful labelling of the layer at a rigid reading.**  Let every state of `C` be LOW at
`K ≤ g + 1`, and `P ∈ C` in the code grid, active below the cap `h`, with its proper donor fields
amalgam cells of grade at most `g + 1` labelled below `h`, and `P d < h`.  Let every cell of
graded index `(univ.erase y, g + 1)` (there is one, `w₀`) read the donor top `t` as the
replacement at `g + 1` of its reading of `d`, and let `u` have grade `g + 1` and scope in
`univ.erase y`.  Then no labelling `w` lawful below `(univ, g + 1)` in the layer, agreeing with the
row of `P` capped at `h` there, labels the copy of `u` above `θ = visibilityReplace (g + 1) (g + 1)
(P d)` and above the donor maximum of `P`, and the owner and the lost top (of grade at most
`g + 1`) with a frontier above `θ`. -/
theorem SLvl.Good.not_lawful_sS_of_rigid {K : ℕ} {Nf : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}
    (hN : N.Good A) (hKj : K ≤ g + 1) {y : Fin (m + 2)} {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace (g + 1) (g + 1) (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T) (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    (hog : I.amalgam.toCellScheme.grade o ≤ g + 1) (hrg : I.amalgam.toCellScheme.grade r ≤ g + 1)
    (hClow : ∀ Q ∈ C, lowPred K Nf T o r Q)
    {P : CProf I} (hPC : P ∈ C) (hPB : ∀ f, P f ∈ codeGrid (g + 1) (bound I)) {h : Label.{u}}
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {w : Fin (N.S.card + C.card) → Label.{u}}
    (hw : (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ w z)
    (hwP : ∀ z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1),
      min (w z) h = min (N.Φs C P z) h)
    (hwu : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) <
      w (Fin.castAdd C.card (N.embed u)))
    (hwD : donorMax Nf P < w (Fin.castAdd C.card (N.embed u)))
    (hwfr : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) <
      min (w (Fin.castAdd C.card (N.embed o)))
        (visibilityReplace K K (w (Fin.castAdd C.card (N.embed r))))) :
    False := by
  classical
  set θ := visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) with hθ
  set W' : Prof I := fun e ↦ w (Fin.castAdd C.card (N.embed e)) with hW'
  -- the amalgam part is lawful below the coatom `univ.erase y`
  have hWy : I.amalgam.rows.IsLawfulBelow (univ.erase y, g + 1) (fun e ↦ W' e) :=
    (hN.isLawfulBelow_sS_iff (Seed.ne_univ_erase y)).mp
      (hw.mono (X := (univ.erase y, g + 1)) ⟨erase_subset _ _, le_rfl⟩)
  have hgw₀ : I.amalgam.toCellScheme.grade w₀ = g + 1 := congrArg Prod.snd hw₀
  -- it reads `d` as `P` does
  have hW'd : W' d = P (Sum.inl d) := by
    have hdg : I.amalgam.toCellScheme.grade d ≤ g + 1 :=
      (hrigid w₀ hw₀).2.1.2.trans hgw₀.le
    have h1 := hwP _ (hN.embed_mem_below_sS hdg)
    rw [SLvl.Φs_castAdd, hN.literal] at h1
    exact Label.eq_of_min_eq_of_lt h1.symm hd
  -- availability below the coatom `univ.erase y` and rigidity keep the donor top below `θ`
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hWy
  have hw₀b : w₀ ∈ I.amalgam.toCellScheme.below (univ.erase y, g + 1) := by
    rw [CellScheme.mem_below, hw₀]
  obtain ⟨w₁, hw₁, huw⟩ := havail u w₀ hw₀b
    (by rw [show I.amalgam.toCellScheme.scope w₀ = univ.erase y from congrArg Prod.fst hw₀]
        exact huy)
    (by rw [hug, hgw₀])
  have hw₁g : I.amalgam.toCellScheme.grade w₁ = g + 1 := congrArg Prod.snd (hw₁.trans hw₀)
  have hw₁b : w₁ ∈ I.amalgam.toCellScheme.below (univ.erase y, g + 1) := by
    rw [CellScheme.mem_below, hw₁, hw₀]
  obtain ⟨htw, hdw, hrow⟩ := hrigid w₁ (hw₁.trans hw₀)
  have hθw : θ < W' w₁ := hwu.trans_le huw
  have hdθ : P (Sum.inl d) ≤ θ := le_visibilityReplace (by omega) _
  have hrig := Scheme.min_le_visibilityReplace_of_rowAt_eq hWy hw₁b htw hdw
    (by rw [hw₁g]; exact hrow) (by rw [hW'd]; exact hdθ.trans_lt hθw)
  rw [hw₁g, hW'd] at hrig
  have hW't : W' t ≤ θ := by
    rcases le_total (W' t) (W' w₁) with hle | hle
    · rwa [min_eq_left hle] at hrig
    · rw [min_eq_right hle] at hrig; exact absurd hrig (_root_.not_le.mpr hθw)
  have htg : I.amalgam.toCellScheme.grade t ≤ g + 1 := htw.2.trans hw₁g.le
  -- availability on the layer puts a new cell `v` above the copy of `u`
  obtain ⟨iP, -⟩ := exists_equivFin_eq hPC
  obtain ⟨-, -, havail'⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨v, hv, hwv⟩ := havail' (Fin.castAdd C.card (N.embed u)) (Fin.natAdd N.S.card iP)
    (SLvl.natAdd_mem_below_sS iP)
    (by rw [Scheme.appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [Scheme.appendFullCellsScheme_grade_natAdd, Scheme.appendFullCellsScheme_grade_castAdd,
          hN.lowerEmb.grade_eq, hug])
  have hnew : ∀ v' : Fin (N.S.card + C.card), (N.sS C).toCellScheme.gradedIndex v' =
      ((univ : Finset (Fin (m + 2))), g + 1) → ∃ i, v' = Fin.natAdd N.S.card i := by
    intro v' hv'
    induction v' using Fin.addCases with
    | right i => exact ⟨i, rfl⟩
    | left e =>
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hv'
      rcases N.inv e with he | he
      · have h2 : N.S.toCellScheme.grade e = g + 1 := congrArg Prod.snd hv'
        omega
      · exact absurd (congrArg Prod.fst hv') he
  obtain ⟨i, rfl⟩ := hnew v (hv.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ iP))
  have hθv : θ < w (Fin.natAdd N.S.card i) := hwu.trans_le hwv
  -- its state is active, and LOW
  set Q : CProf I := (C.equivFin.symm i).1 with hQ
  have hQact : donorMax Nf Q < Q (Sum.inr ()) :=
    hN.donorMax_lt_of_isLawfulBelow_sS hPC hPB hNf hact hw hwP i (hwD.trans_le hwv)
  have hft := hClow Q (C.equivFin.symm i).2 hQact (Sum.inl t) ht
  -- the witness of `v` reads the donor top below `θ` and the owner above
  obtain ⟨gg, σ, hσ, hgv, hread⟩ := Scheme.exists_reading hw (SLvl.natAdd_mem_below_sS i)
  have hgradev : (N.sS C).toCellScheme.grade (Fin.natAdd N.S.card i) = g + 1 :=
    Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i
  have hreadE {e : Fin I.amalgam.card} (he : I.amalgam.toCellScheme.grade e ≤ g + 1) :
      min (W' e) (w (Fin.natAdd N.S.card i)) = min (σ (Q (Sum.inl e)))
        (gg ((N.sS C).toCellScheme.grade (Fin.castAdd C.card (N.embed e)))) ∧
        w (Fin.natAdd N.S.card i) ≤
          gg ((N.sS C).toCellScheme.grade (Fin.castAdd C.card (N.embed e))) := by
    have hzb := hN.embed_mem_below_sS (C := C) he
    refine ⟨?_, hgv.trans (hσ.antitone (hgradev ▸ hzb.2))⟩
    have h1 := hread _ (by
      rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]; exact hzb)
    rw [hN.rowAt_sS_natAdd_embed i he] at h1
    exact h1
  have hσt : σ (Q (Sum.inl t)) ≤ θ := by
    obtain ⟨h1, h2⟩ := hreadE htg
    rw [Label.eq_of_min_eq_min_of_lt h1 (hW't.trans_lt hθv) h2]
    exact hW't
  have hσo : θ < σ (Q (Sum.inl o)) := by
    obtain ⟨h1, -⟩ := hreadE hog
    have h2 : θ < min (W' o) (w (Fin.natAdd N.S.card i)) :=
      lt_min (hwfr.trans_le (min_le_left _ _)) hθv
    rw [h1] at h2
    exact h2.trans_le (min_le_left _ _)
  have hσr : min (W' r) (w (Fin.natAdd N.S.card i)) ≤ σ (Q (Sum.inl r)) := by
    obtain ⟨h1, -⟩ := hreadE hrg
    rw [h1]
    exact min_le_left _ _
  -- the LOW clause of `Q`, read by the witness, puts the lost top below `θ`
  have hfrQ : σ (min (Q (Sum.inl o)) (visibilityReplace K K (Q (Sum.inl r)))) ≤ θ :=
    (hσ.monotone ((le_max_right _ _).trans hft)).trans hσt
  rw [hσ.monotone.map_min] at hfrQ
  have hvr : σ (visibilityReplace K K (Q (Sum.inl r))) ≤ θ := by
    rcases min_le_iff.mp hfrQ with h1 | h1
    · exact absurd (hσo.trans_le h1) (lt_irrefl _)
    · exact h1
  have hσr' : σ (Q (Sum.inl r)) ≤ θ :=
    (hσ.monotone (le_visibilityReplace (by omega) _)).trans hvr
  have hW'r : W' r ≤ θ := by
    rcases min_le_iff.mp (hσr.trans hσr') with h1 | h1
    · exact h1
    · exact absurd (hθv.trans_le h1) (lt_irrefl _)
  -- the frontier of the prescription lies below `θ`, a contradiction
  have hθK : IsSelfVisible K θ :=
    (show IsSelfVisible (g + 1) θ from visibilityReplace_self_visibilityReplace le_rfl _).mono hKj
  have h3 : visibilityReplace K K (W' r) ≤ θ := by
    have := monotone_visibilityReplace (k := K) le_rfl hW'r
    rwa [hθK] at this
  exact absurd (hwfr.trans_le ((min_le_right _ _).trans h3)) (lt_irrefl _)

/-- **The literal extension of an amalgam prescription to the layer**: `a` at the copies of the
amalgam cells, the row of `P` elsewhere; it is lawful below a coatom when `a` is, and agrees with
the row of `P` capped at `h` there when `a` agrees with `P` capped at `h`. -/
theorem SLvl.Good.exists_prescription_sS (hN : N.Good A) {x : Fin (m + 2)} (P : CProf I)
    {h : Label.{u}} {a : Prof I}
    (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      min (a e) h = min (P (Sum.inl e)) h) :
    ∃ p : Fin (N.S.card + C.card) → Label.{u},
      (∀ e, p (Fin.castAdd C.card (N.embed e)) = a e) ∧
      (N.sS C).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ p z) ∧
      ∀ z ∈ (N.sS C).toCellScheme.below (univ.erase x, g + 1),
        min (N.Φs C P z) h = min (p z) h := by
  classical
  have hinj : Function.Injective fun e : Fin I.amalgam.card ↦ Fin.castAdd C.card (N.embed e) :=
    (Fin.castAdd_injective _ _).comp N.embed.injective
  have hpe (e : Fin I.amalgam.card) :
      Function.extend (fun e ↦ Fin.castAdd C.card (N.embed e)) a (N.Φs C P)
        (Fin.castAdd C.card (N.embed e)) = a e :=
    hinj.extend_apply a _ e
  have hXne : (univ.erase x : Finset (Fin (m + 2))) ≠ univ := Seed.ne_univ_erase x
  refine ⟨Function.extend (fun e ↦ Fin.castAdd C.card (N.embed e)) a (N.Φs C P), hpe,
    (hN.isLawfulBelow_sS_iff hXne).mpr (by simpa only [hpe] using ha), fun z hz ↦ ?_⟩
  obtain ⟨d, rfl, hd⟩ := hN.exists_embed_of_mem_below_sS hXne hz
  rw [SLvl.Φs_castAdd, hN.literal, hpe]
  exact (haP d hd).symm

/-- **The layer of the LOW catalogue does not lift capped from the coatom at a rigid reading.**
In the configuration of `ProfileTower.not_stateCatStep_of_rigid` at the grade `g + 1`, with the
state `P` a member of the catalogue `sCat I (g + 1) (lowPred K Nf T o r)` over a good state level,
its proper donor fields amalgam cells of grade at most `g + 1`, and the prescription `a` above the
donor maximum of `P` at `u`, the layer does not lift capped from `(univ.erase x, g + 1)` to
`(univ, g + 1)`: the lift of `a` in the cap ball of the row of `P` at `h` would be a labelling
excluded by `ProfileTower.SLvl.Good.not_lawful_sS_of_rigid`. -/
theorem SLvl.Good.not_cappedLift_sS_of_rigid {K : ℕ} {Nf : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}
    (hN : N.Good (lowPred K Nf T o r)) (hKj : K ≤ g + 1) {x y : Fin (m + 2)}
    {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace (g + 1) (g + 1) (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    {P : CProf I} (hP : P ∈ sCat I (g + 1) (lowPred K Nf T o r)) {h : Label.{u}}
    (hh : IsSelfVisible (g + 1) h)
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hau : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) < a u)
    (hDu : donorMax Nf P < a u)
    (hfr : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) <
      min (a o) (visibilityReplace K K (a r))) :
    ¬ (N.sS (sCat I (g + 1) (lowPred K Nf T o r))).rows.CappedLift
      (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  intro hlift
  set C := sCat I (g + 1) (lowPred K Nf T o r) with hC
  obtain ⟨hPB, hPcut, -, hPA⟩ := mem_sCat.mp hP
  obtain ⟨pf, hpe, hp, hag⟩ := hN.exists_prescription_sS (C := C) P ha haP
  obtain ⟨r', hr', hr'q, hr'p⟩ := (Rows.cappedLift_iff_forall_exists _).mp hlift h hh
    (fun z ↦ pf z) (fun z ↦ N.Φs C P z) hp (hN.isLawfulBelow_Φs hP hPB hPcut hPA)
    fun e ↦ hag e.1 e.2
  have hwa (e : Fin I.amalgam.card)
      (he : e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
      Rows.extendBot ((univ : Finset (Fin (m + 2))), g + 1) r'
        (Fin.castAdd C.card (N.embed e)) = a e := by
    have hzb : Fin.castAdd C.card (N.embed e) ∈
        (N.sS C).toCellScheme.below (univ.erase x, g + 1) := by
      rw [CellScheme.mem_below, hN.gradedIndex_sS_embed]; exact he
    rw [Rows.extendBot_of_mem r' ((N.sS C).toCellScheme.below_mono
      (show ((univ.erase x, g + 1) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, g + 1) from
        ⟨erase_subset _ _, le_rfl⟩) hzb), ← hpe e]
    exact hr'p ⟨_, hzb⟩
  refine hN.not_lawful_sS_of_rigid hKj hw₀ hrigid ht huy hug ho.2 hr.2
    (fun Q hQ ↦ (mem_sCat.mp hQ).2.2.2) hP hPB hNf hact hd
    (Rows.isLawfulBelow_extendBot.mpr hr') (fun z hz ↦ ?_) ?_ ?_ ?_
  · rw [Rows.extendBot_of_mem r' hz]
    exact hr'q ⟨z, hz⟩
  · rw [hwa u hux]; exact hau
  · rw [hwa u hux]; exact hDu
  · rw [hwa o ho, hwa r hr]; exact hfr

/-- **The layer of the LOW catalogue has no owner-capped lift at the cap at a rigid reading**, for
an owner `o'` of the prescription above the cap: in the configuration of
`ProfileTower.SLvl.Good.not_cappedLift_sS_of_rigid` with `h < a u`, the owner-capped lift of `a`
at the label of `o'` (`CellScheme.Rows.HasOwnerCappedLifts`) would be a labelling excluded by
`ProfileTower.SLvl.Good.not_lawful_sS_of_rigid`, since capping at the owner label keeps the labels
at `u`, `o` and `r` above `θ`. -/
theorem SLvl.Good.not_hasOwnerCappedLifts_sS_of_rigid {K : ℕ}
    {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
    {o r : Fin I.amalgam.card} (hN : N.Good (lowPred K Nf T o r)) (hKj : K ≤ g + 1)
    {x y : Fin (m + 2)} {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace (g + 1) (g + 1) (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    {P : CProf I} (hP : P ∈ sCat I (g + 1) (lowPred K Nf T o r)) {h : Label.{u}}
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hau : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) < a u)
    (hDu : donorMax Nf P < a u) (hhu : h < a u)
    (hfr : visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) <
      min (a o) (visibilityReplace K K (a r)))
    {o' : Fin I.amalgam.card}
    (ho' : I.amalgam.toCellScheme.gradedIndex o' = (univ.erase x, g + 1))
    (ho'max : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      I.amalgam.toCellScheme.grade e = g + 1 → a e ≤ a o') :
    ¬ (N.sS (sCat I (g + 1) (lowPred K Nf T o r))).rows.HasOwnerCappedLifts
      (erase_subset x univ) g h := by
  classical
  intro hown
  set C := sCat I (g + 1) (lowPred K Nf T o r) with hC
  obtain ⟨hPB, hPcut, -, hPA⟩ := mem_sCat.mp hP
  have hXne : (univ.erase x : Finset (Fin (m + 2))) ≠ univ := Seed.ne_univ_erase x
  obtain ⟨pf, hpe, hp, hag⟩ := hN.exists_prescription_sS (C := C) P ha haP
  have hzb {e : Fin I.amalgam.card} (he : e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
      Fin.castAdd C.card (N.embed e) ∈ (N.sS C).toCellScheme.below (univ.erase x, g + 1) := by
    rw [CellScheme.mem_below, hN.gradedIndex_sS_embed]; exact he
  have hua : a u ≤ a o' := ho'max u hux hug
  obtain ⟨w', hw', hw'p, hw'q⟩ := hown (fun z ↦ pf z) (fun z ↦ N.Φs C P z) hp
    (hN.isLawfulBelow_Φs hP hPB hPcut hPA) (fun e ↦ hag e.1 e.2)
    ⟨_, hzb (show o' ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1) from ho'.le)⟩
    (by rw [hN.gradedIndex_sS_embed]; exact ho')
    (fun e he ↦ by
      obtain ⟨d', hde, hd'⟩ := hN.exists_embed_of_mem_below_sS hXne e.2
      change pf e.1 ≤ pf (Fin.castAdd C.card (N.embed o'))
      have hg : I.amalgam.toCellScheme.grade d' = g + 1 := by
        have h1 : (N.sS C).toCellScheme.grade e.1 = g + 1 := he
        rw [hde] at h1
        rwa [show (N.sS C).toCellScheme.grade (Fin.castAdd C.card (N.embed d')) =
          I.amalgam.toCellScheme.grade d' from congrArg Prod.snd (hN.gradedIndex_sS_embed d')]
          at h1
      rw [hde, hpe, hpe]
      exact ho'max d' hd' hg)
    (by change h < pf (Fin.castAdd C.card (N.embed o')); rw [hpe]; exact hhu.trans_le hua)
  have hwa (e : Fin I.amalgam.card)
      (he : e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
      Rows.extendBot ((univ : Finset (Fin (m + 2))), g + 1) w'
        (Fin.castAdd C.card (N.embed e)) = min (a e) (a o') := by
    rw [Rows.extendBot_of_mem w' ((N.sS C).toCellScheme.below_mono
      (show ((univ.erase x, g + 1) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, g + 1) from
        ⟨erase_subset _ _, le_rfl⟩) (hzb he))]
    refine (hw'p ⟨_, hzb he⟩).trans ?_
    rw [hpe, hpe]
  set θ := visibilityReplace (g + 1) (g + 1) (P (Sum.inl d)) with hθ
  have hθo' : θ < a o' := hau.trans_le hua
  refine hN.not_lawful_sS_of_rigid hKj hw₀ hrigid ht huy hug ho.2 hr.2
    (fun Q hQ ↦ (mem_sCat.mp hQ).2.2.2) hP hPB hNf hact hd
    (Rows.isLawfulBelow_extendBot.mpr hw') (fun z hz ↦ ?_) ?_ ?_ ?_
  · rw [Rows.extendBot_of_mem w' hz]
    exact hw'q ⟨z, hz⟩
  · rw [hwa u hux, min_eq_left hua]; exact hau
  · rw [hwa u hux, min_eq_left hua]; exact hDu
  · rw [hwa o ho, hwa r hr, visibilityReplace_min le_rfl]
    have h1 : θ < a o := hfr.trans_le (min_le_left _ _)
    have h2 : θ < visibilityReplace K K (a r) := hfr.trans_le (min_le_right _ _)
    have h3 : θ < visibilityReplace K K (a o') :=
      hθo'.trans_le (le_visibilityReplace (by omega) _)
    exact lt_min (lt_min h1 hθo') (lt_min h2 h3)

/-! ### The lifts of the state tower fail at a rigid reading -/

/-- **The lifts of the state tower fail at a rigid reading.**  Over a good level `L` at the grade
`g`, for the LOW clause at `K ≤ g + 1` with designated fields of grade at most `K`, if at some
layer `J < J₀` (with `g + J ≤ m`) a member `P` of the catalogue at `g + J + 1` meets the rigid
configuration of `ProfileTower.SLvl.Good.not_cappedLift_sS_of_rigid` from a point `x`, then the
state tower does not lift (`ProfileTower.STowerLifts`): the lifts would make the level below that
layer good (`ProfileTower.sTower_good`), and its layer does not lift capped from `x`. -/
theorem not_sTowerLifts_of_rigid {L : Lvl I g} (hL : L.Good) {K : ℕ}
    {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
    {o r : Fin I.amalgam.card} (hF : FieldsLE K Nf T o) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hKg : K ≤ g + 1) {J₀ J : ℕ} (hJ : J < J₀) (hJm : g + J ≤ m)
    {x y : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {t d u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + J + 1))
    (hrigid : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + J + 1) →
      t ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w t = visibilityReplace (g + J + 1) (g + J + 1) (I.amalgam.rowAt w d))
    (ht : Sum.inl t ∈ T)
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + J + 1)
    (ho : o ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    (hr : r ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    {P : CProf I} (hP : P ∈ sCat I (g + J + 1) (lowPred K Nf T o r)) {h : Label.{u}}
    (hh : IsSelfVisible (g + J + 1) h) (hNh : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h) (hd : P (Sum.inl d) < h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + J + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hau : visibilityReplace (g + J + 1) (g + J + 1) (P (Sum.inl d)) < a u)
    (hDu : donorMax Nf P < a u)
    (hfr : visibilityReplace (g + J + 1) (g + J + 1) (P (Sum.inl d)) <
      min (a o) (visibilityReplace K K (a r))) :
    ¬ STowerLifts L (lowPred K Nf T o r) J₀ := by
  intro hlift
  have hN := sTower_good hL (fun W ↦ lowPred_withCut_bot W)
    (fun j hj P hP ↦ lowPred_scode hF hrK (hKg.trans hj) hP) hlift J hJ.le hJm
  refine hN.not_cappedLift_sS_of_rigid (by omega) hw₀ hrigid ht hux huy hug ho hr hP hh
    (fun f hf ↦ ?_) hact hd ha haP hau hDu hfr (hlift J hJ x hx)
  obtain ⟨e, rfl, he⟩ := hNh f hf
  obtain ⟨e', he', hge'⟩ := hF.1 _ hf
  cases he'
  exact ⟨e, rfl, by omega, he⟩

/-! ### The contract fails at a held frontier -/

/-- **A new cell above a cell of grade `g + 1`, with an active state.**  Under the hypotheses of
`ProfileTower.SLvl.Good.donorMax_lt_of_isLawfulBelow_sS`, a cell `z` of grade `g + 1` below
`(univ, g + 1)` labelled above the donor maximum of `P` lies below a new cell `v` in the labels of
`w` (availability), and the state of `v` is active. -/
theorem SLvl.Good.exists_active_above (hN : N.Good A) {Nf : Finset (Fin I.amalgam.card ⊕ Unit)}
    {P : CProf I} (hPC : P ∈ C) (hPB : ∀ f, P f ∈ codeGrid (g + 1) (bound I)) {h : Label.{u}}
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h)
    {w : Fin (N.S.card + C.card) → Label.{u}}
    (hw : (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ w z)
    (hwP : ∀ z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1),
      min (w z) h = min (N.Φs C P z) h)
    {z : Fin (N.S.card + C.card)}
    (hzg : (N.sS C).toCellScheme.grade z = g + 1) (hzD : donorMax Nf P < w z) :
    ∃ i, w z ≤ w (Fin.natAdd N.S.card i) ∧
      donorMax Nf (C.equivFin.symm i).1 < (C.equivFin.symm i).1 (Sum.inr ()) := by
  obtain ⟨iP, -⟩ := exists_equivFin_eq hPC
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨v, hv, hwv⟩ := havail z (Fin.natAdd N.S.card iP) (SLvl.natAdd_mem_below_sS iP)
    (by rw [Scheme.appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [Scheme.appendFullCellsScheme_grade_natAdd]; exact hzg)
  have hnew : ∀ v' : Fin (N.S.card + C.card), (N.sS C).toCellScheme.gradedIndex v' =
      ((univ : Finset (Fin (m + 2))), g + 1) → ∃ i, v' = Fin.natAdd N.S.card i := by
    intro v' hv'
    induction v' using Fin.addCases with
    | right i => exact ⟨i, rfl⟩
    | left e =>
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hv'
      rcases N.inv e with he | he
      · have h2 : N.S.toCellScheme.grade e = g + 1 := congrArg Prod.snd hv'
        omega
      · exact absurd (congrArg Prod.fst hv') he
  obtain ⟨i, rfl⟩ := hnew v (hv.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ iP))
  exact ⟨i, hwv, hN.donorMax_lt_of_isLawfulBelow_sS hPC hPB hNf hact hw hwP i
    (hzD.trans_le hwv)⟩

/-- **The reading at a new cell of the amalgam cells**: a witness `(gg, σ)` with
`min (w e) (w v) = min (σ (Q e)) (gg (grade e))` at every amalgam cell `e` of grade at most
`g + 1`, `Q` the state of `v`, and `w v ≤ gg (g + 1)`. -/
theorem SLvl.Good.exists_reading_sS (hN : N.Good A) {w : Fin (N.S.card + C.card) → Label.{u}}
    (hw : (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ w z)
    (i : Fin C.card) :
    ∃ gg σ, IsWitness gg σ ∧ w (Fin.natAdd N.S.card i) ≤ gg (g + 1) ∧
      ∀ e : Fin I.amalgam.card, I.amalgam.toCellScheme.grade e ≤ g + 1 →
        min (w (Fin.castAdd C.card (N.embed e))) (w (Fin.natAdd N.S.card i)) =
          min (σ ((C.equivFin.symm i).1 (Sum.inl e))) (gg (I.amalgam.toCellScheme.grade e)) := by
  obtain ⟨gg, σ, hσ, hgv, hread⟩ := Scheme.exists_reading hw (SLvl.natAdd_mem_below_sS i)
  refine ⟨gg, σ, hσ, by rwa [Scheme.appendFullCellsScheme_grade_natAdd] at hgv, fun e he ↦ ?_⟩
  have h1 := hread _ (by
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]; exact hN.embed_mem_below_sS he)
  rwa [hN.rowAt_sS_natAdd_embed i he, show (N.sS C).toCellScheme.grade
    (Fin.castAdd C.card (N.embed e)) = I.amalgam.toCellScheme.grade e from
    congrArg Prod.snd (hN.gradedIndex_sS_embed e)] at h1

/-- **No lawful labelling of the layer at a held frontier.**  Let every state of `C` be LOW at
`K ≤ g + 1`, and `P ∈ C` in the code grid, active below the cap `h`, with its proper donor fields
amalgam cells of grade at most `g + 1` labelled below `h`.  Let every cell of graded index
`(univ.erase y, g + 1)` (there is one, `w₀`) read the owner `o` at least as `d₁` and the lost top
`r` at least as `d₂`, and let `u` have grade `g + 1` and scope in `univ.erase y`.  Then no
labelling `w` lawful below `(univ, g + 1)` in the layer, agreeing with the row of `P` capped at `h`
there, labels the copy of `u` above `d₁`, `d₂` and the donor maximum of `P`, and the donor top `t`
(of grade at most `g + 1`) below `min (w d₁) (visibilityReplace K K (w d₂))`. -/
theorem SLvl.Good.not_lawful_sS_of_held {K : ℕ} {Nf : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}
    (hN : N.Good A) (hKj : K ≤ g + 1) {y : Fin (m + 2)} {t d₁ d₂ u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hheld : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      o ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      r ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₁ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₂ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w d₁ ≤ I.amalgam.rowAt w o ∧ I.amalgam.rowAt w d₂ ≤ I.amalgam.rowAt w r)
    (ht : Sum.inl t ∈ T) (htg : I.amalgam.toCellScheme.grade t ≤ g + 1)
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    (hClow : ∀ Q ∈ C, lowPred K Nf T o r Q)
    {P : CProf I} (hPC : P ∈ C) (hPB : ∀ f, P f ∈ codeGrid (g + 1) (bound I)) {h : Label.{u}}
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h)
    {w : Fin (N.S.card + C.card) → Label.{u}}
    (hw : (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ w z)
    (hwP : ∀ z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1),
      min (w z) h = min (N.Φs C P z) h)
    (hu₁ : w (Fin.castAdd C.card (N.embed d₁)) < w (Fin.castAdd C.card (N.embed u)))
    (hu₂ : w (Fin.castAdd C.card (N.embed d₂)) < w (Fin.castAdd C.card (N.embed u)))
    (hwD : donorMax Nf P < w (Fin.castAdd C.card (N.embed u)))
    (hwt : w (Fin.castAdd C.card (N.embed t)) < min (w (Fin.castAdd C.card (N.embed d₁)))
      (visibilityReplace K K (w (Fin.castAdd C.card (N.embed d₂))))) :
    False := by
  classical
  set W' : Prof I := fun e ↦ w (Fin.castAdd C.card (N.embed e)) with hW'
  have hWy : I.amalgam.rows.IsLawfulBelow (univ.erase y, g + 1) (fun e ↦ W' e) :=
    (hN.isLawfulBelow_sS_iff (Seed.ne_univ_erase y)).mp
      (hw.mono (X := (univ.erase y, g + 1)) ⟨erase_subset _ _, le_rfl⟩)
  have hgw₀ : I.amalgam.toCellScheme.grade w₀ = g + 1 := congrArg Prod.snd hw₀
  -- availability below the coatom `univ.erase y`: the owner and the lost top are held
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hWy
  have hw₀b : w₀ ∈ I.amalgam.toCellScheme.below (univ.erase y, g + 1) := by
    rw [CellScheme.mem_below, hw₀]
  obtain ⟨w₁, hw₁, huw⟩ := havail u w₀ hw₀b
    (by rw [show I.amalgam.toCellScheme.scope w₀ = univ.erase y from congrArg Prod.fst hw₀]
        exact huy)
    (by rw [hug, hgw₀])
  have hw₁g : I.amalgam.toCellScheme.grade w₁ = g + 1 := congrArg Prod.snd (hw₁.trans hw₀)
  have hw₁b : w₁ ∈ I.amalgam.toCellScheme.below (univ.erase y, g + 1) := by
    rw [CellScheme.mem_below, hw₁, hw₀]
  obtain ⟨how, hrw, hd₁w, hd₂w, hrow₁, hrow₂⟩ := hheld w₁ (hw₁.trans hw₀)
  have hWo : W' d₁ ≤ W' o :=
    Scheme.le_of_rowAt_le_of_lt hWy hw₁b hd₁w how hrow₁ (hu₁.trans_le huw)
  have hWr : W' d₂ ≤ W' r :=
    Scheme.le_of_rowAt_le_of_lt hWy hw₁b hd₂w hrw hrow₂ (hu₂.trans_le huw)
  have hog : I.amalgam.toCellScheme.grade o ≤ g + 1 := how.2.trans hw₁g.le
  have hrg : I.amalgam.toCellScheme.grade r ≤ g + 1 := hrw.2.trans hw₁g.le
  -- a new cell above the copy of `u`, with an active and LOW state
  obtain ⟨i, hwv, hQact⟩ := hN.exists_active_above hPC hPB hNf hact hw hwP
    (z := Fin.castAdd C.card (N.embed u))
    (by rw [Scheme.appendFullCellsScheme_grade_castAdd, hN.lowerEmb.grade_eq, hug]) hwD
  set Q : CProf I := (C.equivFin.symm i).1 with hQ
  have hft := hClow Q (C.equivFin.symm i).2 hQact (Sum.inl t) ht
  obtain ⟨gg, σ, hσ, hgv, hread⟩ := hN.exists_reading_sS hw i
  have hgle {e : Fin I.amalgam.card} (he : I.amalgam.toCellScheme.grade e ≤ g + 1) :
      w (Fin.natAdd N.S.card i) ≤ gg (I.amalgam.toCellScheme.grade e) :=
    hgv.trans (hσ.antitone he)
  have htv : W' t < w (Fin.natAdd N.S.card i) :=
    (hwt.trans_le (min_le_left _ _)).trans (hu₁.trans_le hwv)
  have hσt : σ (Q (Sum.inl t)) = W' t :=
    Label.eq_of_min_eq_min_of_lt (hread t htg) htv (hgle htg)
  have hd₁v : W' d₁ < w (Fin.natAdd N.S.card i) := hu₁.trans_le hwv
  have hd₂v : W' d₂ < w (Fin.natAdd N.S.card i) := hu₂.trans_le hwv
  have hσo : W' d₁ ≤ σ (Q (Sum.inl o)) := by
    have h1 := hread o hog
    have h2 : W' d₁ ≤ min (W' o) (w (Fin.natAdd N.S.card i)) := le_min hWo hd₁v.le
    rw [h1] at h2
    exact h2.trans (min_le_left _ _)
  have hσr : W' d₂ ≤ σ (Q (Sum.inl r)) := by
    have h1 := hread r hrg
    have h2 : W' d₂ ≤ min (W' r) (w (Fin.natAdd N.S.card i)) := le_min hWr hd₂v.le
    rw [h1] at h2
    exact h2.trans (min_le_left _ _)
  -- the LOW clause of `Q`, read by the witness
  have hfrQ : σ (min (Q (Sum.inl o)) (visibilityReplace K K (Q (Sum.inl r)))) ≤ W' t :=
    (hσ.monotone ((le_max_right _ _).trans hft)).trans hσt.le
  rw [hσ.monotone.map_min] at hfrQ
  have hvr : σ (visibilityReplace K K (Q (Sum.inl r))) ≤ W' t := by
    rcases min_le_iff.mp hfrQ with h1 | h1
    · exact absurd ((hwt.trans_le (min_le_left _ _)).trans_le (hσo.trans h1)) (lt_irrefl _)
    · exact h1
  have hcap : σ (Q (Sum.inl r)) ≤ gg K :=
    (hσ.monotone (le_visibilityReplace (by omega) _)).trans
      (hvr.trans (htv.le.trans (hgv.trans (hσ.antitone hKj))))
  rw [hσ.visibilityReplace_comm _ K hcap K le_rfl] at hvr
  have h3 : visibilityReplace K K (W' d₂) ≤ W' t :=
    (monotone_visibilityReplace le_rfl hσr).trans hvr
  exact absurd (hwt.trans_le ((min_le_right _ _).trans h3)) (lt_irrefl _)

/-- **The layer of the LOW catalogue does not lift capped from the coatom at a held frontier.**
In the configuration of `ProfileTower.not_stateCatStep_of_held` at the grade `g + 1`, with the
state `P` a member of the catalogue `sCat I (g + 1) (lowPred K Nf T o r)` over a good state level,
its proper donor fields amalgam cells of grade at most `g + 1`, and the prescription `a` above the
donor maximum of `P` at `u`, the layer does not lift capped from `(univ.erase x, g + 1)` to
`(univ, g + 1)`: the lift of `a` in the cap ball of the row of `P` at `h` would be a labelling
excluded by `ProfileTower.SLvl.Good.not_lawful_sS_of_held`. -/
theorem SLvl.Good.not_cappedLift_sS_of_held {K : ℕ} {Nf : Finset (Fin I.amalgam.card ⊕ Unit)}
    {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}
    (hN : N.Good (lowPred K Nf T o r)) (hKj : K ≤ g + 1) {x y : Fin (m + 2)}
    {t d₁ d₂ u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + 1))
    (hheld : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + 1) →
      o ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      r ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₁ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₂ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w d₁ ≤ I.amalgam.rowAt w o ∧ I.amalgam.rowAt w d₂ ≤ I.amalgam.rowAt w r)
    (ht : Sum.inl t ∈ T) (htx : t ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + 1)
    {P : CProf I} (hP : P ∈ sCat I (g + 1) (lowPred K Nf T o r)) {h : Label.{u}}
    (hh : IsSelfVisible (g + 1) h)
    (hNf : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ I.amalgam.toCellScheme.grade e ≤ g + 1 ∧
      P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hu₁ : a d₁ < a u) (hu₂ : a d₂ < a u) (hDu : donorMax Nf P < a u)
    (hat : a t < min (a d₁) (visibilityReplace K K (a d₂))) :
    ¬ (N.sS (sCat I (g + 1) (lowPred K Nf T o r))).rows.CappedLift
      (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  intro hlift
  set C := sCat I (g + 1) (lowPred K Nf T o r) with hC
  obtain ⟨hPB, hPcut, -, hPA⟩ := mem_sCat.mp hP
  obtain ⟨pf, hpe, hp, hag⟩ := hN.exists_prescription_sS (C := C) P ha haP
  obtain ⟨r', hr', hr'q, hr'p⟩ := (Rows.cappedLift_iff_forall_exists _).mp hlift h hh
    (fun z ↦ pf z) (fun z ↦ N.Φs C P z) hp (hN.isLawfulBelow_Φs hP hPB hPcut hPA)
    fun e ↦ hag e.1 e.2
  have hwa (e : Fin I.amalgam.card)
      (he : e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1)) :
      Rows.extendBot ((univ : Finset (Fin (m + 2))), g + 1) r'
        (Fin.castAdd C.card (N.embed e)) = a e := by
    have hzb : Fin.castAdd C.card (N.embed e) ∈
        (N.sS C).toCellScheme.below (univ.erase x, g + 1) := by
      rw [CellScheme.mem_below, hN.gradedIndex_sS_embed]; exact he
    rw [Rows.extendBot_of_mem r' ((N.sS C).toCellScheme.below_mono
      (show ((univ.erase x, g + 1) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, g + 1) from
        ⟨erase_subset _ _, le_rfl⟩) hzb), ← hpe e]
    exact hr'p ⟨_, hzb⟩
  refine hN.not_lawful_sS_of_held hKj hw₀ hheld ht htx.2 huy hug
    (fun Q hQ ↦ (mem_sCat.mp hQ).2.2.2) hP hPB hNf hact
    (Rows.isLawfulBelow_extendBot.mpr hr') (fun z hz ↦ ?_) ?_ ?_ ?_ ?_
  · rw [Rows.extendBot_of_mem r' hz]
    exact hr'q ⟨z, hz⟩
  · rw [hwa u hux, hwa d₁ hd₁]; exact hu₁
  · rw [hwa u hux, hwa d₂ hd₂]; exact hu₂
  · rw [hwa u hux]; exact hDu
  · rw [hwa t htx, hwa d₁ hd₁, hwa d₂ hd₂]; exact hat

/-! ### The lifts of the state tower fail at a layer that does not lift -/

/-- **The lifts of the state tower fail at a layer that does not lift when its level is good.**
Over a good level `L` at the grade `g`, for the LOW clause at `K ≤ g + 1` with designated fields of
grade at most `K`: if for some `J < J₀` (with `g + J ≤ m`) and `x ∈ Pts` the layer of the level
`J` does not lift capped from `univ.erase x` whenever that level is good, the state tower does not
lift: its lifts would make the level good (`ProfileTower.sTower_good`). -/
theorem not_sTowerLifts_of_layer {L : Lvl I g} (hL : L.Good) {K : ℕ}
    {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
    {o r : Fin I.amalgam.card} (hF : FieldsLE K Nf T o) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hKg : K ≤ g + 1) {J₀ J : ℕ} (hJ : J < J₀) (hJm : g + J ≤ m)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hlayer : (sTower L (lowPred K Nf T o r) J).Good (lowPred K Nf T o r) →
      ¬ ((sTower L (lowPred K Nf T o r) J).sS
        (sCat I (g + J + 1) (lowPred K Nf T o r))).rows.CappedLift
        (X := (univ.erase x, g + J + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + J + 1))
        ⟨erase_subset _ _, le_rfl⟩) :
    ¬ STowerLifts L (lowPred K Nf T o r) J₀ := fun hlift ↦
  hlayer (sTower_good hL (fun W ↦ lowPred_withCut_bot W)
    (fun _ hj _ hP ↦ lowPred_scode hF hrK (hKg.trans hj) hP) hlift J hJ.le hJm) (hlift J hJ x hx)

/-- **The lifts of the state tower fail at a held frontier**: the configuration of
`ProfileTower.SLvl.Good.not_cappedLift_sS_of_held` at a member of the catalogue of a layer
`J < J₀` (with `g + J ≤ m`) of the state tower of the LOW clause, from a point `x`. -/
theorem not_sTowerLifts_of_held {L : Lvl I g} (hL : L.Good) {K : ℕ}
    {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
    {o r : Fin I.amalgam.card} (hF : FieldsLE K Nf T o) (hrK : I.amalgam.toCellScheme.grade r ≤ K)
    (hKg : K ≤ g + 1) {J₀ J : ℕ} (hJ : J < J₀) (hJm : g + J ≤ m)
    {x y : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    {t d₁ d₂ u w₀ : Fin I.amalgam.card}
    (hw₀ : I.amalgam.toCellScheme.gradedIndex w₀ = (univ.erase y, g + J + 1))
    (hheld : ∀ w, I.amalgam.toCellScheme.gradedIndex w = (univ.erase y, g + J + 1) →
      o ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      r ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₁ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      d₂ ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex w) ∧
      I.amalgam.rowAt w d₁ ≤ I.amalgam.rowAt w o ∧ I.amalgam.rowAt w d₂ ≤ I.amalgam.rowAt w r)
    (ht : Sum.inl t ∈ T) (htx : t ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    (hux : u ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1))
    (huy : I.amalgam.toCellScheme.scope u ⊆ univ.erase y)
    (hug : I.amalgam.toCellScheme.grade u = g + J + 1)
    {P : CProf I} (hP : P ∈ sCat I (g + J + 1) (lowPred K Nf T o r)) {h : Label.{u}}
    (hh : IsSelfVisible (g + J + 1) h) (hNh : ∀ f ∈ Nf, ∃ e, f = Sum.inl e ∧ P (Sum.inl e) < h)
    (hact : donorMax Nf P < min (P (Sum.inr ())) h)
    {a : Prof I} (ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + J + 1) (fun e ↦ a e))
    (haP : ∀ e ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1),
      min (a e) h = min (P (Sum.inl e)) h)
    (hu₁ : a d₁ < a u) (hu₂ : a d₂ < a u) (hDu : donorMax Nf P < a u)
    (hat : a t < min (a d₁) (visibilityReplace K K (a d₂))) :
    ¬ STowerLifts L (lowPred K Nf T o r) J₀ :=
  not_sTowerLifts_of_layer hL hF hrK hKg hJ hJm hx fun hN ↦
    hN.not_cappedLift_sS_of_held (by omega) hw₀ hheld ht htx hd₁ hd₂ hux huy hug hP hh
      (fun f hf ↦ by
        obtain ⟨e, rfl, he⟩ := hNh f hf
        obtain ⟨e', he', hge'⟩ := hF.1 _ hf
        cases he'
        exact ⟨e, rfl, by omega, he⟩) hact ha haP hu₁ hu₂ hDu hat

end ProfileTower

end VaughtConjecture

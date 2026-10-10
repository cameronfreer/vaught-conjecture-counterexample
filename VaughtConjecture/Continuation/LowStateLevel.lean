/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowPaddingLevel

/-!
# Levels indexed by states

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the levels above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

A **state** is a profile with a cutoff (`ProfileTower.CProf`): the labels of the amalgam cells and
one more field, the cutoff, free of them.  Above the grade `K` of the controllers the
padding of [AFK26] indexes the sections by states: the section of a state reads every controller
through the cutoff of the state itself (`VaughtConjecture.Continuation.LowPaddingObstruction`
shows why a cutoff read off the amalgam profile cannot).

**State levels** (`ProfileTower.SLvl`).  A scheme, a section for every state, and the old cells.
**Good state levels** (`ProfileTower.SLvl.Good A`): the scheme fields of `ProfileTower.Lvl.Good`;
the section lawful at the states with amalgam part lawful on the cut that satisfy `A`, in the code
grid, literal at the old cells, agreeing capped at every cap self-visible and short where the
states agree capped (cutoff included), and readable at the states with the cutoff `⊥`.

**Forgetting the cutoff** (`ProfileTower.SLvl.forget`, `ProfileTower.SLvl.Good.forget`, compiled in
this repository).  The section of an amalgam profile is the section of the state with the cutoff
`⊥`.  When `A` holds with the cutoff `⊥`, a good state level is a good level, so the completion
below the full grade (`ProfileTower.Lvl.Good.completion`) and the reading of
`ProfileTower.ReadsActualOn` apply to it unchanged.  Conversely a good level is a good state level
reading the amalgam part (`ProfileTower.Lvl.Good.toS`).

**The next state level** (`ProfileTower.SLvl.next`, `ProfileTower.SLvl.Good.next`, compiled in this
repository).  Over a state level at the grade `g`, one cell of full scope and grade `g + 1` per
state of a finite set `C` of states; its row is the section of the state at the cells of the level
and the agreement heights with the states of `C`, cutoff included.  The section of the next state
level reads, at the cells of grade at most `g + 1`, the row of the **state code** of a state
(`ProfileTower.scode`: the orbit code at `g + 1` over all fields, the cutoff included, of its
splice), through the upper decoder of the splice; the orbit code over all fields is what keeps
capped agreement (`Label.min_upperDecoderAt_comp_eq` over the fields).  For `C` the **state
catalogue** of `A` (`ProfileTower.sCat`: states in the code grid, amalgam part lawful on the cut,
fixed by the orbit code over all fields, satisfying `A`) the next state level is good, given that
`A` holds with the cutoff `⊥`, is kept by the state code, and the layer lifts from the two coatoms
at `g + 1`: the lift is the one hypothesis (for the LOW clause, the LOW step at the grade `g + 1`).
Its forgetful level extends at `⊥` (`ProfileTower.SLvl.Good.hasBotExtension_next`).

**States with the cutoff `⊥`** (`Label.orbitCode_withCut_bot`,
`Label.isReadableAt_withCut_bot_iff`).
A cutoff `⊥` is no key: the orbit code over all fields of an amalgam profile with the cutoff `⊥` is
its orbit code with the cutoff `⊥`, and readability is that of the amalgam profile.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Label

open Finset

variable {ι : Type*} {k K : ℕ} {w : ι → Label.{u}} {x : Label.{u}}

/-- The cutoff `⊥` adds no key. -/
theorem isKey_withCut_bot :
    IsKey k (Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u})) x ↔ IsKey k w x := by
  constructor
  · rintro ⟨f, hf, hfx⟩
    rcases f with d | z
    · exact ⟨d, hf, hfx⟩
    · exact absurd rfl hf
  · rintro ⟨d, hd, hdx⟩
    exact ⟨Sum.inl d, hd, hdx⟩

/-- The cutoff `⊥` adds no orbit key. -/
theorem isOrbitKey_withCut_bot :
    IsOrbitKey k (Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u})) x ↔ IsOrbitKey k w x := by
  constructor
  · rintro ⟨f, hfx, hf⟩
    rcases f with d | z
    · exact ⟨d, hfx, hf⟩
    · exact absurd (isSelfVisible_bot k) hf
  · rintro ⟨d, hdx, hd⟩
    exact ⟨Sum.inl d, hdx, hd⟩

/-- **Readability for a profile with the cutoff `⊥` is readability for the profile.** -/
theorem isReadableAt_withCut_bot_iff :
    IsReadableAt K (Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u})) x ↔ IsReadableAt K w x := by
  unfold IsReadableAt
  rw [isKey_withCut_bot, isOrbitKey_withCut_bot]

variable [Fintype ι]

/-- The cutoff `⊥` leaves the key ranks. -/
theorem keyRank_withCut_bot :
    keyRank k (Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u})) x = keyRank k w x := by
  classical
  unfold keyRank valueRank
  congr 1
  ext y
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨f, rfl⟩, hy, hyx⟩
    rcases f with d | z
    · exact ⟨⟨d, rfl⟩, hy, hyx⟩
    · exact absurd (visibilityReplace_bot k k) hy
  · rintro ⟨⟨d, rfl⟩, hy, hyx⟩
    exact ⟨⟨Sum.inl d, rfl⟩, hy, hyx⟩

/-- The cutoff `⊥` leaves the orbit map. -/
theorem orbitMap_withCut_bot :
    orbitMap k (Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u})) x = orbitMap k w x := by
  unfold orbitMap codeBlock
  rw [keyRank_withCut_bot, propext isKey_withCut_bot, propext isOrbitKey_withCut_bot]

/-- **The orbit code of a profile with the cutoff `⊥` is its orbit code with the cutoff `⊥`.** -/
theorem orbitCode_withCut_bot :
    orbitCode k (Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u})) =
      Sum.elim (orbitCode k w) fun _ ↦ ⊥ := by
  funext f
  rcases f with d | z
  · exact orbitMap_withCut_bot
  · exact orbitMap_bot (k := k) (w := Sum.elim w fun _ : Unit ↦ (⊥ : Label.{u}))

end VaughtConjecture.Label

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### State levels -/

variable (I) in
/-- **A state level** at the grade `g`: a scheme, a section for every state, and the old cells,
every cell of grade at most `g` or of scope other than the ground set. -/
structure SLvl (g : ℕ) where
  /-- The scheme. -/
  S : Scheme.{u} (m + 2) /-- The section of a state. -/
  σs : CProf I → Fin S.card → Label.{u} /-- The old cells. -/
  embed : Fin I.amalgam.card ↪o Fin S.card /-- Every cell has grade at most `g` or scope other
  than the ground set. -/
  inv : ∀ d, S.toCellScheme.grade d ≤ g ∨ S.toCellScheme.scope d ≠ univ

variable {g : ℕ}

/-- **The forgetful level**: the section of an amalgam profile is that of the state with the cutoff
`⊥`. -/
def SLvl.forget (N : SLvl I g) : Lvl I g := ⟨N.S, fun P ↦ N.σs (withCut P ⊥), N.embed, N.inv⟩

/-- **A level as a state level**, reading the amalgam part of a state. -/
def Lvl.toS (L : Lvl I g) : SLvl I g := ⟨L.S, fun P ↦ L.σ (camal P), L.embed, L.inv⟩

/-- **A good state level** for a predicate `A` on states (see the module docstring). -/
structure SLvl.Good (A : CProf I → Prop) (N : SLvl I g) : Prop where
  lowerEmb : I.amalgam.toCellScheme.IsLowerEmbedding N.S.toCellScheme N.embed
  scope_embed : ∀ d, N.S.toCellScheme.scope (N.embed d) = I.amalgam.toCellScheme.scope d
  comap_rows : N.S.rows.comap lowerEmb = I.amalgam.rows
  mem_range : ∀ z, N.S.toCellScheme.scope z ≠ univ → z ∈ Set.range N.embed
  faces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces
  wf : N.S.IsWellFormed
  coded : N.S.IsCoded
  consistent : N.S.rows.IsConsistent
  lawful : ∀ P : CProf I, IsCutLawful I g (camal P) → A P →
    N.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g) fun z ↦ N.σs P z
  mem : ∀ P : CProf I, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, N.σs P z ∈ codeGrid (g + 1) (bound I)
  literal : ∀ P d, N.σs P (N.embed d) = P (Sum.inl d)
  capAgree : ∀ P P' : CProf I, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) → ∀ h : Label.{u},
    IsSelfVisible (g + 1) h → IsShort (g + 1) h → (∀ f, min (P f) h = min (P' f) h) →
    ∀ z, min (N.σs P z) h = min (N.σs P' z) h
  readable : ∀ Q : Prof I, orbitCode (g + 1) Q = Q → (∀ d, Q d ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, IsReadableAt (g + 1) Q (N.σs (withCut Q ⊥) z)
  lift : ∀ x ∈ (Pts : Finset (Fin (m + 2))), ∀ j ≤ g,
    N.S.rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨erase_subset _ _, le_rfl⟩
  complete : ∀ j, 0 < j → j ≤ g →
    ∃ z, N.S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), j)

variable {A : CProf I → Prop}

/-- **A good state level forgets to a good level**, when `A` holds with the cutoff `⊥`. -/
theorem SLvl.Good.forget {N : SLvl I g} (hN : N.Good A) (hA0 : ∀ W : Prof I, A (withCut W ⊥)) :
    N.forget.Good where
  lowerEmb := hN.lowerEmb
  scope_embed := hN.scope_embed
  comap_rows := hN.comap_rows
  mem_range := hN.mem_range
  faces := hN.faces
  wf := hN.wf
  coded := hN.coded
  consistent := hN.consistent
  lawful P hP := hN.lawful _ hP (hA0 P)
  mem P hP := hN.mem _ fun f ↦ by
    rcases f with d | z
    exacts [hP d, mem_insert_self _ _]
  literal P d := hN.literal _ d
  capAgree P P' hP h hh hs hag := hN.capAgree _ _ (fun f ↦ by
      rcases f with d | z
      exacts [hP d, mem_insert_self _ _]) h hh hs fun f ↦ by
    rcases f with d | z
    exacts [hag d, rfl]
  readable := hN.readable
  lift := hN.lift
  complete := hN.complete

/-- **A good level is a good state level** reading the amalgam part, for every predicate. -/
theorem Lvl.Good.toS {L : Lvl I g} (hL : L.Good) (A : CProf I → Prop) : L.toS.Good A where
  lowerEmb := hL.lowerEmb
  scope_embed := hL.scope_embed
  comap_rows := hL.comap_rows
  mem_range := hL.mem_range
  faces := hL.faces
  wf := hL.wf
  coded := hL.coded
  consistent := hL.consistent
  lawful P hP _ := hL.lawful (camal P) hP
  mem P hP := hL.mem (camal P) fun _ ↦ hP _
  literal P d := hL.literal (camal P) d
  capAgree P P' hP h hh hs hag := hL.capAgree (camal P) (camal P') (fun _ ↦ hP _) h hh hs
    fun _ ↦ hag _
  readable := hL.readable
  lift := hL.lift
  complete := hL.complete

/-- No cell of a state level at the grade `g` lies above `(univ, g + 1)`. -/
theorem SLvl.not_le (N : SLvl I g) (d : Fin N.S.card) :
    ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ N.S.toCellScheme.gradedIndex d :=
  N.forget.not_le d

/-- **The cover of `(univ, g + 1)`** in a good state level: a cell below `(univ, g + 1)` lies below
`(univ, g)` or below one of the coatoms at the grade `g + 1`. -/
theorem SLvl.Good.mem_below_cover {N : SLvl I g} (hN : N.Good A) {x y : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset _)) (hy : y ∈ (Pts : Finset _)) (hxy : x ≠ y) (z : Fin N.S.card)
    (hz : z ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
    z ∈ N.S.toCellScheme.below (univ.erase x, g + 1) ∨
      z ∈ N.S.toCellScheme.below (univ, g) ∨ z ∈ N.S.toCellScheme.below (univ.erase y, g + 1) := by
  have hgi (d : Fin I.amalgam.card) :
      N.S.toCellScheme.gradedIndex (N.embed d) = I.amalgam.toCellScheme.gradedIndex d :=
    Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)
  by_cases hzg : N.S.toCellScheme.grade z ≤ g
  · exact .inr (.inl ⟨subset_univ _, hzg⟩)
  obtain ⟨d, rfl⟩ := hN.mem_range z ((N.inv z).resolve_left hzg)
  have hd : I.amalgam.toCellScheme.grade d ≤ g + 1 := by
    have := hz.2
    rwa [hgi] at this
  rcases I.scope_subset_or hx hy hxy d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, hgi]; exact ⟨h, hd⟩
  · refine .inr (.inr ?_)
    rw [CellScheme.mem_below, hgi]; exact ⟨h, hd⟩

/-! ### State codes and state catalogues -/

/-- The **splice of a state** at the grade `k`: the splice of its amalgam part, its cutoff. -/
noncomputable abbrev hatS (k : ℕ) (P : CProf I) : CProf I :=
  withCut (hat I k (camal P)) (P (Sum.inr ()))

/-- The **state code** at the grade `k`: the orbit code over all fields of the splice. -/
noncomputable abbrev scode (k : ℕ) (P : CProf I) : CProf I := orbitCode k (hatS k P)

theorem card_fields : Fintype.card (Fin I.amalgam.card ⊕ Unit) = I.amalgam.card + 1 := by simp

/-- The state code lies in the code grid. -/
theorem scode_mem_codeGrid (k : ℕ) (P : CProf I) (f : Fin I.amalgam.card ⊕ Unit) :
    scode k P f ∈ codeGrid k (bound I) :=
  orbitMap_mem_codeGrid (by rw [card_fields]; simp only [bound]; omega) _

variable (I) in
open Classical in
/-- The **state catalogue** of `A` at the grade `k`: the states with values in the code grid,
amalgam part lawful on the cut, fixed by the orbit code over all fields, satisfying `A`. -/
noncomputable def sCat (k : ℕ) (A : CProf I → Prop) : Finset (CProf I) :=
  (Fintype.piFinset fun _ ↦ codeGrid k (bound I)).filter fun P ↦
    IsCutLawful I k (camal P) ∧ orbitCode k P = P ∧ A P

theorem mem_sCat {k : ℕ} {P : CProf I} : P ∈ sCat I k A ↔
    (∀ f, P f ∈ codeGrid k (bound I)) ∧ IsCutLawful I k (camal P) ∧ orbitCode k P = P ∧
      A P := by
  classical
  simp only [sCat, Finset.mem_filter, Fintype.mem_piFinset]

/-- The splice of a state with amalgam part lawful on the cut has amalgam part lawful on the cut. -/
theorem isCutLawful_camal_scode {k : ℕ} {P : CProf I} (hP : IsCutLawful I k (camal P)) :
    IsCutLawful I k (camal (scode k P)) := by
  obtain ⟨hC, hD⟩ := isCutLawful_hat hP
  exact ⟨hC.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap k (hatS k P))
      fun _ ↦ orbitMap_eq_bot_iff.mp,
    hD.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap k (hatS k P))
      fun _ ↦ orbitMap_eq_bot_iff.mp⟩

/-- **The state code of a state lies in the state catalogue** when it satisfies `A`. -/
theorem scode_mem_sCat {k : ℕ} {P : CProf I} (hP : IsCutLawful I k (camal P))
    (hA : A (scode k P)) : scode k P ∈ sCat I k A :=
  mem_sCat.mpr ⟨scode_mem_codeGrid k P, isCutLawful_camal_scode hP, orbitCode_orbitCode, hA⟩

/-- **The state code of a profile with the cutoff `⊥`** is its code with the cutoff `⊥`. -/
theorem scode_withCut_bot (k : ℕ) (W : Prof I) : scode k (withCut W ⊥) = withCut (code k W) ⊥ :=
  orbitCode_withCut_bot

/-- The splices of states agreeing capped agree capped. -/
theorem min_hatS_eq {k : ℕ} {P P' : CProf I} {h : Label.{u}}
    (hag : ∀ f, min (P f) h = min (P' f) h) (f : Fin I.amalgam.card ⊕ Unit) :
    min (hatS k P f) h = min (hatS k P' f) h := by
  rcases f with d | z
  · exact min_hat_eq (fun d ↦ hag (Sum.inl d)) d
  · exact hag _

theorem hatS_mem_codeGrid {k K B : ℕ} {P : CProf I} (hP : ∀ f, P f ∈ codeGrid K B)
    (f : Fin I.amalgam.card ⊕ Unit) : hatS k P f ∈ codeGrid K B := by
  rcases f with d | z
  · exact hat_mem_codeGrid (fun d ↦ hP (Sum.inl d)) d
  · exact hP _

/-! ### The next state level -/

section Next

variable (N : SLvl I g) (C : Finset (CProf I))

/-- The **row labelling of a state** over a state level: its section at the cells of the level,
and the agreement heights with the states of `C`, cutoff included. -/
noncomputable def SLvl.Φs (R : CProf I) : Fin (N.S.card + C.card) → Label.{u} :=
  Fin.append (N.σs R) fun i ↦ agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm i).1

/-- The scheme of the next state level: one cell at `(univ, g + 1)` per state of `C`. -/
noncomputable abbrev SLvl.sS : Scheme.{u} (m + 2) :=
  N.S.appendFullCells (g + 1) C.card (fun i ↦ N.Φs C (C.equivFin.symm i).1) N.not_le

/-- The section of the next state level: at the cells of grade at most `g + 1`, the row labelling
of the state code, read by the upper decoder of the splice; above, the section of the level. -/
noncomputable def SLvl.nextσ (P : CProf I) : Fin (N.S.card + C.card) → Label.{u} := fun z ↦
  if (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1 then
    upperDecoderAt (g + 1) (g + 2) (bound I) (hatS (g + 1) P) (N.Φs C (scode (g + 1) P) z)
  else Fin.append (N.σs P) (fun _ ↦ ⊥) z

/-- **The next state level** on `C`, at the grade `g + 1`. -/
noncomputable def SLvl.next : SLvl I (g + 1) where
  S := N.sS C
  σs := N.nextσ C
  embed := N.embed.trans (Fin.castAddOrderEmb _)
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_scope_castAdd]
      exact (N.inv d).imp_left fun h ↦ h.trans (Nat.le_succ g)
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

variable {N C}

@[simp] theorem SLvl.Φs_castAdd (R : CProf I) (e : Fin N.S.card) :
    N.Φs C R (Fin.castAdd _ e) = N.σs R e := Fin.append_left _ _ e

@[simp] theorem SLvl.Φs_natAdd (R : CProf I) (i : Fin C.card) :
    N.Φs C R (Fin.natAdd _ i) = agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm i).1 :=
  Fin.append_right _ _ i

theorem SLvl.nextσ_of_le {P : CProf I} {z : Fin (N.S.card + C.card)}
    (hz : (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1) :
    N.nextσ C P z =
      upperDecoderAt (g + 1) (g + 2) (bound I) (hatS (g + 1) P) (N.Φs C (scode (g + 1) P) z) := by
  unfold SLvl.nextσ; exact ite_eq_left hz

variable (hN : N.Good A)
include hN

theorem SLvl.Good.Φs_mem_codeGrid {R : CProf I} (hR : ∀ f, R f ∈ codeGrid (g + 1) (bound I))
    (z : Fin (N.S.card + C.card)) : N.Φs C R z ∈ codeGrid (g + 1) (bound I) := by
  induction z using Fin.addCases with
  | left e => rw [SLvl.Φs_castAdd]; exact hN.mem R hR e
  | right i =>
    rw [SLvl.Φs_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

theorem SLvl.Good.exists_old_of_lt {z : Fin (N.S.card + C.card)}
    (hz : ¬ (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1) :
    ∃ d, z = Fin.castAdd _ (N.embed d) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le hz
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd] at hz
    have he : N.S.toCellScheme.scope e ≠ univ := (N.inv e).resolve_left (by omega)
    obtain ⟨d, rfl⟩ := hN.mem_range e he
    exact ⟨d, rfl⟩

theorem SLvl.Good.nextσ_old_of_lt {P : CProf I} {d : Fin I.amalgam.card}
    (hd : ¬ (N.S.appendFullCellsScheme (g + 1) C.card).grade (Fin.castAdd _ (N.embed d)) ≤ g + 1) :
    N.nextσ C P (Fin.castAdd _ (N.embed d)) = P (Sum.inl d) := by
  unfold SLvl.nextσ
  rw [ite_eq_right hd, Fin.append_left, hN.literal]

/-- **The row labelling of a state of `C` is lawful below `(univ, g + 1)`**, for a state with values
in the code grid, amalgam part lawful on the grade-`(g + 1)` cut, satisfying `A`. -/
theorem SLvl.Good.isLawfulBelow_Φs {R : CProf I} (hRC : R ∈ C)
    (hRB : ∀ f, R f ∈ codeGrid (g + 1) (bound I)) (hRc : IsCutLawful I (g + 1) (camal R))
    (hRA : A R) :
    (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1) fun z ↦ N.Φs C R z := by
  classical
  obtain ⟨hC, hD⟩ := hRc
  have hlow : (N.sS C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g)
      fun z ↦ N.Φs C R z := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff
      (by rintro ⟨-, h⟩; simp only at h; omega)).mpr ?_
    simpa only [SLvl.Φs_castAdd] using hN.lawful R
      ⟨hC.mono (X := (_, g)) ⟨subset_rfl, by omega⟩, hD.mono (X := (_, g)) ⟨subset_rfl, by omega⟩⟩
      hRA
  have hold (x : Fin (m + 2))
      (hRX : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ camal R d) :
      N.S.rows.IsLawfulBelow (univ.erase x, g + 1) fun e ↦ N.σs R e := by
    have hsp : I.amalgam.toCellScheme.IsSourcePrefix N.S.toCellScheme N.embed
        (univ.erase x, g + 1) :=
      ⟨hN.lowerEmb, hN.scope_embed, fun z hz ↦ hN.mem_range z fun he ↦
        Seed.ne_univ_erase x (univ_subset_iff.mp (he ▸ (hz.1 : N.S.toCellScheme.scope z ⊆ _)))⟩
    rw [← hsp.isLawfulBelow_iff le_rfl, hN.comap_rows]
    exact (Rows.isLawfulBelow_congr (w' := fun d ↦ N.σs R (N.embed d))
      fun d _ ↦ (hN.literal R d).symm).mp hRX
  have hcoat (x : Fin (m + 2))
      (hRX : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) fun d ↦ camal R d) :
      (N.sS C).rows.IsLawfulBelow (univ.erase x, g + 1) fun z ↦ N.Φs C R z := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff fun h ↦ Seed.ne_univ_erase x
      (univ_subset_iff.mp h.1)).mpr ?_
    simpa only [SLvl.Φs_castAdd] using hold x hRX
  have hcC := hcoat _ hC
  have hcD := hcoat _ hD
  obtain ⟨ho2, hl2, ha2⟩ := Rows.isLawfulBelow_iff_forall.mp hlow
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hcC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hcD
  have hcases {e : Fin N.S.card}
      (he : Fin.castAdd C.card e ∈
        (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      Fin.castAdd C.card e ∈ (N.sS C).toCellScheme.below (coatC, g + 1) ∨
        Fin.castAdd C.card e ∈
          (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g) ∨
        Fin.castAdd C.card e ∈ (N.sS C).toCellScheme.below (coatD, g + 1) := by
    have he' : e ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) := by
      have := he
      rwa [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact hN.mem_below_cover (by simp) (by simp) Seed.last_ne_castSucc e he'
  obtain ⟨i₀, hi₀⟩ := exists_equivFin_eq hRC
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [hoC _ h, ho2 _ h, hoD _ h]
    | right j =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, SLvl.Φs_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hlC _ h, hl2 _ h, hlD _ h]
    | right j =>
      set κ := agreementHeight (grid (g + 1) (bound I)) R (C.equivFin.symm j).1 with hκ
      have hκm : κ ∈ grid (g + 1) (bound I) := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible (g + 1) κ := isSelfVisible_of_mem_grid hκm
      refine ⟨constStepSuppressor (g + 1) κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : (N.sS C).toCellScheme.grade t ≤ g + 1 := t.2.2.trans_eq
        (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd N.S (g + 1) _ j))
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, SLvl.Φs_natAdd]
      obtain ⟨t, -⟩ := t
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [SLvl.Φs_castAdd, SLvl.Φs_castAdd]
        exact hN.capAgree R (C.equivFin.symm j).1 hRB κ hκv (isShort_of_mem_grid hκm)
          (fun f ↦ (agreementHeight_spec (bot_mem_grid _ _) R (C.equivFin.symm j).1).2 f) e
      | right j' =>
        rw [SLvl.Φs_natAdd, SLvl.Φs_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [haC s _ h hst hg, ha2 s _ h hst hg, haD s _ h hst hg]
    | right j =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [SLvl.Φs_natAdd, hi₀, agreementHeight_self (gridPoint_mem_grid le_rfl)
        (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
      exact le_gridPoint_of_mem_codeGrid (hN.Φs_mem_codeGrid hRB s)

/-- **The layer of a state catalogue over a good state level is consistent.** -/
theorem SLvl.Good.sS_consistent (hCsub : ∀ P ∈ C, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) ∧ A P) :
    (N.sS C).rows.IsConsistent := by
  intro s
  induction s using Fin.addCases with
  | right i =>
    have hu := Scheme.appendFullCellsScheme_gradedIndex_natAdd N.S (g + 1) C.card i
    have hm := (C.equivFin.symm i).2
    have h := hN.isLawfulBelow_Φs hm (hCsub _ hm).1 (hCsub _ hm).2.1 (hCsub _ hm).2.2
    change (N.sS C).rows.IsLawfulBelow ((N.sS C).toCellScheme.gradedIndex (Fin.natAdd _ i))
      ((N.sS C).rows.row (Fin.natAdd _ i))
    rw [Scheme.appendFullCells_row_natAdd_eq]
    rw [show (N.sS C).toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin (m + 2))), g + 1) from hu]
    exact h
  | left s =>
    have hφ := Scheme.isLowerEmbedding_castAdd (S := N.S) (g + 1) C.card
      (fun i ↦ N.Φs C (C.equivFin.symm i).1) N.not_le
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [Scheme.comap_rows_castAdd]
    convert hN.consistent s using 1
    funext t
    exact congrArg (fun R : N.S.toCellScheme.Rows ↦ R.row s t) Scheme.comap_rows_castAdd

omit hN in
/-- Capped lifts below a pair not above `(univ, g + 1)` are those of the level. -/
theorem SLvl.cappedLift_sS_iff {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ Y) :
    (N.sS C).rows.CappedLift hXY ↔ N.S.rows.CappedLift hXY :=
  Scheme.cappedLift_appendFullCells_iff hXY hY

end Next

/-! ### The next state level on a state catalogue is good -/

section NextGood

variable {N : SLvl I g}

local notation "𝒮" => sCat I (g + 1) A

/-- **The next state level on the state catalogue of `A` is good**, over a good state level, for
`g + 1 ≤ m`, when `A` holds with the cutoff `⊥`, the state code keeps `A`, and the layer lifts
from the two coatoms at `g + 1`. -/
theorem SLvl.Good.next (hN : N.Good A) (hgm : g + 1 ≤ m) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hAc : ∀ P : CProf I, A P → A (scode (g + 1) P))
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (N.sS 𝒮).rows.CappedLift (X := (univ.erase x, g + 1))
        (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩) :
    (N.next 𝒮).Good A := by
  have hCsub : ∀ P ∈ 𝒮, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) ∧ A P := fun P hP ↦
    ⟨(mem_sCat.mp hP).1, (mem_sCat.mp hP).2.1, (mem_sCat.mp hP).2.2.2⟩
  have hemb := Scheme.isLowerEmbedding_castAdd (S := N.S) (g + 1) (𝒮).card
    (fun i ↦ N.Φs 𝒮 ((𝒮).equivFin.symm i).1) N.not_le
  have hcard : 2 * Fintype.card (Fin I.amalgam.card ⊕ Unit) = bound I := by
    rw [card_fields]; simp only [bound]; ring
  refine
    { lowerEmb := hemb.comp hN.lowerEmb
      scope_embed := fun d ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (hN.scope_embed d)
      comap_rows := ?_
      mem_range := ?_
      faces := hN.faces
      wf := Scheme.isWellFormed_appendFullCells (M := (𝒮).card)
        (r := fun i ↦ N.Φs 𝒮 ((𝒮).equivFin.symm i).1) (h := N.not_le) hN.wf (by omega)
        (by omega)
      coded := Scheme.isCoded_appendFullCells (h := N.not_le) hN.coded fun i d ↦
        lt_omega0_sq_of_mem_codeGrid (hN.Φs_mem_codeGrid (hCsub _ ((𝒮).equivFin.symm i).2).1 d)
      consistent := hN.sS_consistent hCsub
      lawful := fun P hP hPA ↦ ?_
      mem := fun P hP z ↦ ?_
      literal := fun P d ↦ ?_
      capAgree := fun P P' hP h hh hs hag z ↦ ?_
      readable := fun Q hQ hQB z ↦ ?_
      lift := fun x hx j hj ↦ ?_
      complete := fun j hj0 hj ↦ ?_ }
  · have h := Rows.comap_comap (N.sS 𝒮).rows hemb hN.lowerEmb
    rw [Scheme.comap_rows_castAdd, hN.comap_rows] at h
    exact h.symm
  · intro z hz
    induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left e =>
      have hz' : N.S.toCellScheme.scope e ≠ univ := by
        have := (Scheme.appendFullCellsScheme_scope_castAdd N.S (g + 1) (𝒮).card e)
        exact fun h ↦ hz (this.trans h)
      obtain ⟨d, rfl⟩ := hN.mem_range e hz'
      exact ⟨d, rfl⟩
  · -- lawful
    have hQ := scode_mem_sCat (A := A) hP (hAc P hPA)
    have h := (hN.isLawfulBelow_Φs hQ (hCsub _ hQ).1 (hCsub _ hQ).2.1
      (hCsub _ hQ).2.2).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_upperDecoderAt (w := hatS (g + 1) P) (B := bound I) (K := g + 2) (by omega))
      (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
    refine (Rows.isLawfulBelow_congr (R := (N.sS 𝒮).rows)
      (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) (hatS (g + 1) P)
        (N.Φs 𝒮 (scode (g + 1) P) z)) (w' := N.nextσ 𝒮 P) fun z hz ↦ ?_).mp h
    exact (SLvl.nextσ_of_le hz.2).symm
  · -- mem
    change N.nextσ 𝒮 P z ∈ _
    by_cases hz : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade z ≤ g + 1
    · rw [SLvl.nextσ_of_le hz]
      exact upperDecoderAt_mem_codeGrid_of_mem (by omega) (hatS_mem_codeGrid hP)
        (hN.Φs_mem_codeGrid (scode_mem_codeGrid _ _) z)
    · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
      rw [hN.nextσ_old_of_lt hz]
      exact hP _
  · -- literal
    change N.nextσ 𝒮 P (Fin.castAdd _ (N.embed d)) = P (Sum.inl d)
    by_cases hd : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade
        (Fin.castAdd _ (N.embed d)) ≤ g + 1
    · rw [SLvl.nextσ_of_le hd, SLvl.Φs_castAdd, hN.literal]
      change upperDecoderAt (g + 1) (g + 2) (bound I) (hatS (g + 1) P)
        (orbitCode (g + 1) (hatS (g + 1) P) (Sum.inl d)) = P (Sum.inl d)
      rw [upperDecoderAt_orbitCode]
      rw [Scheme.appendFullCellsScheme_grade_castAdd, hN.lowerEmb.grade_eq] at hd
      exact hat_of_le hd
    · exact hN.nextσ_old_of_lt hd
  · -- capAgree
    change min (N.nextσ 𝒮 P z) h = min (N.nextσ 𝒮 P' z) h
    by_cases hz : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade z ≤ g + 1
    · rw [SLvl.nextσ_of_le hz, SLvl.nextσ_of_le hz]
      refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
        (fun f ↦ le_gridPoint_of_mem_codeGrid (hatS_mem_codeGrid hP f)) (min_hatS_eq hag)
        (N.Φs 𝒮) (fun c c' hc hc' Γ hΓv hΓs hcc z ↦ ?_) z
      have hcB (f : Fin I.amalgam.card ⊕ Unit) : c f ∈ codeGrid (g + 1) (bound I) :=
        hcard ▸ hc f
      have hcB' (f : Fin I.amalgam.card ⊕ Unit) : c' f ∈ codeGrid (g + 1) (bound I) :=
        hcard ▸ hc' f
      induction z using Fin.addCases with
      | left e =>
        rw [SLvl.Φs_castAdd, SLvl.Φs_castAdd]
        exact hN.capAgree c c' hcB Γ hΓv hΓs hcc e
      | right i =>
        rw [SLvl.Φs_natAdd, SLvl.Φs_natAdd]
        exact min_agreementHeight_eq_of_isShort hΓv hΓs (fun f ↦ ⟨hcB f, hcB' f⟩) hcc _
    · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
      rw [hN.nextσ_old_of_lt hz, hN.nextσ_old_of_lt hz]
      exact hag _
  · -- readable
    change IsReadableAt (g + 1 + 1) Q (N.nextσ 𝒮 (withCut Q ⊥) z)
    by_cases hz : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade z ≤ g + 1
    · rw [SLvl.nextσ_of_le hz, ← isReadableAt_withCut_bot_iff]
      have hQ' : orbitCode (g + 1 + 1) (withCut Q ⊥) = withCut Q ⊥ := by
        rw [orbitCode_withCut_bot, hQ]
      refine isReadableAt_upperDecoderAt_of_mem hQ' (by omega)
        (hatS_mem_codeGrid fun f ↦ ?_) (fun f ↦ ?_)
        (hN.Φs_mem_codeGrid (scode_mem_codeGrid _ _) z)
      · rcases f with d | u
        exacts [hQB d, mem_insert_self _ _]
      · rcases f with d | u
        · by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
          · change IsReadableAt _ _ (hat I (g + 1) Q d)
            rw [hat_of_le hd]; exact isReadableAt_apply (withCut Q ⊥) (Sum.inl d)
          · change IsReadableAt _ _ (hat I (g + 1) Q d)
            rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
        · exact .inl rfl
    · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
      rw [hN.nextσ_old_of_lt hz]
      exact isReadableAt_apply Q d
  · -- lift
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact (SLvl.cappedLift_sS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
        (hN.lift x hx j (by omega))
    · exact hlift x hx
  · -- complete
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e, he⟩ := hN.complete j hj0 (by omega)
      exact ⟨Fin.castAdd _ e, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).trans he⟩
    · have hbot : (fun _ ↦ ⊥ : CProf I) ∈ 𝒮 := by
        refine mem_sCat.mpr ⟨fun _ ↦ mem_insert_self _ _, (bot_mem_cat (I := I) _ |> mem_cat.mp).1,
          funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl, ?_⟩
        convert hA0 (fun _ ↦ ⊥) using 1
        funext f; rcases f with d | z <;> rfl
      obtain ⟨i₀, -⟩ := exists_equivFin_eq hbot
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

end NextGood

end VaughtConjecture.ProfileTower

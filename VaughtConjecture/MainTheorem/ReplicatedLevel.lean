/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelRecovery
import VaughtConjecture.MainTheorem.ReplicatedGradeLevel
import VaughtConjecture.MainTheorem.ReplicatedGradeStateStep

/-!
# Levels over the attachment, re-rendered per grade

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

A **level** at the grade `j` over the attachment of a seed (`Seed.ALvl`) is a scheme over the
ladder base of the attachment (`Seed.lvBase`: the cells of the attachment and the ladder points),
a **section** for every state of the attachment, and the embedding of the ladder base; every cell
has grade at most `j` or scope other than the ground set.

* **The first level** (`Seed.lvLevel1`): the ladder base, the section of a state the extension of
  the state with the rank member read from its grade one (`Seed.lvBaseSec`).
* **The next level** (`Seed.ALvl.next`) on a finite set `C` of states, at the grade `j + 1`: one
  cell of full scope and grade `j + 1` for each state of `C`, its row the **row labelling**
  (`Seed.ALvl.Φ`) of the state: the section of the level at the state, and the agreement heights
  of the state with the states of `C` in the grid `grid (j + 1) B`.  The section of a state `P` at
  the next level is the upper decoder of `P` applied to the row labelling of its orbit code at
  `j + 1`: a state is never asked to be a member of a lower catalogue; each level renders it
  through its own code (**re-rendering**, not nesting).
* **The catalogue** at the grade `j` (`Seed.lvCat`): the states in the code grid `codeGrid j B`,
  lawful below `(univ, j)`, with values self-visible at `1`, canonical for the orbit code at `j`,
  and admitted at `j` (`Seed.attachAdmits`).  The catalogues of different grades are separate:
  none is asked to contain another.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Scheme.LadderBaseData

variable {n' : ℕ} {B' : LadderBaseData.{u} n'} {H' : ℕ}

/-- The extension of a state with a rank member reads the state on the base cells. -/
theorem stateExtOf_castAdd' (R : Fin B'.S.card → Label.{u}) (a : RankMember B'.S H')
    (d : Fin B'.S.card) : B'.stateExtOf R a (Fin.castAdd _ d) = R d :=
  Fin.append_left _ _ d

/-- The values of the extension of a state with a rank member are `⊥`, `1`, or values of the
state. -/
theorem stateExtOf_cases (R : Fin B'.S.card → Label.{u}) (a : RankMember B'.S H')
    (t : Fin (B'.ladderBase H').card) :
    B'.stateExtOf R a t = ⊥ ∨ B'.stateExtOf R a t = 1 ∨ ∃ e, B'.stateExtOf R a t = R e := by
  induction t using Fin.addCases with
  | left d => exact .inr (.inr ⟨d, Fin.append_left _ _ d⟩)
  | right j =>
    change Fin.append R _ (Fin.natAdd _ j) = ⊥ ∨ Fin.append R _ (Fin.natAdd _ j) = 1 ∨
      ∃ e, Fin.append R _ (Fin.natAdd _ j) = R e
    rw [Fin.append_right]
    exact posTable_eq _

end Scheme.LadderBaseData

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ}

section Defs

variable (I : Seed.{u} α m) (g : Fin n ↪ Fin m) (H : ℕ)

/-- **The ladder base of the levels**: the attachment with its ladder points. -/
noncomputable abbrev lvBase : Scheme.{u} (m + 2) := (I.attachmentBase g).ladderBase H

open Classical in
/-- **The section of the first level**: the extension of a state with the rank member read from
its grade one, for a state lawful below `(univ, 1)` (with at most `H` cells); `⊥` otherwise. -/
noncomputable def lvBaseSec (R : Fin (I.attachment g).card → Label.{u}) :
    Fin (I.lvBase g H).card → Label.{u} :=
  if h : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ R d) ∧
      (I.attachmentBase g).S.card ≤ H then
    (I.attachmentBase g).stateExtOf R
      (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf h.2 h.1)
  else fun _ ↦ ⊥

/-- **A level** at the grade `j` over the attachment: a scheme, a section for every state, the
embedding of the ladder base; every cell has grade at most `j` or scope other than the ground
set. -/
structure ALvl (j : ℕ) where
  /-- The scheme. -/
  S : Scheme.{u} (m + 2)
  /-- The section of a state. -/
  σ : (Fin (I.attachment g).card → Label.{u}) → Fin S.card → Label.{u}
  /-- The cells of the ladder base. -/
  embed : Fin (I.lvBase g H).card → Fin S.card
  /-- Every cell has grade at most `j` or scope other than the ground set. -/
  inv : ∀ z, S.toCellScheme.grade z ≤ j ∨ S.toCellScheme.scope z ≠ univ

variable (B : ℕ)

open Classical in
/-- **The catalogue at the grade `j`**: the states in the code grid `codeGrid j B`, lawful below
`(univ, j)`, with values self-visible at `1`, canonical for the orbit code at `j`, admitted at
`j`. -/
noncomputable def lvCat {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) (j : ℕ) :
    Finset (Fin (I.attachment g).card → Label.{u}) :=
  (Fintype.piFinset fun _ ↦ codeGrid j B).filter fun R ↦
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) (fun d ↦ R d) ∧
      (∀ e, IsSelfVisible 1 (R e)) ∧ orbitCode j R = R ∧ I.attachAdmits g hd Q j R

variable {I g} in
/-- The admission predicate of the levels. -/
def lvAdm {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) (k : ℕ) (R : Fin (I.attachment g).card → Label.{u}) :
    Prop :=
  I.attachAdmits g hd Q k R

end Defs

variable {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

theorem mem_lvCat {d : StageType.{u} α (n + 1)}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} {j : ℕ} {R : Fin (I.attachment g).card → Label.{u}} :
    R ∈ I.lvCat g B hd Q j ↔ (∀ e, R e ∈ codeGrid j B) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) (fun d ↦ R d) ∧
      (∀ e, IsSelfVisible 1 (R e)) ∧ orbitCode j R = R ∧ I.attachAdmits g hd Q j R := by
  classical
  simp only [lvCat, mem_filter, Fintype.mem_piFinset]

/-- The section of the first level at a state lawful below `(univ, 1)`. -/
theorem lvBaseSec_of_isLawfulBelow (hcard : (I.attachmentBase g).S.card ≤ H)
    {R : Fin (I.attachment g).card → Label.{u}}
    (hR : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ R d)) :
    I.lvBaseSec g H R = (I.attachmentBase g).stateExtOf R
      (Scheme.RankMember.ofLawfulBelowOne (I.attachmentBase g).wf hcard hR) := by
  simp only [lvBaseSec, hR, hcard, and_self, dite_true]

/-! ### The first level and the next level -/

namespace ALvl

variable {j : ℕ} (N : I.ALvl g H j)

/-- No cell of a level at the grade `j` lies above `(univ, j + 1)`. -/
theorem not_le (z : Fin N.S.card) :
    ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ N.S.toCellScheme.gradedIndex z := fun h ↦ by
  rcases N.inv z with hz | hz
  · have := h.2; change j + 1 ≤ N.S.toCellScheme.grade z at this; omega
  · exact hz (univ_subset_iff.mp h.1)

/-- The cells of the attachment in a level. -/
noncomputable def attEmb (d : Fin (I.attachment g).card) : Fin N.S.card :=
  N.embed (Fin.castAdd _ d)

variable (B) in
/-- **The row labelling of a state** over a level: the section of the level at the state, and the
agreement heights of the state with the states of `C` in the grid `grid (j + 1) B`. -/
noncomputable def Φ (C : Finset (Fin (I.attachment g).card → Label.{u}))
    (R : Fin (I.attachment g).card → Label.{u}) : Fin (N.S.card + C.card) → Label.{u} :=
  Fin.append (N.σ R) fun i ↦ agreementHeight (grid (j + 1) B) R (C.equivFin.symm i).1

variable (B) in
/-- The scheme of the next level: one cell at `(univ, j + 1)` per state of `C`, its row the row
labelling of the state. -/
noncomputable abbrev nS (C : Finset (Fin (I.attachment g).card → Label.{u})) : Scheme.{u} (m + 2) :=
  N.S.appendFullCells (j + 1) C.card (fun i ↦ N.Φ B C (C.equivFin.symm i).1) N.not_le

variable (B) in
/-- **The next level** on `C`, at the grade `j + 1`: the section of a state `P` is the upper
decoder of `P` applied to the row labelling of the orbit code of `P` at `j + 1`. -/
noncomputable def next (C : Finset (Fin (I.attachment g).card → Label.{u})) :
    I.ALvl g H (j + 1) where
  S := N.nS B C
  σ P z := upperDecoderAt (j + 1) (j + 2) B P (N.Φ B C (orbitCode (j + 1) P) z)
  embed t := Fin.castAdd _ (N.embed t)
  inv z := by
    induction z using Fin.addCases with
    | left z =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_scope_castAdd]
      exact (N.inv z).imp_left fun h ↦ h.trans (Nat.le_succ j)
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

variable {N}

@[simp] theorem Φ_castAdd (C : Finset (Fin (I.attachment g).card → Label.{u}))
    (R : Fin (I.attachment g).card → Label.{u}) (e : Fin N.S.card) :
    N.Φ B C R (Fin.castAdd _ e) = N.σ R e := Fin.append_left _ _ e

@[simp] theorem Φ_natAdd (C : Finset (Fin (I.attachment g).card → Label.{u}))
    (R : Fin (I.attachment g).card → Label.{u}) (i : Fin C.card) :
    N.Φ B C R (Fin.natAdd _ i) = agreementHeight (grid (j + 1) B) R (C.equivFin.symm i).1 :=
  Fin.append_right _ _ i

theorem next_σ (C : Finset (Fin (I.attachment g).card → Label.{u}))
    (P : Fin (I.attachment g).card → Label.{u}) (z : Fin (N.next B C).S.card) :
    (N.next B C).σ P z = upperDecoderAt (j + 1) (j + 2) B P (N.Φ B C (orbitCode (j + 1) P) z) :=
  rfl

theorem next_attEmb (C : Finset (Fin (I.attachment g).card → Label.{u}))
    (d : Fin (I.attachment g).card) :
    (N.next B C).attEmb d = Fin.castAdd _ (N.attEmb d) := rfl

end ALvl

variable (I g H) in
/-- **The first level**: the ladder base, the section the extension with the rank member read
from the grade one. -/
noncomputable def lvLevel1 : I.ALvl g H 1 where
  S := I.lvBase g H
  σ := I.lvBaseSec g H
  embed t := t
  inv z := by
    induction z using Fin.addCases with
    | left d =>
      refine .inr ?_
      rw [Scheme.appendFullCellsScheme_scope_castAdd]
      exact (I.attachmentBase g).scope_ne_univ d
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

/-! ### Good levels -/

variable (B) in
/-- **A good level** at the grade `j`, for a predicate `A` on states (the admission): the scheme is
well formed and consistent, the attachment embeds as a lower embedding keeping scopes and rows,
every cell of scope other than the ground set is a cell of the attachment, and the section is
lawful below `(univ, j)` at the lawful admitted states, takes values in the code grid at `j + 1`,
is literal on the attachment, keeps capped agreement at the caps self-visible and short at `j + 1`,
and is readable at the canonical states. -/
structure ALvl.Good {j : ℕ} (N : I.ALvl g H j)
    (A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop) : Prop where
  wf : N.S.IsWellFormed
  consistent : N.S.rows.IsConsistent
  lowerEmb : (I.attachment g).toCellScheme.IsLowerEmbedding N.S.toCellScheme N.attEmb
  scope_attEmb : ∀ d, N.S.toCellScheme.scope (N.attEmb d) = (I.attachment g).toCellScheme.scope d
  comap_rows : N.S.rows.comap lowerEmb = (I.attachment g).rows
  mem_range : ∀ z, N.S.toCellScheme.scope z ≠ univ → z ∈ Set.range N.attEmb
  lawful : ∀ P : Fin (I.attachment g).card → Label.{u},
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) (fun d ↦ P d) →
    (∀ e, IsSelfVisible 1 (P e)) → A j P →
    N.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun z ↦ N.σ P z
  mem : ∀ P : Fin (I.attachment g).card → Label.{u}, (∀ d, P d ∈ codeGrid (j + 1) B) →
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P d) →
    ∀ z, N.σ P z ∈ codeGrid (j + 1) B
  literal : ∀ P : Fin (I.attachment g).card → Label.{u},
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P d) →
    ∀ d, N.σ P (N.attEmb d) = P d
  capAgree : ∀ P P' : Fin (I.attachment g).card → Label.{u},
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P d) →
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ P' d) →
    (∀ d, P d ∈ codeGrid (j + 1) B) → ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h →
    (∀ d, min (P d) h = min (P' d) h) → ∀ z, min (N.σ P z) h = min (N.σ P' z) h
  readable : ∀ Q : Fin (I.attachment g).card → Label.{u}, orbitCode (j + 1) Q = Q →
    (∀ d, Q d ∈ codeGrid (j + 1) B) →
    (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun d ↦ Q d) →
    ∀ z, IsReadableAt (j + 1) Q (N.σ Q z)

/-- `1` is in the code grid of every grade `k ≥ 1`. -/
theorem one_mem_codeGrid {k B' : ℕ} (hk : 1 ≤ k) : (1 : Label.{u}) ∈ codeGrid k B' := by
  refine mem_codeGrid.mpr (.inr ⟨0, Nat.zero_le _, 1, hk, ?_⟩)
  simp

/-- A canonical state with a value of the natural key has an orbit key there. -/
theorem isOrbitKey_of_natural {K : ℕ} {Q : Fin (I.attachment g).card → Label.{u}}
    (hQ : orbitCode K Q = Q) {d : Fin (I.attachment g).card} (hd : Q d ≠ ⊥)
    (hk : visibilityReplace K K (Q d) = gridPoint K 0) : IsOrbitKey K Q (Q d) := by
  by_contra ho
  have hne := orbitCode_ne_even_of_not_isOrbitKey hd ho 0
  have hP : orbitCode K Q d = gridPoint K (codeBlock K Q (Q d)) := by
    rw [orbitCode_apply]; exact orbitMap_of_not_isOrbitKey hd ho
  have hsv : IsSelfVisible K (orbitCode K Q d) := hP ▸ isSelfVisible_gridPoint K _
  rw [show orbitCode K Q d = Q d from congrFun hQ d] at hsv hne
  exact hne (hsv.symm.trans hk)

/-- **The first level is good**, for `0 < H` and the attachment with at most `H` cells, at every
predicate. -/
theorem lvLevel1_good (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop) :
    (I.lvLevel1 g H).Good B A := by
  have hemb := Scheme.isLowerEmbedding_castAdd (S := (I.attachmentBase g).S) 1
    (Scheme.ladderCard (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    (Scheme.baseRow H (Scheme.rankProf (I.attachmentBase g).S H)) (I.attachmentBase g).noFull
  refine
    { wf := (I.attachmentBase g).isWellFormed_ladderBase H (by omega)
      consistent := (I.attachmentBase g).isConsistent_ladderBase H hH
      lowerEmb := hemb
      scope_attEmb := fun d ↦ Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d
      comap_rows := Scheme.comap_rows_castAdd (h := (I.attachmentBase g).noFull)
      mem_range := fun z hz ↦ ?_
      lawful := fun P hP hv _ ↦ ?_
      mem := fun P hP hP1 z ↦ ?_
      literal := fun P hP d ↦ ?_
      capAgree := fun P P' hP hP' _ h hh _ hag z ↦ ?_
      readable := fun Q hQ _ hQ1 z ↦ ?_ }
  · induction z using Fin.addCases with
    | left d => exact ⟨d, rfl⟩
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  · change (I.lvBase g H).rows.IsLawfulBelow _ fun z ↦ I.lvBaseSec g H P z
    rw [lvBaseSec_of_isLawfulBelow hcard hP]
    exact (I.attachmentBase g).isLawfulBelow_stateExtOf hH hcard le_rfl hP hv
  · change I.lvBaseSec g H P z ∈ _
    rw [lvBaseSec_of_isLawfulBelow hcard hP1]
    rcases Scheme.LadderBaseData.stateExtOf_cases P _ z with h | h | ⟨e, h⟩ <;> rw [h]
    · exact mem_insert_self _ _
    · exact one_mem_codeGrid (by omega)
    · exact hP e
  · change I.lvBaseSec g H P (Fin.castAdd _ d) = P d
    rw [lvBaseSec_of_isLawfulBelow hcard hP]
    exact Scheme.LadderBaseData.stateExtOf_castAdd' (B' := I.attachmentBase g) P _ d
  · change min (I.lvBaseSec g H P z) h = min (I.lvBaseSec g H P' z) h
    rw [lvBaseSec_of_isLawfulBelow hcard hP, lvBaseSec_of_isLawfulBelow hcard hP']
    by_cases h0 : h = ⊥
    · rw [h0, min_bot_right, min_bot_right]
    exact ((I.attachmentBase g).min_stateExtOf_eq hcard h0 (hh.mono (by omega)) hP hP'
      (fun d ↦ (hag d).symm) z).symm
  · change IsReadableAt 2 Q (I.lvBaseSec g H Q z)
    rw [lvBaseSec_of_isLawfulBelow hcard hQ1]
    rcases Scheme.LadderBaseData.stateExtOf_cases Q _ z with h | h | ⟨e, h⟩ <;> rw [h]
    · exact .inl rfl
    · refine .inr (.inr (by_cases (fun hkey ↦ .inl ?_) fun hkey ↦ .inr hkey))
      obtain ⟨e, he0, hek⟩ := hkey
      have h1 : visibilityReplace 2 2 (1 : Label.{u}) = gridPoint 2 0 :=
        visibilityReplace_one_eq_gridPoint le_rfl
      exact (isOrbitKey_congr hek).mp (isOrbitKey_of_natural hQ he0 (hek.trans h1))
    · exact isReadableAt_apply Q e

/-! ### The next level of a good level -/

/-- **The attachment lies in the two coatoms**: every cell of the attachment has its scope in the
context face `univ.erase (m + 1)` or in `univ.erase m`, which contains the donor face. -/
theorem scope_attachment_subset_coat (d : Fin (I.attachment g).card) :
    (I.attachment g).toCellScheme.scope d ⊆ ProfileTower.coatC ∨
      (I.attachment g).toCellScheme.scope d ⊆ ProfileTower.coatD := by
  rcases I.scope_attachment g d with h | h
  · exact .inl (h.trans (map_castSuccEmb_eq_ctxCoatom).le)
  · refine .inr (h.trans fun x hx ↦ mem_erase.mpr ⟨?_, mem_univ _⟩)
    rw [univ_map_extendByLast, mem_insert] at hx
    rcases hx with rfl | hx
    · exact last_ne_castSucc
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      obtain ⟨i, -, rfl⟩ := mem_map.mp hy
      intro h'
      have := congrArg Fin.val h'
      simp only [Function.Embedding.trans_apply, Fin.castSuccEmb_apply, Fin.val_castSucc,
        Fin.val_last] at this
      exact absurd this (g i).2.ne

/-- The attachment admission passes down one grade. -/
theorem attachAdmits_pred {d : StageType.{u} α (n + 1)}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} {k : ℕ} {R : Fin (I.attachment g).card → Label.{u}}
    (h : I.attachAdmits g hd Q (k + 1) R) : I.attachAdmits g hd Q k R :=
  fun hk ↦ h (by omega)

/-- **The orbit code at a grade `k` of an admitted state is admitted at `k`.** -/
theorem attachAdmits_orbitCode {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ}
    {P : Fin (I.attachment g).card → Label.{u}} (hP : I.attachAdmits g hd Q k P) :
    I.attachAdmits g hd Q k (orbitCode k P) := fun hk ↦
  attachAdmits_comp_of_le hd hQ hk hk hP (isWitness_orbitMap k P) (fun _ ↦ orbitMap_eq_bot_iff)
    k hk

namespace ALvl.Good

variable {j : ℕ} {N : I.ALvl g H j} {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

variable (hN : N.Good B (lvAdm hd Q))
include hN

theorem gradedIndex_attEmb (e : Fin (I.attachment g).card) :
    N.S.toCellScheme.gradedIndex (N.attEmb e) = (I.attachment g).toCellScheme.gradedIndex e :=
  Prod.ext (hN.scope_attEmb e) (hN.lowerEmb.grade_eq e)

/-- The attachment is a source prefix of a good level at every pair off the full face. -/
theorem isSourcePrefix {X : Finset (Fin (m + 2)) × ℕ} (hX : X.1 ≠ univ) :
    (I.attachment g).toCellScheme.IsSourcePrefix N.S.toCellScheme N.attEmb X :=
  ⟨hN.lowerEmb, hN.scope_attEmb, fun z hz ↦ hN.mem_range z fun he ↦
    hX (univ_subset_iff.mp (he ▸ hz.1))⟩

/-- Lawfulness below a pair off the full face is lawfulness on the attachment. -/
theorem isLawfulBelow_old_iff {X : Finset (Fin (m + 2)) × ℕ} (hX : X.1 ≠ univ)
    {w : Fin N.S.card → Label.{u}} :
    N.S.rows.IsLawfulBelow X (fun z ↦ w z) ↔
      (I.attachment g).rows.IsLawfulBelow X (fun e ↦ w (N.attEmb e)) := by
  have h := hN.isSourcePrefix hX
  rw [← h.isLawfulBelow_iff le_rfl, hN.comap_rows]
  rfl

/-- **The cover of `(univ, j + 1)`**: a cell of a good level below `(univ, j + 1)` lies below
`(univ, j)` or below one of the two coatoms at `j + 1`. -/
theorem mem_below_cover (z : Fin N.S.card)
    (hz : z ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), j + 1)) :
    z ∈ N.S.toCellScheme.below (ProfileTower.coatC, j + 1) ∨
      z ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), j) ∨
        z ∈ N.S.toCellScheme.below (ProfileTower.coatD, j + 1) := by
  by_cases hzg : N.S.toCellScheme.grade z ≤ j
  · exact .inr (.inl ⟨subset_univ _, hzg⟩)
  obtain ⟨e, rfl⟩ := hN.mem_range z ((N.inv z).resolve_left hzg)
  have he : (I.attachment g).toCellScheme.grade e ≤ j + 1 := by
    have := hz.2
    rwa [hN.gradedIndex_attEmb] at this
  rcases scope_attachment_subset_coat e with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, hN.gradedIndex_attEmb]; exact ⟨h, he⟩
  · refine .inr (.inr ?_)
    rw [CellScheme.mem_below, hN.gradedIndex_attEmb]; exact ⟨h, he⟩

theorem Φ_mem_codeGrid (C : Finset (Fin (I.attachment g).card → Label.{u}))
    {R : Fin (I.attachment g).card → Label.{u}} (hR : ∀ e, R e ∈ codeGrid (j + 1) B)
    (hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1) (fun e ↦ R e))
    (z : Fin (N.S.card + C.card)) : N.Φ B C R z ∈ codeGrid (j + 1) B := by
  induction z using Fin.addCases with
  | left e => rw [ALvl.Φ_castAdd]; exact hN.mem R hR hR1 e
  | right i =>
    rw [ALvl.Φ_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- **The row labelling of a state of the catalogue at `j + 1` is lawful below `(univ, j + 1)`**
in the scheme of the next level: below `(univ, j)` it is the section of the level
(`ALvl.Good.lawful`); below each coatom it reads the state on the attachment
(`ALvl.Good.literal`); at the new cells it reads agreement heights, kept by the capped agreement
of the section (`ALvl.Good.capAgree`), and is available at the cell of the state itself. -/
theorem isLawfulBelow_Φ {R : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ I.lvCat g B hd Q (j + 1)) :
    (N.nS B (I.lvCat g B hd Q (j + 1))).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j + 1)
      fun z ↦ N.Φ B (I.lvCat g B hd Q (j + 1)) R z := by
  classical
  set C := I.lvCat g B hd Q (j + 1) with hC
  obtain ⟨hRB, hRl, hRv, -, hRA⟩ := mem_lvCat.mp hR
  have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ R e) := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hlow : (N.nS B C).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun z ↦ N.Φ B C R z := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff (by rintro ⟨-, h⟩; simp only at h; omega)).mpr
      ?_
    simpa only [ALvl.Φ_castAdd] using hN.lawful R
      (hRl.mono (X := ((univ : Finset (Fin (m + 2))), j)) ⟨subset_rfl, by omega⟩) hRv
      (attachAdmits_pred hRA)
  have hcoat (x : Fin (m + 2)) :
      (N.nS B C).rows.IsLawfulBelow (univ.erase x, j + 1) fun z ↦ N.Φ B C R z := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff fun h ↦ ne_univ_erase x
      (univ_subset_iff.mp h.1)).mpr ?_
    simp only [ALvl.Φ_castAdd]
    rw [hN.isLawfulBelow_old_iff (ne_univ_erase x)]
    exact (Rows.isLawfulBelow_congr (w' := fun e ↦ N.σ R (N.attEmb e))
      fun e _ ↦ (hN.literal R hR1 e).symm).mp
        (hRl.mono (X := (univ.erase x, j + 1)) ⟨erase_subset _ _, le_rfl⟩)
  obtain ⟨ho2, hl2, ha2⟩ := Rows.isLawfulBelow_iff_forall.mp hlow
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp (hcoat (Fin.last (m + 1)))
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp (hcoat (Fin.castSucc (Fin.last m)))
  have hcases {e : Fin N.S.card}
      (he : Fin.castAdd C.card e ∈
        (N.nS B C).toCellScheme.below ((univ : Finset (Fin (m + 2))), j + 1)) :
      Fin.castAdd C.card e ∈ (N.nS B C).toCellScheme.below (ProfileTower.coatC, j + 1) ∨
        Fin.castAdd C.card e ∈
          (N.nS B C).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) ∨
        Fin.castAdd C.card e ∈ (N.nS B C).toCellScheme.below (ProfileTower.coatD, j + 1) := by
    have he' : e ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), j + 1) := by
      have := he
      rwa [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact hN.mem_below_cover e he'
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (C.equivFin.symm i₀).1 = R :=
    ⟨C.equivFin ⟨R, hR⟩, by simp⟩
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [hoC _ h, ho2 _ h, hoD _ h]
    | right i =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, ALvl.Φ_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hlC _ h, hl2 _ h, hlD _ h]
    | right i =>
      set κ := agreementHeight (grid (j + 1) B) R (C.equivFin.symm i).1 with hκ
      have hκm : κ ∈ grid (j + 1) B := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible (j + 1) κ := isSelfVisible_of_mem_grid hκm
      have hE := mem_lvCat.mp (C.equivFin.symm i).2
      refine ⟨constStepSuppressor (j + 1) κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : (N.nS B C).toCellScheme.grade t ≤ j + 1 := t.2.2.trans_eq
        (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd N.S (j + 1) _ i))
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, ALvl.Φ_natAdd]
      obtain ⟨t, -⟩ := t
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [ALvl.Φ_castAdd, ALvl.Φ_castAdd]
        exact hN.capAgree R (C.equivFin.symm i).1 hR1
          (hE.2.1.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩) hRB κ
          hκv (isShort_of_mem_grid hκm)
          (agreementHeight_spec (bot_mem_grid _ _) R (C.equivFin.symm i).1).2 e
      | right i' =>
        rw [ALvl.Φ_natAdd, ALvl.Φ_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [haC s _ h hst hg, ha2 s _ h hst hg, haD s _ h hst hg]
    | right i =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [ALvl.Φ_natAdd, hi₀, agreementHeight_self (gridPoint_mem_grid le_rfl)
        (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
      exact le_gridPoint_of_mem_codeGrid (hN.Φ_mem_codeGrid C hRB hR1 s)

/-- **The next level of a good level on the catalogue is good**: the scheme facts are those of the
layer appended to a good scheme; the section of a lawful admitted state is the upper decoder (a
witness bounded by `j + 1` sending only `⊥` to `⊥`) of the row labelling of its orbit code, a
state of the catalogue (`ALvl.Good.isLawfulBelow_Φ`); it is literal on the attachment (the upper
decoder reads the code back); it keeps capped agreement at the caps self-visible and short at
`j + 2` (`Label.min_upperDecoderAt_comp_eq_of_codes`, through the capped agreement of the level and
of the agreement heights at the caps short at `j + 1`); and it is readable at the canonical states
(`Label.isReadableAt_upperDecoderAt_of_mem`). -/
theorem next {p₀ : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀} (hQ : Q.ClassCalibrated hte)
    (hj : j + 1 ≤ m + 2) (hB : 2 * (I.attachment g).card ≤ B) :
    (N.next B (I.lvCat g B hd Q (j + 1))).Good B (lvAdm hd Q) := by
  classical
  set C := I.lvCat g B hd Q (j + 1) with hC
  have hemb := Scheme.isLowerEmbedding_castAdd (S := N.S) (j + 1) C.card
    (fun i ↦ N.Φ B C (C.equivFin.symm i).1) N.not_le
  have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by simpa using hB
  have hcode1 {P : Fin (I.attachment g).card → Label.{u}}
      (hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ P e)) :
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
        (fun e ↦ orbitCode (j + 1) P e) :=
    hP1.orbitCode fun e ↦ e.2.2.trans (by omega)
  have hcodeB (P : Fin (I.attachment g).card → Label.{u}) (e : Fin (I.attachment g).card) :
      orbitCode (j + 1) P e ∈ codeGrid (j + 1) B := orbitMap_mem_codeGrid hcB _
  refine
    { wf := Scheme.isWellFormed_appendFullCells (M := C.card)
        (r := fun i ↦ N.Φ B C (C.equivFin.symm i).1) (h := N.not_le) hN.wf (by omega) hj
      consistent := ?_
      lowerEmb := hemb.comp hN.lowerEmb
      scope_attEmb := fun e ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (hN.scope_attEmb e)
      comap_rows := ?_
      mem_range := fun z hz ↦ ?_
      lawful := fun P hP hv hA ↦ ?_
      mem := fun P hP hP1 z ↦ ?_
      literal := fun P hP1 e ↦ ?_
      capAgree := fun P P' hP hP' hPB h hh hs hag z ↦ ?_
      readable := fun Q' hQ' hQB hQ1 z ↦ ?_ }
  · -- consistency
    change (N.nS B C).rows.IsConsistent
    intro s
    induction s using Fin.addCases with
    | right i =>
      have hu := Scheme.appendFullCellsScheme_gradedIndex_natAdd N.S (j + 1) C.card i
      have h := hN.isLawfulBelow_Φ (C.equivFin.symm i).2
      change (N.nS B C).rows.IsLawfulBelow ((N.nS B C).toCellScheme.gradedIndex (Fin.natAdd _ i))
        ((N.nS B C).rows.row (Fin.natAdd _ i))
      rw [Scheme.appendFullCells_row_natAdd_eq]
      rw [show (N.nS B C).toCellScheme.gradedIndex (Fin.natAdd _ i) =
        ((univ : Finset (Fin (m + 2))), j + 1) from hu]
      exact h
    | left s =>
      refine (CellScheme.Rows.isLawfulBelow_comap_iff hemb (hemb.image_below_gradedIndex s)).mp ?_
      rw [Scheme.comap_rows_castAdd]
      convert hN.consistent s using 1
      funext t
      exact congrArg (fun R : N.S.toCellScheme.Rows ↦ R.row s t) Scheme.comap_rows_castAdd
  · -- the rows on the attachment
    have h := Rows.comap_comap (N.nS B C).rows hemb hN.lowerEmb
    rw [Scheme.comap_rows_castAdd, hN.comap_rows] at h
    exact h.symm
  · -- the cells of proper scope
    induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left e =>
      have hz' : N.S.toCellScheme.scope e ≠ univ := by
        have := (Scheme.appendFullCellsScheme_scope_castAdd N.S (j + 1) C.card e)
        exact fun h ↦ hz (this.trans h)
      obtain ⟨e', rfl⟩ := hN.mem_range e hz'
      exact ⟨e', rfl⟩
  · -- lawful
    have hQC : orbitCode (j + 1) P ∈ C := mem_lvCat.mpr ⟨hcodeB P, hP.orbitCode fun e ↦ e.2.2,
      fun e ↦ isSelfVisible_one_orbitCode (by omega) (hv e), orbitCode_orbitCode,
      attachAdmits_orbitCode hQ hA⟩
    exact (hN.isLawfulBelow_Φ hQC).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_upperDecoderAt (w := P) (B := B) (K := j + 2) (by omega))
      (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
  · -- mem
    exact upperDecoderAt_mem_codeGrid_of_mem (by omega) hP
      (hN.Φ_mem_codeGrid C (hcodeB P) (hcode1 hP1) z)
  · -- literal
    change upperDecoderAt (j + 1) (j + 2) B P
      (N.Φ B C (orbitCode (j + 1) P) (Fin.castAdd _ (N.attEmb e))) = P e
    rw [ALvl.Φ_castAdd, hN.literal _ (hcode1 hP1)]
    exact upperDecoderAt_orbitCode e
  · -- capped agreement
    refine min_upperDecoderAt_comp_eq_of_codes (k := j + 1) (K := j + 2) (by omega) hh hs
      (fun e ↦ le_gridPoint_of_mem_codeGrid (hPB e)) hag (N.Φ B C)
      (fun Γ hΓ hΓs hcc z ↦ ?_) z
    induction z using Fin.addCases with
    | left e =>
      rw [ALvl.Φ_castAdd, ALvl.Φ_castAdd]
      exact hN.capAgree _ _ (hcode1 hP) (hcode1 hP') (hcodeB P) Γ hΓ hΓs hcc e
    | right i =>
      rw [ALvl.Φ_natAdd, ALvl.Φ_natAdd]
      exact min_agreementHeight_eq_of_isShort hΓ hΓs (fun e ↦ ⟨hcodeB P e, hcodeB P' e⟩) hcc _
  · -- readable
    exact isReadableAt_upperDecoderAt_of_mem hQ' (by omega) hQB (fun e ↦ isReadableAt_apply Q' e)
      (hN.Φ_mem_codeGrid C (hcodeB Q') (hcode1 hQ1) z)

end ALvl.Good

end Seed

end VaughtConjecture

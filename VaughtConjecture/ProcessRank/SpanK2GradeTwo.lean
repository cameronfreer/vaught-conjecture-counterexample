/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevel
import VaughtConjecture.ProcessRank.SpanK2Ladder

/-!
# The grade-two catalogue and the controller readings for the attachment of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the first grade at which admission
constrains the construction.

**States and admission.**  A state is a labelling `R` of the eight cells of the attachment
`ProcessRank.k2Attachment`.  Its fields are read on the two copies through
`ProcessRank.attField` (`Sum.inl i` the cell `i` of `{0, 1}`, `Sum.inr i` its copy on `{2, 3}`),
and it is admitted at the grade `2` for the top cells `ProcessRank.k2Tops = {c₀, c₀₁, a}` of the
test types with `K = 2` (`ProcessRank.IsAdmitted`).

**The catalogue** (`ProcessRank.k2Cat2`): the states in the code grid `codeGrid 2 16`, lawful
below `(univ, 2)` on the attachment, with values self-visible at the grade one, canonical for the
orbit code at the grade two, and admitted at the grade two.  The grid bound `16` is twice the number
of cells; the ladder height stays `8`.

**The controller row** (`ProcessRank.k2ControllerRow`) of a state lawful below `(univ, 1)` is the
extension of the state to the ladder with its own rank member
(`Scheme.LadderBaseData.stateExtOf`, `Scheme.RankMember.ofLawfulBelowOne`): the state on the
attachment, the positive table of the state at the ladder indices of the member on the ladder
points.  For a catalogue state it is lawful below `(univ, 2)` on the ladder
(`ProcessRank.isLawfulBelow_k2ControllerRow`).

**The factorization** (`ProcessRank.k2ControllerRow_factor`, `ProcessRank.k2Cat2_factor`): the
readings of the controller row on the ladder points and on the attachment cells factor through
one rank member `b` and one monotone table `Φ` with `Φ 0 = ⊥` (the positive table of the state).

**A separated admitted state** (`ProcessRank.k2SepState`, the orbit code at the grade two of the
attachment row): it lies in the catalogue, is separated, and its two copies agree on the
designated cells (`ProcessRank.k2SepState_mem`, `ProcessRank.isSeparated_k2SepState`,
`ProcessRank.k2SepState_agree`), and its controller row reads the two copies of every designated
cell equally (`ProcessRank.k2ControllerRow_k2SepState_agree`).

Open: shadows and twins, the controllers of grades three and four, legality of a master scheme over
the attachment, and the four-point span of mutual rigidity of the test pair.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- The cell of the attachment carrying a field: `Sum.inl i` on `{0, 1}`, `Sum.inr i` on
`{2, 3}`. -/
def attField : Fin 4 ⊕ Fin 4 → Fin k2AttachmentBase.{u}.S.card :=
  Sum.elim (fun i ↦ ⟨i, by change _ < 8; omega⟩) fun i ↦ ⟨i + 4, by change _ < 8; omega⟩

/-- The attachment has at most eight cells. -/
theorem k2_card_le : k2AttachmentBase.{u}.S.card ≤ 8 := le_rfl

/-- The rank vector of the rank member of a state lawful below `(univ, 1)` is the rank vector of
the state. -/
theorem rankProf_ofLawfulBelowOne {n H : ℕ} {S : Scheme.{u} n} (hwf : S.IsWellFormed)
    (hcard : S.card ≤ H) {R : Fin S.card → Label.{u}}
    (hR : S.rows.IsLawfulBelow ((univ : Finset (Fin n)), 1) fun d ↦ R d) (d : Fin S.card) :
    Scheme.rankProf S H (Scheme.RankMember.ofLawfulBelowOne hwf hcard hR) d = rankVector R d :=
  rfl

/-- The top cells of the test types with `K = 2`: `c₀`, `c₀₁` and the apex. -/
def k2Tops : Set (Fin 4) := {0, 2, 3}

open Classical in
/-- **The grade-two catalogue**: the states in `codeGrid 2 16`, lawful below `(univ, 2)` on the
attachment, with values self-visible at the grade one, canonical for the orbit code at the grade
two, and admitted at the grade two for the top cells `{c₀, c₀₁, a}` with `K = 2`. -/
noncomputable def k2Cat2 : Finset (Fin k2AttachmentBase.{u}.S.card → Label.{u}) :=
  (Fintype.piFinset fun _ ↦ codeGrid 2 16).filter fun R ↦
    k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) (fun e ↦ R e) ∧
      (∀ e, IsSelfVisible 1 (R e)) ∧ orbitCode 2 R = R ∧
      IsAdmitted k2Tops 2 2 fun x ↦ R (attField x)

theorem mem_k2Cat2 {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} :
    R ∈ k2Cat2 ↔ (∀ e, R e ∈ codeGrid 2 16) ∧
      k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) (fun e ↦ R e) ∧
      (∀ e, IsSelfVisible 1 (R e)) ∧ orbitCode 2 R = R ∧
      IsAdmitted k2Tops 2 2 fun x ↦ R (attField x) := by
  classical
  simp only [k2Cat2, mem_filter, Fintype.mem_piFinset]

open Classical in
/-- **The controller row** of a state: for a state lawful below `(univ, 1)`, its extension to the
ladder with its own rank member; `⊥` otherwise. -/
noncomputable def k2ControllerRow (R : Fin k2AttachmentBase.{u}.S.card → Label.{u}) :
    Fin k2Ladder.{u}.card → Label.{u} :=
  if h : k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1) (fun e ↦ R e) then
    k2AttachmentBase.stateExtOf R
      (Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le h)
  else fun _ ↦ ⊥

theorem k2ControllerRow_of_isLawfulBelow {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (h : k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1) (fun e ↦ R e)) :
    k2ControllerRow R = k2AttachmentBase.stateExtOf R
      (Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le h) :=
  dite_eq_left h

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex 8 (Scheme.rankProf k2AttachmentBase.S 8) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))

/-- The cell of the ladder of a ladder point. -/
noncomputable def k2LadPt
    (v : Scheme.LadderPt k2AttachmentBase.{u}.S (Scheme.RankMember k2AttachmentBase.{u}.S 8) 8) :
    Fin k2Ladder.{u}.card :=
  Fin.natAdd _ (Scheme.ladderEquiv _ _ 8 v)

/-- **The controller readings factor through one rank member and one table**: for a state lawful
below `(univ, 1)` with values self-visible at the grade one, the controller row reads every ladder
point `v` as `Φ (idx b v)` and every attachment cell `e` as `Φ (rankProf b e)`, for the rank member
`b` of the state and its positive table `Φ`, monotone with `Φ 0 = ⊥`. -/
theorem k2ControllerRow_factor {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (h : k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1) (fun e ↦ R e))
    (hv : ∀ e, IsSelfVisible 1 (R e)) :
    ∃ (b : Scheme.RankMember k2AttachmentBase.{u}.S 8) (Φ : ℕ → Label.{u}), Monotone Φ ∧ Φ 0 = ⊥ ∧
      (∀ v, k2ControllerRow R (k2LadPt v) = Φ (idx b v)) ∧
      ∀ e, k2ControllerRow R (Fin.castAdd _ e) = Φ (Scheme.rankProf k2AttachmentBase.S 8 b e) := by
  refine ⟨Scheme.RankMember.ofLawfulBelowOne (H := 8) k2AttachmentBase.wf k2_card_le h,
    posTable R, monotone_posTable, posTable_zero, fun v ↦ ?_, fun e ↦ ?_⟩
  · rw [k2ControllerRow_of_isLawfulBelow h, k2LadPt]
    change Fin.append R _ (Fin.natAdd _ _) = _
    rw [Fin.append_right, Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
  · rw [k2ControllerRow_of_isLawfulBelow h, Scheme.LadderBaseData.stateExtOf_castAdd',
      rankProf_ofLawfulBelowOne]
    exact (posTable_rankVector hv e).symm

/-- A state lawful below `(univ, 2)` is lawful below `(univ, 1)`. -/
theorem isLawfulBelow_one_of_two {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (hl : k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) (fun e ↦ R e)) :
    k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1) (fun e ↦ R e) :=
  hl.mono (X := ((univ : Finset (Fin 4)), 1)) ⟨subset_rfl, by decide⟩

/-- **The controller row of a catalogue state is lawful below `(univ, 2)` on the ladder**
(`Scheme.LadderBaseData.isLawfulBelow_stateExtOf`). -/
theorem isLawfulBelow_k2ControllerRow {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}}
    (hR : R ∈ k2Cat2) :
    k2Ladder.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) fun t ↦ k2ControllerRow R t := by
  obtain ⟨-, hl, hv, -, -⟩ := mem_k2Cat2.mp hR
  have h := Scheme.LadderBaseData.isLawfulBelow_stateExtOf (B := k2AttachmentBase) (H := 8)
    (by decide) k2_card_le (k := 2) (by decide) hl hv
  simp only [k2ControllerRow_of_isLawfulBelow (isLawfulBelow_one_of_two hl)]
  exact h

/-- **The factorization for every catalogue state.** -/
theorem k2Cat2_factor {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hR : R ∈ k2Cat2) :
    ∃ (b : Scheme.RankMember k2AttachmentBase.{u}.S 8) (Φ : ℕ → Label.{u}), Monotone Φ ∧ Φ 0 = ⊥ ∧
      (∀ v, k2ControllerRow R (k2LadPt v) = Φ (idx b v)) ∧
      ∀ e, k2ControllerRow R (Fin.castAdd _ e) = Φ (Scheme.rankProf k2AttachmentBase.S 8 b e) := by
  obtain ⟨-, hl, hv, -, -⟩ := mem_k2Cat2.mp hR
  exact k2ControllerRow_factor (isLawfulBelow_one_of_two hl) hv

/-! ### A separated admitted state -/

/-- **A separated admitted state**: the orbit code at the grade two of the attachment row. -/
noncomputable def k2SepState : Fin k2AttachmentBase.{u}.S.card → Label.{u} :=
  orbitCode 2 fun e ↦ attRow e

/-- A field is designated for the top cells `{c₀, c₀₁, a}` exactly when its cell is one of them. -/
theorem isDesignated_k2Tops_iff (x : Fin 4 ⊕ Fin 4) :
    IsDesignated k2Tops x ↔ fieldCell x = 0 ∨ fieldCell x = 2 ∨ fieldCell x = 3 :=
  Iff.rfl

/-- The attachment row at a field is the test row at its cell. -/
theorem attRow_attField (x : Fin 4 ⊕ Fin 4) : attRow.{u} (attField x) = testRow (fieldCell x) := by
  rcases x with d | d <;> exact congrArg testRow (Fin.ext (by simp [attField, attCell]))

/-- **The attachment row is separated** for the top cells `{c₀, c₀₁, a}`: the designated cells
read `ω * 2 + 1` or `ω * 2 + 2`, the cell `c₁` reads `ω + 1`. -/
theorem isSeparated_attRow : IsSeparated k2Tops fun x ↦ attRow.{u} (attField x) := by
  have h₁ := omega0_add_one_lt.{u}
  have h₂ := omega0_mul_two_add_one_le.{u}
  intro x hx
  dsimp only
  rw [attRow_attField]
  refine ⟨bot_lt_iff_ne_bot.mpr (testRow_ne_bot _), fun y hy ↦ ?_⟩
  rw [attRow_attField]
  rw [isDesignated_k2Tops_iff] at hx hy
  have hy1 : fieldCell y = 1 := (by decide : ∀ e : Fin 4, ¬ (e = 0 ∨ e = 2 ∨ e = 3) → e = 1) _ hy
  rw [hy1]
  rcases hx with h | h | h <;> rw [h]
  · exact h₁
  · exact h₁
  · exact h₁.trans_le h₂

/-- **The attachment row is admitted**: its two copies agree on every cell. -/
theorem isAdmitted_attRow : IsAdmitted k2Tops 2 2 fun x ↦ attRow.{u} (attField x) :=
  fun _ _ d _ ↦ by dsimp only; rw [attRow_attField, attRow_attField]; rfl

/-- **The separated admitted state lies in the grade-two catalogue.** -/
theorem k2SepState_mem : k2SepState.{u} ∈ k2Cat2 := by
  have hl : k2AttachmentBase.{u}.S.rows.IsLawful fun e ↦ attRow e := isLawful_attRow
  refine mem_k2Cat2.mpr ⟨fun e ↦ orbitMap_mem_codeGrid (by decide) _, ?_, fun e ↦ ?_,
    orbitCode_orbitCode, ?_⟩
  · exact (hl.isLawfulBelow _).orbitCode fun d ↦ d.2.2
  · exact isSelfVisible_one_orbitCode (by decide) (k2AttachmentBase.isSelfVisible_one_of_isLawful
      hl e)
  · exact (isAdmitted_iff_of_le_iff (fun _ _ ↦ orbitCode_le_iff) fun _ ↦ orbitCode_eq_bot_iff).mpr
      isAdmitted_attRow

/-- **The separated admitted state is separated.** -/
theorem isSeparated_k2SepState : IsSeparated k2Tops fun x ↦ k2SepState.{u} (attField x) :=
  (isSeparated_iff_of_le_iff (fun _ _ ↦ orbitCode_le_iff) fun _ ↦ orbitCode_eq_bot_iff).mpr
    isSeparated_attRow

/-- **Agreement on the designated cells**: the two copies of every designated cell carry equal
values in the separated admitted state, as its admission requires. -/
theorem k2SepState_agree {d : Fin 4} (hd : d ∈ k2Tops) :
    k2SepState.{u} (attField (Sum.inl d)) = k2SepState (attField (Sum.inr d)) :=
  (mem_k2Cat2.mp k2SepState_mem).2.2.2.2 le_rfl isSeparated_k2SepState d hd

/-- **The controller row reads the two copies of a designated cell equally** at a separated
catalogue state: the row is the state on the attachment, and admission makes the copies equal. -/
theorem k2ControllerRow_agree {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hR : R ∈ k2Cat2)
    (hsep : IsSeparated k2Tops fun x ↦ R (attField x)) {d : Fin 4} (hd : d ∈ k2Tops) :
    k2ControllerRow R (Fin.castAdd _ (attField (Sum.inl d))) =
      k2ControllerRow R (Fin.castAdd _ (attField (Sum.inr d))) := by
  obtain ⟨-, hl, -, -, hA⟩ := mem_k2Cat2.mp hR
  rw [k2ControllerRow_of_isLawfulBelow (isLawfulBelow_one_of_two hl),
    Scheme.LadderBaseData.stateExtOf_castAdd', Scheme.LadderBaseData.stateExtOf_castAdd']
  exact hA le_rfl hsep d hd

/-- **The test**: the controller row of the separated admitted state reads the two copies of every
designated cell equally. -/
theorem k2ControllerRow_k2SepState_agree {d : Fin 4} (hd : d ∈ k2Tops) :
    k2ControllerRow k2SepState.{u} (Fin.castAdd _ (attField (Sum.inl d))) =
      k2ControllerRow k2SepState (Fin.castAdd _ (attField (Sum.inr d))) :=
  k2ControllerRow_agree k2SepState_mem isSeparated_k2SepState hd

end VaughtConjecture.ProcessRank

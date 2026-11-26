/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2MixedLifts

/-!
# The grade-three section on the grade-two scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the sections on the grade-two scheme
`ProcessRank.k2Grade2` of the states of the grade-three catalogue, the readings the grade-three
cells will carry on the old cells, following the next level of the replicated construction
(`Seed.ALvl.Good.next`), at the block bound `16` with no new cells.

**The grade-three catalogue** (`ProcessRank.k2Cat3`): the states `P` on the eight attachment
cells with values in `codeGrid 3 16`, lawful below `(univ, 3)`, with values self-visible at the
grade one, canonical for the orbit code at the grade three (`orbitCode 3 P = P`), and admitted at
the grade three for the top cells `{c₀, c₀₁, a}` with `K = 2` (`IsAdmitted k2Tops 2 3`), as the
grade-two catalogue `ProcessRank.k2Cat2` one grade up.  Compiled here (theorem named):
* the code at the grade three of the attachment labels lies in the catalogue
  (`ProcessRank.k2Code3_mem`): the concrete grade-three state of this attachment, to which the
  results below apply;
* the orbit code `C = orbitCode 2 P` of such a state lies in the grade-two catalogue
  (`ProcessRank.orbitCode_mem_k2Cat2`);
* the **section** of `P` (`ProcessRank.k2Sec3`) is the upper decoder of `P`, at the grade two with
  cap grade three and block bound `16`, applied to the row of `C`.  It is lawful on `k2Grade2`
  (`ProcessRank.isLawful_k2Sec3`) and reads `P` on the attachment cells
  (`ProcessRank.k2Sec3_att`);
* **one-member reading** (`ProcessRank.k2Sec3_readMember`): the section reads the ladder and the
  attachment through the rank member of `C` and one monotone table with `⊥` at `0`;
* **cross-grade shadow** (`ProcessRank.k2Sec3_shadow`): the hypothesis `hshadow` of
  `ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for a cell reading the old cells through
  the section, against every cell of full scope of `k2Grade2` at the grade two.  It is the
  grade-two shadow of the controller rows of `C` (`ProcessRank.k2ControllerRow_shadow`) through
  the monotone upper decoder;
* **controller domination** (`ProcessRank.le_k2Sec3_controller`, and in the form of the
  hypothesis `htwinAbove`, `ProcessRank.k2Sec3_twinAbove`): the controller of `C` is read by the
  section at least `P e` at every attachment cell `e`.  The controller reads itself as the top
  `gridPoint 2 16` of the grid (`Label.agreementHeight_self`), the code `C e` lies below it, the
  decoder is monotone and decodes `C e` as `P e`.

Open: the grade-three cells and their consistency, the grade four, legality of the completed
scheme, the four-point span of mutual rigidity of the test pair, and the countable upper bound on
the Scott classes.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label MirrorAttachment
open scoped Ordinal

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex 8 (Scheme.rankProf k2AttachmentBase.S 8) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))

/-! ### The grade-three catalogue -/

open Classical in
/-- **The grade-three catalogue**: the states in `codeGrid 3 16`, lawful below `(univ, 3)` on the
attachment, with values self-visible at the grade one, canonical for the orbit code at the grade
three, and admitted at the grade three for the top cells `{c₀, c₀₁, a}` with `K = 2`.  It is
irreducible and used through `ProcessRank.mem_k2Cat3`: unfolding it during elaboration exceeds
the recursion limit. -/
@[irreducible] noncomputable def k2Cat3 : Finset (Fin k2AttachmentBase.{u}.S.card → Label.{u}) :=
  (Fintype.piFinset fun _ ↦ codeGrid 3 16).filter fun P ↦
    k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun e ↦ P e) ∧
      (∀ e, IsSelfVisible 1 (P e)) ∧ orbitCode 3 P = P ∧
      IsAdmitted k2Tops 2 3 fun x ↦ P (attField x)

theorem mem_k2Cat3 {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} :
    P ∈ k2Cat3 ↔ (∀ e, P e ∈ codeGrid 3 16) ∧
      k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun e ↦ P e) ∧
      (∀ e, IsSelfVisible 1 (P e)) ∧ orbitCode 3 P = P ∧
      IsAdmitted k2Tops 2 3 fun x ↦ P (attField x) := by
  classical
  unfold k2Cat3
  rw [mem_filter, Fintype.mem_piFinset]

/-- **The orbit code at the grade two of a grade-three state lies in the grade-two catalogue.** -/
theorem orbitCode_mem_k2Cat2 {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    orbitCode 2 P ∈ k2Cat2 := by
  obtain ⟨-, hl, hv, -, hA⟩ := mem_k2Cat3.mp hP
  have hl2 : k2AttachmentBase.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) (fun e ↦ P e) :=
    hl.mono (X := ((univ : Finset (Fin 4)), 2)) ⟨subset_rfl, by decide⟩
  refine mem_k2Cat2.mpr ⟨fun e ↦ orbitMap_mem_codeGrid (by decide) _,
    hl2.orbitCode fun d ↦ d.2.2, fun e ↦ isSelfVisible_one_orbitCode (by decide) (hv e),
    orbitCode_orbitCode, ?_⟩
  exact (isAdmitted_iff_of_le_iff (fun _ _ ↦ orbitCode_le_iff) fun _ ↦ orbitCode_eq_bot_iff).mpr
    (hA.mono (by decide))

/-- The labels of the attachment at the fields, at the grade three: the two copies of each top
cell read `⊤`. -/
theorem isAdmitted_three_k2AttLabel :
    IsAdmitted k2Tops 2 3 fun x ↦ k2AttLabel.{u} (attField x) := by
  intro _ _ d hd
  rcases hd with rfl | rfl | rfl <;> rfl

/-- The **code at the grade three of the attachment labels**. -/
noncomputable def k2Code3 : Fin k2AttachmentBase.{u}.S.card → Label.{u} :=
  orbitCode 3 fun e ↦ k2AttLabel e

/-- **The code at the grade three of the attachment labels lies in the grade-three catalogue**:
the concrete grade-three state of this attachment, so the results on sections below apply to it. -/
theorem k2Code3_mem : k2Code3.{u} ∈ k2Cat3 := by
  have hl : k2AttachmentBase.{u}.S.rows.IsLawful fun e ↦ k2AttLabel e := isLawful_k2AttLabel
  refine mem_k2Cat3.mpr ⟨fun e ↦ orbitMap_mem_codeGrid (by decide) _, ?_, fun e ↦ ?_,
    orbitCode_orbitCode, ?_⟩
  · exact (hl.isLawfulBelow _).orbitCode fun d ↦ d.2.2
  · exact isSelfVisible_one_orbitCode (by decide) (k2AttachmentBase.isSelfVisible_one_of_isLawful
      hl e)
  · exact (isAdmitted_iff_of_le_iff (fun _ _ ↦ orbitCode_le_iff) fun _ ↦ orbitCode_eq_bot_iff).mpr
      isAdmitted_three_k2AttLabel

/-! ### The section -/

/-- **The section of a state** on the grade-two scheme: the upper decoder of the state, at the
grade two with cap grade three and block bound `16`, applied to the row of its orbit code at the
grade two. -/
noncomputable def k2Sec3 (P : Fin k2AttachmentBase.{u}.S.card → Label.{u})
    (z : Fin k2Grade2.{u}.card) : Label.{u} :=
  upperDecoderAt 2 3 16 P (k2Phi (orbitCode 2 P) z)

/-- The upper decoder at the grade two with cap grade three is monotone and fixes `⊥`. -/
theorem isWitness_k2Decoder (P : Fin k2AttachmentBase.{u}.S.card → Label.{u}) :
    IsWitness (stepSuppressor.{u} 2) (upperDecoderAt 2 3 16 P) :=
  isWitness_upperDecoderAt (by decide)

/-- **The section of a grade-three state is lawful on the grade-two scheme.** -/
theorem isLawful_k2Sec3 {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    k2Grade2.{u}.rows.IsLawful (k2Sec3 P) :=
  (isLawful_k2Phi (orbitCode_mem_k2Cat2 hP)).map_of_apply_eq_bot k2Grade2_grade_le
    (isWitness_k2Decoder P) fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot

/-- The row of a catalogue state reads an attachment cell as the state. -/
theorem k2Phi_att {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hR : R ∈ k2Cat2)
    (e : Fin k2AttachmentBase.{u}.S.card) : k2Phi R (k2Att e) = R e := by
  obtain ⟨-, hl, -, -, -⟩ := mem_k2Cat2.mp hR
  rw [k2Phi_castAdd, k2ControllerRow_of_isLawfulBelow (isLawfulBelow_one_of_two hl),
    Scheme.LadderBaseData.stateExtOf_castAdd']

/-- **The section reads the state on the attachment cells** (`Label.upperDecoderAt_orbitCode`). -/
theorem k2Sec3_att {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3)
    (e : Fin k2AttachmentBase.{u}.S.card) : k2Sec3 P (k2Att e) = P e := by
  unfold k2Sec3
  rw [k2Phi_att (orbitCode_mem_k2Cat2 hP)]
  exact upperDecoderAt_orbitCode e

/-! ### The row conditions across the grades -/

/-- **The one-member reading of the section**: the section reads the ladder points and the
attachment cells through the rank member of the orbit code and one monotone table with `⊥` at
`0`, in the form of the hypothesis `hreadMember` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed`. -/
theorem k2Sec3_readMember {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    ∃ (b : Scheme.RankMember k2AttachmentBase.{u}.S 8) (Φ : ℕ → Label.{u}), Monotone Φ ∧
      Φ 0 = ⊥ ∧ (∀ v, k2Sec3 P (k2Lad v) = Φ (idx b v)) ∧
      ∀ e, k2Sec3 P (k2Att e) = Φ (Scheme.rankProf k2AttachmentBase.S 8 b e) := by
  obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := k2Cat2_factor (orbitCode_mem_k2Cat2 hP)
  have hw := isWitness_k2Decoder P
  refine ⟨b, upperDecoderAt 2 3 16 P ∘ Φ, hw.monotone.comp hΦ, by
    rw [Function.comp_apply, hΦ0, hw.map_bot], fun v ↦ ?_, fun e ↦ ?_⟩
  · unfold k2Sec3
    rw [k2Phi_castAdd, hl]
    rfl
  · unfold k2Sec3
    rw [k2Phi_castAdd, ha]
    rfl

/-- **The cross-grade shadow**: the hypothesis `hshadow` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for a cell of full scope at the grade three
reading the old cells through the section of a grade-three state, against the cells of full scope
of the grade-two scheme.  For every such cell `u` at a grade `k` with `2 ≤ k ≤ 3` and every
attachment cell `e` of grade `k`, a ladder point `v` is read by `u` as `e`, and by the section as
`e` at the cap read by the section at `u`. -/
theorem k2Sec3_shadow {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    ∀ (u : Fin k2Grade2.{u}.card) k,
      k2Grade2.{u}.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), k) → 2 ≤ k → k ≤ 3 →
      ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e = k → ∃ v,
        k2Grade2.{u}.rowAt u (k2Lad v) = k2Grade2.{u}.rowAt u (k2Att e) ∧
        min (k2Sec3 P (k2Lad v)) (k2Sec3 P u) = min (k2Sec3 P (k2Att e)) (k2Sec3 P u) := by
  intro u k hu hk2 _ e _
  obtain ⟨-, i', rfl⟩ := exists_natAdd_of_gradedIndex hu hk2
  obtain ⟨v, h1, h2⟩ := k2ControllerRow_shadow (orbitCode_mem_k2Cat2 hP)
    (k2Cat2.equivFin.symm i').2 e
  have hm := (isWitness_k2Decoder P).monotone
  refine ⟨v, ?_, ?_⟩
  · rw [k2Grade2_rowAt_natAdd_castAdd, k2Grade2_rowAt_natAdd_castAdd]
    exact h1
  · unfold k2Sec3
    rw [k2Phi_castAdd, k2Phi_castAdd, k2Phi_natAdd, ← hm.map_min, ← hm.map_min, h2]

/-- **Controller domination**: the controller of the orbit code of a grade-three state is read by
the section of the state at least the state at every attachment cell. -/
theorem le_k2Sec3_controller {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3)
    (e : Fin k2AttachmentBase.{u}.S.card) :
    P e ≤ k2Sec3 P (Fin.natAdd _ (k2Cat2.equivFin ⟨orbitCode 2 P, orbitCode_mem_k2Cat2 hP⟩)) := by
  have hC := orbitCode_mem_k2Cat2 hP
  rw [← k2Sec3_att hP e]
  unfold k2Sec3
  rw [k2Phi_natAdd, Equiv.symm_apply_apply, agreementHeight_self (gridPoint_mem_grid le_rfl)
    (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
  exact (isWitness_k2Decoder P).monotone
    (le_gridPoint_of_mem_codeGrid (k2Phi_mem_codeGrid hC (k2Att e)))

/-- **Controller domination**, in the form of the hypothesis `htwinAbove` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for a cell reading the old cells through the
section: at every grade `k` with `2 ≤ k ≤ 3` and every attachment cell `e` of grade `k`, a cell of
full scope at the grade `k` is read by the section at least as `e`.  The attachment has no cell of
grade three, so `k = 2`, and the cell is the controller of the orbit code. -/
theorem k2Sec3_twinAbove {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    ∀ k, 2 ≤ k → k ≤ 3 → ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e = k →
      ∃ et, k2Grade2.{u}.toCellScheme.gradedIndex et = ((univ : Finset (Fin 4)), k) ∧
        k2Sec3 P (k2Att e) ≤ k2Sec3 P et := by
  intro k hk2 _ e he
  have hk : k = 2 := by
    have hle : k2AttachmentBase.{u}.S.toCellScheme.grade e ≤ 2 :=
      (by decide : ∀ d : Fin 8, attGrade d ≤ 2) e
    omega
  subst hk
  refine ⟨Fin.natAdd _ (k2Cat2.equivFin ⟨orbitCode 2 P, orbitCode_mem_k2Cat2 hP⟩),
    k2Grade2_gradedIndex_natAdd _, ?_⟩
  rw [k2Sec3_att hP e]
  exact le_k2Sec3_controller hP e

end VaughtConjecture.ProcessRank

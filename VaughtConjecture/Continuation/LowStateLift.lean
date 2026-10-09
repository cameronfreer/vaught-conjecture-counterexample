/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateTower

/-!
# The capped lift of a state layer from the state step

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the lifts of the state
tower); semantic contract, items 3 and 8.

The lifts of the state tower (`ProfileTower.STowerLifts`) are the hypothesis of the LOW displays
on the families whose state tower lifts (`StageType.hasLowDisplaysOn_stateLifts`).  This file
reduces the lift of every layer of the state tower to a **state step** on the amalgam, the state
form of the catalogue step of `VaughtConjecture.Extension.TowerCatalogueLayer`.

**Readability at the states** (`ProfileTower.SLvl.ReadableS`).  The extension through a state
layer at a positive cap decodes the row of the orbit code `Q` of a state over all fields with the
orbit decoder of the state at the cap, and needs the section of the level at `Q` read literally
below the cap: readable for `Q`.  `ProfileTower.SLvl.Good` asks readability only at the states with
the cutoff `⊥` (what the forgetful level needs); the extension needs it at every canonical state.
It holds at every next state level (`ProfileTower.SLvl.Good.readableS_next`) and at a canonical
next level read as a state level (`ProfileTower.Lvl.Good.readableS_toS_next`), since both sections
are upper decoders of splices of the state, readable for any canonical reader whose values they
take (`Label.isReadableAt_upperDecoderAt_of_mem`); compiled in this repository.

**The extension through a state layer** (`ProfileTower.SLvl.Good.exists_extension_s`,
`ProfileTower.SLvl.Good.exists_extension_s_bot`, compiled in this repository): as for the
catalogue layer, with the orbit code over all fields of the state `withCut W β` in place of the
orbit code of `W` with the cutoff `β`; the serving state is canonical over all fields, so the code
agrees with it capped at the cap (`Label.min_orbitCode_eq` over the fields).

**The state step** (`ProfileTower.SLvl.SCatStep`) and **the lift**
(`ProfileTower.SLvl.Good.cappedLift_sS`, compiled in this repository): at every state `P` of the
catalogue and every positive cap self-visible and short at `g + 1`, every labelling lawful below the
coatom agreeing there with `P` capped at the cap is, at the amalgam cells below the coatom, an
amalgam profile `W` lawful on the cut whose state `withCut W β`, for some `β`, agrees with `P`
capped at the cap, cutoff included, with orbit code over all fields satisfying `A`.  The cap `⊥`
needs no hypothesis (`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom` on the forgetful level).

**The LOW state step from the frontier condition** (`ProfileTower.exists_jointCutoff`,
`ProfileTower.SLvl.sCatStep_of_frontier`, compiled in this repository).  For the LOW clause, the
state step follows from the **frontier step** (`ProfileTower.SLvl.SFrontierStep`): an amalgam
profile `W` lawful on the cut, extending the prescription, agreeing with the amalgam part of `P`
capped at the cap, satisfying the frontier condition when its donor maximum is below the capped
cutoff of `P`.  The cutoff is `min (P β) h`, and the orbit map over all fields, a witness bounded by
the grade, carries the frontier condition.  The frontier step is what the LOW steps of the
catalogue layer build before they code the cutoff (`ProfileTower.Lvl.Good.lowStep_donor`,
`ProfileTower.Lvl.Good.lowStep_private`, which use the profile `P` only through its code-grid
values, its amalgam part lawful on the cut, its LOW clause, and the coding of the cutoff).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {A : CProf I → Prop}

/-! ### Readability at the states -/

/-- **Readability at the canonical states**: the section of a state level at every state fixed by
the orbit code over all fields at `g + 1`, with values in the code grid, is readable for it. -/
def SLvl.ReadableS (N : SLvl I g) : Prop :=
  ∀ Q : CProf I, orbitCode (g + 1) Q = Q → (∀ f, Q f ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, IsReadableAt (g + 1) Q (N.σs Q z)

/-- The splice of a state is readable for the state. -/
theorem isReadableAt_hatS (k K : ℕ) (Q : CProf I) (f : Fin I.amalgam.card ⊕ Unit) :
    IsReadableAt K Q (hatS k Q f) := by
  rcases f with d | z
  · by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
    · change IsReadableAt K Q (hat I k (camal Q) d)
      rw [hat_of_le hd]; exact isReadableAt_apply Q (Sum.inl d)
    · change IsReadableAt K Q (hat I k (camal Q) d)
      rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
  · exact isReadableAt_apply Q _

/-- **A next state level is readable at the canonical states.** -/
theorem SLvl.Good.readableS_next {N : SLvl I g} (hN : N.Good A) (C : Finset (CProf I)) :
    (N.next C).ReadableS := by
  intro Q hQ hQB z
  change IsReadableAt (g + 1 + 1) Q (N.nextσ C Q z)
  by_cases hz : (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1
  · rw [SLvl.nextσ_of_le hz]
    refine isReadableAt_upperDecoderAt_of_mem (B' := bound I) hQ (by omega)
      (hatS_mem_codeGrid hQB)
      (isReadableAt_hatS _ _ Q) ?_
    induction z using Fin.addCases with
    | left e => rw [SLvl.Φs_castAdd]; exact hN.mem _ (scode_mem_codeGrid _ _) e
    | right i =>
      rw [SLvl.Φs_natAdd]
      exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
    rw [hN.nextσ_old_of_lt hz]
    exact isReadableAt_apply Q _

/-- **A canonical next level read as a state level is readable at the canonical states.** -/
theorem Lvl.Good.readableS_toS_next {L : Lvl I g} (hL : L.Good) : L.next.toS.ReadableS := by
  intro Q hQ hQB z
  change IsReadableAt (g + 1 + 1) Q (L.nextσ (camal Q) z)
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).grade z ≤ g + 1
  · rw [Lvl.nextσ_of_le hz]
    refine isReadableAt_upperDecoderAt_of_mem hQ (by omega)
      (hat_mem_codeGrid fun d ↦ hQB (Sum.inl d)) (fun d ↦ ?_)
      (hL.Φ_mem_codeGrid (code_mem_codeGrid _ _) z)
    exact isReadableAt_hatS (g + 1) _ Q (Sum.inl d)
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt hz
    rw [hL.nextσ_old_of_lt hz]
    exact isReadableAt_apply Q (Sum.inl d)

/-! ### The extension through a state layer -/

section Ext

variable {N : SLvl I g}

local notation "𝒮" => sCat I (g + 1) A

/-- A cell of a state layer of scope other than the ground set below `(univ, g + 1)` is an old
amalgam cell of grade at most `g + 1`. -/
theorem SLvl.Good.exists_old_sS (hN : N.Good A) {C : Finset (CProf I)} {z : Fin (N.sS C).card}
    (hz : z ∈ (N.sS C).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1))
    (hne : (N.sS C).toCellScheme.scope z ≠ univ) :
    ∃ d, I.amalgam.toCellScheme.grade d ≤ g + 1 ∧ z = Fin.castAdd _ (N.embed d) := by
  induction z using Fin.addCases with
  | right j => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j) hne
  | left e =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hne
    obtain ⟨d, rfl⟩ := hN.mem_range e hne
    refine ⟨d, ?_, rfl⟩
    have := hz.2
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      show N.S.toCellScheme.gradedIndex (N.embed d) = I.amalgam.toCellScheme.gradedIndex d from
        Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)] at this
    exact this

/-- A cell of a state layer of graded index `(univ, g + 1)` is a new cell. -/
theorem SLvl.exists_natAdd_eq_sS (N : SLvl I g) {C : Finset (CProf I)} {u : Fin (N.sS C).card}
    (hu : (N.sS C).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1)) :
    ∃ i, Fin.natAdd _ i = u := by
  by_cases hlt : (u : ℕ) < N.S.card
  · refine absurd ?_ (N.not_le ⟨u, hlt⟩)
    rw [← Scheme.appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < N.S.card + C.card := u.2
    exact ⟨⟨u - N.S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- **Extension through a state layer at a positive cap.**  Let `P` be a state of the catalogue,
`h` self-visible and short at `g + 1`, other than `⊥`, and `V = withCut W β` a state agreeing with
`P` capped at `h` whose orbit code over all fields lies in the catalogue.  Then some labelling
lawful below `(univ, g + 1)` reads `W` at the old cells of grade at most `g + 1` and agrees with
the row of `P` capped at `h`. -/
theorem SLvl.Good.exists_extension_s (hN : N.Good A) (hR : N.ReadableS) {P : CProf I}
    (hP : P ∈ 𝒮) {h : Label.{u}} (hh : IsSelfVisible (g + 1) h) (hs : IsShort (g + 1) h)
    (hb : h ≠ ⊥) {W : Prof I} {β : Label.{u}}
    (hVP : ∀ f, min (withCut W β f) h = min (P f) h)
    (hQC : orbitCode (g + 1) (withCut W β) ∈ 𝒮) :
    ∃ q : (N.sS 𝒮).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (N.sS 𝒮).rows.IsLawfulBelow (univ, g + 1) q ∧
      (∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        q ⟨Fin.castAdd _ (N.embed d), by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            show N.S.toCellScheme.gradedIndex (N.embed d) =
              I.amalgam.toCellScheme.gradedIndex d from
              Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)]
          exact ⟨subset_univ _, hd⟩⟩ = W d) ∧
      ∀ z, min (q z) h = min (N.Φs 𝒮 P z) h := by
  set V : CProf I := withCut W β with hV
  set Q : CProf I := orbitCode (g + 1) V with hQ
  obtain ⟨hPB, -, hPo, -⟩ := mem_sCat.mp hP
  obtain ⟨hQB, hQc, hQo, hQA⟩ := mem_sCat.mp hQC
  have hQP (f : Fin I.amalgam.card ⊕ Unit) : min (Q f) h = min (P f) h :=
    min_orbitCode_eq hh hs hPo hVP f
  have hQV (f : Fin I.amalgam.card ⊕ Unit) : min (orbitCode (g + 1) V f) h = min (V f) h :=
    (hQP f).trans (hVP f).symm
  have hag (z : (N.sS 𝒮).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
      min (orbitDecoder (g + 1) V h (N.Φs 𝒮 Q z)) h = min (N.Φs 𝒮 P z) h := by
    obtain ⟨z, -⟩ := z
    induction z using Fin.addCases with
    | left e =>
      rw [min_orbitDecoder_eq_of_isReadableAt hh hQV (by
          rw [SLvl.Φs_castAdd]
          exact hR Q hQo hQB e),
        SLvl.Φs_castAdd, SLvl.Φs_castAdd]
      exact hN.capAgree Q P hQB h hh hs hQP e
    | right j =>
      rw [SLvl.Φs_natAdd, SLvl.Φs_natAdd,
        min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
          (bot_mem_grid _ _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs (fun f ↦ ⟨hQB f, hPB f⟩) hQP _
  refine ⟨fun z ↦ orbitDecoder (g + 1) V h (N.Φs 𝒮 Q z),
    (hN.isLawfulBelow_Φs hQC hQB hQc hQA).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb) (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb), fun d hd ↦ ?_,
    hag⟩
  change orbitDecoder (g + 1) V h (N.Φs 𝒮 Q (Fin.castAdd _ (N.embed d))) = W d
  rw [SLvl.Φs_castAdd, hN.literal, hQ, orbitDecoder_orbitCode hQV (Sum.inl d)]
  rfl

/-- **Extension through a state layer at the cap `⊥`**: an amalgam profile lawful on the cut whose
state with the cutoff `⊥` has its orbit code in the catalogue extends. -/
theorem SLvl.Good.exists_extension_s_bot (hN : N.Good A) {W : Prof I}
    (hQC : withCut (orbitCode (g + 1) W) ⊥ ∈ 𝒮) :
    ∃ q : (N.sS 𝒮).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) → Label.{u},
      (N.sS 𝒮).rows.IsLawfulBelow (univ, g + 1) q ∧
      ∀ d (hd : I.amalgam.toCellScheme.grade d ≤ g + 1),
        q ⟨Fin.castAdd _ (N.embed d), by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
            show N.S.toCellScheme.gradedIndex (N.embed d) =
              I.amalgam.toCellScheme.gradedIndex d from
              Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)]
          exact ⟨subset_univ _, hd⟩⟩ = W d := by
  set Q : CProf I := withCut (orbitCode (g + 1) W) ⊥ with hQ
  obtain ⟨hQB, hQc, -, hQA⟩ := mem_sCat.mp hQC
  have hQW (d : Fin I.amalgam.card) :
      min (orbitCode (g + 1) W d) (gridPoint (g + 1) 0) = min (W d) (gridPoint (g + 1) 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder (g + 1) W (gridPoint (g + 1) 0) (N.Φs 𝒮 Q z),
    (hN.isLawfulBelow_Φs hQC hQB hQc hQA).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun d hd ↦ ?_⟩
  change orbitDecoder (g + 1) W (gridPoint (g + 1) 0)
    (N.Φs 𝒮 Q (Fin.castAdd _ (N.embed d))) = W d
  rw [SLvl.Φs_castAdd, hN.literal]
  exact orbitDecoder_orbitCode hQW d

end Ext


/-! ### The state step and the lift -/

section Lift

variable {N : SLvl I g}

local notation "𝒮" => sCat I (g + 1) A

variable (N A) in
/-- **The state step** from the coatom `univ.erase x` at the grade `g + 1` (see the module
docstring). -/
def SLvl.SCatStep (x : Fin (m + 2)) : Prop :=
  ∀ P ∈ 𝒮, ∀ h : Label.{u}, IsSelfVisible (g + 1) h → IsShort (g + 1) h → ⊥ < h →
    ∀ w : Fin (N.sS 𝒮).card → Label.{u},
    (N.sS 𝒮).rows.IsLawfulBelow (univ.erase x, g + 1) (fun z ↦ w z) →
    (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
        min (w (Fin.castAdd _ (N.embed d))) h = min (P (Sum.inl d)) h) →
    ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (N.embed d))) ∧
      (∀ f, min (withCut W β f) h = min (P f) h) ∧ A (orbitCode (g + 1) (withCut W β))

/-- The orbit code over all fields of a state with amalgam part lawful on the cut lies in the
state catalogue when it satisfies `A`. -/
theorem orbitCode_withCut_mem_sCat {W : Prof I} (hW : IsCutLawful I (g + 1) W) {β : Label.{u}}
    (hA : A (orbitCode (g + 1) (withCut W β))) : orbitCode (g + 1) (withCut W β) ∈ 𝒮 := by
  have hB : 2 * Fintype.card (Fin I.amalgam.card ⊕ Unit) ≤ bound I := by
    rw [card_fields]; simp only [bound]; omega
  refine mem_sCat.mpr ⟨fun f ↦ orbitMap_mem_codeGrid hB _, ⟨?_, ?_⟩, orbitCode_orbitCode, hA⟩
  · exact hW.1.map_of_apply_eq_bot (fun d ↦ d.2.2)
      (isWitness_orbitMap (g + 1) (withCut W β)) fun _ ↦ orbitMap_eq_bot_iff.mp
  · exact hW.2.map_of_apply_eq_bot (fun d ↦ d.2.2)
      (isWitness_orbitMap (g + 1) (withCut W β)) fun _ ↦ orbitMap_eq_bot_iff.mp

/-- **The capped lift from a coatom into a state layer from the state step**, over a good state
level readable at the canonical states, for `g + 1 ≤ m`, when `A` holds with the cutoff `⊥`: the
one-grade lift `CellScheme.Rows.cappedLift_of_boundary_short` with the boundary triple of the
coatom, the lift of the level at `g`, the cap `⊥` by
`ProfileTower.Lvl.Good.exists_cutLawful_of_coatom` on the forgetful level, and the positive caps by
the state step and `ProfileTower.SLvl.Good.exists_extension_s`. -/
theorem SLvl.Good.cappedLift_sS (hN : N.Good A) (hR : N.ReadableS) (hgm : g + 1 ≤ m)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hstep : N.SCatStep A x) :
    (N.sS 𝒮).rows.CappedLift (X := (univ.erase x, g + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  have hF := hN.forget hA0
  have hCsub : ∀ P ∈ 𝒮, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) ∧ A P := fun P hP ↦
    ⟨(mem_sCat.mp hP).1, (mem_sCat.mp hP).2.1, (mem_sCat.mp hP).2.2.2⟩
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  have hgi (d : Fin I.amalgam.card) :
      N.S.toCellScheme.gradedIndex (N.embed d) = I.amalgam.toCellScheme.gradedIndex d :=
    Prod.ext (hN.scope_embed d) (hN.lowerEmb.grade_eq d)
  have hlift : (N.sS 𝒮).rows.CappedLift (X := (univ.erase x, g))
      (Y := ((univ : Finset (Fin (m + 2))), g)) ⟨erase_subset _ _, le_rfl⟩ :=
    (SLvl.cappedLift_sS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr (hN.lift x hx g le_rfl)
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq (univ.erase x, g + 1)
    ⟨I.erase_mem_faces hx, by omega, show g + 1 ≤ #(univ.erase x) by rw [hcard]; omega⟩
    (Seed.ne_univ_erase x)
  have hle : ((univ.erase x, g + 1) : Finset (Fin (m + 2)) × ℕ) ≤
      ((univ : Finset (Fin (m + 2))), g + 1) := ⟨erase_subset _ _, le_rfl⟩
  have hcoat {z : Fin (N.sS 𝒮).card}
      (hz : z ∈ (N.sS 𝒮).toCellScheme.below (univ.erase x, g + 1)) :
      ∃ d, I.amalgam.toCellScheme.grade d ≤ g + 1 ∧
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∧ z = Fin.castAdd _ (N.embed d) := by
    have hne : (N.sS 𝒮).toCellScheme.scope z ≠ univ := fun he ↦
      Seed.ne_univ_erase x (univ_subset_iff.mp (he ▸ (hz.1 :
        (N.sS 𝒮).toCellScheme.scope z ⊆ univ.erase x)))
    obtain ⟨d, hd, rfl⟩ := hN.exists_old_sS ((N.sS 𝒮).toCellScheme.below_mono hle hz) hne
    refine ⟨d, hd, ?_, rfl⟩
    have h1 : (N.sS 𝒮).toCellScheme.gradedIndex (Fin.castAdd _ (N.embed d)) ≤
        (univ.erase x, g + 1) := hz
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hgi] at h1
    exact h1.1
  have hbot0 : (fun _ ↦ ⊥ : CProf I) ∈ 𝒮 := by
    refine mem_sCat.mpr ⟨fun _ ↦ mem_insert_self _ _, (bot_mem_cat (I := I) _ |> mem_cat.mp).1,
      funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl, ?_⟩
    convert hA0 (fun _ ↦ ⊥) using 1
    funext f; rcases f with d | z <;> rfl
  obtain ⟨i₀, -⟩ := exists_equivFin_eq hbot0
  refine Rows.cappedLift_of_boundary_short (U := (univ.erase x, g + 1))
    (V := (univ.erase x, g + 1)) (O := (univ.erase x, g + 1)) (erase_subset _ _)
    ⟨Fin.castAdd _ (N.embed c), by
      rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hgi, hc]⟩ hlift
    le_rfl le_rfl le_rfl hle hle (fun _ hd _ ↦ hd) (Rows.cappedLift_refl _)
    (Rows.cappedLift_refl _) ?_
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩ fun u hu ↦ ?_
  · -- the extension from the boundary at `⊥`
    intro w hw _ _
    have hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ (univ.erase x, g + 1) :=
      fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1)
    have hw' := (Lvl.isLawfulBelow_catS_iff (L := N.forget) (C := 𝒮) (v := w) hX).mpr
      ((Scheme.isLawfulBelow_appendFullCells_iff (v := w) hX).mp hw)
    obtain ⟨W, hW, hWw⟩ := hF.exists_cutLawful_of_coatom (w := w) hgm hx hw'
    have hQC : withCut (orbitCode (g + 1) W) ⊥ ∈ 𝒮 := by
      refine mem_sCat.mpr ⟨fun f ↦ ?_, ⟨hW.1.orbitCode fun d ↦ d.2.2,
        hW.2.orbitCode fun d ↦ d.2.2⟩, by rw [orbitCode_withCut_bot, orbitCode_orbitCode],
        hA0 _⟩
      rcases f with d | z
      · exact codeGrid_mono (B := 2 * I.amalgam.card) (by simp only [bound]; omega)
          (orbitMap_mem_codeGrid (w := W) (by simp) _)
      · exact mem_insert_self _ _
    obtain ⟨q, hq, hqW⟩ := hN.exists_extension_s_bot hQC
    refine ⟨q, hq, fun z hz ↦ ?_, fun _ ↦ by simp⟩
    obtain ⟨z, hzY⟩ := z
    obtain ⟨d, hd, hds, rfl⟩ := hcoat (hz.elim id id)
    have := hqW d hd
    rwa [hWw d hd hds] at this
  · -- the serving state and its row
    obtain ⟨i, rfl⟩ := N.exists_natAdd_eq_sS hu
    set P := ((𝒮).equivFin.symm i).1 with hP_def
    have hP : P ∈ 𝒮 := ((𝒮).equivFin.symm i).2
    obtain ⟨hPB, -, -, -⟩ := mem_sCat.mp hP
    have hrowB (z : (N.sS 𝒮).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
        (N.sS 𝒮).rows.rowBelow _ hu z = N.Φs 𝒮 P z :=
      Scheme.appendFullCells_row_natAdd (S := N.S) (k := g + 1)
        (r := fun i ↦ N.Φs 𝒮 ((𝒮).equivFin.symm i).1) (h := N.not_le) i _
    refine ⟨hN.sS_consistent hCsub _, fun z ↦ ?_, fun z ↦ ?_, fun h hh hs hb ↦ ?_⟩
    · rw [hrowB]; exact isShort_of_mem_codeGrid (hN.Φs_mem_codeGrid hPB _)
    · rw [hrowB]; exact ne_top_of_mem_codeGrid (hN.Φs_mem_codeGrid hPB _)
    · intro w hw _ hwS
      have hwP (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ g + 1)
          (hds : I.amalgam.toCellScheme.scope d ⊆ univ.erase x) :
          min (w (Fin.castAdd _ (N.embed d))) h = min (P (Sum.inl d)) h := by
        have hm : Fin.castAdd (𝒮).card (N.embed d) ∈
            (N.sS 𝒮).toCellScheme.below (univ.erase x, g + 1) := by
          rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd, hgi]
          exact ⟨hds, hd⟩
        have h1 := hwS ⟨_, (N.sS 𝒮).toCellScheme.below_mono hle hm⟩ (.inl hm)
        rwa [hrowB, SLvl.Φs_castAdd, hN.literal] at h1
      obtain ⟨W, β, hW, hWw, hVP, hAQ⟩ := hstep P hP h hh hs hb w hw hwP
      obtain ⟨q, hq, hqW, hqa⟩ := hN.exists_extension_s hR hP hh hs hb.ne' hVP
        (orbitCode_withCut_mem_sCat hW hAQ)
      refine ⟨q, hq, fun z hz ↦ ?_, fun z ↦ by rw [hrowB]; exact hqa z⟩
      obtain ⟨z, hzY⟩ := z
      obtain ⟨d, hd, hds, rfl⟩ := hcoat (hz.elim id id)
      have := hqW d hd
      rwa [hWw d hd hds] at this

end Lift

/-! ### The LOW state step from the frontier condition -/

section Frontier

variable {K k : ℕ} {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o r : Fin I.amalgam.card}

/-- **The joint cutoff.**  Let `P` be a canonical LOW state over all fields at `k ≥ K`, `h`
self-visible and short at `k`, and `W` an amalgam profile agreeing with the amalgam part of `P`
capped at `h` that satisfies the frontier condition when its donor maximum is below the capped
cutoff of `P` (the cutoff being neither a proper donor field nor a donor top).  Then the state of
`W` with the cutoff `min (P β) h` agrees with `P` capped at `h` and its orbit code over all fields
is LOW. -/
theorem exists_jointCutoff (hK : K ≤ k) {P : CProf I} (hPlow : lowPred K Nf T o r P)
    {h : Label.{u}} {W : Prof I} (hWP : ∀ d, min (W d) h = min (P (Sum.inl d)) h)
    (hN : Sum.inr () ∉ Nf) (hT : Sum.inr () ∉ T)
    (hfr : donorMax Nf (withCut W ⊥) < min (P (Sum.inr ())) h →
      ∀ x ∈ T, Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ x) :
    (∀ f, min (withCut W (min (P (Sum.inr ())) h) f) h = min (P f) h) ∧
      lowPred K Nf T o r (orbitCode k (withCut W (min (P (Sum.inr ())) h))) := by
  set β := min (P (Sum.inr ())) h with hβ
  set V : CProf I := withCut W β with hV
  have hVP (f : Fin I.amalgam.card ⊕ Unit) : min (V f) h = min (P f) h := by
    rcases f with d | z
    · exact hWP d
    · change min β h = _; rw [hβ, min_assoc, min_self]
  refine ⟨hVP, ?_⟩
  have hdm : donorMax Nf V = donorMax Nf (withCut W ⊥) := donorMax_congr fun f hf ↦ by
    rcases f with d | z
    · rfl
    · cases z; exact absurd hf hN
  have hVlow : lowPred K Nf T o r V := by
    intro hact x hx
    obtain ⟨x', rfl⟩ : ∃ x', x = Sum.inl x' := by
      rcases x with x' | z
      · exact ⟨x', rfl⟩
      · cases z; exact absurd hx hT
    refine max_le ?_ ?_
    · -- the serving state is active, so its donor tops reach its cutoff
      have hβh : β ≤ h := min_le_right _ _
      have hMh : donorMax Nf V < h := hact.trans_le hβh
      have hPN : ∀ f ∈ Nf, P f = V f := fun f hf ↦ by
        have hf' : V f < h := (le_donorMax hf).trans_lt hMh
        exact eq_of_min_eq_of_lt (hVP f) hf'
      have hPact : donorMax Nf P < P (Sum.inr ()) := by
        rw [donorMax_congr hPN]
        exact hact.trans_le (min_le_left _ _)
      have hx' := (le_max_left _ _).trans (hPlow hPact _ hx)
      have h1 : min β h ≤ min (V (Sum.inl x')) h := by
        rw [hVP (Sum.inl x')]
        exact min_le_min_right _ ((min_le_left _ _).trans hx')
      rw [min_eq_left hβh] at h1
      exact h1.trans (min_le_left _ _)
    · have := hfr (by rw [← hdm]; exact hact) _ hx
      exact this
  exact hVlow.map (isWitness_orbitMap k V) (stepSuppressor_of_le hK)

variable (N) in
/-- **The frontier step** from the coatom `univ.erase x` at the grade `g + 1`, for the LOW clause at
`K`: at every state `P` of the catalogue and every positive cap self-visible and short at `g + 1`,
every labelling lawful below the coatom agreeing there with `P` capped at the cap is, at the amalgam
cells below the coatom, an amalgam profile lawful on the cut agreeing with the amalgam part of `P`
capped at the cap, satisfying the frontier condition when its donor maximum is below the capped
cutoff of `P`. -/
def SLvl.SFrontierStep (N : SLvl I g) (K : ℕ) (Nf : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) (x : Fin (m + 2)) : Prop :=
  ∀ P ∈ sCat I (g + 1) (lowPred K Nf T o r), ∀ h : Label.{u}, IsSelfVisible (g + 1) h →
    IsShort (g + 1) h → ⊥ < h →
    ∀ w : Fin (N.sS (sCat I (g + 1) (lowPred K Nf T o r))).card → Label.{u},
    (N.sS (sCat I (g + 1) (lowPred K Nf T o r))).rows.IsLawfulBelow (univ.erase x, g + 1)
      (fun z ↦ w z) →
    (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      I.amalgam.toCellScheme.scope d ⊆ univ.erase x →
        min (w (Fin.castAdd _ (N.embed d))) h = min (P (Sum.inl d)) h) →
    ∃ W : Prof I, IsCutLawful I (g + 1) W ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
        I.amalgam.toCellScheme.scope d ⊆ univ.erase x → W d = w (Fin.castAdd _ (N.embed d))) ∧
      (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧
      (donorMax Nf (withCut W ⊥) < min (P (Sum.inr ())) h →
        ∀ y ∈ T, Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W ⊥) ≤ withCut W ⊥ y)

/-- **The LOW state step from the frontier step**, at a grade `g + 1 ≥ K`, the cutoff being neither
a proper donor field nor a donor top (`ProfileTower.exists_jointCutoff`). -/
theorem SLvl.sCatStep_of_frontier {N : SLvl I g} (hK : K ≤ g + 1) (hN : Sum.inr () ∉ Nf)
    (hT : Sum.inr () ∉ T) {x : Fin (m + 2)} (h : N.SFrontierStep K Nf T o r x) :
    N.SCatStep (lowPred K Nf T o r) x := by
  intro P hP c hc hs hb w hw hwP
  obtain ⟨W, hW, hWw, hWP, hfr⟩ := h P hP c hc hs hb w hw hwP
  obtain ⟨hVP, hlow⟩ := exists_jointCutoff hK (mem_sCat.mp hP).2.2.2 hWP hN hT hfr
  exact ⟨W, _, hW, hWw, hVP, hlow⟩

end Frontier


/-! ### The lifts of the state tower from the frontier steps -/

section TowerLifts

variable {L : Lvl I g}

/-- **The frontier steps of the state tower of the LOW clause** below the layer `J₀`: every layer at
a grade `g + J + 1` with `J < J₀` has the frontier step from the two coatoms. -/
def STowerFrontier (L : Lvl I g) (K : ℕ) (Nf : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o r : Fin I.amalgam.card) (J₀ : ℕ) : Prop :=
  ∀ J < J₀, ∀ x ∈ (Pts : Finset (Fin (m + 2))),
    (sTower L (lowPred K Nf T o r) J).SFrontierStep K Nf T o r x

/-- **The state tower of the LOW clause lifts from its frontier steps**, over a good level read as a
state level readable at the canonical states, up to the grade `m`, when the LOW clause is at
`K ≤ g + 1`, is kept by the state codes from `g + 1` on, and its cutoff is neither a proper donor
field nor a donor top. -/
theorem sTowerLifts_of_frontier (hL : L.Good) (hRL : L.toS.ReadableS) {K : ℕ}
    {Nf : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
    {o r : Fin I.amalgam.card} (hK : K ≤ g + 1) (hN : Sum.inr () ∉ Nf) (hT : Sum.inr () ∉ T)
    (hAc : ∀ j, g + 1 ≤ j → ∀ P : CProf I, lowPred K Nf T o r P →
      lowPred K Nf T o r (scode j P)) :
    ∀ J₀, g + J₀ ≤ m → STowerFrontier L K Nf T o r J₀ →
      STowerLifts L (lowPred K Nf T o r) J₀
  | 0, _, _ => fun J hJ ↦ absurd hJ (Nat.not_lt_zero J)
  | J₀ + 1, hm, hfr => by
    have ih := sTowerLifts_of_frontier hL hRL hK hN hT hAc J₀ (by omega)
      (fun J hJ ↦ hfr J (by omega))
    intro J hJ x hx
    have hgood := sTower_good hL (fun W ↦ lowPred_withCut_bot W) hAc ih J (by omega) (by omega)
    have hR : (sTower L (lowPred K Nf T o r) J).ReadableS := by
      rcases J with _ | J
      · exact hRL
      · exact (sTower_good hL (fun W ↦ lowPred_withCut_bot W) hAc ih J (by omega)
          (by omega)).readableS_next _
    exact hgood.cappedLift_sS hR (by omega) hx (fun W ↦ lowPred_withCut_bot W)
      (SLvl.sCatStep_of_frontier (by omega) hN hT (hfr J hJ x hx))

end TowerLifts


/-! ### The state step from the step on the amalgam -/

section Amalgam

variable {N : SLvl I g}

/-- **The state step from the step for states on the amalgam**: a state step on amalgam
labellings below the coatom (`ProfileTower.StateCatStep` has this form),
whose conclusion satisfies `A` before coding, gives the state step of a good state level when `A`
is kept by the orbit code over all fields. -/
theorem SLvl.sCatStep_of_amalgam (hN : N.Good A)
    (hAo : ∀ V : CProf I, A V → A (orbitCode (g + 1) V)) {x : Fin (m + 2)}
    (hstep : ∀ P : CProf I, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) →
      IsCutLawful I (g + 1) (camal P) → A P →
      ∀ h : Label.{u}, IsSelfVisible (g + 1) h → IsShort (g + 1) h → ⊥ < h →
      ∀ a : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1) (fun d ↦ a d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1),
        min (a d) h = min (P (Sum.inl d)) h) →
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + 1) W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, g + 1), W d = a d) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧ A (withCut W β)) :
    N.SCatStep A x := by
  intro P hP h hh hs hb w hw hwP
  obtain ⟨hPB, hPC, -, hPA⟩ := mem_sCat.mp hP
  have hX : ¬ ((univ : Finset (Fin (m + 2))), g + 1) ≤ (univ.erase x, g + 1) :=
    fun h' ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h'.1)
  have ha : I.amalgam.rows.IsLawfulBelow (univ.erase x, g + 1)
      (fun d ↦ w (Fin.castAdd _ (N.embed d))) :=
    (SLvl.Good.isLawfulBelow_old_iff hN (X := (univ.erase x, g + 1)) (Seed.ne_univ_erase x)
      (w := fun e ↦ w (Fin.castAdd _ e))).mp
      ((Scheme.isLawfulBelow_appendFullCells_iff (v := w) hX).mp hw)
  obtain ⟨W, β, hW, hWa, hWP, -, hβ, hA⟩ := hstep P hPB hPC hPA h hh hs hb _ ha
    fun d hd ↦ hwP d hd.2 hd.1
  refine ⟨W, β, hW, fun d hd hds ↦ hWa d ⟨hds, hd⟩, fun f ↦ ?_, hAo _ hA⟩
  rcases f with d | z
  · exact hWP d
  · exact hβ

/-- **The steps for states on the amalgam of the state tower** below the layer `J₀`: the step on
the amalgam at every grade `g + J + 1` with `J < J₀`, from the two coatoms. -/
def STowerAmalgamSteps (g : ℕ) (A : CProf I → Prop) (J₀ : ℕ) : Prop :=
  ∀ J < J₀, ∀ x ∈ (Pts : Finset (Fin (m + 2))),
    ∀ P : CProf I, (∀ f, P f ∈ codeGrid (g + J + 1) (bound I)) →
      IsCutLawful I (g + J + 1) (camal P) → A P →
      ∀ h : Label.{u}, IsSelfVisible (g + J + 1) h → IsShort (g + J + 1) h → ⊥ < h →
      ∀ a : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase x, g + J + 1) (fun d ↦ a d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1),
        min (a d) h = min (P (Sum.inl d)) h) →
      ∃ (W : Prof I) (β : Label.{u}), IsCutLawful I (g + J + 1) W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, g + J + 1), W d = a d) ∧
        (∀ d, min (W d) h = min (P (Sum.inl d)) h) ∧ β ∈ codeGrid (g + J + 1) (bound I) ∧
        min β h = min (P (Sum.inr ())) h ∧ A (withCut W β)

/-- **The state tower lifts from the steps for states on the amalgam**, over a good level read as
a state level readable at the canonical states, up to the grade `m`, when `A` holds with the
cutoff `⊥` and is kept by the state codes and the orbit codes over all fields from `g + 1` on. -/
theorem sTowerLifts_of_amalgam {L : Lvl I g} (hL : L.Good) (hRL : L.toS.ReadableS)
    (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hAc : ∀ j, g + 1 ≤ j → ∀ P : CProf I, A P → A (scode j P))
    (hAo : ∀ j, g + 1 ≤ j → ∀ V : CProf I, A V → A (orbitCode j V)) :
    ∀ J₀, g + J₀ ≤ m → STowerAmalgamSteps g A J₀ → STowerLifts L A J₀
  | 0, _, _ => fun J hJ ↦ absurd hJ (Nat.not_lt_zero J)
  | J₀ + 1, hm, hst => by
    have ih := sTowerLifts_of_amalgam hL hRL hA0 hAc hAo J₀ (by omega)
      (fun J hJ ↦ hst J (by omega))
    intro J hJ x hx
    have hgood := sTower_good hL hA0 hAc ih J (by omega) (by omega)
    have hR : (sTower L A J).ReadableS := by
      rcases J with _ | J
      · exact hRL
      · exact (sTower_good hL hA0 hAc ih J (by omega) (by omega)).readableS_next _
    exact hgood.cappedLift_sS hR (by omega) hx hA0
      (SLvl.sCatStep_of_amalgam hgood (hAo _ (by omega)) (hst J hJ x hx))

end Amalgam


/-! ### Readability of the levels from the grade `0` -/

/-- **The level at the grade `0`, read as a state level, is readable at the canonical states**: its
section is the amalgam part of the state, a value of the state. -/
theorem readableS_base₀ : (base₀ I).toS.ReadableS :=
  fun Q _ _ z ↦ isReadableAt_apply Q (Sum.inl z)

/-- **Every level from the grade `0` up to `m`, read as a state level, is readable at the canonical
states** (`ProfileTower.readableS_base₀`, `ProfileTower.Lvl.Good.readableS_toS_next`). -/
theorem readableS_lvlZero : ∀ g, g ≤ m → (lvlZero I g).toS.ReadableS
  | 0, _ => readableS_base₀
  | g + 1, h => (lvlZero_good g (by omega)).readableS_toS_next

end VaughtConjecture.ProfileTower

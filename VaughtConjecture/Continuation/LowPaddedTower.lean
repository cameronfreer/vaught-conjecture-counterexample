/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateLift
import VaughtConjecture.Continuation.LowPaddedStep

/-!
# The padded state tower: states keep their fields above the layer

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the levels above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

The state tower of `VaughtConjecture.Continuation.LowStateTower` reads, at each layer, the row of
the **state code** of a state: the orbit code of its splice, the fields above the grade of the
layer set to `⊥`.  The LOW clause over the proper donor fields of every grade
(`ProfileTower.lowNAll`) is not kept by that splice (`ProfileTower.not_lowPred_scode_of_high`).
The **padded** tower reads the row of the orbit code over all fields of the state itself: a state
keeps its fields above the grade of the layer, and the orbit code keeps the clause
(`ProfileTower.lowPred_orbitCode`).

**The padded next state level** (`ProfileTower.SLvl.pnext`, `ProfileTower.SLvl.Good.pnext`,
compiled in this repository).  The scheme is that of the next state level
(`ProfileTower.SLvl.sS`: one cell of full scope per state of a catalogue, its row the section of
the level and the agreement heights, cutoff included); the section reads, at the cells of grade at
most `g + 1`, the row of the orbit code of the state through the upper decoder of the state.  Over
a good state level, on the state catalogue of a predicate `A` holding with the cutoff `⊥` and kept
by the orbit code, the padded next level is good given the lift of the layer, readable at the
canonical states (`ProfileTower.SLvl.Good.readableS_pnext`), and its forgetful level extends at
`⊥` (the scheme is that of `ProfileTower.SLvl.next`, `ProfileTower.SLvl.Good.hasBotExtension_next`).

**The padded tower** (`ProfileTower.pTower`, `ProfileTower.pTower_good`,
`ProfileTower.pTowerLifts_of_amalgam`, compiled in this repository): `L` read as a state level,
then the padded next levels on the state catalogues of `A`; good up to the grade `m` given its
lifts, and the lifts follow from the steps for states on the amalgam
(`ProfileTower.STowerAmalgamSteps`) through `ProfileTower.SLvl.Good.cappedLift_sS`, which holds
over every good state level readable at the canonical states.

**The chain bounds and the separator** (`ProfileTower.le_pTower_hi`, `ProfileTower.pTower_lo_le`,
`ProfileTower.sepInv_orbitCode`, compiled in this repository): those of the state tower, with the
**padded bottom state** (`ProfileTower.pBot`: the orbit code at `g + J + 1`, …, `g + 2`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ}

/-! ### The padded next state level -/

section PNext

variable (N : SLvl I g) (C : Finset (CProf I))

/-- The **padded section** of the next state level: at the cells of grade at most `g + 1`, the
row labelling of the orbit code over all fields of the state, read by the upper decoder of the
state; above, the section of the level. -/
noncomputable def SLvl.pnextσ (P : CProf I) : Fin (N.S.card + C.card) → Label.{u} := fun z ↦
  if (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1 then
    upperDecoderAt (g + 1) (g + 2) (bound I) P (N.Φs C (orbitCode (g + 1) P) z)
  else Fin.append (N.σs P) (fun _ ↦ ⊥) z

/-- **The padded next state level** on `C`, at the grade `g + 1`: the scheme of the next state
level with the padded section. -/
noncomputable def SLvl.pnext : SLvl I (g + 1) where
  S := N.sS C
  σs := N.pnextσ C
  embed := N.embed.trans (Fin.castAddOrderEmb _)
  inv := (N.next C).inv

variable {N C}

/-- The padded section at a cell of grade at most `g + 1` is the upper decoder of the state at the
row labelling of its orbit code. -/
theorem SLvl.pnextσ_of_le {P : CProf I} {z : Fin (N.S.card + C.card)}
    (hz : (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1) :
    N.pnextσ C P z =
      upperDecoderAt (g + 1) (g + 2) (bound I) P (N.Φs C (orbitCode (g + 1) P) z) := by
  unfold SLvl.pnextσ; exact ite_eq_left hz

/-- The padded section at an old cell of grade above `g + 1` is the state itself. -/
theorem SLvl.Good.pnextσ_old_of_lt {A : CProf I → Prop} (hN : N.Good A) {P : CProf I}
    {d : Fin I.amalgam.card}
    (hd : ¬ (N.S.appendFullCellsScheme (g + 1) C.card).grade (Fin.castAdd _ (N.embed d)) ≤ g + 1) :
    N.pnextσ C P (Fin.castAdd _ (N.embed d)) = P (Sum.inl d) := by
  unfold SLvl.pnextσ
  rw [ite_eq_right hd, Fin.append_left, hN.literal]

/-- The padded next level has the scheme of the next level. -/
theorem SLvl.pnext_S : (N.pnext C).S = (N.next C).S := rfl

end PNext

section PNextGood

variable {N : SLvl I g} {A : CProf I → Prop}

local notation "𝒮" => sCat I (g + 1) A

/-- The orbit code over all fields of a state lies in the code grid with the block bound of the
seed. -/
theorem orbitCode_mem_codeGrid (k : ℕ) (P : CProf I) (f : Fin I.amalgam.card ⊕ Unit) :
    orbitCode k P f ∈ codeGrid k (bound I) :=
  orbitMap_mem_codeGrid (by rw [card_fields]; simp only [bound]; omega) _

/-- **The padded next state level on the state catalogue of `A` is good**, over a good state
level, for `g + 1 ≤ m`, when `A` holds with the cutoff `⊥`, the orbit code at `g + 1` keeps `A`,
and the layer lifts from the two coatoms at `g + 1`. -/
theorem SLvl.Good.pnext (hN : N.Good A) (hgm : g + 1 ≤ m) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hAo : ∀ P : CProf I, A P → A (orbitCode (g + 1) P))
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (N.sS 𝒮).rows.CappedLift (X := (univ.erase x, g + 1))
        (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩) :
    (N.pnext 𝒮).Good A := by
  have hCsub : ∀ P ∈ 𝒮, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) ∧ A P := fun P hP ↦
    ⟨(mem_sCat.mp hP).1, (mem_sCat.mp hP).2.1, (mem_sCat.mp hP).2.2.2⟩
  have hcard : 2 * Fintype.card (Fin I.amalgam.card ⊕ Unit) = bound I := by
    rw [card_fields]; simp only [bound]; ring
  have hemb := Scheme.isLowerEmbedding_castAdd (S := N.S) (g + 1) (𝒮).card
    (fun i ↦ N.Φs 𝒮 ((𝒮).equivFin.symm i).1) N.not_le
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
    have hQ := orbitCode_mem_sCat (A := A) hP (hAo P hPA)
    have h := (hN.isLawfulBelow_Φs hQ (hCsub _ hQ).1 (hCsub _ hQ).2.1
      (hCsub _ hQ).2.2).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_upperDecoderAt (w := P) (B := bound I) (K := g + 2) (by omega))
      (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
    refine (Rows.isLawfulBelow_congr (R := (N.sS 𝒮).rows)
      (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) P
        (N.Φs 𝒮 (orbitCode (g + 1) P) z)) (w' := N.pnextσ 𝒮 P) fun z hz ↦ ?_).mp h
    exact (SLvl.pnextσ_of_le hz.2).symm
  · -- mem
    -- the section of the padded next level, by definition
    change N.pnextσ 𝒮 P z ∈ _
    by_cases hz : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade z ≤ g + 1
    · rw [SLvl.pnextσ_of_le hz]
      exact upperDecoderAt_mem_codeGrid_of_mem (by omega) hP
        (hN.Φs_mem_codeGrid (orbitCode_mem_codeGrid _ _) z)
    · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
      rw [hN.pnextσ_old_of_lt hz]
      exact hP _
  · -- literal
    -- the section of the padded next level, by definition
    change N.pnextσ 𝒮 P (Fin.castAdd _ (N.embed d)) = P (Sum.inl d)
    by_cases hd : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade
        (Fin.castAdd _ (N.embed d)) ≤ g + 1
    · rw [SLvl.pnextσ_of_le hd, SLvl.Φs_castAdd, hN.literal]
      exact upperDecoderAt_orbitCode _
    · exact hN.pnextσ_old_of_lt hd
  · -- capAgree
    -- the section of the padded next level, by definition
    change min (N.pnextσ 𝒮 P z) h = min (N.pnextσ 𝒮 P' z) h
    by_cases hz : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade z ≤ g + 1
    · rw [SLvl.pnextσ_of_le hz, SLvl.pnextσ_of_le hz]
      refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
        (fun f ↦ le_gridPoint_of_mem_codeGrid (hP f)) hag
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
      rw [hN.pnextσ_old_of_lt hz, hN.pnextσ_old_of_lt hz]
      exact hag _
  · -- readable
    -- the section of the padded next level at the state with the cutoff `⊥`, by definition
    change IsReadableAt (g + 1 + 1) Q (N.pnextσ 𝒮 (withCut Q ⊥) z)
    by_cases hz : (N.S.appendFullCellsScheme (g + 1) (𝒮).card).grade z ≤ g + 1
    · rw [SLvl.pnextσ_of_le hz, ← isReadableAt_withCut_bot_iff]
      have hQ' : orbitCode (g + 1 + 1) (withCut Q ⊥) = withCut Q ⊥ := by
        rw [orbitCode_withCut_bot, hQ]
      refine isReadableAt_upperDecoderAt_of_mem hQ' (by omega) (fun f ↦ ?_)
        (fun f ↦ isReadableAt_apply (withCut Q ⊥) f)
        (hN.Φs_mem_codeGrid (orbitCode_mem_codeGrid _ _) z)
      rcases f with d | u
      exacts [hQB d, mem_insert_self _ _]
    · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
      rw [hN.pnextσ_old_of_lt hz]
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

/-- **A padded next state level is readable at the canonical states.** -/
theorem SLvl.Good.readableS_pnext (hN : N.Good A) (C : Finset (CProf I)) :
    (N.pnext C).ReadableS := by
  intro Q hQ hQB z
  -- the section of the padded next level, by definition
  change IsReadableAt (g + 1 + 1) Q (N.pnextσ C Q z)
  by_cases hz : (N.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1
  · rw [SLvl.pnextσ_of_le hz]
    refine isReadableAt_upperDecoderAt_of_mem (B' := bound I) hQ (by omega) hQB
      (fun f ↦ isReadableAt_apply Q f) ?_
    induction z using Fin.addCases with
    | left e => rw [SLvl.Φs_castAdd]; exact hN.mem _ (orbitCode_mem_codeGrid _ _) e
    | right i =>
      rw [SLvl.Φs_natAdd]
      exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · obtain ⟨d, rfl⟩ := hN.exists_old_of_lt hz
    rw [hN.pnextσ_old_of_lt hz]
    exact isReadableAt_apply Q _

/-- **The forgetful level of the padded next state level extends at `⊥`**: its scheme is that of
the next state level (`ProfileTower.SLvl.Good.hasBotExtension_next`). -/
theorem SLvl.Good.hasBotExtension_pnext (hN : N.Good A) (hA0 : ∀ W : Prof I, A (withCut W ⊥)) :
    (N.pnext 𝒮).forget.HasBotExtension :=
  hN.hasBotExtension_next hA0

end PNextGood

/-! ### The padded tower -/

section Tower

variable (L : Lvl I g) (A : CProf I → Prop)

/-- **The padded tower** over a level `L` at the grade `g`: `L` read as a state level, then the
padded next state levels on the state catalogues of `A`. -/
noncomputable def pTower : (J : ℕ) → SLvl I (g + J)
  | 0 => L.toS
  | J + 1 => (pTower J).pnext (sCat I (g + J + 1) A)

/-- **The lifts of the padded tower** below the layer `J₀`: every layer at a grade `g + J + 1`
with `J < J₀` lifts capped from the two coatoms into the full face at its grade. -/
def PTowerLifts (J₀ : ℕ) : Prop :=
  ∀ J < J₀, ∀ x ∈ (Pts : Finset (Fin (m + 2))),
    ((pTower L A J).sS (sCat I (g + J + 1) A)).rows.CappedLift (X := (univ.erase x, g + J + 1))
      (Y := ((univ : Finset (Fin (m + 2))), g + J + 1)) ⟨erase_subset _ _, le_rfl⟩

variable {L A}

/-- **The padded tower is good up to the grade `m`**, given its lifts, when `A` holds with the
cutoff `⊥` and is kept by the orbit codes at the grades above `g`. -/
theorem pTower_good (hL : L.Good) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hAo : ∀ j, g + 1 ≤ j → ∀ P : CProf I, A P → A (orbitCode j P)) {J₀ : ℕ}
    (hlift : PTowerLifts L A J₀) : ∀ J, J ≤ J₀ → g + J ≤ m → (pTower L A J).Good A
  | 0, _, _ => hL.toS A
  | J + 1, hJ, hm => (pTower_good hL hA0 hAo hlift J (by omega) (by omega)).pnext (by omega) hA0
      (hAo _ (by omega)) (hlift J (by omega))

/-- **The padded tower lifts from the steps for states on the amalgam**, over a good level read
as a state level readable at the canonical states, up to the grade `m`, when `A` holds with the
cutoff `⊥` and is kept by the orbit codes over all fields from `g + 1` on. -/
theorem pTowerLifts_of_amalgam (hL : L.Good) (hRL : L.toS.ReadableS)
    (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hAo : ∀ j, g + 1 ≤ j → ∀ V : CProf I, A V → A (orbitCode j V)) :
    ∀ J₀, g + J₀ ≤ m → STowerAmalgamSteps g A J₀ → PTowerLifts L A J₀
  | 0, _, _ => fun J hJ ↦ absurd hJ (Nat.not_lt_zero J)
  | J₀ + 1, hm, hst => by
    have ih := pTowerLifts_of_amalgam hL hRL hA0 hAo J₀ (by omega)
      (fun J hJ ↦ hst J (by omega))
    intro J hJ x hx
    have hgood := pTower_good hL hA0 hAo ih J (by omega) (by omega)
    have hR : (pTower L A J).ReadableS := by
      rcases J with _ | J
      · exact hRL
      · exact (pTower_good hL hA0 hAo ih J (by omega) (by omega)).readableS_pnext _
    exact hgood.cappedLift_sS hR (by omega) hx hA0
      (SLvl.sCatStep_of_amalgam hgood (hAo _ (by omega)) (hst J hJ x hx))

/-- The cells of the layer of controllers among those of the layers above. -/
noncomputable def pEmb : (J : ℕ) → Fin (pTower L A 1).S.card → Fin (pTower L A (J + 1)).S.card
  | 0 => id
  | J + 1 => Fin.castAdd _ ∘ pEmb J

/-- **The layer of controllers is a grade prefix of every layer above**, at `K = g + 1`. -/
theorem isGradePrefix_pEmb :
    ∀ J, Scheme.IsGradePrefix (pTower L A 1).S (pTower L A (J + 1)).S (pEmb (L := L) (A := A) J)
      (g + 1)
  | 0 => Scheme.IsGradePrefix.id _ _
  | J + 1 => (Scheme.IsGradePrefix.castAdd (S := (pTower L A (J + 1)).S) (k := g + (J + 1) + 1)
      (M := (sCat I (g + (J + 1) + 1) A).card)
      (r := fun i ↦ (pTower L A (J + 1)).Φs (sCat I (g + (J + 1) + 1) A)
        ((sCat I (g + (J + 1) + 1) A).equivFin.symm i).1)
      (h := (pTower L A (J + 1)).not_le) (by omega)).comp (isGradePrefix_pEmb J)

/-- The old cells of the layers of the padded tower are the old cells of `L`, through the layer
of controllers. -/
theorem pTower_embed :
    ∀ (J : ℕ) (d : Fin I.amalgam.card),
      (pTower L A (J + 1)).embed d = pEmb (L := L) (A := A) J (Fin.castAdd _ (L.embed d))
  | 0, _ => rfl
  | J + 1, d => congrArg (Fin.castAdd _) (pTower_embed J d)

/-- The **padded bottom state** of `P` through `J` layers: the orbit code at `g + J + 1`, …,
`g + 2`. -/
noncomputable def pBot (g : ℕ) : (J : ℕ) → CProf I → CProf I
  | 0 => id
  | J + 1 => fun P ↦ pBot g J (orbitCode (g + J + 2) P)

/-- **A decoder reads the cutoff cut of the donor maximum of an orbit code at the cutoff cut of
the donor maximum of the state**, at the grades `k ≥ K`. -/
theorem upperDecoder_cutoff_orbitCode {K k : ℕ} (hK : K ≤ k)
    (N : Finset (Fin I.amalgam.card ⊕ Unit)) (P : CProf I) :
    upperDecoderAt k (k + 1) (bound I) P
      (visibilityReplace K K (donorMax N (orbitCode k P))) ≤
      visibilityReplace K K (donorMax N P) := by
  have hw := isWitness_upperDecoderAt (k := k) (K := k + 1) (w := P) (B := bound I) (by omega)
  rw [hw.visibilityReplace_comm _ K (by rw [stepSuppressor_of_le hK]; exact le_top) K le_rfl]
  refine monotone_visibilityReplace le_rfl ?_
  rcases N.eq_empty_or_nonempty with he | hne
  · rw [donorMax, he, sup_empty, upperDecoderAt_bot]; exact bot_le
  obtain ⟨f, hf, hfeq⟩ := exists_mem_eq_sup _ hne (orbitCode k P)
  rw [donorMax, hfeq, upperDecoderAt_orbitCode]
  exact le_donorMax hf

local notation "𝒦" => sCat I (g + 1) A

/-- **The first chain bound**: the section of the layer at `g + J + 1` of the padded tower reads
the controller of the orbit code at `K` of the padded bottom state of `P` at least at the cutoff
of `P`. -/
theorem le_pTower_hi : ∀ (J : ℕ) (P : CProf I) (i : Fin (𝒦).card),
    ((𝒦).equivFin.symm i).1 = orbitCode (g + 1) (pBot g J P) →
    P (Sum.inr ()) ≤ (pTower L A (J + 1)).σs P (pEmb J (Fin.natAdd L.S.card i))
  | 0, P, i, hi => by
    -- the layer of controllers is the padded next level of `L` read as a state level
    change P (Sum.inr ()) ≤ L.toS.pnextσ 𝒦 P (Fin.natAdd _ i)
    rw [SLvl.pnextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_natAdd]), SLvl.Φs_natAdd,
      hi]
    -- the row of the controller of the orbit code reads it at its agreement height with itself
    change P (Sum.inr ()) ≤ upperDecoderAt (g + 1) (g + 2) (bound I) P
      (agreementHeight (grid (g + 1) (bound I)) (orbitCode (g + 1) P) (orbitCode (g + 1) P))
    rw [agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
    have h := upperDecoderAt_orbitCode (k := g + 1) (K := g + 2) (B := bound I) (w := P)
      (Sum.inr ())
    refine le_of_eq_of_le h.symm ((isWitness_upperDecoderAt (by omega)).monotone ?_)
    exact le_gridPoint_of_mem_codeGrid (orbitCode_mem_codeGrid _ _ _)
  | J + 1, P, i, hi => by
    have ih := le_pTower_hi J (orbitCode (g + J + 2) P) i hi
    have hgr : (pTower L A (J + 1)).S.toCellScheme.grade (pEmb J (Fin.natAdd L.S.card i)) =
        g + 1 :=
      ((isGradePrefix_pEmb J).lowerEmb.grade_eq _).trans
        (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
    -- the section of the padded next level at an old controller, by definition
    change P (Sum.inr ()) ≤ (pTower L A (J + 1)).pnextσ (sCat I (g + (J + 1) + 1) A) P
      (Fin.castAdd _ (pEmb J (Fin.natAdd L.S.card i)))
    rw [SLvl.pnextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_castAdd, hgr]; omega),
      SLvl.Φs_castAdd]
    have h := upperDecoderAt_orbitCode (k := g + J + 2) (K := g + J + 2 + 1) (B := bound I)
      (w := P) (Sum.inr ())
    exact le_of_eq_of_le h.symm ((isWitness_upperDecoderAt (by omega)).monotone ih)

/-- **The second chain bound**: the section of the layer at `g + J + 1` of the padded tower reads
the controller of the partner, over a set `N` of fields, of the orbit code at `K` of the padded
bottom state of `P` at most at the cutoff cut over `N` of `P`, when that partner lowers the
cutoff. -/
theorem pTower_lo_le (N : Finset (Fin I.amalgam.card ⊕ Unit)) :
    ∀ (J : ℕ) (P : CProf I) (i : Fin (𝒦).card),
    ((𝒦).equivFin.symm i).1 = Function.update (orbitCode (g + 1) (pBot g J P)) (Sum.inr ())
      (cutoffCut (g + 1) N (orbitCode (g + 1) (pBot g J P))) →
    cutoffCut (g + 1) N (orbitCode (g + 1) (pBot g J P)) <
      orbitCode (g + 1) (pBot g J P) (Sum.inr ()) →
    (pTower L A (J + 1)).σs P (pEmb J (Fin.natAdd L.S.card i)) ≤ cutoffCut (g + 1) N P
  | 0, P, i, hi, hlt => by
    -- the layer of controllers is the padded next level of `L` read as a state level
    change L.toS.pnextσ 𝒦 P (Fin.natAdd _ i) ≤ _
    rw [SLvl.pnextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_natAdd]), SLvl.Φs_natAdd,
      hi]
    refine ((isWitness_upperDecoderAt (by omega)).monotone
      (agreementHeight_update_le (bot_mem_grid _ _) _ hlt)).trans ?_
    exact upperDecoder_cutoff_orbitCode le_rfl N P
  | J + 1, P, i, hi, hlt => by
    have ih := pTower_lo_le N J (orbitCode (g + J + 2) P) i hi hlt
    have hgr : (pTower L A (J + 1)).S.toCellScheme.grade (pEmb J (Fin.natAdd L.S.card i)) =
        g + 1 :=
      ((isGradePrefix_pEmb J).lowerEmb.grade_eq _).trans
        (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
    -- the section of the padded next level at an old controller, by definition
    change (pTower L A (J + 1)).pnextσ (sCat I (g + (J + 1) + 1) A) P
      (Fin.castAdd _ (pEmb J (Fin.natAdd L.S.card i))) ≤ _
    rw [SLvl.pnextσ_of_le (by rw [Scheme.appendFullCellsScheme_grade_castAdd, hgr]; omega),
      SLvl.Φs_castAdd]
    exact ((isWitness_upperDecoderAt (by omega)).monotone ih).trans
      (upperDecoder_cutoff_orbitCode (by omega) N P)

end Tower

/-! ### The separator through the orbit code -/

section Sep

variable {N : Finset (Fin I.amalgam.card ⊕ Unit)} {T : Set (Fin I.amalgam.card ⊕ Unit)}
  {o : Fin I.amalgam.card}

/-- **The orbit code keeps separated states**, at every grade. -/
theorem sepInv_orbitCode {j : ℕ} {P : CProf I} (h : SepInv N T o P) :
    SepInv N T o (orbitCode j P) := by
  obtain ⟨h0, ho, hT, hN⟩ := h
  have hkey : IsKey j P (P (Sum.inr ())) := isKey_apply_iff.mpr h0
  refine ⟨?_, ?_, fun x hx ↦ ?_, fun f hf hf0 k ↦ ?_⟩
  · rw [orbitCode_apply, Ne, orbitMap_eq_bot_iff]; exact h0
  · rw [orbitCode_apply, orbitCode_apply, ho]
  · rw [orbitCode_apply, orbitCode_apply, hT _ hx]
  · rw [orbitCode_apply, Ne, orbitMap_eq_bot_iff] at hf0
    have hlt := hN f hf hf0 j
    have hcb := codeBlock_lt_codeBlock hf0 hkey hlt
    exact visibilityReplace_lt_of_block_lt (visibilityReplace_orbitMap hf0)
      (visibilityReplace_orbitMap h0) hcb k

/-- **The padded bottom state of a separated state is separated.** -/
theorem sepInv_pBot {g : ℕ} : ∀ (J : ℕ) (P : CProf I), SepInv N T o P → SepInv N T o (pBot g J P)
  | 0, _, h => h
  | J + 1, _, h => sepInv_pBot J _ (sepInv_orbitCode h)

/-- **The cutoff cut of an orbit code lies in the grid.** -/
theorem cutoffCut_orbitCode_mem_grid (k : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (P : CProf I) : cutoffCut k N (orbitCode k P) ∈ grid k (bound I) := by
  rcases N.eq_empty_or_nonempty with he | hne
  · rw [cutoffCut, donorMax, he, sup_empty, visibilityReplace_bot]; exact bot_mem_grid _ _
  obtain ⟨f, -, hfeq⟩ := exists_mem_eq_sup _ hne (orbitCode k P)
  rw [cutoffCut, donorMax, hfeq]
  by_cases hf0 : P f = ⊥
  · rw [orbitCode_apply, hf0, orbitMap_bot, visibilityReplace_bot]; exact bot_mem_grid _ _
  · rw [orbitCode_apply, visibilityReplace_orbitMap hf0]
    refine gridPoint_mem_grid ((codeBlock_le _ _ _).trans ?_)
    have := keyRank_le_card k P (P f)
    rw [card_fields] at this
    simp only [bound]
    omega

/-- **The padded bottom state of a state with amalgam part lawful on the cut at `g + J + 1` has
amalgam part lawful on the cut at `g + 1`.** -/
theorem isCutLawful_pBot {g : ℕ} : ∀ (J : ℕ) (P : CProf I),
    IsCutLawful I (g + J + 1) (camal P) → IsCutLawful I (g + 1) (camal (pBot g J P))
  | 0, _, h => h
  | J + 1, P, h => isCutLawful_pBot J _ (by
      obtain ⟨hC, hD⟩ := h
      exact ⟨(hC.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap (g + J + 2) P)
          fun _ ↦ orbitMap_eq_bot_iff.mp).mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩,
        (hD.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap (g + J + 2) P)
          fun _ ↦ orbitMap_eq_bot_iff.mp).mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩⟩)

end Sep

end VaughtConjecture.ProfileTower

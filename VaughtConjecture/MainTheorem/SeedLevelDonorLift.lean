/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SeedLevelChoice

/-!
# The lift of the re-rendered levels from the donor face

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

The levels (`Seed.lvLevel`) lift capped from the donor face into the full face at every grade
`j + 1 ≤ n + 1` (`Seed.lvLevel_cappedLift_donor`), for requests calibrated on the class over a
legal donor with a nonempty root.  At an onto root the donor face is the second coatom
(`Seed.donorFace_eq_coatom_of_surjective`), so the levels lift from the second coatom at every
grade `j + 1 ≤ m + 1` (`Seed.lvLevel_cappedLift_coatom_of_surjective`; at the seed position,
`StageType.lvLevel_cappedLift_coatoms_atSeed`), and so do the levels with their copies at the mixed
faces (`Seed.lvRep_cappedLift_coatom_seedChoice`).

* **The donor state step** (`Seed.exists_donorStateStep`): from an anchor `R₀` of the catalogue
  at the grade `k ≤ n + 1` and a prescription below the donor face at `k` agreeing with it capped
  at a cut `h`, a state of the attachment that is the prescription below the donor face, lawful
  below `(univ, k)`, admitted at `k`, agreeing with `R₀` capped at `h`, with values self-visible
  at `1`.  The attachment lifts capped from the donor face (`Seed.cappedLift_attachment_univ`).
  Admission is asked only from the threshold on, and a grade `k ≤ n + 1 ≤ threshold` reaches it
  only at `k = n + 1 = threshold`; there the cells of the grade `n + 1` outside the donor face are
  capped at `h` (`CellScheme.Rows.isLawfulBelow_capOn`), so the cap value is at most `h`, and the
  reads of the anchor capped at `h` are those of the state
  (`StageType.GrowthRequests.CorrectAt.map`, `StageType.GrowthRequests.CorrectAt.of_min`).  Neither
  the labels pair nor the relative lift is used.
* **The next level** (`Seed.ALvl.Good.cappedLift_next_donor`): the composition of
  `Seed.ALvl.Good.cappedLift_next` with the donor face in place of the context coatom: the short
  lift at a serving row (`Seed.ALvl.Good.cappedLiftAtShort_next_donor`) is the orbit decoder of the
  state of the donor state step applied to the row labelling of its orbit code; the cap `⊥`
  (`Seed.ALvl.Good.hasOwnerCappedLifts_next_bot_donor`) from the bottom state; a cell at
  `(donor face, j + 2)` from the legal donor.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-! ### The donor state step -/

/-- **The donor state step at the grade `k ≤ n + 1`** (see the module docstring). -/
theorem exists_donorStateStep {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 1) {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) fun a ↦ R₀ a)
    (hR₀v : ∀ e, IsSelfVisible 1 (R₀ e)) (hR₀A : I.attachAdmits g hd Q k R₀)
    {h : Label.{u}} (hh : IsSelfVisible k h) {V : Fin (I.attachment g).card → Label.{u}}
    (hV : (I.attachment g).rows.IsLawfulBelow
      (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k) fun a ↦ V a)
    (hVR : ∀ a ∈ (I.attachment g).toCellScheme.below
      (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k), min (V a) h = min (R₀ a) h) :
    ∃ W : Fin (I.attachment g).card → Label.{u},
      (∀ a ∈ (I.attachment g).toCellScheme.below
        (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k), W a = V a) ∧
      (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k) (fun a ↦ W a) ∧
      I.attachAdmits g hd Q k W ∧ (∀ a, min (W a) h = min (R₀ a) h) ∧
      ∀ e, IsSelfVisible 1 (W e) := by
  classical
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hDdef
  have hDc : #D = n + 1 := by rw [hDdef, card_map, card_univ, Fintype.card_fin]
  have hL : (I.attachment g).rows.CappedLift (X := (D, k))
      (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨subset_univ _, le_rfl⟩ :=
    cappedLift_attachment_univ (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; omega) (donor_mem_faces hd) hk
      (by simp only [card_map, card_univ, Fintype.card_fin]; exact hkn) (.inr subset_rfl)
  obtain ⟨r, hr, hrc, hrp⟩ := (Rows.cappedLift_iff_forall_exists _).mp hL h hh
    (fun e ↦ V e) (fun e ↦ R₀ e) hV hR₀ fun e ↦ (hVR e.1 e.2).symm
  set P' : Fin (I.attachment g).card → Label.{u} :=
    Rows.extendBot ((univ : Finset (Fin (m + 2))), k) r with hP'def
  have hP'b : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
      fun a ↦ P' a := Rows.isLawfulBelow_extendBot.mpr hr
  have hgc (a : Fin (I.attachment g).card) :
      (I.attachment g).toCellScheme.grade a ≤ #((I.attachment g).toCellScheme.scope a) :=
    (I.isWellFormed_attachment g).isWellFormed.grade_le_card a
  -- the cells of the grade `n + 1` outside the donor face, capped when `k = n + 1`
  set K : Fin (I.attachment g).card → Prop := fun a ↦ k = n + 1 ∧
    (I.attachment g).toCellScheme.grade a = k ∧ ¬ (I.attachment g).toCellScheme.scope a ⊆ D
    with hKdef
  set P : Fin (I.attachment g).card → Label.{u} := fun a ↦ if K a then min (P' a) h else P' a
    with hPdef
  have hPb : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
      fun a ↦ P a := by
    refine Rows.isLawfulBelow_capOn hP'b hh K (fun a h ↦ h.2.1) (fun e s he hes hs ↦ ?_)
      (fun s t hst hg ht hKt ↦ ?_) (fun u t hu hKt ↦ ?_)
    · have h1 : (I.attachment g).toCellScheme.grade e ≤ (I.attachment g).toCellScheme.grade s :=
        hes.2
      have h2 : (I.attachment g).toCellScheme.grade s ≤ k := hs.2
      exact ⟨he.1, by omega, fun hsD ↦ he.2.2 (hes.1.trans hsD)⟩
    · refine ⟨hKt.1, hg.trans hKt.2.1, fun hsD ↦ ?_⟩
      have htC : (I.attachment g).toCellScheme.scope t ⊆
          univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) :=
        (I.scope_attachment g t).resolve_right hKt.2.2
      have hroot := card_le_card (subset_inter (hst.trans htC) hsD)
      rw [card_root] at hroot
      have := hgc s
      have := hKt.1
      have := hKt.2.1
      omega
    · have hg' : (I.attachment g).toCellScheme.grade u = (I.attachment g).toCellScheme.grade t :=
        congrArg Prod.snd hu
      have hs' : (I.attachment g).toCellScheme.scope u = (I.attachment g).toCellScheme.scope t :=
        congrArg Prod.fst hu
      exact ⟨hKt.1, hg'.trans hKt.2.1, hs' ▸ hKt.2.2⟩
  have hPc (a : Fin (I.attachment g).card) : min (P a) h = min (P' a) h := by
    by_cases hKa : K a
    · simp only [hPdef, hKa, ite_true, min_assoc, min_self]
    · simp only [hPdef, hKa, ite_false]
  set W : Fin (I.attachment g).card → Label.{u} :=
    fun a ↦ if (I.attachment g).toCellScheme.grade a ≤ k then P a else R₀ a with hWdef
  have hWR (a : Fin (I.attachment g).card) : min (W a) h = min (R₀ a) h := by
    by_cases hak : (I.attachment g).toCellScheme.grade a ≤ k
    · have hau : a ∈ (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), k) :=
        ⟨subset_univ _, hak⟩
      simp only [hWdef, hak, ite_true]
      rw [hPc, hP'def, Rows.extendBot_of_mem r hau, hrc ⟨a, hau⟩]
    · simp only [hWdef, hak, ite_false]
  have hWl : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), k)
      fun a ↦ W a :=
    (Rows.isLawfulBelow_congr (w := fun a ↦ P a) (w' := fun a ↦ W a) fun a ha ↦ by
      exact (ite_eq_left (show (I.attachment g).toCellScheme.grade a ≤ k from ha.2)).symm).mp hPb
  refine ⟨W, fun a ha ↦ ?_, hWl, ?_, hWR, fun e ↦ ?_⟩
  · -- the prescription below the donor face
    have hKa : ¬ K a := fun hK ↦ hK.2.2 ha.1
    have hau : a ∈ (I.attachment g).toCellScheme.below ((univ : Finset (Fin (m + 2))), k) :=
      (I.attachment g).toCellScheme.below_mono
        (⟨subset_univ _, le_rfl⟩ : ((D, k) : Finset (Fin (m + 2)) × ℕ) ≤ (univ, k)) ha
    have e1 : W a = P' a := by
      change (if _ then P a else R₀ a) = _
      rw [ite_eq_left (show (I.attachment g).toCellScheme.grade a ≤ k from hau.2)]
      change (if K a then _ else _) = _
      rw [ite_eq_right hKa]
    rw [e1, hP'def, Rows.extendBot_of_mem r hau]
    exact hrp ⟨a, ha⟩
  · -- admitted at `k`: only at `k = n + 1 = threshold`, through the cap at `h`
    intro hN hcls hcap y
    have hNk : Q.threshold = k := le_antisymm hN (hkn.trans hQ.arity)
    have hk' : k = n + 1 := le_antisymm hkn (hQ.arity.trans hN)
    have hcN : IsSelfVisible Q.threshold h := hNk ▸ hh
    have hagr (a : Fin (I.attachment g).card) :
        min (I.attachHatAt g Q.threshold W a) h = min (I.attachHatAt g Q.threshold R₀ a) h := by
      unfold attachHatAt
      split_ifs
      · exact hWR a
      · rfl
    have hcapg : (I.attachment g).toCellScheme.grade (I.attachCtxCell g Q.cap) = k :=
      (grade_attachCtxCell Q.cap).trans hNk
    have hcapK : K (I.attachCtxCell g Q.cap) := by
      refine ⟨hk', hcapg, fun hsub ↦ not_map_castSuccEmb_subset_donor (g := g) ?_⟩
      have hsc : (I.attachment g).toCellScheme.scope (I.attachCtxCell g Q.cap) =
          univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) := by
        rw [attachCtxCell, Scheme.scope_faceCell, hQ.scope_cap]
      exact hsc ▸ hsub
    have hhat : I.attachHatAt g Q.threshold W (I.attachCtxCell g Q.cap) =
        min (P' (I.attachCtxCell g Q.cap)) h := by
      unfold attachHatAt
      rw [hcapg, hNk, ite_eq_left le_rfl]
      simp only [hWdef, hcapg, le_refl, ite_true, hPdef, hcapK]
    have hle : I.attachHatAt g Q.threshold W (I.attachCtxCell g Q.cap) ≤ h :=
      hhat ▸ min_le_right _ _
    have hc0 : h ≠ ⊥ := fun h0 ↦ hcap (by beta_reduce; rw [hhat, h0, min_bot_right])
    have hbot (a : Fin (I.attachment g).card) :
        I.attachHatAt g Q.threshold W a = ⊥ ↔ I.attachHatAt g Q.threshold R₀ a = ⊥ := by
      have h' := hagr a
      constructor
      · intro h0
        rw [h0, min_bot_left] at h'
        exact (min_eq_bot.mp h'.symm).resolve_right hc0
      · intro h0
        rw [h0, min_bot_left] at h'
        exact (min_eq_bot.mp h').resolve_right hc0
    have hA := hR₀A hN (fun x hx ↦ (hbot _).symm.trans (hcls x hx))
      (fun h0 ↦ hcap ((hbot _).mpr h0)) y
    have hmap := hA.map (θ := fun x ↦ min x h) (fun _ _ h' ↦ min_le_min_right h h')
      (min_bot_left h) (fun i hi x ↦ (visibilityReplace_min_of_isSelfVisible hi hcN x).symm)
      (fun hj ↦ (hQ.ref y hj).2.1) hQ.marker.2.1
    have hmap' : Q.CorrectAt (fun x ↦ min (I.attachHatAt g Q.threshold W (I.attachCtxCell g x)) h)
        y (min (I.attachHatAt g Q.threshold W (I.attachDonCell g hd y)) h) := by
      have e1 : (fun x ↦ min (I.attachHatAt g Q.threshold W (I.attachCtxCell g x)) h) =
          (fun x ↦ min x h) ∘ fun x ↦ I.attachHatAt g Q.threshold R₀ (I.attachCtxCell g x) :=
        funext fun x ↦ hagr _
      rw [e1, hagr]
      exact hmap
    exact hmap'.of_min hle hcN (fun hj ↦ (hQ.ref y hj).2.1) hQ.marker.2.1
  · -- values self-visible at `1`
    by_cases hek : (I.attachment g).toCellScheme.grade e ≤ k
    · have ho := (Rows.isLawfulBelow_iff_forall.mp hWl).1 e ⟨subset_univ _, hek⟩
      exact ho.mono ((I.isWellFormed_attachment g).isWellFormed.grade_pos e)
    · simp only [hWdef, hek, ite_false]
      exact hR₀v e

/-! ### The next level from the donor face -/

namespace ALvl.Good

variable {j : ℕ} {H B : ℕ}
  {N : I.ALvl g H (j + 1)} {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
  {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

variable (hN : N.Good B (lvAdm hd Q))
include hN

/-- A cell of the next scheme below the donor face is a cell of the attachment. -/
theorem exists_attEmb_of_mem_donor (C : Finset (Fin (I.attachment g).card → Label.{u})) {k : ℕ}
    {z : Fin (N.nS B C).card}
    (hz : z ∈ (N.nS B C).toCellScheme.below
      (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k)) :
    ∃ a, z = Fin.castAdd _ (N.attEmb a) ∧
      a ∈ (I.attachment g).toCellScheme.below
        (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k) := by
  induction z using Fin.addCases with
  | right i =>
    exfalso
    have h := hz.1
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd] at h
    exact map_extendByLast_ne_univ g (univ_subset_iff.mp h)
  | left e =>
    have hz' := hz
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd] at hz'
    have hsc : N.S.toCellScheme.scope e ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) :=
      hz'.1
    obtain ⟨a, rfl⟩ := hN.mem_range e fun h ↦
      map_extendByLast_ne_univ g (univ_subset_iff.mp (h ▸ hsc))
    refine ⟨a, rfl, ?_⟩
    rw [CellScheme.mem_below, ← hN.gradedIndex_attEmb]
    exact hz'

/-- Lawfulness below the donor face in the next scheme is lawfulness on the attachment. -/
theorem isLawfulBelow_donor_iff (C : Finset (Fin (I.attachment g).card → Label.{u})) {k : ℕ}
    {w : Fin (N.nS B C).card → Label.{u}} :
    (N.nS B C).rows.IsLawfulBelow (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k)
        (fun z ↦ w z) ↔
      (I.attachment g).rows.IsLawfulBelow (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k)
        (fun a ↦ w (Fin.castAdd _ (N.attEmb a))) := by
  rw [Scheme.isLawfulBelow_appendFullCells_iff fun h ↦
    map_extendByLast_ne_univ g (univ_subset_iff.mp h.1)]
  exact hN.isLawfulBelow_old_iff
    (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k)) (map_extendByLast_ne_univ g)
    (w := fun e ↦ w (Fin.castAdd _ e))

/-- **The short lift from the donor face at a serving row of the next level** at the grade
`j + 2 ≤ n + 1`: the donor state step (`Seed.exists_donorStateStep`) in place of the state step
of `Seed.ALvl.Good.cappedLiftAtShort_next`. -/
theorem cappedLiftAtShort_next_donor (hn : 0 < n) (hQ : Q.ClassCalibrated hte)
    (hkn : j + 2 ≤ n + 1) (hB : 2 * (I.attachment g).card ≤ B)
    {u : Fin (N.nS B (I.lvCat g B hd Q (j + 2))).card}
    (hu : (N.nS B (I.lvCat g B hd Q (j + 2))).toCellScheme.gradedIndex u =
      ((univ : Finset (Fin (m + 2))), j + 2)) :
    (N.nS B (I.lvCat g B hd Q (j + 2))).rows.CappedLiftAtShort
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), j + 2))
      (Y := ((univ : Finset (Fin (m + 2))), j + 2)) ⟨subset_univ _, le_rfl⟩
      ((N.nS B (I.lvCat g B hd Q (j + 2))).rows.rowBelow u hu) := by
  classical
  set C := I.lvCat g B hd Q (j + 2) with hC
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hDdef
  intro h hh hs hb f hf _ hfS
  obtain ⟨i, rfl⟩ := exists_natAdd_of_gradedIndex C hu
  set R := (C.equivFin.symm i).1 with hRdef
  obtain ⟨hRB, hRl, hRv, hRc, hRA⟩ := mem_lvCat.mp (C.equivFin.symm i).2
  have hR1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ R e) := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by simpa using hB
  have hS (e : (N.nS B C).toCellScheme.below ((univ : Finset (Fin (m + 2))), j + 2)) :
      (N.nS B C).rows.rowBelow (Fin.natAdd _ i) hu e = N.Φ B C R e.1 :=
    Scheme.appendFullCells_row_natAdd i _
  -- the prescription on the attachment
  set fT := Rows.extendBot (D, j + 2) f with hfT
  have hV : (I.attachment g).rows.IsLawfulBelow (D, j + 2)
      fun a ↦ fT (Fin.castAdd _ (N.attEmb a)) :=
    (hN.isLawfulBelow_donor_iff C).mp (Rows.isLawfulBelow_extendBot.mpr hf)
  have hmemD (a : Fin (I.attachment g).card)
      (ha : a ∈ (I.attachment g).toCellScheme.below (D, j + 2)) :
      Fin.castAdd C.card (N.attEmb a) ∈ (N.nS B C).toCellScheme.below (D, j + 2) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      hN.gradedIndex_attEmb]
    exact ha
  have hVR (a : Fin (I.attachment g).card)
      (ha : a ∈ (I.attachment g).toCellScheme.below (D, j + 2)) :
      min (fT (Fin.castAdd _ (N.attEmb a))) h = min (R a) h := by
    rw [hfT, Rows.extendBot_of_mem f (hmemD a ha), hfS, hS]
    change min (N.Φ B C R (Fin.castAdd _ (N.attEmb a))) h = _
    rw [ALvl.Φ_castAdd, hN.literal R hR1]
  -- the donor state step at the grade `j + 2`
  obtain ⟨W, hWD, hWl, hWA, hWR, hWv⟩ := exists_donorStateStep hte hn hd hQ (k := j + 2)
    (by omega) hkn hRl hRv hRA hh hV hVR
  set P := orbitCode (j + 2) W with hPdef
  have hPC : P ∈ C := mem_lvCat.mpr ⟨fun e ↦ orbitMap_mem_codeGrid hcB _,
    hWl.orbitCode fun e ↦ e.2.2, fun e ↦ isSelfVisible_one_orbitCode (by omega) (hWv e),
    orbitCode_orbitCode, attachAdmits_orbitCode hQ hWA⟩
  obtain ⟨hPB, hPl, -, hPc, -⟩ := mem_lvCat.mp hPC
  have hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ P e) := hPl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hPR : ∀ a, min (P a) h = min (R a) h := min_orbitCode_eq hh hs hRc hWR
  have hPW : ∀ a, min (orbitCode (j + 2) W a) h = min (W a) h :=
    fun a ↦ (hPR a).trans (hWR a).symm
  refine ⟨fun z ↦ orbitDecoder (j + 2) W h (N.Φ B C P z.1),
    (hN.isLawfulBelow_Φ hPC).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb.ne') (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb.ne'),
    fun e ↦ ?_, fun z ↦ ?_⟩
  · -- the prescription below the donor face
    obtain ⟨a, he, ha⟩ := hN.exists_attEmb_of_mem_donor C e.2
    change orbitDecoder (j + 2) W h (N.Φ B C P e.1) = f e
    rw [he, ALvl.Φ_castAdd, hN.literal P hP1, orbitDecoder_orbitCode hPW, hWD a ha, hfT, ← he]
    exact Rows.extendBot_of_mem f e.2
  · -- the capped agreement with the row of `R`
    rw [hS z]
    obtain ⟨z, -⟩ := z
    dsimp only
    induction z using Fin.addCases with
    | left e =>
      rw [ALvl.Φ_castAdd, ALvl.Φ_castAdd,
        min_orbitDecoder_eq_of_isReadableAt hh hPW (hN.readable P hPc hPB hP1 e)]
      exact hN.capAgree P R hP1 hR1 hPB h hh hs hPR e
    | right i' =>
      rw [ALvl.Φ_natAdd, ALvl.Φ_natAdd, min_orbitDecoder_eq
        (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs (fun e ↦ ⟨hPB e, hRB e⟩) hPR _

/-- **The owner-capped lift from the donor face at the cap `⊥` of the next level** at the grade
`j + 2 ≤ n + 1`: the donor state step at the cut `⊥` from the bottom state. -/
theorem hasOwnerCappedLifts_next_bot_donor (hn : 0 < n) (hQ : Q.ClassCalibrated hte)
    (hkn : j + 2 ≤ n + 1) (hB : 2 * (I.attachment g).card ≤ B) :
    (N.nS B (I.lvCat g B hd Q (j + 2))).rows.HasOwnerCappedLifts
      (subset_univ (univ.map (extendByLast (g.trans Fin.castSuccEmb)))) (j + 1) ⊥ := by
  classical
  set C := I.lvCat g B hd Q (j + 2) with hC
  set D := univ.map (extendByLast (g.trans Fin.castSuccEmb)) with hDdef
  intro p q hp _ _ o ho _ _
  have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by simpa using hB
  have hM : IsSelfVisible (j + 1 + 1) (p o) := hp.isSelfVisible_of_gradedIndex_eq ho
  have hp' := hp.min_const_of_isSelfVisible hM
  set pT := Rows.extendBot (D, j + 1 + 1) (fun e ↦ min (p e) (p o)) with hpT
  have hV : (I.attachment g).rows.IsLawfulBelow (D, j + 2)
      fun a ↦ pT (Fin.castAdd _ (N.attEmb a)) :=
    (hN.isLawfulBelow_donor_iff C).mp (Rows.isLawfulBelow_extendBot.mpr hp')
  obtain ⟨W, hWD, hWl, hWA, -, hWv⟩ := exists_donorStateStep hte hn hd hQ (k := j + 2)
    (by omega) hkn (R₀ := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
    (fun _ ↦ isSelfVisible_bot 1) (I.attachAdmits_bot g hd Q _) (isSelfVisible_bot _)
    (V := fun a ↦ pT (Fin.castAdd _ (N.attEmb a))) hV fun _ _ ↦ by simp only [min_bot_right]
  set P := orbitCode (j + 2) W with hPdef
  have hPC : P ∈ C := mem_lvCat.mpr ⟨fun e ↦ orbitMap_mem_codeGrid hcB _,
    hWl.orbitCode fun e ↦ e.2.2, fun e ↦ isSelfVisible_one_orbitCode (by omega) (hWv e),
    orbitCode_orbitCode, attachAdmits_orbitCode hQ hWA⟩
  obtain ⟨-, hPl, -, -, -⟩ := mem_lvCat.mp hPC
  have hP1 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 1)
      (fun e ↦ P e) := hPl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hPW (a : Fin (I.attachment g).card) :
      min (orbitCode (j + 2) W a) (gridPoint (j + 2) 0) = min (W a) (gridPoint (j + 2) 0) :=
    min_orbitCode_gridPoint_zero a
  refine ⟨fun z ↦ orbitDecoder (j + 2) W (gridPoint (j + 2) 0) (N.Φ B C P z.1),
    (hN.isLawfulBelow_Φ hPC).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint _ 0) (gridPoint_ne_bot _ 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot _ 0)), fun e ↦ ?_,
    fun _ ↦ by rw [min_bot_right, min_bot_right]⟩
  obtain ⟨a, he, ha⟩ := hN.exists_attEmb_of_mem_donor C e.2
  change orbitDecoder (j + 2) W (gridPoint (j + 2) 0) (N.Φ B C P e.1) = min (p e) (p o)
  rw [he, ALvl.Φ_castAdd, hN.literal P hP1, orbitDecoder_orbitCode hPW, hWD a ha, hpT, ← he]
  exact Rows.extendBot_of_mem _ e.2

/-- **The lift of the next level from the donor face at the grade `j + 2 ≤ n + 1`**, for requests
calibrated on the class over a legal donor with a nonempty root: the lift at the grade `j + 1`
and the owner-capped lifts at every cap self-visible at `j + 2` (at `⊥`,
`Seed.ALvl.Good.hasOwnerCappedLifts_next_bot_donor`; at a positive cap from the serving rows,
`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short` with
`Seed.ALvl.Good.cappedLiftAtShort_next_donor`) compose by
`CellScheme.Rows.cappedLift_of_ownerCappedLift`; the cell at `(donor face, j + 2)` is a cell of
the legal donor of full scope. -/
theorem cappedLift_next_donor (hdL : d.IsLegal) (hn : 0 < n) (hQ : Q.ClassCalibrated hte)
    (hkn : j + 2 ≤ n + 1) (hB : 2 * (I.attachment g).card ≤ B)
    (hlift : (N.nS B (I.lvCat g B hd Q (j + 2))).rows.CappedLift
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), j + 1))
      (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨subset_univ _, le_rfl⟩) :
    (N.nS B (I.lvCat g B hd Q (j + 2))).rows.CappedLift
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), j + 2))
      (Y := ((univ : Finset (Fin (m + 2))), j + 2)) ⟨subset_univ _, le_rfl⟩ := by
  classical
  set C := I.lvCat g B hd Q (j + 2) with hC
  have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
  have hNext := hN.next hQ (by omega) hB
  have hbot : (fun _ ↦ ⊥ : Fin (I.attachment g).card → Label.{u}) ∈ C :=
    mem_lvCat.mpr ⟨fun _ ↦ mem_insert_self _ _, Rows.isLawfulBelow_const_bot _,
      fun _ ↦ isSelfVisible_bot 1, funext fun _ ↦ orbitCode_eq_bot_iff.mpr rfl,
      I.attachAdmits_bot g hd Q _⟩
  have hY : ∃ t : Fin (N.nS B C).card, (N.nS B C).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin (m + 2))), j + 1 + 1) :=
    ⟨Fin.natAdd _ (C.equivFin ⟨_, hbot⟩), Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩
  refine Rows.cappedLift_of_ownerCappedLift (j := j + 1) (subset_univ _) ?_ hlift
    fun c hc ↦ ?_
  · obtain ⟨y, hy⟩ := StageType.exists_gradedIndex_univ_of_isLegal hdL (k := j + 2)
      (by omega) hkn
    refine ⟨Fin.castAdd _ (N.attEmb (I.attachDonCell g hd y)), ?_⟩
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hN.gradedIndex_attEmb]
    refine Prod.ext ?_ ((Scheme.grade_faceCell (I.comap_donor_attachment_scheme g hd) y).trans
      (congrArg Prod.snd hy))
    change (I.attachment g).toCellScheme.scope (I.attachDonCell g hd y) = _
    have hsy : d.toCellScheme.scope y = univ := congrArg Prod.fst hy
    rw [attachDonCell, Scheme.scope_faceCell, hsy]
  · by_cases hc0 : c = ⊥
    · subst hc0
      exact hN.hasOwnerCappedLifts_next_bot_donor hn hQ hkn hB
    refine Rows.hasOwnerCappedLifts_of_rows_short (subset_univ _) (bot_lt_iff_ne_bot.mpr hc0)
      hc hY fun u hu ↦ ⟨hNext.consistent u, fun e ↦ ?_, fun e ↦ ?_,
        hN.cappedLiftAtShort_next_donor hn hQ hkn hB hu⟩
    all_goals
      obtain ⟨i, rfl⟩ := exists_natAdd_of_gradedIndex C hu
      obtain ⟨hRB, hRl, -, -, -⟩ := mem_lvCat.mp (C.equivFin.symm i).2
      have hmem := hN.Φ_mem_codeGrid C hRB
        (hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩) e.1
      rw [show (N.nS B C).rows.rowBelow (Fin.natAdd _ i) hu e = N.Φ B C (C.equivFin.symm i).1 e.1
        from Scheme.appendFullCells_row_natAdd i _]
    · exact isShort_of_mem_codeGrid hmem
    · exact ne_top_of_le_ne_top (gridPoint_ne_top _ _) (le_gridPoint_of_mem_codeGrid hmem)

end ALvl.Good

/-! ### The levels from the donor face, and from the second coatom at an onto root -/

/-- **The first level lifts from the donor face at the grade one** (the ladder base,
`Scheme.cappedLift_ladderBase_rankMember` with `Seed.cappedLift_attachment_univ_one`). -/
theorem lvLevel1_cappedLift_donor_one {H : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.lvLevel1 g H).S.rows.CappedLift
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_univ _, le_rfl⟩ :=
  Scheme.cappedLift_ladderBase_rankMember (hS := (I.attachmentBase g).noFull)
    (I.attachmentBase g).wf hH hcard _
    (fun h ↦ map_extendByLast_ne_univ g (univ_subset_iff.mp h.1))
    (cappedLift_attachment_univ_one hdF hrF hr1 hdF (by simp) (.inr subset_rfl))

/-- **The levels lift from the donor face at every grade `j + 1 ≤ n + 1`**, for requests
calibrated on the class over a legal donor with a nonempty root (no labels pair, no relative
lift): at the grade one the ladder base (`Seed.lvLevel1_cappedLift_donor_one`), then the next
level (`Seed.ALvl.Good.cappedLift_next_donor`). -/
theorem lvLevel_cappedLift_donor {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hdL : d.IsLegal)
    (hn : 0 < n) (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ n + 1 → (I.lvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), j + 1))
      (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨subset_univ _, le_rfl⟩
  | 0, _ => lvLevel1_cappedLift_donor_one hH hcard (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; exact hn)
  | j + 1, hj => by
    have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
    have hN := lvLevel_good (B := B) (hd := hd) hH hcard hQ hB j (by omega)
    have hlow := lvLevel_cappedLift_donor hH hcard hte hdL hn hd hQ hB j (by omega)
    have hlift := (ALvl.cappedLift_nS_iff (B := B) (I.lvLevel g H B hd Q j)
      (I.lvCat g B hd Q (j + 2)) _ fun h ↦ absurd h.2 (by simp only; omega)).mpr hlow
    exact hN.cappedLift_next_donor hdL hn hQ (by omega) hB hlift

/-- **At an onto root the levels lift from the second coatom at every grade `j + 1 ≤ m + 1`**:
the second coatom is the donor face (`Seed.donorFace_eq_coatom_of_surjective`) and `m ≤ n`. -/
theorem lvLevel_cappedLift_coatom_of_surjective {H B : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {p₀ : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hdL : d.IsLegal)
    (hn : 0 < n) (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) (hg : Function.Surjective g) :
    ∀ j, j + 1 ≤ m + 1 → (I.lvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
      (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  intro j hj
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_surjective g hg
  have hl := lvLevel_cappedLift_donor hH hcard hte hdL hn hd hQ hB j (by omega)
  have key : ∀ (W : Finset (Fin (m + 2)))
      (h : ((W, j + 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), j + 1)),
      W = univ.map (extendByLast (g.trans Fin.castSuccEmb)) →
        (I.lvLevel g H B hd Q j).S.rows.CappedLift h := by
    rintro W h rfl
    exact hl
  exact key _ _ (donorFace_eq_coatom_of_surjective g hg).symm

/-- **The second coatom at an onto root, at the choice**: at every seed with the data of the seed
position and an onto root, the levels at `Seed.seedHeightLevel`, `Seed.seedBlockBound` lift
capped from the second coatom into `(univ, j + 1)` for every `j + 1 ≤ m + 1`.  The threshold is
then `n + 1 = m + 1` (`StageType.GrowthRequests.ClassCalibrated.threshold_eq_of_surjective`). -/
theorem lvLevel_cappedLift_coatom_seedChoice {p : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) :
    ∀ j, j + 1 ≤ m + 1 →
      (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound g) hdA Q j).S.rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  lvLevel_cappedLift_coatom_of_surjective (seedHeightLevel_pos I g)
    (card_attachmentBase_le_seedHeightLevel I g) hte hd.1 hn hdA hQ
    (two_mul_card_le_seedBlockBound I g) hg

/-- **The replicated levels lift from the second coatom at an onto root, at the choice**: the
level at the grade `J + 1 ≤ m + 2` with its copies at the mixed faces, at every grade
`j + 1 ≤ min (J + 1) (m + 1)` (`Seed.lvLevel_cappedLift_iff_of_le`,
`Seed.ALvl.Good.cappedLift_rep_donor`). -/
theorem lvRep_cappedLift_coatom_seedChoice {p : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) (J : ℕ) (hJ : J + 1 ≤ m + 2) (j : ℕ) (hjJ : j ≤ J)
    (hjm : j + 1 ≤ m + 1) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound I g) (hd := hdA) J hJ).rep.rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  ALvl.Good.cappedLift_rep_donor _ _ rfl (donorFace_eq_coatom_of_surjective g hg).symm.subset
    ((lvLevel_cappedLift_iff_of_le le_rfl _ J hjJ).mpr
      (lvLevel_cappedLift_coatom_seedChoice hte hd hn hdA hQ hg j hjm))

end Seed

namespace StageType

/-- **The two coatom lifts of the levels at the seed position**, with exactly the binders of
`StageType.HasLadderGrowthCarriersStableAtSeed`: at the seed of
`StageType.exists_growthSeed_of_isSuccLimit` and the choice `Seed.seedHeightLevel`,
`Seed.seedBlockBound`, the levels lift capped from the context coatom into `(univ, j + 1)` for
every `j + 1 ≤ m + 1` (`Seed.lvLevel_cappedLift_seedChoice`), and, at an onto root, from the
second coatom as well (`Seed.lvLevel_cappedLift_coatom_seedChoice`). -/
theorem lvLevel_cappedLift_coatoms_atSeed {α : Ordinal.{u}} {n m : ℕ}
    (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m) (p' : StageType.{u} α m)
    (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal)
    (hp' : restrictFace Fin.castSuccEmb t' = some p') (p : StageType.{u} α n)
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
    (hd : d ∈ p.cofaces) (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∃ (I : Seed.{u} α m) (hI : I.left = t')
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d),
      (∀ j, j + 1 ≤ m + 1 →
        (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound g) hdA (hI ▸ Q) j).S.rows.CappedLift
          (X := (univ.erase (Fin.last (m + 1)), j + 1))
          (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩) ∧
      (Function.Surjective g → ∀ j, j + 1 ≤ m + 1 →
        (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound g) hdA (hI ▸ Q) j).S.rows.CappedLift
          (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
          (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩) := by
  obtain ⟨I, rfl, hdA⟩ :=
    exists_growthSeed_of_isSuccLimit hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd
  exact ⟨I, rfl, hdA, Seed.lvLevel_cappedLift_seedChoice hte hd hn hdA hpair hQ hrel,
    Seed.lvLevel_cappedLift_coatom_seedChoice hte hd hn hdA hQ⟩

end StageType

end VaughtConjecture

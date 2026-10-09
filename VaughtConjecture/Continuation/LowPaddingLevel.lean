/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowPaddingObstruction
import VaughtConjecture.Extension.AdmittedCompletion

/-!
# The padded catalogue layer: the controllers read at the owner's cutoff

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

The section of the catalogue layer over the canonical levels reads the controllers at the code of
a profile with the cutoff `⊥` (`ProfileTower.Lvl.catσ`), so every cell of full scope above `K`
reads a controller of positive cutoff as `⊥` (`ProfileTower.lowDisplay_label_eq_bot`).  The
**padded section** (`ProfileTower.Lvl.padσ`) reads them at the code `c` of the profile with the
cutoff `c o`, the code of the owner (`ProfileTower.padCut`): a field of the profile, so capped
agreement of profiles is capped agreement of the padded codes, cutoff included, and the section
agrees capped as before.  At the actual profile the owner is `⊤` and the padded code is the
profile of a controller read at the ceiling of the grid; the padded section reads it above the
owner's label (`VaughtConjecture.Continuation.LowPaddingTower`).

**The padded level** (`ProfileTower.Lvl.padNext`).  The catalogue layer of a predicate `A` (the
same scheme as `ProfileTower.Lvl.catNext`) with the padded section.  Its section at `P` is lawful
when the padded code of `P` satisfies `A`; so it is a level good relative to a family `D`
(`ProfileTower.Lvl.GoodOn`) whose catalogue at `g + 1` has padded codes in `A`
(`ProfileTower.Lvl.Good.padNext`, compiled in this repository).  Every field other than lawfulness
is that of the catalogue layer: consistency, the lift from the two coatoms at `g + 1` and the cell
at `(univ, g + 1)` are statements about the scheme; literal, in the code grid, capped agreement and
readable are proved as for `ProfileTower.Lvl.Good.catNext` with the cutoff `c o` in place of `⊥`.

**The owner-LOW catalogues** (`ProfileTower.ownLow`, `ProfileTower.ownCat`).  A profile `w` is
**owner-LOW** when `w` with the cutoff `w o` satisfies the LOW clause: if the donor maximum is below
the owner, every donor top is at least the owner (`ProfileTower.ownLow_iff`; the frontier is at most
the owner).  The owner-LOW catalogue at `k` is `rowCat ownLow k`.  Owner-LOW profiles are kept by
every monotone map fixing `⊥` applied at the designated fields (`ProfileTower.ownLow_of_map`), so
the catalogues satisfy the downward clause from `K` on (`ProfileTower.code_mem_ownCat`), the glued
labelling is owner-LOW (its owner and donor tops are `⊤`), and so is its code at every grade
`≥ K` (`ProfileTower.code_label_mem_ownCat`).  The profiles `⊥` below the donor coatom stay
(the owner may be lowered to `⊥`), which the sub-catalogue at a constant positive cutoff loses
(`ProfileTower.not_botLiftProvisionIn_lowConst`).

**Scope.**  The levels above `K` on the owner-LOW catalogues are levels on a family of catalogues
(`ProfileTower.Lvl.GoodOn.nextOn`), so their lifts are the lift provisions for the owner-LOW
catalogues at each grade above `K` (`ProfileTower.BotLiftProvisionIn`,
`ProfileTower.CapLiftProvisionIn`), not proved here.  They ask more than the LOW step of a state
tower (sections indexed by profiles with a free cutoff field, [AFK26]): the cutoff is tied to
the owner, so at a positive cap the donor tops must reach the owner and not only the frontier, and
at the cap `⊥` from the donor coatom the owner must fall to the donor maximum or to the least donor
top, which fails when availability holds the owner above a donor top of the common face.  The
padded section is the base of either tower: it reads the controllers through a field of the
profile, so it agrees capped with no condition on the cutoff.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- The **padded code** of a profile `c`: `c` with the cutoff `c o`, the value at the owner. -/
abbrev padCut (o : Fin I.amalgam.card) (c : Prof I) : CProf I := withCut c (c o)

/-! ### The padded section -/

section Pad

variable {g : ℕ} {L : Lvl I g} {A : CProf I → Prop} {o : Fin I.amalgam.card}

local notation "𝒞" => predCat I (g + 1) A

variable (A o) in
/-- The **padded section** of the catalogue layer: at the cells of grade at most `g + 1`, the row
labelling of the padded code of the profile, read by the upper decoder of its splice; above, the
section of the level. -/
noncomputable def Lvl.padσ (L : Lvl I g) (P : Prof I) :
    Fin (L.S.card + (predCat I (g + 1) A).card) → Label.{u} := fun z ↦
  if (L.S.appendFullCellsScheme (g + 1) (predCat I (g + 1) A).card).grade z ≤ g + 1 then
    upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
      (L.Φcat (predCat I (g + 1) A) (padCut o (code (g + 1) P)) z)
  else Fin.append (L.σ P) (fun _ ↦ ⊥) z

variable (A o) in
/-- **The padded level**: the catalogue layer of `A` with the padded section, at `g + 1`. -/
noncomputable def Lvl.padNext (L : Lvl I g) : Lvl I (g + 1) where
  S := L.catS (predCat I (g + 1) A)
  σ := L.padσ A o
  embed := L.embed.trans (Fin.castAddOrderEmb _)
  inv := (L.catNext A).inv

theorem Lvl.padσ_of_le {P : Prof I} {z : Fin (L.S.card + (𝒞).card)}
    (hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1) :
    L.padσ A o P z = upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
      (L.Φcat 𝒞 (padCut o (code (g + 1) P)) z) := by
  unfold Lvl.padσ; exact ite_eq_left hz

theorem Lvl.Good.padσ_old_of_lt (hL : L.Good) {P : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade
      (Fin.castAdd _ (L.embed d)) ≤ g + 1) :
    L.padσ A o P (Fin.castAdd _ (L.embed d)) = P d := by
  unfold Lvl.padσ
  rw [ite_eq_right hd, Fin.append_left, hL.literal]

/-- The padded code of a profile lies in the code grid. -/
theorem padCut_code_mem_codeGrid (P : Prof I) (f : Fin I.amalgam.card ⊕ Unit) :
    padCut o (code (g + 1) P) f ∈ codeGrid (g + 1) (bound I) := by
  rcases f with d | z
  · exact code_mem_codeGrid _ _ _
  · exact code_mem_codeGrid _ _ _

/-- **The padded code of a profile of a sub-catalogue with padded codes in `A` lies in the
catalogue of `A`.** -/
theorem padCut_mem_predCat {c : Prof I} (hc : c ∈ cat I (g + 1)) (hA : A (padCut o c)) :
    padCut o c ∈ 𝒞 :=
  mem_predCat.mpr ⟨fun f ↦ by
    rcases f with d | z
    exacts [mem_codeGrid_of_mem_cat hc d, mem_codeGrid_of_mem_cat hc o],
    (mem_cat.mp hc).1, (mem_cat.mp hc).2, hA⟩

/-- **The padded level is a level good relative to `D`**, over a good level, when `A` holds with
the cutoff `⊥`, the catalogue layer lifts from the two coatoms at `g + 1`, and the profiles of
`D (g + 1)` are profiles of the catalogue with padded codes in `A`. -/
theorem Lvl.Good.padNext (hL : L.Good) (hgm : g + 1 ≤ m) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
        (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩)
    {D : ℕ → Finset (Prof I)} (hD : D (g + 1) ⊆ cat I (g + 1))
    (hA : ∀ c ∈ D (g + 1), A (padCut o c)) : (L.padNext A o).GoodOn D := by
  have hN := hL.catNext hgm hA0 hlift
  refine
    { lowerEmb := hN.lowerEmb
      scope_embed := hN.scope_embed
      comap_rows := hN.comap_rows
      mem_range := hN.mem_range
      faces := hN.faces
      wf := hN.wf
      coded := hN.coded
      consistent := hN.consistent
      lawful := fun P _ hPD ↦ ?_
      mem := fun P hP z ↦ ?_
      literal := fun P d ↦ ?_
      capAgree := fun P P' hP h hh hs hag z ↦ ?_
      readable := fun Q hQ hQB z ↦ ?_
      lift := hN.lift
      complete := hN.complete }
  · -- lawful
    have hc := hD hPD
    have hQ := padCut_mem_predCat hc (hA _ hPD)
    have h := (hL.isLawfulBelow_Φcat hQ (fun f ↦ (mem_predCat.mp hQ).1 f)
      (mem_cat.mp hc).1).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_upperDecoderAt (w := hat I (g + 1) P) (B := bound I) (K := g + 2) (by omega))
      (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
    refine (Rows.isLawfulBelow_congr (R := (L.catS 𝒞).rows)
      (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
        (L.Φcat 𝒞 (padCut o (code (g + 1) P)) z)) (w' := L.padσ A o P) fun z hz ↦ ?_).mp h
    exact (L.padσ_of_le hz.2).symm
  · -- mem
    change L.padσ A o P z ∈ _
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.padσ_of_le hz]
      exact upperDecoderAt_mem_codeGrid_of_mem (by omega) (hat_mem_codeGrid hP)
        (hL.Φcat_mem_codeGrid (padCut_code_mem_codeGrid _) z)
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.padσ_old_of_lt hz]
      exact hP d
  · -- literal
    change L.padσ A o P (Fin.castAdd _ (L.embed d)) = P d
    by_cases hd : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade
        (Fin.castAdd _ (L.embed d)) ≤ g + 1
    · rw [L.padσ_of_le hd, Lvl.Φcat_castAdd, hL.literal]
      change upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
        (code (g + 1) P d) = P d
      rw [upperDecoderAt_orbitCode, hat_of_le]
      rw [Scheme.appendFullCellsScheme_grade_castAdd, hL.lowerEmb.grade_eq] at hd
      exact hd
    · exact hL.padσ_old_of_lt hd
  · -- capAgree
    change min (L.padσ A o P z) h = min (L.padσ A o P' z) h
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.padσ_of_le hz, L.padσ_of_le hz]
      refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
        (fun d ↦ le_gridPoint_of_mem_codeGrid (hat_mem_codeGrid hP d)) (min_hat_eq hag)
        (fun c ↦ L.Φcat 𝒞 (padCut o c)) (fun c c' hc hc' Γ hΓv hΓs hcc z ↦ ?_) z
      have hcB (d : Fin I.amalgam.card) : c d ∈ codeGrid (g + 1) (bound I) :=
        codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc d)
      have hcB' (d : Fin I.amalgam.card) : c' d ∈ codeGrid (g + 1) (bound I) :=
        codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc' d)
      induction z using Fin.addCases with
      | left e =>
        rw [Lvl.Φcat_castAdd, Lvl.Φcat_castAdd]
        exact hL.capAgree c c' hcB Γ hΓv hΓs hcc e
      | right i =>
        rw [Lvl.Φcat_natAdd, Lvl.Φcat_natAdd]
        refine min_agreementHeight_eq_of_isShort hΓv hΓs (fun f ↦ ?_) (fun f ↦ ?_) _
        · rcases f with d | z
          exacts [⟨hcB d, hcB' d⟩, ⟨hcB o, hcB' o⟩]
        · rcases f with d | z
          exacts [hcc d, hcc o]
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.padσ_old_of_lt hz, hL.padσ_old_of_lt hz]
      exact hag d
  · -- readable
    change IsReadableAt (g + 1 + 1) Q (L.padσ A o Q z)
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.padσ_of_le hz]
      refine isReadableAt_upperDecoderAt_of_mem hQ (by omega) (hat_mem_codeGrid hQB)
        (fun d ↦ ?_) (hL.Φcat_mem_codeGrid (padCut_code_mem_codeGrid _) z)
      by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
      · rw [hat_of_le hd]; exact isReadableAt_apply Q d
      · rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.padσ_old_of_lt hz]
      exact isReadableAt_apply Q d

end Pad

/-! ### The owner-LOW catalogues -/

section Own

variable (K : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit)) (T : Set (Fin I.amalgam.card ⊕ Unit))
  (o r : Fin I.amalgam.card)

/-- A profile is **owner-LOW** when its padded code satisfies the LOW clause. -/
def ownLow (w : Prof I) : Prop := lowPred K N T o r (padCut o w)

/-- The **owner-LOW catalogue** at the grade `k`. -/
noncomputable abbrev ownCat (k : ℕ) : Finset (Prof I) := rowCat (ownLow K N T o r) k

variable {K N T o r}

/-- **Owner-LOW**: if the donor maximum is below the owner, every donor top is at least the
owner; the frontier is at most the owner. -/
theorem ownLow_iff {w : Prof I} : ownLow K N T o r w ↔
    (donorMax N (padCut o w) < w o → ∀ x ∈ T, w o ≤ padCut o w x) := by
  refine ⟨fun h hlt x hx ↦ (le_max_left _ _).trans (h hlt x hx), fun h hlt x hx ↦ ?_⟩
  exact max_le (h hlt x hx) ((min_le_left _ _).trans (h hlt x hx))

/-- **Owner-LOW profiles are kept by a monotone map fixing `⊥`** applied at the designated
fields. -/
theorem ownLow_of_map {w v : Prof I} {φ : Label.{u} → Label.{u}} (hφ : Monotone φ)
    (hφ0 : φ ⊥ = ⊥) (hN : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ v d = φ (w d))
    (hT : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ v d = φ (w d)) (ho : v o = φ (w o))
    (h : ownLow K N T o r w) : ownLow K N T o r v := by
  classical
  rw [ownLow_iff] at h ⊢
  intro hlt x hx
  have hdm : φ (donorMax N (padCut o w)) ≤ donorMax N (padCut o v) := by
    rcases N.eq_empty_or_nonempty with he | hne
    · rw [donorMax, donorMax, he, sup_empty, sup_empty, hφ0]
    obtain ⟨f, hf, hfeq⟩ := exists_mem_eq_sup _ hne (padCut o w)
    obtain ⟨d, rfl, hd⟩ := hN f hf
    rw [donorMax, hfeq]
    exact (show φ (w d) = padCut o v (Sum.inl d) from hd.symm) ▸ le_sup hf
  have hlt' : donorMax N (padCut o w) < w o := by
    by_contra hge
    rw [not_lt] at hge
    exact absurd ((ho ▸ hφ hge).trans hdm) (not_le.mpr hlt)
  obtain ⟨d, rfl, hd⟩ := hT x hx
  change v o ≤ v d
  rw [ho, hd]
  exact hφ (h hlt' _ hx)

/-- Owner-LOW profiles agreeing at the designated fields. -/
theorem ownLow_congr {w v : Prof I} (hN : ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ v d = w d)
    (hT : ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ v d = w d) (ho : v o = w o)
    (h : ownLow K N T o r w) : ownLow K N T o r v :=
  ownLow_of_map (φ := id) monotone_id rfl hN hT ho h

/-- The designated fields have grade at most `K`. -/
def FieldsLE (K : ℕ) (N : Finset (Fin I.amalgam.card ⊕ Unit))
    (T : Set (Fin I.amalgam.card ⊕ Unit)) (o : Fin I.amalgam.card) : Prop :=
  (∀ f ∈ N, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K) ∧
    (∀ f ∈ T, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ K) ∧
    I.amalgam.toCellScheme.grade o ≤ K

/-- **A profile with an owner-LOW splice at a grade `j ≥ K` is owner-LOW**, and conversely. -/
theorem ownLow_hat_iff (hF : FieldsLE K N T o) {j : ℕ} (hj : K ≤ j) {w : Prof I} :
    ownLow K N T o r (hat I j w) ↔ ownLow K N T o r w := by
  have hN (v w : Prof I) (hvw : ∀ d, I.amalgam.toCellScheme.grade d ≤ K → v d = w d) :
      ∀ f ∈ N, ∃ d, f = Sum.inl d ∧ v d = w d := fun f hf ↦ by
    obtain ⟨d, rfl, hd⟩ := hF.1 f hf
    exact ⟨d, rfl, hvw d hd⟩
  have hT (v w : Prof I) (hvw : ∀ d, I.amalgam.toCellScheme.grade d ≤ K → v d = w d) :
      ∀ f ∈ T, ∃ d, f = Sum.inl d ∧ v d = w d := fun f hf ↦ by
    obtain ⟨d, rfl, hd⟩ := hF.2.1 f hf
    exact ⟨d, rfl, hvw d hd⟩
  have hhat : ∀ d, I.amalgam.toCellScheme.grade d ≤ K → hat I j w d = w d :=
    fun d hd ↦ hat_of_le (hd.trans hj)
  exact ⟨ownLow_congr (hN _ _ fun d hd ↦ (hhat d hd).symm) (hT _ _ fun d hd ↦ (hhat d hd).symm)
    (hhat o hF.2.2).symm, ownLow_congr (hN _ _ hhat) (hT _ _ hhat) (hhat o hF.2.2)⟩

/-- **The code of an owner-LOW profile at a grade `j ≥ K` is owner-LOW.** -/
theorem ownLow_code (hF : FieldsLE K N T o) {j : ℕ} (hj : K ≤ j) {w : Prof I}
    (h : ownLow K N T o r w) : ownLow K N T o r (code j w) := by
  have hw := (ownLow_hat_iff hF hj).mpr h
  have hφ (d : Fin I.amalgam.card) :
      code j w d = orbitMap j (hat I j w) (hat I j w d) := orbitCode_apply d
  refine ownLow_of_map (monotone_orbitMap j (hat I j w)) orbitMap_bot
    (fun f hf ↦ ?_) (fun f hf ↦ ?_) (hφ o) hw
  · obtain ⟨d, rfl, -⟩ := hF.1 f hf
    exact ⟨d, rfl, hφ d⟩
  · obtain ⟨d, rfl, -⟩ := hF.2.1 f hf
    exact ⟨d, rfl, hφ d⟩

/-- **The downward clause for the owner-LOW catalogues** from the grade `K`: the code at `j ≥ K`
of a profile of the owner-LOW catalogue at `j + 1` lies in the owner-LOW catalogue at `j`. -/
theorem code_mem_ownCat (hF : FieldsLE K N T o) {j : ℕ} (hj : K ≤ j) {R : Prof I}
    (hR : R ∈ ownCat K N T o r (j + 1)) : code j R ∈ ownCat K N T o r j := by
  obtain ⟨hRc, hRo⟩ := mem_rowCat.mp hR
  have h1 : ownLow K N T o r R := (ownLow_hat_iff hF (hj.trans (Nat.le_succ j))).mp hRo
  exact mem_rowCat.mpr ⟨code_mem_cat_of_mem_cat hRc,
    (ownLow_hat_iff hF hj).mpr (ownLow_code hF hj h1)⟩

/-- **A profile of the owner-LOW catalogue at a grade `j ≥ K` is owner-LOW.** -/
theorem ownLow_of_mem_ownCat (hF : FieldsLE K N T o) {j : ℕ} (hj : K ≤ j) {R : Prof I}
    (hR : R ∈ ownCat K N T o r j) : ownLow K N T o r R :=
  (ownLow_hat_iff hF hj).mp (mem_rowCat.mp hR).2

/-- **The code at a grade `j ≥ K` of an owner-LOW profile lawful on the cut lies in the owner-LOW
catalogue.** -/
theorem code_mem_ownCat_of (hF : FieldsLE K N T o) {j : ℕ} (hj : K ≤ j) {w : Prof I}
    (hw : IsCutLawful I j w) (h : ownLow K N T o r w) : code j w ∈ ownCat K N T o r j :=
  mem_rowCat.mpr ⟨code_mem_cat_of_isCutLawful hw, (ownLow_hat_iff hF hj).mpr (ownLow_code hF hj h)⟩

end Own

/-! ### The LOW designations of a seed -/

section Seed

variable {o r : Fin I.left.card}

/-- **The LOW designations of a seed have grade at most `K`**, when the private context is a
source-gap context of grade `K` and the donor has top grade at most `K`. -/
theorem fieldsLE_low {K : ℕ}
    (hs : I.left.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last m) o r)
    (htb : I.right.topGrade ≤ K) :
    FieldsLE K (lowN I K) (lowT I) (StageType.faceCell I.restrictFace_left o) := by
  classical
  refine ⟨fun f hf ↦ ?_, fun f hf ↦ ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, by rw [StageType.grade_faceCell]; exact (mem_filter.mp ht).2.2⟩
  · obtain ⟨t, ht, rfl⟩ := hf
    exact ⟨_, rfl, by
      rw [StageType.grade_faceCell]; exact StageType.topGrade_le_iff.mp htb t ht⟩
  · rw [StageType.grade_faceCell, hs.grade_owner]

/-- **The glued labelling is owner-LOW**: its donor tops are `⊤`. -/
theorem ownLow_label {K : ℕ} {N : Finset (Fin I.amalgam.card ⊕ Unit)}
    {r' : Fin I.amalgam.card} :
    ownLow K N (lowT I) (StageType.faceCell I.restrictFace_left o) r'
      (fun d ↦ I.amalgam.label d) := by
  rw [ownLow_iff]
  intro _ x hx
  obtain ⟨t, ht, rfl⟩ := hx
  change _ ≤ I.amalgam.label (StageType.faceCell I.restrictFace_right t)
  rw [show I.amalgam.label (StageType.faceCell I.restrictFace_right t) = ⊤ from
    (StageType.label_faceCell _ t).trans ht]
  exact le_top

end Seed

end VaughtConjecture.ProfileTower

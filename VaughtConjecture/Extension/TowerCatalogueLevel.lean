/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TowerCatalogueLayer

/-!
# The catalogue layer as a level good on a set of profiles

Roadmap, Layer 3 (the controllers of the growth and LOW constructions, and the levels above them).

The catalogue layer of a predicate `A` over a level at the grade `g` is a level at the grade
`g + 1` (`ProfileTower.Lvl.catNext`) whose section operator (`ProfileTower.Lvl.catσ`) reads, at the
cells of grade at most `g + 1`, the row of the code of the profile with the cutoff `⊥` through the
upper decoder of its splice, and the section of the level above.

**Goodness on a set of profiles** (`ProfileTower.Lvl.GoodAt.catNext`).  Over a level good on `S`,
whose catalogue at `g + 1` lies in `S`, the catalogue layer is good on every set `S'` of profiles
whose codes with the cutoff `⊥` satisfy `A`, provided `A` holds at the bottom profile and the layer
lifts from the two coatoms at the grade `g + 1`.  The section of a profile of `S'` is lawful because
the row of its code is (`ProfileTower.Lvl.GoodAt.isLawfulBelow_Φcat`); every other field of
`ProfileTower.Lvl.Good` is a property of the formula of the section, for every profile.  For `A`
true at every cutoff `⊥` and `S = S'` everything, this is the good catalogue level of the LOW
construction; for the admission of the growth requests on the exact class, `S'` is the admitted
profiles, and goodness on every profile fails above the layer
(`ProfileTower.Lvl.Good.not_forall_admitted`).

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {L : Lvl I g}
  {A : CProf I → Prop} {S S' : Prof I → Prop}

local notation "𝒞" => predCat I (g + 1) A

variable (A) in
/-- The **section operator of the catalogue layer**: at the cells of grade at most `g + 1`, the row
labelling of the code of the profile with the cutoff `⊥`, read by the upper decoder of its splice;
above, the section of the level. -/
noncomputable def Lvl.catσ (L : Lvl I g) (P : Prof I) :
    Fin (L.S.card + (predCat I (g + 1) A).card) → Label.{u} := fun z ↦
  if (L.S.appendFullCellsScheme (g + 1) (predCat I (g + 1) A).card).grade z ≤ g + 1 then
    upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
      (L.Φcat (predCat I (g + 1) A) (withCut (code (g + 1) P) ⊥) z)
  else Fin.append (L.σ P) (fun _ ↦ ⊥) z

variable (A) in
/-- **The catalogue layer as a level** at the grade `g + 1`. -/
noncomputable def Lvl.catNext (L : Lvl I g) : Lvl I (g + 1) where
  S := L.catS (predCat I (g + 1) A)
  σ := L.catσ A
  embed := L.embed.trans (Fin.castAddOrderEmb _)
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_scope_castAdd]
      exact (L.inv d).imp_left fun h ↦ h.trans (Nat.le_succ g)
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

theorem Lvl.catσ_of_le {P : Prof I} {z : Fin (L.S.card + (𝒞).card)}
    (hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1) :
    L.catσ A P z = upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
      (L.Φcat 𝒞 (withCut (code (g + 1) P) ⊥) z) := by
  unfold Lvl.catσ; exact ite_eq_left hz

/-- **The section of a catalogue level at its low cells sees the profile only up to its grade**:
two profiles agreeing at the cells of grade at most `g + 1` have the same section at every cell of
grade at most `g + 1` (the code and the upper decoder read the splice `hat I (g + 1) P` only).  So a
table installed at cells of low grade is read by the controllers of the layer above only through the
values of the profile at the cells of grade at most the grade of the level. -/
theorem Lvl.catσ_eq_of_hat_eq {P P' : Prof I} (hPP : hat I (g + 1) P = hat I (g + 1) P')
    {z : Fin (L.S.card + (𝒞).card)}
    (hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1) :
    L.catσ A P z = L.catσ A P' z := by
  rw [L.catσ_of_le hz, L.catσ_of_le hz, hPP, code, code, hPP]

theorem Lvl.GoodAt.exists_old_of_lt_cat (hL : L.GoodAt S) {z : Fin (L.S.card + (𝒞).card)}
    (hz : ¬ (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1) :
    ∃ d, z = Fin.castAdd _ (L.embed d) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le hz
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd] at hz
    obtain ⟨d, rfl⟩ := hL.mem_range_of_lt (by omega : g < L.S.toCellScheme.grade e)
    exact ⟨d, rfl⟩

theorem Lvl.GoodAt.catσ_old_of_lt (hL : L.GoodAt S) {P : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade
      (Fin.castAdd _ (L.embed d)) ≤ g + 1) :
    L.catσ A P (Fin.castAdd _ (L.embed d)) = P d := by
  unfold Lvl.catσ
  rw [ite_eq_right hd, Fin.append_left, hL.literal]

theorem withCut_code_mem_codeGrid (P : Prof I) (f : Fin I.amalgam.card ⊕ Unit) :
    withCut (code (g + 1) P) ⊥ f ∈ codeGrid (g + 1) (bound I) := by
  rcases f with d | z
  · exact code_mem_codeGrid _ _ _
  · exact Finset.mem_insert_self _ _

/-- **The catalogue layer over a level good on `S` is good on `S'`**, when the catalogue lies in
`S`, the codes of the profiles of `S'` with the cutoff `⊥` satisfy `A`, the bottom profile satisfies
`A`, and the layer lifts from the two coatoms at the grade `g + 1`. -/
theorem Lvl.GoodAt.catNext (hL : L.GoodAt S) (hgm : g + 1 ≤ m) (hAS : ∀ P, A P → S (camal P))
    (hcode : ∀ P, S' P → IsCutLawful I (g + 1) P → A (withCut (code (g + 1) P) ⊥))
    (hA0 : A fun _ ↦ ⊥)
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
        (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩) :
    (L.catNext A).GoodAt S' := by
  have hCsub : ∀ P ∈ 𝒞, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) := fun P hP ↦ ⟨(mem_predCat.mp hP).1, (mem_predCat.mp hP).2.1⟩
  have hCS : ∀ P ∈ 𝒞, S (camal P) := fun P hP ↦ hAS P (mem_predCat.mp hP).2.2.2
  have hemb := Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (𝒞).card
    (fun i ↦ L.Φcat 𝒞 ((𝒞).equivFin.symm i).1) L.not_le
  refine
    { lowerEmb := hemb.comp hL.lowerEmb
      scope_embed := fun d ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (hL.scope_embed d)
      comap_rows := ?_
      mem_range := ?_
      faces := hL.faces
      wf := Scheme.isWellFormed_appendFullCells (M := (𝒞).card)
        (r := fun i ↦ L.Φcat 𝒞 ((𝒞).equivFin.symm i).1) (h := L.not_le) hL.wf (by omega)
        (by omega)
      coded := Scheme.isCoded_appendFullCells (h := L.not_le) hL.coded fun i d ↦
        lt_omega0_sq_of_mem_codeGrid (hL.Φcat_mem_codeGrid (hCsub _ ((𝒞).equivFin.symm i).2).1 d)
      consistent := hL.catS_consistent hCsub hCS
      lawful := fun P hPS hP ↦ ?_
      mem := fun P hP z ↦ ?_
      literal := fun P d ↦ ?_
      capAgree := fun P P' hP h hh hs hag z ↦ ?_
      readable := fun Q hQ hQB z ↦ ?_
      lift := fun x hx j hj ↦ ?_
      complete := fun j hj0 hj ↦ ?_ }
  · have h := Rows.comap_comap (L.catS 𝒞).rows hemb hL.lowerEmb
    rw [Scheme.comap_rows_castAdd, hL.comap_rows] at h
    exact h.symm
  · intro z hz
    induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left e =>
      have hz' : L.S.toCellScheme.scope e ≠ univ := by
        have := (Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) (𝒞).card e)
        exact fun h ↦ hz (this.trans h)
      obtain ⟨d, rfl⟩ := hL.mem_range e hz'
      exact ⟨d, rfl⟩
  · -- lawful, for the profiles of `S'`
    have hQ : withCut (code (g + 1) P) ⊥ ∈ 𝒞 :=
      mem_predCat_of (isCutLawful_hat hP) (Finset.mem_insert_self _ _) (hcode P hPS hP)
    have h := (hL.isLawfulBelow_Φcat hQ (hCsub _ hQ).1 (hCsub _ hQ).2
      (hCS _ hQ)).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_upperDecoderAt (w := hat I (g + 1) P) (B := bound I) (K := g + 2) (by omega))
      (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
    refine (Rows.isLawfulBelow_congr (R := (L.catS 𝒞).rows)
      (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
        (L.Φcat 𝒞 (withCut (code (g + 1) P) ⊥) z)) (w' := L.catσ A P) fun z hz ↦ ?_).mp h
    exact (L.catσ_of_le hz.2).symm
  · -- mem
    change L.catσ A P z ∈ _
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.catσ_of_le hz]
      exact upperDecoderAt_mem_codeGrid_of_mem (by omega) (hat_mem_codeGrid hP)
        (hL.Φcat_mem_codeGrid (withCut_code_mem_codeGrid _) z)
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.catσ_old_of_lt hz]
      exact hP d
  · -- literal
    change L.catσ A P (Fin.castAdd _ (L.embed d)) = P d
    by_cases hd : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade
        (Fin.castAdd _ (L.embed d)) ≤ g + 1
    · rw [L.catσ_of_le hd, Lvl.Φcat_castAdd, hL.literal]
      change upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
        (code (g + 1) P d) = P d
      rw [upperDecoderAt_orbitCode, hat_of_le]
      rw [Scheme.appendFullCellsScheme_grade_castAdd, hL.lowerEmb.grade_eq] at hd
      exact hd
    · exact hL.catσ_old_of_lt hd
  · -- capAgree
    change min (L.catσ A P z) h = min (L.catσ A P' z) h
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.catσ_of_le hz, L.catσ_of_le hz]
      refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
        (fun d ↦ le_gridPoint_of_mem_codeGrid (hat_mem_codeGrid hP d)) (min_hat_eq hag)
        (fun c ↦ L.Φcat 𝒞 (withCut c ⊥)) (fun c c' hc hc' Γ hΓv hΓs hcc z ↦ ?_) z
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
          · exact ⟨hcB d, hcB' d⟩
          · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
        · rcases f with d | z
          · exact hcc d
          · rfl
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.catσ_old_of_lt hz, hL.catσ_old_of_lt hz]
      exact hag d
  · -- readable
    change IsReadableAt (g + 1 + 1) Q (L.catσ A Q z)
    by_cases hz : (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1
    · rw [L.catσ_of_le hz]
      refine isReadableAt_upperDecoderAt_of_mem hQ (by omega) (hat_mem_codeGrid hQB)
        (fun d ↦ ?_) (hL.Φcat_mem_codeGrid (withCut_code_mem_codeGrid _) z)
      by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
      · rw [hat_of_le hd]; exact isReadableAt_apply Q d
      · rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
    · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_cat hz
      rw [hL.catσ_old_of_lt hz]
      exact isReadableAt_apply Q d
  · -- lift
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact (L.cappedLift_catS_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
        (hL.lift x hx j (by omega))
    · exact hlift x hx
  · -- complete
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e, he⟩ := hL.complete j hj0 (by omega)
      exact ⟨Fin.castAdd _ e, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).trans he⟩
    · obtain ⟨i₀, -⟩ := exists_equivFin_eq (C := 𝒞) (bot_mem_predCat hA0)
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

/-- **The catalogue level extends at `⊥` on `S'`**: a labelling lawful below both coatoms at the
grade `g + 1` whose amalgam profile `W` lies in `S'` is extended below the full face through the
row of the orbit code of `W` with the cutoff `⊥`
(`ProfileTower.Lvl.GoodAt.exists_extension_cat_bot`), which lies in the catalogue. -/
theorem Lvl.GoodAt.hasBotExtensionOn_catNext (hL : L.GoodAt S) (hAS : ∀ P, A P → S (camal P))
    (hcode : ∀ W, S' W → IsCutLawful I (g + 1) W → A (withCut (orbitCode (g + 1) W) ⊥)) :
    (L.catNext A).HasBotExtensionOn S' := by
  intro w hwC hwD hwS
  have hCsub : ∀ P ∈ 𝒞, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) := fun P hP ↦ ⟨(mem_predCat.mp hP).1, (mem_predCat.mp hP).2.1⟩
  have hCS : ∀ P ∈ 𝒞, S (camal P) := fun P hP ↦ hAS P (mem_predCat.mp hP).2.2.2
  let v : Fin (L.S.card + (𝒞).card) → Label.{u} := w
  set W : Prof I := fun d ↦ v (Fin.castAdd _ (L.embed d)) with hW
  have hcut (z : Fin (m + 2)) (hz : univ.erase z ≠ univ)
      (hwz : (L.catS 𝒞).rows.IsLawfulBelow (univ.erase z, g + 1) fun d ↦ v d) :
      I.amalgam.rows.IsLawfulBelow (univ.erase z, g + 1) fun d ↦ W d := by
    have h1 := (L.isLawfulBelow_catS_iff (C := 𝒞) (X := (univ.erase z, g + 1))
      (fun h ↦ hz (univ_subset_iff.mp h.1))).mp hwz
    exact (hL.isLawfulBelow_old_iff (w := fun e ↦ v (Fin.castAdd _ e)) hz).mp h1
  have hWc : IsCutLawful I (g + 1) W :=
    ⟨hcut _ (Seed.ne_univ_erase _) hwC, hcut _ (Seed.ne_univ_erase _) hwD⟩
  have hQC : withCut (orbitCode (g + 1) W) ⊥ ∈ 𝒞 :=
    mem_predCat_of hWc (Finset.mem_insert_self _ _) (hcode W hwS hWc)
  obtain ⟨q, hq, hqW⟩ := hL.exists_extension_cat_bot hCsub hCS hQC
  refine ⟨q, hq, fun z hz ↦ ?_⟩
  obtain ⟨z, hzb⟩ := z
  change (L.catS 𝒞).toCellScheme.scope z ≠ univ at hz
  change z ∈ (L.catS 𝒞).toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1) at hzb
  change q ⟨z, hzb⟩ = v z
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left e =>
    have he : L.S.toCellScheme.scope e ≠ univ := by
      rwa [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := hL.mem_range e he
    have hd : I.amalgam.toCellScheme.grade d ≤ g + 1 := by
      have := hzb.2
      rwa [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hL.gradedIndex_embed] at this
    exact hqW d hd

variable (A) in
/-- **The catalogue levels above a level**: `j` catalogue layers of `A`. -/
noncomputable def Lvl.catIter {g' : ℕ} (N : Lvl I g') : (j : ℕ) → Lvl I (g' + j)
  | 0 => N
  | j + 1 => (N.catIter j).catNext A

/-- **The catalogue levels above a level good on `S` are good on `S`**, up to the grade `m`, when
the catalogues lie in `S`, the codes of the profiles of `S` with the cutoff `⊥` satisfy `A` at every
grade above, `A` holds at the bottom profile, and every layer lifts from the two coatoms. -/
theorem Lvl.GoodAt.catIter {g' : ℕ} {N : Lvl I g'} (hN : N.GoodAt S)
    (hAS : ∀ P, A P → S (camal P))
    (hcode : ∀ k, g' < k → ∀ P, S P → IsCutLawful I k P → A (withCut (code k P) ⊥))
    (hA0 : A fun _ ↦ ⊥)
    (hlift : ∀ j, g' + j + 1 ≤ m → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      ((N.catIter A j).catS (predCat I (g' + j + 1) A)).rows.CappedLift
        (X := (univ.erase x, g' + j + 1)) (Y := ((univ : Finset (Fin (m + 2))), g' + j + 1))
        ⟨erase_subset _ _, le_rfl⟩) :
    ∀ j, g' + j ≤ m → (N.catIter A j).GoodAt S
  | 0, _ => hN
  | j + 1, h => (hN.catIter hAS hcode hA0 hlift j (by omega)).catNext (by omega) hAS
      (fun P hP hPc ↦ hcode _ (by omega) P hP hPc) hA0 (hlift j (by omega))

end VaughtConjecture.ProfileTower

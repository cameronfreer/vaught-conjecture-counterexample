/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowTower

/-!
# The catalogue layer as a level of the profile tower

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display above the
controllers); semantic contract, items 3, 4 and 8.

Above the grade `K` of the controllers the display is to be completed by the canonical layers of the
profile tower (`ProfileTower.Lvl.next`, `ProfileTower.Lvl.Good.next`) and the completion below the
full grade (`VaughtConjecture.Extension.ProfileTowerCompletion`).  Both start from a good level
(`ProfileTower.Lvl.Good`).  This file makes the catalogue layer of a predicate `A` over a good level
at the grade `g` a level at the grade `g + 1` (`ProfileTower.Lvl.catNext`) and proves it good
(`ProfileTower.Lvl.Good.catNext`, compiled in this repository) when `A` holds at every profile
with the cutoff `⊥` and the layer lifts capped from the two coatoms at the grade `g + 1`.

**The section operator** (`ProfileTower.Lvl.catσ`).  As for the canonical next level, at the cells
of grade at most `g + 1` the section of a profile `P` is the row labelling of its code, read by the
upper decoder of its splice at the grade `g + 1` for caps at `g + 2`; the code is the orbit code of
the splice with the cutoff `⊥`, which lies in the catalogue of `A` (`A` holds with the cutoff `⊥`;
for the LOW clause, a profile with the cutoff `⊥` is not active).  Above, it is the section of the
level.  Every field of `ProfileTower.Lvl.Good` is proved as for the canonical next level: the
agreement heights of two codes with the cutoff `⊥` agree capped where the codes do, the rows of the
catalogue profiles lie in the code grid, and the old cells are read literally.  The lift from
the two coatoms at the grade `g + 1` is a hypothesis; for the LOW predicate it is
`ProfileTower.Lvl.Good.cappedLift_lowS_seed` (`ProfileTower.Lvl.Good.lowNext`, in
`VaughtConjecture.Continuation.LowDisplayLayer`).  This file imports only the generic tower of
profiles (`VaughtConjecture.Continuation.LowTower`), not the LOW steps.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {L : Lvl I g}
  {A : CProf I → Prop}

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

theorem Lvl.Good.exists_old_of_lt_cat (hL : L.Good) {z : Fin (L.S.card + (𝒞).card)}
    (hz : ¬ (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade z ≤ g + 1) :
    ∃ d, z = Fin.castAdd _ (L.embed d) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le hz
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd] at hz
    obtain ⟨d, rfl⟩ := hL.mem_range_of_lt (by omega : g < L.S.toCellScheme.grade e)
    exact ⟨d, rfl⟩

theorem Lvl.Good.catσ_old_of_lt (hL : L.Good) {P : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (L.S.appendFullCellsScheme (g + 1) (𝒞).card).grade
      (Fin.castAdd _ (L.embed d)) ≤ g + 1) :
    L.catσ A P (Fin.castAdd _ (L.embed d)) = P d := by
  unfold Lvl.catσ
  rw [ite_eq_right hd, Fin.append_left, hL.literal]

/-- The code of a profile lawful on the cut, with the cutoff `⊥`, lies in the catalogue. -/
theorem withCut_code_mem_predCat (hA0 : ∀ W : Prof I, A (withCut W ⊥)) {P : Prof I}
    (hP : IsCutLawful I (g + 1) P) : withCut (code (g + 1) P) ⊥ ∈ 𝒞 :=
  mem_predCat_of (isCutLawful_hat hP) (Finset.mem_insert_self _ _) (hA0 _)

theorem withCut_code_mem_codeGrid (P : Prof I) (f : Fin I.amalgam.card ⊕ Unit) :
    withCut (code (g + 1) P) ⊥ f ∈ codeGrid (g + 1) (bound I) := by
  rcases f with d | z
  · exact code_mem_codeGrid _ _ _
  · exact Finset.mem_insert_self _ _

/-- **The good level below the catalogue layer, and the catalogue layer lifting from the two
coatoms at the grade `g + 1`, give a good level.** -/
theorem Lvl.Good.catNext (hL : L.Good) (hgm : g + 1 ≤ m) (hA0 : ∀ W : Prof I, A (withCut W ⊥))
    (hlift : ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      (L.catS 𝒞).rows.CappedLift (X := (univ.erase x, g + 1))
        (Y := ((univ : Finset (Fin (m + 2))), g + 1)) ⟨erase_subset _ _, le_rfl⟩) :
    (L.catNext A).Good := by
  have hCsub : ∀ P ∈ 𝒞, (∀ f, P f ∈ codeGrid (g + 1) (bound I)) ∧
      IsCutLawful I (g + 1) (camal P) := fun P hP ↦ ⟨(mem_predCat.mp hP).1, (mem_predCat.mp hP).2.1⟩
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
      consistent := hL.catS_consistent hCsub
      lawful := fun P hP ↦ ?_
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
  · -- lawful
    have hQ := withCut_code_mem_predCat hA0 hP
    have h := (hL.isLawfulBelow_Φcat hQ (hCsub _ hQ).1 (hCsub _ hQ).2).map_of_apply_eq_bot
      (fun z ↦ z.2.2)
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
    · obtain ⟨i₀, -⟩ := exists_equivFin_eq (C := 𝒞) (bot_mem_predCat (hA0 (fun _ ↦ ⊥) |> fun h ↦
        by convert h using 1; funext f; rcases f with d | z <;> rfl))
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

/-! ### The canonical levels above -/

/-- The **canonical levels above a level**: `j` canonical next levels (`ProfileTower.Lvl.next`). -/
noncomputable def Lvl.iter {g' : ℕ} (N : Lvl I g') : (j : ℕ) → Lvl I (g' + j)
  | 0 => N
  | j + 1 => (N.iter j).next

/-- **The canonical levels above a good level are good**, up to the grade `m`
(`ProfileTower.Lvl.Good.next`); with the LOW level (`ProfileTower.Lvl.Good.lowNext`) as base they
complete the display above the controllers, and the last one, a next level, extends at `⊥`
(`ProfileTower.Lvl.Good.hasBotExtension_next`), as `ProfileTower.Lvl.Good.completion` asks. -/
theorem Lvl.Good.iter {g' : ℕ} {N : Lvl I g'} (hN : N.Good) :
    ∀ j, g' + j ≤ m → (N.iter j).Good
  | 0, _ => hN
  | j + 1, h => (hN.iter j (by omega)).next (by omega)

end VaughtConjecture.ProfileTower

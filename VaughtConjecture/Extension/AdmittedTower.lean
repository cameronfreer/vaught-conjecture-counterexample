/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedCompletion

/-!
# The tower of layers on a family of catalogues

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with restricted catalogues at the
reading grades: layers on sub-catalogues below the top grade, carrying further layers.

Let `D : ℕ → Finset (Prof I)` be a family of catalogues, `D k ⊆ cat I k`.  **The next level on
`C`** (`ProfileTower.Lvl.nextOn L C`) of a level `L` at the grade `g` is the layer on `C`
(`ProfileTower.Lvl.nextSOn`) with the section operator of the canonical next level read on `C`
(`ProfileTower.Lvl.nextσOn`: at the cells of grade at most `g + 1`, the row labelling on `C` of the
code of the profile at `g + 1`, read by the upper decoder of its splice).

**The next level is good relative to `D`** (`ProfileTower.Lvl.GoodOn.nextOn`), for a level good
relative to `D` at the grade `g`, `g + 1 ≤ m + 1`, the layer on `C = D (g + 1)`, under
* the **downward clause** at `g`: the code at `g` of every profile of `D (g + 1)` lies in `D g`;
* the **lift provisions** for `D (g + 1)` at the grade `g + 1` from either coatom
  (`ProfileTower.BotLiftProvisionIn`, `ProfileTower.CapLiftProvisionIn`).
The section of a profile whose code lies in `D (g + 1)` is lawful: the row labelling of its code
is lawful by the downward clause (`ProfileTower.Lvl.GoodOn.isLawfulBelow_ΦOn`), and the upper
decoder is a witness sending only `⊥` to `⊥`.  The other invariants (codes in the grid, literal,
capped agreement, readable) are read off the row labellings as for the canonical next level; the
lift at `g + 1` is `ProfileTower.Lvl.GoodOn.cappedLift_nextSOn`; and the cell at `(univ, g + 1)`
comes from the provision at `⊥` (the code of a profile lifted from `⊥` lies in `D (g + 1)`).

**The family of a predicate** (`ProfileTower.rowFamily I N Rw`: the whole catalogue below `N`,
the catalogue of `Rw` from `N`) has the downward clause at the grades `k ≤ m` from that of `Rw` at
`N ≤ k ≤ m` (`ProfileTower.rowFamily_down`), and the lift provisions at every grade
`0 < k ≤ m + 1` from those of `Rw` at `N ≤ k ≤ m + 1` (`ProfileTower.rowFamily_lift`).  The levels
on the family and the completion are in `VaughtConjecture.Extension.RowCompletionZero`
(`Seed.exists_rowCompletion₀`).

## Placement

The engine of the restricted catalogue at the reading grades (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)"); the admitted completion at every reading grade `N ≥ 3`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The next level on a catalogue -/

section NextOn

variable {g : ℕ} (L : Lvl I g) (C : Finset (Prof I))

/-- The section operator of the next level on `C`: at the cells of grade at most `g + 1`, the row
labelling on `C` of the code of the profile, read by the upper decoder of its splice; above, the
section of the level. -/
noncomputable def Lvl.nextσOn (P : Prof I) : Fin (L.S.card + C.card) → Label.{u} := fun z ↦
  if (L.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1 then
    upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P) (L.ΦOn C (code (g + 1) P) z)
  else Fin.append (L.σ P) (fun _ ↦ ⊥) z

/-- **The next level on `C`**, at the grade `g + 1`. -/
noncomputable def Lvl.nextOn : Lvl I (g + 1) where
  S := L.nextSOn C
  σ := L.nextσOn C
  embed := L.embedOn C
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_scope_castAdd]
      exact (L.inv d).imp_left fun h ↦ h.trans (Nat.le_succ g)
    | right i => exact .inl (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

/-- On the whole catalogue the next level on `C` is the next level. -/
theorem Lvl.nextOn_cat : L.nextOn (cat I (g + 1)) = L.next := rfl

variable {L C} {D : ℕ → Finset (Prof I)}

theorem Lvl.nextσOn_of_le {P : Prof I} {z : Fin (L.S.card + C.card)}
    (hz : (L.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1) :
    L.nextσOn C P z =
      upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P) (L.ΦOn C (code (g + 1) P) z) := by
  unfold Lvl.nextσOn; exact ite_eq_left hz

theorem Lvl.GoodOn.ΦOn_old (hL : L.GoodOn D) (R : Prof I) (d : Fin I.amalgam.card) :
    L.ΦOn C R (Fin.castAdd _ (L.embed d)) = R d := by
  rw [Lvl.ΦOn_castAdd, hL.literal]

/-- A cell of the layer on `C` of grade above `g + 1` is an old cell of the level. -/
theorem Lvl.GoodOn.exists_old_of_lt_On (hL : L.GoodOn D) {z : Fin (L.S.card + C.card)}
    (hz : ¬ (L.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1) :
    ∃ d, z = Fin.castAdd _ (L.embed d) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le hz
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd] at hz
    obtain ⟨d, rfl⟩ := hL.mem_range_of_lt (by omega : g < L.S.toCellScheme.grade e)
    exact ⟨d, rfl⟩

theorem Lvl.GoodOn.nextσOn_old_of_lt (hL : L.GoodOn D) {P : Prof I} {d : Fin I.amalgam.card}
    (hd : ¬ (L.S.appendFullCellsScheme (g + 1) C.card).grade (Fin.castAdd _ (L.embed d)) ≤ g + 1) :
    L.nextσOn C P (Fin.castAdd _ (L.embed d)) = P d := by
  unfold Lvl.nextσOn
  rw [ite_eq_right hd, Fin.append_left, hL.literal]

/-- **The next section on `C` is literal.** -/
theorem Lvl.GoodOn.nextOn_literal (hL : L.GoodOn D) (P : Prof I) (d : Fin I.amalgam.card) :
    (L.nextOn C).σ P ((L.nextOn C).embed d) = P d := by
  change L.nextσOn C P (Fin.castAdd _ (L.embed d)) = P d
  by_cases hd : (L.S.appendFullCellsScheme (g + 1) C.card).grade
      (Fin.castAdd _ (L.embed d)) ≤ g + 1
  · rw [Lvl.nextσOn_of_le hd, hL.ΦOn_old, upperDecoderAt_orbitCode, hat_of_le]
    rw [Scheme.appendFullCellsScheme_grade_castAdd, hL.lowerEmb.grade_eq] at hd
    exact hd
  · exact hL.nextσOn_old_of_lt hd

/-- **The next section on `C` is lawful** at the profiles whose code at `g + 1` lies in `C`, under
the downward clause. -/
theorem Lvl.GoodOn.nextOn_lawful (hL : L.GoodOn D) (hC : C ⊆ cat I (g + 1))
    (hdown : ∀ R ∈ C, code g R ∈ D g) (P : Prof I) (hPC : code (g + 1) P ∈ C) :
    (L.nextOn C).S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g + 1)
      fun z ↦ (L.nextOn C).σ P z := by
  have h := (hL.isLawfulBelow_ΦOn (hC hPC) (hdown _ hPC) hPC).map_of_apply_eq_bot
    (fun z ↦ z.2.2)
    (isWitness_upperDecoderAt (w := hat I (g + 1) P) (B := bound I) (K := g + 2) (by omega))
    (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot)
  refine (Rows.isLawfulBelow_congr (R := (L.nextSOn C).rows)
    (w := fun z ↦ upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) P)
      (L.ΦOn C (code (g + 1) P) z)) (w' := L.nextσOn C P) fun z hz ↦ ?_).mp h
  exact (Lvl.nextσOn_of_le hz.2).symm

/-- **The next section on `C` takes values in the code grid at `g + 2`.** -/
theorem Lvl.GoodOn.nextOn_mem (hL : L.GoodOn D) (P : Prof I)
    (hP : ∀ d, P d ∈ codeGrid (g + 1 + 1) (bound I)) (z : Fin (L.nextOn C).S.card) :
    (L.nextOn C).σ P z ∈ codeGrid (g + 1 + 1) (bound I) := by
  change L.nextσOn C P z ∈ _
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1
  · rw [Lvl.nextσOn_of_le hz]
    exact upperDecoderAt_mem_codeGrid_of_mem (by omega) (hat_mem_codeGrid hP)
      (hL.ΦOn_mem_codeGrid (code_mem_codeGrid _ _) z)
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_On hz
    rw [hL.nextσOn_old_of_lt hz]
    exact hP d

/-- **The next section on `C` agrees capped at every cap self-visible and short at `g + 2`.** -/
theorem Lvl.GoodOn.nextOn_capAgree (hL : L.GoodOn D) (P P' : Prof I)
    (hP : ∀ d, P d ∈ codeGrid (g + 1 + 1) (bound I)) (h : Label.{u})
    (hh : IsSelfVisible (g + 1 + 1) h) (hs : IsShort (g + 1 + 1) h)
    (hag : ∀ d, min (P d) h = min (P' d) h) (z : Fin (L.nextOn C).S.card) :
    min ((L.nextOn C).σ P z) h = min ((L.nextOn C).σ P' z) h := by
  change min (L.nextσOn C P z) h = min (L.nextσOn C P' z) h
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1
  · rw [Lvl.nextσOn_of_le hz, Lvl.nextσOn_of_le hz]
    refine min_upperDecoderAt_comp_eq (k := g + 1) (K := g + 2) (by omega) hh hs
      (fun d ↦ le_gridPoint_of_mem_codeGrid (hat_mem_codeGrid hP d)) (min_hat_eq hag) (L.ΦOn C)
      (fun c c' hc hc' Γ hΓv hΓs hcc z ↦ ?_) z
    have hcB (d : Fin I.amalgam.card) : c d ∈ codeGrid (g + 1) (bound I) :=
      codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc d)
    have hcB' (d : Fin I.amalgam.card) : c' d ∈ codeGrid (g + 1) (bound I) :=
      codeGrid_mono (by simp only [Fintype.card_fin, bound]; omega) (hc' d)
    induction z using Fin.addCases with
    | left e =>
      rw [Lvl.ΦOn_castAdd, Lvl.ΦOn_castAdd]
      exact hL.capAgree c c' hcB Γ hΓv hΓs hcc e
    | right i =>
      rw [Lvl.ΦOn_natAdd, Lvl.ΦOn_natAdd]
      exact min_agreementHeight_eq_of_isShort hΓv hΓs (fun d ↦ ⟨hcB d, hcB' d⟩) hcc _
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_On hz
    rw [hL.nextσOn_old_of_lt hz, hL.nextσOn_old_of_lt hz]
    exact hag d

/-- **The next section on `C` is readable at `g + 2`** for the orbit-canonical profiles. -/
theorem Lvl.GoodOn.nextOn_readable (hL : L.GoodOn D) (Q : Prof I)
    (hQ : orbitCode (g + 1 + 1) Q = Q) (hQB : ∀ d, Q d ∈ codeGrid (g + 1 + 1) (bound I))
    (z : Fin (L.nextOn C).S.card) : IsReadableAt (g + 1 + 1) Q ((L.nextOn C).σ Q z) := by
  change IsReadableAt (g + 1 + 1) Q (L.nextσOn C Q z)
  by_cases hz : (L.S.appendFullCellsScheme (g + 1) C.card).grade z ≤ g + 1
  · rw [Lvl.nextσOn_of_le hz]
    refine isReadableAt_upperDecoderAt_of_mem hQ (by omega) (hat_mem_codeGrid hQB) (fun d ↦ ?_)
      (hL.ΦOn_mem_codeGrid (code_mem_codeGrid _ _) z)
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ g + 1
    · rw [hat_of_le hd]; exact isReadableAt_apply Q d
    · rw [hat_of_lt (_root_.not_le.mp hd)]; exact .inl rfl
  · obtain ⟨d, rfl⟩ := hL.exists_old_of_lt_On hz
    rw [hL.nextσOn_old_of_lt hz]
    exact isReadableAt_apply Q d

/-- **The next level on `C` is good relative to `D`**, for `C = D (g + 1) ⊆ cat I (g + 1)`, under
the downward clause at `g` and the lift provisions for `C` at `g + 1` from either coatom. -/
theorem Lvl.GoodOn.nextOn (hL : L.GoodOn D) (hgm : g + 1 ≤ m + 1)
    (hC : D (g + 1) ⊆ cat I (g + 1)) (hdown : ∀ R ∈ D (g + 1), code g R ∈ D g)
    (hbot : ∀ x ∈ (Pts : Finset (Fin (m + 2))), BotLiftProvisionIn (D (g + 1)) (g + 1) x)
    (hcap : ∀ x ∈ (Pts : Finset (Fin (m + 2))), CapLiftProvisionIn (D (g + 1)) (g + 1) x) :
    (L.nextOn (D (g + 1))).GoodOn D where
  lowerEmb := (Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (D (g + 1)).card
      (fun i ↦ L.ΦOn (D (g + 1)) (entryOn (D (g + 1)) i)) L.not_le).comp hL.lowerEmb
  scope_embed d := (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans (hL.scope_embed d)
  comap_rows := by
    have h := Rows.comap_comap (L.nextSOn (D (g + 1))).rows
      (Scheme.isLowerEmbedding_castAdd (S := L.S) (g + 1) (D (g + 1)).card
        (fun i ↦ L.ΦOn (D (g + 1)) (entryOn (D (g + 1)) i)) L.not_le) hL.lowerEmb
    rw [Scheme.comap_rows_castAdd, hL.comap_rows] at h
    exact h.symm
  mem_range z hz := by
    induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left e =>
      have hz' : L.S.toCellScheme.scope e ≠ univ := by
        have := Scheme.appendFullCellsScheme_scope_castAdd L.S (g + 1) (D (g + 1)).card e
        exact fun h ↦ hz (this.trans h)
      obtain ⟨d, rfl⟩ := hL.mem_range e hz'
      exact ⟨d, rfl⟩
  faces := hL.faces
  wf := hL.isWellFormed_nextSOn (by omega)
  coded := hL.isCoded_nextSOn hC
  consistent := hL.isConsistent_nextSOn hC hdown
  lawful P _ hPC := hL.nextOn_lawful hC hdown P hPC
  mem := hL.nextOn_mem
  literal := hL.nextOn_literal
  capAgree := hL.nextOn_capAgree
  readable := hL.nextOn_readable
  lift x hx j hj := by
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact (Lvl.cappedLift_nextSOn_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
        (hL.lift x hx j (by omega))
    · exact hL.cappedLift_nextSOn hC hdown hgm hx (hbot x hx) (hcap x hx)
  complete j hj0 hj := by
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e, he⟩ := hL.complete j hj0 (by omega)
      exact ⟨Fin.castAdd _ e, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e).trans he⟩
    · obtain ⟨x, hx⟩ : ∃ x, x ∈ (Pts : Finset (Fin (m + 2))) := ⟨Fin.last (m + 1), by simp⟩
      obtain ⟨W, -, -, hWC⟩ := hbot x hx (fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
      obtain ⟨i₀, -⟩ := exists_entryOn_eq hWC
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩

end NextOn

/-! ### The catalogues of an admission from its grade -/

/-- The catalogue of a predicate that holds everywhere is the whole catalogue. -/
theorem rowCat_of_forall {Rw : I.State → Prop} (h : ∀ s, Rw s) (k : ℕ) : rowCat Rw k = cat I k := by
  ext R
  rw [mem_rowCat]
  exact ⟨fun hR ↦ hR.1, fun hR ↦ ⟨hR, h _⟩⟩

/-- Catalogues of equivalent predicates are equal. -/
theorem rowCat_congr {Rw Rw' : I.State → Prop} (h : ∀ s, Rw s ↔ Rw' s) (k : ℕ) :
    rowCat Rw k = rowCat Rw' k := by
  ext R
  rw [mem_rowCat, mem_rowCat, h]

variable (I) in
/-- **The family of catalogues of a predicate from a grade `N`**: at the grade `k`, the profiles of
the catalogue whose splice at `k` satisfies `Rw` when `N ≤ k`; the whole catalogue below `N`, the
catalogue of `Rw` from `N`. -/
noncomputable def rowFamily (N : ℕ) (Rw : I.State → Prop) (k : ℕ) : Finset (Prof I) :=
  rowCat (fun s ↦ N ≤ k → Rw s) k

theorem rowFamily_of_lt {N : ℕ} (Rw : I.State → Prop) {k : ℕ} (hk : k < N) :
    rowFamily I N Rw k = cat I k :=
  rowCat_of_forall (fun _ h ↦ absurd h (by omega)) k

theorem rowFamily_of_le {N : ℕ} (Rw : I.State → Prop) {k : ℕ} (hk : N ≤ k) :
    rowFamily I N Rw k = rowCat Rw k :=
  rowCat_congr (fun _ ↦ ⟨fun h ↦ h hk, fun h _ ↦ h⟩) k

/-- **The downward clause for the family of a predicate** at the grades `k ≤ m`, from the
downward clause of its catalogues at the grades `N ≤ k ≤ m`; below `N` the codes of profiles lie in
the catalogue. -/
theorem rowFamily_down {N : ℕ} {Rw : I.State → Prop}
    (hdown : ∀ k, N ≤ k → k ≤ m → ∀ R ∈ rowCat Rw (k + 1), code k R ∈ rowCat Rw k) (k : ℕ)
    (hkm : k ≤ m) (R : Prof I) (hR : R ∈ rowFamily I N Rw (k + 1)) :
    code k R ∈ rowFamily I N Rw k := by
  rcases lt_or_ge k N with hk | hk
  · rw [rowFamily_of_lt Rw hk]
    exact code_mem_cat_of_mem_cat (rowCat_subset _ _ hR)
  · rw [rowFamily_of_le Rw hk]
    rw [rowFamily_of_le Rw (by omega)] at hR
    exact hdown k hk hkm R hR

/-- The whole catalogue at the top grade has the lift provision at `⊥`, for `0 < m`. -/
theorem botLiftProvisionIn_cat_top (hm : 0 < m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) : BotLiftProvisionIn (cat I (m + 1)) (m + 1) x :=
    fun f hf ↦ by
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_top hm hx (isSelfVisible_bot _)
    (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
    fun _ _ ↦ by simp
  exact ⟨W, hW, hWf, code_mem_cat_of_isCutLawful hW⟩

/-- The whole catalogue at the top grade has the lift provision at the positive caps, for
`0 < m`. -/
theorem capLiftProvisionIn_cat_top (hm : 0 < m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) : CapLiftProvisionIn (cat I (m + 1)) (m + 1) x :=
    fun h hh _ _ P hP f hf hfP ↦ by
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_top hm hx hh (mem_cat.mp hP).1 hf hfP
  exact ⟨W, hW, hWf, hWP, mem_cat.mpr ⟨⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩⟩

/-- **The lift provisions for the family of a predicate**, at every grade `0 < k ≤ m + 1`: those
of the predicate at the grades `≥ N`, those of the whole catalogue below. -/
theorem rowFamily_lift (hm : 0 < m) {N : ℕ} {Rw : I.State → Prop}
    (hbot : ∀ k, N ≤ k → k ≤ m + 1 → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      BotLiftProvisionOf Rw k x)
    (hcap : ∀ k, N ≤ k → k ≤ m + 1 → ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      CapLiftProvisionOf Rw k x) {k : ℕ} (hk0 : 0 < k)
    (hkm : k ≤ m + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    BotLiftProvisionIn (rowFamily I N Rw k) k x ∧ CapLiftProvisionIn (rowFamily I N Rw k) k x := by
  rcases lt_or_ge k N with hk | hk
  · rw [rowFamily_of_lt _ hk]
    rcases Nat.lt_or_eq_of_le hkm with hkm' | rfl
    · exact ⟨botLiftProvisionIn_cat hk0 (by omega) hx, capLiftProvisionIn_cat hk0 (by omega) hx⟩
    · exact ⟨botLiftProvisionIn_cat_top hm hx, capLiftProvisionIn_cat_top hm hx⟩
  · rw [rowFamily_of_le _ hk]
    exact ⟨hbot k hk hkm x hx, hcap k hk hkm x hx⟩

end VaughtConjecture.ProfileTower

/-! ### The admitted completion -/

namespace VaughtConjecture

open Finset Label ProfileTower

/-- **The trivial admission with the lift provisions**, from a grade `N ≥ 1`, for `0 < m`. -/
noncomputable def Seed.LiftAdmission.all {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (N : ℕ) (hN : 1 ≤ N) (hm : 0 < m) : I.LiftAdmission where
  toAdmission := Seed.Admission.all I N
  botLift k hk hkm x hx := by
    change BotLiftProvisionIn (rowCat _ k) k x
    have hk' : N ≤ k := hk
    rw [rowCat_of_forall (fun _ ↦ .inr trivial)]
    rcases Nat.lt_or_eq_of_le hkm with hkm' | rfl
    · exact botLiftProvisionIn_cat (by omega) (by omega) hx
    · exact botLiftProvisionIn_cat_top hm hx
  capLift k hk hkm x hx := by
    change CapLiftProvisionIn (rowCat _ k) k x
    have hk' : N ≤ k := hk
    rw [rowCat_of_forall (fun _ ↦ .inr trivial)]
    rcases Nat.lt_or_eq_of_le hkm with hkm' | rfl
    · exact capLiftProvisionIn_cat (by omega) (by omega) hx
    · exact capLiftProvisionIn_cat_top hm hx

end VaughtConjecture

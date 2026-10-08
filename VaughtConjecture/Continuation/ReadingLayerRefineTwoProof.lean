/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefineTwo

/-!
# The refining server at the grade `2` under a separating block

Roadmap, Layer 3 ((R3) of the table of 3.4).

The statement `TowerProfile.RefiningServerTwo` ("a refining server exists at the grade `2`") is
proved at the grade `1` (`TowerProfile.refiningServerOne`) and open at the grade `2` under the
negation of `TowerProfile.SeparatingServersTwo`.

* `TowerProfile.exists_two_of_separating`: the refining server at the grade `2` from a separating
  server: a cell of graded index `(univ, 2)`, at least `h` in `e`, whose entry on the layer at
  the grade `1` is separated by a block `ω * γ` (the cap `ω * γ + 2` is self-visible and short
  at `2`).
* `TowerProfile.refiningServerTwo_of_separating`: `TowerProfile.SeparatingServersTwo I` implies
  `TowerProfile.RefiningServerTwo I`.
* `TowerProfile.not_separatingServerTwo_of_frozen`: the construction through a separating server
  is refuted at every state where each candidate server is frozen
  (`TowerProfile.FrozenServerTwo`): its entry reads a cell at least `h` in `e` below `2`, or in
  the block of a cell less than `h` in `e`.  The codes of the cells of graded index `(univ, 1)`
  lie in the code grid at `1`, so such a code `ω * β + 1` sits below a code `ω * β + 2` of the
  same block.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace Label

/-- A label self-visible at `2` at least `ω * β` is at least `ω * β + 2`. -/
theorem omega0_mul_add_two_le {β : Ordinal.{u}} {t : Label.{u}} (ht : IsSelfVisible 2 t)
    (hβ : (((ω * β : Ordinal.{u}) : Label.{u})) ≤ t) :
    (((ω * β + 2 : Ordinal.{u}) : Label.{u})) ≤ t := by
  induction t using recBotCoeTop with
  | bot => exact absurd hβ (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact le_top
  | coe o =>
    rw [WithBot.coe_le_coe, WithTop.coe_le_coe] at hβ ⊢
    have h2 : (2 : Ordinal.{u}) ≤ o % ω := by exact_mod_cast isSelfVisible_coe.mp ht
    have hq : β ≤ o / ω := (Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp hβ
    rcases hq.lt_or_eq with hlt | heq
    · exact ((omega0_mul_add_natCast_lt hlt 2 0).trans_le
        (by rw [add_zero]; exact Ordinal.mul_div_le o ω)).le.trans' (by simp)
    · calc ω * β + 2 ≤ ω * β + o % ω := (add_le_add_iff_left _).mpr h2
        _ = o := by rw [heq]; exact Ordinal.div_add_mod o ω

/-- A positive label self-visible at `2` is at least `2`. -/
theorem two_le_of_isSelfVisible {x : Label.{u}} (hx : IsSelfVisible 2 x) (hx0 : ⊥ < x) :
    (2 : Label.{u}) ≤ x := by
  have h := omega0_mul_add_two_le (β := 0) hx (by
    simpa using (show ((0 : Ordinal.{u}) : Label.{u}) ≤ x from by
      induction x using recBotCoeTop with
      | bot => exact absurd hx0 (lt_irrefl _)
      | top => exact le_top
      | coe o => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (zero_le (a := o)))))
  simpa using h

end Label

namespace TowerProfile

open TopReadingApexExample StageType

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The cell of the layer at the grade `2` in the profile layer. -/
noncomputable abbrev twoCell (I : Seed.{u} α 3) (a : Fin (I.tower 2).card) :
    Fin (scheme I).card :=
  Fin.castAdd _ a

theorem isLawfulBelow_two_of_scheme {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d) :
    (I.tower 2).rows.IsLawfulBelow (univ, 2) fun d ↦ e (twoCell I d) :=
  (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower 2) (k := 3) (M := mult I)
    (r := fun i ↦ fieldLab I (entry I i)) (h := I.not_univ_succ_le_tower 2) (v := e)
    (X := ((univ : Finset (Fin 5)), 2)) (fun h ↦ absurd h.2 (by omega))).mp he

theorem isLawfulBelow_scheme_of_two {w : Fin (scheme I).card → Label.{u}}
    (hw : (I.tower 2).rows.IsLawfulBelow (univ, 2) fun d ↦ w (twoCell I d)) :
    (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ w d :=
  (Scheme.isLawfulBelow_appendFullCells_iff (S := I.tower 2) (k := 3) (M := mult I)
    (r := fun i ↦ fieldLab I (entry I i)) (h := I.not_univ_succ_le_tower 2) (v := w)
    (X := ((univ : Finset (Fin 5)), 2)) (fun h ↦ absurd h.2 (by omega))).mpr hw

theorem gradedIndex_twoCell (y : Fin (I.tower 2).card) :
    (scheme I).toCellScheme.gradedIndex (twoCell I y) = (I.tower 2).toCellScheme.gradedIndex y :=
  Scheme.appendFullCellsScheme_gradedIndex_castAdd (I.tower 2) 3 _ y

theorem exists_twoCell_eq {x : Fin (scheme I).card}
    (hx : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
    ∃ y, twoCell I y = x := by
  have h1 : (x : ℕ) < (I.tower 2).card :=
    Scheme.lt_card_of_mem_below (S := I.tower 2) (k := 3) (M := mult I)
      (fun h ↦ absurd h.2 (by omega)) hx
  exact ⟨⟨x, h1⟩, Fin.ext rfl⟩

/-- **A separating server at the grade `2`** for a labelling `e` and a cap `h`: a cell of graded
index `(univ, 2)` (the entry `i` of the layer at the grade `1`) at least `h` in `e`, and a block
`γ` such that its entry reads the cells of the layer at the grade `1` at least `ω * γ + 2` exactly
where `e` is at least `h`, reads no such cell in `[ω * γ, ω * γ + 2)`, and every other cell of
graded index `(univ, 2)` read at least `ω * γ + 2` is at least `h` in `e`.  At the grade `1` the
least code where `e` is at least `h` always gives such a block; at the grade `2` it may not
(`TowerProfile.not_separatingServerTwo_of_frozen`). -/
def SeparatingServerTwo (I : Seed.{u} α 3) (e : Fin (scheme I).card → Label.{u}) (h : Label.{u}) :
    Prop :=
  ∃ i : Fin ((I.tower 1).catalogue 2).card, ∃ γ : Ordinal.{u},
    h ≤ e (twoCell I (Fin.natAdd _ i)) ∧
    (∀ d : Fin (I.tower 1).card, (I.tower 1).toCellScheme.grade d ≤ 2 →
      ((((ω * γ + 2 : Ordinal.{u})) : Label.{u}) ≤ (I.tower 1).catalogueEntry 2 i d ↔
          h ≤ e (oneCell I d)) ∧
        ((I.tower 1).catalogueEntry 2 i d < (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) →
          (I.tower 1).catalogueEntry 2 i d < (((ω * γ : Ordinal.{u})) : Label.{u}))) ∧
    ∀ j : Fin ((I.tower 1).catalogue 2).card,
      (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) ≤ agreementHeight ((I.tower 1).fieldGrid 2)
        ((I.tower 1).catalogueEntry 2 i) ((I.tower 1).catalogueEntry 2 j) →
        h ≤ e (twoCell I (Fin.natAdd _ j))

/-- **The refining server at the grade `2` under a separating server** (the statement of
`TowerProfile.RefiningServerTwo` at `e` and `h`, under `TowerProfile.SeparatingServerTwo I e h`
in place of the cell of grade `2` at least `h`).  The construction of
`TowerProfile.exists_one_of_target` one grade up: the lexicographic raise of the entry of the
separating server across the block `ω * γ`, extended through the cells of graded index `(univ, 2)`
agreeing with its field row capped at `ω * γ + 2` (`Scheme.exists_extension_fieldLayer`, the cap
short at `2`), and decoded piecewise across the block. -/
theorem exists_two_of_separating {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 2) fun d ↦ e d)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {V : Label.{u}} (hV : IsSelfVisible 2 V) (hhV : h ≤ V)
    {q : Fin (I.tower 1).card → Label.{u}}
    (hq : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun d ↦ q d.1)
    (hqe : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → min (q d) h = min (e (oneCell I d)) h)
    (hqV : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → h ≤ q d → V ≤ q d)
    (hsep : SeparatingServerTwo I e h) :
    ∃ w : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ w d) ∧
      (∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 → w (oneCell I d) = q d) ∧
      (∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2),
        min (w x) h = min (e x) h) ∧
      ∀ x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2), h ≤ e x → V ≤ w x := by
  classical
  obtain ⟨i, γ, heu, hlinkc, hnew⟩ := hsep
  have hh2 : IsSelfVisible 2 h := hh.mono (by omega)
  have hh0 : h ≠ ⊥ := hhb.ne'
  have he₂ := isLawfulBelow_two_of_scheme he
  set a₀ := (I.tower 1).catalogueEntry 2 i with ha₀def
  have ha₀ : a₀ ∈ (I.tower 1).catalogue 2 := Scheme.catalogueEntry_mem i
  have hu' : (I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin 5)), 2) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ i
  -- the witness of `e` at the server
  obtain ⟨τ₀, hτ₀, hτ₀h, hτ₀E⟩ := CellScheme.Rows.exists_isWitness_rowBelow
    (R := (I.tower 2).rows) hu' he₂ (c := h) hh2 heu
  have hfr (x : Fin (I.tower 2).card)
      (hx : x ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      τ₀ ((I.tower 1).fieldRow 2 a₀ x) = min (e (twoCell I x)) h := by
    have := hτ₀E ⟨x, hx⟩
    have h2 := Scheme.fieldLayer_row_natAdd (S := I.tower 1) (k := 2)
      (hS := I.not_univ_succ_le_tower 1) i ⟨x, le_trans hx hu'.ge⟩
    exact (congrArg τ₀ h2).symm.trans this
  -- the layer at the grade `1` inside the layer at the grade `2`
  have hcast (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
      (Fin.castAdd _ d : Fin (I.tower 2).card) ∈
        (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) := by
    have g1 : (I.tower 2).toCellScheme.gradedIndex (Fin.castAdd _ d) =
        (I.tower 1).toCellScheme.gradedIndex d :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd (I.tower 1) 2 _ d
    exact (CellScheme.mem_below _).mpr (g1.trans_le
      (((I.tower 1).toCellScheme.gradedIndex_le_iff).mpr ⟨subset_univ _, hd⟩))
  have hτa (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
      τ₀ (a₀ d) = min (e (oneCell I d)) h :=
    (congrArg τ₀ (Scheme.fieldRow_castAdd (S := I.tower 1) (k := 2) a₀ d)).symm.trans
      (hfr _ (hcast d hd))
  set θ : Label.{u} := (((ω * γ : Ordinal.{u})) : Label.{u}) with hθdef
  set c : Label.{u} := (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) with hcdef
  have hθc : θ ≤ c := WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)
  have hlink (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
      θ ≤ a₀ d ↔ h ≤ q d := by
    constructor
    · intro hθd
      have hca : c ≤ a₀ d := not_lt.mp fun hlt ↦ ((hlinkc d hd).2 hlt).not_ge hθd
      exact Label.le_of_min_eq_of_le' (hqe d hd) (((hlinkc d hd).1).mp hca)
    · intro hqd
      exact hθc.trans (((hlinkc d hd).1).mpr (Label.le_of_min_eq_of_le' (hqe d hd).symm hqd))
  -- the lexicographic raise
  have ha₀l : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun d ↦ a₀ d.1 :=
    (Scheme.mem_catalogue.mp ha₀).1.isLawfulBelow _
  have hW := CellScheme.Rows.IsLawfulBelow.lex ha₀l hq (β := γ) (K := 2) hh2 hhb
    (fun d hd ↦ hd.2) (fun d hd ↦ hlink d hd.2)
  have hc : IsSelfVisible 2 c := by
    rw [hcdef, isSelfVisible_coe, Ordinal.mul_add_mod_self,
      Ordinal.mod_eq_of_lt (by simpa using Ordinal.natCast_lt_omega0 2)]
    simp
  have hcs : IsShort 2 c := fun o ho ↦ by
    have : o = ω * γ + 2 := WithTop.coe_injective (WithBot.coe_injective ho)
    rw [this, Ordinal.mul_add_mod_self,
      Ordinal.mod_eq_of_lt (by simpa using Ordinal.natCast_lt_omega0 2)]
    simp
  have hag (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
      min (if a₀ d < θ then a₀ d else shiftL (ω * γ) (q d)) c = min (a₀ d) c := by
    by_cases had : a₀ d < θ
    · simp only [had, ↓reduceIte]
    · simp only [had, ↓reduceIte]
      have hθd : θ ≤ a₀ d := not_lt.mp had
      have hqd : h ≤ q d := (hlink d hd).mp hθd
      have h2q : (((2 : Ordinal.{u})) : Label.{u}) ≤ q d :=
        (Label.two_le_of_isSelfVisible hh2 hhb).trans hqd
      have hca : c ≤ a₀ d := not_lt.mp fun hlt ↦ ((hlinkc d hd).2 hlt).not_ge hθd
      rw [min_eq_right (show c ≤ shiftL (ω * γ) (q d) from monotone_shiftL _ h2q),
        min_eq_right hca]
  obtain ⟨r, hr, hrW, hrc⟩ := Scheme.exists_extension_fieldLayer (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) hW ha₀ (h := c) hc (WithBot.bot_lt_coe _) (.inl hcs) hag
  -- the decoder
  have hV0 : V ≠ ⊥ := (hhb.trans_le hhV).ne'
  have hL : IsWitness (stepSuppressor 2) ((fun t ↦ min (raise h t) V) ∘ τ₀) :=
    hτ₀.comp_of_bot_reflecting ((isWitness_raise (K := 2) (hh.mono (by omega)) hhb).min_const hV)
      fun t ht ↦ eq_bot_of_raise_eq_bot ((min_eq_bot.mp ht).resolve_right hV0)
  have hD := isWitness_piecewise (m := 2) (β := γ) (c := id)
    (L := (fun t ↦ min (raise h t) V) ∘ τ₀) (U := fun t ↦ max V (subL (ω * γ) t))
    (IsWitness.id_step 2) hL
    (fun x y _ hxy ↦ max_le_max le_rfl (monotone_subL _ hxy))
    (fun x hx k hk i hi ↦ by
      have hx' : (((ω * γ : Ordinal.{u})) : Label.{u}) ≤ x := hx
      rw [subL_visibilityReplace hx', visibilityReplace_max hi,
        (hV.mono hk).visibilityReplace_eq])
    (fun x _ ↦ (hhb.trans_le (hhV.trans (le_max_left _ _))).ne')
    (fun x y _ _ ↦ (min_le_right _ _).trans (le_max_left _ _))
    (fun x hx _ k i hi ↦ by
      change visibilityReplace k i x < θ
      rw [visibilityReplace_lt_omega0_mul_iff]
      exact hx)
  set D : Label.{u} → Label.{u} := fun t ↦
    if id t < θ then ((fun t ↦ min (raise h t) V) ∘ τ₀) t else max V (subL (ω * γ) t)
    with hDdef
  -- the cells of the layer at the grade `2`
  have hcases (y : Fin (I.tower 2).card) : (∃ d : Fin (I.tower 1).card, Fin.castAdd _ d = y) ∨
      ∃ j : Fin ((I.tower 1).catalogue 2).card, Fin.natAdd _ j = y := by
    change Fin ((I.tower 1).card + ((I.tower 1).catalogue 2).card) at y
    induction y using Fin.addCases with
    | left d => exact .inl ⟨d, rfl⟩
    | right j => exact .inr ⟨j, rfl⟩
  have hq2 (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2)
      (hθd : θ ≤ a₀ d) : c ≤ shiftL (ω * γ) (q d) :=
    monotone_shiftL _ ((Label.two_le_of_isSelfVisible hh2 hhb).trans ((hlink d hd).mp hθd))
  -- the decoded extension, cell by cell
  have hcell (x : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      min (D (r x)) h = min (e (twoCell I x)) h ∧ (h ≤ e (twoCell I x) → V ≤ D (r x)) := by
    have hfrx := hfr x.1 x.2
    by_cases hrx : r x < θ
    · have hrc' := hrc x
      have hrxc : r x < c := hrx.trans_le hθc
      have hfx : (I.tower 1).fieldRow 2 a₀ x.1 = r x := by
        rw [min_eq_left hrxc.le] at hrc'
        rcases lt_or_ge ((I.tower 1).fieldRow 2 a₀ x.1) c with hl | hl
        · rw [min_eq_left hl.le] at hrc'
          exact hrc'.symm
        · rw [min_eq_right hl] at hrc'
          exact absurd hrc' hrxc.ne
      have hDx : D (r x) = min (raise h (τ₀ (r x))) V := by
        simp only [hDdef, id, hrx, ↓reduceIte, Function.comp]
      rw [hDx, ← hfx, hfrx]
      by_cases hex : h ≤ e (twoCell I x)
      · rw [min_eq_right hex, show raise h h = ⊤ from ite_eq_left le_rfl, min_top_left,
          min_eq_right hhV]
        exact ⟨rfl, fun _ ↦ le_rfl⟩
      · have hlt := not_le.mp hex
        rw [min_eq_left hlt.le, show raise h (e (twoCell I x)) = e (twoCell I x) from
          ite_eq_right hex, min_eq_left (hlt.le.trans hhV)]
        exact ⟨min_eq_left hlt.le, fun h' ↦ absurd h' hex⟩
    · have hθr : θ ≤ r x := not_lt.mp hrx
      have hDV : V ≤ D (r x) := by
        simp only [hDdef, id, hrx, ↓reduceIte]
        exact le_max_left _ _
      -- the extension reads at least the cap, so the field row does
      obtain ⟨y, hy⟩ := x
      have hcr : c ≤ r ⟨y, hy⟩ := by
        rcases hcases y with ⟨d, hdy⟩ | ⟨j, hjy⟩
        · have hd : (I.tower 1).toCellScheme.grade d ≤ 2 := by
            subst hdy
            exact (Scheme.appendFullCellsScheme_grade_castAdd (I.tower 1) 2 _ d).symm.trans_le
              hy.2
          have hrd : r ⟨y, hy⟩ = if a₀ d < θ then a₀ d else shiftL (ω * γ) (q d) := by
            subst hdy
            exact hrW d hd
          have hθr' := hθr.trans_eq hrd
          refine le_of_le_of_eq ?_ hrd.symm
          by_cases had : a₀ d < θ
          · simp only [had, ↓reduceIte] at hθr'
            exact absurd hθr' (not_le.mpr had)
          · simp only [had, ↓reduceIte]
            exact hq2 d hd (not_lt.mp had)
        · have hvr : IsSelfVisible 2 (r ⟨y, hy⟩) := by
            have h1 := (CellScheme.Rows.isLawfulBelow_iff.mp hr).orderly ⟨y, hy⟩
            have h2 : (I.tower 2).toCellScheme.grade y = 2 := by
              subst hjy
              exact Scheme.appendFullCellsScheme_grade_natAdd (I.tower 1) 2 _ j
            change IsSelfVisible ((I.tower 2).toCellScheme.grade y) (r ⟨y, hy⟩) at h1
            rwa [h2] at h1
          exact omega0_mul_add_two_le hvr hθr
      have hcf : c ≤ (I.tower 1).fieldRow 2 a₀ y := by
        have := hrc ⟨y, hy⟩
        rw [min_eq_right hcr] at this
        exact min_eq_right_iff.mp this.symm
      have hex : h ≤ e (twoCell I y) := by
        rcases hcases y with ⟨d, hdy⟩ | ⟨j, hjy⟩
        · subst hdy
          have hd : (I.tower 1).toCellScheme.grade d ≤ 2 :=
            (Scheme.appendFullCellsScheme_grade_castAdd (I.tower 1) 2 _ d).symm.trans_le hy.2
          have hfd : (I.tower 1).fieldRow 2 a₀ (Fin.castAdd _ d) = a₀ d :=
            Scheme.fieldRow_castAdd (S := I.tower 1) (k := 2) a₀ d
          have := ((hlinkc d hd).1).mp (hcf.trans_eq hfd)
          exact this
        · subst hjy
          have hfj : (I.tower 1).fieldRow 2 a₀ (Fin.natAdd _ j) =
              agreementHeight ((I.tower 1).fieldGrid 2) a₀ ((I.tower 1).catalogueEntry 2 j) :=
            Scheme.fieldRow_natAdd (S := I.tower 1) (k := 2) a₀ j
          exact hnew j (hcf.trans_eq hfj)
      exact ⟨by rw [min_eq_right (hhV.trans hDV), min_eq_right hex], fun _ ↦ hDV⟩
  -- lawful on the layer at the grade `2`, by the companion `e`
  have hlaw : (I.tower 2).rows.IsLawfulBelow (univ, 2) (D ∘ r) :=
    hr.map_of_bot_iff he₂ (fun d ↦ d.2.2) hD fun x ↦ eq_bot_iff_of_min_eq (hcell x).1 hh0
  -- the labelling of the profile layer
  set rt : Fin (I.tower 2).card → Label.{u} := fun x ↦
    if hx : x ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) then D (r ⟨x, hx⟩)
    else ⊥ with hrtdef
  set w₂ : Fin (scheme I).card → Label.{u} := fun x ↦
    if hx : (x : ℕ) < (I.tower 2).card then rt ⟨x, hx⟩ else ⊥ with hw₂def
  have hw₂two (y : Fin (I.tower 2).card) : w₂ (twoCell I y) = rt y := by
    have hy : ((twoCell I y : Fin (scheme I).card) : ℕ) < (I.tower 2).card := y.2
    simp only [hw₂def, hy, ↓reduceDIte]
    rfl
  have hrt (x : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      rt x.1 = D (r x) := by
    simp only [hrtdef, x.2, ↓reduceDIte]
    rfl
  have hmemtwo {x : Fin (scheme I).card}
      (hx : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2)) :
      ∃ y : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2), twoCell I y.1 = x := by
    obtain ⟨y, rfl⟩ := exists_twoCell_eq hx
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [CellScheme.mem_below, ← gradedIndex_twoCell]
    exact hx
  refine ⟨w₂, isLawfulBelow_scheme_of_two ?_, fun d hd ↦ ?_, fun x hx ↦ ?_, fun x hx hex ↦ ?_⟩
  · have heq : (fun d : (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) ↦
        w₂ (twoCell I d)) = D ∘ r := funext fun d ↦ (hw₂two d).trans (hrt d)
    rw [heq]
    exact hlaw
  · change w₂ (twoCell I (Fin.castAdd ((I.tower 1).catalogue 2).card d)) = q d
    refine (hw₂two _).trans ((hrt ⟨_, hcast d hd⟩).trans ((congrArg D (hrW d hd)).trans ?_))
    by_cases had : a₀ d < θ
    · have hed : ¬ h ≤ e (oneCell I d) := fun hed ↦ had.not_ge ((hlink d hd).mpr
        (Label.le_of_min_eq_of_le' (hqe d hd) hed))
      have hlt := not_le.mp hed
      simp only [had, ↓reduceIte, hDdef, id, Function.comp, hτa d hd, min_eq_left hlt.le,
        show raise h (e (oneCell I d)) = e (oneCell I d) from ite_eq_right hed,
        min_eq_left (hlt.le.trans hhV)]
      exact (Label.eq_of_min_eq_of_lt (hqe d hd).symm hlt).symm
    · have hθd : θ ≤ a₀ d := not_lt.mp had
      have hqd : h ≤ q d := (hlink d hd).mp hθd
      have hns : ¬ shiftL (ω * γ) (q d) < θ :=
        not_lt.mpr (coe_le_shiftL _ (hhb.trans_le hqd).ne')
      simp only [had, ↓reduceIte, hDdef, id, hns, subL_shiftL]
      exact max_eq_right (hqV d hd hqd)
  · obtain ⟨y, rfl⟩ := hmemtwo hx
    rw [hw₂two, hrt]
    exact (hcell y).1
  · obtain ⟨y, rfl⟩ := hmemtwo hx
    rw [hw₂two, hrt]
    exact (hcell y).2 hex

/-- **Separating servers at the grade `2`** at a seed on five points: for every labelling `e` of
the profile layer lawful below `(univ, 2)` and every cap `h` self-visible at `4` with a cell of
grade `2` of the layer at the grade `1` at least `h` in `e`, a separating server
(`TowerProfile.SeparatingServerTwo`). -/
def SeparatingServersTwo (I : Seed.{u} α 3) : Prop :=
  ∀ e : Fin (scheme I).card → Label.{u}, (scheme I).rows.IsLawfulBelow (univ, 2) (fun d ↦ e d) →
    ∀ h : Label.{u}, IsSelfVisible 4 h → ⊥ < h →
      (∃ z₀, (I.tower 1).toCellScheme.grade z₀ = 2 ∧ h ≤ e (oneCell I z₀)) →
      SeparatingServerTwo I e h

/-- **A refining server exists at the grade `2` under separating servers.** -/
theorem refiningServerTwo_of_separating (hsep : SeparatingServersTwo I) : RefiningServerTwo I :=
  fun e he h hh hhb _ hV hhV _ hq hqe hqV hz₀ ↦
    exists_two_of_separating he hh hhb hV hhV hq hqe hqV (hsep e he h hh hhb hz₀)

/-- A server whose entry no block separates: it reads a cell at least `h` in `e` below `2`, or a
cell at least `h` in `e` in the block `ω * β` of a cell less than `h` in `e`. -/
def FrozenServerTwo (I : Seed.{u} α 3) (e : Fin (scheme I).card → Label.{u}) (h : Label.{u})
    (i : Fin ((I.tower 1).catalogue 2).card) : Prop :=
  ∃ d₁ : Fin (I.tower 1).card, (I.tower 1).toCellScheme.grade d₁ ≤ 2 ∧ h ≤ e (oneCell I d₁) ∧
    ((I.tower 1).catalogueEntry 2 i d₁ < (((2 : Ordinal.{u})) : Label.{u}) ∨
      ∃ d₂ : Fin (I.tower 1).card, ∃ β : Ordinal.{u}, (I.tower 1).toCellScheme.grade d₂ ≤ 2 ∧
        ¬ h ≤ e (oneCell I d₂) ∧
        (((ω * β : Ordinal.{u})) : Label.{u}) ≤ (I.tower 1).catalogueEntry 2 i d₂ ∧
        (I.tower 1).catalogueEntry 2 i d₁ < (((ω * (β + 1) : Ordinal.{u})) : Label.{u}))

/-- **Route (b) refuted at a frozen state**: if every cell of graded index `(univ, 2)` at least
`h` in `e` is a frozen server (`TowerProfile.FrozenServerTwo`), no separating server exists. -/
theorem not_separatingServerTwo_of_frozen {e : Fin (scheme I).card → Label.{u}} {h : Label.{u}}
    (hfr : ∀ i, h ≤ e (twoCell I (Fin.natAdd _ i)) → FrozenServerTwo I e h i) :
    ¬ SeparatingServerTwo I e h := by
  rintro ⟨i, γ, heu, hlinkc, -⟩
  obtain ⟨d₁, hd₁, he₁, hcase⟩ := hfr i heu
  have hc₁ := ((hlinkc d₁ hd₁).1).mpr he₁
  rcases hcase with hlow | ⟨d₂, β, hd₂, he₂, hβ, hd₁β⟩
  · have h2c : (((2 : Ordinal.{u})) : Label.{u}) ≤ (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) :=
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_add_self)
    exact (hlow.trans_le h2c).not_ge hc₁
  · have hlt₂ : (I.tower 1).catalogueEntry 2 i d₂ < (((ω * γ : Ordinal.{u})) : Label.{u}) :=
      (hlinkc d₂ hd₂).2 (not_le.mp fun hc ↦ he₂ (((hlinkc d₂ hd₂).1).mp hc))
    have hβγ : ω * β < ω * γ :=
      WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp (hβ.trans_lt hlt₂))
    have hβγ' : β + 1 ≤ γ :=
      Order.add_one_le_of_lt (lt_of_mul_lt_mul_left' hβγ)
    have hle : (((ω * (β + 1) : Ordinal.{u})) : Label.{u}) ≤
        (((ω * γ + 2 : Ordinal.{u})) : Label.{u}) :=
      WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        ((mul_le_mul_right hβγ' ω).trans le_self_add))
    exact (hd₁β.trans_le hle).not_ge hc₁

end TowerProfile

end VaughtConjecture

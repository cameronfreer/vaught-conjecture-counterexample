/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapOwnerPartnerObstruction

/-!
# The LOW clause with the frontier and a separate field: the state-level test

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3); the owner-as-partner
obstruction of `VaughtConjecture.Continuation.SourceGapOwnerPartnerObstruction`.

**The clause** (`FieldAdmission.LowAt Lo Tops L R b`), read on a state of the seed: the context face
`L`, the donor face `R` (both on the five cells of the input, sharing the root `y`), and a **field**
`b`.  The owner is `o` (`3`) of `L`, the lost top `r` (`4`) of `L`, `K = 2`; `Lo` are the donor
cells designated below the top and `Tops` the designated tops.  If the maximum of `R` over `Lo` is
below `b`, every designated top is at least `max b (frontier L)`, with the **frontier**
`min (L o) (visibilityReplace 2 2 (L r))` (`FieldAdmission.frontier`).  This is
`SourceGapRequests.AdmitsLowAt` of the admission lane at these data.  The field is a coordinate of
the state, not the value at a cell of the faces (prospective: the value at a field cell of an
entry, recovered at a reader; not compiled).  So the lift provisions carry it: a provision returns,
with the face, a field self-visible at `2` agreeing with the given one capped at `h`
(`FieldAdmission.IsFieldAdmission`).

**The provisions hold** at every cap self-visible at `2`, for every designation with the
designated tops among `z'`, `o'`, `r'` (any designated cells below the top), from both coatoms:

* at the input `SeparationObstruction.T` (`FieldAdmission.isFieldAdmission_T`), so for both of
  its donors at once: the twisted donor `(⊤, ⊥, ⊤, ⊤, v)`, `v ≠ ⊤` (designation
  `FieldAdmission.loU`, `FieldAdmission.topsU`) and the input itself (designation
  `FieldAdmission.loSelf`, `FieldAdmission.topsSelf`);
* at the input `OwnerPartner.t2`, where the owner-as-partner clause fails
  (`OwnerPartner.not_capProvision_context`), with the donor on the scheme of `T`
  (`FieldAdmission.isFieldAdmission_t2`).

The served faces: from the context coatom, `(f y, ⊥, f y, o', r')` with `o'`, `r'` those of the
donor below `h` and raised to `max h (frontier f)` (and `max h o'`) at or above it; the frontier of
a lawful context face is at most its root (`o ≤ y` at `T`; at `t2`, `min r o ≤ min y o`).  From
the donor coatom, the context face capped at `h` at `o` and `r` with the root of the donor face.
The field is capped at `h` in both.

**What the clause decides** (`FieldAdmission.eq_top_of_lowAt`): with the context at the labels of
the input (`o`, `r` at `⊤`, so the frontier is `⊤`), a state whose low maximum is below the field
has every designated top at `⊤`.  The actual states are admitted at the field `⊤`
(`FieldAdmission.lowAt_of_forall_eq_top`), and the mixed state (`o'` below `⊤`, `r' = v`) is
excluded at every field above `v` (`FieldAdmission.not_lowAt_mixed`).  Images under monotone maps
fixing `⊥` with values self-visible at `2` keep the clause at the image of the field
(`FieldAdmission.lowAt_comp`).

**Status.**  One clause, with the designation read off the donor, serves `T` with both donors and
`t2` at the level of states (GO).  Not compiled: the field cell in the completion (the lower layer
of `VaughtConjecture.Continuation.SourceGapAdmittedSeed` has no cell carrying the field; the
engine needs a cell of grade `2` whose row leaves its value free above a self-visible bound), and
the recovery of the field at the reader.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label SeparationObstruction
open SeparatedInstance (omegaAddTwo)

/-! ### The lawful labellings of the input `t2` -/

namespace OwnerPartner

/-- **The lawful labellings of `t2`** have the form `(v, ⊥, v, w, s)` with
`min s w ≤ min v w`, `min v s = min w s`, and `min v w` self-visible at `2`: the row of `o` reads
`r` below `y` below `o` (so a witness at `o` gives the first inequality, and at a value of `y`
below `o` the shifter commutes with visibility replacement at `2`), and the row of `r` reads `y`
and `o` alike below the cap at `r`. -/
theorem eq_lab2_of_isLawful {P : Fin 5 → Label.{u}} (hP : S2.{u}.rows.IsLawful P) :
    P = lab (P 0) (P 3) (P 4) ∧ min (P 4) (P 3) ≤ min (P 0) (P 3) ∧
      min (P 0) (P 4) = min (P 3) (P 4) ∧ IsSelfVisible 2 (min (P 0) (P 3)) := by
  have hmem (c d : Fin 5) (h : cells.gradedIndex d ≤ cells.gradedIndex c) :
      d ∈ cells.below (cells.gradedIndex c) := h
  have h1 : P 1 = ⊥ := hP.eq_bot_of_row_self_eq_bot 1 rfl
  have hzy : P 2 ≤ P 0 := by
    have := (hP.locality 2).le_of_le (d := ⟨2, hmem 2 2 le_rfl⟩) (d' := ⟨0, hmem 2 0 (by decide)⟩)
      le_rfl le_rfl
    simpa using this
  have hyz : P 0 ≤ P 2 := by
    obtain ⟨u, hu, hle⟩ := hP.availability 0 2 (by decide) rfl
    have key : ∀ u : Fin 5, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
    rwa [key u hu] at hle
  -- the row of `o`
  obtain ⟨g, σ, hw, he⟩ := hP.locality 3
  have e0 := he ⟨0, hmem 3 0 (by decide)⟩
  have e3 := he ⟨3, hmem 3 3 le_rfl⟩
  have e4 := he ⟨4, hmem 3 4 (by decide)⟩
  change min (P 0) (P 3) = min (σ omegaAddTwo) (g 1) at e0
  change min (P 3) (P 3) = min (σ high) (g 2) at e3
  change min (P 4) (P 3) = min (σ low) (g 2) at e4
  rw [min_self] at e3
  have hg : g 2 ≤ g 1 := hw.antitone (by omega)
  have hsw : min (P 4) (P 3) ≤ min (P 0) (P 3) := by
    rw [e4, e0]
    exact min_le_min (hw.monotone low_lt_omegaAddTwo.le) hg
  have hsv : IsSelfVisible 2 (min (P 0) (P 3)) := by
    rcases le_total (P 3) (P 0) with h30 | h03
    · rw [min_eq_right h30]
      exact hP.orderly 3
    · rcases h03.lt_or_eq with h03 | h03
      · have hP3 : P 3 ≤ g 2 := e3 ▸ min_le_right _ _
        have hlt : min (σ omegaAddTwo) (g 1) < g 1 := by
          rw [← e0, min_eq_left h03.le]
          exact (h03.trans_le hP3).trans_le hg
        have hσ : σ omegaAddTwo < g 1 := by
          by_contra hc
          rw [min_eq_right (not_lt.mp hc)] at hlt
          exact lt_irrefl _ hlt
        rw [e0, min_eq_left hσ.le]
        have hσ2 : σ omegaAddTwo ≤ g 2 := by
          have : min (σ omegaAddTwo) (g 1) = σ omegaAddTwo := min_eq_left hσ.le
          rw [← this, ← e0, min_eq_left h03.le]
          exact h03.le.trans hP3
        have hc := hw.visibilityReplace_comm omegaAddTwo 2 hσ2 2 le_rfl
        rw [isSelfVisible_omegaAddTwo_two.visibilityReplace_eq] at hc
        exact hc.symm
      · rw [h03, min_self]
        exact hP.orderly 3
  -- the row of `r`
  have hyr : min (P 0) (P 4) = min (P 3) (P 4) := by
    obtain ⟨g', σ', hw', he'⟩ := hP.locality 4
    have f0 := he' ⟨0, hmem 4 0 (by decide)⟩
    have f3 := he' ⟨3, hmem 4 3 (by decide)⟩
    have f4 := he' ⟨4, hmem 4 4 le_rfl⟩
    change min (P 0) (P 4) = min (σ' low) (g' 1) at f0
    change min (P 3) (P 4) = min (σ' low) (g' 2) at f3
    change min (P 4) (P 4) = min (σ' omegaAddTwo) (g' 2) at f4
    rw [min_self] at f4
    have hg' : g' 2 ≤ g' 1 := hw'.antitone (by omega)
    have hX : min (σ' low) (g' 1) ≤ g' 2 := by
      rw [← f0]
      exact (min_le_right _ _).trans (f4 ▸ min_le_right _ _)
    rw [f0, f3]
    refine le_antisymm (le_min (min_le_left _ _) hX) (min_le_min le_rfl hg')
  refine ⟨funext fun d ↦ ?_, hsw, hyr, hsv⟩
  fin_cases d
  · rfl
  · exact h1
  · exact le_antisymm hzy hyz
  · rfl
  · rfl

end OwnerPartner

namespace FieldAdmission

/-! ### The clause -/

/-- The **frontier** of a context face: the owner capped at the replacement at `2` of the lost
top. -/
noncomputable def frontier (L : Fin 5 → Label.{u}) : Label.{u} :=
  min (L 3) (visibilityReplace 2 2 (L 4))

/-- **The LOW clause at the field `b`** on a state of the seed: if the donor face `R` is below `b`
on the designated cells `Lo`, every designated top is at least `b` and at least the frontier of the
context face `L`. -/
def LowAt (Lo Tops : Finset (Fin 5)) (L R : Fin 5 → Label.{u}) (b : Label.{u}) : Prop :=
  Lo.sup R < b → ∀ t ∈ Tops, max b (frontier L) ≤ R t

/-- The designation at the twisted donor: `e'`, `r'` below the top. -/
abbrev loU : Finset (Fin 5) := {1, 4}

/-- The designation at the twisted donor: the tops `z'`, `o'`. -/
abbrev topsU : Finset (Fin 5) := {2, 3}

/-- The designation at the self donor: `e'` below the top. -/
abbrev loSelf : Finset (Fin 5) := {1}

/-- The designation at the self donor: the tops `z'`, `o'`, `r'`. -/
abbrev topsSelf : Finset (Fin 5) := {2, 3, 4}

variable {Lo Tops : Finset (Fin 5)}

/-- Capping a minimum caps both arguments. -/
theorem min_min_cap (x y h : Label.{u}) : min (min x y) h = min (min x h) (min y h) := by
  rw [min_assoc, min_assoc, min_left_comm h y h, min_self, min_left_comm]

theorem frontier_of_isSelfVisible {L : Fin 5 → Label.{u}} (h4 : IsSelfVisible 2 (L 4)) :
    frontier L = min (L 3) (L 4) := by
  rw [frontier, h4.visibilityReplace_eq]

/-- The clause holds at the field `⊥`-state. -/
theorem lowAt_bot : LowAt Lo Tops (fun _ ↦ (⊥ : Label.{u})) (fun _ ↦ ⊥) ⊥ :=
  fun h ↦ absurd h (not_lt.mpr bot_le)

/-- A state whose designated tops are `⊤` satisfies the clause at every field. -/
theorem lowAt_of_forall_eq_top {L R : Fin 5 → Label.{u}} {b : Label.{u}}
    (h : ∀ t ∈ Tops, R t = ⊤) : LowAt Lo Tops L R b :=
  fun _ t ht ↦ (h t ht).symm ▸ le_top

/-- **Images**: under a monotone map fixing `⊥` with values self-visible at `2`, the image of an
admitted state satisfies the clause at the image of the field. -/
theorem lowAt_comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ0 : σ ⊥ = ⊥)
    (hsv : ∀ x, IsSelfVisible 2 (σ x)) {L R : Fin 5 → Label.{u}} {b : Label.{u}}
    (h : LowAt Lo Tops L R b) :
    LowAt Lo Tops (fun z ↦ σ (L z)) (fun z ↦ σ (R z)) (σ b) := by
  intro hlt t ht
  have hlt' : Lo.sup R < b := by
    by_contra hc
    refine hlt.not_ge ?_
    have hc' : b ≤ Lo.sup R := not_lt.mp hc
    rcases Lo.eq_empty_or_nonempty with he | hne
    · subst he
      rw [Finset.sup_empty, le_bot_iff] at hc'
      rw [hc', hσ0]
      exact bot_le
    · obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup Lo hne R
      exact (hσ (hc'.trans hdeq.le)).trans
        (Finset.le_sup (f := fun z ↦ σ (R z)) hd)
  refine le_trans ?_ (hσ (h hlt' t ht))
  rw [hσ.map_max]
  refine max_le_max le_rfl ?_
  rw [frontier, frontier, (hsv (L 4)).visibilityReplace_eq, hσ.map_min]
  exact min_le_min le_rfl (hσ (le_visibilityReplace (by omega) _))

/-- **What the clause decides**: with the context face at the labels of the input (`o`, `r` at
`⊤`), a state whose low maximum is below the field has every designated top at `⊤`. -/
theorem eq_top_of_lowAt {R : Fin 5 → Label.{u}} {b : Label.{u}}
    (h : LowAt Lo Tops (lab ⊤ ⊤ ⊤) R b) (hlt : Lo.sup R < b) : ∀ t ∈ Tops, R t = ⊤ := by
  intro t ht
  have := h hlt t ht
  have hF : frontier (lab ⊤ ⊤ ⊤ : Fin 5 → Label.{u}) = ⊤ := by
    rw [frontier_of_isSelfVisible (isSelfVisible_top 2)]
    rfl
  rw [hF, max_top_right] at this
  exact top_le_iff.mp this

/-- **The mixed state is excluded at every field above `r'`**: the context at the labels of the
input with the donor `(⊤, ⊥, ⊤, c, v)`, `c < ⊤`. -/
theorem not_lowAt_mixed {c v b : Label.{u}} (hc : c < ⊤) (hvb : v < b) :
    ¬ LowAt loU topsU (lab ⊤ ⊤ ⊤) (lab ⊤ c v) b := fun h ↦ by
  have hlt : loU.sup (lab ⊤ c v) < b := by
    have : loU.sup (lab ⊤ c v : Fin 5 → Label.{u}) = v := by
      simp [loU, lab]
    rw [this]
    exact hvb
  have := eq_top_of_lowAt h hlt 3 (by simp [topsU])
  exact hc.ne this

/-! ### The provisions -/

/-- **A field admission of states** for the context lawfulness `C` and the donor lawfulness `D`:
it holds at the `⊥`-state, passes to images, and has the lift provisions from both coatoms at every
cap `h` self-visible at `2`, carrying a field self-visible at `2` agreeing with the given field
capped at `h`. -/
structure IsFieldAdmission (C D : (Fin 5 → Label.{u}) → Prop)
    (Adm : (Fin 5 → Label.{u}) → (Fin 5 → Label.{u}) → Label.{u} → Prop) : Prop where
  bot : Adm (fun _ ↦ ⊥) (fun _ ↦ ⊥) ⊥
  comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ0 : σ ⊥ = ⊥)
    (hsv : ∀ x, IsSelfVisible 2 (σ x)) {L R : Fin 5 → Label.{u}} {b : Label.{u}}
    (h : Adm L R b) : Adm (fun z ↦ σ (L z)) (fun z ↦ σ (R z)) (σ b)
  context {h b : Label.{u}} (hh : IsSelfVisible 2 h) (hb : IsSelfVisible 2 b)
    {L R f : Fin 5 → Label.{u}} (hL : C L) (hR : D R) (hy : L 0 = R 0) (hadm : Adm L R b)
    (hf : C f) (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : Fin 5 → Label.{u}, ∃ b' : Label.{u}, D W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (R d) h) ∧ IsSelfVisible 2 b' ∧ min b' h = min b h ∧ Adm f W b'
  donor {h b : Label.{u}} (hh : IsSelfVisible 2 h) (hb : IsSelfVisible 2 b)
    {L R f : Fin 5 → Label.{u}} (hL : C L) (hR : D R) (hy : L 0 = R 0) (hadm : Adm L R b)
    (hf : D f) (hfR : ∀ d, min (f d) h = min (R d) h) :
    ∃ W : Fin 5 → Label.{u}, ∃ b' : Label.{u}, C W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (L d) h) ∧ IsSelfVisible 2 b' ∧ min b' h = min b h ∧ Adm W f b'

/-- The designated cells of a served face below the field capped at `h` carry the given face. -/
private theorem sup_lt_of_agree {W R : Fin 5 → Label.{u}} {b h : Label.{u}}
    (hWR : ∀ d, min (W d) h = min (R d) h) (hlt : Lo.sup W < min b h) : Lo.sup R < b := by
  have hb0 : ⊥ < min b h := bot_le.trans_lt hlt
  have hbb : (⊥ : Label.{u}) < b := hb0.trans_le (min_le_left _ _)
  refine (Finset.sup_lt_iff hbb).mpr fun d hd ↦ ?_
  have hWd : W d < min b h := (Finset.sup_lt_iff hb0).mp hlt d hd
  have hRd : R d = W d := Label.eq_of_min_eq_of_lt (hWR d) (hWd.trans_le (min_le_right _ _))
  rw [hRd]
  exact hWd.trans_le (min_le_left _ _)

/-- **The provision from the context coatom**, given the facts it uses about the context faces:
the served donor face is `(f y, ⊥, f y, o', r')` with `o'`, `r'` those of the donor below `h`, and
`max h (frontier f)`, `max h o'` at or above it; the field is capped at `h`. -/
theorem contextProvision (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) {h b : Label.{u}}
    (hh : IsSelfVisible 2 h) (hb : IsSelfVisible 2 b) {L R f : Fin 5 → Label.{u}}
    (hL4 : IsSelfVisible 2 (L 4)) (hR : S.{u}.rows.IsLawful R) (hy : L 0 = R 0)
    (hadm : LowAt Lo Tops L R b) (hf0 : IsSelfVisible 1 (f 0))
    (hf3 : IsSelfVisible 2 (f 3)) (hf4 : IsSelfVisible 2 (f 4)) (hfF : min (f 3) (f 4) ≤ f 0)
    (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : Fin 5 → Label.{u}, ∃ b' : Label.{u}, S.{u}.rows.IsLawful W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (R d) h) ∧ IsSelfVisible 2 b' ∧ min b' h = min b h ∧
      LowAt Lo Tops f W b' := by
  obtain ⟨hRe, hw'a, has'⟩ := eq_lab_of_isLawful hR
  set a := R 0
  set w' := R 3
  set s' := R 4
  set F := min (f 3) (f 4) with hFdef
  have ha : min (f 0) h = min a h := (hfL 0).trans (by rw [hy])
  have hfa_lt (hah : a < h) : f 0 = a := Label.eq_of_min_eq_of_lt ha.symm hah
  have hfa_ge (hah : h ≤ a) : h ≤ f 0 := le_of_min_eq_of_le ha hah
  have hFL : min F h = min (frontier L) h := by
    rw [frontier_of_isSelfVisible hL4, hFdef, min_min_cap, hfL 3, hfL 4,
      ← min_min_cap]
  have hR1 : R 1 = ⊥ := by rw [hRe]; rfl
  have hR2 : R 2 = a := by rw [hRe]; rfl
  have hw'sv : IsSelfVisible 2 w' := hR.orderly 3
  have hs'sv : IsSelfVisible 2 s' := hR.orderly 4
  set w2 := if w' < h then w' else max h F with hw2def
  set s2 := if s' < h then s' else max h w2 with hs2def
  have hw2a : w2 ≤ f 0 := by
    by_cases hw : w' < h
    · rw [hw2def, ite_eq_left hw]
      by_cases hah : a < h
      · rw [hfa_lt hah]; exact hw'a
      · exact hw.le.trans (hfa_ge (not_lt.mp hah))
    · rw [hw2def, ite_eq_right hw]
      exact max_le (hfa_ge ((not_lt.mp hw).trans hw'a)) hfF
  have hw2sv : IsSelfVisible 2 w2 := by
    rw [hw2def]; split_ifs
    exacts [hw'sv, hh.max (hf3.min hf4)]
  have hs2sv : IsSelfVisible 2 s2 := by
    rw [hs2def]; split_ifs
    exacts [hs'sv, hh.max hw2sv]
  -- if `r'` is at least `h` and `o'` below it, the root is `o'`
  have hroot (hs : h ≤ s') (hw : w' < h) : a = w' := by
    have e : min a s' = w' := by rw [has', min_eq_left (hw.le.trans hs)]
    by_contra hne
    rcases le_total a s' with has | has
    · rw [min_eq_left has] at e; exact hne e
    · rw [min_eq_right has] at e; exact absurd (e ▸ hs) (not_le.mpr hw)
  have hlaw : min (f 0) s2 = min w2 s2 := by
    by_cases hs : s' < h
    · rw [hs2def, ite_eq_left hs]
      by_cases hw : w' < h
      · rw [hw2def, ite_eq_left hw]
        by_cases hah : a < h
        · rw [hfa_lt hah]; exact has'
        · have hfa := hfa_ge (not_lt.mp hah)
          rw [min_eq_right (hs.le.trans hfa)]
          rw [min_eq_right (hs.le.trans (not_lt.mp hah))] at has'
          exact has'
      · rw [hw2def, ite_eq_right hw, min_eq_right (hs.le.trans (le_max_left _ _)),
          min_eq_right (hs.le.trans (hfa_ge ((not_lt.mp hw).trans hw'a)))]
    · have hs' := not_lt.mp hs
      rw [hs2def, ite_eq_right hs]
      by_cases hw2h : h ≤ w2
      · rw [max_eq_right hw2h, min_eq_right hw2a, min_self]
      · have hw : w' < h := by
          by_contra hw
          rw [hw2def, ite_eq_right hw] at hw2h
          exact hw2h (le_max_left _ _)
        have haw := hroot hs' hw
        have hw2 : w2 = w' := by rw [hw2def, ite_eq_left hw]
        rw [max_eq_left (not_le.mp hw2h).le, hw2, hfa_lt (haw ▸ hw), haw]
  have hagree (d : Fin 5) : min (lab (f 0) w2 s2 d) h = min (R d) h := by
    fin_cases d
    · exact ha
    · change min ⊥ h = min (R 1) h; rw [hR1]
    · change min (f 0) h = min (R 2) h; rw [hR2]; exact ha
    · change min w2 h = min w' h
      by_cases hw : w' < h
      · rw [hw2def, ite_eq_left hw]
      · rw [hw2def, ite_eq_right hw, min_eq_right (le_max_left _ _), min_eq_right (not_lt.mp hw)]
    · change min s2 h = min s' h
      by_cases hs : s' < h
      · rw [hs2def, ite_eq_left hs]
      · rw [hs2def, ite_eq_right hs, min_eq_right (le_max_left _ _), min_eq_right (not_lt.mp hs)]
  refine ⟨lab (f 0) w2 s2, min b h,
    isLawful_lab hf0 hw2sv hs2sv hw2a hlaw, rfl, hagree, hb.min hh, by rw [min_assoc, min_self],
    fun hlt t ht ↦ ?_⟩
  have horig := hadm (sup_lt_of_agree hagree hlt) t ht
  rw [frontier_of_isSelfVisible hf4]
  by_cases hRt : R t < h
  · have hWt : lab (f 0) w2 s2 t = R t := Label.eq_of_min_eq_of_lt (hagree t).symm hRt
    rw [hWt]
    have hFt : F = frontier L := by
      have hfr : frontier L < h := ((le_max_right _ _).trans horig).trans_lt hRt
      exact Label.eq_of_min_eq_of_lt hFL.symm hfr
    refine max_le ((min_le_left _ _).trans ((le_max_left _ _).trans horig)) ?_
    change F ≤ R t
    rw [hFt]
    exact (le_max_right _ _).trans horig
  · have hRt' := not_lt.mp hRt
    have hWt : h ≤ lab (f 0) w2 s2 t := le_of_min_eq_of_le (hagree t) hRt'
    refine max_le ((min_le_right _ _).trans hWt) ?_
    change F ≤ lab (f 0) w2 s2 t
    rcases hTops t ht with rfl | rfl | rfl
    · exact hfF
    · change F ≤ w2
      rw [hw2def, ite_eq_right (not_lt.mpr hRt')]
      exact le_max_right _ _
    · change F ≤ s2
      rw [hs2def, ite_eq_right (not_lt.mpr hRt')]
      by_cases hw : w' < h
      · have haw := hroot hRt' hw
        exact hfF.trans ((hfa_lt (haw ▸ hw)).le.trans ((haw ▸ hw).le.trans (le_max_left _ _)))
      · rw [hw2def, ite_eq_right hw]
        exact (le_max_right _ _).trans (le_max_right _ _)

/-- **The provision from the donor coatom**, given lawfulness of the served context face: the
context face capped at `h` at `o` and `r`, with the root of the donor face; the field is capped at
`h`. -/
theorem donorProvision {C : (Fin 5 → Label.{u}) → Prop} {h b : Label.{u}}
    (hh : IsSelfVisible 2 h) (hb : IsSelfVisible 2 b) {L R f : Fin 5 → Label.{u}}
    (hLe : L = lab (L 0) (L 3) (L 4)) (hL4 : IsSelfVisible 2 (L 4)) (hy : L 0 = R 0)
    (hadm : LowAt Lo Tops L R b) (hfR : ∀ d, min (f d) h = min (R d) h)
    (hW : C (lab (f 0) (min (L 3) h) (min (L 4) h))) :
    ∃ W : Fin 5 → Label.{u}, ∃ b' : Label.{u}, C W ∧ W 0 = f 0 ∧
      (∀ d, min (W d) h = min (L d) h) ∧ IsSelfVisible 2 b' ∧ min b' h = min b h ∧
      LowAt Lo Tops W f b' := by
  have ha : min (f 0) h = min (L 0) h := (hfR 0).trans (by rw [hy])
  have hagree (d : Fin 5) : min (lab (f 0) (min (L 3) h) (min (L 4) h) d) h = min (L d) h := by
    fin_cases d
    · exact ha
    · change min ⊥ h = min (L 1) h; rw [hLe]; rfl
    · change min (f 0) h = min (L 2) h; rw [hLe]; exact ha
    · change min (min (L 3) h) h = min (L 3) h; rw [min_assoc, min_self]
    · change min (min (L 4) h) h = min (L 4) h; rw [min_assoc, min_self]
  refine ⟨_, min b h, hW, rfl, hagree, hb.min hh, by rw [min_assoc, min_self],
    fun hlt t ht ↦ ?_⟩
  have horig := hadm (sup_lt_of_agree hfR hlt) t ht
  have hFW : frontier (lab (f 0) (min (L 3) h) (min (L 4) h)) ≤ min (frontier L) h := by
    rw [frontier_of_isSelfVisible (hL4.min hh), frontier_of_isSelfVisible hL4]
    change min (min (L 3) h) (min (L 4) h) ≤ _
    rw [← min_min_cap]
  by_cases hRt : R t < h
  · rw [Label.eq_of_min_eq_of_lt (hfR t).symm hRt]
    exact max_le ((min_le_left _ _).trans ((le_max_left _ _).trans horig))
      (hFW.trans ((min_le_left _ _).trans ((le_max_right _ _).trans horig)))
  · have hft : h ≤ f t := le_of_min_eq_of_le (hfR t) (not_lt.mp hRt)
    exact max_le ((min_le_right _ _).trans hft) (hFW.trans ((min_le_right _ _).trans hft))

/-! ### The field admission at `T` and at `t2` -/

/-- **The clause is a field admission at the input `T`** (context and donor on the scheme of `T`),
for every designation with the designated tops among `z'`, `o'`, `r'`. -/
theorem isFieldAdmission_T (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) :
    IsFieldAdmission S.{u}.rows.IsLawful S.{u}.rows.IsLawful (LowAt Lo Tops) where
  bot := lowAt_bot
  comp hσ hσ0 hsv _ _ _ h := lowAt_comp hσ hσ0 hsv h
  context := fun {h b} hh hb {L R f} hL hR hy hadm hf hfL ↦ by
    obtain ⟨-, hfwa, -⟩ := eq_lab_of_isLawful hf
    exact contextProvision hTops hh hb (hL.orderly 4) hR hy hadm (hf.orderly 0)
      (hf.orderly 3) (hf.orderly 4) ((min_le_left _ _).trans hfwa) hfL
  donor := fun {h b} hh hb {L R f} hL hR hy hadm hf hfR ↦ by
    obtain ⟨hLe, hwa, has⟩ := eq_lab_of_isLawful hL
    refine donorProvision hh hb hLe (hL.orderly 4) hy hadm hfR ?_
    have ha : min (f 0) h = min (L 0) h := (hfR 0).trans (by rw [hy])
    refine isLawful_lab (hf.orderly 0) ((hL.orderly 3).min hh) ((hL.orderly 4).min hh) ?_ ?_
    · by_cases hah : L 0 < h
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah]
        exact (min_le_left _ _).trans hwa
      · exact (min_le_right _ _).trans (le_of_min_eq_of_le ha (not_lt.mp hah))
    · by_cases hah : L 0 < h
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_assoc, has, min_min_cap]
      · have hf0 := le_of_min_eq_of_le ha (not_lt.mp hah)
        rw [min_eq_right ((min_le_right _ _).trans hf0), ← min_min_cap,
          ← has, min_comm (L 0), min_assoc, min_eq_right (not_lt.mp hah)]

/-- **The clause is a field admission at the input `t2`** (context on the scheme of `t2`, donor on
that of `T`), for every designation with the designated tops among `z'`, `o'`, `r'`: the
owner-as-partner clause fails there (`OwnerPartner.not_capProvision_context`). -/
theorem isFieldAdmission_t2 (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) :
    IsFieldAdmission OwnerPartner.S2.{u}.rows.IsLawful S.{u}.rows.IsLawful (LowAt Lo Tops) where
  bot := lowAt_bot
  comp hσ hσ0 hsv _ _ _ h := lowAt_comp hσ hσ0 hsv h
  context := fun {h b} hh hb {L R f} hL hR hy hadm hf hfL ↦ by
    obtain ⟨-, hfsw, -, -⟩ := OwnerPartner.eq_lab2_of_isLawful hf
    refine contextProvision hTops hh hb (hL.orderly 4) hR hy hadm (hf.orderly 0)
      (hf.orderly 3) (hf.orderly 4) ?_ hfL
    rw [min_comm]
    exact hfsw.trans (min_le_left _ _)
  donor := fun {h b} hh hb {L R f} hL hR hy hadm hf hfR ↦ by
    obtain ⟨hLe, hsw, has, hsv⟩ := OwnerPartner.eq_lab2_of_isLawful hL
    refine donorProvision hh hb hLe (hL.orderly 4) hy hadm hfR ?_
    have ha : min (f 0) h = min (L 0) h := (hfR 0).trans (by rw [hy])
    refine OwnerPartner.isLawful_lab2 (hf.orderly 0) ((hL.orderly 3).min hh)
      ((hL.orderly 4).min hh) ?_ ?_ ?_
    · by_cases hah : L 0 < h
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_assoc]
        exact hsv.min hh
      · rw [min_eq_right ((min_le_right _ _).trans (le_of_min_eq_of_le ha (not_lt.mp hah)))]
        exact (hL.orderly 3).min hh
    · by_cases hah : L 0 < h
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_min_cap, ← min_assoc]
        exact min_le_min_right _ hsw
      · rw [min_eq_right ((min_le_right _ _).trans (le_of_min_eq_of_le ha (not_lt.mp hah)))]
        exact min_le_right _ _
    · by_cases hah : L 0 < h
      · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_assoc, has, min_min_cap]
      · have hf0 := le_of_min_eq_of_le ha (not_lt.mp hah)
        rw [min_eq_right ((min_le_right _ _).trans hf0), ← min_min_cap,
          ← has, min_comm (L 0), min_assoc, min_eq_right (not_lt.mp hah)]

/-! ### Both donors at `T`, and the twisted donor at `t2` -/

theorem topsU_sub : ∀ t ∈ topsU, t = 2 ∨ t = 3 ∨ t = 4 := by decide

theorem topsSelf_sub : ∀ t ∈ topsSelf, t = 2 ∨ t = 3 ∨ t = 4 := by decide

/-- **One clause at `T` for both donors**: the twisted donor's designation and the self donor's
designation give field admissions at `T`, and the actual states are admitted at the field `⊤`. -/
theorem isFieldAdmission_T_both (v : Label.{u}) :
    IsFieldAdmission S.{u}.rows.IsLawful S.{u}.rows.IsLawful (LowAt loU topsU) ∧
      IsFieldAdmission S.{u}.rows.IsLawful S.{u}.rows.IsLawful (LowAt loSelf topsSelf) ∧
      LowAt loU topsU (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v) ⊤ ∧
      LowAt loSelf topsSelf (lab ⊤ ⊤ ⊤ : Fin 5 → Label.{u}) (lab ⊤ ⊤ ⊤) ⊤ :=
  ⟨isFieldAdmission_T topsU_sub, isFieldAdmission_T topsSelf_sub,
    lowAt_of_forall_eq_top fun t ht ↦ by
      simp only [topsU, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl <;> rfl,
    lowAt_of_forall_eq_top fun t ht ↦ by
      simp only [topsSelf, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> rfl⟩

/-- **The clause at `t2` with the twisted donor**: a field admission, with the actual state (the
labels of `t2`, the donor `(⊤, ⊥, ⊤, ⊤, v)`) admitted at the field `⊤`. -/
theorem isFieldAdmission_t2_U (v : Label.{u}) :
    IsFieldAdmission OwnerPartner.S2.{u}.rows.IsLawful S.{u}.rows.IsLawful (LowAt loU topsU) ∧
      LowAt loU topsU (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ v) ⊤ :=
  ⟨isFieldAdmission_t2 topsU_sub, lowAt_of_forall_eq_top fun t ht ↦ by
    simp only [topsU, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> rfl⟩

end FieldAdmission

end VaughtConjecture

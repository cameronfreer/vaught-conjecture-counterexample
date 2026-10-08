/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Continuation.H2One
import VaughtConjecture.Continuation.H2Two
import VaughtConjecture.Continuation.SourceGapOwnerPartnerObstruction

/-!
# Owner lowering at grade `1` on two points (work file)

WORK FILE (branch `research/work-owner-one`).

Owner lowering at the grade `1` (`FieldAdmission.OwnerLowering … o r 1 …`) is the hypothesis
`hOL` of `H2.stateAdmission_one`.  This file shows that it does **not** follow from legality and
the source-gap clauses at grade `1`.

**The obstruction** (`H2.le_frontierAt_one`, `H2.not_ownerLowering_one_of_label_ne_top`).  In a
source-gap context of grade `1` the owner `o` and the lost top `r` are labelled `⊤`, so locality of
the label of the context at the owner forces every cell `a` of grade `1` labelled below `⊤` to be
read by the owner below the lost top.  In every lawful labelling `W`, locality at the owner then
gives `min (W a) (W o) ≤ min (W r) (W o)`, and when the owner is the only cell of its graded index,
availability gives `W a ≤ W o`; so the frontier `min (W o) (W r)` is at least `W a`.  For a cell
`a` of the common face, `W a` is prescribed by the donor face; a donor face with a value above the
cap there forbids a frontier at most the cap, and owner lowering fails.  The strict source gaps
constrain only the cells labelled `⊤`, so they do not exclude such a cell.  The proof of
`FieldAdmission.ownerLowering_of_isLegal` avoids this by capping the cells of the top grade `K`,
which at `K = 1` include the cells of grade `1` of the common face.

**The instance** (`OwnerGradeOne.ctx`, `OwnerGradeOne.isLegal_ctx`).  On two points with the
interval plan, four cells:

| cell | scope  | grade | row on the cells `0`–`2`  | label |
|------|--------|-------|---------------------------|-------|
| 0    | `{0}`  | 1     | `(2, ω + 2, ω·2 + 2)`     | `⊥`   |
| 1    | `{1}`  | 1     | the same                  | `⊤`   |
| 2    | `univ` | 1     | the same                  | `⊤`   |
| 3    | `univ` | 2     | `⊥`                       | `⊥`   |

The lawful labellings are `(a, b, c, ⊥)` with `a ≤ b ≤ c` self-visible at `1`
(`OwnerGradeOne.isLawful_lab`, `OwnerGradeOne.conditions_univ`).  With owner `2`, lost top `1` and
lost point `1`, it is a source-gap context of grade `1` along every root on the point `0`
(`OwnerGradeOne.isSourceGapContextAt_ctx`): the gap at the owner is `ω + 2 < ω·2 + 2`, and every
cell labelled `⊤` contains the lost point.

**The refutation** (`OwnerGradeOne.not_ownerLowering_one`,
`OwnerGradeOne.exists_not_ownerLowering_one`).  The face on `{0}` is the cell `0` alone; its
labelling `(1)` is lawful, so it extends to a lawful labelling of every legal donor with this face
(bountifulness at the cap `⊥`).  At the cap `⊥` that donor face agrees on the root with every
context face, and its value `1` at the cell `0`, labelled `⊥` in the context, is above the cap.  So
owner lowering at the grade `1` fails at this legal context **for every legal donor** with the same
root face, the context itself among them.  What is refuted is the clause `OwnerLowering … 1 …` at
this context; donor raising and the other inputs of `H2.stateAdmission_one` are not addressed.

**Owner lowering below the designated tops** (`H2.OwnerLoweringBelow`,
`H2.selfLow_isStateAdmissionGap_of_below`, `H2.stateAdmission_one_of_below`).  The donor provision
of the clause uses owner lowering only through the designated tops: below the cap the frontier of
the lowered face is that of the context face (agreement capped at `h`), and at or above the cap it
must be at most the designated top.  So owner lowering may be weakened to owner lowering below the
designated tops: the frontier of the lowered face at most every designated top `t` of the donor
face at least `h` with `visibilityReplace K K (Lo.sup g) < g t`.  With it in place of owner
lowering, the clause is an admission of states under donor raising with the gap
(`H2.DonorRaisingGap`).  At the context above, with itself as donor and the designated tops among
the cells `1` and `2`, donor raising and owner lowering below the designated tops hold
(`OwnerGradeOne.donorRaising_ctx`, `OwnerGradeOne.ownerLoweringBelow_ctx`), so the clause is an
admission of states there (`OwnerGradeOne.isStateAdmission_ctx`) although owner lowering fails.

**The clause is not an admission at every context of grade `1`** (`OwnerGradeOneTop.ctx`,
`OwnerGradeOneTop.not_isStateAdmission_designated`).  A second legal context on two points, with the
root cell `0` labelled `⊤` and a cell `3` of graded index `(univ, 2)`, labelled `⊥`, whose row reads
every cell at `2`: in every lawful labelling the cell `3` lies below the lost top `1` (locality at
`3`, the grade of `1` being below that of `3`), the lost top below the root cell, and the root cell
below the owner.  At a cap `h` with finite part `1` (here `h = 1`), a context face at least `h` at
the cell `3` forces every face agreeing with it capped at `h` to be at least `h` at `3`, hence at
least `h + 1` there (the cell `3` is self-visible at `2`), hence above `h` at the lost top and at
the owner.  A donor face with the lost top at exactly `h` and the cell `3` at `⊥` then admits no
lowered face with frontier at most its lost top.  With the designation of the clause at two points
(the designated cells the cells labelled below `⊤`, the designated tops containing every cell
labelled `⊤` of grade at most `1`, off the root and not determined by the root), the donor provision
of the clause fails at the cap `1`: the clause is **not an admission of states** at this legal
context with itself as donor, and owner lowering below the designated tops fails there.  So no form
of owner lowering serves at grade `1` in general; the root cell here is labelled `⊤`, so the cells
of the root are not all designated cells.
-/

universe u

/-! ### The obstruction at grade `1` -/

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- **The frontier at grade `1` is at least every cell labelled below `⊤`** of grade `1`, in every
lawful labelling `f` of a source-gap context of grade `1` whose owner is the only cell of its
graded index.  The label of the context is `⊤` at the owner and at the lost top, so locality of
the label at the owner reads such a cell `a` below the lost top; locality of `f` at the owner then
gives `min (f a) (f o) ≤ min (f r) (f o)`, and availability gives `f a ≤ f o`. -/
theorem le_frontierAt_one {k n : ℕ} {t' : StageType.{u} α k} {g₀ : Fin n ↪ Fin k} {l : Fin k}
    {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt 1 g₀ l o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {f : Fin t'.card → Label.{u}} (hf : t'.rows.IsLawful f) {a : Fin t'.card}
    (ha : t'.label a ≠ ⊤) (hga : t'.toCellScheme.grade a = 1) :
    f a ≤ frontierAt o r 1 f := by
  have hgr1 : t'.toCellScheme.grade r ≤ 1 := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hgr : t'.toCellScheme.grade r = 1 :=
    le_antisymm hgr1 (t'.isWellFormed.isWellFormed.grade_pos r)
  have hbelow (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ 1) :
      d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) :=
    (CellScheme.mem_below _).mpr ⟨show t'.toCellScheme.scope d ⊆ t'.toCellScheme.scope o by
      rw [hs.scope_owner]; exact subset_univ _,
      show t'.toCellScheme.grade d ≤ t'.toCellScheme.grade o by rw [hs.grade_owner]; exact hd⟩
  set x := t'.rows.row o ⟨r, hbelow r hgr1⟩
  set y := t'.rows.row o ⟨a, hbelow a hga.le⟩
  -- the label of the context reads `a` below the lost top
  have hyx : y ≤ x := by
    obtain ⟨g, σ, hw, he⟩ := t'.isLawful.locality o
    have er := he ⟨r, hbelow r hgr1⟩
    have ea := he ⟨a, hbelow a hga.le⟩
    change min (t'.label r) (t'.label o) = min (σ x) (g (t'.toCellScheme.grade r)) at er
    change min (t'.label a) (t'.label o) = min (σ y) (g (t'.toCellScheme.grade a)) at ea
    rw [hs.label_lost, hs.label_owner, min_self, eq_comm, _root_.min_eq_top] at er
    rw [hs.label_owner, min_top_right, hga, ← hgr, er.2, min_top_right] at ea
    by_contra hxy
    exact ha (ea.trans (top_le_iff.mp (er.1 ▸ hw.monotone (not_le.mp hxy).le)))
  -- locality and availability at the owner
  have hloc := (hf.locality o).le_of_le (d := ⟨a, hbelow a hga.le⟩) (d' := ⟨r, hbelow r hgr1⟩)
    hyx (by rw [hgr, hga])
  change min (f a) (f o) ≤ min (f r) (f o) at hloc
  obtain ⟨u, hu, hau⟩ := hf.availability a o (by rw [hs.scope_owner]; exact subset_univ _)
    (hga.trans hs.grade_owner.symm)
  rw [honly u hu] at hau
  rw [min_eq_left hau] at hloc
  exact le_min hau ((hloc.trans (min_le_left _ _)).trans (le_visibilityReplace (by omega) _))

/-- **Owner lowering at grade `1` fails** at a source-gap context of grade `1` whose owner is the
only cell of its graded index, as soon as a cell `i` of the common face of grade `1`, labelled
below `⊤`, takes in some lawful donor face a value above a cap `h` at which the donor face agrees
on the face with some lawful context face: a lowered context face has the value of the donor face
at `i`, which is at most the frontier (`H2.le_frontierAt_one`), which would be at most `h`. -/
theorem not_ownerLowering_one_of_label_ne_top {k n m n' : ℕ} {t' : StageType.{u} α k}
    {g₀ : Fin n' ↪ Fin k} {l : Fin k} {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt 1 g₀ l o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {f : Fin n ↪ Fin k} {s : StageType.{u} α n} (ht : restrictFace f t' = some s)
    {tb : StageType.{u} α m} {gb : Fin n ↪ Fin m} (htb : restrictFace gb tb = some s)
    {i : Fin s.card} (hi : s.label i ≠ ⊤) (hgi : s.toCellScheme.grade i = 1) {h : Label.{u}}
    (hh : IsSelfVisible 1 h) {L : Fin t'.card → Label.{u}} (hL : t'.rows.IsLawful L)
    {G : Fin tb.card → Label.{u}} (hG : tb.rows.IsLawful G)
    (hroot : ∀ j, min (G (faceCell htb j)) h = min (L (faceCell ht j)) h)
    (hlt : h < G (faceCell htb i)) :
    ¬ OwnerLowering (faceCell ht) (faceCell htb) o r 1 t'.rows.IsLawful tb.rows.IsLawful := by
  intro hOL
  obtain ⟨W, hW, hWr, -, hF⟩ := hOL hh hL hG hroot
  have hle := le_frontierAt_one hs honly hW (a := faceCell ht i)
    (by rw [label_faceCell]; exact hi) (by rw [grade_faceCell]; exact hgi)
  rw [hWr i] at hle
  exact absurd (hle.trans hF) (not_le.mpr hlt)

/-! ### Owner lowering below the designated tops -/

section Below

variable {ιC ιD ιR : Type*} {rc : ιR → ιC} {rd : ιR → ιD} {K : ℕ}

variable (rc rd) in
/-- **Owner lowering below the designated tops** `Tops`: a lawful context face and a lawful donor
face `g` agreeing with it on the root capped at `h` give a lawful context face with the root of
the donor face, agreeing with the context face capped at `h`, whose frontier is at most every
designated top `t` of `g` at least `h` and above the replaced maximum of the designated cells `Lo`
(`visibilityReplace K K (Lo.sup g) < g t`, the antecedent of `H2.SelfLowG`).  It follows from owner
lowering (`H2.ownerLoweringBelow_of_ownerLowering`) and is what the donor provision of the clause
uses. -/
def OwnerLoweringBelow (o r : ιC) (K : ℕ) (C : (ιC → Label.{u}) → Prop)
    (D : (ιD → Label.{u}) → Prop) (Lo Tops : Finset ιD) : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible K h → ∀ {L : ιC → Label.{u}} {g : ιD → Label.{u}}, C L → D g →
    (∀ x, min (g (rd x)) h = min (L (rc x)) h) →
    ∃ W : ιC → Label.{u}, C W ∧ (∀ x, W (rc x) = g (rd x)) ∧ (∀ d, min (W d) h = min (L d) h) ∧
      ∀ t ∈ Tops, h ≤ g t → visibilityReplace K K (Lo.sup g) < g t → frontierAt o r K W ≤ g t

/-- Owner lowering gives owner lowering below every designation. -/
theorem ownerLoweringBelow_of_ownerLowering {o r : ιC} {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} (hOL : OwnerLowering rc rd o r K C D) (Lo Tops : Finset ιD) :
    OwnerLoweringBelow rc rd o r K C D Lo Tops := fun hh _ _ hL hg hroot ↦ by
  obtain ⟨W, hW, hWr, hWL, hWF⟩ := hOL hh hL hg hroot
  exact ⟨W, hW, hWr, hWL, fun _ _ ht _ ↦ hWF.trans ht⟩

/-- **The clause is an admission of states** under the order law at the owner, the frontier bound
at the root cells `A`, donor raising with the gap, and owner lowering below the designated tops (in
place of owner lowering, `H2.selfLow_isStateAdmissionGap`).  Below the cap the frontier of the
lowered face is that of the context face, by agreement capped at `h`; at or above the cap it is at
most the designated top. -/
theorem selfLow_isStateAdmissionGap_of_below {o r : ιC} {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {Lo Tops : Finset ιD} (A : Set ιR)
    (hCo : ∀ f, C f → IsSelfVisible K (f o))
    (hCF : ∀ f, C f → ∀ a ∈ A, frontierAt o r K f ≤ f (rc a))
    (hDR : DonorRaisingGap rc rd K C D A Lo Tops)
    (hOL : OwnerLoweringBelow rc rd o r K C D Lo Tops) :
    IsStateAdmission rc rd K C D (SelfLowG o r K Lo Tops) where
  bot := fun _ _ h ↦ absurd h (by simp)
  comp := fun {σ} hσ hσ0 hc {L R} h t ht hlt ↦ by
    have hlt' : visibilityReplace K K (Lo.sup R) < R t := by
      by_contra hcon
      refine hlt.not_ge ?_
      have hc' : R t ≤ visibilityReplace K K (Lo.sup R) := not_lt.mp hcon
      calc σ (R t) ≤ σ (visibilityReplace K K (Lo.sup R)) := hσ hc'
        _ = visibilityReplace K K (σ (Lo.sup R)) := hc _
        _ ≤ visibilityReplace K K (Lo.sup fun z ↦ σ (R z)) :=
          monotone_visibilityReplace le_rfl (le_sup_comp hσ0 R)
    have := hσ (h t ht hlt')
    refine le_trans (le_of_eq ?_) this
    rw [frontierAt, frontierAt, hσ.map_min, hc]
  context := fun {h} hh {L f R} hL hR hy hadm hf hfL ↦ by
    have hroot (x : ιR) : min (f (rc x)) h = min (R (rd x)) h := by rw [hfL, hy]
    have hsv : IsSelfVisible K (frontierAt o r K f) :=
      (hCo f hf).min (visibilityReplace_self_visibilityReplace le_rfl (f r))
    have hgap : ∀ t ∈ Tops, visibilityReplace K K (Lo.sup R) < R t →
        min (frontierAt o r K f) h ≤ R t := fun t ht hlt ↦ by
      rw [frontierAt_cap (o := o) (r := r) hh hfL]
      exact (min_le_left _ _).trans (hadm t ht hlt)
    obtain ⟨W, hW, hWr, hWR, hWt⟩ := hDR hh hsv hR hf hroot (hCF f hf) hgap
    refine ⟨W, hW, hWr, hWR, fun t ht hlt ↦ ?_⟩
    by_cases hRt : R t < h
    · have hWt' : W t = R t := Label.eq_of_min_eq_of_lt (hWR t).symm hRt
      rw [hWt'] at hlt ⊢
      have hsup := sup_eq_of_lt_cap (Lo := Lo) hWR hRt hlt
      have horig := hadm t ht (by rw [hsup]; exact hlt)
      have hFF : frontierAt o r K f = frontierAt o r K L :=
        Label.eq_of_min_eq_of_lt (frontierAt_cap (o := o) (r := r) hh hfL).symm (horig.trans_lt hRt)
      rw [hFF]
      exact horig
    · rcases hWt t ht (not_lt.mp hRt) with h1 | h1
      · exact h1
      · exact absurd hlt (not_lt.mpr h1)
  donor := fun {h} hh {L R f} hL hR hy hadm hf hfR ↦ by
    have hroot (x : ιR) : min (f (rd x)) h = min (L (rc x)) h := by rw [hfR, hy]
    obtain ⟨W, hW, hWr, hWL, hWF⟩ := hOL hh hL hf hroot
    refine ⟨W, hW, hWr, hWL, fun t ht hlt ↦ ?_⟩
    by_cases hRt : R t < h
    · have hft : f t = R t := Label.eq_of_min_eq_of_lt (hfR t).symm hRt
      rw [hft] at hlt ⊢
      have hsup := sup_eq_of_lt_cap (Lo := Lo) hfR hRt hlt
      have horig := hadm t ht (by rw [hsup]; exact hlt)
      have hFW : frontierAt o r K W = frontierAt o r K L :=
        Label.eq_of_min_eq_of_lt (frontierAt_cap (o := o) (r := r) hh hWL).symm
          (horig.trans_lt hRt)
      rw [hFW]
      exact horig
    · have hft : h ≤ f t := by
        have e := hfR t
        rw [min_eq_right (not_lt.mp hRt)] at e
        exact min_eq_right_iff.mp e
      exact hWF t ht hft hlt

end Below

/-- **The state-level provisions at grade `1`**, from donor raising with the gap and owner lowering
below the designated tops at the grade `1` (both hypotheses); owner lowering itself
(`H2.stateAdmission_one`) fails at some legal contexts (`OwnerGradeOne.not_ownerLowering_one`). -/
theorem stateAdmission_one_of_below {t' : StageType.{u} α 2} {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hDR : DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Lo Tops)
    (hOL : OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r 1
      t'.rows.IsLawful tb.rows.IsLawful Lo Tops) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (SelfLowG o r 1 Lo Tops) := by
  refine selfLow_isStateAdmissionGap_of_below (rootTops hp l) (fun f hf ↦ ?_)
    (fun f hf a ha ↦ ?_) hDR hOL
  · have := hf.orderly o
    rwa [hs.grade_owner] at this
  · exact hs.frontier_le hf ((StageType.label_faceCell hp a).trans ha.1) ha.2

end VaughtConjecture.H2

namespace VaughtConjecture.OwnerGradeOne

open Finset Label CellScheme StageType FieldAdmission
open SeparatedInstance (omegaAddTwo)
open SeparationObstruction (low low_lt_omegaAddTwo)
open OwnerPartner (high omegaAddTwo_lt_high transformsTo_threeLevel_step)
open scoped Ordinal

/-! ### The display -/

/-- The cells on `Fin 2`, with faces the intervals: `0` of scope `{0}`, `1` of scope `{1}`, `2` of
scope `univ`, all of grade `1`, and `3` of scope `univ` and grade `2`. -/
def cells : CellScheme (Fin 4) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, {1}, univ, univ], ![1, 1, 1, 2]⟩

/-- The value read at a cell: `2` at `0`, `ω + 2` at `1`, `ω·2 + 2` at `2`, `⊥` at `3`. -/
noncomputable def val : Fin 4 → Label.{u} := ![low, omegaAddTwo, high, ⊥]

/-- The rows: the dead cell `3` reads `⊥`; every other cell reads `val`. -/
noncomputable def rowValue (s t : Fin 4) : Label.{u} := if s = 3 then ⊥ else val t

/-- The scheme of the display. -/
noncomputable abbrev S : Scheme.{u} 2 := ⟨4, cells, ⟨fun s d ↦ rowValue s d.1⟩⟩

/-- The labelling `(a, b, c, ⊥)`. -/
noncomputable def lab (a b c : Label.{u}) : Fin 4 → Label.{u} := ![a, b, c, ⊥]

private theorem isSelfVisible_low : IsSelfVisible 1 low.{u} :=
  (isSelfVisible_natCast 2).mpr (by norm_num)

private theorem isSelfVisible_omegaAddTwo : IsSelfVisible 1 omegaAddTwo.{u} :=
  isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega)

private theorem isSelfVisible_high' : IsSelfVisible 1 high.{u} :=
  OwnerPartner.isSelfVisible_high.mono (by omega)

/-- Every cell other than `3` has grade `1`. -/
private theorem grade_eq_one : ∀ d : Fin 4, d ≠ 3 → cells.grade d = 1 := by decide

/-- The cells below a cell other than `3` are among `0`–`2`. -/
private theorem ne_three_of_le : ∀ s d : Fin 4, s ≠ 3 →
    cells.gradedIndex d ≤ cells.gradedIndex s → d ≠ 3 := by decide

/-- **Lawful sections**: `(a, b, c, ⊥)` is lawful for `a ≤ b ≤ c` self-visible at `1`. -/
theorem isLawful_lab {a b c : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hc : IsSelfVisible 1 c) (hab : a ≤ b) (hbc : b ≤ c) : S.{u}.rows.IsLawful (lab a b c) where
  orderly d := by
    fin_cases d
    exacts [ha, hb, hc, isSelfVisible_bot _]
  locality s := by
    by_cases hs : s = 3
    · subst hs
      convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at the dead cell `3`
      change min _ (lab a b c 3) = ⊥
      simp [lab]
    · have hm : IsSelfVisible 1 (lab a b c s) := by
        fin_cases s
        exacts [ha, hb, hc, absurd rfl hs]
      refine transformsTo_threeLevel_step (K := 1)
        (fun d : cells.below (cells.gradedIndex s) ↦ (grade_eq_one d.1
          (ne_three_of_le s d.1 hs d.2)).le) (ha.min hm) (hb.min hm) (hc.min hm)
        (min_le_min_right _ hab) (min_le_min_right _ hbc) fun ⟨d, hd⟩ ↦ ?_
      have hd3 := ne_three_of_le s d hs hd
      right
      -- the row of `s` at `d` is `val d`
      change (rowValue s d = low ∧ _) ∨ (rowValue s d = omegaAddTwo ∧ _) ∨
        (rowValue s d = high ∧ _)
      simp only [rowValue, hs, ite_false]
      fin_cases d
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inr (.inr ⟨rfl, rfl⟩)
      · exact absurd rfl hd3
  availability s t hst hg := by
    have key : ∀ s t : Fin 4, cells.scope s ⊆ cells.scope t → cells.grade s = cells.grade t →
        ∃ u : Fin 4, cells.gradedIndex u = cells.gradedIndex t ∧
          (u = s ∨ (s ≠ 3 ∧ u = 2)) := by decide
    obtain ⟨u, hu, hu'⟩ := key s t hst hg
    refine ⟨u, hu, ?_⟩
    rcases hu' with rfl | ⟨h3, rfl⟩
    · exact le_rfl
    · fin_cases s
      · exact hab.trans hbc
      · exact hbc
      · exact le_rfl
      · exact absurd rfl h3

/-- A lawful section gives lawful labellings below every pair. -/
theorem isLawfulBelow_of_isLawful {w : Fin 4 → Label.{u}} (h : S.{u}.rows.IsLawful w)
    (X : Finset (Fin 2) × ℕ) : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d) :=
  CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d _ ↦ h.orderly d, fun s _ ↦ h.locality s, fun s t _ hst hg ↦ h.availability s t hst hg⟩

/-- **Lawful sections below `(univ, 1)`**, necessary conditions: self-visible at `1` at `0`–`2`,
and `0` at most `1` at most `2`.  Availability puts `0` and `1` below the cell `2`, the only cell
of graded index `(univ, 1)`, which reads `0` below `1`. -/
theorem conditions_univ {w : Fin 4 → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d)) :
    IsSelfVisible 1 (w 0) ∧ IsSelfVisible 1 (w 1) ∧ IsSelfVisible 1 (w 2) ∧ w 0 ≤ w 1 ∧
      w 1 ≤ w 2 := by
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have m : ∀ i : Fin 4, i ≠ 3 → cells.gradedIndex i ≤ ((univ : Finset (Fin 2)), 1) := by decide
  have only2 : ∀ u : Fin 4, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
  have below2 : ∀ i : Fin 4, i ≠ 3 → cells.gradedIndex i ≤ cells.gradedIndex 2 := by decide
  -- availability: every cell `i ≠ 3` lies below the cell `2`
  have hav (i : Fin 4) (hi : i ≠ 3) : w i ≤ w 2 := by
    obtain ⟨u, hu, hle⟩ := ha i 2 (m 2 (by decide)) ((below2 i hi).1) (by
      revert i; decide)
    rwa [only2 u hu] at hle
  -- locality at `2`: the row reads `0` below `1`
  have h01 := (hl 2 (m 2 (by decide))).le_of_le (d := ⟨0, below2 0 (by decide)⟩)
    (d' := ⟨1, below2 1 (by decide)⟩)
    (by
      -- the row of `2` is `val`
      change rowValue 2 0 ≤ rowValue 2 1
      simp only [rowValue, show (2 : Fin 4) ≠ 3 by decide, ite_false]
      exact low_lt_omegaAddTwo.le)
    (by rw [grade_eq_one 1 (by decide), grade_eq_one 0 (by decide)])
  change min (w 0) (w 2) ≤ min (w 1) (w 2) at h01
  rw [min_eq_left (hav 0 (by decide)), min_eq_left (hav 1 (by decide))] at h01
  exact ⟨ho 0 (m 0 (by decide)), ho 1 (m 1 (by decide)), ho 2 (m 2 (by decide)), h01,
    hav 1 (by decide)⟩

/-- A section below `X`, extended by `⊥`, is lawful below `X`. -/
private theorem isLawfulBelow_extendBot {X : Finset (Fin 2) × ℕ} {q : cells.below X → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow X q) :
    S.{u}.rows.IsLawfulBelow X (fun d ↦ CellScheme.Rows.extendBot X q d) := by
  convert hq using 1
  funext d
  exact CellScheme.Rows.extendBot_of_mem q d.2

/-- **The capped lift from `({0}, 1)` to `(univ, 1)`**: the prescription `x` at `0` lifts to
`(x, max b x, max c x, ⊥)`, for `(a, b, c)` the ambient labels. -/
private theorem cappedLift_zero
    (h : (({0} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨-, hv1, hv2, hq01, hq12⟩ := conditions_univ (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  set wp := CellScheme.Rows.extendBot (({0} : Finset (Fin 2)), 1) p
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have m0 : cells.gradedIndex 0 ≤ (({0} : Finset (Fin 2)), 1) := by decide
  have hv0 : IsSelfVisible 1 (wp 0) := by
    rw [← hpw ⟨0, m0⟩]; exact hp.orderly ⟨0, m0⟩
  have hc0 : min (wq 0) c = min (wp 0) c := by
    have := hpq ⟨0, m0⟩; rwa [hqw, hpw] at this
  -- an ambient label at least the one at `0`, raised to the prescription
  have hmax {y : Label.{u}} (hy : wq 0 ≤ y) : min (max y (wp 0)) c = min y c := by
    rw [min_max_distrib_right, ← hc0, max_eq_left (min_le_min_right c hy)]
  refine ⟨fun d ↦ lab (wp 0) (max (wq 1) (wp 0)) (max (wq 2) (wp 0)) d,
    isLawfulBelow_of_isLawful (isLawful_lab hv0 (hv1.max hv0) (hv2.max hv0) (le_max_right _ _)
      (max_le_max hq12 le_rfl)) _, fun ⟨d, hd⟩ ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · exact hc0.symm
    · exact hmax hq01
    · exact hmax (hq01.trans hq12)
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 4, cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) → d = 0 := by
      decide
    obtain rfl := key d hd'
    rw [hpw]
    rfl

/-- **The capped lift from `({1}, 1)` to `(univ, 1)`**: the prescription `y` at `1` lifts to
`(min a y, y, max c y, ⊥)`, for `(a, b, c)` the ambient labels. -/
private theorem cappedLift_one
    (h : (({1} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨hv0, -, hv2, hq01, hq12⟩ := conditions_univ (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  set wp := CellScheme.Rows.extendBot (({1} : Finset (Fin 2)), 1) p
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have m1 : cells.gradedIndex 1 ≤ (({1} : Finset (Fin 2)), 1) := by decide
  have hv1 : IsSelfVisible 1 (wp 1) := by
    rw [← hpw ⟨1, m1⟩]; exact hp.orderly ⟨1, m1⟩
  have hc1 : min (wq 1) c = min (wp 1) c := by
    have := hpq ⟨1, m1⟩; rwa [hqw, hpw] at this
  -- the ambient label at `0`, lowered to the prescription
  have hmin : min (min (wq 0) (wp 1)) c = min (wq 0) c := by
    rw [inf_inf_distrib_right, ← hc1, min_eq_left (min_le_min_right c hq01)]
  -- the ambient label at `2`, raised to the prescription
  have hmax : min (max (wq 2) (wp 1)) c = min (wq 2) c := by
    rw [min_max_distrib_right, ← hc1, max_eq_left (min_le_min_right c hq12)]
  refine ⟨fun d ↦ lab (min (wq 0) (wp 1)) (wp 1) (max (wq 2) (wp 1)) d,
    isLawfulBelow_of_isLawful (isLawful_lab (hv0.min hv1) hv1 (hv2.max hv1) (min_le_right _ _)
      (le_max_right _ _)) _, fun ⟨d, hd⟩ ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · exact hmin
    · exact hc1.symm
    · exact hmax
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 4, cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) → d = 1 := by
      decide
    obtain rfl := key d hd'
    rw [hpw]
    rfl

/-- **The scheme of the display is legal.** -/
theorem isLegal_S : S.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 4, cells.scope d ∈ cells.faces ∧ 0 < cells.grade d ∧
        cells.grade d ≤ #(cells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := by
    have key : ∀ s d : Fin 4, rowValue.{u} s d = ⊥ ∨ rowValue.{u} s d = low ∨
        rowValue.{u} s d = omegaAddTwo ∨ rowValue.{u} s d = high := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [rowValue, val]
    -- the rows of `S` are `rowValue`
    change rowValue s t.1 < _
    rcases key s t.1 with h | h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 2, by simp [low]⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨2, 2, by simp [high]⟩)
  isConsistent s := by
    by_cases hs : s = 3
    · subst hs
      have hrow : S.{u}.rows.row 3 = fun _ ↦ ⊥ := by
        funext d
        -- the row of the dead cell is `⊥`
        change rowValue 3 d.1 = ⊥
        simp [rowValue]
      -- consistency at `3` is lawfulness of its row below its graded index
      change S.{u}.rows.IsLawfulBelow (cells.gradedIndex 3) (S.{u}.rows.row 3)
      rw [hrow]
      exact CellScheme.Rows.isLawfulBelow_const_bot _
    · have hrow : S.{u}.rows.row s = fun d ↦ lab low omegaAddTwo high d.1 := by
        funext ⟨d, hd⟩
        have hd3 := ne_three_of_le s d hs hd
        -- the row of `s` at `d` is `val d`
        change rowValue s d = _
        simp only [rowValue, hs, ite_false]
        fin_cases d <;> simp_all [val, lab]
      -- consistency at `s` is lawfulness of its row below its graded index
      change S.{u}.rows.IsLawfulBelow (cells.gradedIndex s) (S.{u}.rows.row s)
      rw [hrow]
      exact isLawfulBelow_of_isLawful (isLawful_lab isSelfVisible_low isSelfVisible_omegaAddTwo
        isSelfVisible_high' low_lt_omegaAddTwo.le omegaAddTwo_lt_high.le) _
  isBountiful := by
    refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    obtain ⟨B, j⟩ := X
    obtain ⟨C, k⟩ := Y
    obtain ⟨-, hj0, hjB⟩ := hX
    obtain ⟨hBC, -⟩ := h
    have key : ∀ B C : Finset (Fin 2), B ⊆ C → B ≠ ∅ →
        B = C ∨ (B = {0} ∧ C = Finset.univ) ∨ (B = {1} ∧ C = Finset.univ) := by decide
    have hB : B ≠ ∅ := by
      rintro rfl
      simp at hjB
      omega
    rcases key B C hBC hB with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact CellScheme.Rows.cappedLift_of_fst_eq _ rfl
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_zero _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_one _
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨-, hj0, hjB⟩ := hX
    have hj2 : j ≤ 2 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 2), ∀ j : Fin 3, 0 < (j : ℕ) → (j : ℕ) ≤ #B →
        ∃ d : Fin 4, cells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B ⟨j, by omega⟩ hj0 hjB

/-! ### The context -/

/-- **The context**: the scheme `S` labelled `⊥` at the cell `0` of the root face, `⊤` at the
cells `1` and `2`, and `⊥` at the dead cell. -/
noncomputable def ctx (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊥ ⊤ ⊤
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_bot 1) (isSelfVisible_top 1) (isSelfVisible_top 1)
    bot_le le_rfl
  atStage d := by fin_cases d <;> simp [lab]

/-- The cells of the context, by their index. -/
abbrev cellC (α : Ordinal.{u}) (i : Fin 4) : Fin (ctx α).card := i

/-- **The context is legal.** -/
theorem isLegal_ctx (α : Ordinal.{u}) : (ctx α).IsLegal := isLegal_S

/-- The face `{0}` is a face of the context. -/
theorem mem_faces_castSuccEmb (α : Ordinal.{u}) :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (ctx α).toCellScheme.faces := by
  -- the faces of the context are the interval plan
  change _ ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The root face of the context: its face on `{0}`, the cell `0`. -/
noncomputable def face (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (ctx α).comap Fin.castSuccEmb (mem_faces_castSuccEmb α)

theorem restrictFace_ctx (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (ctx α) = some (face α) := restrictFace_of_mem _ _ _

/-- The row of the context at two of the cells `0`–`2`. -/
private theorem rowAt_ctx (α : Ordinal.{u}) (s d : Fin 4) (hs : s ≠ 3)
    (hd : cells.gradedIndex d ≤ cells.gradedIndex s) :
    (ctx α).rowAt (cellC α s) (cellC α d) = val d := by
  rw [Scheme.rowAt_of_mem (show cellC α d ∈ (ctx α).toCellScheme.below
    ((ctx α).toCellScheme.gradedIndex (cellC α s)) from hd)]
  -- the rows of the context are `rowValue`
  change rowValue s d = _
  simp [rowValue, hs]

/-- **The context is a source-gap context of grade `1`** along every root on the point `0`, with
lost point `1`, owner the cell `2` and lost top the cell `1`. -/
theorem isSourceGapContextAt_ctx (α : Ordinal.{u}) {n : ℕ} (g : Fin n ↪ Fin 1) :
    (ctx α).IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) 1 (cellC α 2) (cellC α 1) where
  notMem_range := by
    rintro ⟨i, hi⟩
    exact (Fin.castSucc_lt_last (g i)).ne hi
  topGrade_eq := by
    refine le_antisymm (topGrade_le_iff.mpr
      (show ∀ d : Fin 4, lab ⊥ ⊤ ⊤ d = ⊤ → cells.grade d ≤ 1 from fun d hd ↦ ?_)) ?_
    · -- the cells labelled `⊤` are `1` and `2`, of grade `1`
      by_cases hd3 : d = 3
      · subst hd3
        simp [lab] at hd
      · exact (grade_eq_one d hd3).le
    · exact grade_le_topGrade (t := ctx α) (d := cellC α 2) rfl
  scope_owner := rfl
  grade_owner := rfl
  label_owner := rfl
  label_lost := rfl
  mem_scope_lost := by
    change (1 : Fin 2) ∈ cells.scope 1
    decide
  gap_owner := by
    rw [rowAt_ctx α 2 1 (by decide) (by decide), rowAt_ctx α 2 2 (by decide) le_rfl]
    change visibilityReplace 1 1 omegaAddTwo < high
    rw [isSelfVisible_omegaAddTwo]
    exact omegaAddTwo_lt_high
  gap_retained a ha hla := by
    -- every cell labelled `⊤` contains the lost point
    change lab ⊥ ⊤ ⊤ a = ⊤ at ha
    change (1 : Fin 2) ∉ cells.scope a at hla
    have key : ∀ a : Fin 4, (1 : Fin 2) ∉ cells.scope a → a = 0 := by decide
    obtain rfl := key a hla
    simp [lab] at ha

/-! ### The refutation -/

/-- The owner `2` is the only cell of its graded index `(univ, 1)`. -/
theorem eq_two_of_gradedIndex (α : Ordinal.{u}) (u : Fin (ctx α).card)
    (hu : (ctx α).toCellScheme.gradedIndex u = (ctx α).toCellScheme.gradedIndex (cellC α 2)) :
    u = cellC α 2 := by
  have key : ∀ u : Fin 4, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
  exact key u hu

/-- **Owner lowering at the grade `1` fails at the context for every legal donor** with the same
root face: the root face `(1)` at the cell `0` (labelled `⊥` in the context) is lawful, so it
extends to a lawful donor face (bountifulness at the cap `⊥`); at the cap `⊥` it agrees on the root
with every context face, and its value `1` at the cell `0` is above the cap
(`H2.not_ownerLowering_one_of_label_ne_top`). -/
theorem not_ownerLowering_one (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {m : ℕ} {tb : StageType.{u} α m}
    (htb : tb.IsLegal) {gb : Fin 1 ↪ Fin m} (htbp : restrictFace gb tb = some p) :
    ¬ OwnerLowering (faceCell hp) (faceCell htbp) (cellC α 2) (cellC α 1) 1
      (ctx α).rows.IsLawful tb.rows.IsLawful := by
  have h1 : IsSelfVisible 1 (1 : Label.{u}) := isSelfVisible_one.mpr le_rfl
  have hL : (ctx α).rows.IsLawful (lab 1 1 1) := isLawful_lab h1 h1 h1 le_rfl le_rfl
  obtain ⟨G, hG, hGr⟩ := exists_isLawful_extend_of_restrictFace htb htbp
    (isLawful_comp_faceCell hp hL)
  obtain ⟨z, hz⟩ := exists_faceCell_eq_of_last_notMem hp (s := cellC α 0) (by
    change Fin.last 1 ∉ cells.scope 0
    decide)
  refine H2.not_ownerLowering_one_of_label_ne_top (isSourceGapContextAt_ctx α
    (Function.Embedding.refl (Fin 1))) (eq_two_of_gradedIndex α) hp htbp (i := z)
    ?_ ?_ (isSelfVisible_bot 1) hL hG (fun _ ↦ by simp) ?_
  · rw [← label_faceCell hp, hz]
    simp [ctx, lab]
  · rw [← grade_faceCell hp, hz]
    rfl
  · rw [hGr z, hz]
    simp [lab]

/-- **Owner lowering at the grade `1` is not a consequence of legality and the source-gap
clauses**: there are a legal stage type `t'` on two points, a source-gap context of grade `1` in
it along a root on the point `0`, and its face `p` on `{0}`, with owner lowering at the grade `1`
false for every legal donor with root face `p` (the donor `t'` among them). -/
theorem exists_not_ownerLowering_one (α : Ordinal.{u}) :
    ∃ (t' : StageType.{u} α 2) (o r : Fin t'.card) (p : StageType.{u} α 1)
      (hp : restrictFace Fin.castSuccEmb t' = some p), t'.IsLegal ∧
      t'.IsSourceGapContextAt 1 ((Function.Embedding.refl (Fin 1)).trans Fin.castSuccEmb) 1 o r ∧
      ∀ {m : ℕ} {tb : StageType.{u} α m}, tb.IsLegal → ∀ {gb : Fin 1 ↪ Fin m}
        (htbp : restrictFace gb tb = some p),
        ¬ OwnerLowering (faceCell hp) (faceCell htbp) o r 1 t'.rows.IsLawful tb.rows.IsLawful :=
  ⟨ctx α, cellC α 2, cellC α 1, face α, restrictFace_ctx α, isLegal_ctx α,
    isSourceGapContextAt_ctx α _, fun htb _ htbp ↦ not_ownerLowering_one α _ htb htbp⟩

/-! ### The clause is still an admission at the context -/

/-- The dead cell `3` is `⊥` in every lawful labelling. -/
theorem eq_bot_three {w : Fin 4 → Label.{u}} (hw : S.{u}.rows.IsLawful w) : w 3 = ⊥ :=
  hw.eq_bot_of_row_self_eq_bot 3 (by
    -- the row of the dead cell is `⊥`
    change rowValue 3 3 = ⊥
    simp [rowValue])

/-- The face on `{0}` is the cell `0`. -/
theorem faceCell_eq_zero (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) (x : Fin p.card) :
    faceCell hp x = cellC α 0 := by
  have key : ∀ d : Fin 4, Fin.last 1 ∉ cells.scope d → d = 0 := by decide
  exact key _ (last_notMem_scope_faceCell hp x)

/-- **Owner lowering below the designated tops holds at the context** with the context itself as
donor, for the designated tops among the cells `1` and `2`: the lowered face is
`(y, max (min b h) y, max (min c h) y, ⊥)` for `y` the root value of the donor face and `(a, b, c)`
the context face, with frontier at most `max h y`, and `y` is at most every top of the donor
face. -/
theorem ownerLoweringBelow_ctx (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) (Lo : Finset (Fin (ctx α).card))
    {Tops : Finset (Fin (ctx α).card)} (hTops : ∀ t ∈ Tops, t = cellC α 1 ∨ t = cellC α 2) :
    H2.OwnerLoweringBelow (faceCell hp) (faceCell hp) (cellC α 2) (cellC α 1) 1
      (ctx α).rows.IsLawful (ctx α).rows.IsLawful Lo Tops := by
  intro h hh L g hL hg hroot
  obtain ⟨-, hL1, hL2, hL01, hL12⟩ := conditions_univ (isLawfulBelow_of_isLawful hL _)
  obtain ⟨hg0, -, -, hg01, hg12⟩ := conditions_univ (isLawfulBelow_of_isLawful hg _)
  obtain ⟨z, hz⟩ := exists_faceCell_eq_of_last_notMem hp (s := cellC α 0) (by
    change Fin.last 1 ∉ cells.scope 0
    decide)
  have h0 : min (g (cellC α 0)) h = min (L (cellC α 0)) h := by
    have := hroot z
    rwa [hz] at this
  -- a context label at least the one at `0`, capped at `h` and raised to the root value
  have hraise {v : Label.{u}} (hv : L (cellC α 0) ≤ v) :
      min (max (min v h) (g (cellC α 0))) h = min v h := by
    rw [min_max_distrib_right, min_assoc, min_self, h0, max_eq_left (min_le_min_right h hv)]
  refine ⟨lab (g (cellC α 0)) (max (min (L (cellC α 1)) h) (g (cellC α 0)))
      (max (min (L (cellC α 2)) h) (g (cellC α 0))),
    isLawful_lab hg0 ((hL1.min hh).max hg0) ((hL2.min hh).max hg0) (le_max_right _ _)
      (max_le_max (min_le_min_right _ hL12) le_rfl), fun x ↦ ?_, fun d ↦ ?_, fun t ht hht _ ↦ ?_⟩
  · rw [faceCell_eq_zero α hp x]
    rfl
  · have key : ∀ d : Fin 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
    rcases key d with rfl | rfl | rfl | rfl
    · exact h0
    · exact hraise hL01
    · exact hraise (hL01.trans hL12)
    · change min ⊥ h = min (L (cellC α 3)) h
      rw [eq_bot_three hL]
  · have hgt : g (cellC α 0) ≤ g t := by
      rcases hTops t ht with rfl | rfl
      exacts [hg01, hg01.trans hg12]
    exact (min_le_left _ _).trans (max_le ((min_le_right _ _).trans hht) hgt)

/-- The raised donor label: `max (max (min y h) x) (c if h ≤ y)`. -/
private noncomputable def raise (h c x y : Label.{u}) : Label.{u} :=
  max (max (min y h) x) (if h ≤ y then c else ⊥)

private theorem raise_cap {h c x y y₀ : Label.{u}} (hy : y₀ ≤ y)
    (h0 : min x h = min y₀ h) : min (raise h c x y) h = min y h := by
  unfold raise
  split_ifs with hhy
  · rw [min_eq_right hhy, min_eq_right]
    exact (min_eq_right hhy ▸ le_max_left (min y h) x).trans (le_max_left _ _)
  · have hyh : y < h := not_le.mp hhy
    have hx : x = y₀ := Label.eq_of_min_eq_of_lt h0.symm (hy.trans_lt hyh)
    have hmin : min y h = y := min_eq_left hyh.le
    rw [max_bot_right, hx, hmin, max_eq_left hy, hmin]

private theorem raise_mono {h c x y y' : Label.{u}} (hy : y ≤ y') :
    raise h c x y ≤ raise h c x y' := by
  unfold raise
  refine max_le_max (max_le_max (min_le_min_right _ hy) le_rfl) ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hy) h2
  · exact bot_le
  · exact le_rfl

private theorem isSelfVisible_raise {h c x y : Label.{u}} (hh : IsSelfVisible 1 h)
    (hc : IsSelfVisible 1 c) (hx : IsSelfVisible 1 x) (hy : IsSelfVisible 1 y) :
    IsSelfVisible 1 (raise h c x y) := by
  unfold raise
  refine ((hy.min hh).max hx).max ?_
  split_ifs
  exacts [hc, isSelfVisible_bot _]

/-- **Donor raising holds at the context** with the context itself as donor, for the designated
tops among the cells `1` and `2` and every set of root cells: the raised donor face is
`(x, raise b, raise c, ⊥)` for `x` the root value of the context face and `(a, b, c)` the donor
face, where `raise y = max (max (min y h) x) (c if h ≤ y)`. -/
theorem donorRaising_ctx (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) (A : Set (Fin p.card))
    {Tops : Finset (Fin (ctx α).card)} (hTops : ∀ t ∈ Tops, t = cellC α 1 ∨ t = cellC α 2) :
    DonorRaising (faceCell hp) (faceCell hp) 1 (ctx α).rows.IsLawful (ctx α).rows.IsLawful A
      Tops := by
  intro h c hh hc R f hR hf hroot _
  obtain ⟨-, hR1, hR2, hR01, hR12⟩ := conditions_univ (isLawfulBelow_of_isLawful hR _)
  obtain ⟨hf0, -, -, -, -⟩ := conditions_univ (isLawfulBelow_of_isLawful hf _)
  obtain ⟨z, hz⟩ := exists_faceCell_eq_of_last_notMem hp (s := cellC α 0) (by
    change Fin.last 1 ∉ cells.scope 0
    decide)
  have h0 : min (f (cellC α 0)) h = min (R (cellC α 0)) h := by
    have := hroot z
    rwa [hz] at this
  set x := f (cellC α 0)
  refine ⟨lab x (raise h c x (R (cellC α 1))) (raise h c x (R (cellC α 2))),
    isLawful_lab hf0 (isSelfVisible_raise hh hc hf0 hR1) (isSelfVisible_raise hh hc hf0 hR2)
      ((le_max_right _ _).trans (le_max_left _ _)) (raise_mono hR12), fun y ↦ ?_, fun d ↦ ?_,
    fun t ht hht ↦ ?_⟩
  · rw [faceCell_eq_zero α hp y]
    rfl
  · have key : ∀ d : Fin 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
    rcases key d with rfl | rfl | rfl | rfl
    · exact h0
    · exact raise_cap hR01 h0
    · exact raise_cap (hR01.trans hR12) h0
    · change min ⊥ h = min (R (cellC α 3)) h
      rw [eq_bot_three hR]
  · have hc' (y : Label.{u}) (hy : h ≤ y) : c ≤ raise h c x y := by
      unfold raise
      split_ifs
      exact le_max_right _ _
    rcases hTops t ht with rfl | rfl
    exacts [hc' _ hht, hc' _ hht]

/-- **The clause is an admission of states at the context** with the context itself as donor, for
every designation with the designated tops among the cells `1` and `2`
(`H2.stateAdmission_one_of_below`), although owner lowering at the grade `1` fails there
(`OwnerGradeOne.not_ownerLowering_one`). -/
theorem isStateAdmission_ctx (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {Lo Tops : Finset (Fin (ctx α).card)}
    (hTops : ∀ t ∈ Tops, t = cellC α 1 ∨ t = cellC α 2) :
    H2.IsStateAdmission (faceCell hp) (faceCell hp) 1 (ctx α).rows.IsLawful
      (ctx α).rows.IsLawful (H2.SelfLowG (cellC α 2) (cellC α 1) 1 Lo Tops) :=
  H2.stateAdmission_one_of_below (isSourceGapContextAt_ctx α (Function.Embedding.refl _)) hp hp
    (H2.donorRaisingGap_of_V (H2.donorRaisingV_of (donorRaising_ctx α hp _ hTops)))
    (ownerLoweringBelow_ctx α hp Lo hTops)

end VaughtConjecture.OwnerGradeOne

/-! ### A context where the clause is not an admission at grade `1` -/

namespace VaughtConjecture.OwnerGradeOneTop

open Finset Label CellScheme StageType FieldAdmission
open SeparatedInstance (omegaAddTwo)
open SeparationObstruction (low low_lt_omegaAddTwo)
open OwnerPartner (high omegaAddTwo_lt_high transformsTo_threeLevel_step)
open OwnerGradeOne (cells)
open scoped Ordinal

/-- The value read at a cell of grade `1`: `ω + 2` at `0`, `2` at `1`, `ω·2 + 2` at `2`. -/
noncomputable def val : Fin 4 → Label.{u} := ![omegaAddTwo, low, high, ⊥]

/-- The rows: the cell `3` of grade `2` reads every cell at `2`; every other cell reads `val`. -/
noncomputable def rowValue (s t : Fin 4) : Label.{u} := if s = 3 then low else val t

/-- The scheme of the display. -/
noncomputable abbrev S : Scheme.{u} 2 := ⟨4, cells, ⟨fun s d ↦ rowValue s d.1⟩⟩

/-- The labelling `(x, y, z, w)`. -/
noncomputable def lab (x y z w : Label.{u}) : Fin 4 → Label.{u} := ![x, y, z, w]

private theorem isSelfVisible_low (k : ℕ) (hk : k ≤ 2) : IsSelfVisible k low.{u} :=
  (isSelfVisible_natCast 2).mpr hk

private theorem isSelfVisible_omegaAddTwo : IsSelfVisible 1 omegaAddTwo.{u} :=
  isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega)

private theorem isSelfVisible_high' : IsSelfVisible 1 high.{u} :=
  OwnerPartner.isSelfVisible_high.mono (by omega)

private theorem grade_eq_one : ∀ d : Fin 4, d ≠ 3 → cells.grade d = 1 := by decide

private theorem ne_three_of_le : ∀ s d : Fin 4, s ≠ 3 →
    cells.gradedIndex d ≤ cells.gradedIndex s → d ≠ 3 := by decide

/-- **Lawful sections**: `(x, y, z, w)` is lawful for `w ≤ y ≤ x ≤ z`, with `x`, `y`, `z`
self-visible at `1` and `w` at `2`. -/
theorem isLawful_lab {x y z w : Label.{u}} (hx : IsSelfVisible 1 x) (hy : IsSelfVisible 1 y)
    (hz : IsSelfVisible 1 z) (hw : IsSelfVisible 2 w) (hwy : w ≤ y) (hyx : y ≤ x)
    (hxz : x ≤ z) : S.{u}.rows.IsLawful (lab x y z w) where
  orderly d := by
    fin_cases d
    exacts [hx, hy, hz, hw]
  locality s := by
    by_cases hs : s = 3
    · subst hs
      refine transformsTo_threeLevel_step (K := 2) (a := w) (b := w) (c := w)
        (fun d : cells.below (cells.gradedIndex 3) ↦ d.2.2) hw hw hw le_rfl le_rfl
        fun ⟨d, hd⟩ ↦ ?_
      right; left
      -- the row of `3` reads `2` everywhere, and `w` is below every label
      refine ⟨by simp [rowValue], ?_⟩
      change min (lab x y z w d) (lab x y z w 3) = w
      have key : ∀ d : Fin 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
      rcases key d with rfl | rfl | rfl | rfl
      · exact min_eq_right (hwy.trans hyx)
      · exact min_eq_right hwy
      · exact min_eq_right (hwy.trans (hyx.trans hxz))
      · exact min_self _
    · have hm : IsSelfVisible 1 (lab x y z w s) := by
        fin_cases s
        exacts [hx, hy, hz, absurd rfl hs]
      refine transformsTo_threeLevel_step (K := 1)
        (fun d : cells.below (cells.gradedIndex s) ↦ (grade_eq_one d.1
          (ne_three_of_le s d.1 hs d.2)).le) (hy.min hm) (hx.min hm) (hz.min hm)
        (min_le_min_right _ hyx) (min_le_min_right _ hxz) fun ⟨d, hd⟩ ↦ ?_
      have hd3 := ne_three_of_le s d hs hd
      right
      -- the row of `s` at `d` is `val d`
      change (rowValue s d = low ∧ _) ∨ (rowValue s d = omegaAddTwo ∧ _) ∨
        (rowValue s d = high ∧ _)
      simp only [rowValue, hs, ite_false]
      fin_cases d
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr (.inr ⟨rfl, rfl⟩)
      · exact absurd rfl hd3
  availability s t hst hg := by
    have key : ∀ s t : Fin 4, cells.scope s ⊆ cells.scope t → cells.grade s = cells.grade t →
        ∃ u : Fin 4, cells.gradedIndex u = cells.gradedIndex t ∧
          (u = s ∨ (s ≠ 3 ∧ u = 2)) := by decide
    obtain ⟨u, hu, hu'⟩ := key s t hst hg
    refine ⟨u, hu, ?_⟩
    rcases hu' with rfl | ⟨h3, rfl⟩
    · exact le_rfl
    · fin_cases s
      · exact hxz
      · exact hyx.trans hxz
      · exact le_rfl
      · exact absurd rfl h3

/-- A lawful section gives lawful labellings below every pair. -/
theorem isLawfulBelow_of_isLawful {w : Fin 4 → Label.{u}} (h : S.{u}.rows.IsLawful w)
    (X : Finset (Fin 2) × ℕ) : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d) :=
  CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d _ ↦ h.orderly d, fun s _ ↦ h.locality s, fun s t _ hst hg ↦ h.availability s t hst hg⟩

/-- **Lawful sections below `(univ, 1)`**, necessary conditions: self-visible at `1` at `0`–`2`,
and `1` at most `0` at most `2` (availability at the only cell `2` of graded index `(univ, 1)`,
which reads `1` below `0`). -/
theorem conditions_univ {w : Fin 4 → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d)) :
    IsSelfVisible 1 (w 0) ∧ IsSelfVisible 1 (w 1) ∧ IsSelfVisible 1 (w 2) ∧ w 1 ≤ w 0 ∧
      w 0 ≤ w 2 := by
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have m : ∀ i : Fin 4, i ≠ 3 → cells.gradedIndex i ≤ ((univ : Finset (Fin 2)), 1) := by decide
  have only2 : ∀ u : Fin 4, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
  have below2 : ∀ i : Fin 4, i ≠ 3 → cells.gradedIndex i ≤ cells.gradedIndex 2 := by decide
  have hav (i : Fin 4) (hi : i ≠ 3) : w i ≤ w 2 := by
    obtain ⟨u, hu, hle⟩ := ha i 2 (m 2 (by decide)) ((below2 i hi).1) (by
      revert i; decide)
    rwa [only2 u hu] at hle
  have h10 := (hl 2 (m 2 (by decide))).le_of_le (d := ⟨1, below2 1 (by decide)⟩)
    (d' := ⟨0, below2 0 (by decide)⟩)
    (by
      -- the row of `2` is `val`
      change rowValue 2 1 ≤ rowValue 2 0
      simp only [rowValue, show (2 : Fin 4) ≠ 3 by decide, ite_false]
      exact low_lt_omegaAddTwo.le)
    (by rw [grade_eq_one 1 (by decide), grade_eq_one 0 (by decide)])
  change min (w 1) (w 2) ≤ min (w 0) (w 2) at h10
  rw [min_eq_left (hav 1 (by decide)), min_eq_left (hav 0 (by decide))] at h10
  exact ⟨ho 0 (m 0 (by decide)), ho 1 (m 1 (by decide)), ho 2 (m 2 (by decide)), h10,
    hav 0 (by decide)⟩

/-- **The cell `3` lies below the cell `1`** in every lawful labelling: its row reads both at `2`,
and the grade of `1` is below that of `3`. -/
theorem le_one_of_isLawful {w : Fin 4 → Label.{u}} (hw : S.{u}.rows.IsLawful w) : w 3 ≤ w 1 := by
  have h := (hw.locality 3).le_of_le
    (d := ⟨3, cells.mem_below_gradedIndex 3⟩)
    (d' := ⟨1, show cells.gradedIndex 1 ≤ cells.gradedIndex 3 by decide⟩)
    (by
      -- the row of `3` is constantly `2`
      change rowValue 3 3 ≤ rowValue 3 1
      simp [rowValue])
    (by decide)
  change min (w 3) (w 3) ≤ min (w 1) (w 3) at h
  rw [min_self] at h
  exact h.trans (min_le_left _ _)

/-- A section below `X`, extended by `⊥`, is lawful below `X`. -/
private theorem isLawfulBelow_extendBot {X : Finset (Fin 2) × ℕ} {q : cells.below X → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow X q) :
    S.{u}.rows.IsLawfulBelow X (fun d ↦ CellScheme.Rows.extendBot X q d) := by
  convert hq using 1
  funext d
  exact CellScheme.Rows.extendBot_of_mem q d.2

/-- **The capped lift from `({0}, 1)` to `(univ, 1)`**: the prescription `x` at `0` lifts to
`(x, min b x, max c x, ⊥)`, for `(a, b, c)` the ambient labels. -/
private theorem cappedLift_zero
    (h : (({0} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨-, hv1, hv2, hq10, hq02⟩ := conditions_univ (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  set wp := CellScheme.Rows.extendBot (({0} : Finset (Fin 2)), 1) p
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have m0 : cells.gradedIndex 0 ≤ (({0} : Finset (Fin 2)), 1) := by decide
  have hv0 : IsSelfVisible 1 (wp 0) := by
    rw [← hpw ⟨0, m0⟩]; exact hp.orderly ⟨0, m0⟩
  have hc0 : min (wq 0) c = min (wp 0) c := by
    have := hpq ⟨0, m0⟩; rwa [hqw, hpw] at this
  refine ⟨fun d ↦ lab (wp 0) (min (wq 1) (wp 0)) (max (wq 2) (wp 0)) ⊥ d,
    isLawfulBelow_of_isLawful (isLawful_lab hv0 (hv1.min hv0) (hv2.max hv0) (isSelfVisible_bot _)
      bot_le (min_le_right _ _) (le_max_right _ _)) _, fun ⟨d, hd⟩ ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · exact hc0.symm
    · change min (min (wq 1) (wp 0)) c = min (wq 1) c
      rw [inf_inf_distrib_right, ← hc0, min_eq_left (min_le_min_right c hq10)]
    · change min (max (wq 2) (wp 0)) c = min (wq 2) c
      rw [min_max_distrib_right, ← hc0, max_eq_left (min_le_min_right c hq02)]
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 4, cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) → d = 0 := by
      decide
    obtain rfl := key d hd'
    rw [hpw]
    rfl

/-- **The capped lift from `({1}, 1)` to `(univ, 1)`**: the prescription `y` at `1` lifts to
`(max a y, y, max c y, ⊥)`, for `(a, b, c)` the ambient labels. -/
private theorem cappedLift_one
    (h : (({1} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨hv0, -, hv2, hq10, hq02⟩ := conditions_univ (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  set wp := CellScheme.Rows.extendBot (({1} : Finset (Fin 2)), 1) p
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have m1 : cells.gradedIndex 1 ≤ (({1} : Finset (Fin 2)), 1) := by decide
  have hv1 : IsSelfVisible 1 (wp 1) := by
    rw [← hpw ⟨1, m1⟩]; exact hp.orderly ⟨1, m1⟩
  have hc1 : min (wq 1) c = min (wp 1) c := by
    have := hpq ⟨1, m1⟩; rwa [hqw, hpw] at this
  refine ⟨fun d ↦ lab (max (wq 0) (wp 1)) (wp 1) (max (wq 2) (wp 1)) ⊥ d,
    isLawfulBelow_of_isLawful (isLawful_lab (hv0.max hv1) hv1 (hv2.max hv1) (isSelfVisible_bot _)
      bot_le (le_max_right _ _) (max_le_max hq02 le_rfl)) _, fun ⟨d, hd⟩ ↦ ?_,
    fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · change min (max (wq 0) (wp 1)) c = min (wq 0) c
      rw [min_max_distrib_right, ← hc1, max_eq_left (min_le_min_right c hq10)]
    · exact hc1.symm
    · change min (max (wq 2) (wp 1)) c = min (wq 2) c
      rw [min_max_distrib_right, ← hc1, max_eq_left (min_le_min_right c (hq10.trans hq02))]
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 4, cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) → d = 1 := by
      decide
    obtain rfl := key d hd'
    rw [hpw]
    rfl

/-- **The scheme of the display is legal.** -/
theorem isLegal_S : S.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 4, cells.scope d ∈ cells.faces ∧ 0 < cells.grade d ∧
        cells.grade d ≤ #(cells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := by
    have key : ∀ s d : Fin 4, rowValue.{u} s d = ⊥ ∨ rowValue.{u} s d = low ∨
        rowValue.{u} s d = omegaAddTwo ∨ rowValue.{u} s d = high := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [rowValue, val]
    -- the rows of `S` are `rowValue`
    change rowValue s t.1 < _
    rcases key s t.1 with h | h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 2, by simp [low]⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨2, 2, by simp [high]⟩)
  isConsistent s := by
    by_cases hs : s = 3
    · subst hs
      have hrow : S.{u}.rows.row 3 = fun d ↦ lab low low low low d.1 := by
        funext ⟨d, hd⟩
        -- the row of `3` is constantly `2`
        change rowValue 3 d = _
        fin_cases d <;> simp [rowValue, lab]
      change S.{u}.rows.IsLawfulBelow (cells.gradedIndex 3) (S.{u}.rows.row 3)
      rw [hrow]
      exact isLawfulBelow_of_isLawful (isLawful_lab (isSelfVisible_low 1 (by omega))
        (isSelfVisible_low 1 (by omega)) (isSelfVisible_low 1 (by omega))
        (isSelfVisible_low 2 le_rfl) le_rfl le_rfl le_rfl) _
    · have hrow : S.{u}.rows.row s = fun d ↦ lab omegaAddTwo low high ⊥ d.1 := by
        funext ⟨d, hd⟩
        have hd3 := ne_three_of_le s d hs hd
        -- the row of `s` at `d` is `val d`
        change rowValue s d = _
        simp only [rowValue, hs, ite_false]
        fin_cases d <;> simp_all [val, lab]
      change S.{u}.rows.IsLawfulBelow (cells.gradedIndex s) (S.{u}.rows.row s)
      rw [hrow]
      exact isLawfulBelow_of_isLawful (isLawful_lab isSelfVisible_omegaAddTwo
        (isSelfVisible_low 1 (by omega)) isSelfVisible_high' (isSelfVisible_bot _) bot_le
        low_lt_omegaAddTwo.le omegaAddTwo_lt_high.le) _
  isBountiful := by
    refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    obtain ⟨B, j⟩ := X
    obtain ⟨C, k⟩ := Y
    obtain ⟨-, hj0, hjB⟩ := hX
    obtain ⟨hBC, -⟩ := h
    have key : ∀ B C : Finset (Fin 2), B ⊆ C → B ≠ ∅ →
        B = C ∨ (B = {0} ∧ C = Finset.univ) ∨ (B = {1} ∧ C = Finset.univ) := by decide
    have hB : B ≠ ∅ := by
      rintro rfl
      simp at hjB
      omega
    rcases key B C hBC hB with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact CellScheme.Rows.cappedLift_of_fst_eq _ rfl
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_zero _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_one _
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨-, hj0, hjB⟩ := hX
    have hj2 : j ≤ 2 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 2), ∀ j : Fin 3, 0 < (j : ℕ) → (j : ℕ) ≤ #B →
        ∃ d : Fin 4, cells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B ⟨j, by omega⟩ hj0 hjB

/-! #### The context -/

/-- **The context**: the scheme `S` labelled `⊤` at the cells `0`–`2` (the root cell `0` among
them) and `⊥` at the cell `3` of grade `2`. -/
noncomputable def ctx (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊤ ⊤ ⊤ ⊥
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_top 1) (isSelfVisible_top 1) (isSelfVisible_top 1)
    (isSelfVisible_bot 2) bot_le le_rfl le_rfl
  atStage d := by fin_cases d <;> simp [lab]

/-- The cells of the context, by their index. -/
abbrev cellC (α : Ordinal.{u}) (i : Fin 4) : Fin (ctx α).card := i

/-- **The context is legal.** -/
theorem isLegal_ctx (α : Ordinal.{u}) : (ctx α).IsLegal := isLegal_S

/-- The face `{0}` is a face of the context. -/
theorem mem_faces_castSuccEmb (α : Ordinal.{u}) :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (ctx α).toCellScheme.faces := by
  -- the faces of the context are the interval plan
  change _ ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The root face of the context: its face on `{0}`, the cell `0`. -/
noncomputable def face (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (ctx α).comap Fin.castSuccEmb (mem_faces_castSuccEmb α)

theorem restrictFace_ctx (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (ctx α) = some (face α) := restrictFace_of_mem _ _ _

/-- The row of the context at two of the cells `0`–`2`. -/
private theorem rowAt_ctx (α : Ordinal.{u}) (s d : Fin 4) (hs : s ≠ 3)
    (hd : cells.gradedIndex d ≤ cells.gradedIndex s) :
    (ctx α).rowAt (cellC α s) (cellC α d) = val d := by
  rw [Scheme.rowAt_of_mem (show cellC α d ∈ (ctx α).toCellScheme.below
    ((ctx α).toCellScheme.gradedIndex (cellC α s)) from hd)]
  -- the rows of the context are `rowValue`
  change rowValue s d = _
  simp [rowValue, hs]

/-- **The context is a source-gap context of grade `1`** along every root on the point `0`, with
lost point `1`, owner the cell `2` and lost top the cell `1`: the owner reads the lost top at `2`,
the root top `0` at `ω + 2` and itself at `ω·2 + 2`. -/
theorem isSourceGapContextAt_ctx (α : Ordinal.{u}) {n : ℕ} (g : Fin n ↪ Fin 1) :
    (ctx α).IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) 1 (cellC α 2) (cellC α 1) where
  notMem_range := by
    rintro ⟨i, hi⟩
    exact (Fin.castSucc_lt_last (g i)).ne hi
  topGrade_eq := by
    refine le_antisymm (topGrade_le_iff.mpr
      (show ∀ d : Fin 4, lab ⊤ ⊤ ⊤ ⊥ d = ⊤ → cells.grade d ≤ 1 from fun d hd ↦ ?_)) ?_
    · by_cases hd3 : d = 3
      · subst hd3
        simp [lab] at hd
      · exact (grade_eq_one d hd3).le
    · exact grade_le_topGrade (t := ctx α) (d := cellC α 2) rfl
  scope_owner := rfl
  grade_owner := rfl
  label_owner := rfl
  label_lost := rfl
  mem_scope_lost := by
    change (1 : Fin 2) ∈ cells.scope 1
    decide
  gap_owner := by
    rw [rowAt_ctx α 2 1 (by decide) (by decide), rowAt_ctx α 2 2 (by decide) le_rfl]
    change visibilityReplace 1 1 low < high
    rw [isSelfVisible_low 1 (by omega)]
    exact low_lt_omegaAddTwo.trans omegaAddTwo_lt_high
  gap_retained a ha hla := by
    change (1 : Fin 2) ∉ cells.scope a at hla
    have key : ∀ a : Fin 4, (1 : Fin 2) ∉ cells.scope a → a = 0 := by decide
    obtain rfl := key a hla
    rw [rowAt_ctx α 2 1 (by decide) (by decide), rowAt_ctx α 2 0 (by decide) (by decide)]
    change visibilityReplace 1 1 low < omegaAddTwo
    rw [isSelfVisible_low 1 (by omega)]
    exact low_lt_omegaAddTwo

/-- The face on `{0}` is the cell `0`. -/
theorem faceCell_eq_zero (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) (x : Fin p.card) :
    faceCell hp x = cellC α 0 := by
  have key : ∀ d : Fin 4, Fin.last 1 ∉ cells.scope d → d = 0 := by decide
  exact key _ (last_notMem_scope_faceCell hp x)

/-! #### The lost top cannot be lowered -/

/-- **The frontier is above `1`** in every lawful labelling `W` of the context with
`min (W 3) 1 = 1`: the cell `3` of grade `2` is then above `1` (it is self-visible at `2`), and it
lies below the lost top `1`, below the root cell `0` and below the owner `2`. -/
theorem one_lt_frontierAt (α : Ordinal.{u}) {W : Fin (ctx α).card → Label.{u}}
    (hW : (ctx α).rows.IsLawful W) (h3 : min (W (cellC α 3)) 1 = 1) :
    (1 : Label.{u}) < frontierAt (cellC α 2) (cellC α 1) 1 W := by
  obtain ⟨-, -, -, h10, h02⟩ := conditions_univ (isLawfulBelow_of_isLawful hW _)
  have h31 := le_one_of_isLawful hW
  have hsv : IsSelfVisible 2 (W (cellC α 3)) := hW.orderly (cellC α 3)
  have h1 : (1 : Label.{u}) ≤ W (cellC α 3) := min_eq_right_iff.mp h3
  have hne : W (cellC α 3) ≠ 1 := fun e ↦ by
    rw [e, isSelfVisible_one] at hsv
    omega
  have hlt : (1 : Label.{u}) < W (cellC α 3) := lt_of_le_of_ne h1 (Ne.symm hne)
  exact hlt.trans_le (le_min (h31.trans (h10.trans h02))
    (h31.trans (le_visibilityReplace (by omega) _)))

/-- The designated cells `Lo` within `{3}` have maximum `⊥` in a labelling `⊥` at `3`. -/
private theorem visibilityReplace_sup_eq_bot (α : Ordinal.{u}) {Lo : Finset (Fin (ctx α).card)}
    (hLo : ∀ x ∈ Lo, x = cellC α 3) {g : Fin (ctx α).card → Label.{u}}
    (hg3 : g (cellC α 3) = ⊥) : visibilityReplace 1 1 (Lo.sup g) = ⊥ := by
  rw [visibilityReplace_eq_bot_iff, ← le_bot_iff]
  exact Finset.sup_le fun x hx ↦ by rw [hLo x hx, hg3]

private theorem isSelfVisible_one' : IsSelfVisible 1 (1 : Label.{u}) :=
  isSelfVisible_one.mpr le_rfl

/-- **Owner lowering below the designated tops fails at the context**, with the context itself as
donor, for every designation with the lost top `1` designated and the designated cells `Lo` within
the cell `3`: at the cap `1`, with the context face `(2, 2, 2, 2)` and the donor face
`(2, 1, 2, ⊥)`, the designated top `1` has value `1`, at least the cap and above the replaced
maximum `⊥` of `Lo`, while every lowered face is at least `1` capped at `3`, so its frontier is
above `1` (`OwnerGradeOneTop.one_lt_frontierAt`). -/
theorem not_ownerLoweringBelow (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {Lo Tops : Finset (Fin (ctx α).card)}
    (hLo : ∀ x ∈ Lo, x = cellC α 3) (h1 : cellC α 1 ∈ Tops) :
    ¬ H2.OwnerLoweringBelow (faceCell hp) (faceCell hp) (cellC α 2) (cellC α 1) 1
      (ctx α).rows.IsLawful (ctx α).rows.IsLawful Lo Tops := by
  intro hOL
  have hl1 := isSelfVisible_low.{u} 1 (by omega)
  have hl2 := isSelfVisible_low.{u} 2 le_rfl
  have hL : (ctx α).rows.IsLawful (lab low low low low) :=
    isLawful_lab hl1 hl1 hl1 hl2 le_rfl le_rfl le_rfl
  have h1l : (1 : Label.{u}) ≤ low := by simp [low]
  have hg : (ctx α).rows.IsLawful (lab low 1 low ⊥) :=
    isLawful_lab hl1 isSelfVisible_one' hl1 (isSelfVisible_bot 2) bot_le h1l le_rfl
  obtain ⟨W, hW, -, hWL, hWF⟩ := hOL isSelfVisible_one' hL hg fun x ↦ by
    rw [faceCell_eq_zero α hp x]
    rfl
  have hF := hWF (cellC α 1) h1 le_rfl
    ((visibilityReplace_sup_eq_bot α hLo (g := lab low 1 low ⊥) rfl).trans_lt
      (show (⊥ : Label.{u}) < 1 by simp))
  have h3 : min (W (cellC α 3)) 1 = 1 := (hWL (cellC α 3)).trans (min_eq_right h1l)
  exact absurd hF (not_le.mpr (one_lt_frontierAt α hW h3))

/-- **The clause is not an admission of states at the context** with the context itself as donor,
for every designation with the lost top `1` designated and the designated cells `Lo` within the
cell `3`: the donor provision fails at the cap `1` for the context face `(2, 2, 2, 2)`, the donor
face `(2, 2, 2, ⊥)` (a state of the clause: its frontier `2` is at most every designated top above
the replaced maximum `⊥` of `Lo`), and the served donor face `(2, 1, 2, ⊥)`. -/
theorem not_isStateAdmission (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {Lo Tops : Finset (Fin (ctx α).card)}
    (hLo : ∀ x ∈ Lo, x = cellC α 3) (h1 : cellC α 1 ∈ Tops) :
    ¬ H2.IsStateAdmission (faceCell hp) (faceCell hp) 1 (ctx α).rows.IsLawful
      (ctx α).rows.IsLawful (H2.SelfLowG (cellC α 2) (cellC α 1) 1 Lo Tops) := by
  intro hA
  have hl1 := isSelfVisible_low.{u} 1 (by omega)
  have hl2 := isSelfVisible_low.{u} 2 le_rfl
  have hL : (ctx α).rows.IsLawful (lab low low low low) :=
    isLawful_lab hl1 hl1 hl1 hl2 le_rfl le_rfl le_rfl
  have hR : (ctx α).rows.IsLawful (lab low low low ⊥) :=
    isLawful_lab hl1 hl1 hl1 (isSelfVisible_bot 2) bot_le le_rfl le_rfl
  have h1l : (1 : Label.{u}) ≤ low := by simp [low]
  have hf : (ctx α).rows.IsLawful (lab low 1 low ⊥) :=
    isLawful_lab hl1 isSelfVisible_one' hl1 (isSelfVisible_bot 2) bot_le h1l le_rfl
  have key : ∀ d : Fin 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
  -- the context face and the donor face are a state of the clause
  have hadm : H2.SelfLowG (cellC α 2) (cellC α 1) 1 Lo Tops (lab low low low low)
      (lab low low low ⊥) := by
    intro t _ hlt
    have hfr : frontierAt (cellC α 2) (cellC α 1) 1 (lab low low low low) = low := by
      change min low (visibilityReplace 1 1 low) = low
      rw [hl1, min_self]
    rw [hfr]
    rcases key t with rfl | rfl | rfl | rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact absurd ((visibilityReplace_sup_eq_bot α hLo (g := lab low low low ⊥) rfl).symm.trans_lt
        hlt) (show ¬ (⊥ : Label.{u}) < ⊥ from lt_irrefl _)
  obtain ⟨W, hW, -, hWL, hWadm⟩ := hA.donor isSelfVisible_one' hL hR
    (fun x ↦ by rw [faceCell_eq_zero α hp x]; rfl) hadm hf fun d ↦ by
      rcases key d with rfl | rfl | rfl | rfl
      · rfl
      · change min 1 1 = min low 1
        rw [min_self, min_eq_right h1l]
      · rfl
      · rfl
  have hF := hWadm (cellC α 1) h1
    ((visibilityReplace_sup_eq_bot α hLo (g := lab low 1 low ⊥) rfl).trans_lt
      (show (⊥ : Label.{u}) < 1 by simp))
  have h3 : min (W (cellC α 3)) 1 = 1 := (hWL (cellC α 3)).trans (min_eq_right h1l)
  exact absurd hF (not_le.mpr (one_lt_frontierAt α hW h3))

/-! #### The designation of the clause -/

/-- The cells labelled below `⊤` are the cell `3`. -/
theorem eq_three_of_label_ne_top (α : Ordinal.{u}) {x : Fin (ctx α).card}
    (hx : (ctx α).label x ≠ ⊤) : x = cellC α 3 := by
  have key : ∀ d : Fin 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
  rcases key x with h | h | h | h <;> subst h
  · exact absurd rfl hx
  · exact absurd rfl hx
  · exact absurd rfl hx
  · rfl

/-- The lost top `1` is not visible through the root face. -/
theorem one_notMem_visibleCells (α : Ordinal.{u}) :
    cellC α 1 ∉ (ctx α).toScheme.visibleCells Fin.castSuccEmb := by
  intro h
  obtain ⟨i, hi⟩ := Scheme.mem_visibleCells.mp h (show (1 : Fin 2) ∈ cells.scope 1 by decide)
  exact (Fin.castSucc_lt_last i).ne hi

/-- **The lost top `1` is not determined by the root**: `(2, 1, 2, ⊥)` and `(2, 2, 2, ⊥)` are
lawful, agree at the root cell `0` and differ at `1`. -/
theorem not_rootDet_one (α : Ordinal.{u}) : ¬ H2.RootDet (ctx α) (cellC α 1) := by
  intro hdet
  have hl1 := isSelfVisible_low.{u} 1 (by omega)
  have h1l : (1 : Label.{u}) ≤ low := by simp [low]
  have e := hdet (lab low 1 low ⊥) (lab low low low ⊥)
    (isLawful_lab hl1 isSelfVisible_one' hl1 (isSelfVisible_bot 2) bot_le h1l le_rfl)
    (isLawful_lab hl1 hl1 hl1 (isSelfVisible_bot 2) bot_le le_rfl le_rfl) fun y hy ↦ by
      have key : ∀ d : Fin 4, d ≠ 0 → (1 : Fin 2) ∈ cells.scope d := by decide
      by_cases hy0 : y = cellC α 0
      · rw [hy0]
        rfl
      · obtain ⟨i, hi⟩ := Scheme.mem_visibleCells.mp hy (key y hy0)
        exact absurd hi (Fin.castSucc_lt_last i).ne
  change (1 : Label.{u}) = low at e
  exact absurd e (by simp [low])

/-- **The designation of the clause at two points** (the cells of the donor labelled below `⊤` as
the designated cells, and among the designated tops every cell labelled `⊤` of grade at most `1`,
off the root and not determined by the root): the clause is not an admission of states at the
context with itself as donor, and owner lowering below the designated tops fails. -/
theorem not_isStateAdmission_designated (α : Ordinal.{u}) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb (ctx α) = some p) {Lo Tops : Finset (Fin (ctx α).card)}
    (hLo : ∀ x ∈ Lo, (ctx α).label x ≠ ⊤)
    (hTops : ∀ x, (ctx α).label x = ⊤ → (ctx α).toCellScheme.grade x ≤ 1 →
      x ∉ (ctx α).toScheme.visibleCells Fin.castSuccEmb → ¬ H2.RootDet (ctx α) x → x ∈ Tops) :
    ¬ H2.IsStateAdmission (faceCell hp) (faceCell hp) 1 (ctx α).rows.IsLawful
        (ctx α).rows.IsLawful (H2.SelfLowG (cellC α 2) (cellC α 1) 1 Lo Tops) ∧
      ¬ H2.OwnerLoweringBelow (faceCell hp) (faceCell hp) (cellC α 2) (cellC α 1) 1
        (ctx α).rows.IsLawful (ctx α).rows.IsLawful Lo Tops := by
  have hLo' (x : Fin (ctx α).card) (hx : x ∈ Lo) : x = cellC α 3 :=
    eq_three_of_label_ne_top α (hLo x hx)
  have h1 := hTops (cellC α 1) rfl le_rfl (one_notMem_visibleCells α) (not_rootDet_one α)
  exact ⟨not_isStateAdmission α hp hLo' h1, not_ownerLoweringBelow α hp hLo' h1⟩

end VaughtConjecture.OwnerGradeOneTop

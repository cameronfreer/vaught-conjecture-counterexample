/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapFieldAdmission

/-!
# The LOW clause with a separate field: the provisions for arbitrary faces

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3); the state-level test of
`VaughtConjecture.Continuation.SourceGapFieldAdmission`, for arbitrary inputs.

**Faces in general.**  A state is a context face `L : ιC → Label`, a donor face `R : ιD → Label`
and a field `b`, the faces agreeing on a root `ιR` (through `rc : ιR → ιC`, `rd : ιR → ιD`).  The
clause (`FieldAdmission.LowAtG`) is that of `FieldAdmission.LowAt` with the owner `o`, the lost top
`r`, the grade `K`, the designated cells `Lo` below the top and the designated tops `Tops`, and the
frontier `min (L o) (visibilityReplace K K (L r))` (`FieldAdmission.frontierAt`).  The provisions
(`FieldAdmission.IsFieldAdmissionG`) are those of `FieldAdmission.IsFieldAdmission`, with the root
in place of the cell `y`.

**The frontier is at most the retained tops** (`StageType.IsSourceGapContextAt.frontier_le`), in
every lawful labelling of every source-gap context, with no further hypothesis: the witness at the
owner reads the lost top through the gap below every top cell `a` avoiding the lost point; either
`a` is at least the owner, or it is the shifted row value at `a`, which bounds the shifted row value
at `r` and, below the suppressor at `K`, its replacement at `K`.

**The universal provisions** (`FieldAdmission.isFieldAdmissionG_of`): the clause is a field
admission for the context lawfulness `C` and the donor lawfulness `D` as soon as
* the owner is self-visible at `K` in every lawful context face (the order law at the owner);
* **the frontier is at most the root** at a set `A` of root cells (for a source-gap context, the
  root cells labelled `⊤`: `StageType.IsSourceGapContextAt.frontier_le`);
* **donor raising** (`FieldAdmission.DonorRaising`): a lawful donor face, a lawful context face
  agreeing with it on the root capped at `h`, and a label `c` self-visible at `K` at most the
  context face at `A`, give a lawful donor face with the root of the context face, agreeing with
  the donor face capped at `h`, and at least `c` at every designated top at least `h`;
* **owner lowering** (`FieldAdmission.OwnerLowering`): a lawful context face and a lawful donor
  face agreeing with it on the root capped at `h` give a lawful context face with the root of the
  donor face, agreeing with the context face capped at `h`, with frontier at most `h`.

The served faces are those of these conditions, with the field capped at `h`.

**Instances** (`FieldAdmission.isFieldAdmissionG_T`, `FieldAdmission.isFieldAdmissionG_t2`): at
`SeparationObstruction.T` and at `OwnerPartner.t2` (context), with the donor on the scheme of `T`,
for every designation with the designated tops among `z'`, `o'`, `r'`: the frontier bound from the
source-gap clauses of the two inputs, donor raising on the scheme of `T`
(`FieldAdmission.donorRaising_S`), owner lowering on both schemes
(`FieldAdmission.ownerLowering_S`, `FieldAdmission.ownerLowering_S2`).

**Status.**  Donor raising and owner lowering are hypotheses (named, not derived from legality);
they hold at both inputs here.  No input violating them is compiled.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label SeparationObstruction

/-! ### The frontier at a source-gap context -/

namespace StageType.IsSourceGapContextAt

variable {α : Ordinal.{u}} {n k K : ℕ} {t' : StageType.{u} α k} {g₀ : Fin n ↪ Fin k}
  {l : Fin k} {o r : Fin t'.card}

/-- **The frontier is at most every retained top** in every lawful labelling of a source-gap
context: `min (f o) (visibilityReplace K K (f r)) ≤ f a` for every cell `a` labelled `⊤` whose scope
avoids the lost point. -/
theorem frontier_le (hs : t'.IsSourceGapContextAt K g₀ l o r) {f : Fin t'.card → Label.{u}}
    (hf : t'.rows.IsLawful f) {a : Fin t'.card} (ha : t'.label a = ⊤)
    (hla : l ∉ t'.toCellScheme.scope a) :
    min (f o) (visibilityReplace K K (f r)) ≤ f a := by
  have hga : t'.toCellScheme.grade a ≤ K := hs.topGrade_eq ▸ grade_le_topGrade ha
  have hgr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hbelow (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) :
      d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) :=
    (CellScheme.mem_below _).mpr ⟨show t'.toCellScheme.scope d ⊆ t'.toCellScheme.scope o by
      rw [hs.scope_owner]; exact subset_univ _,
      show t'.toCellScheme.grade d ≤ t'.toCellScheme.grade o by rw [hs.grade_owner]; exact hd⟩
  have hgap := hs.gap_retained a ha hla
  rw [Scheme.rowAt_of_mem (hbelow r hgr), Scheme.rowAt_of_mem (hbelow a hga)] at hgap
  set x := t'.rows.row o ⟨r, hbelow r hgr⟩
  set y := t'.rows.row o ⟨a, hbelow a hga⟩
  obtain ⟨g, σ, hw, he⟩ := hf.locality o
  have eo := he ⟨o, hbelow o hs.grade_owner.le⟩
  have er := he ⟨r, hbelow r hgr⟩
  have ea := he ⟨a, hbelow a hga⟩
  change min (f o) (f o) = min (σ (t'.rows.row o ⟨o, _⟩)) (g (t'.toCellScheme.grade o)) at eo
  change min (f r) (f o) = min (σ x) (g (t'.toCellScheme.grade r)) at er
  change min (f a) (f o) = min (σ y) (g (t'.toCellScheme.grade a)) at ea
  rw [min_self] at eo
  have hfo : f o ≤ g K :=
    (eo.le.trans (min_le_right _ _)).trans (hw.antitone hs.grade_owner.ge)
  have hσxy : σ x ≤ σ y := hw.monotone ((le_visibilityReplace (by omega) x).trans hgap.le)
  by_cases hao : f o ≤ f a
  · exact (min_le_left _ _).trans hao
  have hao' : f a < f o := not_le.mp hao
  have hga' : f o ≤ g (t'.toCellScheme.grade a) := hfo.trans (hw.antitone hga)
  have hfa : f a = σ y := by
    rw [min_eq_left hao'.le] at ea
    rcases le_total (σ y) (g (t'.toCellScheme.grade a)) with h1 | h1
    · rw [min_eq_left h1] at ea; exact ea
    · rw [min_eq_right h1] at ea; exact absurd (ea ▸ hga') (not_le.mpr hao')
  by_cases hro : f o ≤ f r
  · rw [min_eq_right hro] at er
    exact absurd ((er ▸ min_le_left _ _ : f o ≤ σ x).trans (hσxy.trans hfa.ge)) (not_le.mpr hao')
  have hro' : f r < f o := not_le.mp hro
  rw [min_eq_left hro'.le] at er
  by_cases hσx : σ x ≤ g K
  · have hc := hw.visibilityReplace_comm x K hσx K le_rfl
    refine (min_le_right _ _).trans ?_
    calc visibilityReplace K K (f r) ≤ visibilityReplace K K (σ x) :=
          monotone_visibilityReplace le_rfl (er ▸ min_le_left _ _)
      _ = σ (visibilityReplace K K x) := hc.symm
      _ ≤ σ y := hw.monotone hgap.le
      _ = f a := hfa.symm
  · have hlt : f r < σ x := hro'.trans_le (hfo.trans (not_le.mp hσx).le)
    have hfr : f r = g (t'.toCellScheme.grade r) := by
      rcases le_total (σ x) (g (t'.toCellScheme.grade r)) with h1 | h1
      · rw [min_eq_left h1] at er; exact absurd er hlt.ne
      · rw [min_eq_right h1] at er; exact er
    have : g K ≤ g (t'.toCellScheme.grade r) := hw.antitone hgr
    exact absurd (hfr ▸ this) (not_le.mpr (hro'.trans_le hfo))

end StageType.IsSourceGapContextAt

namespace FieldAdmission

/-! ### The clause and the provisions for arbitrary faces -/

section General

variable {ιC ιD ιR : Type*} (rc : ιR → ιC) (rd : ιR → ιD) (o r : ιC) (K : ℕ)

/-- The **frontier** of a context face at the grade `K`. -/
noncomputable def frontierAt (L : ιC → Label.{u}) : Label.{u} :=
  min (L o) (visibilityReplace K K (L r))

/-- **The LOW clause at the field `b`** for arbitrary faces. -/
def LowAtG (Lo Tops : Finset ιD) (L : ιC → Label.{u}) (R : ιD → Label.{u}) (b : Label.{u}) :
    Prop :=
  Lo.sup R < b → ∀ t ∈ Tops, max b (frontierAt o r K L) ≤ R t

/-- **A field admission of states** for arbitrary faces sharing a root. -/
structure IsFieldAdmissionG (C : (ιC → Label.{u}) → Prop) (D : (ιD → Label.{u}) → Prop)
    (Adm : (ιC → Label.{u}) → (ιD → Label.{u}) → Label.{u} → Prop) : Prop where
  bot : Adm (fun _ ↦ ⊥) (fun _ ↦ ⊥) ⊥
  comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ0 : σ ⊥ = ⊥)
    (hsv : ∀ x, IsSelfVisible K (σ x)) {L : ιC → Label.{u}} {R : ιD → Label.{u}}
    {b : Label.{u}} (h : Adm L R b) : Adm (fun z ↦ σ (L z)) (fun z ↦ σ (R z)) (σ b)
  context {h b : Label.{u}} (hh : IsSelfVisible K h) (hb : IsSelfVisible K b)
    {L f : ιC → Label.{u}} {R : ιD → Label.{u}} (hL : C L) (hR : D R)
    (hy : ∀ x, L (rc x) = R (rd x)) (hadm : Adm L R b) (hf : C f)
    (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : ιD → Label.{u}, ∃ b' : Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧
      (∀ d, min (W d) h = min (R d) h) ∧ IsSelfVisible K b' ∧ min b' h = min b h ∧ Adm f W b'
  donor {h b : Label.{u}} (hh : IsSelfVisible K h) (hb : IsSelfVisible K b)
    {L : ιC → Label.{u}} {R f : ιD → Label.{u}} (hL : C L) (hR : D R)
    (hy : ∀ x, L (rc x) = R (rd x)) (hadm : Adm L R b) (hf : D f)
    (hfR : ∀ d, min (f d) h = min (R d) h) :
    ∃ W : ιC → Label.{u}, ∃ b' : Label.{u}, C W ∧ (∀ x, W (rc x) = f (rd x)) ∧
      (∀ d, min (W d) h = min (L d) h) ∧ IsSelfVisible K b' ∧ min b' h = min b h ∧ Adm W f b'

/-- **Donor raising** at the designated tops `Tops`, up to labels at most the context face at the
root cells `A`. -/
def DonorRaising (C : (ιC → Label.{u}) → Prop) (D : (ιD → Label.{u}) → Prop) (A : Set ιR)
    (Tops : Finset ιD) : Prop :=
  ∀ {h c : Label.{u}}, IsSelfVisible K h → IsSelfVisible K c → ∀ {R : ιD → Label.{u}}
    {f : ιC → Label.{u}}, D R → C f → (∀ x, min (f (rc x)) h = min (R (rd x)) h) →
    (∀ a ∈ A, c ≤ f (rc a)) →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t ∈ Tops, h ≤ R t → c ≤ W t

/-- **Owner lowering**: the frontier lowered to the cap with the root of a donor face. -/
def OwnerLowering (C : (ιC → Label.{u}) → Prop) (D : (ιD → Label.{u}) → Prop) : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible K h → ∀ {L : ιC → Label.{u}} {g : ιD → Label.{u}}, C L → D g →
    (∀ x, min (g (rd x)) h = min (L (rc x)) h) →
    ∃ W : ιC → Label.{u}, C W ∧ (∀ x, W (rc x) = g (rd x)) ∧ (∀ d, min (W d) h = min (L d) h) ∧
      frontierAt o r K W ≤ h

variable {rc rd o r K}

theorem isSelfVisible_frontierAt {L : ιC → Label.{u}} (ho : IsSelfVisible K (L o)) :
    IsSelfVisible K (frontierAt o r K L) :=
  ho.min (visibilityReplace_self_visibilityReplace le_rfl (L r))

/-- The frontier capped at a self-visible `h` depends only on the face capped at `h`. -/
theorem frontierAt_cap {h : Label.{u}} (hh : IsSelfVisible K h) {L f : ιC → Label.{u}}
    (hfL : ∀ d, min (f d) h = min (L d) h) :
    min (frontierAt o r K f) h = min (frontierAt o r K L) h := by
  unfold frontierAt
  calc min (min (f o) (visibilityReplace K K (f r))) h
      = min (min (f o) h) (min (visibilityReplace K K (f r)) h) := min_min_cap _ _ _
    _ = min (min (f o) h) (visibilityReplace K K (min (f r) h)) := by
        rw [visibilityReplace_min_of_isSelfVisible le_rfl hh]
    _ = min (min (L o) h) (visibilityReplace K K (min (L r) h)) := by rw [hfL o, hfL r]
    _ = min (min (L o) (visibilityReplace K K (L r))) h := by
        rw [visibilityReplace_min_of_isSelfVisible le_rfl hh, ← min_min_cap]

private theorem sup_lt_of_agreeG {Lo : Finset ιD} {W R : ιD → Label.{u}} {b h : Label.{u}}
    (hWR : ∀ d, min (W d) h = min (R d) h) (hlt : Lo.sup W < min b h) : Lo.sup R < b := by
  have hb0 : ⊥ < min b h := bot_le.trans_lt hlt
  have hbb : (⊥ : Label.{u}) < b := hb0.trans_le (min_le_left _ _)
  refine (Finset.sup_lt_iff hbb).mpr fun d hd ↦ ?_
  have hWd : W d < min b h := (Finset.sup_lt_iff hb0).mp hlt d hd
  have hRd : R d = W d := Label.eq_of_min_eq_of_lt (hWR d) (hWd.trans_le (min_le_right _ _))
  rw [hRd]
  exact hWd.trans_le (min_le_left _ _)

/-- Images of the clause under a monotone map fixing `⊥` with values self-visible at `K`. -/
theorem lowAtG_comp {Lo Tops : Finset ιD} {σ : Label.{u} → Label.{u}} (hσ : Monotone σ)
    (hσ0 : σ ⊥ = ⊥) (hsv : ∀ x, IsSelfVisible K (σ x)) {L : ιC → Label.{u}}
    {R : ιD → Label.{u}} {b : Label.{u}} (h : LowAtG o r K Lo Tops L R b) :
    LowAtG o r K Lo Tops (fun z ↦ σ (L z)) (fun z ↦ σ (R z)) (σ b) := by
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
      exact (hσ (hc'.trans hdeq.le)).trans (Finset.le_sup (f := fun z ↦ σ (R z)) hd)
  refine le_trans ?_ (hσ (h hlt' t ht))
  rw [hσ.map_max]
  refine max_le_max le_rfl ?_
  rw [frontierAt, frontierAt, (hsv (L r)).visibilityReplace_eq, hσ.map_min]
  exact min_le_min le_rfl (hσ (le_visibilityReplace (by omega) _))

/-- **The universal provisions**: under the order law at the owner, the frontier bound at the root
cells `A`, donor raising and owner lowering, the LOW clause with a separate field is a field
admission, for every designation. -/
theorem isFieldAdmissionG_of {C : (ιC → Label.{u}) → Prop} {D : (ιD → Label.{u}) → Prop}
    {Lo Tops : Finset ιD} (A : Set ιR) (hCo : ∀ f, C f → IsSelfVisible K (f o))
    (hCF : ∀ f, C f → ∀ a ∈ A, frontierAt o r K f ≤ f (rc a))
    (hDR : DonorRaising rc rd K C D A Tops) (hOL : OwnerLowering rc rd o r K C D) :
    IsFieldAdmissionG rc rd K C D (LowAtG o r K Lo Tops) where
  bot := fun h ↦ absurd h (not_lt.mpr bot_le)
  comp hσ hσ0 hsv _ _ _ h := lowAtG_comp hσ hσ0 hsv h
  context := fun {h b} hh hb {L f R} hL hR hy hadm hf hfL ↦ by
    have hroot (x : ιR) : min (f (rc x)) h = min (R (rd x)) h := by rw [hfL, hy]
    obtain ⟨W, hW, hWr, hWR, hWt⟩ := hDR hh (isSelfVisible_frontierAt (hCo f hf)) hR hf hroot
      (hCF f hf)
    refine ⟨W, min b h, hW, hWr, hWR, hb.min hh, by rw [min_assoc, min_self],
      fun hlt t ht ↦ ?_⟩
    have horig := hadm (sup_lt_of_agreeG hWR hlt) t ht
    by_cases hRt : R t < h
    · rw [Label.eq_of_min_eq_of_lt (hWR t).symm hRt]
      have hfr : frontierAt o r K L < h := ((le_max_right _ _).trans horig).trans_lt hRt
      have hFF : frontierAt o r K f = frontierAt o r K L :=
        Label.eq_of_min_eq_of_lt (frontierAt_cap hh hfL).symm hfr
      rw [hFF]
      exact max_le ((min_le_left _ _).trans ((le_max_left _ _).trans horig))
        ((le_max_right _ _).trans horig)
    · have hRt' := not_lt.mp hRt
      exact max_le ((min_le_right _ _).trans (le_of_min_eq_of_le (hWR t) hRt'))
        (hWt t ht hRt')
  donor := fun {h b} hh hb {L R f} hL hR hy hadm hf hfR ↦ by
    have hroot (x : ιR) : min (f (rd x)) h = min (L (rc x)) h := by rw [hfR, hy]
    obtain ⟨W, hW, hWr, hWL, hWF⟩ := hOL hh hL hf hroot
    refine ⟨W, min b h, hW, hWr, hWL, hb.min hh, by rw [min_assoc, min_self],
      fun hlt t ht ↦ ?_⟩
    have horig := hadm (sup_lt_of_agreeG hfR hlt) t ht
    have hFW : frontierAt o r K W ≤ min (frontierAt o r K L) h := by
      rw [← frontierAt_cap hh hWL]
      exact le_min le_rfl hWF
    by_cases hRt : R t < h
    · rw [Label.eq_of_min_eq_of_lt (hfR t).symm hRt]
      exact max_le ((min_le_left _ _).trans ((le_max_left _ _).trans horig))
        (hFW.trans ((min_le_left _ _).trans ((le_max_right _ _).trans horig)))
    · have hft : h ≤ f t := le_of_min_eq_of_le (hfR t) (not_lt.mp hRt)
      exact max_le ((min_le_right _ _).trans hft) (hFW.trans ((min_le_right _ _).trans hft))

end General

/-! ### The two conditions at the inputs `T` and `t2` -/

/-- The root of the faces on five cells: the cell `y`. -/
abbrev root5 : Fin 1 → Fin 5 := fun _ ↦ 0

/-- **Donor raising on the scheme of `T`**, at the designated tops among `z'`, `o'`, `r'`, for
every context whose lawful faces have the root self-visible at `1`: the donor face
`(f y, ⊥, f y, o', r')` with `o'`, `r'` of the given donor face below `h`, and `max h c`,
`max h o'` at or above it. -/
theorem donorRaising_S {C : (Fin 5 → Label.{u}) → Prop} {Tops : Finset (Fin 5)}
    (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) (hC0 : ∀ f, C f → IsSelfVisible 1 (f 0)) :
    DonorRaising root5 root5 2 C S.{u}.rows.IsLawful Set.univ Tops := by
  intro h c hh hc R f hR hf hroot hcf
  have hc0 : c ≤ f 0 := hcf 0 (Set.mem_univ _)
  obtain ⟨hRe, hw'a, has'⟩ := eq_lab_of_isLawful hR
  set a := R 0
  set w' := R 3
  set s' := R 4
  have ha : min (f 0) h = min a h := hroot 0
  have hfa_lt (hah : a < h) : f 0 = a := Label.eq_of_min_eq_of_lt ha.symm hah
  have hfa_ge (hah : h ≤ a) : h ≤ f 0 := le_of_min_eq_of_le ha hah
  have hR1 : R 1 = ⊥ := by rw [hRe]; rfl
  have hR2 : R 2 = a := by rw [hRe]; rfl
  set w2 := if w' < h then w' else max h c with hw2def
  set s2 := if s' < h then s' else max h w2 with hs2def
  have hw2a : w2 ≤ f 0 := by
    by_cases hw : w' < h
    · rw [hw2def, ite_eq_left hw]
      by_cases hah : a < h
      · rw [hfa_lt hah]; exact hw'a
      · exact hw.le.trans (hfa_ge (not_lt.mp hah))
    · rw [hw2def, ite_eq_right hw]
      exact max_le (hfa_ge ((not_lt.mp hw).trans hw'a)) hc0
  have hw2sv : IsSelfVisible 2 w2 := by
    rw [hw2def]; split_ifs
    exacts [hR.orderly 3, hh.max hc]
  have hs2sv : IsSelfVisible 2 s2 := by
    rw [hs2def]; split_ifs
    exacts [hR.orderly 4, hh.max hw2sv]
  have hroot' (hs : h ≤ s') (hw : w' < h) : a = w' := by
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
        have haw := hroot' hs' hw
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
  refine ⟨lab (f 0) w2 s2, isLawful_lab (hC0 f hf) hw2sv hs2sv hw2a hlaw, fun _ ↦ rfl, hagree,
    fun t ht hRt ↦ ?_⟩
  rcases hTops t ht with rfl | rfl | rfl
  · exact hc0
  · change c ≤ w2
    rw [hw2def, ite_eq_right (not_lt.mpr hRt)]
    exact le_max_right _ _
  · change c ≤ s2
    rw [hs2def, ite_eq_right (not_lt.mpr hRt)]
    by_cases hw : w' < h
    · have haw := hroot' hRt hw
      exact hc0.trans ((hfa_lt (haw ▸ hw)).le.trans ((haw ▸ hw).le.trans (le_max_left _ _)))
    · rw [hw2def, ite_eq_right hw]
      exact (le_max_right _ _).trans (le_max_right _ _)

/-- The frontier of the context face capped at `h` at `o` and `r` is at most `h`. -/
theorem frontierAt_lab_le (f0 w s h : Label.{u}) :
    frontierAt (3 : Fin 5) 4 2 (lab f0 (min w h) (min s h)) ≤ h := by
  rw [frontierAt]
  exact (min_le_left _ _).trans (min_le_right _ _)

/-- **Owner lowering on the scheme of `T`**: the context face capped at `h` at `o` and `r`, with
the root of the donor face. -/
theorem ownerLowering_S :
    OwnerLowering root5 root5 (3 : Fin 5) 4 2 S.{u}.rows.IsLawful S.{u}.rows.IsLawful := by
  intro h hh L g hL hg hroot
  obtain ⟨hLe, hwa, has⟩ := eq_lab_of_isLawful hL
  have ha : min (g 0) h = min (L 0) h := hroot 0
  have hagree (d : Fin 5) : min (lab (g 0) (min (L 3) h) (min (L 4) h) d) h = min (L d) h := by
    fin_cases d
    · exact ha
    · change min ⊥ h = min (L 1) h; rw [hLe]; rfl
    · change min (g 0) h = min (L 2) h; rw [hLe]; exact ha
    · change min (min (L 3) h) h = min (L 3) h; rw [min_assoc, min_self]
    · change min (min (L 4) h) h = min (L 4) h; rw [min_assoc, min_self]
  refine ⟨_, isLawful_lab (hg.orderly 0) ((hL.orderly 3).min hh) ((hL.orderly 4).min hh) ?_ ?_,
    fun _ ↦ rfl, hagree, frontierAt_lab_le _ _ _ _⟩
  · by_cases hah : L 0 < h
    · rw [Label.eq_of_min_eq_of_lt ha.symm hah]
      exact (min_le_left _ _).trans hwa
    · exact (min_le_right _ _).trans (le_of_min_eq_of_le ha (not_lt.mp hah))
  · by_cases hah : L 0 < h
    · rw [Label.eq_of_min_eq_of_lt ha.symm hah, ← min_assoc, has, min_min_cap]
    · have hf0 := le_of_min_eq_of_le ha (not_lt.mp hah)
      rw [min_eq_right ((min_le_right _ _).trans hf0), ← min_min_cap,
        ← has, min_comm (L 0), min_assoc, min_eq_right (not_lt.mp hah)]

/-- **Owner lowering on the scheme of `t2`**, as on that of `T`. -/
theorem ownerLowering_S2 :
    OwnerLowering root5 root5 (3 : Fin 5) 4 2 OwnerPartner.S2.{u}.rows.IsLawful
      S.{u}.rows.IsLawful := by
  intro h hh L g hL hg hroot
  obtain ⟨hLe, hsw, has, hsv⟩ := OwnerPartner.eq_lab2_of_isLawful hL
  have ha : min (g 0) h = min (L 0) h := hroot 0
  have hagree (d : Fin 5) : min (lab (g 0) (min (L 3) h) (min (L 4) h) d) h = min (L d) h := by
    fin_cases d
    · exact ha
    · change min ⊥ h = min (L 1) h; rw [hLe]; rfl
    · change min (g 0) h = min (L 2) h; rw [hLe]; exact ha
    · change min (min (L 3) h) h = min (L 3) h; rw [min_assoc, min_self]
    · change min (min (L 4) h) h = min (L 4) h; rw [min_assoc, min_self]
  refine ⟨_, OwnerPartner.isLawful_lab2 (hg.orderly 0) ((hL.orderly 3).min hh)
    ((hL.orderly 4).min hh) ?_ ?_ ?_, fun _ ↦ rfl, hagree, frontierAt_lab_le _ _ _ _⟩
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

/-! ### `T` and `t2` as instances -/

/-- The frontier bound at the input `T`, from its source-gap clauses. -/
theorem frontierAt_le_T {f : Fin 5 → Label.{u}} (hf : S.{u}.rows.IsLawful f) :
    frontierAt (3 : Fin 5) 4 2 f ≤ f 0 :=
  (isSourceGapContextAt_T 0).frontier_le (f := f) hf rfl (by decide)

/-- The frontier bound at the input `t2`, from its source-gap clauses. -/
theorem frontierAt_le_t2 {f : Fin 5 → Label.{u}} (hf : OwnerPartner.S2.{u}.rows.IsLawful f) :
    frontierAt (3 : Fin 5) 4 2 f ≤ f 0 :=
  (OwnerPartner.isSourceGapContextAt_t2 0).frontier_le (f := f) hf rfl (by decide)

/-- **`T` is an instance** of the universal provisions, for every designation with the designated
tops among `z'`, `o'`, `r'` (so for both of its donors). -/
theorem isFieldAdmissionG_T {Lo Tops : Finset (Fin 5)} (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) :
    IsFieldAdmissionG root5 root5 2 S.{u}.rows.IsLawful S.{u}.rows.IsLawful
      (LowAtG (3 : Fin 5) 4 2 Lo Tops) :=
  isFieldAdmissionG_of Set.univ (fun _ hf ↦ hf.orderly 3)
    (fun _ hf _ _ ↦ frontierAt_le_T hf) (donorRaising_S hTops fun _ hf ↦ hf.orderly 0)
    ownerLowering_S

/-- **`t2` is an instance** of the universal provisions (context on the scheme of `t2`, donor on
that of `T`). -/
theorem isFieldAdmissionG_t2 {Lo Tops : Finset (Fin 5)}
    (hTops : ∀ t ∈ Tops, t = 2 ∨ t = 3 ∨ t = 4) :
    IsFieldAdmissionG root5 root5 2 OwnerPartner.S2.{u}.rows.IsLawful S.{u}.rows.IsLawful
      (LowAtG (3 : Fin 5) 4 2 Lo Tops) :=
  isFieldAdmissionG_of Set.univ (fun _ hf ↦ hf.orderly 3)
    (fun _ hf _ _ ↦ frontierAt_le_t2 hf) (donorRaising_S hTops fun _ hf ↦ hf.orderly 0)
    ownerLowering_S2

end FieldAdmission

end VaughtConjecture

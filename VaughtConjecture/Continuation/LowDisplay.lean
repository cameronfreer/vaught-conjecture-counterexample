/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Continuation.SourceGapContext
import VaughtConjecture.Extension.CanonicalCode
import VaughtConjecture.Extension.PinnedExtension

/-!
# LOW displays: exact donor recovery from finite-cut receiving

Roadmap, Layer 3 ((R2) of the table of 3.4: exact residual receiving, the LOW construction of
3.3); semantic contract, items 4 and 8.

The two-coface geometry of the LOW construction [Kni26, §3.3]: a **private context** `t'` on
`k + 1` points and a **donor** `tb` on `k + 1` points are two one-point cofaces of one stage type
`p` on `k` points, `t'` along `Fin.castSuccEmb` and `tb` along `Fin.castSuccEmb`.  A **display** of
the pair is a legal stage type `D` on `k + 2` points with face `t'` along `Fin.castSuccEmb` (the
private face) and face `tb` along `extendByLast Fin.castSuccEmb` (the donor face): a coface of `t'`
completing the coatom pair `(t', tb)` over `p`.

**LOW displays** (`StageType.IsLowDisplay`).  A display `D` is a LOW display at a threshold `a`
(a label other than `⊤`) when every lawful section `q` of the rows of `D` that agrees with `t'` on
the private face, and agrees with the labels of `D` at some cutoff `δ > a` (`min (q i) δ =
min (D.label i) δ` at every cell), agrees with `tb` on the donor face.  The sections `q` are
arbitrary lawful labellings: no stage bound, no top-freeness, no relation to `D` beyond the cutoff.
This is what converts finite-cut receiving into exact donor recovery, literal tops included.

**Recovery** (`StageType.IsLowDisplay.isDeterminedWithin`, compiled in this repository).  Every
member of the receiving family of a LOW display at a cutoff above the threshold, with private face
`t'`, has donor face `tb`: so `tb` is determined over `t'` along `Fin.castSuccEmb` within that
family (`StageType.IsDeterminedWithin`), and so is every face of `tb` along `extendByLast g` over
`t'` along `g.trans Fin.castSuccEmb`
(`StageType.IsDeterminedWithin.restrictFace_extendByLast`).  At a limit stage a permitted cutoff
above the threshold exists (`StageType.IsLowDisplay.exists_cutoff`).

**Separated displays** (`StageType.IsSeparatedLowDisplay`; `StageType.IsLowDisplay.of_separated`,
compiled in this repository).  The mechanism of [Kni26, §3.3] for LOW displays: two cells `lo` and
`hi` of `D`, labelled by a proper label and by `⊤` (the **separator**), and the **separator
reading**: every lawful section that agrees with `t'` on the private face and reads `lo` strictly
below `hi` reads every donor top as `⊤`.  A cutoff above the label of `lo` keeps `lo` below `hi`
in every section agreeing with `D` at the cutoff (`Label.lt_of_min_eq_of_min_eq`), and above the
proper donor labels it keeps those labels; so a separated display with threshold above the label
of `lo` and the proper donor labels is a LOW display.

**The instance without new tops** (`StageType.exists_isLowDisplay_of_forall_top_root`, compiled in
this repository).  When every top of the donor lies in the common face, every display is a LOW
display at a threshold above its proper labels: donor tops are private cells, kept literally.  The
display is the exact pinned extension of `t'` along `Fin.castSuccEmb` through `tb`
(`StageType.exists_pinned_extension`, from the compiled coatom extension property).

**LOW displays at source-gap contexts** (`StageType.HasLowDisplays`, a statement about stage
types; open).  At a limit stage, for every legal source-gap context `t'` of grade `K` with the lost
point last, with coatom face `p`, and every legal coface `tb` of `p` of top grade at most `K`, the
pair `(t', tb)` has a LOW display at a threshold other than `⊤`.  This is the finite theorem of
the LOW construction [Kni26, §3.3]: the display is built on the coatom amalgam of `t'` and `tb`
with full-scope rows of every grade up to `k + 2` added, the separator among the new full-scope
cells of grade `K`, and the separator reading from the strict source gaps of the context.  Its
proof is the construction of that scheme, its legality for the two-coface geometry, and the
reading; not formalized here.  The coding of the rows is the native one (`Scheme.IsCoded`, row
values below `ω²`): the construction keeps the rows of `t'` and `tb` literally and codes only its
new rows.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Two readings at a cutoff -/

namespace Label

/-- **A cutoff keeps a separator**: if `lo` lies below the cutoff `δ`, a label `x` agreeing with
`lo` at `δ` lies strictly below a label `y` agreeing with `⊤` at `δ`. -/
theorem lt_of_min_eq_of_min_eq {lo δ x y : Label.{u}} (hlo : lo < δ)
    (hx : min x δ = min lo δ) (hy : min y δ = min ⊤ δ) : x < y := by
  rw [min_eq_left hlo.le] at hx
  rw [min_eq_right le_top] at hy
  have hxδ : x < δ := by
    by_contra h
    rw [min_eq_right (not_lt.mp h)] at hx
    exact hlo.ne hx.symm
  rw [min_eq_left hxδ.le] at hx
  exact hx ▸ hlo.trans_le (min_eq_right_iff.mp hy)

end Label

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-! ### Stage types on one scheme -/

/-- **Labels on one scheme**: a stage type `q` on the scheme of `D` has a labelling of the cells of
`D`, lawful for the rows of `D`, agreeing with the labels of `q` at equal positions. -/
theorem exists_isLawful_of_toScheme_eq {q D : StageType.{u} α n} (h : q.toScheme = D.toScheme) :
    ∃ l : Fin D.card → Label.{u}, D.rows.IsLawful l ∧
      ∀ (i : Fin q.card) (j : Fin D.card), (i : ℕ) = j → q.label i = l j := by
  obtain ⟨S, lq, _, _, hlq, _⟩ := q
  obtain ⟨S', _, _, _, _, _⟩ := D
  obtain rfl : S = S' := h
  exact ⟨lq, hlq, fun i j hij ↦ by obtain rfl := Fin.ext hij; rfl⟩

/-- **Face cells on one scheme**: two stage types on one scheme with the same face along `f`
have their face cells at equal positions. -/
theorem val_faceCell_eq {q D : StageType.{u} α n} (h : q.toScheme = D.toScheme)
    {f : Fin m ↪ Fin n} {t : StageType.{u} α m} (hq : restrictFace f q = some t)
    (hD : restrictFace f D = some t) (i : Fin t.card) :
    (faceCell hq i : ℕ) = faceCell hD i := by
  obtain ⟨S, _, _, _, _, _⟩ := q
  obtain ⟨S', _, _, _, _, _⟩ := D
  obtain rfl : S = S' := h
  rfl

/-- **Visible cells on one scheme**: the cells visible through `f` depend only on the scheme. -/
theorem mem_visibleCells_of_toScheme_eq {q D : StageType.{u} α n} (h : q.toScheme = D.toScheme)
    {f : Fin m ↪ Fin n} {i : Fin q.card} {j : Fin D.card} (hij : (i : ℕ) = j)
    (hi : i ∈ q.toScheme.visibleCells f) : j ∈ D.toScheme.visibleCells f := by
  obtain ⟨S, _, _, _, _, _⟩ := q
  obtain ⟨S', _, _, _, _, _⟩ := D
  obtain rfl : S = S' := h
  obtain rfl := Fin.ext hij
  exact hi

/-! ### LOW displays -/

/-- The **private cells** of a display: the cells of `D` visible through `Fin.castSuccEmb`, at the
cells of the private context. -/
noncomputable abbrev privateCell {t' : StageType.{u} α (k + 1)} {D : StageType.{u} α (k + 2)}
    (h : restrictFace Fin.castSuccEmb D = some t') : Fin t'.card → Fin D.card :=
  faceCell h

/-- A **LOW display** of the donor `tb` over the private context `t'`, at the threshold `a`: a
legal stage type `D` on `k + 2` points with face `t'` along `Fin.castSuccEmb` and face `tb` along
`extendByLast Fin.castSuccEmb`, such that every lawful section of the rows of `D` agreeing with
`t'` on the private face and with the labels of `D` at a cutoff above `a` agrees with `tb` on the
donor face. -/
structure IsLowDisplay (t' tb : StageType.{u} α (k + 1)) (D : StageType.{u} α (k + 2))
    (a : Label.{u}) : Prop where
  /-- The display is legal. -/
  isLegal : D.IsLegal
  /-- The private face is the private context. -/
  face_private : restrictFace Fin.castSuccEmb D = some t'
  /-- The donor face is the donor. -/
  face_donor : restrictFace (extendByLast Fin.castSuccEmb) D = some tb
  /-- The threshold is not `⊤`. -/
  ne_top : a ≠ ⊤
  /-- **Recovery**: lawful sections with the private face literal and the observation of `D` at a
  cutoff above the threshold have the donor face literal. -/
  recovery : ∀ q : Fin D.card → Label.{u}, D.rows.IsLawful q →
    (∀ z, q (faceCell face_private z) = t'.label z) → ∀ δ : Label.{u}, a < δ →
      (∀ i, min (q i) δ = min (D.label i) δ) → ∀ x, q (faceCell face_donor x) = tb.label x

variable {t' tb : StageType.{u} α (k + 1)} {D : StageType.{u} α (k + 2)} {a : Label.{u}}

/-- A LOW display is a coface of the private context. -/
theorem IsLowDisplay.mem_cofaces (hD : IsLowDisplay t' tb D a) : D ∈ t'.cofaces :=
  ⟨hD.isLegal, hD.face_private⟩

/-- **Recovery in the receiving family**: every member of the receiving family of a LOW display at
a cutoff above the threshold, with private face `t'`, has donor face `tb`.  So `tb` is determined
over `t'` along `Fin.castSuccEmb` within that family. -/
theorem IsLowDisplay.isDeterminedWithin (hD : IsLowDisplay t' tb D a) {δ : Label.{u}}
    (hδ : a < δ) :
    IsDeterminedWithin (receivingFamily D δ) t' Fin.castSuccEmb tb := by
  intro q ⟨hS, hcap⟩ hq
  obtain ⟨l, hl, hql⟩ := exists_isLawful_of_toScheme_eq hS
  -- the position of a cell of `q` as a cell of `D`
  have hcard : q.card = D.card := congrArg Scheme.card hS
  have hpos (j : Fin D.card) : ((Fin.cast hcard.symm j : Fin q.card) : ℕ) = j := rfl
  have hlj (j : Fin D.card) : l j = q.label (Fin.cast hcard.symm j) :=
    (hql _ j (hpos j)).symm
  have hcapl (j : Fin D.card) : min (l j) δ = min (D.label j) δ := by
    rw [hlj]
    exact hcap _ j (hpos j)
  -- the private face of `q` is literal
  have hprivate (z : Fin t'.card) : l (faceCell hD.face_private z) = t'.label z := by
    rw [hlj, ← label_faceCell hq z]
    congr 1
    exact Fin.ext ((val_faceCell_eq hS hq hD.face_private z).symm)
  have hrec := hD.recovery l hl hprivate δ hδ hcapl
  rw [← hD.face_donor]
  refine restrictFace_congr_label hS fun i j hij hi ↦ ?_
  obtain ⟨x, rfl⟩ := exists_faceCell_eq hD.face_donor (mem_visibleCells_of_toScheme_eq hS hij hi)
  rw [hql i _ hij, hrec x, label_faceCell]

/-- **Determination of the faces of the donor**: if `tb` is determined over `t'` along
`Fin.castSuccEmb` within a family, then its face `d` along `extendByLast g` is determined over
`t'` along `g.trans Fin.castSuccEmb` within the same family. -/
theorem IsDeterminedWithin.restrictFace_extendByLast {U : Set (StageType.{u} α (k + 2))}
    (hdet : IsDeterminedWithin U t' Fin.castSuccEmb tb) {g : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d) :
    IsDeterminedWithin U t' (g.trans Fin.castSuccEmb) d := by
  intro q hqU hq
  rw [← VaughtConjecture.extendByLast_trans, ← restrictFace_trans q _ _ (hdet q hqU hq)]
  exact hd

/-- **A permitted cutoff above the threshold**: at a limit stage, some permitted cutoff lies above
a threshold other than `⊤` that occurs at the stage. -/
theorem exists_isPermittedCutoff_lt (hα : Order.IsSuccLimit α) (ha : a ≠ ⊤)
    (haα : AtStage α a) : ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧ a < δ := by
  have hlt : a < α := haα.resolve_right ha
  induction a using WithBot.recBotCoe with
  | bot =>
    exact ⟨((0 : Ordinal.{u}) : Label.{u}), isPermittedCutoff_coe.mpr hα.bot_lt,
      WithBot.bot_lt_coe _⟩
  | coe a =>
    induction a using WithTop.recTopCoe with
    | top => exact absurd rfl ha
    | coe o =>
      have ho : o < α := by exact_mod_cast hlt
      exact ⟨((Order.succ o : Ordinal.{u}) : Label.{u}),
        isPermittedCutoff_coe.mpr (hα.succ_lt ho), by exact_mod_cast Order.lt_succ o⟩

/-- **LOW displays determine the donor at a permitted cutoff**: at a limit stage, a LOW display at
a threshold occurring at the stage determines every face `d` of the donor along `extendByLast g`
over `t'` along `g.trans Fin.castSuccEmb`, at a permitted cutoff. -/
theorem IsLowDisplay.exists_cutoff (hD : IsLowDisplay t' tb D a) (hα : Order.IsSuccLimit α)
    (haα : AtStage α a) {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast g) tb = some d) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D δ) t' (g.trans Fin.castSuccEmb) d := by
  obtain ⟨δ, hδ, haδ⟩ := exists_isPermittedCutoff_lt hα hD.ne_top haα
  exact ⟨δ, hδ, (hD.isDeterminedWithin haδ).restrictFace_extendByLast hd⟩

/-! ### Separated displays -/

/-- A **separated LOW display**: a display `D` of `tb` over `t'` with two cells `lo` and `hi`, the
**separator**, labelled by a proper label and by `⊤`, such that every lawful section of the rows
of `D` agreeing with `t'` on the private face and reading `lo` strictly below `hi` reads every top
of the donor as `⊤` (the **separator reading**). -/
structure IsSeparatedLowDisplay (t' tb : StageType.{u} α (k + 1)) (D : StageType.{u} α (k + 2))
    (lo hi : Fin D.card) : Prop where
  /-- The display is legal. -/
  isLegal : D.IsLegal
  /-- The private face is the private context. -/
  face_private : restrictFace Fin.castSuccEmb D = some t'
  /-- The donor face is the donor. -/
  face_donor : restrictFace (extendByLast Fin.castSuccEmb) D = some tb
  /-- The lower separator cell carries a proper label. -/
  label_lo : D.label lo ≠ ⊤
  /-- The upper separator cell carries `⊤`. -/
  label_hi : D.label hi = ⊤
  /-- **The separator reading.** -/
  reading : ∀ q : Fin D.card → Label.{u}, D.rows.IsLawful q →
    (∀ z, q (faceCell face_private z) = t'.label z) → q lo < q hi →
      ∀ x, tb.label x = ⊤ → q (faceCell face_donor x) = ⊤

/-- **A separated display is a LOW display** at every threshold, other than `⊤`, at least the
label of the lower separator cell and the labels of the donor other than `⊤`: a cutoff above the
threshold keeps the separator (`Label.lt_of_min_eq_of_min_eq`), the separator reading gives the
donor tops, and the cutoff keeps the proper donor labels (`Label.eq_of_min_eq_of_lt`). -/
theorem IsLowDisplay.of_separated {lo hi : Fin D.card} (hD : IsSeparatedLowDisplay t' tb D lo hi)
    (ha : a ≠ ⊤) (hlo : D.label lo ≤ a) (htb : ∀ x, tb.label x ≠ ⊤ → tb.label x ≤ a) :
    IsLowDisplay t' tb D a where
  isLegal := hD.isLegal
  face_private := hD.face_private
  face_donor := hD.face_donor
  ne_top := ha
  recovery q hq hp δ haδ hcap x := by
    have hsep : q lo < q hi :=
      Label.lt_of_min_eq_of_min_eq (hlo.trans_lt haδ) (hcap lo) (hD.label_hi ▸ hcap hi)
    by_cases hx : tb.label x = ⊤
    · rw [hx]
      exact hD.reading q hq hp hsep x hx
    · have h := hcap (faceCell hD.face_donor x)
      rw [label_faceCell] at h
      exact Label.eq_of_min_eq_of_lt h.symm ((htb x hx).trans_lt haδ)

/-- **A separated display at a limit stage is a LOW display at a threshold occurring at the
stage**: the threshold is an ordinal below the stage above every label of the display other than
`⊤` (`StageType.exists_lt_forall_label_lt`). -/
theorem exists_isLowDisplay_of_separated (hα : Order.IsSuccLimit α) {lo hi : Fin D.card}
    (hD : IsSeparatedLowDisplay t' tb D lo hi) :
    ∃ a : Label.{u}, AtStage α a ∧ IsLowDisplay t' tb D a := by
  obtain ⟨o, hoα, ho⟩ := D.exists_lt_forall_label_lt hα
  have hoα' : (o : Label.{u}) < α := by exact_mod_cast hoα
  refine ⟨(o : Label.{u}), .inl hoα',
    IsLowDisplay.of_separated hD (ne_top_of_lt hoα') (ho lo hD.label_lo).le fun x hx ↦ ?_⟩
  rw [← label_faceCell hD.face_donor x] at hx ⊢
  exact (ho _ hx).le

/-! ### The instance without new tops -/

/-- **Displays without new tops are LOW displays**: if every top of the donor `tb` avoids the last
point (lies in the common face `p`), every display of `(t', tb)` is a LOW display at every
threshold, other than `⊤`, at least its labels other than `⊤`.  A donor top is a private cell,
kept literally by the private face, and the cutoff keeps the proper donor labels. -/
theorem IsLowDisplay.of_forall_top_root (hD : D.IsLegal)
    (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb)
    (htop : ∀ x, tb.label x = ⊤ → Fin.last k ∉ tb.toCellScheme.scope x)
    (ha : a ≠ ⊤) (hDa : ∀ i, D.label i ≠ ⊤ → D.label i ≤ a) : IsLowDisplay t' tb D a where
  isLegal := hD
  face_private := h₁
  face_donor := h₂
  ne_top := ha
  recovery q _ hp δ haδ hcap x := by
    by_cases hx : tb.label x = ⊤
    · -- the donor top avoids the new point, so it is a private cell
      have hlast : Fin.last (k + 1) ∉ D.toCellScheme.scope (faceCell h₂ x) := by
        rw [scope_faceCell, mem_map]
        rintro ⟨y, hy, hyl⟩
        induction y using Fin.lastCases with
        | last => exact htop x hx hy
        | cast y =>
          rw [extendByLast_castSucc] at hyl
          exact (Fin.castSucc_lt_last _).ne hyl
      obtain ⟨z, hz⟩ := exists_faceCell_eq_of_last_notMem h₁ hlast
      rw [← hz, hp z, ← label_faceCell h₁ z, hz, label_faceCell, hx]
    · have h := hcap (faceCell h₂ x)
      have hxa : tb.label x ≤ a := by
        have := hDa (faceCell h₂ x) (by rwa [label_faceCell])
        rwa [label_faceCell] at this
      rw [label_faceCell] at h
      exact Label.eq_of_min_eq_of_lt h.symm (hxa.trans_lt haδ)

end StageType

end VaughtConjecture

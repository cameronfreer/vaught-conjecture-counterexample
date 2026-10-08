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

**Reading through a controller** (`StageType.exists_controller`,
`StageType.IsControllerReading.label_eq_top`,
`StageType.IsSeparatedLowDisplay.of_controllerReading`, compiled in this repository). In a legal
stage type, a lawful section `q` that is `⊤` at a cell of grade `K` is, at every cell of grade at
most `K`, the image `σ` of the row of some cell of graded index `(univ, K)` (a **controller**) under
a locality witness `(g, σ)` with `g K = ⊤`: completeness gives a controller, availability makes `q`
top at one of them, and locality there has target `q`. So the separator reading follows from the
**controller reading** (`StageType.IsControllerReading`), a property of the rows of the controllers:
for every controller and every such witness, if `σ` reads the owner and the lost top as `⊤` and the
separator strictly increasing, it reads every donor top as `⊤`. This is the form in which [Kni26,
§3.3] reads the donor through the controller of the actual state.

**The instance without new tops** (`StageType.IsLowDisplay.of_forall_top_root` here, and
`StageType.exists_isLowDisplay_of_forall_top_root` in
`VaughtConjecture.MainTheorem.LowDisplayRoute`, compiled in this repository).  When every top of
the donor lies in the common face, every display is a LOW display at a threshold above its proper
labels: donor tops are private cells, kept literally.  The display is the exact pinned extension
of `t'` along `Fin.castSuccEmb` through `tb`
(`StageType.exists_pinned_extension`, from the compiled coatom extension property).

**The LOW family** (`StageType.IsLowFamily`): the inputs of the construction, a legal source-gap
context `t'` of grade `K` with the lost point last and a legal donor `tb` of top grade at most `K`
with the same face `p` (the root) along `Fin.castSuccEmb`.  The root is shared
(`StageType.IsLowFamily.label_root`), the donor tops avoiding the new point are root cells
(`StageType.IsLowFamily.exists_root_of_last_notMem`), and the strict source gaps hold at the
private copies of the root tops (`StageType.IsLowFamily.gap_root`).

**LOW displays at source-gap contexts** (`StageType.HasLowDisplays`, in
`VaughtConjecture.MainTheorem.LowDisplayRoute`, a statement about stage types; open). At a limit
stage, every LOW family `(t', tb)` has a LOW display at a threshold occurring at the stage. This is
the finite theorem of the LOW construction [Kni26, §3.3]: the display is built on the coatom amalgam
of `t'` and `tb` with full-scope rows of every grade up to `k + 2` added, the separator among the
new full-scope cells of grade `K`, and the separator reading from the strict source gaps of the
context. Its proof is the construction of that scheme, its legality for the two-coface geometry, and
the reading; not formalized here. The coding of the rows is the native one (`Scheme.IsCoded`, row
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

/-! ### Reading through a controller -/

/-- **The top chart**: in a legal stage type `D` on `m` points, let `q` be a lawful section of the
rows of `D` with `q s = ⊤` at a cell `s` of grade `K`.  Some cell `w` of graded index `(univ, K)`
(a **controller**) has a locality witness `(g, σ)` with `g K = ⊤` such that `q` is `σ` of the row
of `w` at every cell of grade at most `K`.  Completeness gives a cell of graded index
`(univ, K)`, availability of `q` makes one of them `⊤`, and locality there has target `q`. -/
theorem exists_controller {D : StageType.{u} α m} (hD : D.IsLegal) {q : Fin D.card → Label.{u}}
    (hq : D.rows.IsLawful q) {s : Fin D.card} (hs : q s = ⊤) :
    ∃ w : Fin D.card, D.toCellScheme.gradedIndex w = (univ, D.toCellScheme.grade s) ∧
      ∃ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧
        g (D.toCellScheme.grade s) = ⊤ ∧ ∀ d : Fin D.card,
          D.toCellScheme.grade d ≤ D.toCellScheme.grade s → q d = σ (D.rowAt w d) := by
  have hg : D.toCellScheme.grade s ≤ #(univ : Finset (Fin m)) := by
    rw [card_univ, Fintype.card_fin]
    exact D.grade_le s
  obtain ⟨u₀, hu₀⟩ := (isLegal_iff.mp hD).2.2 (univ, D.toCellScheme.grade s)
    ⟨D.univ_mem_faces, D.isWellFormed.isWellFormed.grade_pos s, hg⟩
  have hsc : D.toCellScheme.scope s ⊆ D.toCellScheme.scope u₀ := by
    rw [show D.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
    exact subset_univ _
  obtain ⟨w, hw, hsw⟩ := hq.availability s u₀ hsc (congrArg Prod.snd hu₀).symm
  rw [hu₀] at hw
  rw [hs, top_le_iff] at hsw
  have hb {y : Fin D.card} (hy : D.toCellScheme.grade y ≤ D.toCellScheme.grade s) :
      y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex w) := by
    rw [CellScheme.mem_below, hw]
    exact ⟨subset_univ _, hy⟩
  obtain ⟨g, σ, hwit, heq⟩ := hq.locality w
  -- below `w`, the target of locality is `q` itself, since `q w = ⊤`
  have hq' (d : D.toCellScheme.below (D.toCellScheme.gradedIndex w)) :
      q d = min (σ (D.rows.row w d)) (g (D.toCellScheme.grade d)) := by
    have := heq d
    simp only [hsw, min_top_right] at this
    exact this
  have hgw : g (D.toCellScheme.grade s) = ⊤ := by
    have h := (hq' ⟨w, D.toCellScheme.mem_below_gradedIndex w⟩).symm.trans hsw
    rw [show D.toCellScheme.grade w = D.toCellScheme.grade s from congrArg Prod.snd hw] at h
    exact (_root_.min_eq_top.mp h).2
  refine ⟨w, hw, g, σ, hwit, hgw, fun d hd ↦ ?_⟩
  rw [hq' ⟨d, hb hd⟩, Scheme.rowAt_of_mem (hb hd)]
  have hgd : g (D.toCellScheme.grade d) = ⊤ := top_le_iff.mp (hgw ▸ hwit.antitone hd)
  rw [hgd, min_top_right]

/-- The **controller reading** of a stage type `D` at grade `K`, for the cells `o`, `r`
(the private tops), the separator `lo`, `hi`, and a set `X` of cells (the donor tops): for every
controller `w` (graded index `(univ, K)`) and every witness `(g, σ)` with `g K = ⊤`, if `σ` reads
`o` and `r` through the row of `w` as `⊤` and `lo` strictly below `hi`, then it reads every cell
of `X` as `⊤`.  A property of the rows of the controllers alone. -/
def IsControllerReading (D : StageType.{u} α m) (K : ℕ) (o r lo hi : Fin D.card)
    (X : Set (Fin D.card)) : Prop :=
  ∀ w : Fin D.card, D.toCellScheme.gradedIndex w = (univ, K) →
    ∀ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ → g K = ⊤ →
      σ (D.rowAt w o) = ⊤ → σ (D.rowAt w r) = ⊤ → σ (D.rowAt w lo) < σ (D.rowAt w hi) →
        ∀ x ∈ X, σ (D.rowAt w x) = ⊤

/-- **The controller reading gives the reading of every lawful section**: in a legal `D`, a
lawful section `q` with `q o = q r = ⊤` and `q lo < q hi`, where `o` has grade `K` and `r`,
`lo`, `hi` and the cells of `X` have grade at most `K`, reads every cell of `X` as `⊤`.  The top
chart at `o` (`StageType.exists_controller`) gives a controller `w` with `q = σ ∘ (row of w)` up
to grade `K`. -/
theorem IsControllerReading.label_eq_top {D : StageType.{u} α m} (hD : D.IsLegal) {K : ℕ}
    {o r lo hi : Fin D.card} {X : Set (Fin D.card)} (hX : IsControllerReading D K o r lo hi X)
    (ho : D.toCellScheme.grade o = K) (hr : D.toCellScheme.grade r ≤ K)
    (hlo : D.toCellScheme.grade lo ≤ K) (hhi : D.toCellScheme.grade hi ≤ K)
    (hXK : ∀ x ∈ X, D.toCellScheme.grade x ≤ K) {q : Fin D.card → Label.{u}}
    (hq : D.rows.IsLawful q) (hqo : q o = ⊤) (hqr : q r = ⊤) (hsep : q lo < q hi) :
    ∀ x ∈ X, q x = ⊤ := by
  obtain ⟨w, hw, g, σ, hwit, hg, hread⟩ := exists_controller hD hq hqo
  rw [ho] at hw hg hread
  intro x hx
  rw [hread x (hXK x hx)]
  refine hX w hw g σ hwit hg ?_ ?_ ?_ x hx
  · rw [← hread o ho.le, hqo]
  · rw [← hread r hr, hqr]
  · rwa [← hread lo hlo, ← hread hi hhi]

/-- **Separated displays from the controller reading**: a display `D` of `tb` over `t'` (legal,
with the two faces) at a source-gap context of grade `K` with owner `o` and lost top `r`, with
separator cells `lo`, `hi` of grade at most `K` labelled by a proper label and by `⊤`, is a
separated LOW display when the controller reading holds at grade `K` for the private copies of
`o` and `r`, the separator, and the donor copies of the tops of `tb` (of top grade at most `K`). -/
theorem IsSeparatedLowDisplay.of_controllerReading {K n : ℕ} {h : Fin n ↪ Fin (k + 1)}
    {l : Fin (k + 1)} {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K h l o r)
    (htbK : tb.topGrade ≤ K) (hD : D.IsLegal) (h₁ : restrictFace Fin.castSuccEmb D = some t')
    (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some tb) {lo hi : Fin D.card}
    (hlo : D.label lo ≠ ⊤) (hhi : D.label hi = ⊤) (hlog : D.toCellScheme.grade lo ≤ K)
    (hhig : D.toCellScheme.grade hi ≤ K)
    (hX : IsControllerReading D K (faceCell h₁ o) (faceCell h₁ r) lo hi
      {i | ∃ x, tb.label x = ⊤ ∧ faceCell h₂ x = i}) :
    IsSeparatedLowDisplay t' tb D lo hi where
  isLegal := hD
  face_private := h₁
  face_donor := h₂
  label_lo := hlo
  label_hi := hhi
  reading q hq hp hsep x hx := by
    have hr : D.toCellScheme.grade (faceCell h₁ r) ≤ K := by
      rw [grade_faceCell, ← hs.topGrade_eq]
      exact grade_le_topGrade hs.label_lost
    refine hX.label_eq_top hD (by rw [grade_faceCell]; exact hs.grade_owner) hr hlog hhig
      ?_ hq (by rw [hp]; exact hs.label_owner) (by rw [hp]; exact hs.label_lost) hsep _ ⟨x, hx, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [grade_faceCell]
    exact topGrade_le_iff.mp htbK y hy

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

/-! ### The LOW family -/

/-- The **LOW family** at a source-gap context: a legal private context `t'` on `k + 1` points,
a source-gap context of grade `K` with the lost point last, owner `o` and lost top `r`; a legal
donor `tb` of top grade at most `K`; and their common face `p` along `Fin.castSuccEmb` (the
**root**).  These are the inputs of the LOW construction [Kni26, §3.3]. -/
structure IsLowFamily (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop where
  /-- The private context is legal. -/
  isLegal_private : t'.IsLegal
  /-- The donor is legal. -/
  isLegal_donor : tb.IsLegal
  /-- The root is the face of the private context along the first points. -/
  face_private : restrictFace Fin.castSuccEmb t' = some p
  /-- The root is the face of the donor along the first points. -/
  face_donor : restrictFace Fin.castSuccEmb tb = some p
  /-- The private context is a source-gap context with the lost point last. -/
  isSourceGapContextAt : t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r
  /-- The tops of the donor have grade at most `K`. -/
  topGrade_donor : tb.topGrade ≤ K

namespace IsLowFamily

variable {K : ℕ} {p : StageType.{u} α k} {o r : Fin t'.card}

/-- **The root is shared**: the private and donor copies of a root cell carry its label. -/
theorem label_root (hF : IsLowFamily K t' tb p o r) (y : Fin p.card) :
    t'.label (faceCell hF.face_private y) = tb.label (faceCell hF.face_donor y) := by
  rw [label_faceCell, label_faceCell]

/-- **The donor tops off the root are the new tops**: a top of the donor avoiding the new point is
the donor copy of a root cell. -/
theorem exists_root_of_last_notMem (hF : IsLowFamily K t' tb p o r) {x : Fin tb.card}
    (hx : Fin.last k ∉ tb.toCellScheme.scope x) : ∃ y, faceCell hF.face_donor y = x :=
  exists_faceCell_eq_of_last_notMem hF.face_donor hx

/-- **The strict source gaps at the root tops**: the owner's row reads the private copy of every
root cell labelled `⊤` strictly above its replaced reading of the lost top. -/
theorem gap_root (hF : IsLowFamily K t' tb p o r) {y : Fin p.card} (hy : p.label y = ⊤) :
    Label.visibilityReplace K K (t'.rowAt o r) < t'.rowAt o (faceCell hF.face_private y) :=
  hF.isSourceGapContextAt.gap_retained _ (by rw [label_faceCell]; exact hy)
    (last_notMem_scope_faceCell hF.face_private y)

/-- **The tops of the donor have grade at most `K`.** -/
theorem grade_le (hF : IsLowFamily K t' tb p o r) {x : Fin tb.card} (hx : tb.label x = ⊤) :
    tb.toCellScheme.grade x ≤ K :=
  (topGrade_le_iff.mp hF.topGrade_donor) x hx

end IsLowFamily

end StageType

end VaughtConjecture

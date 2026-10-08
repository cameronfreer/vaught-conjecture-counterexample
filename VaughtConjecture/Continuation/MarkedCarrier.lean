/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Extension.PrescribedFullRows
import VaughtConjecture.Stage.MarkedCap

/-!
# Marked carriers: determination over a marked-cap context with reference cells

Roadmap, Layer 3 ((R3) of the table of 3.4: the hollow context with its private cap, marker and
reference cells; determination) and 3.4 (prescribed rows at the cells of full scope).

**The marked-carrier context** (`StageType.IsMarkedCarrierContextAt`, defined in this repository).
A marked-cap context (`StageType.IsMarkedCapContext`, top cap `c` of grade `N > n + 1`, marker `r`,
and the row inequality at the root) together with a **reference cell** at the threshold `N`
(`StageType.IsReferenceAt`) for every proper label of a new cell of the donor `d`: a cell of grade
at most `N` labelled `μ + kz` with `kz < N`, the donor label being `μ + i` with `i ≤ N`.

**The marked prescription** (`StageType.markedPrescription`).  At the grade `N`, a cell of full
scope reads every new cell of `d` labelled `⊤` at least as the marker, and every new cell with a
proper label in one block with a reference cell; it asks nothing of the new cells labelled `⊥`.

**A marked carrier determines the donor** (`StageType.isDeterminedWithin_of_isPrescribedExtension`,
compiled in this repository (theorem named)).  A prescribed extension `D` for the marked
prescription over `t'` carrying `d` determines `d` over `t'` along `h` within the bottom-pattern
family of `D` (the clause of a model that prescribes where a realized coface is `⊥`, [Kni26,
Definition 3.2.1, clause 4(a)ii]): the bottom pattern fixes the new cells labelled `⊥`; availability
from the top cap gives a cell of graded index `(univ, N)` labelled `⊤`, and its row forces the
other new cells (`CellScheme.Rows.IsLawful.eq_top_of_row_le` for the tops, with no condition on
the grade of the marker; the reading of a reference cell for the proper labels).  A reading of a
new cell as `⊥` is avoided on purpose: by bountifulness it would force `⊥` in every extension of
every lawful labelling of `t'` whose cap is not `⊥`.

**Marked carriers** (`StageType.HasMarkedCarriers`, a named hypothesis on stage types; open): a
prescribed extension for the marked prescription exists over every legal marked-carrier context
and legal donor.  It follows from `StageType.HasPrescribedFullRows` (open) and the compatibility
of the marked prescriptions (`StageType.HasCompatibleMarkedPrescriptions`, open)
(`StageType.HasPrescribedFullRows.hasMarkedCarriers`), and it implies that compatibility
(`StageType.HasMarkedCarriers.hasCompatibleMarkedPrescriptions`).  No implication from
`StageType.HasApexCoatomExtensions` or `StageType.HasCoatomExtensions` is compiled.  Under it,
determination within the bottom-pattern family of a coface holds over marked-carrier contexts
(`StageType.HasMarkedCarriers.exists_coface_isDeterminedWithin`).

**The cutoff form** (`StageType.topMarkedPrescription`,
`StageType.isDeterminedWithin_receivingFamily_of_isPrescribedExtension`, compiled in this
repository (theorem named)).  The top-marked prescription asks only that the cells of graded index
`(univ, N)` read the new tops of `d` at least as the marker.  A prescribed extension for it
determines `d` within its receiving family at a cutoff above its labels other than `⊤`: the
cutoff keeps those labels, and the reading makes the new tops `⊤`.  No reference cell is needed.
**Top-marked carriers** (`StageType.HasTopMarkedCarriers`, a named hypothesis on stage types;
open) ask a prescribed extension for it over every legal marked-cap context; they follow from
`StageType.HasPrescribedFullRows` and `StageType.HasCompatibleTopMarkedPrescriptions` and imply
the latter.  Where the donor has no new top (or, for marked carriers, all its new cells are `⊥`)
the prescription is empty and the exact pinned extension is a carrier, under the coatom extension
property (`StageType.HasCoatomExtensions.exists_isPrescribedExtension_topMarkedPrescription`,
`StageType.HasCoatomExtensions.exists_isPrescribedExtension_markedPrescription`).

**Compatibility, argued.**  By bountifulness every lawful labelling of the context extends to a
carrier, so a prescription constrains every lawful labelling, not only the labels.  For the
readings of the new tops this is consistent with ties of a new top below a top of the root: at a
lawful labelling with the cap and the marker `⊤`, every cell read by the cap at least as the marker
is `⊤` (`CellScheme.Rows.IsLawful.eq_top_of_row_le` with the cap as reading cell), the tops of the
root among them.  The compatibility of either prescription is not proved here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

/-! ### A cell read at least as a top under a top is a top -/

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-! ### The marked-carrier context and the marked prescription -/

/-- A **reference cell** at the threshold `N` for a label `o`: a cell `z` of grade at most `N`
labelled `μ + kz` with `μ` zero or a limit and `kz < N`, such that `o = μ + i` with `i ≤ N`.  The
label `o` is then the visibility replacement at the threshold `N` of the label of `z`. -/
def IsReferenceAt (t' : StageType.{u} α k) (N : ℕ) (o : Label.{u}) (z : Fin t'.card) : Prop :=
  t'.toCellScheme.grade z ≤ N ∧ ∃ (μ : Ordinal.{u}) (kz i : ℕ), Order.IsSuccPrelimit μ ∧
    t'.label z = ((μ + kz : Ordinal.{u}) : Label.{u}) ∧ kz < N ∧
    o = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i ≤ N

/-- A stage type `t'` on `k` points is a **marked-carrier context** along `h : Fin n ↪ Fin k` for
a donor `d` on `n + 1` points, with top cap `c` and marker `r`: `t'` is a marked-cap context
along `h` with these cells (`StageType.IsMarkedCapContext`), and every label of a new cell of `d`
(a cell whose scope contains the new point) other than `⊥` and `⊤` has a reference cell in `t'`
at the threshold `N`, the grade of `c`. -/
def IsMarkedCarrierContextAt (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (c r : Fin t'.card) : Prop :=
  t'.IsTopCap c ∧ t'.IsMarker c r ∧ n + 1 < t'.toCellScheme.grade c ∧
    (∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
      visibilityReplace (t'.toCellScheme.grade c) (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a) ∧
    ∀ j : Fin d.card, Fin.last n ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j ≠ ⊤ →
      ∃ z, t'.IsReferenceAt (t'.toCellScheme.grade c) (d.label j) z

/-- A **marked-carrier context**: a marked-carrier context with some top cap and marker. -/
def IsMarkedCarrierContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) : Prop :=
  ∃ c r, t'.IsMarkedCarrierContextAt h d c r

/-- A marked-carrier context is a marked-cap context. -/
theorem IsMarkedCarrierContext.isMarkedCapContext {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (ht : t'.IsMarkedCarrierContext h d) :
    t'.IsMarkedCapContext h :=
  let ⟨c, r, hc, hr, hn, ha, _⟩ := ht
  ⟨c, r, hc, hr, hn, ha⟩

/-- The **marked prescription** with top cap `c` and marker `r`: at the grade `N` of `c`, a cell
of full scope reads every new cell of `d` labelled `⊤` at least as `r`, and every new cell with a
proper label `μ + i` in one block with a reference cell labelled `μ + kz` (`kz < N`, `i ≤ N`,
grade at most `N`), at `ω * ν + kz` and `ω * ν + i`.  It asks nothing of the new cells labelled
`⊥` (the bottom pattern fixes them) and nothing at the other grades. -/
def markedPrescription (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) (c r : Fin t'.card) :
    FullRowPrescription t' d :=
  fun g ρ _ ↦ g = t'.toCellScheme.grade c →
    ∀ j : Fin d.card, Fin.last n ∈ d.toCellScheme.scope j →
      (d.label j = ⊤ → ρ (.inl r) ≤ ρ (.inr j)) ∧
      (d.label j ≠ ⊥ → d.label j ≠ ⊤ → ∃ (z : Fin t'.card) (μ ν : Ordinal.{u}) (kz i : ℕ),
        Order.IsSuccPrelimit μ ∧ t'.toCellScheme.grade z ≤ g ∧
        t'.label z = ((μ + kz : Ordinal.{u}) : Label.{u}) ∧ kz < g ∧
        d.label j = ((μ + i : Ordinal.{u}) : Label.{u}) ∧ i ≤ g ∧
        ρ (.inl z) = ((ω * ν + kz : Ordinal.{u}) : Label.{u}) ∧
        ρ (.inr j) = ((ω * ν + i : Ordinal.{u}) : Label.{u}))

/-! ### Determination by a marked carrier -/

/-- **A marked carrier determines the donor.**  Let `t'` restrict along `h` to `t`, let `d` be a
one-point coface of `t`, let `c` be a top cap of `t'` of grade `N ≥ n + 1`, and `r` a cell of `t'`
labelled `⊤`.  If `D` is a prescribed extension for the marked prescription over `t'` carrying
`d` (a legal one-point extension of `t'` with face `d` along `extendByLast h` whose cells of
graded index `(univ, N)` read the new cells of `d` as prescribed), then `d` is determined over
`t'` along `h` within the bottom-pattern family of `D` (the stage types on the scheme of `D` that
are `⊥` exactly where `D` is, at the cells of grade at most `k`).

Let `q` be such a stage type with face `t'` along the first points.  The cells of the root keep
their labels, and the new cells labelled `⊥` in `d` are `⊥` in `q` (the bottom pattern).  The top
cap of `t'` is labelled `⊤` in `q`, so by availability some cell `u` of graded index `(univ, N)` is
labelled `⊤`, and its row reads the other new cells of `d` as prescribed: a new cell labelled `⊤`
in `d` is read at least as `r`, hence is `⊤` (`CellScheme.Rows.IsLawful.eq_top_of_row_le`); one
with a proper label is read in one block with its reference cell, under the top cap, hence has the
prescribed label (`CellScheme.Rows.IsLawful.label_eq_of_reading`).  No reading forces `⊥`: a
reading of a cell as `⊥` would force `⊥` in every extension of every lawful labelling of `t'` with
a cap not `⊥` (bountifulness), while the bottom pattern concerns the realized member only. -/
theorem isDeterminedWithin_of_isPrescribedExtension {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} {d : StageType.{u} α (n + 1)} {c r : Fin t'.card}
    (ht : restrictFace h t' = some t) (hd : restrictFace Fin.castSuccEmb d = some t)
    (hc : t'.IsTopCap c) (hr : t'.label r = ⊤) (hn : n + 1 ≤ t'.toCellScheme.grade c)
    {D : StageType.{u} α (k + 1)}
    (hD : IsPrescribedExtension t' h d (markedPrescription t' d c r) D) :
    IsDeterminedWithin (bottomPatternFamily D.toScheme D.label) t' h d := by
  obtain ⟨hDl, h₁, h₂, he₁, he₂, hS⟩ := hD
  rintro ⟨S, ℓ, hw, hcod, hl, hat⟩ ⟨hq, hpat⟩ hq₁
  -- the stage type `q` has the scheme of `D`
  change S = D.toScheme at hq
  subst hq
  set q : StageType.{u} α (k + 1) := ⟨D.toScheme, ℓ, hw, hcod, hl, hat⟩ with hqdef
  set N := t'.toCellScheme.grade c
  -- the cells of `t'` keep their labels in `q`
  have hold (z : Fin t'.card) : ℓ (faceCell h₁ z) = t'.label z := label_faceCell hq₁ z
  obtain ⟨hf₂, -⟩ := (restrictFace_eq_some_iff D (extendByLast h)).mp h₂
  have hf₂' : univ.map (extendByLast h) ∈ q.toCellScheme.faces := hf₂
  -- the labels of `q` at the cells of the donor face
  have hlab (j : Fin d.card) : ℓ (faceCell h₂ j) = d.label j := by
    by_cases hj : Fin.last n ∈ d.toCellScheme.scope j
    · -- a new cell: read by a cell of graded index `(univ, N)` labelled `⊤`
      have hNk : N ≤ k := t'.grade_le c
      have hpos : 0 < N := (Nat.succ_pos n).trans_le hn
      obtain ⟨u₀, hu₀⟩ := hDl.isComplete ((univ : Finset (Fin (k + 1))), N)
        ⟨D.univ_mem_faces, hpos, by simpa using hNk.trans (Nat.le_succ k)⟩
      have hc' : D.toCellScheme.grade (faceCell h₁ c) = N := grade_faceCell h₁ c
      have hsu₀ : D.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
      obtain ⟨u, hu, hcu⟩ := hl.availability (faceCell h₁ c) u₀
        (by rw [hsu₀]; exact subset_univ _) (hc'.trans (congrArg Prod.snd hu₀).symm)
      have hu' : D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), N) := hu.trans hu₀
      have hℓu : ℓ u = ⊤ := by
        have h' : ℓ (faceCell h₁ c) ≤ ℓ u := hcu
        rw [hold, hc.2.1] at h'
        exact top_le_iff.mp h'
      have hbelow (y : Fin D.card) (hy : D.toCellScheme.grade y ≤ N) :
          y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
        rw [CellScheme.mem_below, hu']
        exact Prod.mk_le_mk.mpr ⟨subset_univ _, hy⟩
      have hx : faceCell h₂ j ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
        hbelow _ ((grade_faceCell h₂ j).trans_le ((d.grade_le j).trans hn))
      obtain ⟨htop, hprop⟩ := hS u N hu' rfl j hj
      -- the readings of the known cells are entries of the row of `u`
      have hread (y : Fin D.card) (hy : y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u)) :
          D.rowAt u y = D.rows.row u ⟨y, hy⟩ := Scheme.rowAt_of_mem hy
      by_cases hjt : d.label j = ⊤
      · have hs : faceCell h₁ r ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
          hbelow _ ((grade_faceCell h₁ r).trans_le (hc.2.2 r hr))
        have hrow := htop hjt
        -- the readings are those of the cells of `D` at `r` and at `j`
        change D.rowAt u (faceCell h₁ r) ≤ D.rowAt u (faceCell h₂ j) at hrow
        rw [hread _ hs, hread _ hx] at hrow
        rw [hjt]
        exact hl.eq_top_of_row_le hs hx hℓu ((hold r).trans hr) hrow
      by_cases hjb : d.label j = ⊥
      · -- the bottom pattern of `D` at the cell of `j`, of grade at most `k`
        have hgx : D.toCellScheme.grade (faceCell h₂ j) ≤ k :=
          (grade_faceCell h₂ j).trans_le (((d.grade_le j).trans hn).trans hNk)
        rw [hjb]
        set x : Fin D.card := faceCell h₂ j
        exact (hpat x x rfl hgx).mpr ((label_faceCell h₂ j).trans hjb)
      obtain ⟨z, μ, ν, kz, i, hμ, hzN, hz, hkz, hdj, hiN, hρz, hρj⟩ := hprop hjb hjt
      have ha : faceCell h₁ z ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
        hbelow _ ((grade_faceCell h₁ z).trans_le hzN)
      have hb : faceCell h₁ c ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
        hbelow _ hc'.le
      -- the readings are those of the cells of `D` at `z` and at `j`
      change D.rowAt u (faceCell h₁ z) = _ at hρz
      change D.rowAt u (faceCell h₂ j) = _ at hρj
      rw [hread _ ha] at hρz
      rw [hread _ hx] at hρj
      have hcap : ℓ (faceCell h₁ c) = ⊤ := (hold c).trans hc.2.1
      rw [hdj]
      refine hl.label_eq_of_reading ha hb hx hμ ?_ (hc'.symm ▸ hkz) (hc'.symm ▸ hiN) ?_ hρz hρj
        ((hold z).trans hz) hcu (hcap ▸ WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))
        (hcap ▸ WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))
      · rw [grade_faceCell, hc']
        exact hzN
      · rw [grade_faceCell, hc']
        exact (d.grade_le j).trans hn
    · -- a cell of the root: its label is that of `t'`
      obtain ⟨i, rfl⟩ := exists_faceCell_eq_of_last_notMem hd hj
      rw [← faceCell_faceCell h₁ h₂ ht hd i, hold, label_faceCell, label_faceCell]
  rw [restrictFace_of_mem q _ hf₂']
  refine congrArg some (StageType.ext ?_ fun i j hij ↦ ?_)
  · -- the scheme of the face of `q` is the face of the scheme of `D`
    change D.toScheme.comap (extendByLast h) = d.toScheme
    exact comap_toScheme_of_restrictFace h₂
  -- the label of the face at `i` is the label of `q` at the cell of `D` at `j`
  change ℓ (D.toScheme.cellMap (extendByLast h) i) = d.label j
  have hcell : D.toScheme.cellMap (extendByLast h) i = faceCell h₂ j := by
    change _ = D.toScheme.cellMap (extendByLast h) (Fin.cast _ j)
    congr 1
    exact Fin.ext hij
  rw [hcell, hlab]

/-! ### Marked carriers: a named hypothesis -/

variable (α) in
/-- **Marked carriers** at the stage `α` (a named hypothesis on stage types; open): over every
legal marked-carrier context `t'` along `h` for a legal donor `d`, a one-point coface of the face
of `t'` along `h`, with top cap `c` and marker `r`, there is a prescribed extension for the marked
prescription: a legal one-point extension of `t'` carrying `d` whose cells of graded index
`(univ, N)` (`N` the grade of `c`) read every new cell of `d` labelled `⊤` at least as `r`, and
every new cell with a proper label in one block with a reference cell. -/
def HasMarkedCarriers : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (_ : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (_ : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCarrierContextAt h d c r →
      ∃ D, IsPrescribedExtension t' h d (markedPrescription t' d c r) D

variable (α) in
/-- **Compatibility of the marked prescriptions** at the stage `α` (open): at every input of
`StageType.HasMarkedCarriers`, the marked prescription is compatible with the faces
(`StageType.IsFaceCompatible`). -/
def HasCompatibleMarkedPrescriptions : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCarrierContextAt h d c r → IsFaceCompatible t' ht d hd (markedPrescription t' d c r)

/-- **Marked carriers from prescribed rows**: `StageType.HasPrescribedFullRows` and the
compatibility of the marked prescriptions give marked carriers. -/
theorem HasPrescribedFullRows.hasMarkedCarriers (hpr : HasPrescribedFullRows.{u} α)
    (hcomp : HasCompatibleMarkedPrescriptions.{u} α) : HasMarkedCarriers.{u} α :=
  fun _ _ t' h t ht d hd c r ht' hd' hctx ↦
    hpr t' h t ht d hd ht' hd' _ (hcomp t' h t ht d hd c r ht' hd' hctx)

/-- **Compatibility is necessary**: marked carriers make the marked prescriptions compatible with
the faces (`StageType.IsPrescribedExtension.isFaceCompatible`).  So under
`StageType.HasPrescribedFullRows`, marked carriers are exactly this compatibility. -/
theorem HasMarkedCarriers.hasCompatibleMarkedPrescriptions (hcar : HasMarkedCarriers.{u} α) :
    HasCompatibleMarkedPrescriptions.{u} α := fun _ _ t' h t ht d hd c r ht' hd' hctx ↦
  let ⟨_, hD⟩ := hcar t' h t ht d hd c r ht' hd' hctx
  hD.isFaceCompatible ht hd

/-- **Marked carriers where the prescription is empty**: under the coatom extension property at
`α`, if every new cell of `d` is labelled `⊥`, the exact pinned extension of `t'` carrying `d`
(`StageType.exists_pinned_extension`) is a prescribed extension for the marked prescription, which
asks nothing there.  This is the only case of `StageType.HasMarkedCarriers` compiled here. -/
theorem HasCoatomExtensions.exists_isPrescribedExtension_markedPrescription
    (hext : HasCoatomExtensions.{u} α) {t' : StageType.{u} α k} (ht' : t'.IsLegal)
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} (ht : restrictFace h t' = some t)
    {d : StageType.{u} α (n + 1)} (hd' : d.IsLegal) (hd : restrictFace Fin.castSuccEmb d = some t)
    (c r : Fin t'.card)
    (hbot : ∀ j : Fin d.card, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊥) :
    ∃ D, IsPrescribedExtension t' h d (markedPrescription t' d c r) D := by
  obtain ⟨D, hD, h₁, h₂⟩ := exists_pinned_extension hext ht' ht hd' hd
  refine ⟨D, hD, h₁, h₂, comap_toScheme_of_restrictFace h₁, comap_toScheme_of_restrictFace h₂,
    fun _ _ _ _ j hj ↦ ⟨fun htop ↦ absurd ((hbot j hj).symm.trans htop) bot_ne_top,
      fun hb ↦ absurd (hbot j hj) hb⟩⟩

/-- **Determination over a marked-carrier context**, conditional on marked carriers: over a legal
marked-carrier context `t'` along `h` for a legal one-point coface `d` of the face `t` of `t'`
along `h`, some legal one-point coface `D'` of `t'` determines `d` within its bottom-pattern
family. -/
theorem HasMarkedCarriers.exists_coface_isDeterminedWithin (hcar : HasMarkedCarriers.{u} α)
    {t' : StageType.{u} α k} (ht' : t'.IsLegal) {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces)
    (hctx : t'.IsMarkedCarrierContext h d) :
    ∃ D' ∈ t'.cofaces, IsDeterminedWithin (bottomPatternFamily D'.toScheme D'.label) t' h d := by
  obtain ⟨c, r, hcr⟩ := hctx
  obtain ⟨D, hD⟩ := hcar t' h t ht d hd.2 c r ht' hd.1 hcr
  exact ⟨D, ⟨hD.1, hD.2.1⟩, isDeterminedWithin_of_isPrescribedExtension ht hd.2 hcr.1
    hcr.2.1.1 hcr.2.2.1.le hD⟩

/-! ### The cutoff form: top-marked carriers -/

/-- The **top-marked prescription** with top cap `c` and marker `r`: at the grade `N` of `c`, a
cell of full scope reads every new cell of `d` labelled `⊤` at least as `r`.  It asks nothing
else. -/
def topMarkedPrescription (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1))
    (c r : Fin t'.card) : FullRowPrescription t' d :=
  fun g ρ _ ↦ g = t'.toCellScheme.grade c →
    ∀ j : Fin d.card, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ →
      ρ (.inl r) ≤ ρ (.inr j)

/-- **A top-marked carrier determines the donor at a cutoff.**  Let `t'` restrict along `h` to
`t`, let `d` be a one-point coface of `t`, `c` a top cap of `t'` of grade `N ≥ n + 1`, and `r` a
cell of `t'` labelled `⊤`.  If `D` is a prescribed extension for the top-marked prescription over
`t'` carrying `d`, and the cutoff `δ` lies above every label of `D` other than `⊤`, then `d` is
determined over `t'` along `h` within the receiving family of `D` at `δ`.  The labels below `δ`
are kept by the receiving family, and a new cell labelled `⊤` in `d` is read at least as `r` by a
cell of graded index `(univ, N)` labelled `⊤` (availability from the top cap), hence is `⊤`
(`CellScheme.Rows.IsLawful.eq_top_of_row_le`). -/
theorem isDeterminedWithin_receivingFamily_of_isPrescribedExtension {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} {d : StageType.{u} α (n + 1)} {c r : Fin t'.card}
    (ht : restrictFace h t' = some t) (hd : restrictFace Fin.castSuccEmb d = some t)
    (hc : t'.IsTopCap c) (hr : t'.label r = ⊤) (hn : n + 1 ≤ t'.toCellScheme.grade c)
    {D : StageType.{u} α (k + 1)}
    (hD : IsPrescribedExtension t' h d (topMarkedPrescription t' d c r) D) {δ : Label.{u}}
    (hδ : ∀ j, D.label j ≠ ⊤ → D.label j < δ) :
    IsDeterminedWithin (receivingFamily D δ) t' h d := by
  obtain ⟨hDl, h₁, h₂, he₁, he₂, hS⟩ := hD
  rintro ⟨S, ℓ, hw, hcod, hl, hat⟩ ⟨hq, hcut⟩ hq₁
  -- the stage type `q` has the scheme of `D`
  change S = D.toScheme at hq
  subst hq
  set q : StageType.{u} α (k + 1) := ⟨D.toScheme, ℓ, hw, hcod, hl, hat⟩ with hqdef
  set N := t'.toCellScheme.grade c
  have hold (z : Fin t'.card) : ℓ (faceCell h₁ z) = t'.label z := label_faceCell hq₁ z
  obtain ⟨hf₂, -⟩ := (restrictFace_eq_some_iff D (extendByLast h)).mp h₂
  have hf₂' : univ.map (extendByLast h) ∈ q.toCellScheme.faces := hf₂
  have hlab (j : Fin d.card) : ℓ (faceCell h₂ j) = d.label j := by
    by_cases hjt : d.label j = ⊤
    · by_cases hj : Fin.last n ∈ d.toCellScheme.scope j
      · -- a new top: read by a cell of graded index `(univ, N)` labelled `⊤`
        have hNk : N ≤ k := t'.grade_le c
        have hpos : 0 < N := (Nat.succ_pos n).trans_le hn
        obtain ⟨u₀, hu₀⟩ := hDl.isComplete ((univ : Finset (Fin (k + 1))), N)
          ⟨D.univ_mem_faces, hpos, by simpa using hNk.trans (Nat.le_succ k)⟩
        have hc' : D.toCellScheme.grade (faceCell h₁ c) = N := grade_faceCell h₁ c
        have hsu₀ : D.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
        obtain ⟨u, hu, hcu⟩ := hl.availability (faceCell h₁ c) u₀
          (by rw [hsu₀]; exact subset_univ _) (hc'.trans (congrArg Prod.snd hu₀).symm)
        have hu' : D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), N) :=
          hu.trans hu₀
        have hℓu : ℓ u = ⊤ := by
          have h' : ℓ (faceCell h₁ c) ≤ ℓ u := hcu
          rw [hold, hc.2.1] at h'
          exact top_le_iff.mp h'
        have hbelow (y : Fin D.card) (hy : D.toCellScheme.grade y ≤ N) :
            y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
          rw [CellScheme.mem_below, hu']
          exact Prod.mk_le_mk.mpr ⟨subset_univ _, hy⟩
        have hx : faceCell h₂ j ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
          hbelow _ ((grade_faceCell h₂ j).trans_le ((d.grade_le j).trans hn))
        have hs : faceCell h₁ r ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) :=
          hbelow _ ((grade_faceCell h₁ r).trans_le (hc.2.2 r hr))
        have hrow := hS u N hu' rfl j hj hjt
        -- the readings are those of the cells of `D` at `r` and at `j`
        change D.rowAt u (faceCell h₁ r) ≤ D.rowAt u (faceCell h₂ j) at hrow
        rw [Scheme.rowAt_of_mem hs, Scheme.rowAt_of_mem hx] at hrow
        rw [hjt]
        exact hl.eq_top_of_row_le hs hx hℓu ((hold r).trans hr) hrow
      · -- a top of the root: its label is that of `t'`
        obtain ⟨i, rfl⟩ := exists_faceCell_eq_of_last_notMem hd hj
        rw [← faceCell_faceCell h₁ h₂ ht hd i, hold, label_faceCell, label_faceCell]
    · -- a label other than `⊤` lies below the cutoff, where the receiving family keeps it
      set x : Fin D.card := faceCell h₂ j
      have hDx : D.label x = d.label j := label_faceCell h₂ j
      have hlt : D.label x < δ := hδ x (hDx ▸ hjt)
      have hmin := hcut x x rfl
      rw [min_eq_left hlt.le] at hmin
      rw [← hDx]
      rcases le_total (ℓ x) δ with hle | hle
      · rwa [min_eq_left hle] at hmin
      · rw [min_eq_right hle] at hmin
        exact absurd hmin hlt.ne'
  rw [restrictFace_of_mem q _ hf₂']
  refine congrArg some (StageType.ext ?_ fun i j hij ↦ ?_)
  · -- the scheme of the face of `q` is the face of the scheme of `D`
    change D.toScheme.comap (extendByLast h) = d.toScheme
    exact comap_toScheme_of_restrictFace h₂
  -- the label of the face at `i` is the label of `q` at the cell of `D` at `j`
  change ℓ (D.toScheme.cellMap (extendByLast h) i) = d.label j
  have hcell : D.toScheme.cellMap (extendByLast h) i = faceCell h₂ j := by
    change _ = D.toScheme.cellMap (extendByLast h) (Fin.cast _ j)
    congr 1
    exact Fin.ext hij
  rw [hcell, hlab]

variable (α) in
/-- **Top-marked carriers** at the stage `α` (a named hypothesis on stage types; open): over every
legal marked-cap context `t'` along `h` with top cap `c` and marker `r`, and every legal donor `d`
that is a one-point coface of the face of `t'` along `h`, there is a prescribed extension for the
top-marked prescription: a legal one-point extension of `t'` carrying `d` whose cells of graded
index `(univ, N)` read every new cell of `d` labelled `⊤` at least as `r`. -/
def HasTopMarkedCarriers : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (_ : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (_ : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCapContextAt h c r →
      ∃ D, IsPrescribedExtension t' h d (topMarkedPrescription t' d c r) D

variable (α) in
/-- **Compatibility of the top-marked prescriptions** at the stage `α` (open). -/
def HasCompatibleTopMarkedPrescriptions : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCapContextAt h c r →
      IsFaceCompatible t' ht d hd (topMarkedPrescription t' d c r)

/-- **Top-marked carriers from prescribed rows** and the compatibility of the top-marked
prescriptions. -/
theorem HasPrescribedFullRows.hasTopMarkedCarriers (hpr : HasPrescribedFullRows.{u} α)
    (hcomp : HasCompatibleTopMarkedPrescriptions.{u} α) : HasTopMarkedCarriers.{u} α :=
  fun _ _ t' h t ht d hd c r ht' hd' hctx ↦
    hpr t' h t ht d hd ht' hd' _ (hcomp t' h t ht d hd c r ht' hd' hctx)

/-- **Compatibility is necessary** for top-marked carriers. -/
theorem HasTopMarkedCarriers.hasCompatibleTopMarkedPrescriptions
    (hcar : HasTopMarkedCarriers.{u} α) : HasCompatibleTopMarkedPrescriptions.{u} α :=
  fun _ _ t' h t ht d hd c r ht' hd' hctx ↦
    let ⟨_, hD⟩ := hcar t' h t ht d hd c r ht' hd' hctx
    hD.isFaceCompatible ht hd

/-- **Top-marked carriers where the prescription is empty**: under the coatom extension property
at `α`, if no new cell of `d` is labelled `⊤`, the exact pinned extension of `t'` carrying `d` is
a prescribed extension for the top-marked prescription, which asks nothing there. -/
theorem HasCoatomExtensions.exists_isPrescribedExtension_topMarkedPrescription
    (hext : HasCoatomExtensions.{u} α) {t' : StageType.{u} α k} (ht' : t'.IsLegal)
    {h : Fin n ↪ Fin k} {t : StageType.{u} α n} (ht : restrictFace h t' = some t)
    {d : StageType.{u} α (n + 1)} (hd' : d.IsLegal) (hd : restrictFace Fin.castSuccEmb d = some t)
    (c r : Fin t'.card)
    (hnt : ∀ j : Fin d.card, Fin.last n ∈ d.toCellScheme.scope j → d.label j ≠ ⊤) :
    ∃ D, IsPrescribedExtension t' h d (topMarkedPrescription t' d c r) D := by
  obtain ⟨D, hD, h₁, h₂⟩ := exists_pinned_extension hext ht' ht hd' hd
  exact ⟨D, hD, h₁, h₂, comap_toScheme_of_restrictFace h₁, comap_toScheme_of_restrictFace h₂,
    fun _ _ _ _ j hj htop ↦ absurd htop (hnt j hj)⟩

end StageType

end VaughtConjecture

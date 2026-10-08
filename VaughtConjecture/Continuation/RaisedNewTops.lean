/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrier
import VaughtConjecture.Continuation.TopReadingApexSeed

/-!
# Raising the new tops: what a restricted reading layer needs of the donor

Roadmap, Layer 3 ((R3) of the table of 3.4).

A **restricted reading layer** at a marked cap ties the lawful labellings only at the marked
cells: every cell of graded index `(univ, N)` (`N` the grade of the top cap `c`) reads every new
cell of the donor labelled `⊤` at least as the marker `r`, and nothing else is asked of its rows.
This is the top-marked prescription (`StageType.topMarkedPrescription`); the doubling of a type
with itself is the symmetric case, where the tied pairs are the two copies of one cell.

**What the obstruction at `seedTR` refutes.**  `TowerProfile.not_extendsFromBoundary_seedTR` applies
to every such layer that is a sheet layer at the grade `4` over the profile layer (the entries
lawful, not `⊤` at the new top, and reading; the reading marks among them): the extension from the
boundary of the coatom and of `(univ, 3)` fails.  That extension is a step of one bountifulness
proof, not a law: bountifulness is the capped lift from each coatom alone
(`CellScheme.Rows.isBountiful_of_coatoms`), and a lift from the coatom may choose the cells off
the coatom, the new top included.  The tie is across grades (the marker at the grade of the layer
on the coatom, the new top below `(univ, 3)`), so the boundary fixes both of its ends.  In the
doubling a tie at the grade `j` of the layer joins the two copies of one cell of that grade, one of
them off the boundary, and the ties at lower grades already hold below `(univ, j - 1)`.  What the
coatom lift needs instead is the following face condition.

**The raise requirement** (`StageType.RaisesNewTops t' ht d hd r s`): every lawful labelling `a` of
`t'` with `a r = a s = ⊤` has a lawful labelling of `d` that agrees with `a` on the root and labels
every new top of `d` with `⊤`.

* **Necessity** (`StageType.exists_extend_top_of_reads`, compiled in this repository (theorem
  named)): in a legal one-point extension `D` of `t'` carrying `d` whose cells of graded index
  `(univ, N)` read the new cells in question at least as `r`, every lawful labelling of `t'` with
  `⊤` at `r` and at a cell `s` of grade `N` extends to a lawful labelling of `D` with `⊤` at those
  cells (extension from the face at the cap `⊥`, availability from `s`, the reading at a cell
  labelled `⊤`).  Hence a top-marked carrier gives the raise requirement
  (`StageType.IsPrescribedExtension.raisesNewTops`), and top-marked carriers give it at every
  legal marked-cap context, for `s` the top cap or any cell of its grade
  (`StageType.HasTopMarkedCarriers.raisesNewTops`); the universal form is the named statement
  `StageType.HasRaisingMarkedCaps` (open), implied by `StageType.HasTopMarkedCarriers`
  (`StageType.HasTopMarkedCarriers.hasRaisingMarkedCaps`).
* **A refutation schema** (`StageType.not_raisesNewTops_of_row_le`,
  `StageType.not_isPrescribedExtension_of_row_le`, compiled): if a new top `j` of `d` reads a root
  cell `y₁` at most as a root cell `y₂` of grade at most that of `y₁`, and some lawful labelling of
  `t'` with `⊤` at `r` and `s` labels `y₁` strictly above `y₂`, the raise fails (locality at `j`
  labelled `⊤`), and no top-marked carrier exists for `(t', d)`.  An instance at a legal marked-cap
  context is not compiled (prospective).
* **No inversion under an apex** (`StageType.le_of_label_le_addApex`, `StageType.le_of_tie_addApex`,
  compiled): a lawful labelling of `t₀.addApex` with `⊤` at the apex keeps the order of the labels
  of two cells `z₁`, `z₂` with `grade z₂ ≤ grade z₁` (the apex row is the code of the labels), so
  with `s` the apex the schema never applies there.
  An instance of the schema with `s` the top cap needs a top cap whose row separates two root cells
  that its labels tie.
* **Rigid roots** (`StageType.raisesNewTops_of_rigid`, compiled): if every lawful labelling of `t'`
  with `⊤` at `r` and `s` agrees with the labels of `t'` on the root, the labels of `d` raise.
* **At `TL`** (`TwoFaceLiftExistsCounterexample.eq_label_TL_of_apex`,
  `TwoFaceLiftExistsCounterexample.raisesNewTops_TL`, `TopReadingApexExample.raisesNewTops_seedTR`,
  `TwoFaceLiftExistsCounterexample.isMarkedCapContextAt_raisesNewTops_TL`, compiled): a lawful
  labelling of `TL` with `⊤` at the apex is the labelling of `TL` (the apex row reads every other
  cell as `⊥`), so the raise requirement holds at `TL` along every embedding for every donor; at
  `seedTR` for the donor `rightType`, and at every marked-cap context of `TL` (embeddings of at most
  two points) for every donor.  This is feasibility of a necessary condition only: no restricted
  layer at `seedTR` is constructed here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-! ### The raise requirement -/

/-- The **raise requirement** for `t'` along `h` (face `t`), the donor `d`, the marker `r` and a
cell `s`: every lawful labelling of `t'` labelling `r` and `s` with `⊤` has a lawful labelling of
`d` agreeing with it on the root and labelling every new cell of `d` labelled `⊤` with `⊤`. -/
def RaisesNewTops (t' : StageType.{u} α k) {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (r s : Fin t'.card) : Prop :=
  ∀ a : Fin t'.card → Label.{u}, t'.rows.IsLawful a → a r = ⊤ → a s = ⊤ →
    ∃ b : Fin d.card → Label.{u}, d.rows.IsLawful b ∧
      (∀ i, b (faceCell hd i) = a (faceCell ht i)) ∧
      ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → b j = ⊤

/-- **The reading layer forces the raise.**  Let `D` be a legal one-point extension of `t'`
carrying `d`, `s` a cell of `t'` of grade `N`, `r` a cell of `t'` of grade at most `N`, and `P` a
set of cells of `d` of grade at most `N` that every cell of `D` of graded index `(univ, N)` reads at
least as `r`.  Every lawful labelling of `t'` labelling `r` and `s` with `⊤` extends to a lawful
labelling of `D` labelling the cells of `P` with `⊤`. -/
theorem exists_extend_top_of_reads {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} {D : StageType.{u} α (k + 1)} (hD : D.IsLegal)
    (h₁ : restrictFace Fin.castSuccEmb D = some t') (h₂ : restrictFace (extendByLast h) D = some d)
    {N : ℕ} {r s : Fin t'.card} (hs : t'.toCellScheme.grade s = N)
    (hr : t'.toCellScheme.grade r ≤ N) {P : Fin d.card → Prop}
    (hP : ∀ j, P j → d.toCellScheme.grade j ≤ N)
    (hreads : ∀ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), N) →
      ∀ j, P j → D.rowAt u (faceCell h₁ r) ≤ D.rowAt u (faceCell h₂ j))
    {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a) (har : a r = ⊤) (has : a s = ⊤) :
    ∃ a' : Fin D.card → Label.{u}, D.rows.IsLawful a' ∧ (∀ z, a' (faceCell h₁ z) = a z) ∧
      ∀ j, P j → a' (faceCell h₂ j) = ⊤ := by
  obtain ⟨a', ha', hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁ ha
  refine ⟨a', ha', hext, fun j hj ↦ ?_⟩
  have hNk : N ≤ k := hs ▸ t'.grade_le s
  have hpos : 0 < N := hs ▸ t'.isWellFormed.isWellFormed.grade_pos s
  obtain ⟨u₀, hu₀⟩ := hD.isComplete ((univ : Finset (Fin (k + 1))), N)
    ⟨D.univ_mem_faces, hpos, by simpa using hNk.trans (Nat.le_succ k)⟩
  have hsN : D.toCellScheme.grade (faceCell h₁ s) = N := (grade_faceCell h₁ s).trans hs
  obtain ⟨u, hu, hsu⟩ := ha'.availability (faceCell h₁ s) u₀
    (by rw [show D.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]; exact subset_univ _)
    (hsN.trans (congrArg Prod.snd hu₀).symm)
  have hu' : D.toCellScheme.gradedIndex u = ((univ : Finset (Fin (k + 1))), N) := hu.trans hu₀
  have hau : a' u = ⊤ := top_le_iff.mp (by rw [← has, ← hext]; exact hsu)
  have hbelow (y : Fin D.card) (hy : D.toCellScheme.grade y ≤ N) :
      y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu']
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, hy⟩
  have hrb := hbelow _ ((grade_faceCell h₁ r).trans_le hr)
  have hjb := hbelow _ ((grade_faceCell h₂ j).trans_le (hP j hj))
  have hrow := hreads u hu' j hj
  rw [Scheme.rowAt_of_mem hrb, Scheme.rowAt_of_mem hjb] at hrow
  exact ha'.eq_top_of_row_le hrb hjb hau (by rw [hext, har]) hrow

/-- **A top-marked carrier gives the raise requirement**, for the marker `r` and every cell `s`
of the grade of the top cap `c`. -/
theorem IsPrescribedExtension.raisesNewTops {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} {d : StageType.{u} α (n + 1)} {c r s : Fin t'.card}
    (ht : restrictFace h t' = some t) (hd : restrictFace Fin.castSuccEmb d = some t)
    (hc : t'.IsTopCap c) (hr : t'.label r = ⊤) (hn : n + 1 ≤ t'.toCellScheme.grade c)
    (hs : t'.toCellScheme.grade s = t'.toCellScheme.grade c) {D : StageType.{u} α (k + 1)}
    (hD : IsPrescribedExtension t' h d (topMarkedPrescription t' d c r) D) :
    t'.RaisesNewTops ht d hd r s := by
  obtain ⟨hDl, h₁, h₂, he₁, he₂, hS⟩ := hD
  intro a ha har has
  obtain ⟨a', ha', hext, htop⟩ := exists_extend_top_of_reads hDl h₁ h₂ hs (hc.2.2 r hr)
    (P := fun j ↦ Fin.last n ∈ d.toCellScheme.scope j ∧ d.label j = ⊤)
    (fun j _ ↦ (d.grade_le j).trans hn)
    (fun u hu j hj ↦ by
      have hrow := hS u _ hu rfl j hj.1 hj.2
      exact hrow) ha har has
  refine ⟨fun j ↦ a' (faceCell h₂ j), isLawful_comp_faceCell h₂ ha', fun i ↦ ?_,
    fun j hj hjt ↦ htop j ⟨hj, hjt⟩⟩
  change a' (faceCell h₂ (faceCell hd i)) = a (faceCell ht i)
  rw [← faceCell_faceCell h₁ h₂ ht hd i, hext]

/-- **Top-marked carriers give the raise requirement at every legal marked-cap context**, for the
marker `r` and every cell `s` of the grade of the top cap `c` (the top cap itself among them). -/
theorem HasTopMarkedCarriers.raisesNewTops (hcar : HasTopMarkedCarriers.{u} α)
    {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {c r s : Fin t'.card} (ht' : t'.IsLegal)
    (hd' : d.IsLegal) (hctx : t'.IsMarkedCapContextAt h c r)
    (hs : t'.toCellScheme.grade s = t'.toCellScheme.grade c) :
    t'.RaisesNewTops ht d hd r s :=
  let ⟨_, hD⟩ := hcar t' h t ht d hd c r ht' hd' hctx
  hD.raisesNewTops ht hd hctx.1 hctx.2.1.1 hctx.2.2.1.le hs

variable (α) in
/-- **Raising marked caps** at the stage `α` (a named statement; open): at every legal marked-cap
context `t'` along `h` with top cap `c` and marker `r`, every legal donor `d` (a one-point coface
of the face of `t'` along `h`) meets the raise requirement for `r` and `c`.  It is necessary for
top-marked carriers (`StageType.HasTopMarkedCarriers.hasRaisingMarkedCaps`). -/
def HasRaisingMarkedCaps : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (ht : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (hd : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCapContextAt h c r → t'.RaisesNewTops ht d hd r c

/-- **Top-marked carriers raise the marked caps.** -/
theorem HasTopMarkedCarriers.hasRaisingMarkedCaps (hcar : HasTopMarkedCarriers.{u} α) :
    HasRaisingMarkedCaps.{u} α := fun _ _ _ _ _ ht _ hd _ _ ht' hd' hctx ↦
  hcar.raisesNewTops ht hd ht' hd' hctx rfl

/-! ### When the raise fails, and when it holds -/

/-- **A refutation schema for the raise.**  Let `j` be a new cell of `d` labelled `⊤` whose row
reads the root cell `y₁` at most as the root cell `y₂`, the grade of `y₂` at most that of `y₁`.  If
some lawful labelling of `t'` labelling `r` and `s` with `⊤` labels `y₁` strictly above `y₂`, the
raise requirement fails: a lawful labelling of `d` labelling `j` with `⊤` labels `y₁` at most as
`y₂` (locality at `j`). -/
theorem not_raisesNewTops_of_row_le {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {r s : Fin t'.card}
    {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a) (har : a r = ⊤) (has : a s = ⊤)
    {j : Fin d.card} (hj : Fin.last n ∈ d.toCellScheme.scope j) (hjt : d.label j = ⊤)
    {y₁ y₂ : Fin t.card}
    (hy₁ : faceCell hd y₁ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hy₂ : faceCell hd y₂ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hrow : d.rows.row j ⟨_, hy₁⟩ ≤ d.rows.row j ⟨_, hy₂⟩)
    (hg : t.toCellScheme.grade y₂ ≤ t.toCellScheme.grade y₁)
    (hlt : a (faceCell ht y₂) < a (faceCell ht y₁)) :
    ¬ t'.RaisesNewTops ht d hd r s := by
  intro hraise
  obtain ⟨b, hb, hagree, htop⟩ := hraise a ha har has
  have hloc := (hb.locality j).le_of_le (d := ⟨_, hy₁⟩) (d' := ⟨_, hy₂⟩) hrow
    (by rw [grade_faceCell, grade_faceCell]; exact hg)
  change min (b (faceCell hd y₁)) (b j) ≤ min (b (faceCell hd y₂)) (b j) at hloc
  rw [htop j hj hjt, min_top_right, min_top_right, hagree, hagree] at hloc
  exact absurd hloc (not_le.mpr hlt)

/-- **No top-marked carrier where the raise fails**: under the hypotheses of
`StageType.not_raisesNewTops_of_row_le`, with `c` a top cap, `r` labelled `⊤`, `n + 1` at most the
grade of `c` and `s` of that grade, `t'` has no top-marked carrier for `d`. -/
theorem not_isPrescribedExtension_of_row_le {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {c r s : Fin t'.card} (hc : t'.IsTopCap c)
    (hr : t'.label r = ⊤) (hn : n + 1 ≤ t'.toCellScheme.grade c)
    (hs : t'.toCellScheme.grade s = t'.toCellScheme.grade c)
    {a : Fin t'.card → Label.{u}} (ha : t'.rows.IsLawful a) (har : a r = ⊤) (has : a s = ⊤)
    {j : Fin d.card} (hj : Fin.last n ∈ d.toCellScheme.scope j) (hjt : d.label j = ⊤)
    {y₁ y₂ : Fin t.card}
    (hy₁ : faceCell hd y₁ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hy₂ : faceCell hd y₂ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hrow : d.rows.row j ⟨_, hy₁⟩ ≤ d.rows.row j ⟨_, hy₂⟩)
    (hg : t.toCellScheme.grade y₂ ≤ t.toCellScheme.grade y₁)
    (hlt : a (faceCell ht y₂) < a (faceCell ht y₁)) :
    ¬ ∃ D, IsPrescribedExtension t' h d (topMarkedPrescription t' d c r) D := fun ⟨_, hD⟩ ↦
  not_raisesNewTops_of_row_le ht hd ha har has hj hjt hy₁ hy₂ hrow hg hlt
    (hD.raisesNewTops ht hd hc hr hn hs)

/-- **Rigid roots raise.**  If every lawful labelling of `t'` labelling `r` and `s` with `⊤` agrees
with the labels of `t'` on the root, the labels of `d` meet the raise requirement. -/
theorem raisesNewTops_of_rigid {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {t : StageType.{u} α n} (ht : restrictFace h t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t) {r s : Fin t'.card}
    (hrigid : ∀ a : Fin t'.card → Label.{u}, t'.rows.IsLawful a → a r = ⊤ → a s = ⊤ →
      ∀ i, a (faceCell ht i) = t.label i) :
    t'.RaisesNewTops ht d hd r s := fun a ha har has ↦
  ⟨d.label, d.isLawful, fun i ↦ by rw [label_faceCell, hrigid a ha har has], fun _ _ hj ↦ hj⟩

/-! ### No inversion under an apex -/

section Apex

variable {t₀ : StageType.{u} α k} (ht₀ : t₀.IsLegalBelowFullGrade) (hk : 0 < k)

/-- The apex row reads every cell at the code of its label. -/
theorem row_addApex_last_eq {z : Fin (t₀.addApex ht₀ hk).card}
    (hz : z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _))) :
    (t₀.addApex ht₀ hk).rows.row (Fin.last _) ⟨z, hz⟩ =
      blockEncode (apexCodes ht₀) k ((t₀.addApex ht₀ hk).label z) := by
  -- the rows of `t₀.addApex` are those of `appendFullCell`
  change (t₀.toScheme.appendFullCell k (apexRow ht₀) ht₀.not_le).rows.row (Fin.last _) ⟨z, hz⟩ = _
  rw [Scheme.appendFullCell_row_last]
  change Fin (t₀.card + 1) at z
  induction z using Fin.lastCases with
  | last => rw [apexRow_last, addApex_label_last]
  | cast d => rw [apexRow_castSucc, addApex_label_castSucc]

/-- **A labelling with `⊤` at the apex keeps the order of the labels**: if the apex is labelled
`⊤`, a cell labelled at most another of no larger grade is labelled at most it (locality at the
apex, whose row is the code of the labels). -/
theorem le_of_label_le_addApex {a : Fin (t₀.addApex ht₀ hk).card → Label.{u}}
    (ha : (t₀.addApex ht₀ hk).rows.IsLawful a) (htop : a (Fin.last _) = ⊤)
    {z₁ z₂ : Fin (t₀.addApex ht₀ hk).card}
    (hl : (t₀.addApex ht₀ hk).label z₁ ≤ (t₀.addApex ht₀ hk).label z₂)
    (hg : (t₀.addApex ht₀ hk).toCellScheme.grade z₂ ≤
      (t₀.addApex ht₀ hk).toCellScheme.grade z₁) : a z₁ ≤ a z₂ := by
  have hlast : (t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _) = (univ, k) :=
    addApex_gradedIndex_last ht₀ hk
  have hmem (z : Fin (t₀.addApex ht₀ hk).card) : z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _)) := by
    rw [CellScheme.mem_below, hlast]
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t₀.addApex ht₀ hk).grade_le z⟩
  have h := (ha.locality (Fin.last _)).le_of_le (d := ⟨z₁, hmem z₁⟩) (d' := ⟨z₂, hmem z₂⟩)
    (by rw [row_addApex_last_eq, row_addApex_last_eq]; exact monotone_blockEncode hl) hg
  change min (a z₁) (a (Fin.last _)) ≤ min (a z₂) (a (Fin.last _)) at h
  rwa [htop, min_top_right, min_top_right] at h

/-- **The refutation schema never applies under an apex at the apex.**  Over `t₀.addApex` along
`h`, let a new top `j` of a donor `d` read the root cell `y₁` at most as the root cell `y₂`, of
grade at most that of `y₁`.  Then every lawful labelling with `⊤` at the apex labels `y₁` at most
as `y₂`: the labels of `d` tie them (locality at `j`), the labels of the root are those of `d`,
and the apex keeps their order. -/
theorem le_of_tie_addApex {h : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace h (t₀.addApex ht₀ hk) = some t) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace Fin.castSuccEmb d = some t)
    {a : Fin (t₀.addApex ht₀ hk).card → Label.{u}} (ha : (t₀.addApex ht₀ hk).rows.IsLawful a)
    (htop : a (Fin.last _) = ⊤) {j : Fin d.card} (hjt : d.label j = ⊤) {y₁ y₂ : Fin t.card}
    (hy₁ : faceCell hd y₁ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hy₂ : faceCell hd y₂ ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex j))
    (hrow : d.rows.row j ⟨_, hy₁⟩ ≤ d.rows.row j ⟨_, hy₂⟩)
    (hg : t.toCellScheme.grade y₂ ≤ t.toCellScheme.grade y₁) :
    a (faceCell ht y₁) ≤ a (faceCell ht y₂) := by
  have hloc := (d.isLawful.locality j).le_of_le (d := ⟨_, hy₁⟩) (d' := ⟨_, hy₂⟩) hrow
    (by rw [grade_faceCell, grade_faceCell]; exact hg)
  change min (d.label (faceCell hd y₁)) (d.label j) ≤
    min (d.label (faceCell hd y₂)) (d.label j) at hloc
  rw [hjt, min_top_right, min_top_right, label_faceCell, label_faceCell] at hloc
  refine le_of_label_le_addApex ht₀ hk ha htop ?_ ?_
  · rwa [label_faceCell, label_faceCell]
  · rw [grade_faceCell, grade_faceCell]
    exact hg

end Apex

end StageType

/-! ### The raise at `TL` and at `seedTR` -/

namespace TwoFaceLiftExistsCounterexample

variable {α : Ordinal.{u}}

/-- The only cell of `TL` labelled `⊤` is the apex. -/
theorem eq_last_of_label_TL {x : Fin (TL α).card} (hx : (TL α).label x = ⊤) :
    x = Fin.last _ := by
  -- `TL` has the cells of `TL₀` and the apex
  change Fin ((TL₀ α).card + 1) at x
  induction x using Fin.lastCases with
  | last => rfl
  | cast d =>
    exact absurd ((StageType.addApex_label_castSucc (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) d).symm.trans hx) bot_ne_top

/-- **A lawful labelling of `TL` labelling the apex with `⊤` is the labelling of `TL`**: the apex
row reads every other cell as `⊥`, so locality at the apex sends every other cell to `⊥`. -/
theorem eq_label_TL_of_apex {a : Fin (TL α).card → Label.{u}} (ha : (TL α).rows.IsLawful a)
    (htop : a (Fin.last _) = ⊤) : a = (TL α).label := by
  funext z
  by_cases hz : z = Fin.last _
  · subst hz
    rw [htop]
    exact (StageType.addApex_label_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega)).symm
  · have hzb : z ∈ (TL α).toCellScheme.below ((TL α).toCellScheme.gradedIndex (Fin.last _)) := by
      have hg : (TL α).toCellScheme.gradedIndex (Fin.last _) = (univ, 4) :=
        StageType.addApex_gradedIndex_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega)
      rw [CellScheme.mem_below, hg]
      exact Prod.mk_le_mk.mpr ⟨subset_univ _, (TL α).grade_le z⟩
    have hrow : (TL α).rows.row (Fin.last _) ⟨z, hzb⟩ = ⊥ := by
      rw [← Scheme.rowAt_of_mem hzb]
      exact StageType.rowAt_addApex_last_of_ne (t := TL₀ α) isLegalBelowFullGrade_SL (by omega)
        (fun _ ↦ rfl) hz
    have h := (ha.locality (Fin.last _)).eq_bot (d := ⟨z, hzb⟩) hrow
    change min (a z) (a (Fin.last _)) = ⊥ at h
    rw [htop, min_top_right] at h
    rw [h]
    -- the other cells of `TL` are those of `TL₀`, labelled `⊥`
    change Fin ((TL₀ α).card + 1) at z
    induction z using Fin.lastCases with
    | last => exact absurd rfl hz
    | cast d =>
      exact (StageType.addApex_label_castSucc (t := TL₀ α) isLegalBelowFullGrade_SL
        (by omega) d).symm

/-- **The raise at `TL`**: along every embedding and for every donor, the raise requirement holds
at the apex (marker and top cap): the root is rigid. -/
theorem raisesNewTops_TL {n : ℕ} {h : Fin n ↪ Fin 4} {t : StageType.{u} α n}
    (ht : StageType.restrictFace h (TL α) = some t) {d : StageType.{u} α (n + 1)}
    (hd : StageType.restrictFace Fin.castSuccEmb d = some t) :
    (TL α).RaisesNewTops ht d hd (Fin.last _) (Fin.last _) :=
  StageType.raisesNewTops_of_rigid ht hd fun a ha har _ i ↦ by
    rw [eq_label_TL_of_apex ha har, StageType.label_faceCell]

/-- **At the marked-cap contexts of `TL`**: along every embedding of at most two points, `TL` is a
marked-cap context with the apex as top cap and marker, and every donor meets the raise
requirement there. -/
theorem isMarkedCapContextAt_raisesNewTops_TL {n : ℕ} (h : Fin n ↪ Fin 4) (hn : n ≤ 2)
    {t : StageType.{u} α n} (ht : StageType.restrictFace h (TL α) = some t)
    {d : StageType.{u} α (n + 1)} (hd : StageType.restrictFace Fin.castSuccEmb d = some t) :
    (TL α).IsMarkedCapContextAt h (Fin.last _) (Fin.last _) ∧
      (TL α).RaisesNewTops ht d hd (Fin.last _) (Fin.last _) := by
  obtain ⟨-, -, c, r, hc, hr, hgc, hroot⟩ := TowerProfile.isMarkedCapContext_TL α h hn
  obtain rfl := eq_last_of_label_TL hc.2.1
  obtain rfl := eq_last_of_label_TL hr.1
  exact ⟨⟨hc, hr, hgc, hroot⟩, raisesNewTops_TL ht hd⟩

end TwoFaceLiftExistsCounterexample

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample

/-- **The raise at `seedTR`**: the right coatom type `rightType` meets the raise requirement over
`TL` along the face of `T5`, at the apex of `TL`. -/
theorem raisesNewTops_seedTR (α : Ordinal.{u}) :
    (TL α).RaisesNewTops (restrictFace_TL α) (rightType α) (restrictFace_rightType α)
      (Fin.last _) (Fin.last _) :=
  raisesNewTops_TL _ _

end TopReadingApexExample

end VaughtConjecture

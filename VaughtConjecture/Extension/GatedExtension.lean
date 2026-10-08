/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Basic
import VaughtConjecture.Extension.Gate
import VaughtConjecture.Stage.Legal

/-!
# Gated extensions

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple with
the display's bottom pattern) and the vocabulary of Layer 3 (private context, private cap, display,
gate); the stage-level form of the gate data of `VaughtConjecture.Extension.Gate`.

**Setting.**  A legal stage type `P` on `n` points (the type of the private context), a face
`f : Fin m ↪ Fin n` of `P` (the root), and a stage type `d` on `m + 1` points (the donor, the root
followed by a new point).  The scheme to be realized lives on `n + 1` points, the new point being
the last; its **private face** is taken along `Fin.castSuccEmb` and its **donor face** along
`extendByLast f`, the face `f` followed by the new point.  The **new cells** of the donor are its
cells whose scope contains its last point.

* A **gated extension** of `P` over `f` with donor `d` (`StageType.GatedExtension P f d`) is a
  legal stage type, the **display**, on `n + 1` points whose two faces are literally `P` and `d`
  (the display of the roadmap is the labelling of the constructed scheme; here it is that scheme
  with that labelling, as a stage type),
  together with two cells: the **gate**, of graded index `(univ, n)` (full scope, grade the private
  arity `n`), and the **cap**, of graded index `(univ.map Fin.castSuccEmb, n)` (the private cap,
  full scope on the private points).  The other cells of graded index `(univ, n)`, the **twins** of
  the gate, are labelled `⊥` in the display, and the row of the gate reads every new donor cell as
  in `CellScheme.Rows.IsGate`, the private cells being those visible through `Fin.castSuccEmb` and
  the donor cells those visible through `extendByLast f`.  The display labels the gate at least as
  the cap, so not `⊥` (`GatedExtension.cap_le_gate`, `GatedExtension.label_gate_ne_bot`): the
  display has the bottom pattern that gate recovery reads.
* The donor is **anchored** in `P` below a cell `C` (`StageType.IsAnchored P C d`) when every
  new donor cell whose label is neither `⊥` nor at least `P.label C` is labelled
  `vr_n(P.label z, i)` (`Label.visibilityReplace n i`) for some cell `z` of `P` (its **anchor**)
  and some `i ≤ n`.  The anchor may be self-visible at `n`, and `i = n` is allowed; an anchor whose
  label is not self-visible at `n` (`¬ Label.IsSelfVisible n (P.label z)`) is a **proper anchor**.
  When `C` has grade `n`, as in `HasGatedPinnedExtensions`, its label is self-visible at `n`, so
  the anchor of a donor label below `P.label C` is itself labelled below `P.label C`
  (`Label.le_visibilityReplace_of_le`).  This is exactly what the readings of the gate force: a
  gated extension whose cap carries the label of `C` has an anchored donor
  (`GatedExtension.isAnchored`).
* The **gated pinned extension property** at stage `α` (`StageType.HasGatedPinnedExtensions α`)
  asks for a gated extension, with cap labelled as a given non-bottom cell `C` of graded index
  `(univ, n)` of `P`, for every legal `P`, every face `f` of `P` with restriction `p`, and every
  legal one-point coface `d` of `p` anchored in `P` below `C`, when `m + 1 < n`.

`HasGatedPinnedExtensions` is a universal hypothesis, in the pattern of
`StageType.HasCoatomExtensions`, and it is **false at every stage**
(`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`, in
`VaughtConjecture.Extension.GatedExtensionCounterexample`).  The legal private type
`GatedExtensionCounterexample.P α` on two points, with two cells of full scope and full grade
ordered oppositely by two lawful labellings in the cap ball of its labelling at `2`, has no gated
extension, whatever the face and the donor (`GatedExtensionCounterexample.isEmpty_gatedExtension`):
in every legal one-point extension of it, every cell of graded index `(univ, 2)` has a twin not
labelled `⊥` (`GatedExtensionCounterexample.exists_twin_label_ne_bot`).  The capped lifts that
bountifulness asks for keep the twins at `⊥`, so availability makes the gate dominate both cells,
and the one witness of the gate cannot read both orders.  The definition is kept to state that
refutation.  The structure `GatedExtension` is inhabited, for a private type with a unique cell of
full scope and full grade (`StageType.GatedExtension.instance_two_zero`), and the statements about
a given gated extension, here and in `VaughtConjecture.Realization.GateRecovery`, stand.

**The coupled gate.**  A **coupled gated extension** (`StageType.CoupledGatedExtension`) has the
same data with the clause on the twins replaced by a condition on the rows of the display: every
twin `t` of the gate `G` reads `G` at least as it reads the cap `C`, `row t C ≤ row t G`
(`CellScheme.Rows.TwinsReadGate`).  Then the gate is at least the cap in every lawful labelling of
the rows of the display (`CoupledGatedExtension.cap_le_gate`), by availability and locality alone,
so the display does not label the gate `⊥` (`CoupledGatedExtension.label_gate_ne_bot`), and the
readings of the gate still force anchoring (`CoupledGatedExtension.isAnchored`).  The **coupled
gated pinned extension property** (`StageType.HasCoupledGatedPinnedExtensions α`) asks for a coupled
gated extension for the same inputs.  It is a named hypothesis, and it is **false at every stage
above `1`** (`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`): at a
private type with a proper anchor below the cap, the readings of the gate carry a lawful private
labelling that drops the anchor and keeps the cap to a labelling of the donor face that the donor's
rows forbid (`StageType.CoupledGatedExtension.carriesBottoms`).  The definition is kept to state
that refutation and the theorems conditional on it.  It holds at the input that refutes the gated
pinned extension property: over the empty root, with the donor `P α|{0}` and the cap `3`, the
private type `GatedExtensionCounterexample.P α` has a coupled gated extension
(`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`), whose gate has a twin not labelled
`⊥` (`CoupledGateExamples.exists_coupledGatedExtension`; the display labels it `⊤`).  Every legal
one-point extension of `P α` has such a twin
(`GatedExtensionCounterexample.exists_twin_label_ne_bot`).  It also holds at `P α` with the donor
labelled `⊤` (`CoupledGateInstance.coupledGatedPinnedExtension_donor`).  **Cap lowering**, stated in
the docstring of `StageType.HasCoupledGatedPinnedExtensions`, is a requirement of the construction
at the lifts from faces containing the new point; the refutation does not use it.

**Readings in the own block.**  The row of a cell `C` **reads a label `l` in its own block**
(`StageType.ReadsInOwnBlock`) when it reads some cell below `C` labelled `l` in the block of its
reading of `C` itself; a lawful labelling that keeps `C` keeps such a cell
(`StageType.ReadsInOwnBlock.exists_ne_bot`).  The anchoring and the bottom transport condition are
also stated at a grade `k` (`StageType.IsAnchoredAt`, `StageType.CarriesBottomsAt`; at `k = n`
they are `IsAnchored` and `CarriesBottoms`), and the condition at `k` holds at a cap of graded
index `(univ, k)` that reads an anchor of every donor label below it in its own block
(`StageType.carriesBottomsAt_of_readsInOwnBlock`; at the arity,
`StageType.carriesBottoms_of_row_mem_block`).  This serves only anchors in one block: two labels
read in the own block, strictly below the label of `C` and not self-visible at its grade, are
visibility replacements of each other (`StageType.eq_visibilityReplace_of_readsInOwnBlock`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A **gated extension** of a stage type `P` on `n` points over the face `f`, with donor
`d` on `m + 1` points: a legal **display** on `n + 1` points whose faces along `Fin.castSuccEmb`
and `extendByLast f` are literally `P` and `d`, with a **gate** of graded index `(univ, n)` whose
twins are labelled `⊥` and whose row reads the new donor cells against the **cap**, of graded index
`(univ.map Fin.castSuccEmb, n)`. -/
structure GatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gate. -/
  gate : Fin display.card
  /-- The cap, the private cap seen in the display. -/
  cap : Fin display.card
  /-- The gate has full scope and grade `n`. -/
  gradedIndex_gate : display.toCellScheme.gradedIndex gate = (univ, n)
  /-- The cap has full scope on the private points and grade `n`. -/
  gradedIndex_cap : display.toCellScheme.gradedIndex cap = (univ.map Fin.castSuccEmb, n)
  /-- The twins of the gate are labelled `⊥` in the display. -/
  label_twin : ∀ t, display.toCellScheme.gradedIndex t = (univ, n) → t ≠ gate →
    display.label t = ⊥
  /-- The gate data: the row of the gate reads every new donor cell. -/
  isGate : display.rows.IsGate gate cap (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    (display.toCellScheme.visible (Set.range (extendByLast f))) display.label

/-- The donor `d` is **anchored** in `P` below the cell `C`: every new donor cell whose label is
neither `⊥` nor at least that of `C` is labelled `vr_n(P.label z, i)` for an anchor `z` of `P`
and some `i ≤ n`. -/
def IsAnchored (P : StageType.{u} α n) (C : Fin P.card) (d : StageType.{u} α (m + 1)) : Prop :=
  ∀ j : Fin d.card, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
    ∃ z : Fin P.card, ∃ i ≤ n, d.label j = visibilityReplace n i (P.label z)

/-- **Donors without proper new labels are anchored**: if every new cell of the donor `d` (a cell
whose scope contains the new point) is labelled `⊥` or `⊤`, then `d` is anchored in every `P` below
every cell `C`; no anchor is needed. -/
theorem isAnchored_of_forall_label_eq_bot_or_top
    (P : StageType.{u} α n) (C : Fin P.card) {d : StageType.{u} α (m + 1)}
    (hd : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j = ⊥ ∨ d.label j = ⊤) :
    IsAnchored P C d := by
  intro j hj hbot hlt
  rcases hd j hj with h | h
  · exact absurd h hbot
  · exact absurd (h ▸ hlt) not_top_lt

variable (α) in
/-- The **gated pinned extension property** at stage `α`: for every legal `P` on `n` points, every
face `f` of `P` with restriction `p`, every legal one-point coface `d` of `p`, and every cell `C` of
`P` of graded index `(univ, n)` not labelled `⊥` below which `d` is anchored, if `m + 1 < n` there
is a gated extension of `P` over `f` with donor `d` whose cap carries the label of `C`.

This universal hypothesis is false at every stage
(`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`): it fails at `n = 2` over the empty
root with a donor whose new cell is labelled `⊥`, for a private type with two cells of full scope
and full grade ordered oppositely by two lawful labellings in the cap ball of its labelling at `2`
(`GatedExtensionCounterexample.P α`); the labels `⊥` of the twins of the gate are incompatible
with the bountifulness of the display. -/
def HasGatedPinnedExtensions : Prop :=
  ∀ {n m : ℕ} (P : StageType.{u} α n) (f : Fin m ↪ Fin n) (p : StageType.{u} α m)
    (d : StageType.{u} α (m + 1)) (C : Fin P.card),
    P.IsLegal → restrictFace f P = some p → d.IsLegal → restrictFace Fin.castSuccEmb d = some p →
    P.toCellScheme.gradedIndex C = (univ, n) → P.label C ≠ ⊥ → m + 1 < n → IsAnchored P C d →
    ∃ E : GatedExtension P f d, E.display.label E.cap = P.label C

namespace GatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : GatedExtension P f d)

/-- The gate has grade `n`. -/
theorem grade_gate : E.display.toCellScheme.grade E.gate = n :=
  congrArg Prod.snd E.gradedIndex_gate

/-- The display labels the gate at least as the cap: the gate inequality for the display. -/
theorem cap_le_gate : E.display.label E.cap ≤ E.display.label E.gate :=
  E.isGate.cap_le_gate E.display.isLawful (fun _ _ ↦ rfl) fun t ht htG ↦
    E.label_twin t (ht.trans E.gradedIndex_gate) htG

/-- The display does not label the gate `⊥`. -/
theorem label_gate_ne_bot : E.display.label E.gate ≠ ⊥ :=
  E.isGate.gate_ne_bot E.display.isLawful (fun _ _ ↦ rfl) fun t ht htG ↦
    E.label_twin t (ht.trans E.gradedIndex_gate) htG

end GatedExtension

/-- A **coupled gated extension** of a stage type `P` on `n` points over the face `f`, with donor
`d` on `m + 1` points: a gated extension (`GatedExtension`) in which the twins of the gate are not
required to be labelled `⊥`; instead the rows of the display couple them to the gate: every twin
reads the gate at least as it reads the cap (`CellScheme.Rows.TwinsReadGate`). -/
structure CoupledGatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gate. -/
  gate : Fin display.card
  /-- The cap, the private cap seen in the display. -/
  cap : Fin display.card
  /-- The gate has full scope and grade `n`. -/
  gradedIndex_gate : display.toCellScheme.gradedIndex gate = (univ, n)
  /-- The cap has full scope on the private points and grade `n`. -/
  gradedIndex_cap : display.toCellScheme.gradedIndex cap = (univ.map Fin.castSuccEmb, n)
  /-- The twins of the gate read the gate at least as the cap. -/
  twinsReadGate : display.rows.TwinsReadGate gate cap
  /-- The gate data: the row of the gate reads every new donor cell. -/
  isGate : display.rows.IsGate gate cap (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    (display.toCellScheme.visible (Set.range (extendByLast f))) display.label

variable (α) in
/-- The **coupled gated pinned extension property** at stage `α`: the gated pinned extension
property (`HasGatedPinnedExtensions`) with coupled gated extensions in place of gated extensions.
For every legal `P` on `n` points, every face `f` of `P` with restriction `p`, every legal
one-point coface `d` of `p`, and every cell `C` of `P` of graded index `(univ, n)` not labelled
`⊥` below which `d` is anchored, if `m + 1 < n` there is a coupled gated extension of `P` over `f`
with donor `d` whose cap carries the label of `C`.

This is a **named hypothesis, and it is false at every stage above `1`**
(`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`, at a private type with a
proper anchor below the cap; `StageType.CoupledGatedExtension.carriesBottoms`).  It holds at the
input at which `HasGatedPinnedExtensions` is refuted, the private type
`GatedExtensionCounterexample.P α` over the empty root with the donor `P α|{0}` and the cap `3`
(`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`).  **Cap lowering (CL)**, below, is a
requirement of the construction that the refutation does not use.  In every lawful labelling of the
display the gate dominates the cap, so a lift from a coatom `(F ∪ {y}, n)` (`F` a face of `n - 1`
private points containing the root, `y` the new point) whose prescriptions at a donor cell and at
its anchor force the gate below a label `v` also forces the private cap below `v`.  The statement to
be decided is: for the private type `P`, a face `F` of `n - 1` points, a cap `c` self-visible at
`n`, a labelling `p` lawful below `(F, n - 1)` in the cap ball of the labelling of `P` at `c`, and a
label `v ≥ c` self-visible at `n`, some lawful labelling of `P` extends `p`, lies in that cap ball,
and is at most `v` at `C`.  (CL) is the uniform form of that requirement, over every `p` and every
`v ≥ c`; it is a strengthening, not shown necessary for the property and not shown sufficient for
it.  A failure of (CL) refutes the coupled design only at a pair `(p, v)` that a forcing
prescription from an anchored legal donor actually realizes.  The case of a donor labelled `⊤` on
`P α`, which exercises it, is compiled (`CoupledGateInstance.coupledGatedPinnedExtension_donor`). -/
def HasCoupledGatedPinnedExtensions : Prop :=
  ∀ {n m : ℕ} (P : StageType.{u} α n) (f : Fin m ↪ Fin n) (p : StageType.{u} α m)
    (d : StageType.{u} α (m + 1)) (C : Fin P.card),
    P.IsLegal → restrictFace f P = some p → d.IsLegal → restrictFace Fin.castSuccEmb d = some p →
    P.toCellScheme.gradedIndex C = (univ, n) → P.label C ≠ ⊥ → m + 1 < n → IsAnchored P C d →
    ∃ E : CoupledGatedExtension P f d, E.display.label E.cap = P.label C

namespace CoupledGatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : CoupledGatedExtension P f d)

/-- The gate has grade `n`. -/
theorem grade_gate : E.display.toCellScheme.grade E.gate = n :=
  congrArg Prod.snd E.gradedIndex_gate

/-- **The gate inequality for every lawful labelling of the rows of the display**, the display's
own labelling, the lifts that bountifulness asks for, and the realized types alike. -/
theorem cap_le_gate {q : Fin E.display.card → Label.{u}}
    (hq : E.display.rows.IsLawful q) : q E.cap ≤ q E.gate :=
  CellScheme.Rows.cap_le_gate_of_twinsReadGate hq E.isGate.scope_cap_subset E.isGate.grade_cap
    E.twinsReadGate

/-- The display labels the gate at least as the cap, so not `⊥`. -/
theorem label_gate_ne_bot : E.display.label E.gate ≠ ⊥ := fun h ↦
  E.isGate.cap_ne_bot (le_bot_iff.mp (h ▸ E.cap_le_gate E.display.isLawful))

end CoupledGatedExtension

/-- **The readings of a gate force anchoring**, for a display `Q` with literal faces `P` and `d`:
if the row of a cell `G` of grade `n` reads every new donor cell against a cap `C'` labelled as the
cell `C` of `P`, the donor is anchored in `P` below `C`. -/
theorem isAnchored_of_isGate {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} {Q : StageType.{u} α (n + 1)} {G C' : Fin Q.card}
    (hP : restrictFace Fin.castSuccEmb Q = some P) (hd : restrictFace (extendByLast f) Q = some d)
    (hG : Q.toCellScheme.grade G = n)
    (hgate : Q.rows.IsGate G C' (Q.toCellScheme.visible (Set.range Fin.castSuccEmb))
      (Q.toCellScheme.visible (Set.range (extendByLast f))) Q.label)
    {C : Fin P.card} (hC : Q.label C' = P.label C) : IsAnchored P C d := by
  obtain ⟨hfP, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hP
  obtain ⟨hfd, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hd
  intro j hj hne hlt
  set e := Q.cellMap (extendByLast f) j
  have heQ : e ∈ Q.toCellScheme.visible (Set.range (extendByLast f)) :=
    Scheme.mem_visibleCells.mp (Q.cellMap_mem _ j)
  have heP : e ∉ Q.toCellScheme.visible (Set.range Fin.castSuccEmb) := fun h ↦ by
    -- The scope of a cell of the donor face is the preimage of the scope of its cell
    -- (`Scheme.comap_scope`, by definition).
    have hj' : Fin.last m ∈ (Q.toCellScheme.scope e).preimage (extendByLast f)
        (extendByLast f).injective.injOn := hj
    have hlast : Fin.last n ∈ Q.toCellScheme.scope e := by
      simpa using mem_preimage.mp hj'
    obtain ⟨i, hi⟩ := h hlast
    exact (Fin.castSucc_lt_last i).ne hi
  have hlt' : Q.label e < Q.label C' := hC ▸ hlt
  cases hgate.reads e heQ heP with
  | bot hwe _ => exact absurd hwe hne
  | botAnchor _ _ _ hwe _ => exact absurd hwe hne
  | top _ _ _ heC _ => exact absurd heC hlt'.not_ge
  | ref z hz i hi hwe _ =>
    have hz' : z.1 ∈ Set.range (Q.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]
      exact hz
    obtain ⟨z', hz'⟩ := hz'
    refine ⟨z', i, hG ▸ hi, ?_⟩
    -- The labels of the faces `d` and `P` are the labels of their cells (`comap_label`).
    change Q.label e = visibilityReplace n i (Q.label (Q.cellMap Fin.castSuccEmb z'))
    rw [hz']
    rw [hG] at hwe
    exact hwe

/-- **A gated extension has an anchored donor**: the donor of a gated extension whose cap carries
the label of a cell `C` of `P` is anchored in `P` below `C`.  So the anchoring hypothesis of
`HasGatedPinnedExtensions` is necessary for its conclusion. -/
theorem GatedExtension.isAnchored {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} (E : GatedExtension P f d) {C : Fin P.card}
    (hC : E.display.label E.cap = P.label C) : IsAnchored P C d :=
  isAnchored_of_isGate E.restrictFace_castSuccEmb E.restrictFace_extendByLast E.grade_gate
    E.isGate hC

/-- **A coupled gated extension has an anchored donor**: the donor of a coupled gated extension
whose cap carries the label of a cell `C` of `P` is anchored in `P` below `C`.  So the anchoring
hypothesis of `HasCoupledGatedPinnedExtensions` is necessary for its conclusion. -/
theorem CoupledGatedExtension.isAnchored {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} (E : CoupledGatedExtension P f d) {C : Fin P.card}
    (hC : E.display.label E.cap = P.label C) : IsAnchored P C d :=
  isAnchored_of_isGate E.restrictFace_castSuccEmb E.restrictFace_extendByLast E.grade_gate
    E.isGate hC

end StageType

end VaughtConjecture

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### The bottom transport condition -/

/-- The **bottom transport condition** for a private type `P` on `n` points, a one-point donor `d`
(on `m + 1` points, the last one new) and a cap label `c`: every lawful labelling `a` of `P` that
is not `⊥` at the cells of `P` of graded index `(univ, n)` labelled `c` has a lawful labelling `ρ`
of `d` such that, at every new donor cell `j` (one whose scope contains the new point) not
labelled `⊥`,
* `ρ j = ⊥` if `d.label j` is not at least `c` and `a` is `⊥` at every cell `i` of `P` with
  `d.label j = vr_n(P.label i, k)` for some `k ≤ n` (every possible anchor of `j`);
* `ρ j ≠ ⊥` if `a` is not `⊥` at any cell `i` of `P` that is a possible anchor of `j` or is
  labelled at least `c` when `j` is.

Every coupled gated extension forces it (`CoupledGatedExtension.carriesBottoms`). -/
def CarriesBottoms (P : StageType.{u} α n) (d : StageType.{u} α (m + 1)) (c : Label.{u}) :
    Prop :=
  ∀ a : Fin P.card → Label.{u}, P.rows.IsLawful a →
    (∀ i, P.toCellScheme.gradedIndex i = (univ, n) → P.label i = c → a i ≠ ⊥) →
    ∃ ρ : Fin d.card → Label.{u}, d.rows.IsLawful ρ ∧
      ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
        (¬ c ≤ d.label j →
          (∀ i, ∀ k ≤ n, d.label j = visibilityReplace n k (P.label i) → a i = ⊥) → ρ j = ⊥) ∧
        ((∀ i, ((∃ k ≤ n, d.label j = visibilityReplace n k (P.label i)) ∨
            (c ≤ P.label i ∧ c ≤ d.label j)) → a i ≠ ⊥) → ρ j ≠ ⊥)

/-- **The bottom transport condition holds without donor labels strictly below the cap**: if every
new donor cell is labelled `⊥` or at least `c`, the labelling of `d` itself meets the condition.
So the condition can fail only through a donor label strictly between `⊥` and `c`, which an
anchored donor reads through an anchor. -/
theorem carriesBottoms_of_forall_label {P : StageType.{u} α n} {d : StageType.{u} α (m + 1)}
    {c : Label.{u}}
    (hd : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j = ⊥ ∨ c ≤ d.label j) :
    CarriesBottoms P d c := fun _ _ _ ↦
  ⟨d.label, d.isLawful, fun j hj hne ↦
    ⟨fun hlt _ ↦ ((hd j hj).resolve_left hne |> hlt).elim, fun _ ↦ hne⟩⟩

/-! ### Readings in the cap's own block, at a given grade -/

/-- The row of a cell `C` of `P` **reads a cell labelled `l` in its own block**: some cell `z`
below `C`, labelled `l`, is read by the row of `C` in the block `[μ, μ + ω)` (`μ` zero or a limit)
of its reading of `C` itself. -/
def ReadsInOwnBlock (P : StageType.{u} α n) (C : Fin P.card) (l : Label.{u}) : Prop :=
  ∃ z, ∃ hz : z ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C), P.label z = l ∧
    ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ i i' : ℕ,
      P.rows.row C ⟨z, hz⟩ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
      P.rows.row C ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩ =
        ((μ + i' : Ordinal.{u}) : Label.{u})

/-- A lawful labelling not `⊥` at `C` is not `⊥` at a cell that the row of `C` reads, labelled
`l`, in its own block (`CellScheme.Rows.IsLawful.ne_bot_of_row_mem_block`). -/
theorem ReadsInOwnBlock.exists_ne_bot {P : StageType.{u} α n} {C : Fin P.card} {l : Label.{u}}
    (h : P.ReadsInOwnBlock C l) {a : Fin P.card → Label.{u}} (ha : P.rows.IsLawful a)
    (hC : a C ≠ ⊥) : ∃ z, P.label z = l ∧ a z ≠ ⊥ := by
  obtain ⟨z, hz, hzl, μ, hμ, i, i', hrz, hrC⟩ := h
  exact ⟨z, hzl, ha.ne_bot_of_row_mem_block hz hμ hrz hrC hC⟩

/-- The donor `d` is **anchored at the grade `k`** in `P` below the cell `C`: every new donor cell
whose label is neither `⊥` nor at least that of `C` is labelled `vr_k(P.label z, i)` for a cell
`z` of `P` and some `i ≤ k`.  At `k = n` this is `IsAnchored` (`isAnchoredAt_iff`); a design with
the gate at grade `k` reads the donor through visibility replacement at `k`. -/
def IsAnchoredAt (P : StageType.{u} α n) (C : Fin P.card) (k : ℕ)
    (d : StageType.{u} α (m + 1)) : Prop :=
  ∀ j : Fin d.card, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
    ∃ z : Fin P.card, ∃ i ≤ k, d.label j = visibilityReplace k i (P.label z)

/-- Anchoring at the arity is `IsAnchored`. -/
theorem isAnchoredAt_iff {P : StageType.{u} α n} {C : Fin P.card} {d : StageType.{u} α (m + 1)} :
    IsAnchoredAt P C n d ↔ IsAnchored P C d :=
  Iff.rfl

/-- The **bottom transport condition at the grade `k`**: `CarriesBottoms` with the cells of graded
index `(univ, k)` labelled `c` in place of those of graded index `(univ, n)`, and visibility
replacement at `k` in place of `n`.  At `k = n` it is `CarriesBottoms` (`carriesBottomsAt_iff`).
It is the condition that the proof of `CoupledGatedExtension.carriesBottoms` would give for a gate
and a cap of grade `k` (argued from that proof, not compiled: such a design is not defined in the
library). -/
def CarriesBottomsAt (P : StageType.{u} α n) (d : StageType.{u} α (m + 1)) (c : Label.{u})
    (k : ℕ) : Prop :=
  ∀ a : Fin P.card → Label.{u}, P.rows.IsLawful a →
    (∀ i, P.toCellScheme.gradedIndex i = (univ, k) → P.label i = c → a i ≠ ⊥) →
    ∃ ρ : Fin d.card → Label.{u}, d.rows.IsLawful ρ ∧
      ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
        (¬ c ≤ d.label j →
          (∀ i, ∀ k' ≤ k, d.label j = visibilityReplace k k' (P.label i) → a i = ⊥) → ρ j = ⊥) ∧
        ((∀ i, ((∃ k' ≤ k, d.label j = visibilityReplace k k' (P.label i)) ∨
            (c ≤ P.label i ∧ c ≤ d.label j)) → a i ≠ ⊥) → ρ j ≠ ⊥)

/-- The bottom transport condition at the arity is `CarriesBottoms`. -/
theorem carriesBottomsAt_iff {P : StageType.{u} α n} {d : StageType.{u} α (m + 1)}
    {c : Label.{u}} : CarriesBottomsAt P d c n ↔ CarriesBottoms P d c :=
  Iff.rfl

/-- **The bottom transport condition at the grade `k` holds at a cap that reads the donor's
anchors in its own block**: let `C` be a cell of graded index `(univ, k)` of `P`, and suppose
every new donor label neither `⊥` nor at least the label of `C` is `vr_k(l, k')`, `k' ≤ k`, for a
label `l` that the row of `C` reads in its own block.
Then a lawful labelling of `P` not `⊥` at `C` is not `⊥` at a cell labelled `l`, which is a
possible anchor, and the labelling of the donor itself meets the condition.  At `k = n` this is
`carriesBottoms_of_row_mem_block`, with the anchor given by its label. -/
theorem carriesBottomsAt_of_readsInOwnBlock {P : StageType.{u} α n}
    {d : StageType.{u} α (m + 1)} {C : Fin P.card} {k : ℕ}
    (hC : P.toCellScheme.gradedIndex C = (univ, k))
    (hread : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
      ∃ l, (∃ k' ≤ k, d.label j = visibilityReplace k k' l) ∧ P.ReadsInOwnBlock C l) :
    CarriesBottomsAt P d (P.label C) k := by
  intro a ha hcap
  refine ⟨d.label, d.isLawful, fun j hj hne ↦ ⟨fun hlt hdrop ↦ ?_, fun _ ↦ hne⟩⟩
  obtain ⟨l, ⟨k', hk', hjl⟩, hl⟩ := hread j hj hne (lt_of_not_ge hlt)
  obtain ⟨z, hzl, hz⟩ := hl.exists_ne_bot ha (hcap C hC rfl)
  exact (hz (hdrop z k' hk' (hzl ▸ hjl))).elim

/-! ### The bottom transport condition at the arity, from readings in the own block -/

/-- **The bottom transport condition holds when the cap reads an anchor of every donor label below
it in its own block.**  Let `C` be a cell of `P` of graded index `(univ, n)`, and suppose every new
donor cell labelled neither `⊥` nor at least the label of `C` has an anchor `z`
(`d.label j = vr_n(P.label z, k)`, `k ≤ n`) that the row of `C` reads in the block of its reading
of `C` itself.  Then a lawful labelling of `P` not `⊥` at `C` is not `⊥` at that anchor
(`CellScheme.Rows.IsLawful.ne_bot_of_row_mem_block`), and the labelling of `d` itself meets the
condition.  The private type of `CoupledGatedExtensionCounterexample` fails the hypothesis: its cap
reads the anchor `z₁` at `1` and itself at `ω + 2`. -/
theorem carriesBottoms_of_row_mem_block {P : StageType.{u} α n} {d : StageType.{u} α (m + 1)}
    {C : Fin P.card} (hC : P.toCellScheme.gradedIndex C = (univ, n))
    (hblock : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
      d.label j < P.label C →
      ∃ z, ∃ hz : z ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C), ∃ k ≤ n,
        d.label j = visibilityReplace n k (P.label z) ∧ ∃ μ : Ordinal.{u},
          Order.IsSuccPrelimit μ ∧ ∃ i i' : ℕ,
            P.rows.row C ⟨z, hz⟩ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
            P.rows.row C ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩ =
              ((μ + i' : Ordinal.{u}) : Label.{u})) :
    CarriesBottoms P d (P.label C) :=
  -- the anchor `z` is a cell labelled `P.label z` that the row of `C` reads in its own block
  carriesBottomsAt_iff.mp <| carriesBottomsAt_of_readsInOwnBlock hC fun j hj hne hlt ↦ by
    obtain ⟨z, hz, k, hk, hzk, μ, hμ, i, i', hrz, hrC⟩ := hblock j hj hne hlt
    exact ⟨P.label z, ⟨k, hk, hzk⟩, z, hz, rfl, μ, hμ, i, i', hrz, hrC⟩

/-! ### Readings in the own block lie in one block -/

/-- **Readings in the own block lie in one block**: if the row of a cell `C` reads, in its own
block, cells labelled `l` and `l'`, both labels strictly below the label of `C` and neither
self-visible at the grade `K` of `C`, then `l'` is a visibility replacement `vr_K(l, j)` of `l`
for some `j ≤ K`; in particular `l` and `l'` lie in one block.  The locality witness at `C` sends
each reading below the label of `C` to the label read; a reading with finite part at least `K`
would make that label self-visible at `K`, and commutation with visibility replacement at the
finite part of the second reading gives `l'`.  So the own-block mechanism
(`carriesBottoms_of_row_mem_block`, `carriesBottomsAt_of_readsInOwnBlock`) serves anchors below
the cap and not self-visible at its grade only within one block.  The labels `⊥` and `⊤` are
self-visible at every grade, so the premises concern ordinal labels. -/
theorem eq_visibilityReplace_of_readsInOwnBlock {P : StageType.{u} α n} {C : Fin P.card}
    {l l' : Label.{u}} (h : P.ReadsInOwnBlock C l) (h' : P.ReadsInOwnBlock C l')
    (hl : l < P.label C) (hl' : l' < P.label C)
    (hv : ¬ IsSelfVisible (P.toCellScheme.grade C) l)
    (hv' : ¬ IsSelfVisible (P.toCellScheme.grade C) l') :
    ∃ j ≤ P.toCellScheme.grade C, l' = visibilityReplace (P.toCellScheme.grade C) j l := by
  obtain ⟨z, hz, hzl, μ, hμ, i, i₀, hrz, hrC⟩ := h
  obtain ⟨z', hz', hzl', μ', hμ', j, j₀, hrz', hrC'⟩ := h'
  -- the block start of an ordinal label is unique (`Label.add_natCast_eq_add_natCast_iff`)
  obtain rfl : μ = μ' := ((add_natCast_eq_add_natCast_iff hμ hμ').mp
    (WithTop.coe_injective (WithBot.coe_injective (hrC.symm.trans hrC')))).1
  obtain ⟨g, σ, hw, heq⟩ := P.isLawful.locality C
  set K := P.toCellScheme.grade C
  have hCg : P.label C ≤ g K := by
    have := heq ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩
    simp only [min_self] at this
    rw [this]; exact min_le_right _ _
  -- the shifter sends the reading of a cell below `C` with label below `C` to its label
  have hσ : ∀ (y : Fin P.card) (hy : y ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C)),
      P.label y < P.label C → σ (P.rows.row C ⟨y, hy⟩) = P.label y := by
    intro y hy hlt
    have hgy : g K ≤ g (P.toCellScheme.grade y) :=
      hw.antitone ((CellScheme.mem_below _).mp hy).2
    have := heq ⟨y, hy⟩
    simp only [min_eq_left hlt.le] at this
    rcases min_eq_iff.mp this.symm with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (h1 ▸ hlt.trans_le (hCg.trans hgy)) (lt_irrefl _)
  have hσz : σ ((μ + i : Ordinal.{u}) : Label.{u}) = l := by rw [← hrz, hσ z hz (hzl ▸ hl), hzl]
  have hσz' : σ ((μ + j : Ordinal.{u}) : Label.{u}) = l' := by
    rw [← hrz', hσ z' hz' (hzl' ▸ hl'), hzl']
  -- a reading at a finite part at least `K` would make the label self-visible at `K`
  have hfin : ∀ (k : ℕ) (m : Label.{u}), σ ((μ + k : Ordinal.{u}) : Label.{u}) = m →
      m < P.label C → ¬ IsSelfVisible K m → k < K := by
    intro k m hk hm hvm
    by_contra hKk
    have hc := hw.visibilityReplace_comm ((μ + k : Ordinal.{u}) : Label.{u}) K
      (hk ▸ hm.le.trans hCg) K le_rfl
    rw [isSelfVisible_coe_add hμ (not_lt.mp hKk), hk] at hc
    exact hvm hc.symm
  have hi : i < K := hfin i l hσz hl hv
  have hj : j < K := hfin j l' hσz' hl' hv'
  have hc := hw.visibilityReplace_comm ((μ + i : Ordinal.{u}) : Label.{u}) K
    (hσz ▸ hl.le.trans hCg) j hj.le
  rw [visibilityReplace_coe_add_natCast hμ hi j, hσz', hσz] at hc
  exact ⟨j, hj.le, hc⟩


namespace CoupledGatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : CoupledGatedExtension P f d)

/-- A cell of the display whose scope contains the new point is not a private cell. -/
private theorem not_mem_visible_castSuccEmb {e : Fin E.display.card}
    (he : Fin.last n ∈ E.display.toCellScheme.scope e) :
    e ∉ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb) := fun h ↦ by
  obtain ⟨i, hi⟩ := h he
  exact (Fin.castSucc_lt_last i).ne hi

/-- **The gate carries `⊥` from the anchors to a donor cell.**  Let `r` be a lawful labelling of
the display that is not `⊥` at the cap, and `e` a donor cell containing the new point, labelled
neither `⊥` nor at least the cap in the display.  If `r` is `⊥` at every private cell whose label
is sent to the label of `e` by a visibility replacement `vr_n(·, i)`, `i ≤ n`, then `r e = ⊥`. -/
theorem eq_bot_of_isLawful {r : Fin E.display.card → Label.{u}}
    (hr : E.display.rows.IsLawful r) (hcap : r E.cap ≠ ⊥) {e : Fin E.display.card}
    (he : e ∈ E.display.toCellScheme.visible (Set.range (extendByLast f)))
    (hnew : Fin.last n ∈ E.display.toCellScheme.scope e) (hwe : E.display.label e ≠ ⊥)
    (hCe : ¬ E.display.label E.cap ≤ E.display.label e)
    (hz : ∀ z ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb), ∀ i ≤ n,
      E.display.label e = visibilityReplace n i (E.display.label z) → r z = ⊥) : r e = ⊥ := by
  have hG : r E.gate ≠ ⊥ := fun h ↦ hcap (le_bot_iff.mp (h ▸ E.cap_le_gate hr))
  have hgr := E.grade_gate
  exact hr.eq_bot_of_gateReads hG (E.isGate.reads e he (E.not_mem_visible_castSuccEmb hnew))
    hwe hCe fun z hzP i hi hez ↦ hz z hzP i (by rwa [hgr] at hi) (by rwa [hgr] at hez)

/-- **The gate keeps `⊥` away from a donor cell.**  Let `r` be a lawful labelling of the display
that is not `⊥` at the cap, and `e` a donor cell containing the new point, not labelled `⊥` in the
display.  If `r` is not `⊥` at any private cell whose label is sent to the label of `e` by a
visibility replacement `vr_n(·, i)`, `i ≤ n`, nor at any private cell labelled at least the cap
when `e` is, then `r e ≠ ⊥`. -/
theorem ne_bot_of_isLawful {r : Fin E.display.card → Label.{u}}
    (hr : E.display.rows.IsLawful r) (hcap : r E.cap ≠ ⊥) {e : Fin E.display.card}
    (he : e ∈ E.display.toCellScheme.visible (Set.range (extendByLast f)))
    (hnew : Fin.last n ∈ E.display.toCellScheme.scope e) (hwe : E.display.label e ≠ ⊥)
    (hz : ∀ z ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      ((∃ i ≤ n, E.display.label e = visibilityReplace n i (E.display.label z)) ∨
        (E.display.label E.cap ≤ E.display.label z ∧
          E.display.label E.cap ≤ E.display.label e)) → r z ≠ ⊥) : r e ≠ ⊥ := by
  have hG : r E.gate ≠ ⊥ := fun h ↦ hcap (le_bot_iff.mp (h ▸ E.cap_le_gate hr))
  have hgr := E.grade_gate
  refine hr.ne_bot_of_gateReads hG (E.isGate.reads e he (E.not_mem_visible_castSuccEmb hnew))
    hwe fun z hzP h ↦ hz z hzP ?_
  rcases h with ⟨i, hi, hez⟩ | h
  · exact .inl ⟨i, by rwa [hgr] at hi, by rwa [hgr] at hez⟩
  · exact .inr h

/-- **Every coupled gated extension forces the bottom transport condition** for its private type,
its donor and the label of its cap.  A lawful labelling of `P` extends to a lawful labelling `r`
of the display (bountifulness from the private face at the cap `⊥`); `r` is not `⊥` at the cap,
hence not at the gate (`cap_le_gate`); the donor face of `r` is lawful for `d`, and the readings of
the gate carry `⊥` from the anchors (`eq_bot_of_isLawful`, `ne_bot_of_isLawful`). -/
theorem carriesBottoms {c : Label.{u}} (hc : E.display.label E.cap = c) :
    CarriesBottoms P d c := by
  obtain ⟨hfP, hP⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_castSuccEmb
  obtain ⟨hfd, hd⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_extendByLast
  suffices key : CarriesBottoms (E.display.comap Fin.castSuccEmb hfP)
      (E.display.comap (extendByLast f) hfd) c by
    rw [hP, hd] at key; exact key
  intro a ha hcapa
  obtain ⟨r, hr, -, hra⟩ := Scheme.IsLegal.exists_isLawful_extend E.isLegal hfP
    (isSelfVisible_bot (n + 1)) ha CellScheme.Rows.isLawful_const_bot
    fun _ ↦ by simp only [min_bot_right]
  -- The private cells are the cells of the private face.
  have hpriv : ∀ z ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      ∃ i, E.display.toScheme.cellMap Fin.castSuccEmb i = z := fun z hz ↦ by
    have : z ∈ Set.range (E.display.toScheme.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]; exact hz
    exact this
  -- The cap is the cell of the private face labelled `c`, of graded index `(univ, n)` there.
  have hcap : r E.cap ≠ ⊥ := by
    obtain ⟨i, hi⟩ := hpriv E.cap E.isGate.cap_mem
    have hgi : (E.display.comap Fin.castSuccEmb hfP).toCellScheme.gradedIndex i = (univ, n) := by
      have h := E.display.toScheme.map_comap_gradedIndex Fin.castSuccEmb i
      rw [hi, E.gradedIndex_cap] at h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      exact Prod.ext ((Finset.map_injective _) h1) h2
    rw [← hi, hra i]
    refine hcapa i hgi ?_
    -- The labels of the private face are those of its cells (`comap_label`, by definition).
    change E.display.label (E.display.toScheme.cellMap Fin.castSuccEmb i) = c
    rw [hi, hc]
  refine ⟨fun j ↦ r (E.display.toScheme.cellMap (extendByLast f) j),
    hr.comap (E.display.toScheme.isLowerEmbedding_comap _), fun j hj hjb ↦ ?_⟩
  set e := E.display.toScheme.cellMap (extendByLast f) j
  have he : e ∈ E.display.toCellScheme.visible (Set.range (extendByLast f)) :=
    Scheme.mem_visibleCells.mp (E.display.toScheme.cellMap_mem _ j)
  have hnew : Fin.last n ∈ E.display.toCellScheme.scope e := by
    -- The scope of a cell of the donor face is the preimage of the scope of its cell
    -- (`Scheme.comap_scope`, by definition).
    have hj' : Fin.last m ∈ (E.display.toCellScheme.scope e).preimage (extendByLast f)
        (extendByLast f).injective.injOn := hj
    simpa using mem_preimage.mp hj'
  have hle : E.display.label e = (E.display.comap (extendByLast f) hfd).label j := rfl
  refine ⟨fun hCe hanc ↦ E.eq_bot_of_isLawful hr hcap he hnew hjb (by rwa [hc, hle])
      fun z hz i hi hez ↦ ?_,
    fun hanc ↦ E.ne_bot_of_isLawful hr hcap he hnew hjb fun z hz hez ↦ ?_⟩
  · obtain ⟨i', rfl⟩ := hpriv z hz
    rw [hra i']
    exact hanc i' i hi hez
  · obtain ⟨i', rfl⟩ := hpriv z hz
    rw [hra i']
    rw [hc] at hez
    exact hanc i' hez

end CoupledGatedExtension

/-- **The coupled gated pinned extension property forces the bottom transport condition** at each
of its inputs: for a legal `P`, a face `f` with restriction `p`, a legal one-point coface `d` of
`p`, and a cell `C` of `P` of graded index `(univ, n)` not labelled `⊥` below which `d` is
anchored, with `m + 1 < n`, the condition holds for `P`, `d` and the label of `C`. -/
theorem HasCoupledGatedPinnedExtensions.carriesBottoms
    (h : HasCoupledGatedPinnedExtensions α) {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)} {C : Fin P.card} (hP : P.IsLegal)
    (hp : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hC : P.toCellScheme.gradedIndex C = (univ, n)) (hC0 : P.label C ≠ ⊥) (hmn : m + 1 < n)
    (ha : IsAnchored P C d) : CarriesBottoms P d (P.label C) := by
  obtain ⟨E, hE⟩ := h P f p d C hP hp hd hdp hC hC0 hmn ha
  exact E.carriesBottoms hE

end VaughtConjecture.StageType

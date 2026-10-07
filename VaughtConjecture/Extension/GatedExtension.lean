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

**Several gates.**  A **per-block coupled gated extension**
(`StageType.PerBlockCoupledGatedExtension P f d k`) has `k` gates, each with its own cap, a private
cell of a given graded index, its own twin–gate coupling, and the readings of the donor cells whose
labels lie in a given set; cap and gate of each pair have equal grades, as the clauses of
`CellScheme.Rows.IsGate` ask.  A coupled gated extension is one with one gate, whose cap has graded
index `(univ, n)` and reads every label (`StageType.CoupledGatedExtension.toPerBlock`).  It is the
display of the per-block design of `VaughtConjecture.Realization.PerBlockCarrying`.

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

/-- A **per-block coupled gated extension** of `P` on `n` points over the face `f`, with donor `d`
on `m + 1` points and `k` gates: a legal display on `n + 1` points whose two faces are literally
`P` and `d`, with, for each `t : Fin k`, a gate `gate t` and a cap `cap t`, a private cell of
graded index `capIndex t` in `P`; the twins of each gate read it at least as its cap
(`CellScheme.Rows.TwinsReadGate`), and the row of each gate reads, against its cap, the donor cells
whose labels lie in `readLabels t` (`CellScheme.Rows.IsGate`, whose clauses ask that cap and gate
have equal grades and nested scopes).  A coupled gated extension is the case of one gate, with the
gate and cap of graded index `(univ, n)` (`CoupledGatedExtension.gradedIndex_gate`) and every label
read (`CoupledGatedExtension.toPerBlock`).  Only the clauses that the per-block bottom transport
condition uses are stated
(`PerBlockCoupledGatedExtension.carriesBottomsPerBlock`); no universal extension property for it
is stated. -/
structure PerBlockCoupledGatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) (k : ℕ) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gates. -/
  gate : Fin k → Fin display.card
  /-- The caps, private cells of the display. -/
  cap : Fin k → Fin display.card
  /-- The graded index of each cap in the private type. -/
  capIndex : Fin k → Finset (Fin n) × ℕ
  /-- Each cap has the graded index `capIndex t` of the private type, on the private points. -/
  gradedIndex_cap : ∀ t, display.toCellScheme.gradedIndex (cap t) =
    ((capIndex t).1.map Fin.castSuccEmb, (capIndex t).2)
  /-- The labels of the donor cells that each gate reads. -/
  readLabels : Fin k → Set Label.{u}
  /-- The twins of each gate read the gate at least as its cap. -/
  twinsReadGate : ∀ t, display.rows.TwinsReadGate (gate t) (cap t)
  /-- The gate data: the row of each gate reads every donor cell whose label it reads. -/
  isGate : ∀ t, display.rows.IsGate (gate t) (cap t)
    (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    {e | e ∈ display.toCellScheme.visible (Set.range (extendByLast f)) ∧
      display.label e ∈ readLabels t} display.label

/-- **A coupled gated extension is a per-block one with one gate**: its gate and its cap, of graded
index `(univ, n)`, with every donor label read. -/
def CoupledGatedExtension.toPerBlock {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} (E : CoupledGatedExtension P f d) :
    PerBlockCoupledGatedExtension P f d 1 where
  display := E.display
  isLegal := E.isLegal
  restrictFace_castSuccEmb := E.restrictFace_castSuccEmb
  restrictFace_extendByLast := E.restrictFace_extendByLast
  gate _ := E.gate
  cap _ := E.cap
  capIndex _ := (univ, n)
  gradedIndex_cap _ := E.gradedIndex_cap
  readLabels _ := Set.univ
  twinsReadGate _ := E.twinsReadGate
  isGate _ := by simpa only [Set.mem_univ, and_true, Set.ofPred_mem_eq] using E.isGate

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

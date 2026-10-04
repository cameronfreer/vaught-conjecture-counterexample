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
  and some `i ≤ n`.  The anchor may be self-visible at `n`, and `i = n` is allowed.  When `C` has
  grade `n`, as in `HasGatedPinnedExtensions`, its label is self-visible at `n`, so the anchor of
  a donor label below `P.label C` is itself labelled below `P.label C`
  (`Label.le_visibilityReplace_of_le`).  This is exactly
  what the readings of the gate force: a gated extension whose cap carries the label of `C` has an
  anchored donor (`GatedExtension.isAnchored`).
* The **gated pinned extension property** at stage `α` (`StageType.HasGatedPinnedExtensions α`)
  asks for a gated extension, with cap labelled as a given non-bottom cell `C` of graded index
  `(univ, n)` of `P`, for every legal `P`, every face `f` of `P` with restriction `p`, and every
  legal one-point coface `d` of `p` anchored in `P` below `C`, when `m + 1 < n`.

`HasGatedPinnedExtensions` is a **named hypothesis**, in the pattern of
`StageType.HasCoatomExtensions`, not a theorem, and nothing here claims it.  The legality of a
gated extension contains (an analysis, not compiled here) an exact pinned extension of a face of
`P` over the root (the restriction to the last coatom of a chain of faces from the root with the
new point to the whole set, by accessibility of plans and completeness) and a full-scope layer of
grade `n` in which the gate and its twins are controlled.  The planned derivation, from
`HasCoatomExtensions` for the coatom extensions of the chain before the last, as in
`StageType.exists_pinned_extension`, together with a gated form of the last coatom extension, is
prospective.  No gated extension is exhibited here: the abstract schemes of
`VaughtConjecture.Extension.GateExamples` carry no legality.

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

This is an existence statement, a hypothesis and not a theorem: it is still to be proved.  The
legality of the display contains (an analysis, not compiled here) an exact pinned extension of a
face of `P` over the root and a controlled full-scope layer of grade `n`; the planned derivation
from `HasCoatomExtensions` and a gated last coatom extension is prospective. -/
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

end StageType

end VaughtConjecture

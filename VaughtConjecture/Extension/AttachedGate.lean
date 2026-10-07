/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.GatedExtension

/-!
# Attached gated extensions

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple with
the display's bottom pattern) and 3.3 (the recovery statements, item 1: agreement below a cutoff);
the vocabulary of `VaughtConjecture.Extension.Gate` (private cells, donor cells, display, private
cap, gate, twins, readings, anchors).

**The design.**  In a gated extension (`StageType.GatedExtension`) the display labels every twin of
the gate `⊥`; the universal form of that property fails at every stage
(`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).  In a coupled gated extension
(`StageType.CoupledGatedExtension`) every twin reads the gate at least as the private cap, so the
gate dominates the cap in every lawful labelling; the universal coupled property
(`StageType.HasCoupledGatedPinnedExtensions`) is open on `main` (a separate open change argues
that it fails above stage `1`, through a lawful private labelling that is `⊥` at an anchor and not
at the cap).  An **attached gated extension** puts the condition on the row of the gate instead,
and places no condition on the labels of the twins:

* a set of **readers**: cells of the graded index `(univ, n)` of the gate that are gates in the
  sense of `CellScheme.Rows.IsGate`, that is, whose rows read every new donor cell through an
  anchor or through a private cell labelled at least the cap, for the same cap and display;
* the row of the gate is `⊥` at every other cell of its graded index outside the readers
  (`CellScheme.Rows.ReadsOnly`), and reads one reader, the **ceiling**, at least as it reads the
  gate itself (so the ceiling is at least the gate in every lawful labelling);
* the display does not label the gate `⊥`.

A reader may be the gate itself, which may then serve as its own ceiling.  **Availability** is the
second law of a lawful section: a cell of the grade of a cell `t`, with scope inside that of `t`,
lies below some cell of the graded index of `t`.

**Recovery through the readers** (`StageType.AttachedGatedExtension.recover_of_isLawful`, from
`CellScheme.Rows.IsLawful.recover_of_readsOnly`).  Let `q` be a lawful labelling, literally the
display on the private cells, and not `⊥` at the gate.  Every cell of the graded index of the gate
outside the readers is `⊥` in `q`, so availability for the private cap and the gate gives a reader
at least the label of the cap, and gate recovery through that reader gives agreement with the
display on every donor cell below that label.  Availability may reach a twin of the gate; what is
excluded is a twin that is not a reader.  No label of the twins is read, and no legality is used.

**The lifts that legality forces** (`StageType.AttachedGatedExtension.exists_lift`).  Let `c ≠ ⊥`
be self-visible at `n + 1`, and `a` a lawful labelling of the private face in the cap ball of the
display at `c`.  Bountifulness of the display (`Scheme.IsLegal.exists_isLawful_extend`) gives a
lawful labelling `r` of the display with private face `a` and the observation of the display at
`c`.  The gate is not `⊥` in the display, so not in `r`; so some reader `K` is at least `r` at the
cap, and each reading of the row of `K` through an anchor `z` is transported:
`min (r e) (r C) = min (vr_n(r z, i)) (r C)`
(`CellScheme.Rows.IsLawful.min_eq_visibilityReplace_of_row_eq`).  Argued, not formalized: at the
cap `⊥` a lift may label the gate and every reader `⊥`, so nothing is forced through the readers
there; and since `c ≠ ⊥`, `a` is not `⊥` at a private cell not labelled `⊥`
(`Label.ne_bot_of_min_eq_of_ne_bot`), so the transported readings force no `⊥` at a donor cell not
labelled `⊥`.  The coupled gate, by contrast, forces the readings of its gate for every lawful
private labelling, at the cap `⊥` included (by `cap_le_gate_of_twinsReadGate` with
`min_eq_visibilityReplace_of_row_eq`; argued, not formalized).

**One dominating cell for two opposite cells is impossible**
(`StageType.not_forall_le_of_opposite`).  If two cells of the private face of graded index
`(univ, n)` are ordered oppositely by two lawful labellings in the cap ball of the private labels
at a cap `c ≠ ⊥` self-visible at `n`, then in a legal one-point extension no single cell `K` of
graded index `(univ, n)` dominates that graded index in every labelling lawful below it that is
not `⊥` at a cell `G` the extension does not label `⊥`: the lifts of the two labellings
(`StageType.IsLegal.exists_isLawfulBelow_castSucc`) keep `G` not `⊥`, and `K` would read the two
cells in both orders with one row (`CellScheme.Rows.row_lt_of_le_dominant`).  These lifts have
private faces other than the private labels.  In particular a cell `G` whose row is `⊥` at every
other cell of its graded index except one ceiling (the gate itself included) is labelled `⊥` by
every such extension (`StageType.label_eq_bot_of_readsOnly_singleton`); this is a statement about
that row design.  It does not decide whether, for labellings with the literal private face,
availability from the private cap must reach a reader other than the ceiling.  The instance is
`GatedExtensionCounterexample.P α` (`VaughtConjecture.Extension.AttachedGateCounterexample`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

Lawful sections, locality and availability are [Kni26, Definition 2.5.4]; bountifulness is
[Kni26, Definition 2.5.14]; the bottom-pattern clause read by the construction is
[Kni26, Definition 3.2.1], clause 4(a)ii.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Attached gated extensions -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- An **attached gated extension** of a stage type `P` on `n` points over the face `f`, with donor
`d` on `m + 1` points: a legal **display** on `n + 1` points whose faces along `Fin.castSuccEmb` and
`extendByLast f` are literally `P` and `d`; a **gate** of graded index `(univ, n)`, not labelled `⊥`
by the display; the **cap**, of graded index `(univ.map Fin.castSuccEmb, n)`; and a set of
**readers** of graded index `(univ, n)`, each reading every new donor cell against the cap as in
`CellScheme.Rows.IsGate`.  The row of the gate is `⊥` at every other cell of its graded index
outside the readers, and reads one reader, the **ceiling**, at least as it reads the gate.
Nothing is asked of the labels of the twins of the gate. -/
structure AttachedGatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
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
  /-- The readers. -/
  readers : Set (Fin display.card)
  /-- The ceiling, a reader that the gate reads at least as itself. -/
  ceiling : Fin display.card
  /-- The ceiling is a reader. -/
  ceiling_mem : ceiling ∈ readers
  /-- The gate has full scope and grade `n`. -/
  gradedIndex_gate : display.toCellScheme.gradedIndex gate = (univ, n)
  /-- The cap has full scope on the private points and grade `n`. -/
  gradedIndex_cap : display.toCellScheme.gradedIndex cap = (univ.map Fin.castSuccEmb, n)
  /-- The readers have full scope and grade `n`. -/
  gradedIndex_reader : ∀ K ∈ readers, display.toCellScheme.gradedIndex K = (univ, n)
  /-- The display does not label the gate `⊥`. -/
  label_gate_ne_bot : display.label gate ≠ ⊥
  /-- The row of the gate is `⊥` at every other cell of its graded index outside the readers. -/
  readsOnly : display.rows.ReadsOnly gate readers
  /-- The row of the gate reads the ceiling at least as it reads the gate. -/
  row_gate_le_ceiling : display.rows.row gate ⟨gate, display.toCellScheme.mem_below_gradedIndex _⟩ ≤
    display.rows.row gate
      ⟨ceiling, ((gradedIndex_reader ceiling ceiling_mem).trans gradedIndex_gate.symm).le⟩
  /-- Every reader reads every new donor cell against the cap. -/
  isGate : ∀ K ∈ readers, display.rows.IsGate K cap
    (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    (display.toCellScheme.visible (Set.range (extendByLast f))) display.label

namespace AttachedGatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : AttachedGatedExtension P f d)

/-- The ceiling has the graded index of the gate. -/
theorem gradedIndex_ceiling_eq :
    E.display.toCellScheme.gradedIndex E.ceiling = E.display.toCellScheme.gradedIndex E.gate :=
  (E.gradedIndex_reader E.ceiling E.ceiling_mem).trans E.gradedIndex_gate.symm

/-- The gate has grade `n`. -/
theorem grade_gate : E.display.toCellScheme.grade E.gate = n :=
  congrArg Prod.snd E.gradedIndex_gate

/-- A reader has grade `n`. -/
theorem grade_reader {K : Fin E.display.card} (hK : K ∈ E.readers) :
    E.display.toCellScheme.grade K = n :=
  congrArg Prod.snd (E.gradedIndex_reader K hK)

/-- The scope of the cap lies in that of the gate. -/
theorem scope_cap_subset : E.display.toCellScheme.scope E.cap ⊆
    E.display.toCellScheme.scope E.gate := by
  rw [show E.display.toCellScheme.scope E.cap = univ.map Fin.castSuccEmb from
      congrArg Prod.fst E.gradedIndex_cap,
    show E.display.toCellScheme.scope E.gate = univ from congrArg Prod.fst E.gradedIndex_gate]
  exact subset_univ _

/-- The cap has the grade of the gate. -/
theorem grade_cap : E.display.toCellScheme.grade E.cap = E.display.toCellScheme.grade E.gate :=
  (congrArg Prod.snd E.gradedIndex_cap).trans E.grade_gate.symm

/-- **Recovery for a lawful labelling of the display's rows**: literally the display on the private
cells and not `⊥` at the gate, it has a reader at least the label of the cap, and agrees with the
display on every donor cell below that label. -/
theorem recover_of_isLawful {q : Fin E.display.card → Label.{u}} (hq : E.display.rows.IsLawful q)
    (hlit : ∀ x ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      q x = E.display.label x) (hG : q E.gate ≠ ⊥) :
    ∃ K ∈ E.readers, E.display.label E.cap ≤ q K ∧
      ∀ e ∈ E.display.toCellScheme.visible (Set.range (extendByLast f)),
        min (q e) (E.display.label E.cap) = min (E.display.label e) (E.display.label E.cap) :=
  hq.recover_of_readsOnly E.readsOnly E.isGate E.ceiling_mem E.gradedIndex_ceiling_eq
    E.row_gate_le_ceiling hlit hG

/-- **The lifts that legality asks for.**  Let `c ≠ ⊥` be self-visible at `n + 1` and let `a` be a
lawful labelling of the private face of the display (the scheme of `P`) that agrees with the
private labels capped at `c`.  Bountifulness of the display gives a lawful labelling `r` of the
display with private face `a` and the observation of the display at `c`.  It is not `⊥` at the
gate, some reader `K` is at least its value at the cap, and every reading of the row of `K`
through an anchor `z` is transported to `r` below its value at the cap. -/
theorem exists_lift {c : Label.{u}} (hc : IsSelfVisible (n + 1) c) (hc0 : c ≠ ⊥)
    {a : Fin (E.display.toScheme.comap Fin.castSuccEmb).card → Label.{u}}
    (ha : (E.display.toScheme.comap Fin.castSuccEmb).rows.IsLawful a)
    (hac : ∀ i, min (E.display.label (E.display.toScheme.cellMap Fin.castSuccEmb i)) c =
      min (a i) c) :
    ∃ r : Fin E.display.card → Label.{u}, E.display.rows.IsLawful r ∧
      (∀ x, min (r x) c = min (E.display.label x) c) ∧
      (∀ i, r (E.display.toScheme.cellMap Fin.castSuccEmb i) = a i) ∧ r E.gate ≠ ⊥ ∧
      ∃ K ∈ E.readers, r E.cap ≤ r K ∧
        ∀ (z e : E.display.toCellScheme.below (E.display.toCellScheme.gradedIndex K)) (i : ℕ),
          i ≤ n → E.display.rows.row K e = visibilityReplace n i (E.display.rows.row K z) →
            min (r e) (r E.cap) = min (visibilityReplace n i (r z)) (r E.cap) := by
  obtain ⟨hf, -⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_castSuccEmb
  obtain ⟨r, hr, hrc, hra⟩ := E.isLegal.exists_isLawful_extend hf hc ha E.display.isLawful
    fun i ↦ hac i
  have hG : r E.gate ≠ ⊥ :=
    Label.ne_bot_of_min_eq_of_ne_bot (hrc E.gate) E.label_gate_ne_bot hc0
  obtain ⟨K, hK, -, hle⟩ := hr.exists_mem_le_of_readsOnly E.readsOnly E.ceiling_mem
    E.gradedIndex_ceiling_eq E.row_gate_le_ceiling hG E.scope_cap_subset E.grade_cap
  refine ⟨r, hr, hrc, hra, hG, K, hK, hle, fun z e i hi hrow ↦ ?_⟩
  have hgK := E.grade_reader hK
  have h := hr.min_eq_visibilityReplace_of_row_eq (z := z) (e := e) (i := i)
    (by rw [hgK]; exact hi) (by rw [hgK]; exact hrow)
  rw [hgK] at h
  calc min (r e) (r E.cap) = min (min (r e) (r K)) (r E.cap) := by
        rw [min_assoc, min_eq_right hle]
    _ = min (min (visibilityReplace n i (r z)) (r K)) (r E.cap) := by rw [h]
    _ = min (visibilityReplace n i (r z)) (r E.cap) := by rw [min_assoc, min_eq_right hle]

end AttachedGatedExtension

/-- **A gated extension whose gate has no twins is an attached gated extension**, with the gate as
its only reader and as its own ceiling. -/
def GatedExtension.toAttachedGatedExtension {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} (E : GatedExtension P f d)
    (huniq : ∀ t, E.display.toCellScheme.gradedIndex t = (univ, n) → t = E.gate) :
    AttachedGatedExtension P f d where
  display := E.display
  isLegal := E.isLegal
  restrictFace_castSuccEmb := E.restrictFace_castSuccEmb
  restrictFace_extendByLast := E.restrictFace_extendByLast
  gate := E.gate
  cap := E.cap
  readers := {E.gate}
  ceiling := E.gate
  ceiling_mem := rfl
  gradedIndex_gate := E.gradedIndex_gate
  gradedIndex_cap := E.gradedIndex_cap
  gradedIndex_reader K hK := by rw [Set.mem_singleton_iff.mp hK]; exact E.gradedIndex_gate
  label_gate_ne_bot := E.label_gate_ne_bot
  readsOnly t ht htG _ := absurd (huniq t (ht.trans E.gradedIndex_gate)) htG
  row_gate_le_ceiling := le_rfl
  isGate K hK := by rw [Set.mem_singleton_iff.mp hK]; exact E.isGate

/-! ### One dominating cell for two opposite cells is impossible -/

/-- **Lifting from the private face at a cap.**  Let `Q` be a legal stage type on `n + 1` points,
`0 < n`, whose face along `Fin.castSuccEmb` is closed, and let `c` be self-visible at `n`.  A
lawful labelling `q` of the face whose observation at `c` is that of the labels of the face extends
to a labelling `r` lawful below `(univ, n)`, equal to `q` on the face, with the observation of the
labels of `Q` at `c` at every cell below `(univ, n)`: bountifulness of `Q` from
`(univ.map Fin.castSuccEmb, n)` to `(univ, n)`. -/
theorem IsLegal.exists_isLawfulBelow_castSucc {Q : StageType.{u} α (n + 1)} (hQ : Q.IsLegal)
    (hfQ : univ.map Fin.castSuccEmb ∈ Q.toCellScheme.faces) (hn : 0 < n) {c : Label.{u}}
    (hc : IsSelfVisible n c) {q : Fin (Q.comap Fin.castSuccEmb hfQ).card → Label.{u}}
    (hq : (Q.comap Fin.castSuccEmb hfQ).rows.IsLawful q)
    (hqc : ∀ i, min ((Q.comap Fin.castSuccEmb hfQ).label i) c = min (q i) c) :
    ∃ r : Fin Q.card → Label.{u}, Q.rows.IsLawfulBelow (univ, n) (fun x ↦ r x) ∧
      (∀ x ∈ Q.toCellScheme.below (univ, n), min (r x) c = min (Q.label x) c) ∧
      ∀ i, r (Q.toScheme.cellMap Fin.castSuccEmb i) = q i := by
  let φ := Q.toScheme.cellMap Fin.castSuccEmb
  let X : Finset (Fin (n + 1)) × ℕ := (univ.map Fin.castSuccEmb, n)
  let Y : Finset (Fin (n + 1)) × ℕ := (univ, n)
  have hX : X ∈ Q.toCellScheme.gradedFaces := ⟨hfQ, hn, by simp [X]⟩
  have hY : Y ∈ Q.toCellScheme.gradedFaces := ⟨Q.univ_mem_faces, hn, by simp [Y]⟩
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  let x : Fin Q.card → Label.{u} := Function.extend φ q fun _ ↦ ⊥
  have hxφ : ∀ i, x (φ i) = q i := fun i ↦ φ.injective.extend_apply _ _ i
  have hxX : Q.rows.IsLawfulBelow X (fun d ↦ x d) := by
    refine (Q.toScheme.isLawfulBelow_comap_cellMap_iff Fin.castSuccEmb (univ, n) x).mp ?_
    have h : (Q.toScheme.comap Fin.castSuccEmb).rows.IsLawfulBelow (univ, n)
        (fun i ↦ q i.1) := hq.isLawfulBelow (univ, n)
    have heq : (fun i : (Q.toScheme.comap Fin.castSuccEmb).toCellScheme.below (univ, n) ↦
        x (Q.toScheme.cellMap Fin.castSuccEmb i)) = fun i ↦ q i.1 :=
      funext fun i ↦ hxφ i.1
    rw [heq]; exact h
  have hcapX : ∀ d : Q.toCellScheme.below X,
      min (Q.label (Set.inclusion (Q.toCellScheme.below_mono hXY) d)) c = min (x d) c := by
    intro d
    have hvis : (d : Fin Q.card) ∈ Q.toScheme.visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      have : Q.toCellScheme.scope d ⊆ univ.map Fin.castSuccEmb := d.2.1
      intro z hz
      obtain ⟨a, -, rfl⟩ := mem_map.mp (this (mem_coe.mp hz))
      exact ⟨a, rfl⟩
    obtain ⟨i, hi⟩ : (d : Fin Q.card) ∈ Set.range φ := by
      rw [Scheme.range_cellMap]; exact mem_coe.mpr hvis
    -- The inclusion of the cells below `X` into those below `Y` keeps the cell.
    change min (Q.label d) c = min (x d) c
    rw [← hi, hxφ i]; exact hqc i
  obtain ⟨r', hr', hcap, hres⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (hQ.isBountiful hX hY hXY) c hc (fun d ↦ x d) (fun d ↦ Q.label d) hxX
    (Q.isLawful.isLawfulBelow Y) hcapX
  let r := CellScheme.Rows.extendBot Y r'
  have hrY : ∀ y (hy : y ∈ Q.toCellScheme.below Y), r y = r' ⟨y, hy⟩ :=
    fun y hy ↦ CellScheme.Rows.extendBot_of_mem r' hy
  refine ⟨r, CellScheme.Rows.isLawfulBelow_extendBot.mpr hr', fun y hy ↦ ?_, fun i ↦ ?_⟩
  · rw [hrY y hy]; exact hcap ⟨y, hy⟩
  · have hiX : φ i ∈ Q.toCellScheme.below X := by
      have hvis := Q.toScheme.cellMap_mem Fin.castSuccEmb i
      rw [Scheme.mem_visibleCells] at hvis
      refine ⟨fun z hz ↦ ?_, ?_⟩
      · obtain ⟨a, ha⟩ := hvis hz
        exact mem_map.mpr ⟨a, mem_univ _, ha⟩
      · have := (Q.comap Fin.castSuccEmb hfQ).grade_le i
        rw [← Q.toScheme.map_comap_gradedIndex Fin.castSuccEmb i] at *
        exact this
    rw [hrY (φ i) (Q.toCellScheme.below_mono hXY hiX)]
    exact (hres ⟨φ i, hiX⟩).trans (hxφ i)

/-- **No single dominating cell at a private type with two opposite cells.**  Let `Q` be a legal
stage type on `n + 1` points whose face along `Fin.castSuccEmb` is literally `P`, and let two
cells `C₁`, `C₂` of `P` of graded index `(univ, n)` be ordered oppositely by two lawful labellings
of `P` in the cap ball of its labels at a cap `c ≠ ⊥` self-visible at `n`.  For every cell `G` of
`Q` of graded index `(univ, n)` not labelled `⊥` and every cell `K` of that graded index, some
labelling lawful below `(univ, n)` is not `⊥` at `G` and labels some cell of that graded index
strictly above `K`.  The labellings used have the two given private faces, not the labels of
`P`. -/
theorem not_forall_le_of_opposite {P : StageType.{u} α n} (Q : StageType.{u} α (n + 1))
    (hQ : Q.IsLegal) (hQP : restrictFace Fin.castSuccEmb Q = some P) {C₁ C₂ : Fin P.card}
    (hC₁ : P.toCellScheme.gradedIndex C₁ = (univ, n))
    (hC₂ : P.toCellScheme.gradedIndex C₂ = (univ, n)) {c : Label.{u}} (hc : IsSelfVisible n c)
    (hc0 : c ≠ ⊥) {p p' : Fin P.card → Label.{u}} (hp : P.rows.IsLawful p)
    (hp' : P.rows.IsLawful p') (hpc : ∀ i, min (P.label i) c = min (p i) c)
    (hp'c : ∀ i, min (P.label i) c = min (p' i) c) (h12 : p C₂ < p C₁) (h21 : p' C₁ < p' C₂)
    {G K : Fin Q.card} (hG : Q.toCellScheme.gradedIndex G = (univ, n))
    (hK : Q.toCellScheme.gradedIndex K = (univ, n)) (hG0 : Q.label G ≠ ⊥) :
    ¬ ∀ r : Fin Q.card → Label.{u}, Q.rows.IsLawfulBelow (univ, n) (fun x ↦ r x) → r G ≠ ⊥ →
      ∀ t, Q.toCellScheme.gradedIndex t = (univ, n) → r t ≤ r K := by
  intro hdom
  obtain ⟨hfQ, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hQP
  have hn : 0 < n := by
    have h := (Q.comap Fin.castSuccEmb hfQ).isWellFormed.isWellFormed.grade_pos C₁
    rwa [show (Q.comap Fin.castSuccEmb hfQ).toCellScheme.grade C₁ = n from
      congrArg Prod.snd hC₁] at h
  let φ := Q.toScheme.cellMap Fin.castSuccEmb
  have hGY : G ∈ Q.toCellScheme.below (univ, n) := by rw [CellScheme.mem_below, hG]
  have hgi : ∀ i, (Q.comap Fin.castSuccEmb hfQ).toCellScheme.gradedIndex i = (univ, n) →
      Q.toCellScheme.gradedIndex (φ i) = (univ.map Fin.castSuccEmb, n) := fun i hi ↦ by
    rw [← Q.toScheme.map_comap_gradedIndex Fin.castSuccEmb i]
    -- The face of `Q` along `Fin.castSuccEmb` has the restricted scheme, by definition.
    change Prod.map (Finset.map Fin.castSuccEmb) id
      ((Q.comap Fin.castSuccEmb hfQ).toCellScheme.gradedIndex i) = _
    rw [hi]; rfl
  have hs : ∀ i, (Q.comap Fin.castSuccEmb hfQ).toCellScheme.gradedIndex i = (univ, n) →
      Q.toCellScheme.scope (φ i) ⊆ (univ : Finset (Fin (n + 1))) ∧
        Q.toCellScheme.grade (φ i) = n := fun i hi ↦
    ⟨subset_univ _, congrArg Prod.snd (hgi i hi)⟩
  obtain ⟨r, hr, hrc, hrφ⟩ := hQ.exists_isLawfulBelow_castSucc hfQ hn hc hp hpc
  obtain ⟨r', hr', hr'c, hr'φ⟩ := hQ.exists_isLawfulBelow_castSucc hfQ hn hc hp' hp'c
  have hrG : r G ≠ ⊥ := Label.ne_bot_of_min_eq_of_ne_bot (hrc G hGY) hG0 hc0
  have hr'G : r' G ≠ ⊥ := Label.ne_bot_of_min_eq_of_ne_bot (hr'c G hGY) hG0 hc0
  exact lt_asymm
    (CellScheme.Rows.row_lt_of_le_dominant hK hr (hdom r hr hrG) (hs C₁ hC₁).1 (hs C₁ hC₁).2
      (hs C₂ hC₂).1 (hs C₂ hC₂).2 ((hrφ C₂).trans_lt (h12.trans_eq (hrφ C₁).symm)))
    (CellScheme.Rows.row_lt_of_le_dominant hK hr' (hdom r' hr' hr'G) (hs C₂ hC₂).1
      (hs C₂ hC₂).2 (hs C₁ hC₁).1 (hs C₁ hC₁).2
      ((hr'φ C₁).trans_lt (h21.trans_eq (hr'φ C₂).symm)))

/-- **A gate that reads only one ceiling is labelled `⊥`** at a private type with two opposite
cells: in a legal stage type `Q` on `n + 1` points with literal face `P` along `Fin.castSuccEmb`,
where two cells of `P` of graded index `(univ, n)` are ordered oppositely by two lawful labellings
in the cap ball of the labels of `P` at a cap `c ≠ ⊥` self-visible at `n`, a cell `G` of graded
index `(univ, n)` whose row is `⊥` at every other cell of its graded index except one cell `K`,
which it reads at least as itself, is labelled `⊥`.  The case `K = G` is a gate whose row is `⊥`
at all its twins. -/
theorem label_eq_bot_of_readsOnly_singleton {P : StageType.{u} α n} (Q : StageType.{u} α (n + 1))
    (hQ : Q.IsLegal) (hQP : restrictFace Fin.castSuccEmb Q = some P) {C₁ C₂ : Fin P.card}
    (hC₁ : P.toCellScheme.gradedIndex C₁ = (univ, n))
    (hC₂ : P.toCellScheme.gradedIndex C₂ = (univ, n)) {c : Label.{u}} (hc : IsSelfVisible n c)
    (hc0 : c ≠ ⊥) {p p' : Fin P.card → Label.{u}} (hp : P.rows.IsLawful p)
    (hp' : P.rows.IsLawful p') (hpc : ∀ i, min (P.label i) c = min (p i) c)
    (hp'c : ∀ i, min (P.label i) c = min (p' i) c) (h12 : p C₂ < p C₁) (h21 : p' C₁ < p' C₂)
    {G K : Fin Q.card} (hG : Q.toCellScheme.gradedIndex G = (univ, n))
    (hKG : Q.toCellScheme.gradedIndex K = Q.toCellScheme.gradedIndex G)
    (honly : Q.rows.ReadsOnly G {K})
    (hrow : Q.rows.row G ⟨G, Q.toCellScheme.mem_below_gradedIndex G⟩ ≤ Q.rows.row G ⟨K, hKG.le⟩) :
    Q.label G = ⊥ := by
  by_contra hG0
  exact not_forall_le_of_opposite Q hQ hQP hC₁ hC₂ hc hc0 hp hp' hpc hp'c h12 h21 hG
    (hKG.trans hG) hG0 fun r hr hrG ↦
      CellScheme.Rows.IsLawfulBelow.le_of_readsOnly_singleton hG hKG hr honly hrow hrG

end StageType

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.GatedExtension
import VaughtConjecture.Extension.Gluing

/-!
# Attached gated extensions

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple with
the display's bottom pattern) and 3.3 (the recovery statements, item 1: agreement below a cutoff);
the vocabulary of `VaughtConjecture.Extension.Gate` (private cells, donor cells, display, private
cap, gate, twins, readings).

**The design.**  In a gated extension (`StageType.GatedExtension`) the display labels every twin of
the gate `⊥`; that property fails at every stage
(`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).  In a coupled gated extension
(`StageType.CoupledGatedExtension`) every twin reads the gate at least as the private cap, so the
gate dominates the cap in every lawful labelling; the universal coupled property fails at every
stage above `1` (a result under review, at a private type with a proper anchor): a lawful private
labelling that is `⊥` at an anchor and not at the cap is then carried, through the gate, to a
donor labelling that the donor's rows forbid.  An **attached gated extension** puts the
condition on the row of the gate instead, and places no condition on the labels of the twins:

* a set of **readers**, cells of the graded index `(univ, n)` of the gate whose rows read every
  donor cell as in `CellScheme.Rows.IsGate` (each reader is a gate in the sense of
  `VaughtConjecture.Extension.Gate`, for the same private cap and display);
* the row of the gate is `⊥` at every other cell of its graded index outside the readers
  (`CellScheme.Rows.ReadsOnly`), and reads one reader, the **ceiling**, at least as it reads the
  gate itself;
* the display does not label the gate `⊥`.

A reader may be the gate itself, in which case it may serve as its own ceiling.

**Recovery through the readers** (`CellScheme.Rows.IsLawful.recover_of_readsOnly`).  Let `q` be a
lawful labelling, literally the display on the private cells, and not `⊥` at the gate `G`.  The
row of `G` makes every cell of its graded index outside the readers `⊥`
(`CellScheme.Rows.IsLawful.eq_bot_of_row_eq_bot`), and the ceiling at least `q G`
(`CellScheme.Rows.IsLawful.le_of_row_self_le`).  Availability for the private cap `C` and `G`
gives a cell of the graded index of `G` at least `q C`; it is therefore a reader, or `G`, below the
ceiling (`CellScheme.Rows.IsLawful.exists_mem_le_of_readsOnly`).  That reader is a gate whose value
is at least the label of the cap, and gate recovery from the gate inequality
(`CellScheme.Rows.IsGate.recover_of_cap_le_gate`) gives agreement with the display on every donor
cell below the label of the cap.  Availability may reach a twin of the gate: what is excluded is
a twin that is not a reader, not a twin as such.  No label of the twins is read, and no legality
is used.

**The lifts that legality asks for** (`StageType.AttachedGatedExtension.exists_lift`).  Let `c ≠ ⊥`
be self-visible at `n + 1`, and `a` a lawful labelling of the private face in the cap ball of the
display at `c`.  Bountifulness of the display (`Scheme.IsLegal.exists_isLawful_extend`) gives a
lawful labelling `r` of the display with private face `a` and the observation of the display at
`c`.  The gate is not `⊥` in the display, so not in `r`; so some reader `K` has `r` at least the
cap, and each reading of the row of `K` through an anchor `z` is transported:
`min (r e) (r C) = min (vr_n(r z, i)) (r C)`
(`CellScheme.Rows.IsLawful.min_eq_visibilityReplace_of_row_eq`).  This is forced only at caps
`c ≠ ⊥`, for private labellings that agree with the private labels below `c`; such a labelling is
not `⊥` at any private cell not labelled `⊥`, so no `⊥` is carried from an anchor to a donor cell
(`Label.ne_bot_of_min_eq_of_ne_bot`).  At the cap `⊥`, a lift may label the gate `⊥`, and nothing
is forced through the readers.  This is the difference from the coupled gate, whose bottom
transport condition is forced at the cap `⊥` for every lawful private labelling.

**One dominating cell is not enough** (`StageType.not_forall_le_of_opposite`).  If two cells of
the private face of graded index `(univ, n)` are ordered oppositely by two lawful labellings in the
cap ball of the private labels at a cap `c ≠ ⊥` self-visible at `n`, then in a legal one-point
extension no single cell `K` of graded index `(univ, n)` dominates that graded index in every
labelling lawful below it that is not `⊥` at a cell `G` the extension does not label `⊥`.  The
lifts of the two labellings keep `G` not `⊥`, and `K`, at least the larger of the two cells by
availability, would read them in both orders with one row (`CellScheme.Rows.row_lt_of_le_dominant`).
In particular a gate whose row is `⊥` at every other cell of its graded index except one ceiling
(the gate itself included) is labelled `⊥` by every such extension
(`StageType.label_eq_bot_of_readsOnly_singleton`).  So an attached gated extension of such a
private type has a reader that is neither the gate nor its ceiling, read by the gate not as `⊥`,
and availability can reach it.  The instance is `GatedExtensionCounterexample.P α`
(`VaughtConjecture.Extension.AttachedGateCounterexample`).

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

/-- A minimum with a label `c ≠ ⊥` that agrees with the minimum of a label not `⊥` is not `⊥`
at its first argument. -/
theorem Label.ne_bot_of_min_eq_of_ne_bot {a b c : Label.{u}} (h : min a c = min b c)
    (hb : b ≠ ⊥) (hc : c ≠ ⊥) : a ≠ ⊥ := by
  rintro rfl
  rw [min_eq_left bot_le] at h
  exact (min_eq_bot.mp h.symm).elim hb hc

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {G K C : ι} {S P Q : Set ι}
  {w q : ι → Label.{u}}

/-! ### The row of a gate that reads only a set of cells -/

/-- The row of `G` **reads only `S`** at its graded index: it is `⊥` at every other cell of the
graded index of `G` that is not in `S`. -/
def ReadsOnly (R : D.Rows.{u}) (G : ι) (S : Set ι) : Prop :=
  ∀ t (ht : D.gradedIndex t = D.gradedIndex G), t ≠ G → t ∉ S → R.row G ⟨t, ht.le⟩ = ⊥

namespace IsLawful

/-- A cell `K` of the graded index of `G` that the row of `G` reads at least as `G` itself is at
least `G` in every lawful labelling. -/
theorem le_of_row_self_le (hq : R.IsLawful q) (hKG : D.gradedIndex K = D.gradedIndex G)
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩) : q G ≤ q K := by
  have h := (hq.locality G).le_of_le (d := ⟨G, D.mem_below_gradedIndex G⟩) (d' := ⟨K, hKG.le⟩)
    hrow (congrArg Prod.snd hKG).le
  simp only [min_self] at h
  exact h.trans (min_le_left _ _)

/-- **Availability reaches a member of `S`.**  Let the row of `G` read only `S` at its graded
index, and read some `K ∈ S` of that graded index at least as `G` itself.  In a lawful labelling
not `⊥` at `G`, every cell `C` with scope in that of `G` and of the grade of `G` lies below some
member of `S` of the graded index of `G`. -/
theorem exists_mem_le_of_readsOnly (hq : R.IsLawful q) (honly : R.ReadsOnly G S) (hK : K ∈ S)
    (hKG : D.gradedIndex K = D.gradedIndex G)
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩) (hG : q G ≠ ⊥)
    (hCG : D.scope C ⊆ D.scope G) (hgr : D.grade C = D.grade G) :
    ∃ u ∈ S, D.gradedIndex u = D.gradedIndex G ∧ q C ≤ q u := by
  obtain ⟨u, hu, hle⟩ := hq.availability C G hCG hgr
  by_cases huG : u = G
  · subst huG
    exact ⟨K, hK, hKG, hle.trans (hq.le_of_row_self_le hKG hrow)⟩
  by_cases huS : u ∈ S
  · exact ⟨u, huS, hu, hle⟩
  · have h0 : q u = ⊥ := hq.eq_bot_of_row_eq_bot (t := ⟨u, hu.le⟩) hG (honly u hu huG huS)
    exact ⟨K, hK, hKG, (hle.trans h0.le).trans bot_le⟩

/-- **Recovery through the readers.**  Let the row of `G` read only `S` at its graded index, and
read some `K ∈ S` of that graded index at least as `G` itself, and let every member of `S` be a
gate for the private cap `C`, the private cells `P`, the donor cells `Q`, and the display `w`.  A
lawful labelling `q`, literally `w` on `P` and not `⊥` at `G`, has a member `u` of `S` with
`w C ≤ q u`, and agrees with `w` on every donor cell below `w C`.  Nothing is assumed about the
values of `q` at the twins of `G`. -/
theorem recover_of_readsOnly (hq : R.IsLawful q) (honly : R.ReadsOnly G S)
    (hS : ∀ u ∈ S, R.IsGate u C P Q w) (hK : K ∈ S) (hKG : D.gradedIndex K = D.gradedIndex G)
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩)
    (hlit : ∀ x ∈ P, q x = w x) (hG : q G ≠ ⊥) :
    ∃ u ∈ S, w C ≤ q u ∧ ∀ e ∈ Q, min (q e) (w C) = min (w e) (w C) := by
  have hgK := hS K hK
  have hCG : D.scope C ⊆ D.scope G :=
    hgK.scope_cap_subset.trans (congrArg Prod.fst hKG).le
  have hgr : D.grade C = D.grade G := hgK.grade_cap.trans (congrArg Prod.snd hKG)
  obtain ⟨u, hu, -, hle⟩ := hq.exists_mem_le_of_readsOnly honly hK hKG hrow hG hCG hgr
  rw [hlit C hgK.cap_mem] at hle
  exact ⟨u, hu, hle, (hS u hu).recover_of_cap_le_gate hq hlit hle⟩

/-- **A reading through an anchor, transported.**  If the row of `K` reads `e` as `vr_N` of its
reading of `z`, `N` the grade of `K`, then every lawful labelling `q` labels `e` as `vr_N` of its
own label at `z`, up to its label at `K`: one witness at `K` commutes with the replacement below
`q K` (`Label.IsWitness.min_apply_visibilityReplace`). -/
theorem min_eq_visibilityReplace_of_row_eq (hq : R.IsLawful q) {z e : D.below (D.gradedIndex K)}
    {i : ℕ} (hi : i ≤ D.grade K)
    (hrow : R.row K e = visibilityReplace (D.grade K) i (R.row K z)) :
    min (q e) (q K) = min (visibilityReplace (D.grade K) i (q z)) (q K) := by
  obtain ⟨g, σ, hw, hgN, heq⟩ := hq.exists_gateWitness K
  have hz' : min (σ (R.row K z)) (q K) = min (q z) (q K) := (heq z).symm
  have h' := hw.min_apply_visibilityReplace (hq.orderly K) hgN hz' hi
  rwa [← hrow, ← heq e] at h'

end IsLawful

/-! ### One dominating cell reads every order with one row -/

/-- **A dominating cell orders what it dominates.**  Let `r` be lawful below the graded index `Y`
of a cell `K` and let `K` dominate every cell of graded index `Y`.  If `r` orders two cells `A`,
`B` of the grade of `Y`, with scopes inside that of `Y`, strictly, `r B < r A`, then the row of
`K` orders them strictly the same way: availability puts `A` below a cell of graded index `Y`,
hence below `K`, and locality at `K`, at equal grades, reads `A` and `B` with one witness. -/
theorem row_lt_of_le_dominant {Y : Finset α × ℕ} (hKY : D.gradedIndex K = Y)
    {r : ι → Label.{u}} (hr : R.IsLawfulBelow Y (fun d ↦ r d))
    (hdom : ∀ t, D.gradedIndex t = Y → r t ≤ r K) {A B : ι} (hsA : D.scope A ⊆ Y.1)
    (hgA : D.grade A = Y.2) (hsB : D.scope B ⊆ Y.1) (hgB : D.grade B = Y.2) (hAB : r B < r A) :
    R.row K ⟨B, by rw [CellScheme.mem_below, hKY]; exact (D.gradedIndex_le_iff).mpr ⟨hsB, hgB.le⟩⟩
      < R.row K
        ⟨A, by rw [CellScheme.mem_below, hKY]; exact (D.gradedIndex_le_iff).mpr ⟨hsA, hgA.le⟩⟩ := by
  obtain ⟨-, hl, ha⟩ := isLawfulBelow_iff_forall.mp hr
  have hKmem : K ∈ D.below Y := by rw [CellScheme.mem_below, hKY]
  have hsK : D.scope K = Y.1 := congrArg Prod.fst hKY
  have hgK : D.grade K = Y.2 := congrArg Prod.snd hKY
  have hAK : r A ≤ r K := by
    obtain ⟨u, hu, hle⟩ := ha A K hKmem (hsK ▸ hsA) (hgK ▸ hgA)
    exact hle.trans (hdom u (hu.trans hKY))
  by_contra hnot
  rw [not_lt] at hnot
  have h := (hl K hKmem).le_of_le
    (d := ⟨A, by rw [CellScheme.mem_below, hKY]; exact (D.gradedIndex_le_iff).mpr ⟨hsA, hgA.le⟩⟩)
    (d' := ⟨B, by rw [CellScheme.mem_below, hKY]; exact (D.gradedIndex_le_iff).mpr ⟨hsB, hgB.le⟩⟩)
    hnot (by simp only; rw [hgA, hgB])
  simp only at h
  rw [min_eq_left hAK] at h
  exact absurd (h.trans (min_le_left _ _)) (not_le.mpr hAB)

/-- **A gate whose row reads only one ceiling makes it dominant.**  Let `r` be lawful below the
graded index `Y` of `G`, not `⊥` at `G`, and let the row of `G` be `⊥` at every cell of graded
index `Y` other than `G` and `K`, and read `K` at least as `G`.  Then `K` dominates every cell of
graded index `Y`. -/
theorem IsLawfulBelow.le_of_readsOnly_singleton {Y : Finset α × ℕ} (hGY : D.gradedIndex G = Y)
    (hKG : D.gradedIndex K = D.gradedIndex G) {r : ι → Label.{u}}
    (hr : R.IsLawfulBelow Y (fun d ↦ r d)) (honly : R.ReadsOnly G {K})
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩) (hG : r G ≠ ⊥) :
    ∀ t, D.gradedIndex t = Y → r t ≤ r K := by
  obtain ⟨-, hl, -⟩ := isLawfulBelow_iff_forall.mp hr
  have hGmem : G ∈ D.below Y := by rw [CellScheme.mem_below, hGY]
  have hGK : r G ≤ r K := by
    have h := (hl G hGmem).le_of_le (d := ⟨G, D.mem_below_gradedIndex G⟩) (d' := ⟨K, hKG.le⟩)
      hrow (congrArg Prod.snd hKG).le
    simp only [min_self] at h
    exact h.trans (min_le_left _ _)
  intro t ht
  by_cases htG : t = G
  · exact htG ▸ hGK
  by_cases htK : t = K
  · exact htK ▸ le_rfl
  have ht' : D.gradedIndex t = D.gradedIndex G := ht.trans hGY.symm
  have h0 := (hl G hGmem).eq_bot (d := ⟨t, ht'.le⟩) (honly t ht' htG htK)
  exact ((min_eq_bot.mp h0).resolve_right hG).le.trans bot_le

end CellScheme.Rows

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

/-! ### One dominating cell is not enough -/

/-- **No single dominating cell at a private type with two opposite cells.**  Let `Q` be a legal
stage type on `n + 1` points whose face along `Fin.castSuccEmb` is literally `P`, and let two
cells `C₁`, `C₂` of `P` of graded index `(univ, n)` be ordered oppositely by two lawful labellings
of `P` in the cap ball of its labels at a cap `c ≠ ⊥` self-visible at `n`.  For every cell `G` of
`Q` of graded index `(univ, n)` not labelled `⊥` and every cell `K` of that graded index, some
labelling lawful below `(univ, n)` is not `⊥` at `G` and labels some cell of that graded index
strictly above `K`. -/
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
  let X : Finset (Fin (n + 1)) × ℕ := (univ.map Fin.castSuccEmb, n)
  let Y : Finset (Fin (n + 1)) × ℕ := (univ, n)
  have hX : X ∈ Q.toCellScheme.gradedFaces := ⟨hfQ, hn, by simp [X]⟩
  have hY : Y ∈ Q.toCellScheme.gradedFaces := ⟨Q.univ_mem_faces, hn, by simp [Y]⟩
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  have hgi : ∀ i, (Q.comap Fin.castSuccEmb hfQ).toCellScheme.gradedIndex i = (univ, n) →
      Q.toCellScheme.gradedIndex (φ i) = X := fun i hi ↦ by
    rw [← Q.toScheme.map_comap_gradedIndex Fin.castSuccEmb i]
    -- The face of `Q` along `Fin.castSuccEmb` has the restricted scheme, by definition.
    change Prod.map (Finset.map Fin.castSuccEmb) id
      ((Q.comap Fin.castSuccEmb hfQ).toCellScheme.gradedIndex i) = X
    rw [hi]; rfl
  -- Each labelling of the face lifts, at the cap `c`, to a labelling lawful below `Y`.
  have hlift : ∀ q : Fin (Q.comap Fin.castSuccEmb hfQ).card → Label.{u},
      (Q.comap Fin.castSuccEmb hfQ).rows.IsLawful q →
      (∀ i, min ((Q.comap Fin.castSuccEmb hfQ).label i) c = min (q i) c) →
      ∃ r : Fin Q.card → Label.{u}, Q.rows.IsLawfulBelow Y (fun x ↦ r x) ∧ r G ≠ ⊥ ∧
        ∀ i, r (φ i) = q i := fun q hq hqc ↦ by
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
      change min (Q.label d) c = min (x d) c
      rw [← hi, hxφ i]; exact hqc i
    obtain ⟨r', hr', hcap, hres⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
      (hQ.isBountiful hX hY hXY) c hc (fun d ↦ x d) (fun d ↦ Q.label d) hxX
      (Q.isLawful.isLawfulBelow Y) hcapX
    let r := CellScheme.Rows.extendBot Y r'
    have hrY : ∀ y (hy : y ∈ Q.toCellScheme.below Y), r y = r' ⟨y, hy⟩ :=
      fun y hy ↦ CellScheme.Rows.extendBot_of_mem r' hy
    have hGY : G ∈ Q.toCellScheme.below Y := by rw [CellScheme.mem_below, hG]
    refine ⟨r, CellScheme.Rows.isLawfulBelow_extendBot.mpr hr', ?_, fun i ↦ ?_⟩
    · rw [hrY G hGY]
      exact Label.ne_bot_of_min_eq_of_ne_bot (hcap ⟨G, hGY⟩) hG0 hc0
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
  obtain ⟨r, hr, hrG, hrφ⟩ := hlift p hp hpc
  obtain ⟨r', hr', hr'G, hr'φ⟩ := hlift p' hp' hp'c
  have hs : ∀ i, (Q.comap Fin.castSuccEmb hfQ).toCellScheme.gradedIndex i = (univ, n) →
      Q.toCellScheme.scope (φ i) ⊆ Y.1 ∧ Q.toCellScheme.grade (φ i) = Y.2 := fun i hi ↦
    ⟨subset_univ _, congrArg Prod.snd (hgi i hi)⟩
  exact lt_asymm
    (CellScheme.Rows.row_lt_of_le_dominant hK hr (hdom r hr hrG) (hs C₁ hC₁).1 (hs C₁ hC₁).2
      (hs C₂ hC₂).1 (hs C₂ hC₂).2 ((hrφ C₂).trans_lt (h12.trans_eq (hrφ C₁).symm)))
    (CellScheme.Rows.row_lt_of_le_dominant hK hr' (hdom r' hr' hr'G) (hs C₂ hC₂).1
      (hs C₂ hC₂).2 (hs C₁ hC₁).1 (hs C₁ hC₁).2 ((hr'φ C₁).trans_lt (h21.trans_eq (hr'φ C₂).symm)))

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

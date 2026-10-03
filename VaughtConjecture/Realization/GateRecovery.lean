/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.GatedExtension
import VaughtConjecture.Realization.Families

/-!
# Gate recovery for realized occurrences

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the occurrence realized by the
bottom-pattern clause) and 3.3 (the recovery statements, item 1: agreement below a cutoff); the
stage-level form of `CellScheme.Rows.IsGate.recover` (`VaughtConjecture.Extension.Gate`).

**The bottom pattern transfers at grades at most `n`.**  A stage type `q` on `n + 1` points in the
bottom-pattern family of a labelling `ρ` of a scheme `S` ([Kni26, Definition 3.2.1, clause 4(a)ii])
is bottom at a cell of grade at most `n` exactly when `ρ` is
(`label_ne_bot_of_mem_bottomPatternFamily`, `label_eq_bot_of_mem_bottomPatternFamily`).  A cell of
grade `n + 1` is not tested (`VaughtConjecture.Realization.GateRecoveryExamples`).  The gate of a
gated extension has grade `n`, so a member of the bottom-pattern family of the display does not
label the gate `⊥`, and labels its twins `⊥` (`GatedExtension.label_gate_ne_bot_of_mem`): this is
the **gate equation** of the roadmap.

**Gate recovery for realizations** (`GatedExtension.mem_receivingFamily`).  Let `E` be a gated
extension of `P` over `f` with donor `d` (`StageType.GatedExtension`), and let `q` be a stage type
on the scheme of the display whose face along `Fin.castSuccEmb` is literally `P` and which has the
display's bottom pattern on the cells of grade at most `n`.  Then the donor face `d'` of `q`, along
`extendByLast f`, has the scheme of `d` and agrees with `d` below the label of the cap:
`d' ∈ receivingFamily d (E.display.label E.cap)`.  The donor face is defined
(`GatedExtension.exists_restrictFace_mem_receivingFamily`), and agreement passes to every lower
cutoff (`GatedExtension.mem_receivingFamily_of_le`, by `StageType.mem_receivingFamily_of_le`).  The
proof reads the display only through its bottom pattern: the literal private face gives the
literal hypothesis of `CellScheme.Rows.IsGate.recover`, and the bottom pattern at the gate's
graded index, of grade `n`, gives its twin hypothesis.  It is stated for any display with gate
data (`mem_receivingFamily_of_isGate`); the labels of `q` are lawful because `q` is a stage type,
and no legality of `q` or of the display is used.

**What is unconditional and what is not.**  Every statement here is a theorem about a given gated
extension.  No gated extension is exhibited: its legality needs the construction, and the gated
pinned extension property `StageType.HasGatedPinnedExtensions` that would supply one is a
hypothesis, still to be proved.  Finite-cut receiving (R1) is not claimed.  Its assembly still
needs:

* the acquisition of the private context in a model: an occurrence of arity `n ≥ m + 2`
  containing the root as a literal face, with a cell of graded index `(univ, n)` whose label is not
  `⊥` and lies above the requested cutoff, and a donor anchored below it
  (`StageType.IsAnchored`), through uniformity, high-arity dominance, and generalized saturation
  as in [Kni26, Lemma 8.1.1];
* the gated extension, from `HasGatedPinnedExtensions`;
* the realization of its bottom pattern over the private tuple by the bottom-pattern clause of the
  model (`Realization.IsModel.bottomPattern_of_isLawful` with `ρ` the display's labels), which
  gives a coface `q` of the private type in the bottom-pattern family of the display, and then the
  agreement here, at the requested cutoff.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### The bottom pattern at grades at most `n` -/

section BottomPattern

variable {q : StageType.{u} α (n + 1)} {S : Scheme.{u} (n + 1)} {ρ : Fin S.card → Label.{u}}

/-- **The bottom pattern transfers at grades at most `n`**: a member of the bottom-pattern family
of `ρ` is not bottom at a cell of grade at most `n` where `ρ` is not bottom. -/
theorem label_ne_bot_of_mem_bottomPatternFamily (hq : q ∈ bottomPatternFamily S ρ)
    (i : Fin q.card) (j : Fin S.card) (hij : (i : ℕ) = j) (hgr : q.toCellScheme.grade i ≤ n)
    (hρ : ρ j ≠ ⊥) : q.label i ≠ ⊥ :=
  fun h ↦ hρ ((hq.2 i j hij hgr).mp h)

/-- A member of the bottom-pattern family of `ρ` is bottom at a cell of grade at most `n` where
`ρ` is bottom. -/
theorem label_eq_bot_of_mem_bottomPatternFamily (hq : q ∈ bottomPatternFamily S ρ)
    (i : Fin q.card) (j : Fin S.card) (hij : (i : ℕ) = j) (hgr : q.toCellScheme.grade i ≤ n)
    (hρ : ρ j = ⊥) : q.label i = ⊥ :=
  (hq.2 i j hij hgr).mpr hρ

end BottomPattern

/-! ### Gate recovery for stage types -/

/-- **Gate recovery for stage types.**  Let `Q` on `n + 1` points have literal faces `P` along
`Fin.castSuccEmb` and `d` along `extendByLast f`, and gate data at a cell `G` of grade at most `n`
with cap `C`, its twins labelled `⊥`.  A stage type `q` with literal face `P` in the bottom-pattern
family of the labels of `Q` has a donor face that agrees with `d` below the label of `C`. -/
theorem mem_receivingFamily_of_isGate {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} {Q : StageType.{u} α (n + 1)} {G C : Fin Q.card}
    (hQP : restrictFace Fin.castSuccEmb Q = some P)
    (hQd : restrictFace (extendByLast f) Q = some d) (hG : Q.toCellScheme.grade G ≤ n)
    (htwin : ∀ t, Q.toCellScheme.gradedIndex t = Q.toCellScheme.gradedIndex G → t ≠ G →
      Q.label t = ⊥)
    (hgate : Q.rows.IsGate G C (Q.toCellScheme.visible (Set.range Fin.castSuccEmb))
      (Q.toCellScheme.visible (Set.range (extendByLast f))) Q.label)
    {q : StageType.{u} α (n + 1)} (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily Q.toScheme Q.label) {d' : StageType.{u} α (m + 1)}
    (hd' : restrictFace (extendByLast f) q = some d') :
    d' ∈ receivingFamily d (Q.label C) := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain ⟨rfl, hpat⟩ := hq
  obtain ⟨-, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hQd
  obtain ⟨-, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hd'
  obtain ⟨_, hQP⟩ := (restrictFace_eq_some_iff _ _).mp hQP
  obtain ⟨_, hqP⟩ := (restrictFace_eq_some_iff _ _).mp hP
  -- The literal private face: `ℓ` is the display's labelling on the private cells.
  have hlit : ∀ x ∈ Q.toCellScheme.visible (Set.range Fin.castSuccEmb), ℓ x = Q.label x := by
    intro x hx
    have hx' : x ∈ Set.range (Q.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]
      exact hx
    obtain ⟨i, rfl⟩ := hx'
    exact label_congr (hqP.trans hQP.symm) (i := i) (j := i) rfl
  -- The bottom pattern at the gate's graded index, of grade at most `n`: the twins are bottom.
  have htwin' : ∀ t, Q.toCellScheme.gradedIndex t = Q.toCellScheme.gradedIndex G → t ≠ G →
      ℓ t = ⊥ := fun t ht htG ↦
    (hpat t t rfl ((congrArg Prod.snd ht).trans_le hG)).mpr (htwin t ht htG)
  have hrec := (hgate.recover hℓ hlit htwin').2
  refine ⟨rfl, fun i j hij ↦ ?_⟩
  obtain rfl := Fin.ext hij
  exact hrec _ (Scheme.mem_visibleCells.mp (Q.cellMap_mem _ i))

namespace GatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : GatedExtension P f d) {q : StageType.{u} α (n + 1)}

/-- **The gate equation**: a member of the bottom-pattern family of the display does not label
the gate `⊥`. -/
theorem label_gate_ne_bot_of_mem (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    (i : Fin q.card) (hi : (i : ℕ) = E.gate) : q.label i ≠ ⊥ := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain ⟨rfl, hpat⟩ := hq
  obtain rfl := Fin.ext hi
  exact label_ne_bot_of_mem_bottomPatternFamily ⟨rfl, hpat⟩ _ _ rfl E.grade_gate.le
    E.label_gate_ne_bot

/-- **Gate recovery for a gated extension.**  A stage type with literal private face `P` in the
bottom-pattern family of the display has a donor face that agrees with the donor `d` below the
label of the cap. -/
theorem mem_receivingFamily (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    {d' : StageType.{u} α (m + 1)} (hd' : restrictFace (extendByLast f) q = some d') :
    d' ∈ receivingFamily d (E.display.label E.cap) :=
  mem_receivingFamily_of_isGate E.restrictFace_castSuccEmb E.restrictFace_extendByLast
    E.grade_gate.le (fun t ht htG ↦ E.label_twin t (ht.trans E.gradedIndex_gate) htG) E.isGate
    hP hq hd'

/-- **Gate recovery at a cutoff**: agreement with the donor below every cutoff at most the label
of the cap. -/
theorem mem_receivingFamily_of_le (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    {d' : StageType.{u} α (m + 1)} (hd' : restrictFace (extendByLast f) q = some d')
    {c : Label.{u}} (hc : c ≤ E.display.label E.cap) : d' ∈ receivingFamily d c :=
  StageType.mem_receivingFamily_of_le (E.mem_receivingFamily hP hq hd') hc

/-- **The donor face is defined**: a stage type in the bottom-pattern family of the display has a
face along `extendByLast f`, which agrees with the donor below the label of the cap. -/
theorem exists_restrictFace_mem_receivingFamily (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label) :
    ∃ d' : StageType.{u} α (m + 1), restrictFace (extendByLast f) q = some d' ∧
      d' ∈ receivingFamily d (E.display.label E.cap) := by
  have hf : univ.map (extendByLast f) ∈ q.toCellScheme.faces := by
    rw [hq.1, ← isSome_restrictFace_iff, E.restrictFace_extendByLast]
    rfl
  exact ⟨_, restrictFace_of_mem q _ hf, E.mem_receivingFamily hP hq (restrictFace_of_mem q _ hf)⟩

end GatedExtension

end StageType

end VaughtConjecture

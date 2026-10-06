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
label the gate `⊥` (`GatedExtension.label_gate_ne_bot_of_mem`): this is the **gate equation** of
the roadmap.  It labels the twins of the gate `⊥` (`GatedExtension.label_twin_eq_bot_of_mem`).

**Gate recovery for realizations** (`GatedExtension.recover`).  Let `E` be a gated extension of
`P` over `f` with donor `d` (`StageType.GatedExtension`), and let `q` be a stage type on the
scheme of the display whose face along `Fin.castSuccEmb` is literally `P` and which has the
display's bottom pattern on the cells of grade at most `n`.  Then the donor face `d'` of `q`, along
`extendByLast f`, has the scheme of `d` and agrees with `d` below the label of the cap:
`d' ∈ receivingFamily d (E.display.label E.cap)`.  The donor face is defined
(`GatedExtension.exists_restrictFace_mem_receivingFamily`), and agreement passes to every lower
cutoff (`GatedExtension.recover_of_le`, by `StageType.mem_receivingFamily_of_le`).  Of the labels
of the display, the proof reads only their bottom pattern, besides the private labels, which are
those of `P`; it also uses that `q` has the scheme and rows of the display.  The literal private
face gives the literal hypothesis of `CellScheme.Rows.IsGate.recover`, and the bottom pattern at
the gate's graded index, of grade `n`, gives its twin hypothesis.  It is stated for any display
with gate data (`mem_receivingFamily_of_isGate`); the labels of `q` are lawful because `q` is a
stage type, and no legality of `q` or of the display is used.

**Gate recovery with the twin–gate coupling** (`mem_receivingFamily_of_twinsReadGate`).  When the
rows of `Q` couple the twins of the gate to it (`CellScheme.Rows.TwinsReadGate`: every twin reads
the gate at least as the cap), the same conclusion holds for every stage type `q` on the scheme of
`Q` with literal private face, a member of the family of generalized saturation
(`Realization.saturationFamily`): neither the bottom pattern of `q` nor a bound on the grade of the
gate is used, since the gate inequality then holds for every lawful labelling of the rows
(`CellScheme.Rows.IsGate.recover_of_twinsReadGate`).  For a coupled gated extension
(`StageType.CoupledGatedExtension`) the donor face is defined
(`CoupledGatedExtension.exists_restrictFace_mem_receivingFamily`).

**What is unconditional and what is not.**  Every statement here is a theorem about a given gated
extension, and stands.  Gated extensions exist for some inputs
(`StageType.GatedExtension.instance_two_zero`), but the universal gated extension hypothesis
`StageType.HasGatedPinnedExtensions`, which would supply one for every private context, fails at
every stage (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`): the private type
`GatedExtensionCounterexample.P α`, whose two cells of full scope and full grade are ordered
oppositely by two lawful labellings in the cap ball of its labelling at `2`, has no gated extension
(`GatedExtensionCounterexample.isEmpty_gatedExtension`).  Finite-cut receiving for all models, (R1),
is not claimed here; it is open in general.  The private context is acquired by the uniformity and
high-arity-dominance clauses, with exact consistency (no generalized saturation)
(`Realization.IsModel.exists_privateContext`).  The bottom-pattern clause of a model
(`Realization.IsModel.bottomPattern`), applied over an occurrence of the private type to the scheme
and labels of a display, realizes a member of the bottom-pattern family read here; its guard is met,
since the display is a legal coface of the private type in that family.  With the coupled gate,
generalized saturation suffices in place of the bottom-pattern clause; a route to (R1) through these
pieces needs coupled gated extensions over every private context
(`StageType.HasCoupledGatedPinnedExtensions`, a named hypothesis that is false at every stage above
`1`, `CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`), and finite-cut
receiving is proved conditional on it in `VaughtConjecture.Realization.CoupledFiniteCutReceiving`.

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

/-- A member of the bottom-pattern family of the display labels the twins of the gate `⊥`. -/
theorem label_twin_eq_bot_of_mem
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label) (i : Fin q.card)
    (t : Fin E.display.card) (hi : (i : ℕ) = t)
    (ht : E.display.toCellScheme.gradedIndex t = (univ, n)) (htG : t ≠ E.gate) :
    q.label i = ⊥ := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain ⟨rfl, hpat⟩ := hq
  obtain rfl := Fin.ext hi
  exact label_eq_bot_of_mem_bottomPatternFamily ⟨rfl, hpat⟩ _ _ rfl (congrArg Prod.snd ht).le
    (E.label_twin _ ht htG)

/-- **Gate recovery for a gated extension.**  A stage type with literal private face `P` in the
bottom-pattern family of the display has a donor face that agrees with the donor `d` below the
label of the cap. -/
theorem recover (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    {d' : StageType.{u} α (m + 1)} (hd' : restrictFace (extendByLast f) q = some d') :
    d' ∈ receivingFamily d (E.display.label E.cap) :=
  mem_receivingFamily_of_isGate E.restrictFace_castSuccEmb E.restrictFace_extendByLast
    E.grade_gate.le (fun t ht htG ↦ E.label_twin t (ht.trans E.gradedIndex_gate) htG) E.isGate
    hP hq hd'

/-- **Gate recovery at a cutoff**: agreement with the donor below every cutoff at most the label
of the cap. -/
theorem recover_of_le (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    {d' : StageType.{u} α (m + 1)} (hd' : restrictFace (extendByLast f) q = some d')
    {c : Label.{u}} (hc : c ≤ E.display.label E.cap) : d' ∈ receivingFamily d c :=
  mem_receivingFamily_of_le (E.recover hP hq hd') hc

/-- **The donor face is defined**: a stage type in the bottom-pattern family of the display has a
face along `extendByLast f`, which agrees with the donor below the label of the cap. -/
theorem exists_restrictFace_mem_receivingFamily (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label) :
    ∃ d' : StageType.{u} α (m + 1), restrictFace (extendByLast f) q = some d' ∧
      d' ∈ receivingFamily d (E.display.label E.cap) := by
  have hf : univ.map (extendByLast f) ∈ q.toCellScheme.faces := by
    rw [hq.1, ← isSome_restrictFace_iff, E.restrictFace_extendByLast]
    rfl
  exact ⟨_, restrictFace_of_mem q _ hf, E.recover hP hq (restrictFace_of_mem q _ hf)⟩

end GatedExtension

/-! ### Gate recovery with the twin–gate coupling -/

/-- **Gate recovery for stage types with the twin–gate coupling.**  Let `Q` on `n + 1` points have
literal faces `P` along `Fin.castSuccEmb` and `d` along `extendByLast f`, and gate data at a cell
`G` with cap `C`, whose twins read `G` at least as `C` (`CellScheme.Rows.TwinsReadGate`).  A stage
type `q` on the scheme of `Q` with literal face `P` has a donor face that agrees with `d` below the
label of `C`.  No bottom pattern and no bound on the grade of `G` is assumed: the coupling is a
condition on the rows, which `q` shares with `Q`. -/
theorem mem_receivingFamily_of_twinsReadGate {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {d : StageType.{u} α (m + 1)} {Q : StageType.{u} α (n + 1)} {G C : Fin Q.card}
    (hQP : restrictFace Fin.castSuccEmb Q = some P)
    (hQd : restrictFace (extendByLast f) Q = some d) (htw : Q.rows.TwinsReadGate G C)
    (hgate : Q.rows.IsGate G C (Q.toCellScheme.visible (Set.range Fin.castSuccEmb))
      (Q.toCellScheme.visible (Set.range (extendByLast f))) Q.label)
    {q : StageType.{u} α (n + 1)} (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ saturationFamily Q.toScheme) {d' : StageType.{u} α (m + 1)}
    (hd' : restrictFace (extendByLast f) q = some d') :
    d' ∈ receivingFamily d (Q.label C) := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain rfl : S = Q.toScheme := hq
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
  have hrec := (hgate.recover_of_twinsReadGate hℓ hlit htw).2
  refine ⟨rfl, fun i j hij ↦ ?_⟩
  obtain rfl := Fin.ext hij
  exact hrec _ (Scheme.mem_visibleCells.mp (Q.cellMap_mem _ i))

/-- **The donor face of a coupled gated extension is defined, and agrees with the donor below the
cap**, for every stage type on the scheme of the display with literal private face `P`: a member
of the family of generalized saturation over the scheme of the display. -/
theorem CoupledGatedExtension.exists_restrictFace_mem_receivingFamily
    {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
    (E : CoupledGatedExtension P f d) {q : StageType.{u} α (n + 1)}
    (hP : restrictFace Fin.castSuccEmb q = some P) (hq : q ∈ saturationFamily E.display.toScheme) :
    ∃ d' : StageType.{u} α (m + 1), restrictFace (extendByLast f) q = some d' ∧
      d' ∈ receivingFamily d (E.display.label E.cap) := by
  have hf : univ.map (extendByLast f) ∈ q.toCellScheme.faces := by
    have hq' : q.toScheme = E.display.toScheme := hq
    rw [hq', ← isSome_restrictFace_iff, E.restrictFace_extendByLast]
    rfl
  exact ⟨_, restrictFace_of_mem q _ hf,
    mem_receivingFamily_of_twinsReadGate E.restrictFace_castSuccEmb E.restrictFace_extendByLast
      E.twinsReadGate E.isGate hP hq (restrictFace_of_mem q _ hf)⟩

end StageType

end VaughtConjecture

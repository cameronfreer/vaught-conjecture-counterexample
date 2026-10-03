/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.Gate
import VaughtConjecture.Extension.WitnessAlgebra

/-!
# Examples: gate recovery

Roadmap, Layer 3, 3.3 (the recovery statements, item 1) and the vocabulary of Layer 3; regressions
for `VaughtConjecture.Extension.Gate`.

The schemes are abstract cell schemes with explicit rows and labels: no legality, coding, or
well-formedness is claimed.  The labels are natural numbers, `ω + n` (`om n`), `⊥`, and `⊤`; the
witnesses are the identity with its suppressor capped at a self-visible label
(`Label.IsWitness.cap`), killing the finite block (`x < ω ↦ ⊥`, the identity from `ω` on), and
flattening finite parts at `3` (`Label.isWitness_comp_flatten`).  The points are `a, b, c` (the
private context) and the new point `y`; the private cells are the cells visible in the private
points, and the donor cells the cells visible in the root and `y`.  Each lawfulness proof checks
the order law, the locality at every cell with an explicit witness, and availability.

**Positive cases.**

* **P1** (`one_recover`): one private point and an empty root; the gate's row reads the donor
  cells by `bot`, `botAnchor`, and `top`.  The bottom donor labels are recovered, and the donor
  top comes back as a value at least the cap's label, the formal top itself when that label is
  `⊤`.  This exercises the lemma alone: in (R1) the private context has at least two more points
  than the root.
* **P2, P4, P6** (`block_recover`): an empty root, so every donor cell is new; anchors labelled `1`
  and `ω + 1` in two blocks at threshold `3`, and the cap labelled `⊤`.  The donor labels `2`,
  `ω + 2`, and `⊤` are recovered exactly; the display is lawful (`isLawful_blockLabel`).
* **P3** (`root_eq`): the root cell, labelled `ω + 1`, anchors the donor label `ω + 2`; no separate
  reference cell is needed.
* **P5** (`root_cutoff`): the cap labelled `ω + 3`, the actual cut of the anchor block `ω` at
  threshold `3`; agreement below `ω + 3` gives agreement below the cutoff `ω + 1`.
* **P7** (`root_gate_ne_bot`): without twins, no lawful labelling with the literal private face and
  a cap not bottom has a bottom gate.
* **An anchor above the cap** (`root_anchor_above_cap`): with the cap labelled `3` below the anchor
  `ω + 1`, the donor label `ω + 2` still comes back as a value at least `3`; the reading `ref` does
  not bound the anchor by the cap.

The display of the root example is lawful for every cap label self-visible at `3`
(`isLawful_rootDisplay`).

**Negative controls.**

* **NC1** (`twin_bottom_gate`) and **NC2** (`twin_small_gate`): the root example with a twin of
  the gate.  The gate data hold and the display is lawful, but lawful labellings with the literal
  private face and the twin labelled `⊤`, with the gate `⊥` (NC1) or `3` (NC2), label the donor
  cell `⊤` instead of `ω + 2`, which differs below the actual cut `ω + 3`.  So a literal private
  face and a non-bottom gate do not suffice when the gate has twins; the bottom pattern of the
  whole graded index of the gate is the hypothesis of recovery.
* **NC3** (`root_top_at_cap`): with the cap labelled `ω + 3`, a lawful labelling with the literal
  private face realizes the donor top as `ω + 3`; there is no agreement above the cap.
* **NC4** (`high_not_recovered`): a donor label `ω + 4` whose finite part is at least the
  threshold `3` has no reading, and a lawful labelling realizes it as `ω + 3`; the threshold must
  exceed the finite parts of the donor labels.
* **NC5** (`lowCap_not_recovered`): a cap of grade `2`, below the gate's grade `3`, does not reach
  the gate by availability; with every reading in place and no twin, a lawful labelling with the
  literal private face and a bottom gate loses the donor label.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

Witnesses are [Kni26, Definition 2.3.9]; lawful sections, with locality and availability, are
[Kni26, Definition 2.5.4].
-/

namespace VaughtConjecture.GateExamples

open Finset CellScheme CellScheme.Rows Label
open scoped Ordinal

/-! ### Labels of the block `ω` -/

/-- The label `ω + n`. -/
noncomputable def om (n : ℕ) : Label.{0} := ((ω + (n : Ordinal.{0}) : Ordinal.{0}) : Label.{0})

private theorem om_mod (n : ℕ) : (ω + (n : Ordinal.{0})) % ω = n := by
  simpa using omega0_mul_add_natCast_mod (1 : Ordinal.{0}) n

private theorem om_div (n : ℕ) : (ω + (n : Ordinal.{0})) / ω = 1 := by
  simpa using omega0_mul_add_natCast_div (1 : Ordinal.{0}) n

/-- `ω + n` is self-visible at `k` exactly when `k ≤ n`. -/
@[simp] private theorem isSelfVisible_om {k n : ℕ} : IsSelfVisible k (om n) ↔ k ≤ n := by
  rw [om, isSelfVisible_coe, om_mod, Nat.cast_le]

/-- Visibility replacement of `ω + n`. -/
@[simp] private theorem visibilityReplace_om (k i n : ℕ) :
    visibilityReplace k i (om n) = if n < k then om i else om n := by
  unfold om
  rw [visibilityReplace_coe]
  split_ifs with h
  · rw [Ordinal.visibilityReplace_of_lt (by rw [om_mod]; exact_mod_cast h), om_div, mul_one]
  · rw [Ordinal.visibilityReplace_of_le (by rw [om_mod]; exact_mod_cast not_lt.mp h)]

@[simp] private theorem om_le_om {m n : ℕ} : om m ≤ om n ↔ m ≤ n := by
  simp only [om, WithBot.coe_le_coe, WithTop.coe_le_coe, add_le_add_iff_left, Nat.cast_le]

@[simp] private theorem om_inj {m n : ℕ} : om m = om n ↔ m = n := by
  rw [le_antisymm_iff, om_le_om, om_le_om, ← le_antisymm_iff]

@[simp] private theorem natCast_lt_om (m n : ℕ) : (m : Label.{0}) < om n := by
  rw [om, ← WithBot.coe_natCast, ← WithTop.coe_natCast]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((Ordinal.natCast_lt_omega0 m).trans_le le_self_add))

@[simp] private theorem ofNat_lt_om (m n : ℕ) [m.AtLeastTwo] :
    (ofNat(m) : Label.{0}) < om n :=
  natCast_lt_om m n

@[simp] private theorem ofNat_le_om (m n : ℕ) [m.AtLeastTwo] :
    (ofNat(m) : Label.{0}) ≤ om n :=
  (ofNat_lt_om m n).le

/-- The face `{a, b, c}` is not the whole ground set `{a, b, c, y}`. -/
@[simp] private theorem triple_ne_univ : ({0, 1, 2} : Finset (Fin 4)) ≠ univ := by decide

@[simp] private theorem om_lt_top (n : ℕ) : om n < ⊤ :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

@[simp] private theorem om_ne_top (n : ℕ) : om n ≠ ⊤ := (om_lt_top n).ne

@[simp] private theorem om_ne_bot (n : ℕ) : om n ≠ ⊥ := WithBot.coe_ne_bot

/-! ### Witnesses -/

/-- The start `ω` of the block `ω`, as a label. -/
private noncomputable abbrev omega : Label.{0} := ((ω : Ordinal.{0}) : Label.{0})

/-- **Kill the finite block**: bottom below `ω`, the identity from `ω` on. -/
private noncomputable def killFinite (x : Label.{0}) : Label.{0} :=
  open Classical in if x < omega then ⊥ else x

private theorem killFinite_om (n : ℕ) : killFinite (om n) = om n :=
  ite_eq_right (not_lt.mpr (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)))

private theorem killFinite_ofNat (n : ℕ) [n.AtLeastTwo] :
    killFinite (ofNat(n) : Label.{0}) = ⊥ := by
  refine ite_eq_left ?_
  rw [← Nat.cast_ofNat, ← WithBot.coe_natCast, ← WithTop.coe_natCast]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (Ordinal.natCast_lt_omega0 _))

private theorem killFinite_top : killFinite ⊤ = ⊤ := ite_eq_right (not_lt.mpr le_top)

/-- Killing the finite block is a witness. -/
private theorem isWitness_killFinite : IsWitness (fun _ ↦ (⊤ : Label.{0})) killFinite where
  antitone := antitone_const
  isSelfVisible _ := isSelfVisible_top _
  map_bot := ite_eq_left (WithBot.bot_lt_coe _)
  monotone x y hxy := by
    unfold killFinite
    by_cases hy : y < omega
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
    by_cases hx : x < omega
    · rw [ite_eq_left hx]; exact bot_le
    rw [ite_eq_right hx, ite_eq_right hy]
    exact hxy
  visibilityReplace_comm x k _ i _ := by
    have hlt := visibilityReplace_lt_iff (k := k) (i := i) (x := x)
      Ordinal.isSuccLimit_omega0.isSuccPrelimit
    unfold killFinite
    by_cases hxs : x < omega
    · rw [ite_eq_left hxs, ite_eq_left (hlt.mpr hxs), visibilityReplace_bot]
    · rw [ite_eq_right hxs, ite_eq_right (mt hlt.mp hxs)]

/-! ### Checking the laws cell by cell -/

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{0}} {q : ι → Label.{0}}

/-- Locality at `s` from the identity capped at a label `c` self-visible at the grade of `s`. -/
private theorem locality_capped {s : ι} {c : Label.{0}} (hc : IsSelfVisible (D.grade s) c)
    (h : ∀ d (hd : D.gradedIndex d ≤ D.gradedIndex s),
      min (q d) (q s) = min (R.row s ⟨d, hd⟩) c) :
    TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
      fun d ↦ min (q d) (q s) := by
  refine ⟨_, id, IsWitness.id_top.cap hc, fun d ↦ ?_⟩
  have hd : D.grade d.1 ≤ D.grade s := ((D.mem_below).mp d.2).2
  change min (q d) (q s) = min (R.row s d) (if D.grade d ≤ D.grade s then min ⊤ c else ⊥)
  rw [ite_eq_left hd, min_top_left]
  exact h d.1 d.2

/-- Locality at `s` from a given witness. -/
private theorem locality_of {s : ι} {g : ℕ → Label.{0}} {σ : Label.{0} → Label.{0}}
    (hw : IsWitness g σ)
    (h : ∀ d (hd : D.gradedIndex d ≤ D.gradedIndex s),
      min (q d) (q s) = min (σ (R.row s ⟨d, hd⟩)) (g (D.grade d))) :
    TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
      fun d ↦ min (q d) (q s) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

/-! ### The root as anchor (P3, P5, P7, the anchor above the cap, NC3)

Points `a, b, c, y` (`0, 1, 2, 3`).  Cells: the root cell `ρ = ({a}, 1)`, the private cap
`C = ({a, b, c}, 3)`, two donor cells `f, f' = ({y}, 1)`, and the gate `G = (univ, 3)`. -/

/-- The scheme of the root as anchor. -/
def rootScheme : CellScheme (Fin 5) (Fin 4) :=
  ⟨univ, {{0}, {0, 1, 2}, {3}, univ}, ![{0}, {0, 1, 2}, {3}, {3}, univ], ![1, 3, 1, 1, 3]⟩

/-- The rows: `ρ ↦ ω + 1`, `C ↦ ⊤`, `f ↦ ω + 2`, `f' ↦ ⊤`, `G ↦ ⊤`, at every cell. -/
noncomputable def rootRows : rootScheme.Rows.{0} :=
  ⟨fun _ t ↦ ![om 1, ⊤, om 2, ⊤, ⊤] t.1⟩

/-- The labelling with private cap `s` and the second donor cell `t`: `(ω + 1, s, ω + 2, t, s)`;
with `t = ⊤` it is the display. -/
noncomputable def rootLabel (s t : Label.{0}) : Fin 5 → Label.{0} := ![om 1, s, om 2, t, s]

/-- The private cells `ρ, C`: the cells visible in `{a, b, c}`. -/
def rootPrivate : Set (Fin 5) := {0, 1}

/-- The donor cells `ρ, f, f'`: the cells visible in `{a, y}`. -/
def rootDonor : Set (Fin 5) := {0, 2, 3}

/-- The labelling `(ω + 1, s, ω + 2, t, s)` is lawful when `s` is self-visible at `3`, `t` at
`1`, and `t ≥ ω + 2, s`: every row, capped at the label of its cell, is its target. -/
theorem isLawful_rootLabel {s t : Label.{0}} (hs : IsSelfVisible 3 s) (ht : IsSelfVisible 1 t)
    (h2t : om 2 ≤ t) (hst : s ≤ t) : rootRows.IsLawful (rootLabel s t) where
  orderly d := by fin_cases d <;> simp [rootLabel, rootScheme, hs, ht]
  locality c := by
    fin_cases c
    · exact locality_capped (c := om 1) (by simp [rootScheme]) fun d hd ↦ by
        fin_cases d <;> simp [rootScheme, rootRows, rootLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := s) hs fun d hd ↦ by
        fin_cases d <;> simp [rootScheme, rootRows, rootLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := om 2) (by simp [rootScheme]) fun d hd ↦ by
        fin_cases d <;>
          simp [rootScheme, rootRows, rootLabel, gradedIndex, min_eq_right h2t] at hd ⊢
    · exact locality_capped (c := t) ht fun d hd ↦ by
        fin_cases d <;> simp [rootScheme, rootRows, rootLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := s) hs fun d hd ↦ by
        fin_cases d <;>
          simp [rootScheme, rootRows, rootLabel, gradedIndex, min_eq_right hst] at hd ⊢
  availability a b hab hg := by
    have key : ∀ a b : Fin 5, rootScheme.scope a ⊆ rootScheme.scope b →
        rootScheme.grade a = rootScheme.grade b →
        rootScheme.gradedIndex a = rootScheme.gradedIndex b ∨ a = 1 ∧ b = 4 := by decide
    rcases key a b hab hg with h | ⟨rfl, rfl⟩
    · exact ⟨a, h, le_rfl⟩
    · exact ⟨4, rfl, le_rfl⟩

/-- The gate of the root example is its only cell of graded index `(univ, 3)`. -/
theorem root_unique (c : Fin 5) (hc : rootScheme.gradedIndex c = rootScheme.gradedIndex 4) :
    c = 4 := by
  revert c
  decide

/-- **Gate data** of the root example, for every private cap label `s ≠ ⊥`: the root cell `ρ`
anchors `f` (`ω + 2 = vr_3(ω + 1, 2)`), and `f'` is read at the cap. -/
theorem isGate_root {s : Label.{0}} (hs : s ≠ ⊥) :
    rootRows.IsGate 4 1 rootPrivate rootDonor (rootLabel s ⊤) where
  cap_mem := by simp [rootPrivate]
  scope_cap_subset := by simp [rootScheme]
  grade_cap := rfl
  cap_ne_bot := hs
  le_gate e he := by rcases he with rfl | rfl | rfl <;> simp [rootScheme, gradedIndex]
  reads e he heP := by
    rcases he with rfl | rfl | rfl
    · exact absurd (by simp [rootPrivate]) heP
    · exact .ref ⟨0, by simp [rootScheme, gradedIndex]⟩ (by simp [rootPrivate]) 2
        (by simp [rootScheme]) (by simp [rootLabel, rootScheme]) (by simp [rootRows, rootScheme])
    · exact .top ⟨1, by simp [rootScheme, gradedIndex]⟩ (by simp [rootPrivate]) le_rfl le_top
        le_rfl

/-- The display of the root example is lawful, for every private cap label self-visible at `3`. -/
theorem isLawful_rootDisplay {s : Label.{0}} (hs : IsSelfVisible 3 s) :
    rootRows.IsLawful (rootLabel s ⊤) :=
  isLawful_rootLabel hs (isSelfVisible_top 1) le_top le_top

/-- The root example has no twins. -/
private theorem root_noTwin (q : Fin 5 → Label.{0}) :
    ∀ t, rootScheme.gradedIndex t = rootScheme.gradedIndex 4 → t ≠ 4 → q t = ⊥ :=
  fun t ht htG ↦ absurd (root_unique t ht) htG

variable {q : Fin 5 → Label.{0}}

/-- **P3, the root cell as anchor**, with the private cap labelled `⊤`: every lawful labelling
with the literal private face has the donor labels, `ω + 2` and `⊤`. -/
theorem root_eq (hq : rootRows.IsLawful q) (hlit : ∀ x ∈ rootPrivate, q x = rootLabel ⊤ ⊤ x) :
    q 2 = om 2 ∧ q 3 = ⊤ :=
  ⟨(isGate_root top_ne_bot).eq_of_lt_cap hq hlit (root_noTwin q) (by simp [rootDonor])
      (om_lt_top 2),
    (isGate_root top_ne_bot).eq_of_cap_eq_top hq hlit (root_noTwin q) rfl
      (by simp [rootDonor])⟩

/-- **P5, the cut above the cutoff.**  With the private cap labelled `ω + 3` (the actual cut of the
anchor block `ω` at threshold `3`), agreement below `ω + 3` gives agreement below the cutoff
`ω + 1`. -/
theorem root_cutoff (hq : rootRows.IsLawful q)
    (hlit : ∀ x ∈ rootPrivate, q x = rootLabel (om 3) ⊤ x) :
    ∀ e ∈ rootDonor, min (q e) (om 1) = min (rootLabel (om 3) ⊤ e) (om 1) := by
  intro e he
  have h : min (q e) (om 3) = min (rootLabel (om 3) ⊤ e) (om 3) :=
    ((isGate_root (om_ne_bot 3)).recover_of_unique hq hlit root_unique).2 e he
  have h13 : om 1 ≤ om 3 := om_le_om.mpr (by omega)
  calc min (q e) (om 1) = min (min (q e) (om 3)) (om 1) := by rw [min_assoc, min_eq_right h13]
    _ = min (rootLabel (om 3) ⊤ e) (om 1) := by rw [h, min_assoc, min_eq_right h13]

/-- **P7, no bottom gate without twins**: with the private cap not bottom, every lawful labelling
with the literal private face has a gate that is not bottom. -/
theorem root_gate_ne_bot {s : Label.{0}} (hs : s ≠ ⊥) (hq : rootRows.IsLawful q)
    (hlit : ∀ x ∈ rootPrivate, q x = rootLabel s ⊤ x) : q 4 ≠ ⊥ :=
  (isGate_root hs).gate_ne_bot hq hlit (root_noTwin q)

/-- **An anchor above the private cap.**  With the private cap labelled `3`, the anchor `ρ`,
labelled `ω + 1`, lies above it; the donor label `ω + 2` still comes back as a value at least `3`.
-/
theorem root_anchor_above_cap (hq : rootRows.IsLawful q)
    (hlit : ∀ x ∈ rootPrivate, q x = rootLabel 3 ⊤ x) : 3 ≤ q 2 :=
  (isGate_root (by simp)).cap_le_of_cap_le hq hlit (root_noTwin q) (by simp [rootDonor])
    (ofNat_le_om 3 2)

/-- **NC3, tops stop at the private cap.**  With the private cap labelled `ω + 3`, the labelling
that realizes the donor top `f'` as `ω + 3` is lawful and has the literal private face, so the
donor top is not recovered: there is no agreement above `ω + 3`. -/
theorem root_top_at_cap :
    rootRows.IsLawful (rootLabel (om 3) (om 3)) ∧
      (∀ x ∈ rootPrivate, rootLabel (om 3) (om 3) x = rootLabel (om 3) ⊤ x) ∧
      rootLabel (om 3) (om 3) 3 ≠ rootLabel (om 3) ⊤ 3 :=
  ⟨isLawful_rootLabel (by simp) (by simp) (by simp) le_rfl,
    fun x hx ↦ by rcases hx with rfl | rfl <;> rfl, by simp [rootLabel]⟩

/-! ### One private point (P1)

Points `a, y` (`0, 1`); the root is empty.  Cells: the private cap `C = ({a}, 1)`, a private cell
`z₀ = ({a}, 1)` labelled `⊥`, three donor cells `({y}, 1)` labelled `⊥`, `⊥`, `⊤`, and the gate
`G = (univ, 1)`.  The gate's row reads the first donor cell as `⊥` (`bot`), the second at most as
`z₀` (`botAnchor`), and the third at least as the cap (`top`).  This exercises the lemma alone:
the ordinary construction has a private context of arity at least two more than the root. -/

/-- The scheme with one private point. -/
def oneScheme : CellScheme (Fin 6) (Fin 2) :=
  ⟨univ, {{0}, {1}, univ}, ![{0}, {0}, {1}, {1}, {1}, univ], ![1, 1, 1, 1, 1, 1]⟩

/-- The rows: `(⊤, 0, ⊥, 0, ⊤, ⊤)` at every cell. -/
noncomputable def oneRows : oneScheme.Rows.{0} := ⟨fun _ t ↦ ![⊤, 0, ⊥, 0, ⊤, ⊤] t.1⟩

/-- The display with private cap labelled `s`: `(s, ⊥, ⊥, ⊥, ⊤, s)`. -/
noncomputable def oneLabel (s : Label.{0}) : Fin 6 → Label.{0} := ![s, ⊥, ⊥, ⊥, ⊤, s]

/-- Gate data with one private point, for every private cap label `s ≠ ⊥`. -/
theorem isGate_one {s : Label.{0}} (hs : s ≠ ⊥) :
    oneRows.IsGate 5 0 {0, 1} {2, 3, 4} (oneLabel s) where
  cap_mem := by simp
  scope_cap_subset := by simp [oneScheme]
  grade_cap := rfl
  cap_ne_bot := hs
  le_gate e he := by rcases he with rfl | rfl | rfl <;> simp [oneScheme, gradedIndex]
  reads e he _ := by
    rcases he with rfl | rfl | rfl
    · exact .bot rfl rfl
    · exact .botAnchor ⟨1, by simp [oneScheme, gradedIndex]⟩ (by simp) rfl rfl le_rfl
    · exact .top ⟨0, by simp [oneScheme, gradedIndex]⟩ (by simp) le_rfl le_top le_rfl

/-- **P1**: every lawful labelling with the literal private face has the bottom donor labels, and a
value at least the private cap at the donor top; the formal top itself when the cap is `⊤`. -/
theorem one_recover {s : Label.{0}} (hs : s ≠ ⊥) {q : Fin 6 → Label.{0}}
    (hq : oneRows.IsLawful q) (hlit : ∀ x ∈ ({0, 1} : Set (Fin 6)), q x = oneLabel s x) :
    q 2 = ⊥ ∧ q 3 = ⊥ ∧ s ≤ q 4 ∧ (s = ⊤ → q 4 = ⊤) := by
  have huniq (t : Fin 6) (ht : oneScheme.gradedIndex t = oneScheme.gradedIndex 5) : t = 5 := by
    revert t ht
    decide
  have htwin (t) (ht : oneScheme.gradedIndex t = oneScheme.gradedIndex 5) (htG : t ≠ 5) :
      q t = ⊥ := absurd (huniq t ht) htG
  have hb : oneLabel s 2 < s := bot_lt_iff_ne_bot.mpr hs
  refine ⟨(isGate_one hs).eq_of_lt_cap hq hlit htwin (by simp) hb,
    (isGate_one hs).eq_of_lt_cap hq hlit htwin (by simp) hb,
    (isGate_one hs).cap_le_of_cap_le hq hlit htwin (by simp) le_top, fun hs' ↦ ?_⟩
  subst hs'
  exact (isGate_one hs).eq_of_cap_eq_top hq hlit htwin rfl (by simp)

/-! ### Two anchor blocks, an empty root, and a top (P2, P4, P6)

Points `a, b, c, y` (`0, 1, 2, 3`); the root is empty, so every donor cell is new.  Cells:
anchors `z₁ = ({a}, 1)` labelled `1` and `z₂ = ({b}, 1)` labelled `ω + 1`, the private cap
`C = ({a, b, c}, 3)` labelled `⊤`, donor cells `({y}, 1)` labelled `2`, `ω + 2`, and `⊤`, and the
gate `G = (univ, 3)`.  Every row is the display itself. -/

/-- The scheme with two anchor blocks. -/
def blockScheme : CellScheme (Fin 7) (Fin 4) :=
  ⟨univ, {{0}, {1}, {0, 1, 2}, {3}, univ}, ![{0}, {1}, {0, 1, 2}, {3}, {3}, {3}, univ],
    ![1, 1, 3, 1, 1, 1, 3]⟩

/-- The display `(1, ω + 1, ⊤, 2, ω + 2, ⊤, ⊤)`. -/
noncomputable def blockLabel : Fin 7 → Label.{0} := ![1, om 1, ⊤, 2, om 2, ⊤, ⊤]

/-- The rows: the display, at every cell. -/
noncomputable def blockRows : blockScheme.Rows.{0} := ⟨fun _ t ↦ blockLabel t.1⟩

/-- The display of the example with two anchor blocks is lawful. -/
theorem isLawful_blockLabel : blockRows.IsLawful blockLabel where
  orderly d := by fin_cases d <;> simp [blockLabel, blockScheme]
  locality c := locality_capped (c := blockLabel c) (by fin_cases c <;>
    simp [blockLabel, blockScheme]) fun _ _ ↦ rfl
  availability a b hab hg := by
    have key : ∀ a b : Fin 7, blockScheme.scope a ⊆ blockScheme.scope b →
        blockScheme.grade a = blockScheme.grade b →
        blockScheme.gradedIndex a = blockScheme.gradedIndex b ∨ a = 2 ∧ b = 6 := by decide
    rcases key a b hab hg with h | ⟨rfl, rfl⟩
    · exact ⟨a, h, le_rfl⟩
    · exact ⟨6, rfl, le_rfl⟩

/-- Gate data with two anchor blocks: `2 = vr_3(1, 2)`, `ω + 2 = vr_3(ω + 1, 2)`, and the top is
read at the cap. -/
theorem isGate_block : blockRows.IsGate 6 2 {0, 1, 2} {3, 4, 5} blockLabel where
  cap_mem := by simp
  scope_cap_subset := by simp [blockScheme]
  grade_cap := rfl
  cap_ne_bot := by simp [blockLabel]
  le_gate e he := by rcases he with rfl | rfl | rfl <;> simp [blockScheme, gradedIndex]
  reads e he _ := by
    rcases he with rfl | rfl | rfl
    · exact .ref ⟨0, by simp [blockScheme, gradedIndex]⟩ (by simp) 2 (by simp [blockScheme])
        (by simp [blockLabel, blockScheme]) (by simp [blockRows, blockLabel, blockScheme])
    · exact .ref ⟨1, by simp [blockScheme, gradedIndex]⟩ (by simp) 2 (by simp [blockScheme])
        (by simp [blockLabel, blockScheme]) (by simp [blockRows, blockLabel, blockScheme])
    · exact .top ⟨2, by simp [blockScheme, gradedIndex]⟩ (by simp) le_rfl le_rfl le_rfl

/-- **P2, P4, P6**: with an empty root and the private cap labelled `⊤`, every lawful labelling
with the literal private face has every donor label: `2` and `ω + 2` from their anchor blocks, and
the formal top. -/
theorem block_recover {q : Fin 7 → Label.{0}} (hq : blockRows.IsLawful q)
    (hlit : ∀ x ∈ ({0, 1, 2} : Set (Fin 7)), q x = blockLabel x) :
    q 3 = 2 ∧ q 4 = om 2 ∧ q 5 = ⊤ := by
  have huniq (t : Fin 7) (ht : blockScheme.gradedIndex t = blockScheme.gradedIndex 6) :
      t = 6 := by
    revert t ht
    decide
  have htwin (t) (ht : blockScheme.gradedIndex t = blockScheme.gradedIndex 6) (htG : t ≠ 6) :
      q t = ⊥ := absurd (huniq t ht) htG
  exact ⟨isGate_block.eq_of_cap_eq_top hq hlit htwin rfl (by simp),
    isGate_block.eq_of_cap_eq_top hq hlit htwin rfl (by simp),
    isGate_block.eq_of_cap_eq_top hq hlit htwin rfl (by simp)⟩

/-! ### A gate with a twin (NC1, NC2)

The root example with a twin: points `a, b, c, y`; cells `ρ = ({a}, 1)`, `C = ({a, b, c}, 3)`,
`f = ({y}, 1)`, the gate `G` and its twin `G'`, both `(univ, 3)`.  The gate's row is
`(ω + 1, ⊤, ω + 2, ⊤, 3)` and the twin's `(ω + 1, ⊤, ⊤, 3, ⊤)`; the display labels `ρ, C, f` by
`ω + 1, ⊤, ω + 2`, the gate `⊤`, and the twin `⊥`.  The gate data hold, but a lawful labelling
with the literal private face may label the twin `⊤` and the gate `⊥` (NC1) or `3` (NC2): the twin
then serves availability against the cap, and the donor label `ω + 2` is lost, even below the
actual cut `ω + 3`. -/

/-- The scheme with a twin of the gate. -/
def twinScheme : CellScheme (Fin 5) (Fin 4) :=
  ⟨univ, {{0}, {0, 1, 2}, {3}, univ}, ![{0}, {0, 1, 2}, {3}, univ, univ], ![1, 3, 1, 3, 3]⟩

/-- The rows: `(ω + 1, ⊤, ⊤, ⊤, ⊤)` at `ρ, C, f`, the gate's row at `G`, the twin's at `G'`. -/
noncomputable def twinRows : twinScheme.Rows.{0} :=
  ⟨fun c t ↦ ![![om 1, ⊤, ⊤, ⊤, ⊤], ![om 1, ⊤, ⊤, ⊤, ⊤], ![om 1, ⊤, ⊤, ⊤, ⊤],
    ![om 1, ⊤, om 2, ⊤, 3], ![om 1, ⊤, ⊤, 3, ⊤]] c t.1⟩

/-- The labelling `(ω + 1, ⊤, v, x, y)` of `ρ, C, f, G, G'`. -/
noncomputable def twinLabel (v x y : Label.{0}) : Fin 5 → Label.{0} := ![om 1, ⊤, v, x, y]

/-- The private cells `ρ, C`. -/
def twinPrivate : Set (Fin 5) := {0, 1}

/-- The donor cells `ρ, f`. -/
def twinDonor : Set (Fin 5) := {0, 2}

/-- The pairs of cells to which availability applies with distinct graded indices: the cap
below the gate and below the twin. -/
private theorem twin_availability : ∀ a b : Fin 5, twinScheme.scope a ⊆ twinScheme.scope b →
    twinScheme.grade a = twinScheme.grade b →
    twinScheme.gradedIndex a = twinScheme.gradedIndex b ∨ a = 1 ∧ (b = 3 ∨ b = 4) := by
  decide

/-- The display of the example with a twin is lawful. -/
theorem isLawful_twinDisplay : twinRows.IsLawful (twinLabel (om 2) ⊤ ⊥) where
  orderly d := by fin_cases d <;> simp [twinLabel, twinScheme]
  locality c := by
    fin_cases c
    · exact locality_capped (c := om 1) (by simp [twinScheme]) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := om 2) (by simp [twinScheme]) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_of isWitness_killFinite fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, killFinite_om, killFinite_top,
          killFinite_ofNat] at hd ⊢
    · exact locality_of IsWitness.bot_top fun d _ ↦ by simp [twinLabel]
  availability a b hab hg := by
    rcases twin_availability a b hab hg with h | ⟨rfl, rfl | rfl⟩
    · exact ⟨a, h, le_rfl⟩
    · exact ⟨3, rfl, le_rfl⟩
    · exact ⟨3, rfl, le_rfl⟩

/-- Gate data with a twin: the root cell anchors `f`, as without the twin. -/
theorem isGate_twin : twinRows.IsGate 3 1 twinPrivate twinDonor (twinLabel (om 2) ⊤ ⊥) where
  cap_mem := by simp [twinPrivate]
  scope_cap_subset := by simp [twinScheme]
  grade_cap := rfl
  cap_ne_bot := by simp [twinLabel]
  le_gate e he := by rcases he with rfl | rfl <;> simp [twinScheme, gradedIndex]
  reads e he heP := by
    rcases he with rfl | rfl
    · exact absurd (by simp [twinPrivate]) heP
    · exact .ref ⟨0, by simp [twinScheme, gradedIndex]⟩ (by simp [twinPrivate]) 2
        (by simp [twinScheme]) (by simp [twinLabel, twinScheme]) (by simp [twinRows, twinScheme])

/-- The labelling of NC1 is lawful: the gate `⊥`, the twin `⊤`, and `f` labelled `⊤`. -/
theorem isLawful_twinBottom : twinRows.IsLawful (twinLabel ⊤ ⊥ ⊤) where
  orderly d := by fin_cases d <;> simp [twinLabel, twinScheme]
  locality c := by
    fin_cases c
    · exact locality_capped (c := om 1) (by simp [twinScheme]) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_of IsWitness.bot_top fun d _ ↦ by simp [twinLabel]
    · exact locality_of isWitness_killFinite fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, killFinite_om, killFinite_top,
          killFinite_ofNat] at hd ⊢
  availability a b hab hg := by
    rcases twin_availability a b hab hg with h | ⟨rfl, rfl | rfl⟩
    · exact ⟨a, h, le_rfl⟩
    · exact ⟨4, rfl, le_rfl⟩
    · exact ⟨4, rfl, le_rfl⟩

/-- The labelling of NC2 is lawful: the gate `3`, the twin `⊤`, and `f` labelled `⊤`. -/
theorem isLawful_twinSmall : twinRows.IsLawful (twinLabel ⊤ 3 ⊤) where
  orderly d := by fin_cases d <;> simp [twinLabel, twinScheme]
  locality c := by
    fin_cases c
    · exact locality_capped (c := om 1) (by simp [twinScheme]) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := 3) (by simp [twinScheme]) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [twinScheme, twinRows, twinLabel, gradedIndex] at hd ⊢
  availability a b hab hg := by
    rcases twin_availability a b hab hg with h | ⟨rfl, rfl | rfl⟩
    · exact ⟨a, h, le_rfl⟩
    · exact ⟨4, rfl, le_rfl⟩
    · exact ⟨4, rfl, le_rfl⟩

/-- **NC1, a bottom gate.**  The gate data hold for the lawful display, and the lawful labelling
with the literal private face, the gate `⊥`, and the twin `⊤` disagrees with the display at the
donor cell `f`, below the actual cut `ω + 3`. -/
theorem twin_bottom_gate :
    twinRows.IsGate 3 1 twinPrivate twinDonor (twinLabel (om 2) ⊤ ⊥) ∧
      twinRows.IsLawful (twinLabel (om 2) ⊤ ⊥) ∧ twinRows.IsLawful (twinLabel ⊤ ⊥ ⊤) ∧
      (∀ x ∈ twinPrivate, twinLabel ⊤ ⊥ ⊤ x = twinLabel (om 2) ⊤ ⊥ x) ∧ twinLabel ⊤ ⊥ ⊤ 3 = ⊥ ∧
      min (twinLabel ⊤ ⊥ ⊤ 2) (om 3) ≠ min (twinLabel (om 2) ⊤ ⊥ 2) (om 3) :=
  ⟨isGate_twin, isLawful_twinDisplay, isLawful_twinBottom,
    fun x hx ↦ by rcases hx with rfl | rfl <;> rfl, rfl, by simp [twinLabel]⟩

/-- **NC2, a gate that is not bottom.**  The gate data hold for the lawful display, and the lawful
labelling with the literal private face, the gate labelled `3`, not bottom, and the twin `⊤`
disagrees with the display at the donor cell `f`, below the actual
cut `ω + 3`: the literal private face and a non-bottom gate do not give recovery when the gate has
a twin. -/
theorem twin_small_gate :
    twinRows.IsGate 3 1 twinPrivate twinDonor (twinLabel (om 2) ⊤ ⊥) ∧
      twinRows.IsLawful (twinLabel (om 2) ⊤ ⊥) ∧ twinRows.IsLawful (twinLabel ⊤ 3 ⊤) ∧
      (∀ x ∈ twinPrivate, twinLabel ⊤ 3 ⊤ x = twinLabel (om 2) ⊤ ⊥ x) ∧ twinLabel ⊤ 3 ⊤ 3 ≠ ⊥ ∧
      min (twinLabel ⊤ 3 ⊤ 2) (om 3) ≠ min (twinLabel (om 2) ⊤ ⊥ 2) (om 3) :=
  ⟨isGate_twin, isLawful_twinDisplay, isLawful_twinSmall,
    fun x hx ↦ by rcases hx with rfl | rfl <;> rfl, by simp [twinLabel], by simp [twinLabel]⟩

/-! ### A donor label above the threshold (NC4)

Points `a, b, c, y`; cells `ρ = ({a}, 1)` labelled `ω + 1`, `C = ({a, b, c}, 3)` labelled `⊤`,
`f = ({y}, 1)` labelled `ω + 4`, and the gate `G = (univ, 3)`, whose row is `(ω + 1, ⊤, ω + 4, ⊤)`.
The finite part `4` of the donor label is at least the threshold `3`, so no private cell anchors
it, and no gate data exist; and indeed the lawful labelling that flattens finite parts at `3`
realizes `f` as `ω + 3`. -/

/-- The scheme with a donor label above the threshold. -/
def highScheme : CellScheme (Fin 4) (Fin 4) :=
  ⟨univ, {{0}, {0, 1, 2}, {3}, univ}, ![{0}, {0, 1, 2}, {3}, univ], ![1, 3, 1, 3]⟩

/-- The rows: `(ω + 1, ⊤, ⊤, ⊤)` at `ρ, C, f`, and `(ω + 1, ⊤, ω + 4, ⊤)` at the gate. -/
noncomputable def highRows : highScheme.Rows.{0} :=
  ⟨fun c t ↦ if c = 3 then ![om 1, ⊤, om 4, ⊤] t.1 else ![om 1, ⊤, ⊤, ⊤] t.1⟩

/-- The labelling `(ω + 1, ⊤, v, ⊤)`; with `v = ω + 4` it is the display. -/
noncomputable def highLabel (v : Label.{0}) : Fin 4 → Label.{0} := ![om 1, ⊤, v, ⊤]

/-- Flattening of finite parts at `3` fixes `ω + 1`. -/
private theorem flatten_om_one : flatten 3 (om 1) = om 1 := by
  unfold om
  rw [flatten_coe, flattenOrd, om_div, om_mod, mul_one, min_eq_left (Nat.cast_le.mpr
    (by omega))]

/-- Flattening of finite parts at `3` sends `ω + 4` to `ω + 3`. -/
private theorem flatten_om_four : flatten 3 (om 4) = om 3 := by
  unfold om
  rw [flatten_coe, flattenOrd, om_div, om_mod, mul_one, min_eq_right (Nat.cast_le.mpr
    (by omega))]

/-- The pairs of cells to which availability applies with distinct graded indices. -/
private theorem high_availability : ∀ a b : Fin 4, highScheme.scope a ⊆ highScheme.scope b →
    highScheme.grade a = highScheme.grade b →
    highScheme.gradedIndex a = highScheme.gradedIndex b ∨ a = 1 ∧ b = 3 := by
  decide

/-- The labelling `(ω + 1, ⊤, v, ⊤)` is lawful for `v = ω + 4` (the display) and `v = ω + 3`. -/
theorem isLawful_highLabel {v : Label.{0}} (hv : v = om 4 ∨ v = om 3) :
    highRows.IsLawful (highLabel v) where
  orderly d := by rcases hv with rfl | rfl <;> fin_cases d <;> simp [highLabel, highScheme]
  locality c := by
    have hv1 : IsSelfVisible 1 v := by rcases hv with rfl | rfl <;> simp
    fin_cases c
    · exact locality_capped (c := om 1) (by simp [highScheme]) fun d hd ↦ by
        fin_cases d <;> simp [highScheme, highRows, highLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [highScheme, highRows, highLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := v) hv1 fun d hd ↦ by
        fin_cases d <;> simp [highScheme, highRows, highLabel, gradedIndex] at hd ⊢
    · rcases hv with rfl | rfl
      · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
          fin_cases d <;> simp [highScheme, highRows, highLabel] at hd ⊢
      · refine locality_of (isWitness_comp_flatten (f := id) (m := 3) rfl monotone_id
          fun _ _ _ _ _ ↦ rfl) fun d hd ↦ ?_
        fin_cases d <;>
          simp [highScheme, highRows, highLabel, flatten_om_one, flatten_om_four] at hd ⊢
  availability a b hab hg := by
    rcases high_availability a b hab hg with h | ⟨rfl, rfl⟩
    · exact ⟨a, h, le_rfl⟩
    · exact ⟨3, rfl, le_rfl⟩

/-- **NC4, a donor label above the threshold.**  The display is lawful but has no gate data, the
gate has no twin, and the lawful labelling with the literal private face that flattens finite parts
at `3` realizes the donor label `ω + 4`, which lies below the private cap, as `ω + 3`. -/
theorem high_not_recovered :
    ¬ highRows.IsGate 3 1 {0, 1} {2} (highLabel (om 4)) ∧ highRows.IsLawful (highLabel (om 4)) ∧
      (∀ t, highScheme.gradedIndex t = highScheme.gradedIndex 3 → t = 3) ∧
      highRows.IsLawful (highLabel (om 3)) ∧
      (∀ x ∈ ({0, 1} : Set (Fin 4)), highLabel (om 3) x = highLabel (om 4) x) ∧
      highLabel (om 3) 2 ≠ highLabel (om 4) 2 ∧ highLabel (om 4) 2 < highLabel (om 4) 1 := by
  refine ⟨fun h ↦ ?_, isLawful_highLabel (.inl rfl), by decide, isLawful_highLabel (.inr rfl),
    fun x hx ↦ by rcases hx with rfl | rfl <;> rfl, by simp [highLabel], by simp [highLabel]⟩
  cases h.reads 2 rfl (by simp) with
  | bot hwe _ => exact om_ne_bot 4 hwe
  | botAnchor _ _ _ hwe _ => exact om_ne_bot 4 hwe
  | ref z hz i hi hwe _ =>
    obtain ⟨z, _⟩ := z
    have hi : i ≤ 3 := hi
    rcases hz with rfl | rfl
    · change om 4 = visibilityReplace 3 i (om 1) at hwe
      have h13 : 1 < 3 := by omega
      rw [visibilityReplace_om, ite_eq_left h13, om_inj] at hwe
      omega
    · change om 4 = visibilityReplace 3 i ⊤ at hwe
      exact om_ne_top 4 (hwe.trans (visibilityReplace_top 3 i))
  | top _ _ _ heC _ => exact (om_lt_top 4).not_ge heC

/-! ### A private cap below the gate's grade (NC5)

Points `a, b, c, y`; cells `ρ = ({a}, 1)` labelled `ω + 1`, `C = ({a, b, c}, 2)` labelled `⊤`,
`f = ({y}, 1)` labelled `ω + 2`, and the gate `G = (univ, 3)` with row `(ω + 1, ⊤, ω + 2, ⊤)`.
The gate's row reads `f` from the anchor `ρ`, and the gate has no twin, but the cap has grade `2`,
not that of the gate: availability against it does not reach the gate, and the lawful labelling
with a bottom gate and `f` labelled `⊤` has the literal private face. -/

/-- The scheme with a private cap of grade `2`. -/
def lowCapScheme : CellScheme (Fin 4) (Fin 4) :=
  ⟨univ, {{0}, {0, 1, 2}, {3}, univ}, ![{0}, {0, 1, 2}, {3}, univ], ![1, 2, 1, 3]⟩

/-- The rows: `(ω + 1, ⊤, ⊤, ⊤)` at `ρ, C, f`, and `(ω + 1, ⊤, ω + 2, ⊤)` at the gate. -/
noncomputable def lowCapRows : lowCapScheme.Rows.{0} :=
  ⟨fun c t ↦ if c = 3 then ![om 1, ⊤, om 2, ⊤] t.1 else ![om 1, ⊤, ⊤, ⊤] t.1⟩

/-- The labelling `(ω + 1, ⊤, v, x)`; with `v = ω + 2` and `x = ⊤` it is the display. -/
noncomputable def lowCapLabel (v x : Label.{0}) : Fin 4 → Label.{0} := ![om 1, ⊤, v, x]

/-- The only pairs of cells to which availability applies have equal graded indices. -/
private theorem lowCap_availability :
    ∀ a b : Fin 4, lowCapScheme.scope a ⊆ lowCapScheme.scope b →
    lowCapScheme.grade a = lowCapScheme.grade b →
    lowCapScheme.gradedIndex a = lowCapScheme.gradedIndex b := by
  decide

/-- The display `(ω + 1, ⊤, ω + 2, ⊤)` and the labelling `(ω + 1, ⊤, ⊤, ⊥)` are lawful. -/
theorem isLawful_lowCapLabel {v x : Label.{0}} (h : v = om 2 ∧ x = ⊤ ∨ v = ⊤ ∧ x = ⊥) :
    lowCapRows.IsLawful (lowCapLabel v x) where
  orderly d := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases d <;> simp [lowCapLabel, lowCapScheme]
  locality c := by
    have hv1 : IsSelfVisible 1 v := by rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    fin_cases c
    · exact locality_capped (c := om 1) (by simp [lowCapScheme]) fun d hd ↦ by
        fin_cases d <;> simp [lowCapScheme, lowCapRows, lowCapLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
        fin_cases d <;> simp [lowCapScheme, lowCapRows, lowCapLabel, gradedIndex] at hd ⊢
    · exact locality_capped (c := v) hv1 fun d hd ↦ by
        fin_cases d <;> simp [lowCapScheme, lowCapRows, lowCapLabel, gradedIndex] at hd ⊢
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact locality_capped (c := ⊤) (isSelfVisible_top _) fun d hd ↦ by
          fin_cases d <;> simp [lowCapScheme, lowCapRows, lowCapLabel] at hd ⊢
      · exact locality_of IsWitness.bot_top fun d _ ↦ by simp [lowCapLabel]
  availability a b hab hg := ⟨a, lowCap_availability a b hab hg, le_rfl⟩

/-- **NC5, a private cap below the gate's grade.**  The gate's row reads the donor cell `f` from the
anchor `ρ`, and the gate has no twin, but the cap's grade is not the gate's; the lawful labelling
with a bottom gate, `f` labelled `⊤`, and the literal private face disagrees with the display at
`f` below the actual cut `ω + 3`. -/
theorem lowCap_not_recovered :
    GateReads lowCapRows 3 1 {0, 1} (lowCapLabel (om 2) ⊤)
        ⟨2, by simp [lowCapScheme, gradedIndex]⟩ ∧
      lowCapScheme.grade 1 ≠ lowCapScheme.grade 3 ∧ lowCapRows.IsLawful (lowCapLabel (om 2) ⊤) ∧
      (∀ t, lowCapScheme.gradedIndex t = lowCapScheme.gradedIndex 3 → t = 3) ∧
      lowCapRows.IsLawful (lowCapLabel ⊤ ⊥) ∧
      (∀ x ∈ ({0, 1} : Set (Fin 4)), lowCapLabel ⊤ ⊥ x = lowCapLabel (om 2) ⊤ x) ∧
      lowCapLabel ⊤ ⊥ 3 = ⊥ ∧
      min (lowCapLabel ⊤ ⊥ 2) (om 3) ≠ min (lowCapLabel (om 2) ⊤ 2) (om 3) :=
  ⟨.ref ⟨0, by simp [lowCapScheme, gradedIndex]⟩ (by simp) 2 (by simp [lowCapScheme])
      (by simp [lowCapLabel, lowCapScheme]) (by simp [lowCapRows, lowCapScheme]), by decide,
    isLawful_lowCapLabel (.inl ⟨rfl, rfl⟩), by decide, isLawful_lowCapLabel (.inr ⟨rfl, rfl⟩),
    fun x hx ↦ by rcases hx with rfl | rfl <;> rfl, rfl, by simp [lowCapLabel]⟩

end VaughtConjecture.GateExamples

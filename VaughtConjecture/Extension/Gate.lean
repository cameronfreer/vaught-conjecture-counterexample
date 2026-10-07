/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Scheme.Row

/-!
# Gate recovery

Roadmap, Layer 3, 3.3 (the recovery statements, item 1: agreement below a cutoff in the ordinary
construction (R1)); the vocabulary of Layer 3 (private context, private cap, display, gate,
reference cells).

**Setting.**  Fix a cell scheme `D` with semantic rows `R`, and in it:

* a set `P` of **private cells** (in (R1), the cells visible through the embedding of the private
  context) and a set `Q` of **donor cells** (the cells visible through the embedding of the donor,
  the root followed by the new point); the cells in both are the cells of the root;
* a labelling `w`, the **display**: in (R1) a lawful labelling that is literally the private labels
  on `P` and the donor labels on `Q`; here only its values on `P` and `Q` are read, not its
  lawfulness and not its value at the gate;
* the **private cap** `C ∈ P`, a cell with `w C ≠ ⊥`;
* the **gate** `G`, a cell of the grade `N` of `C` whose scope contains that of `C`, above every
  donor cell.  The cells other than `G` with the graded index of `G` are its **twins**.

The row of the gate **reads** a donor cell `e` outside `P` in one of four ways (`GateReads`):

* `bot`: `w e = ⊥`, and the row of `G` is bottom at `e`;
* `botAnchor`: `w e = ⊥`, and the row of `G` at `e` is at most its value at a private cell
  labelled `⊥`;
* `ref`: `w e = vr_N(w z, i)` for a private cell `z`, the **anchor** of `e`, and some `i ≤ N`, and
  the row of `G` at `e` is `vr_N` of its value at `z`, with the same `i`; the reference cells of the
  roadmap are the anchors;
* `top`: `w C ≤ w e`, and the row of `G` at `e` is at least its value at a private cell labelled
  at least `w C`.

`IsGate` collects these data.  It says nothing about the twins.

**Gate recovery** (`IsGate.recover`).  Let `q` be a lawful labelling that is literally `w` on the
private cells and is bottom at every twin of the gate.  Then `w C ≤ q G`, and `q` agrees with the
display on every donor cell below the label `w C` of the private cap:
`min (q e) (w C) = min (w e) (w C)`.  Exactly, a donor label below `w C` is recovered
(`IsGate.eq_of_lt_cap`), and a donor label at least `w C`, the formal top in particular, comes back
only as a value at least `w C` (`IsGate.cap_le_of_cap_le`); when `w C = ⊤` every donor label is
recovered (`IsGate.eq_of_cap_eq_top`).

* **The lower bound on the gate comes from availability.**  Availability
  ([Kni26, Definition 2.5.4]) for the pair `C`, `G` gives a cell `u` with the graded index
  of `G` and `q C ≤ q u`.  When every twin is bottom and `q C = w C` is not, `u` is the gate: this
  is the **gate inequality** `w C ≤ q G` (`IsLawful.cap_le_gate`), and in particular the gate is
  not bottom (`IsGate.gate_ne_bot`).  Locality at the gate gives no lower bound: lowering the
  gate's value to any `x ≤ q G` self-visible at `N` keeps the locality at the gate
  (`IsLawful.locality_lower_gate`, by the cap rule `Label.TransformsTo.min_const`).
* **One witness.**  The locality at the gate gives one witness `(g, σ)` with `q G ≤ g N`, so
  `min (q d) (q G) = min (σ (R.row G d)) (q G)` for every cell `d` below the gate
  (`IsLawful.exists_gateWitness`).  The readings are decoded with this witness alone.  At an anchor
  `z` with `w z < q G`, the equation `q z = w z` determines `σ` at the row's value, which then lies
  below `q G ≤ g N`, so the fifth law of a witness at the threshold `N` carries the replacement
  `vr_N(·, i)` from `z` to `e`; at an anchor with `w z ≥ q G`, the same law, applied to a second
  replacement that undoes the first (`Label.exists_visibilityReplace_visibilityReplace`), keeps `σ`
  at least `q G` (`Label.IsWitness.min_apply_visibilityReplace`,
  `Label.IsWitness.le_apply_visibilityReplace_of_le`).  No composition of witnesses is used: the
  transitivity of [Kni26, Lemma 2.3.14] is not correct as stated
  (`Label.TransformsTo.not_transitive`).  No threshold other than the grade `N` of the gate is
  used, so the suppressor may be bottom above `N`: every cell below the gate has grade at most `N`.
  Neither the offset bound of [Kni26, Lemma 2.5.13], which is not correct as stated, nor any
  coding, legality, or completion is used.
* **Why agreement stops at `w C`.**  An anchor labelled `μ + k` with `k < N` (`μ` zero or a limit)
  and at most `w C` gives `μ + N = vr_N(μ + k, N) ≤ w C`, since `w C` is self-visible at `N`
  (`Label.visibilityReplace_le_of_le`).  So `w C` is at least the **actual cut**, the largest
  `μ + N` over the blocks of such anchors, and agreement holds below the actual cut.  Above `w C`
  nothing bounds the gate or the donor tops: a lawful labelling may realize a donor top as `w C`
  itself (`VaughtConjecture.Extension.GateExamples`).

**Gate recovery with the twin–gate coupling** (`IsGate.recover_of_twinsReadGate`).  The twin
hypothesis of `IsGate.recover` enters only through the gate inequality `w C ≤ q G`
(`IsGate.recover_of_cap_le_gate`).  The rows **couple the twins to the gate**
(`TwinsReadGate`) when every twin `t` of `G` reads `G` at least as it reads `C`:
`R.row t C ≤ R.row t G`.  Then every lawful labelling `q` has `q C ≤ q G`
(`cap_le_gate_of_twinsReadGate`): availability gives a cell `u` with the graded index of `G` and
`q C ≤ q u`, and if `u` is a twin, locality at `u` with its witness `(g, σ)` gives, at equal
grades, `q C = min (σ (R.row u C)) (g N) ≤ min (σ (R.row u G)) (g N) = min (q G) (q u) ≤ q G`.
The coupling is a condition on rows, so it holds for every lawful labelling of the rows at once,
and nothing is assumed about the values at the twins: a twin may carry any label, `⊤` included.
It is the weakest condition on the entries `R.row t C`, `R.row t G` under which every witness reads
`C` at most as `G`, since the identity is a witness (`Label.le_iff_forall_isWitness`).  It is not
necessary for the gate inequality: a twin whose own entry is `⊥` is `⊥` in every lawful labelling
and never serves availability.

**Findings.**

* *The recovery hypothesis is the bottom pattern of the whole graded index of the gate*: the gate
  is not bottom and its twins are bottom.  A literal private face and a non-bottom gate do not
  imply agreement from lawfulness alone when the gate has a twin: a twin labelled `⊤` serves
  availability against the cap, so the cap no longer bounds the gate from below, and the bottom
  pattern of the twins cannot be dropped (the counterexamples `GateExamples.twin_bottom_gate` and
  `GateExamples.twin_small_gate`).  The twin of those counterexamples reads the cap at `⊤` and the
  gate at `3`, so its rows do not couple it to the gate
  (`CoupledGateExamples.not_twinsReadGate_twin`); a condition on the rows that replaces the bottom
  pattern of the twins is the coupling above.  When the gate has no twins, the literal private face
  alone gives recovery (`IsGate.recover_of_unique`), and the gate is not bottom by the gate
  inequality.  When the gate's row is bottom at every twin, a non-bottom gate makes the twins
  bottom (`IsLawful.eq_bot_of_row_eq_bot`, `IsGate.recover_of_row_twin`).  The bottom-pattern
  clause of a model ([Kni26, Definition 3.2.1], clause 4(a)ii) realizes exactly this pattern once
  the display has it, since the grade `N` of the gate is at most the arity of the private context.
* *An anchor may be self-visible at `N`, may lie above the private cap, and `i = N` is allowed.*
  A self-visible anchor reads its own label.  If the anchor's label is at least `q G`, so is the
  donor label, and the reading still bounds `q e` below by `q G`.
* *The legality of a scheme carrying a gate is not addressed here.*  Such a scheme lives on the
  private points and the new point, and its plan contains the root with the new point and the
  whole set; accessibility of plans and completeness then put cells on a chain of faces between
  them, and the restriction to the last coatom of that chain is an exact pinned extension of a face
  of the private context over the root.  So the construction of a legal gated scheme contains
  completion problems of the kind of (R6).  With its twins labelled `⊥`, such a scheme need not
  exist: the universal gated extension hypothesis `StageType.HasGatedPinnedExtensions` fails at
  every stage (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).  With the coupling of
  the rows in place of the labels `⊥` of the twins, a legal scheme carrying a gate exists at the
  input of that refutation (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`); the
  universal form `StageType.HasCoupledGatedPinnedExtensions` is open, and so is general (R1).

**Readers** (`ReadsOnly`, `IsLawful.recover_of_readsOnly`).  A gate may have twins that are not
`⊥`.  The row of a cell `G` **reads only** a set `S` of cells (`ReadsOnly`) when it is `⊥` at
every other cell of the graded index of `G` outside `S`; the members of `S` that are gates in the
sense of `IsGate` are its **readers**, and a member `K` that the row of `G` reads at least as `G`
itself is a **ceiling** of `G`.  In a lawful labelling not `⊥` at `G`, every cell of the graded
index of `G` outside `S`, other than `G` itself, is `⊥` (`IsLawful.eq_bot_of_row_eq_bot`),
and a ceiling is at least `G`
(`IsLawful.le_of_row_self_le`); so **availability** (the second law of a lawful section: a cell of
the grade of `G` with scope inside that of `G` lies below some cell of the graded index of `G`)
puts the private cap below a member of `S` (`IsLawful.exists_mem_le_of_readsOnly`).  If every
member of `S` is a reader, gate recovery through that member gives agreement with the display on
every donor cell below the label of the cap, for every lawful labelling literally the display on
the private cells and not `⊥` at `G` (`IsLawful.recover_of_readsOnly`).  Availability may reach a
twin of `G`; it suffices that the twins it can reach are readers.  A reading through an anchor is
transported to every lawful labelling below the value of the reading cell
(`IsLawful.min_eq_visibilityReplace_of_row_eq`).

**One dominating cell reads one order** (`row_lt_of_le_dominant`).  If, in a labelling lawful
below the graded index `Y` of a cell `K`, `K` dominates every cell of graded index `Y`, the row of
`K` orders any two cells of the grade of `Y` with scopes inside that of `Y` as the labelling does.
A row of `G` that is `⊥` at every other cell of its graded index except one ceiling makes that
ceiling dominant in every labelling lawful below that graded index and not `⊥` at `G`
(`IsLawfulBelow.le_of_readsOnly_singleton`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

Witnesses and the transformation relation are [Kni26, Definition 2.3.9], visibility replacement is
[Kni26, Definition 2.2.3], and lawful sections, with locality and availability, are
[Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture.Label

variable {N i : ℕ} {a b c v x : Label.{u}} {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

/-! ### Scalar lemmas -/

/-- A minimum that lies strictly below its second argument is its first argument. -/
theorem left_eq_of_min_eq_of_lt (h : min a b = v) (hv : v < b) : a = v :=
  ((min_eq_iff.mp h).resolve_right fun h' ↦ hv.ne' h'.1).1

/-- A label that is not self-visible at `N` lies strictly below every label self-visible at `N`
above it. -/
theorem lt_of_not_isSelfVisible_of_le (hx : ¬ IsSelfVisible N x) (hc : IsSelfVisible N c)
    (h : x ≤ c) : x < c :=
  h.lt_of_ne fun hxc ↦ hx (hxc ▸ hc)

/-- Visibility replacement with a value `i < N` of a label that is not self-visible at `N` is not
self-visible at `N`. -/
theorem not_isSelfVisible_visibilityReplace (hx : ¬ IsSelfVisible N x) (hi : i < N) :
    ¬ IsSelfVisible N (visibilityReplace N i x) := by
  induction x using recBotCoeTop with
  | bot => exact absurd (isSelfVisible_bot N) hx
  | coe o =>
    rw [isSelfVisible_coe, not_le] at hx
    rw [visibilityReplace_coe, isSelfVisible_coe, Ordinal.visibilityReplace_mod, ite_eq_left hx,
      Nat.cast_le, not_le]
    exact hi
  | top => exact absurd (isSelfVisible_top N) hx

/-- Visibility replacement with a value `i < N` keeps a label that is not self-visible at `N`
strictly below every label self-visible at `N` above it. -/
theorem visibilityReplace_lt_of_not_isSelfVisible (hx : ¬ IsSelfVisible N x)
    (hc : IsSelfVisible N c) (h : x ≤ c) (hi : i < N) : visibilityReplace N i x < c :=
  lt_of_not_isSelfVisible_of_le (not_isSelfVisible_visibilityReplace hx hi) hc
    (visibilityReplace_le_of_le hi.le hc h)

/-- Visibility replacement with a value `i < N` keeps a label strictly below a label self-visible
at `N` strictly below it. -/
theorem visibilityReplace_lt_of_lt (hc : IsSelfVisible N c) (h : x < c) (hi : i < N) :
    visibilityReplace N i x < c := by
  by_cases hx : IsSelfVisible N x
  · rwa [hx.visibilityReplace_eq]
  · exact visibilityReplace_lt_of_not_isSelfVisible hx hc h.le hi

/-- Visibility replacement with a value `i ≤ N` keeps a label at least a label self-visible at
`N` below it. -/
theorem le_visibilityReplace_of_le (hc : IsSelfVisible N c) (h : c ≤ x) (hi : i ≤ N) :
    c ≤ visibilityReplace N i x := by
  by_contra hlt
  rw [not_le] at hlt
  rcases hi.lt_or_eq with hi | rfl
  · obtain ⟨j, hj, hx⟩ := exists_visibilityReplace_visibilityReplace hi x
    exact (visibilityReplace_lt_of_lt hc hlt hj).not_ge (hx.symm ▸ h)
  · exact (h.trans (le_visibilityReplace (by omega) x)).not_gt hlt

/-! ### One witness below a self-visible cap -/

/-- Past a cap `c` self-visible at `N` and at most `g N`, a shifter stays past it at every
replacement `vr_N(·, i)` with `i ≤ N`. -/
theorem IsWitness.le_apply_visibilityReplace_of_le (hw : IsWitness g σ) (hc : IsSelfVisible N c)
    (hcg : c ≤ g N) (hx : c ≤ σ x) (hi : i ≤ N) : c ≤ σ (visibilityReplace N i x) := by
  by_contra hlt
  rw [not_le] at hlt
  rcases hi.lt_or_eq with hi | rfl
  · -- The label is recovered by a second replacement, with which the shifter commutes.
    obtain ⟨j, hj, hx'⟩ := exists_visibilityReplace_visibilityReplace hi x
    have h := hw.visibilityReplace_comm _ N (hlt.le.trans hcg) j hj.le
    rw [hx'] at h
    exact (h ▸ visibilityReplace_lt_of_lt hc hlt hj).not_ge hx
  · exact (hx.trans (hw.monotone (le_visibilityReplace (by omega) x))).not_gt hlt

/-- **Capped commutation with visibility replacement.**  If a shifter agrees with the label `a`
at the source `x` up to a cap `c` self-visible at `N` and at most `g N`, then it agrees with
`vr_N(a, i)` at `vr_N(x, i)` up to `c`, for every `i ≤ N`. -/
theorem IsWitness.min_apply_visibilityReplace (hw : IsWitness g σ) (hc : IsSelfVisible N c)
    (hcg : c ≤ g N) (hx : min (σ x) c = min a c) (hi : i ≤ N) :
    min (σ (visibilityReplace N i x)) c = min (visibilityReplace N i a) c := by
  rcases lt_or_ge a c with hac | hca
  · -- Below the cap the shifter is determined, and the guard of the fifth law holds.
    have hσ : σ x = a := left_eq_of_min_eq_of_lt (hx.trans (min_eq_left hac.le)) hac
    rw [hw.visibilityReplace_comm x N (hσ ▸ hac.le.trans hcg) i hi, hσ]
  · have hσ : c ≤ σ x := min_eq_right_iff.mp (hx.trans (min_eq_right hca))
    rw [min_eq_right (hw.le_apply_visibilityReplace_of_le hc hcg hσ hi),
      min_eq_right (le_visibilityReplace_of_le hc hca hi)]

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {G C : ι} {P Q : Set ι}
  {w q : ι → Label.{u}}

/-! ### Gates -/

/-- How the row of the gate `G` reads a cell `e` below it, relative to the display `w`, the
private cap `C`, and the private cells `P`. -/
inductive GateReads (R : D.Rows.{u}) (G C : ι) (P : Set ι) (w : ι → Label.{u})
    (e : D.below (D.gradedIndex G)) : Prop
  /-- A bottom label, read as bottom. -/
  | bot (hwe : w e = ⊥) (hrow : R.row G e = ⊥)
  /-- A bottom label, read at most as a private cell labelled bottom. -/
  | botAnchor (z : D.below (D.gradedIndex G)) (hz : z.1 ∈ P) (hwz : w z = ⊥) (hwe : w e = ⊥)
      (hrow : R.row G e ≤ R.row G z)
  /-- A label `vr_N(w z, i)` of the anchor `z`, read as `vr_N` of the reading of `z`. -/
  | ref (z : D.below (D.gradedIndex G)) (hz : z.1 ∈ P) (i : ℕ) (hi : i ≤ D.grade G)
      (hwe : w e = visibilityReplace (D.grade G) i (w z))
      (hrow : R.row G e = visibilityReplace (D.grade G) i (R.row G z))
  /-- A label at least that of the private cap, read at least as a private cell labelled at
  least that of the private cap. -/
  | top (z : D.below (D.gradedIndex G)) (hz : z.1 ∈ P) (hzC : w C ≤ w z) (heC : w C ≤ w e)
      (hrow : R.row G z ≤ R.row G e)

/-- **Gate data**: the private cap `C` is a private cell, not bottom in the display `w`, of the
grade of the gate `G` with scope inside that of `G`; every donor cell lies below the gate, and the
row of the gate reads every donor cell outside the private cells.  Nothing is said about the
twins of the gate. -/
structure IsGate (R : D.Rows.{u}) (G C : ι) (P Q : Set ι) (w : ι → Label.{u}) : Prop where
  /-- The private cap is a private cell. -/
  cap_mem : C ∈ P
  /-- The scope of the private cap lies in that of the gate. -/
  scope_cap_subset : D.scope C ⊆ D.scope G
  /-- The private cap has the grade of the gate. -/
  grade_cap : D.grade C = D.grade G
  /-- The private cap is not bottom in the display. -/
  cap_ne_bot : w C ≠ ⊥
  /-- Every donor cell lies below the gate. -/
  le_gate : ∀ e ∈ Q, D.gradedIndex e ≤ D.gradedIndex G
  /-- The row of the gate reads every donor cell outside the private cells. -/
  reads : ∀ e (he : e ∈ Q), e ∉ P → GateReads R G C P w ⟨e, le_gate e he⟩

/-- **The twins read the gate at least as the cap**: every twin `t` of `G` (a cell `t ≠ G` with
the graded index of `G`) reads `C` at most as it reads `G`, `R.row t C ≤ R.row t G`.  A condition
on the rows, not on any labelling. -/
def TwinsReadGate (R : D.Rows.{u}) (G C : ι) : Prop :=
  ∀ t (hC : C ∈ D.below (D.gradedIndex t)) (hG : G ∈ D.below (D.gradedIndex t)),
    D.gradedIndex t = D.gradedIndex G → t ≠ G → R.row t ⟨C, hC⟩ ≤ R.row t ⟨G, hG⟩

namespace IsLawful

/-- **One witness at the gate.**  The locality at a cell `G` has a witness `(g, σ)` with
`q G ≤ g N`, `N` the grade of `G`; below `G` it decodes the row of `G` up to `q G`. -/
theorem exists_gateWitness (hq : R.IsLawful q) (G : ι) :
    ∃ g σ, IsWitness g σ ∧ q G ≤ g (D.grade G) ∧
      ∀ d : D.below (D.gradedIndex G), min (q d) (q G) = min (σ (R.row G d)) (q G) := by
  obtain ⟨g, σ, hw, heq⟩ := hq.locality G
  have heq : ∀ d : D.below (D.gradedIndex G),
      min (q d) (q G) = min (σ (R.row G d)) (g (D.grade d)) := heq
  have hG : q G ≤ g (D.grade G) := by
    have h := heq ⟨G, D.mem_below_gradedIndex G⟩
    rw [min_self] at h
    exact h ▸ min_le_right _ _
  refine ⟨g, σ, hw, hG, fun d ↦ ?_⟩
  have hgd : q G ≤ g (D.grade d) := hG.trans (hw.antitone ((D.mem_below).mp d.2).2)
  calc min (q d) (q G) = min (min (q d) (q G)) (q G) := by rw [min_assoc, min_self]
    _ = min (min (σ (R.row G d)) (g (D.grade d))) (q G) := by rw [heq d]
    _ = min (σ (R.row G d)) (q G) := by rw [min_assoc, min_eq_right hgd]

/-- **The gate inequality.**  If the scope of `C` lies in that of `G`, their grades agree, and
every other cell with the graded index of `G` is bottom, then `q C ≤ q G`, by availability. -/
theorem cap_le_gate (hq : R.IsLawful q) (hCG : D.scope C ⊆ D.scope G)
    (hgr : D.grade C = D.grade G)
    (htwin : ∀ t, D.gradedIndex t = D.gradedIndex G → t ≠ G → q t = ⊥) : q C ≤ q G := by
  obtain ⟨u, hu, hle⟩ := hq.availability C G hCG hgr
  rcases eq_or_ne u G with rfl | huG
  · exact hle
  · exact (hle.trans_eq (htwin u hu huG)).trans bot_le

/-- **Locality at the gate gives no lower bound on the gate.**  Lowering the value of a lawful
labelling at `G` to any `x ≤ q G` self-visible at the grade of `G` keeps the locality at `G`, by the
cap rule.  So a lower bound on the gate comes from availability, and through it from the bottom
pattern of the cells with the graded index of `G`. -/
theorem locality_lower_gate [DecidableEq ι] (hq : R.IsLawful q) (G : ι) {x : Label.{u}}
    (hx : IsSelfVisible (D.grade G) x) (hxG : x ≤ q G) :
    TransformsTo (fun d : D.below (D.gradedIndex G) ↦ D.grade d) (R.row G)
      fun d ↦ min (Function.update q G x d) (Function.update q G x G) := by
  have h := (hq.locality G).min_const (fun d ↦ ((D.mem_below).mp d.2).2) hx
  convert h using 2 with d
  rw [Function.update_self]
  by_cases hd : d.1 = G
  · rw [hd, Function.update_self, min_self, min_self, min_eq_right hxG]
  · rw [Function.update_of_ne hd, min_assoc, min_eq_right hxG]

/-- A cell read as bottom by the row of a cell `G` that is not bottom is bottom. -/
theorem eq_bot_of_row_eq_bot (hq : R.IsLawful q) (hG : q G ≠ ⊥)
    {t : D.below (D.gradedIndex G)} (hrow : R.row G t = ⊥) : q t = ⊥ :=
  (min_eq_bot.mp ((hq.locality G).eq_bot hrow)).resolve_right hG

/-- From agreement up to the gate, the two outcomes of a reading. -/
private theorem eq_or_le_of_min_eq {e : ι} (hCG : w C ≤ q G)
    (h : min (q e) (q G) = min (w e) (q G)) :
    (q e = w e ∧ w e < w C) ∨ (w C ≤ q e ∧ w C ≤ w e) := by
  rcases lt_or_ge (w e) (w C) with hlt | hle
  · exact .inl ⟨left_eq_of_min_eq_of_lt (h.trans (min_eq_left (hlt.le.trans hCG)))
      (hlt.trans_le hCG), hlt⟩
  · exact .inr ⟨(le_min hle hCG).trans (h.symm ▸ min_le_left _ _), hle⟩

/-- **The outcome of a reading.**  Let `q` be lawful, literally `w` on the private cells, with
`w C ≤ q G` and `w C ≠ ⊥`.  A donor cell read by the gate's row either has its display label,
which lies below `w C`, or has a value at least `w C`, as does its display label. -/
theorem eq_or_le_of_gateReads (hq : R.IsLawful q) (hlit : ∀ x ∈ P, q x = w x) (hC : w C ≠ ⊥)
    (hCG : w C ≤ q G) {e : D.below (D.gradedIndex G)} (h : GateReads R G C P w e) :
    (q e = w e ∧ w e < w C) ∨ (w C ≤ q e ∧ w C ≤ w e) := by
  obtain ⟨g, σ, hw, hgN, heq⟩ := hq.exists_gateWitness G
  have hG : q G ≠ ⊥ := fun h ↦ hC (le_bot_iff.mp (h ▸ hCG))
  have hbot : w e = ⊥ → min (q e) (q G) = ⊥ → q e = w e ∧ w e < w C := fun hwe hm ↦
    ⟨(min_eq_bot.mp hm).resolve_right hG |>.trans hwe.symm, hwe ▸ bot_lt_iff_ne_bot.mpr hC⟩
  cases h with
  | bot hwe hrow =>
    exact .inl (hbot hwe (by rw [heq e, hrow, hw.map_bot, min_eq_left bot_le]))
  | botAnchor z hz hwz hwe hrow =>
    have hσz : σ (R.row G z) = ⊥ := by
      have hz' := heq z
      rw [hlit z hz, hwz, min_eq_left bot_le] at hz'
      exact (min_eq_bot.mp hz'.symm).resolve_right hG
    have hσe : σ (R.row G e) = ⊥ := le_bot_iff.mp (hσz ▸ hw.monotone hrow)
    exact .inl (hbot hwe (by rw [heq e, hσe, min_eq_left bot_le]))
  | ref z hz i hi hwe hrow =>
    have hz' : min (σ (R.row G z)) (q G) = min (w z) (q G) := by rw [← heq z, hlit z hz]
    have h' := hw.min_apply_visibilityReplace (hq.orderly G) hgN hz' hi
    rw [← hrow, ← hwe, ← heq e] at h'
    exact eq_or_le_of_min_eq hCG h'
  | top z hz hzC heC hrow =>
    refine .inr ⟨?_, heC⟩
    calc w C ≤ min (w z) (q G) := le_min hzC hCG
      _ = min (σ (R.row G z)) (q G) := by rw [← hlit z hz, heq z]
      _ ≤ min (σ (R.row G e)) (q G) := min_le_min_right _ (hw.monotone hrow)
      _ = min (q e) (q G) := (heq e).symm
      _ ≤ q e := min_le_left _ _

/-- A donor cell read by the gate's row with display label below `w C` has its display label. -/
theorem eq_of_gateReads_of_lt (hq : R.IsLawful q) (hlit : ∀ x ∈ P, q x = w x) (hC : w C ≠ ⊥)
    (hCG : w C ≤ q G) {e : D.below (D.gradedIndex G)} (h : GateReads R G C P w e)
    (hlt : w e < w C) : q e = w e :=
  (hq.eq_or_le_of_gateReads hlit hC hCG h).elim And.left fun h ↦ absurd h.2 hlt.not_ge

/-- A donor cell read by the gate's row with display label at least `w C` has a value at least
`w C`. -/
theorem cap_le_of_gateReads_of_le (hq : R.IsLawful q) (hlit : ∀ x ∈ P, q x = w x)
    (hC : w C ≠ ⊥) (hCG : w C ≤ q G) {e : D.below (D.gradedIndex G)}
    (h : GateReads R G C P w e) (hle : w C ≤ w e) : w C ≤ q e :=
  (hq.eq_or_le_of_gateReads hlit hC hCG h).elim (fun h ↦ absurd hle h.2.not_ge) And.left

/-- A donor cell read by the gate's row agrees with its display label below `w C`. -/
theorem min_eq_of_gateReads (hq : R.IsLawful q) (hlit : ∀ x ∈ P, q x = w x) (hC : w C ≠ ⊥)
    (hCG : w C ≤ q G) {e : D.below (D.gradedIndex G)} (h : GateReads R G C P w e) :
    min (q e) (w C) = min (w e) (w C) := by
  rcases hq.eq_or_le_of_gateReads hlit hC hCG h with ⟨h, -⟩ | ⟨h₁, h₂⟩
  · rw [h]
  · rw [min_eq_right h₁, min_eq_right h₂]

end IsLawful

/-- **The gate inequality from the twin–gate coupling.**  If the scope of `C` lies in that of
`G`, their grades agree, and the twins of `G` read `G` at least as `C` (`TwinsReadGate`), then
`q C ≤ q G` for every lawful labelling `q`.  Availability gives a cell `u` with the graded index
of `G` and `q C ≤ q u`; if `u` is a twin, locality at `u` reads `C` at most as `G` with one
witness, at equal grades.  Nothing is assumed about the values of `q` at the twins. -/
theorem cap_le_gate_of_twinsReadGate (hq : R.IsLawful q) (hCG : D.scope C ⊆ D.scope G)
    (hgr : D.grade C = D.grade G) (htw : R.TwinsReadGate G C) : q C ≤ q G := by
  obtain ⟨u, hu, hle⟩ := hq.availability C G hCG hgr
  rcases eq_or_ne u G with rfl | huG
  · exact hle
  have hC : C ∈ D.below (D.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]; exact (D.gradedIndex_le_iff).mpr ⟨hCG, hgr.le⟩
  have hG : G ∈ D.below (D.gradedIndex u) := by rw [CellScheme.mem_below, hu]
  obtain ⟨g, σ, hw, heq⟩ := hq.locality u
  have hC' : min (q C) (q u) = min (σ (R.row u ⟨C, hC⟩)) (g (D.grade C)) := heq ⟨C, hC⟩
  have hG' : min (q G) (q u) = min (σ (R.row u ⟨G, hG⟩)) (g (D.grade G)) := heq ⟨G, hG⟩
  rw [min_eq_left hle] at hC'
  calc q C = min (σ (R.row u ⟨C, hC⟩)) (g (D.grade C)) := hC'
    _ ≤ min (σ (R.row u ⟨G, hG⟩)) (g (D.grade G)) := by
        rw [hgr]; exact min_le_min_right _ (hw.monotone (htw u hC hG hu huG))
    _ = min (q G) (q u) := hG'.symm
    _ ≤ q G := min_le_left _ _

/-- **Gate recovery from the gate inequality alone**: the twin hypothesis of `IsGate.recover`
enters only through `w C ≤ q G`.  A lawful labelling literally `w` on the private cells with
`w C ≤ q G` agrees with the display on every donor cell below `w C`. -/
theorem IsGate.recover_of_cap_le_gate (hgate : R.IsGate G C P Q w) (hq : R.IsLawful q)
    (hlit : ∀ x ∈ P, q x = w x) (hCG : w C ≤ q G) :
    ∀ e ∈ Q, min (q e) (w C) = min (w e) (w C) := by
  intro e he
  by_cases heP : e ∈ P
  · rw [hlit e heP]
  · exact hq.min_eq_of_gateReads hlit hgate.cap_ne_bot hCG (hgate.reads e he heP)

namespace IsGate

variable (hgate : R.IsGate G C P Q w) (hq : R.IsLawful q) (hlit : ∀ x ∈ P, q x = w x)
  (htwin : ∀ t, D.gradedIndex t = D.gradedIndex G → t ≠ G → q t = ⊥)
include hgate hq hlit htwin

/-- The gate inequality for gate data: `w C ≤ q G`. -/
theorem cap_le_gate : w C ≤ q G :=
  hlit C hgate.cap_mem ▸ hq.cap_le_gate hgate.scope_cap_subset hgate.grade_cap htwin

/-- The gate is not bottom. -/
theorem gate_ne_bot : q G ≠ ⊥ :=
  fun h ↦ hgate.cap_ne_bot (le_bot_iff.mp (h ▸ hgate.cap_le_gate hq hlit htwin))

/-- The outcome at every donor cell: its display label, which lies below `w C`, or a value at
least `w C`, as is its display label. -/
theorem eq_or_le (e : ι) (he : e ∈ Q) :
    (q e = w e ∧ w e < w C) ∨ (w C ≤ q e ∧ w C ≤ w e) := by
  by_cases heP : e ∈ P
  · rw [hlit e heP]
    exact (lt_or_ge (w e) (w C)).imp (⟨rfl, ·⟩) fun h ↦ ⟨h, h⟩
  · exact hq.eq_or_le_of_gateReads hlit hgate.cap_ne_bot (hgate.cap_le_gate hq hlit htwin)
      (hgate.reads e he heP)

/-- **Gate recovery.**  A lawful labelling `q` that is literally the display `w` on the private
cells and is bottom at every twin of the gate has `w C ≤ q G`, and agrees with the display on
every donor cell below the label `w C` of the private cap. -/
theorem recover : w C ≤ q G ∧ ∀ e ∈ Q, min (q e) (w C) = min (w e) (w C) :=
  ⟨hgate.cap_le_gate hq hlit htwin,
    hgate.recover_of_cap_le_gate hq hlit (hgate.cap_le_gate hq hlit htwin)⟩

/-- **Exact recovery below the private cap**: a donor cell with display label below `w C` has its
display label. -/
theorem eq_of_lt_cap {e : ι} (he : e ∈ Q) (hlt : w e < w C) : q e = w e :=
  (hgate.eq_or_le hq hlit htwin e he).elim And.left fun h ↦ absurd h.2 hlt.not_ge

/-- **Donor labels above the private cap** come back only as values at least `w C`. -/
theorem cap_le_of_cap_le {e : ι} (he : e ∈ Q) (hle : w C ≤ w e) : w C ≤ q e :=
  (hgate.eq_or_le hq hlit htwin e he).elim (fun h ↦ absurd hle h.2.not_ge) And.left

/-- **A private cap labelled `⊤`** recovers every donor label exactly, the formal top included. -/
theorem eq_of_cap_eq_top (hC : w C = ⊤) {e : ι} (he : e ∈ Q) : q e = w e := by
  rcases hgate.eq_or_le hq hlit htwin e he with ⟨h, -⟩ | ⟨h₁, h₂⟩
  · exact h
  · rw [hC, top_le_iff] at h₁ h₂
    rw [h₁, h₂]

end IsGate

/-- **Gate recovery for a gate without twins** (U): the literal private face alone suffices. -/
theorem IsGate.recover_of_unique (hgate : R.IsGate G C P Q w) (hq : R.IsLawful q)
    (hlit : ∀ x ∈ P, q x = w x) (huniq : ∀ t, D.gradedIndex t = D.gradedIndex G → t = G) :
    w C ≤ q G ∧ ∀ e ∈ Q, min (q e) (w C) = min (w e) (w C) :=
  hgate.recover hq hlit fun t ht htG ↦ absurd (huniq t ht) htG

/-- **Gate recovery for a gate whose row is bottom at its twins** (T): a literal private face and a
gate that is not bottom suffice. -/
theorem IsGate.recover_of_row_twin (hgate : R.IsGate G C P Q w) (hq : R.IsLawful q)
    (hlit : ∀ x ∈ P, q x = w x)
    (hrow : ∀ t (ht : D.gradedIndex t = D.gradedIndex G), t ≠ G → R.row G ⟨t, ht.le⟩ = ⊥)
    (hG : q G ≠ ⊥) : w C ≤ q G ∧ ∀ e ∈ Q, min (q e) (w C) = min (w e) (w C) :=
  hgate.recover hq hlit fun t ht htG ↦ hq.eq_bot_of_row_eq_bot hG (hrow t ht htG)

/-- **Gate recovery with the twin–gate coupling**: when the twins of the gate read the gate at
least as the cap (`TwinsReadGate`), a lawful labelling literally `w` on the private cells has
`w C ≤ q G` and agrees with the display on every donor cell below `w C`.  Nothing is assumed about
the values of `q` at the twins. -/
theorem IsGate.recover_of_twinsReadGate (hgate : R.IsGate G C P Q w) (hq : R.IsLawful q)
    (hlit : ∀ x ∈ P, q x = w x) (htw : R.TwinsReadGate G C) :
    w C ≤ q G ∧ ∀ e ∈ Q, min (q e) (w C) = min (w e) (w C) := by
  have hCG : w C ≤ q G := hlit C hgate.cap_mem ▸
    cap_le_gate_of_twinsReadGate hq hgate.scope_cap_subset hgate.grade_cap htw
  exact ⟨hCG, hgate.recover_of_cap_le_gate hq hlit hCG⟩

/-! ### Readers -/

section Readers

variable {K : ι} {S : Set ι}

/-- The row of `G` **reads only `S`** at its graded index: it is `⊥` at every other cell of the
graded index of `G` that is not in `S`. -/
def ReadsOnly (R : D.Rows.{u}) (G : ι) (S : Set ι) : Prop :=
  ∀ t (ht : D.gradedIndex t = D.gradedIndex G), t ≠ G → t ∉ S → R.row G ⟨t, ht.le⟩ = ⊥

/-- A cell `K` of the graded index of `G` that the row of `G` reads at least as `G` itself is at
least `G` in every labelling `q` satisfying the locality at `G`. -/
theorem le_of_row_self_le_of_locality
    (hl : TransformsTo (fun d : D.below (D.gradedIndex G) ↦ D.grade d) (R.row G)
      (fun d ↦ min (q d) (q G)))
    (hKG : D.gradedIndex K = D.gradedIndex G)
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩) : q G ≤ q K := by
  have h := hl.le_of_le (d := ⟨G, D.mem_below_gradedIndex G⟩) (d' := ⟨K, hKG.le⟩) hrow
    (congrArg Prod.snd hKG).le
  simp only [min_self] at h
  exact h.trans (min_le_left _ _)

namespace IsLawful

/-- A cell `K` of the graded index of `G` that the row of `G` reads at least as `G` itself is at
least `G` in every lawful labelling. -/
theorem le_of_row_self_le (hq : R.IsLawful q) (hKG : D.gradedIndex K = D.gradedIndex G)
    (hrow : R.row G ⟨G, D.mem_below_gradedIndex G⟩ ≤ R.row G ⟨K, hKG.le⟩) : q G ≤ q K :=
  le_of_row_self_le_of_locality (hq.locality G) hKG hrow

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
  have hGK : r G ≤ r K := le_of_row_self_le_of_locality (hl G hGmem) hKG hrow
  intro t ht
  by_cases htG : t = G
  · exact htG ▸ hGK
  by_cases htK : t = K
  · exact htK ▸ le_rfl
  have ht' : D.gradedIndex t = D.gradedIndex G := ht.trans hGY.symm
  have h0 := (hl G hGmem).eq_bot (d := ⟨t, ht'.le⟩) (honly t ht' htG htK)
  exact ((min_eq_bot.mp h0).resolve_right hG).le.trans bot_le

end Readers

end VaughtConjecture.CellScheme.Rows

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Continuation
import VaughtConjecture.Realization.Receiving

/-!
# (R4) at one occurrence

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.2–3.4 ((R4) of the table of Layer 3: its occurrence, its evaluation, and its recovery
statement); semantic contract, item 8.

Throughout, `R` is a realization at the block stage `λ_ξ = blockStage ξ` on a carrier `M`, stably
lawful, with stable candidate `R.stableCandidate hlaw` at `λ_{ξ+1} = λ_ξ + ω`.  Fix an occurrence
`x` of the candidate (a tuple typed in `R`, with its stable type), a coface `D` of the type of `x`
at `λ_{ξ+1}` (a legal stage type on one more point whose face along the first points is that type),
and an ordinal `γ`.  **(R4) at `(x, D, γ)`** (`Realization.StablyReceivesAt`) is the body of
`StableCappedReceiving`: some point extends `x` to a tuple whose candidate type `Q` is on the scheme
of `D`, equals `D` at every cell where `D` is not the formal top, and exceeds `γ` at every cell
where `D` is the formal top.  `StableCappedReceiving` is (R4) at every `(x, D, γ)` with `x` of
positive arity and `γ < λ_{ξ+1}`, for every model `R` at `λ_ξ`, `ξ < ω₁`, that is not cover-hollow
and has top-grade supremum `⊤` (`stableCappedReceiving_iff_forall_stablyReceivesAt`).  Larger `γ`
is stronger (`Realization.StablyReceivesAt.mono`), so only `γ = λ_ξ + K`, `K : ℕ`, matters
(`Realization.forall_lt_stablyReceivesAt_iff`).

**The two parts** (`Realization.stablyReceivesAt_iff`, for `λ_ξ ≤ γ`).  (R4) at `(x, D, γ)` holds
exactly when some point `y` extending `x` has

1. **exact receiving of the reduction of the donor in `R`**: the type of `x⌢y` in `R` is exactly
   `D↓λ_ξ`, the formal top included (a statement about `R` at `λ_ξ`); and
2. **calibration of the stable labels**: at each cell `d` with `D↓λ_ξ` the formal top there, the
   stable label of `d` at `x⌢y` is `D d` when `D d` is an ordinal (in the block
   `[λ_ξ, λ_ξ + ω)`), and exceeds `γ` when `D d` is the formal top.

The point `y` is the same in both parts.  Two points with one type in `R` can have different stable
labels: the stable offset is a supremum over the rooted covers of the tuple in `R`, not a function
of its type.  So the two parts cannot be supplied separately, by two receiving statements.

**The old cells are automatic** (`Realization.stableType_label_eq_of_mem_visibleCells`): at a cell
whose scope lies in the first points (a cell **visible through** the face of `x`), the candidate
type of every `x⌢y` with type `D↓λ_ξ` in `R` has the label of `D`, by exact consistency of the
candidate (`Realization.isConsistent_stableCandidate`).  So the content of (R4) is at the **new
cells reducing to the top**: the cells of `D` whose scope contains the new point and whose label is
at least `λ_ξ` (`Realization.stablyReceivesAt_iff_of_mem_cofaces`).

**Donors without new top cells**
(`Realization.exists_stableCandidate_eval_eq_of_hasFiniteCutReceiving`, a special case proved
conditionally on finite-cut receiving of `R`, which is (R1) of the table of Layer 3 for the model
`R`): if every cell of `D` reducing to the top at `λ_ξ` is visible
through the face of `x`, the candidate receives `D` exactly over `x`.  Finite-cut receiving at a
cutoff below `λ_ξ` above every other label of `D↓λ_ξ` gives the type `D↓λ_ξ` exactly, since the
cells where it could differ from `D↓λ_ξ` (the top cells) are old.  At a new cell reducing to the
top no cutoff below `λ_ξ` separates the formal top from a large ordinal, and finite-cut receiving
says nothing about the stable label there.

**(R4) at a model is finite-cut receiving of its candidate.**  For a fixed stably lawful `R`,
finite-cut receiving of the candidate gives (R4) at every `(x, D, γ)` with `γ < λ_{ξ+1}`
(`Realization.stablyReceivesAt_of_hasFiniteCutReceiving`: one cutoff above `γ` and above every
label of `D` other than the formal top, `StageType.capped_of_mem_receivingFamily`).  Conversely,
for a model `R`, (R4) at every occurrence of positive arity and the amalgam over the empty face at
`λ_{ξ+1}` give finite-cut receiving of the candidate
(`Realization.forall_stablyReceivesAt_iff_hasFiniteCutReceiving`).  So (R4) at `R` is an exact
reformulation of finite-cut receiving of the candidate, which is (R1) for the candidate read as a
model.

**Models with a model expansion** (`Realization.eq_stableCandidate_of_reduce_eq`,
`Realization.stablyReceivesAt_of_reduce_eq`).  If `R` is the reduction of an exactly consistent
realization `R'` at `λ_{ξ+1}` with legal types and finite-extension receiving, given forcing donors
at `ξ`, then `R'` is the candidate (normalization, `Realization.label_eq_stableLabel`), and if `R'`
has finite-cut receiving, (R4) holds at every `(x, D, γ)` of `R`.  Apart from its reformulation
as finite-cut receiving of the candidate, this is the only class of models at which (R4) is proved
here; it is derived from the expansion, so it cannot be used to construct the expansion.  The
resulting equivalence of `StableCappedReceiving` with the continuation criterion, under (R1),
forcing donors and the coface instances, is
`Expansion.stableCappedReceiving_iff_continuationCriterion`, in
`VaughtConjecture.Expansion.StableReceiving`.

**The evaluation step** (`Realization.stablyReceivesAt_of_isStableRecoveryScheme`, proved with no
hypothesis beyond modelhood of `R`).  This is the occurrence and the evaluation of (R4) in the
roadmap (Layer 3, 3.2): let `w` be an occurrence of `R` containing `x` along `f`, and let `E` be a
scheme on the points of `w` and one more that is a **stable recovery scheme** for the stable type
`T⁺` of `w`, `f`, `D` and `γ` (`StageType.IsStableRecoveryScheme`): some coface of `T⁺↓λ_ξ` (the
type of `w`) lies on `E`, and every stage type at `λ_{ξ+1}` on `E` with face `T⁺` along the first
points has, along `f` followed by the new point, a face that satisfies (R4)'s conclusion for `D`
and `γ`.  Then generalized saturation realizes `E` over `w`; the candidate type of the realized
tuple is a stage type at `λ_{ξ+1}` on `E` (stable lawfulness, `Realization.IsModel.isStablyLawful`)
with face `T⁺` (exact consistency of the candidate); and its face along `f` followed by the new
point is the candidate type of the received tuple.  The recovery is required for every stage type
on `E` with face `T⁺`, the form of the recovery statement of the roadmap (3.2: for every
restriction-compatible labelling), here applied to the stable labelling.

**The reduction of (R4)** (`StableCappedReceiving.of_stableRecoveryContexts`,
`Realization.stablyReceivesAt_of_acquiresCalibratedContexts`).  (R4) follows from

* `StageType.HasStableRecoverySchemes ξ C`, a **finite** statement about stage types (no
  realization): every legal stage type `T⁺` at `λ_{ξ+1}` that satisfies a predicate `C` (a
  calibration) for `f`, `D` and `γ` has a stable recovery scheme; and
* `Realization.AcquiresCalibratedContexts ξ C`, a statement about one model: over every occurrence
  `x` of its candidate of positive arity, for every `D` and `γ`, some occurrence `w` containing `x`
  has a stable type satisfying `C`.

The calibration `C` is a parameter, so the theorem holds for every choice.  For the **marker and
cap calibration** (`StageType.MarkerCapCalibration`: a cell labelled `λ_ξ + i` and a cell labelled
at least `λ_ξ` and above `γ`) the acquisition is proved for every model that is not cover-hollow
and has top-grade supremum `⊤` (`Realization.IsModel.acquiresCalibratedContexts_markerCap`: the
attained proper stable label, a stable label above `λ_ξ + K` from unbounded growth, and covering).
So (R4) follows from the single finite statement `StageType.HasStableRecoverySchemes ξ
(StageType.MarkerCapCalibration ξ)` at every `ξ < ω₁`
(`StableCappedReceiving.of_hasStableRecoverySchemes_markerCap`).  That statement is false at every
`ξ` (`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`, in
`VaughtConjecture.Continuation.StableRecoveryCounterexample`): over a root with no private point
(`f` the identity) a stable recovery scheme is the scheme of `D`, and two lifts of one five-cell
type order its twins both ways.  Its cap is already the formal top at `λ_ξ` (a label at least
`λ_ξ` reduces to `⊤`, `Label.reduce_of_le`).  What it lacks relative to the roadmap's design
(Layer 3, 3.3) and to the coupled gate form of (R1) (`StageType.HasCoupledGatedPinnedExtensions`)
is a cap of full scope and full grade `N` with stable value above `λ_ξ + ℓ > γ`, a marker offset
below `N` (in the design only), a reference cell (an anchor, `StageType.IsAnchored`) for each
block of a proper label of `D`, and the arity bound `k + 1 < m` for a root of `k` points in `T⁺`
on `m` points.  The form of (R1) without the coupling, `StageType.HasGatedPinnedExtensions`, is
refuted
(`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).  The recovery clause covers every
stage type on the scheme with face `T⁺`, so every proper label of `D` at a new cell, also in a
block below `λ_ξ` with no cell of `T⁺`, must be determined by the rows of the scheme from the
labels of `T⁺` alone.  The graded cap calibration (`StageType.GradedCapCalibration`, in
`VaughtConjecture.Continuation.StableRecovery`) adds a cap of grade above the arity of the root,
the reference offsets and the finite parts of `D`, labelled at least `λ_ξ` plus its grade, and
reference cells of grade at most that of the cap; its acquisition is proved, and stable recovery
schemes for it are open.  The acquisition of the roadmap's calibration, in particular a cap of full
scope and full grade with a large stable value, is not proved.  The apex coatom extension property
does not enter (R4): it enters output 3 only through the coface instances at `λ_{ξ+1}`.

## References

Generalized saturation, which realizes a stable recovery scheme over an occurrence, is
[Kni26, Definition 3.2.1, clause 4(a)i].

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Ordinal Label StageType

/-! ### Capped agreement and receiving families -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **Receiving gives capped agreement**: a member `Q` of the receiving family of `D` at a cutoff
`c` above every label of `D` other than the formal top and above `γ` equals `D` at every cell where
`D` is not the formal top and exceeds `γ` at every cell where `D` is the formal top.  The converse
of `StageType.mem_receivingFamily_of_capped`. -/
theorem capped_of_mem_receivingFamily {D Q : StageType.{u} α n} {c : Label.{u}} {γ : Ordinal.{u}}
    (hQ : Q ∈ receivingFamily D c) (hD : ∀ j, D.label j ≠ ⊤ → D.label j < c)
    (hγ : (γ : Label.{u}) < c) (i : Fin Q.card) (j : Fin D.card) (hij : (i : ℕ) = j) :
    (D.label j ≠ ⊤ → Q.label i = D.label j) ∧ (D.label j = ⊤ → (γ : Label.{u}) < Q.label i) := by
  have h := hQ.2 i j hij
  refine ⟨fun hj ↦ ?_, fun hj ↦ ?_⟩
  · rw [min_eq_left (hD j hj).le] at h
    rcases le_or_gt c (Q.label i) with hc | hc
    · rw [min_eq_right hc] at h
      exact absurd h (hD j hj).ne'
    · rwa [min_eq_left hc.le] at h
  · rw [hj, min_eq_right le_top] at h
    exact hγ.trans_le (min_eq_right_iff.mp h)

/-- **A cutoff for capped agreement**: at a limit stage `α`, for `γ < α`, some permitted cutoff
lies above `γ` and above every label of `D` other than the formal top. -/
theorem exists_isPermittedCutoff_capped (hα : Order.IsSuccLimit α) (D : StageType.{u} α n)
    {γ : Ordinal.{u}} (hγ : γ < α) :
    ∃ c : Label.{u}, IsPermittedCutoff α c ∧ (∀ j, D.label j ≠ ⊤ → D.label j < c) ∧
      (γ : Label.{u}) < c := by
  obtain ⟨δ, hδ, hD⟩ := D.exists_lt_forall_label_lt hα
  refine ⟨((max δ (Order.succ γ) : Ordinal.{u}) : Label.{u}),
    isPermittedCutoff_coe.mpr (max_lt hδ (hα.succ_lt hγ)), fun j hj ↦ ?_, ?_⟩
  · exact (hD j hj).trans_le (by exact_mod_cast le_max_left δ (Order.succ γ))
  · exact_mod_cast (Order.lt_succ γ).trans_le (le_max_right δ (Order.succ γ))

/-- **Equal faces give equal labels at the visible cells**: two stage types on one scheme with the
same face along `f` have the same label at every cell visible through `f` (its scope lies in the
range of `f`). -/
theorem label_eq_of_mem_visibleCells {P : StageType.{u} α m} {f : Fin m ↪ Fin n}
    {Q D : StageType.{u} α n} (hS : Q.toScheme = D.toScheme) (hQ : restrictFace f Q = some P)
    (hD : restrictFace f D = some P) {i : Fin Q.card} {j : Fin D.card} (hij : (i : ℕ) = j)
    (hj : j ∈ D.toScheme.visibleCells f) : Q.label i = D.label j := by
  obtain ⟨S, ℓ, _, _, _, _⟩ := Q
  obtain ⟨S', ℓ', _, _, _, _⟩ := D
  obtain rfl : S = S' := hS
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨hf, hQP⟩ := (restrictFace_eq_some_iff _ f).mp hQ
  obtain ⟨hf', hDP⟩ := (restrictFace_eq_some_iff _ f).mp hD
  obtain ⟨a, rfl⟩ : i ∈ Set.range (S.cellMap f) := by
    rw [Scheme.range_cellMap]
    exact hj
  exact label_congr (hQP.trans hDP.symm) rfl

variable {ξ : Ordinal.{u}}

/-- A **stable recovery scheme** for a stage type `T⁺` at `λ_{ξ+1}` on `m` points, an embedding
`f` of `k` points into them, a stage type `D` on `k + 1` points and an ordinal `γ`: a scheme `E` on
`m + 1` points such that

* some coface of `T⁺↓λ_ξ` lies on `E` (so generalized saturation realizes `E` over an occurrence of
  type `T⁺↓λ_ξ`); and
* **recovery**: every stage type `Q'` at `λ_{ξ+1}` on `E` whose face along the first `m` points is
  `T⁺` has, along `f` followed by the new point, a face `Q` on the scheme of `D` that equals `D` at
  every cell where `D` is not the formal top and exceeds `γ` at every cell where `D` is the formal
  top.

The recovery clause is the counterpart for (R4) of the recovery of a coupled gated extension in
(R1), where every stage type on the display with literal private face has a donor face in the
receiving family (`StageType.CoupledGatedExtension.exists_restrictFace_mem_receivingFamily`, under
`StageType.HasCoupledGatedPinnedExtensions`). -/
def IsStableRecoveryScheme (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) (E : Scheme.{u} (m + 1)) :
    Prop :=
  (∃ q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces, q.toScheme = E) ∧
    ∀ Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1), Q'.toScheme = E →
      restrictFace Fin.castSuccEmb Q' = some Tp →
        ∃ Q, restrictFace (extendByLast f) Q' = some Q ∧ Q.toScheme = D.toScheme ∧
          ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
            (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
              (D.label j = ⊤ → (γ : Label.{u}) < Q.label i)

variable (ξ) in
/-- **Stable recovery schemes for a calibration `C`**, a finite statement about stage types with no
realization: every legal stage type `T⁺` at `λ_{ξ+1}` satisfying `C` for an embedding `f`
(of positive length), a coface `D` of the face of `T⁺` along `f`, and an ordinal `γ < λ_{ξ+1}`,
has a stable recovery scheme.  In the roadmap's design (Layer 3, 3.1 and 3.3) `C` is the calibrated
data of (R4) and the scheme is the growth construction, shared with (R3).  For the marker and cap
calibration (`StageType.MarkerCapCalibration`, acquisition proved) it is **false** at every `ξ`
(`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`); for the
graded cap calibration (`StageType.GradedCapCalibration`, acquisition proved) it is open. -/
def HasStableRecoverySchemes
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      C Tp f D γ → ∃ E : Scheme.{u} (m + 1), Tp.IsStableRecoveryScheme f D γ E

variable (ξ) in
/-- The **marker and cap calibration**: a stage type `T⁺` at `λ_{ξ+1}` has a cell labelled
`λ_ξ + i` for some `i : ℕ` (a **marker**) and a cell labelled at least `λ_ξ` and above `γ` (a
**cap**).  It does not depend on `f` and `D`.  The cap is the formal top at `λ_ξ` (a label at least
`λ_ξ` reduces to `⊤`).  This is less than the calibrated data of the roadmap (Layer 3, 3.3) and of
the coupled gate form of (R1) (`StageType.HasCoupledGatedPinnedExtensions`), which also ask for a
cap of full scope and full grade `N`, a marker offset below `N` (in the design only), reference
cells for the blocks of the proper labels of `D` (anchors, `StageType.IsAnchored`), and the arity
bound `k + 1 < m`.  Stable recovery schemes for it do not exist
(`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`). -/
def MarkerCapCalibration ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (_ : Fin k ↪ Fin m)
    (_ : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) : Prop :=
  (∃ (a : Fin Tp.card) (i : ℕ), Tp.label a = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})) ∧
    ∃ b : Fin Tp.card, (γ : Label.{u}) < Tp.label b ∧ (blockStage ξ : Label.{u}) ≤ Tp.label b

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-! ### (R4) at one occurrence -/

section AtOccurrence

variable (R) (hlaw : R.IsStablyLawful)

/-- **(R4) at one occurrence**: over the occurrence `x` of the stable candidate, for the stage type
`D` on one more point and the ordinal `γ`, some point extends `x` to a tuple whose candidate type
is on the scheme of `D`, equals `D` at every cell where `D` is not the formal top, and exceeds `γ`
at every cell where `D` is the formal top. -/
def StablyReceivesAt (x : (R.stableCandidate hlaw).Occurrence)
    (D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)) (γ : Ordinal.{u}) : Prop :=
  ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
    ∃ Q, (R.stableCandidate hlaw).eval u = some Q ∧ Q.toScheme = D.toScheme ∧
      ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
        (D.label j ≠ ⊤ → Q.label i = D.label j) ∧ (D.label j = ⊤ → (γ : Label.{u}) < Q.label i)

end AtOccurrence

variable {hlaw : R.IsStablyLawful} {x : (R.stableCandidate hlaw).Occurrence}
  {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)} {γ γ' : Ordinal.{u}}

/-- Every ordinal below `λ_{ξ+1}` is at most `λ_ξ + K` for some `K : ℕ`. -/
theorem exists_le_blockStage_add_natCast (hγ : γ < blockStage (ξ + 1)) :
    ∃ K : ℕ, γ ≤ blockStage ξ + K := by
  rcases lt_or_ge γ (blockStage ξ) with hlt | hle
  · exact ⟨0, by simpa using hlt.le⟩
  · rw [blockStage_add_one] at hγ
    obtain ⟨K, hK⟩ := lt_omega0.mp ((Ordinal.sub_lt_of_le hle).mpr hγ)
    exact ⟨K, by rw [← hK, Ordinal.add_sub_cancel_of_le hle]⟩

/-- **Larger `γ` is stronger.** -/
theorem StablyReceivesAt.mono (h : R.StablyReceivesAt hlaw x D γ) (hγ : γ' ≤ γ) :
    R.StablyReceivesAt hlaw x D γ' := by
  obtain ⟨u, hu, Q, hQ, hS, hl⟩ := h
  exact ⟨u, hu, Q, hQ, hS, fun i j hij ↦ ⟨(hl i j hij).1, fun hj ↦
    (by exact_mod_cast hγ : (γ' : Label.{u}) ≤ γ).trans_lt ((hl i j hij).2 hj)⟩⟩

/-- **Only `γ = λ_ξ + K` matters**: (R4) at every `γ < λ_{ξ+1}` is (R4) at every `λ_ξ + K`,
`K : ℕ`. -/
theorem forall_lt_stablyReceivesAt_iff :
    (∀ γ < blockStage (ξ + 1), R.StablyReceivesAt hlaw x D γ) ↔
      ∀ K : ℕ, R.StablyReceivesAt hlaw x D (blockStage ξ + K) := by
  refine ⟨fun h K ↦ h _ ?_, fun h γ hγ ↦ ?_⟩
  · rw [blockStage_add_one]
    exact add_lt_add_right (natCast_lt_omega0 K) _
  · obtain ⟨K, hK⟩ := exists_le_blockStage_add_natCast hγ
    exact (h K).mono hK

/-- **The two parts of (R4) at one occurrence**, for `λ_ξ ≤ γ`: (R4) at `(x, D, γ)` holds exactly
when some point `y` extending `x` has type `D↓λ_ξ` in `R` (exact receiving of the reduction of the
donor, the formal top included) and, at each cell where `D↓λ_ξ` is the formal top, a stable label
equal to the label of `D` when that label is an ordinal and above `γ` when it is the formal top
(calibration).  The point is the same in both parts. -/
theorem stablyReceivesAt_iff (hγ : blockStage ξ ≤ γ) :
    R.StablyReceivesAt hlaw x D γ ↔
      ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
        R.eval u = some (D.reduce (isSuccPrelimit_blockStage ξ)) ∧
        ∀ d : Fin D.card, (D.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤ →
          (D.label d ≠ ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u
              (D.reduce (isSuccPrelimit_blockStage ξ)) d = D.label d) ∧
          (D.label d = ⊤ → (γ : Label.{u}) < R.stableLabel (blockStage (ξ + 1))
              (isSuccPrelimit_blockStage ξ) u (D.reduce (isSuccPrelimit_blockStage ξ)) d) := by
  constructor
  · rintro ⟨u, hu, Q, hQ, hS, hl⟩
    obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hQ
    obtain rfl : t = D.reduce (isSuccPrelimit_blockStage ξ) := by
      refine StageType.ext hS fun i j hij ↦ ?_
      refine (reduce_stableSection (R := R) (u := u) i).symm.trans ?_
      -- `(D.reduce _).label j` is `Label.reduce (blockStage ξ) (D.label j)` by definition
      -- (`StageType.reduce_label`, which `rw` does not match here)
      change _ = Label.reduce (blockStage ξ) (D.label j)
      by_cases hj : D.label j = ⊤
      · have hle : ((blockStage ξ : Ordinal.{u}) : Label.{u}) ≤ R.stableSection u t i :=
          le_trans (by exact_mod_cast hγ) ((hl i j hij).2 hj).le
        exact (Label.reduce_of_le hle).trans
          ((congrArg (Label.reduce (blockStage ξ)) hj).trans Label.reduce_top).symm
      · exact congrArg _ ((hl i j hij).1 hj)
    refine ⟨u, hu, ht, fun d hd ↦ ?_⟩
    have e : R.stableSection u (D.reduce (isSuccPrelimit_blockStage ξ)) d =
        R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u
          (D.reduce (isSuccPrelimit_blockStage ξ)) d := stableSection_of_eq_top hd
    exact ⟨fun h1 ↦ e.symm.trans ((hl d d rfl).1 h1), fun h1 ↦ ((hl d d rfl).2 h1).trans_eq e⟩
  · rintro ⟨u, hu, ht, hcal⟩
    refine ⟨u, hu, _, stableCandidate_eval_of_eval ht, rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    by_cases hd : (D.reduce (isSuccPrelimit_blockStage ξ)).label i = ⊤
    · have e : R.stableSection u (D.reduce (isSuccPrelimit_blockStage ξ)) i =
          R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u
            (D.reduce (isSuccPrelimit_blockStage ξ)) i := stableSection_of_eq_top hd
      exact ⟨fun h1 ↦ e.trans ((hcal i hd).1 h1), fun h1 ↦ ((hcal i hd).2 h1).trans_eq e.symm⟩
    · have e : R.stableSection u (D.reduce (isSuccPrelimit_blockStage ξ)) i =
          (D.reduce (isSuccPrelimit_blockStage ξ)).label i := stableSection_of_ne_top hd
      have hlt : D.label i < (blockStage ξ : Label.{u}) := by
        by_contra hge
        exact hd (Label.reduce_of_le (not_lt.mp hge))
      exact ⟨fun _ ↦ e.trans (Label.reduce_of_lt hlt),
        fun hi ↦ absurd ((congrArg (Label.reduce (blockStage ξ)) hi).trans Label.reduce_top) hd⟩

/-- **The reduction of a coface is a coface**: for a coface `D` of the type of an occurrence `x`
of the candidate, `D↓λ_ξ` is a coface of the type in `R` of the tuple of `x`. -/
theorem reduce_mem_cofaces {t : StageType.{u} (blockStage ξ) x.arity}
    (ht : R.eval x.tuple = some t) (hD : D ∈ x.type.cofaces) :
    D.reduce (isSuccPrelimit_blockStage ξ) ∈ t.cofaces := by
  refine ⟨hD.1.reduce _, ?_⟩
  have hx := x.eval_tuple
  rw [stableCandidate_eval_of_eval ht, Option.some_inj] at hx
  rw [restrictFace_reduce, hD.2, Option.map_some, ← hx, reduce_stableType]

/-- **The old cells are automatic**: if `x⌢y` has type `D↓λ_ξ` in `R`, the candidate type of
`x⌢y` has the label of `D` at every cell visible through the face of `x`, by exact consistency of
the candidate. -/
theorem stableType_label_eq_of_mem_visibleCells (hR : R.IsConsistent) (hc : R.IsCovering)
    (hD : D ∈ x.type.cofaces) {u : Fin (x.arity + 1) ↪ M} (hu : Fin.castSuccEmb.trans u = x.tuple)
    (ht : R.eval u = some (D.reduce (isSuccPrelimit_blockStage ξ))) {d : Fin D.card}
    (hd : d ∈ D.toScheme.visibleCells Fin.castSuccEmb) :
    (R.stableType hlaw u _ ht).label d = D.label d := by
  have hface : restrictFace Fin.castSuccEmb (R.stableType hlaw u _ ht) = some x.type := by
    rw [← isConsistent_stableCandidate hR hc u _ Fin.castSuccEmb (stableCandidate_eval_of_eval ht),
      hu, x.eval_tuple]
  exact label_eq_of_mem_visibleCells (Q := R.stableType hlaw u _ ht) (D := D) rfl hface hD.2 rfl hd

/-- **(R4) at one occurrence is calibration at the new cells reducing to the top**: for a coface
`D`, in an exactly consistent covering `R` and for `λ_ξ ≤ γ`, (R4) at `(x, D, γ)` holds exactly
when some point `y` extending `x` has type `D↓λ_ξ` in `R` and the calibrated stable labels at the
cells reducing to the top that are not visible through the face of `x`. -/
theorem stablyReceivesAt_iff_of_mem_cofaces (hR : R.IsConsistent) (hc : R.IsCovering)
    (hD : D ∈ x.type.cofaces) (hγ : blockStage ξ ≤ γ) :
    R.StablyReceivesAt hlaw x D γ ↔
      ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
        R.eval u = some (D.reduce (isSuccPrelimit_blockStage ξ)) ∧
        ∀ d : Fin D.card, d ∉ D.toScheme.visibleCells Fin.castSuccEmb →
          (D.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤ →
          (D.label d ≠ ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u
              (D.reduce (isSuccPrelimit_blockStage ξ)) d = D.label d) ∧
          (D.label d = ⊤ → (γ : Label.{u}) < R.stableLabel (blockStage (ξ + 1))
              (isSuccPrelimit_blockStage ξ) u (D.reduce (isSuccPrelimit_blockStage ξ)) d) := by
  rw [stablyReceivesAt_iff hγ]
  refine ⟨fun ⟨u, hu, ht, h⟩ ↦ ⟨u, hu, ht, fun d _ hd ↦ h d hd⟩,
    fun ⟨u, hu, ht, h⟩ ↦ ⟨u, hu, ht, fun d hd ↦ ?_⟩⟩
  by_cases hv : d ∈ D.toScheme.visibleCells Fin.castSuccEmb
  · have hl := stableType_label_eq_of_mem_visibleCells (hlaw := hlaw) hR hc hD hu ht hv
    have e : R.stableSection u (D.reduce (isSuccPrelimit_blockStage ξ)) d =
        R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u
          (D.reduce (isSuccPrelimit_blockStage ξ)) d := stableSection_of_eq_top hd
    have key := e.symm.trans hl
    exact ⟨fun _ ↦ key, fun h1 ↦ (lt_of_lt_of_eq (WithBot.coe_lt_coe.mpr
      (WithTop.coe_lt_top γ)) h1.symm).trans_eq key.symm⟩
  · exact h d hv hd

/-! ### Where non-hollowness and unbounded growth are used -/

/-- **(R4) fails at a cover-hollow realization for every donor with a label in the new block**: if
`R` is cover-hollow, the candidate types have no label in `[λ_ξ, λ_ξ + ω)`, so (R4) fails at
`(x, D, γ)` for every `D` with a label `λ_ξ + i` and every `γ`.  Cover-hollow models are excluded
by the hypotheses of `StableCappedReceiving`, so this refutes nothing. -/
theorem not_stablyReceivesAt_of_isCoverHollow (hh : R.IsCoverHollow) {j : Fin D.card} {i : ℕ}
    (hj : D.label j = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})) (γ : Ordinal.{u}) :
    ¬ R.StablyReceivesAt hlaw x D γ := by
  rintro ⟨u, -, Q, hQ, hS, hl⟩
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hQ
  have hne : D.label j ≠ ⊤ := by
    rw [hj]
    exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
  set k : Fin (R.stableType hlaw u t ht).card := ⟨j, j.2.trans_eq (congrArg Scheme.card hS).symm⟩
  have h : R.stableSection u t k = ((blockStage ξ + i : Ordinal.{u}) : Label.{u}) :=
    ((hl k j rfl).1 hne).trans hj
  rw [congrFun (stableSection_eq_label_of_isCoverHollow hh ht) k] at h
  rcases t.atStage k with hlt | htop
  · rw [h] at hlt
    exact (Label.coe_le_coe_add (blockStage ξ) i).not_gt hlt
  · rw [h] at htop
    exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne htop

/-- **(R4) fails at bounded stable labels for every donor with a top cell**: if every stable label
of `R` at a cell labelled the formal top is at most `λ_ξ + K`, every label of the candidate is at
most `λ_ξ + K`, so (R4) fails at `(x, D, λ_ξ + K)` for every `D` with a cell labelled the formal
top.  Under top-grade supremum `⊤` the stable labels are unbounded
(`Realization.not_forall_stableLabel_le_of_topGradeSup_eq_top`), so `hK` is excluded by the
hypotheses of `StableCappedReceiving`, and this refutes nothing. -/
theorem not_stablyReceivesAt_of_stableLabel_le {K : ℕ}
    (hK : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤
        ((blockStage ξ + K : Ordinal.{u}) : Label.{u}))
    {j : Fin D.card} (hj : D.label j = ⊤) : ¬ R.StablyReceivesAt hlaw x D (blockStage ξ + K) := by
  rintro ⟨u, -, Q, hQ, hS, hl⟩
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hQ
  set k : Fin (R.stableType hlaw u t ht).card := ⟨j, j.2.trans_eq (congrArg Scheme.card hS).symm⟩
  have h : ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) < R.stableSection u t k :=
    (hl k j rfl).2 hj
  refine h.not_ge ?_
  by_cases hd : t.label k = ⊤
  · rw [stableSection_of_eq_top hd]
    exact hK u t ht k hd
  · rw [stableSection_of_ne_top hd]
    exact ((t.atStage k).resolve_right hd).le.trans (Label.coe_le_coe_add _ K)

/-- **Unbounded growth excludes bounded stable labels**: for a stably lawful `R` with top-grade
supremum `⊤`, the stable labels at the cells labelled the formal top are not all at most
`λ_ξ + K`, since some label of the candidate exceeds `λ_ξ + K`
(`Realization.exists_lt_stableCandidate_label`).  So the hypothesis of
`Realization.not_stablyReceivesAt_of_stableLabel_le` is excluded by those of
`StableCappedReceiving`. -/
theorem not_forall_stableLabel_le_of_topGradeSup_eq_top (hgrow : R.topGradeSup = ⊤)
    (hlaw : R.IsStablyLawful) (K : ℕ) :
    ¬ ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤
        ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) := by
  intro hK
  obtain ⟨⟨n, u, T, hT⟩, a, ha⟩ := exists_lt_stableCandidate_label hgrow hlaw K
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hT
  -- the label of the stable type at `a` is the stable section there
  change ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) < R.stableSection u t a at ha
  refine ha.not_ge ?_
  by_cases hd : t.label a = ⊤
  · rw [stableSection_of_eq_top hd]
    exact hK u t ht a hd
  · rw [stableSection_of_ne_top hd]
    exact ((t.atStage a).resolve_right hd).le.trans (Label.coe_le_coe_add _ K)

/-! ### Donors without new top cells -/

/-- **Exact receiving of a donor without new top cells**, conditional on finite-cut receiving of
`R` ((R1) for `R`): in an exactly consistent covering `R` with finite-cut receiving, if every cell
of the coface `D` reducing to the top at `λ_ξ` is visible through the face of `x`, some point
extends `x` to a tuple whose candidate type is `D`. -/
theorem exists_stableCandidate_eval_eq_of_hasFiniteCutReceiving (hR : R.IsConsistent)
    (hc : R.IsCovering) (hrec : R.HasFiniteCutReceiving) (hD : D ∈ x.type.cofaces)
    (hnew : ∀ d : Fin D.card, (D.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤ →
      d ∈ D.toScheme.visibleCells Fin.castSuccEmb) :
    ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
      (R.stableCandidate hlaw).eval u = some D := by
  obtain ⟨t, ht, -⟩ := exists_eq_stableType_of_stableCandidate_eval x.eval_tuple
  have hd := reduce_mem_cofaces ht hD
  obtain ⟨c, hcut, hDc, hγc⟩ := exists_isPermittedCutoff_capped (isSuccLimit_blockStage ξ)
    (D.reduce (isSuccPrelimit_blockStage ξ)) (isSuccLimit_blockStage ξ).bot_lt
  obtain ⟨u, hu, q, hq, hqe⟩ := hrec ⟨x.arity, x.tuple, t, ht⟩ _ hd c hcut
  have hqt : restrictFace Fin.castSuccEmb q = some t := by
    rw [← hR u q _ hqe, hu]
    exact ht
  obtain rfl : q = D.reduce (isSuccPrelimit_blockStage ξ) := by
    refine StageType.ext hq.1 fun i j hij ↦ ?_
    by_cases hj : (D.reduce (isSuccPrelimit_blockStage ξ)).label j = ⊤
    · exact label_eq_of_mem_visibleCells hq.1 hqt hd.2 hij (hnew j hj)
    · exact (capped_of_mem_receivingFamily hq hDc hγc i j hij).1 hj
  refine ⟨u, hu, (stableCandidate_eval_of_eval hqe).trans
    (congrArg some (StageType.ext rfl fun i j hij ↦ ?_))⟩
  obtain rfl : i = j := Fin.ext hij
  by_cases hj : (D.reduce (isSuccPrelimit_blockStage ξ)).label i = ⊤
  · exact stableType_label_eq_of_mem_visibleCells hR hc hD hu hqe (hnew i hj)
  · have e : R.stableSection u (D.reduce (isSuccPrelimit_blockStage ξ)) i =
        (D.reduce (isSuccPrelimit_blockStage ξ)).label i := stableSection_of_ne_top hj
    have hlt' : D.label i < (blockStage ξ : Label.{u}) := by
      by_contra hge
      exact hj (Label.reduce_of_le (not_lt.mp hge))
    exact e.trans (Label.reduce_of_lt hlt')

/-! ### (R4) at a model as finite-cut receiving of its candidate -/

/-- **Finite-cut receiving of the candidate gives (R4)** at every occurrence, every coface and
every `γ < λ_{ξ+1}`: one cutoff above `γ` and above every label of `D` other than the formal top. -/
theorem stablyReceivesAt_of_hasFiniteCutReceiving
    (hr : (R.stableCandidate hlaw).HasFiniteCutReceiving) (hD : D ∈ x.type.cofaces)
    (hγ : γ < blockStage (ξ + 1)) : R.StablyReceivesAt hlaw x D γ := by
  obtain ⟨c, hc, hDc, hγc⟩ := exists_isPermittedCutoff_capped (isSuccLimit_blockStage (ξ + 1)) D hγ
  obtain ⟨u, hu, Q, hQ, hQe⟩ := hr x D hD c hc
  exact ⟨u, hu, Q, hQe, hQ.1, capped_of_mem_receivingFamily hQ hDc hγc⟩

/-- **(R4) at a model is finite-cut receiving of its candidate**: for a model `R`, given the
amalgam over the empty face at `λ_{ξ+1}`, (R4) at every occurrence of the candidate of positive
arity, every coface and every `γ < λ_{ξ+1}` is equivalent to finite-cut receiving of the
candidate. -/
theorem forall_stablyReceivesAt_iff_hasFiniteCutReceiving (hR : R.IsModel)
    (hamal : ∀ ⦃n : ℕ⦄ (P : StageType.{u} (blockStage (ξ + 1)) n)
      (d : StageType.{u} (blockStage (ξ + 1)) 1), P.IsLegal → d.IsLegal →
        ∃ Q ∈ P.cofaces, restrictFace (Fin.natAddEmb n) Q = some d) :
    (∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, 0 < x.arity →
      ∀ D ∈ x.type.cofaces, ∀ γ < blockStage (ξ + 1),
        R.StablyReceivesAt hR.isStablyLawful x D γ) ↔
      (R.stableCandidate hR.isStablyLawful).HasFiniteCutReceiving := by
  refine ⟨fun h ↦ hasFiniteCutReceiving_of_pos hR.nonempty
    (hasLegalTypes_stableCandidate hR.hasLegalTypes)
    (isConsistent_stableCandidate hR.isConsistent hR.isCovering)
    (isCovering_stableCandidate hR.isCovering) hamal fun x hx D hD c hc ↦ ?_,
    fun hr x _ D hD γ hγ ↦ stablyReceivesAt_of_hasFiniteCutReceiving hr hD hγ⟩
  induction c using Label.recBotCoeTop with
  | bot => exact absurd hc not_isPermittedCutoff_bot
  | top => exact absurd hc not_isPermittedCutoff_top
  | coe γ =>
    obtain ⟨u, hu, Q, hQ, hS, hl⟩ := h x hx D hD γ (isPermittedCutoff_coe.mp hc)
    exact ⟨u, hu, Q, mem_receivingFamily_of_capped hS hl, hQ⟩

/-! ### Models with a model expansion -/

/-- **A model expansion is the candidate**, conditional on forcing donors at `ξ` (still to be
proved) and on finite-extension receiving of the expansion (from (R1), still to be proved): an
exactly consistent realization `R'` at `λ_{ξ+1}` with legal types and reduction `R` is the stable
candidate of `R` (normalization, `Realization.label_eq_stableLabel`). -/
theorem eq_stableCandidate_of_reduce_eq (hF : ForcingDonors.{u} ξ)
    {R' : Realization.{u, v} (blockStage (ξ + 1)) M} (hR' : R'.IsConsistent)
    (hl' : R'.HasLegalTypes) (hrec' : R'.HasFiniteExtensionReceiving)
    (h : R'.reduce (isSuccPrelimit_blockStage ξ) = R) : R' = R.stableCandidate hlaw := by
  subst h
  refine Realization.ext fun u ↦ ?_
  cases hT : R'.eval u with
  | none =>
    refine (stableCandidate_eval_eq_none_iff.mpr ?_).symm
    rw [reduce_eval, hT, Option.map_none]
  | some T =>
    have hTu : (R'.reduce (isSuccPrelimit_blockStage ξ)).eval u =
        some (T.reduce (isSuccPrelimit_blockStage ξ)) := by
      rw [reduce_eval, hT, Option.map_some]
    rw [stableCandidate_eval_of_eval hTu]
    have heq : (R'.reduce (isSuccPrelimit_blockStage ξ)).stableSection u
        (T.reduce (isSuccPrelimit_blockStage ξ)) = T.label := funext fun d ↦ by
      by_cases hd : (T.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤
      · rw [stableSection_of_eq_top hd]
        exact (label_eq_stableLabel hR' hl' hrec' hF (covers_of_eval u hT) d hd).symm
      · rw [stableSection_of_ne_top hd]
        have hlt : Label.reduce (blockStage ξ) (T.label d) < blockStage ξ :=
          ((T.reduce _).atStage d).resolve_right hd
        exact Label.reduce_of_lt (Label.reduce_lt_iff.mp hlt)
    refine congrArg some (StageType.ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    exact (congrFun heq i).symm

/-- **(R4) at a model with a model expansion**, conditional on forcing donors at `ξ` (still to be
proved): if `R` is the reduction of an exactly consistent realization `R'` at `λ_{ξ+1}` with legal
types and finite-cut receiving, then (R4) holds at every occurrence of the candidate of `R`, every
coface and every `γ < λ_{ξ+1}`.  Non-hollowness and unbounded growth are not used.  This is derived
from the expansion `R'` and cannot be used to construct it. -/
theorem stablyReceivesAt_of_reduce_eq (hF : ForcingDonors.{u} ξ)
    {R' : Realization.{u, v} (blockStage (ξ + 1)) M} (hR' : R'.IsConsistent)
    (hl' : R'.HasLegalTypes) (hrec' : R'.HasFiniteCutReceiving)
    (h : R'.reduce (isSuccPrelimit_blockStage ξ) = R) (hD : D ∈ x.type.cofaces)
    (hγ : γ < blockStage (ξ + 1)) : R.StablyReceivesAt hlaw x D γ := by
  have heq := eq_stableCandidate_of_reduce_eq (hlaw := hlaw) hF hR' hl'
    (HasFiniteCutReceiving.hasFiniteExtensionReceiving hrec' hR'
      (isSuccPrelimit_blockStage (ξ + 1))) h
  exact stablyReceivesAt_of_hasFiniteCutReceiving (heq ▸ hrec') hD hγ

/-! ### The evaluation step -/

/-- **The evaluation step of (R4)**: for a model `R`, if an occurrence `w` of `R` contains the
tuple of `x` along `f` and `E` is a stable recovery scheme for the stable type of `w`, `f`, `D` and
`γ`, then (R4) holds at `(x, D, γ)`.  Generalized saturation realizes `E` over `w`; the candidate
type of the realized tuple has face the stable type of `w`, and its face along `f` followed by the
new point is the candidate type of the received tuple. -/
theorem stablyReceivesAt_of_isStableRecoveryScheme (hR : R.IsModel) (w : R.Occurrence)
    {f : Fin x.arity ↪ Fin w.arity} (hf : f.trans w.tuple = x.tuple) {E : Scheme.{u} (w.arity + 1)}
    (hE : (R.stableType hlaw w.tuple w.type w.eval_tuple).IsStableRecoveryScheme f D γ E) :
    R.StablyReceivesAt hlaw x D γ := by
  obtain ⟨⟨q, hq, hqE⟩, hrec⟩ := hE
  rw [reduce_stableType] at hq
  obtain ⟨v, hv, q', hq'E, hvq⟩ := hR.saturation w E ⟨q, hq, hqE⟩
  have hcons := isConsistent_stableCandidate (hlaw := hlaw) hR.isConsistent hR.isCovering
  have hQ'v := stableCandidate_eval_of_eval (hlaw := hlaw) hvq
  have hface : restrictFace Fin.castSuccEmb (R.stableType hlaw v q' hvq) =
      some (R.stableType hlaw w.tuple w.type w.eval_tuple) := by
    rw [← hcons v _ Fin.castSuccEmb hQ'v, hv]
    exact stableCandidate_eval_of_eval w.eval_tuple
  obtain ⟨Q, hQ, hS, hl⟩ := hrec (R.stableType hlaw v q' hvq) hq'E hface
  refine ⟨(extendByLast f).trans v, ?_, Q, ?_, hS, hl⟩
  · rw [← hf, ← hv, ← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc]
  · rw [hcons v _ _ hQ'v, hQ]

/-! ### The reduction of (R4) to acquisition and a finite construction -/

variable (ξ) in
/-- **Acquisition of calibrated contexts** for a calibration `C`, a statement about one model,
open: over every occurrence `x` of the candidate of positive arity, for every coface `D` of its
type and every `γ < λ_{ξ+1}`, some occurrence `w` of `R` contains the tuple of `x` along some `f`
and its stable type satisfies `C` for `f`, `D` and `γ`. -/
def AcquiresCalibratedContexts
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop)
    (R : Realization.{u, v} (blockStage ξ) M) (hlaw : R.IsStablyLawful) : Prop :=
  ∀ x : (R.stableCandidate hlaw).Occurrence, 0 < x.arity → ∀ D ∈ x.type.cofaces,
    ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      ∃ (w : R.Occurrence) (f : Fin x.arity ↪ Fin w.arity), f.trans w.tuple = x.tuple ∧
        C (R.stableType hlaw w.tuple w.type w.eval_tuple) f D γ

/-- **(R4) at a model from acquisition and stable recovery schemes**: for a model `R` and a
calibration `C`, acquisition of calibrated contexts in `R` and stable recovery schemes for `C`
give (R4) at every occurrence of the candidate of positive arity, every coface and every
`γ < λ_{ξ+1}`. -/
theorem stablyReceivesAt_of_acquiresCalibratedContexts {C : ∀ ⦃m k : ℕ⦄,
      StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
        StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (hR : R.IsModel) (hS : StageType.HasStableRecoverySchemes ξ C)
    (hA : AcquiresCalibratedContexts ξ C R hR.isStablyLawful)
    (x : (R.stableCandidate hR.isStablyLawful).Occurrence) (hx : 0 < x.arity)
    (D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)) (hD : D ∈ x.type.cofaces)
    (γ : Ordinal.{u}) (hγ : γ < blockStage (ξ + 1)) :
    R.StablyReceivesAt hR.isStablyLawful x D γ := by
  obtain ⟨w, f, hf, hC⟩ := hA x hx D hD γ hγ
  have hface : restrictFace f (R.stableType hR.isStablyLawful w.tuple w.type w.eval_tuple) =
      some x.type := by
    rw [← isConsistent_stableCandidate hR.isConsistent hR.isCovering w.tuple _ f
      (stableCandidate_eval_of_eval w.eval_tuple), hf]
    exact x.eval_tuple
  obtain ⟨E, hE⟩ := hS _ f x.type (hR.hasLegalTypes w.tuple w.type w.eval_tuple) hx hface D hD γ
    hγ hC
  exact stablyReceivesAt_of_isStableRecoveryScheme hR w hf hE

/-- **Acquisition of the marker and cap calibration**: a model `R` at `λ_ξ` that is not
cover-hollow and has top-grade supremum `⊤` acquires calibrated contexts for the marker and cap
calibration.  Over an occurrence `x` of the candidate and for `γ ≤ λ_ξ + K`, non-hollowness gives
an occurrence of the candidate with a label `λ_ξ + i`
(`Realization.exists_stableCandidate_label_eq_coe_add`), unbounded growth one with a label above
`λ_ξ + K` (`Realization.exists_lt_stableCandidate_label`), covering one occurrence `w` of `R`
containing the three tuples, and exact consistency of the candidate carries both labels to the
stable type of `w`. -/
theorem IsModel.acquiresCalibratedContexts_markerCap (hR : R.IsModel) (hnh : ¬ R.IsCoverHollow)
    (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (StageType.MarkerCapCalibration ξ) R hR.isStablyLawful := by
  classical
  intro x _ D _ γ hγ
  obtain ⟨K, hK⟩ := exists_le_blockStage_add_natCast hγ
  obtain ⟨z₀, a, i, ha⟩ := exists_stableCandidate_label_eq_coe_add hnh hR.isStablyLawful
  obtain ⟨z₁, b, hb⟩ := exists_lt_stableCandidate_label hgrow hR.isStablyLawful K
  obtain ⟨w, hw⟩ := hR.isCovering.exists_subset_support
    (univ.map x.tuple ∪ univ.map z₀.tuple ∪ univ.map z₁.tuple)
  obtain ⟨f, hf⟩ := w.exists_trans_eq (subset_union_left.trans (subset_union_left.trans hw))
  obtain ⟨f₀, hf₀⟩ := w.exists_trans_eq (subset_union_right.trans (subset_union_left.trans hw))
  obtain ⟨f₁, hf₁⟩ := w.exists_trans_eq (subset_union_right.trans hw)
  have hcons := isConsistent_stableCandidate (hlaw := hR.isStablyLawful) hR.isConsistent
    hR.isCovering
  let W : (R.stableCandidate hR.isStablyLawful).Occurrence :=
    ⟨w.arity, w.tuple, _, stableCandidate_eval_of_eval w.eval_tuple⟩
  obtain ⟨a', ha'⟩ := Occurrence.exists_label_eq_of_trans_eq hcons (y := W) hf₀ a
  obtain ⟨b', hb'⟩ := Occurrence.exists_label_eq_of_trans_eq hcons (y := W) hf₁ b
  refine ⟨w, f, hf, ⟨a', i, ha'.trans ha⟩, b', ?_, ?_⟩
  · exact lt_of_le_of_lt (by exact_mod_cast hK) (hb.trans_eq hb'.symm)
  · exact (Label.coe_le_coe_add _ K).trans (hb.trans_eq hb'.symm).le

end Realization

/-! ### (R4) as the conjunction of its occurrences -/

/-- **(R4) is (R4) at every occurrence**: `StableCappedReceiving` is `Realization.StablyReceivesAt`
at every occurrence of positive arity of the candidate of every model at `λ_ξ`, `ξ < ω₁`, that is
not cover-hollow and has top-grade supremum `⊤`, every coface and every `γ < λ_{ξ+1}`. -/
theorem stableCappedReceiving_iff_forall_stablyReceivesAt :
    StableCappedReceiving.{w} ↔
      ∀ ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M),
        ξ < ω₁ → ∀ hR : R.IsModel, ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
          ∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, 0 < x.arity →
            ∀ D ∈ x.type.cofaces, ∀ γ : Ordinal.{0}, γ < blockStage (ξ + 1) →
              R.StablyReceivesAt hR.isStablyLawful x D γ :=
  ⟨fun h ↦ h.receive, fun h ↦ ⟨h⟩⟩

/-- **Stable recovery contexts** on the carriers in the universe `w`, open: for every `ξ < ω₁`
there is a calibration `C` with stable recovery schemes at `ξ` that every model at `λ_ξ` which is
not cover-hollow and has top-grade supremum `⊤` acquires. -/
structure StableRecoveryContexts : Prop where
  /-- The calibration at `ξ`, with its stable recovery schemes and its acquisition. -/
  exists_calibration ⦃ξ : Ordinal.{0}⦄ : ξ < ω₁ →
    ∃ C : ∀ ⦃m k : ℕ⦄, StageType.{0} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
        StageType.{0} (blockStage (ξ + 1)) (k + 1) → Ordinal.{0} → Prop,
      StageType.HasStableRecoverySchemes ξ C ∧
        ∀ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) (hR : R.IsModel),
          ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
            Realization.AcquiresCalibratedContexts ξ C R hR.isStablyLawful

/-- **(R4) from stable recovery contexts**: acquisition of calibrated contexts and stable recovery
schemes, for one calibration at each `ξ < ω₁`, give (R4).  The evaluation step is
`Realization.stablyReceivesAt_of_isStableRecoveryScheme`. -/
theorem StableCappedReceiving.of_stableRecoveryContexts (h : StableRecoveryContexts.{w}) :
    StableCappedReceiving.{w} :=
  stableCappedReceiving_iff_forall_stablyReceivesAt.mpr fun _ _ R hξ hR hnh hgrow x hx D hD γ hγ ↦
    have ⟨_, hS, hA⟩ := h.exists_calibration hξ
    Realization.stablyReceivesAt_of_acquiresCalibratedContexts hR hS (hA R hR hnh hgrow) x hx D
      hD γ hγ

/-- **(R4) from one finite statement**: stable recovery schemes for the marker and cap calibration
at every `ξ < ω₁`, a finite statement about stage types, give (R4); the acquisition is proved
(`Realization.IsModel.acquiresCalibratedContexts_markerCap`).  The hypothesis is false
(`Continuation.StableRecoveryCounterexample.not_forall_hasStableRecoverySchemes_markerCap`). -/
theorem StableCappedReceiving.of_hasStableRecoverySchemes_markerCap
    (h : ∀ ξ < ω₁,
      StageType.HasStableRecoverySchemes.{0} ξ (StageType.MarkerCapCalibration.{0} ξ)) :
    StableCappedReceiving.{w} :=
  StableCappedReceiving.of_stableRecoveryContexts ⟨fun ξ hξ ↦ ⟨_, h ξ hξ,
    fun _ _ hR hnh hgrow ↦ Realization.IsModel.acquiresCalibratedContexts_markerCap hR hnh hgrow⟩⟩

end VaughtConjecture

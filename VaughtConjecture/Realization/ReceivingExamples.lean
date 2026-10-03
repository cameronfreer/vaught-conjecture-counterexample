/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Language.Density
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Receiving

/-!
# Examples for receiving for finite extensions

Special cases of `VaughtConjecture.Realization.Receiving`:

* **the one-point case**: finite-extension receiving gives back finite-cut receiving, and a donor
  on one new point along the initial segment is one step of the chain;
* **two new points**: a type on two more points whose face is not the received type is not a
  coface of it, so the next step needs the repaired donor, which exists; the cutoff `0` at stage
  `ω` and the cutoffs of the transfer, the block stages `λ_η = ω + ω · η`, are self-visible at no
  positive arity, so they cannot serve as repair caps, and the auxiliary cap at the first block
  stage is `ω + 3`;
* **a non-closed intermediate face**: in the interval plan on three points the pair `{0, 2}` is not
  a closed face while `{0, 1}` is, and under exact consistency a tuple on a non-closed face of an
  occurrence is untyped, so the points must be added along closed faces;
* **the empty root**: every legal donor is received over a typed empty tuple;
* **descent along stage reduction**: receiving at a limit stage `α ≥ ω` descends to the reduction
  to `ω`, cutoff by cutoff; the reduction to stage `0` has no permitted cutoff;
* **stage `ω`**: every structure satisfying the density sentence has finite-extension receiving,
  unconditionally.

The global forms, for models at countable limit stages, are in
`VaughtConjecture.Expansion.AgreementExamples`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Realization

open Finset Label StageType

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-! ### The one-point case -/

/-- Finite-cut receiving, through finite-extension receiving, gives back finite-cut receiving. -/
example (h : R.HasFiniteCutReceiving) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α) :
    R.HasFiniteCutReceiving :=
  (h.hasFiniteExtensionReceiving hR hα).hasFiniteCutReceiving

/-- The two forms of receiving agree for an exactly consistent realization at a limit stage. -/
example (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α) :
    R.HasFiniteExtensionReceiving ↔ R.HasFiniteCutReceiving :=
  hasFiniteExtensionReceiving_iff hR hα

/-- A donor on one new point along the initial segment, at a cap self-visible at `n + 1`: one
repair, one receiving step, and the trivial final reindexing. -/
example (h : R.HasFiniteCutReceiving) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α)
    {n : ℕ} {t : Fin n ↪ M} {p : StageType.{u} α n} (ht : R.eval t = some p)
    {D : StageType.{u} α (n + 1)} (hD : D ∈ p.cofaces) {c : Label.{u}}
    (hc : IsPermittedCutoff α c) (hcv : IsSelfVisible (n + 1) c) :
    ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧
      ∃ q ∈ receivingFamily D c, R.eval u = some q :=
  h.exists_extend_of_mem_receivingFamily hR hα hD.1 hc hcv ht hD.2 (self_mem_receivingFamily p c)

/-! ### Two new points: the repair and the auxiliary cap -/

/-- **The naive step fails**: if the received type `q₁` is not the face `D₁` of the donor `D`
along the initial segment, `D` is not a coface of `q₁`. -/
example {n : ℕ} {D : StageType.{u} α (n + 2)} {D₁ q₁ : StageType.{u} α (n + 1)}
    (h : restrictFace Fin.castSuccEmb D = some D₁) (hne : q₁ ≠ D₁) : D ∉ q₁.cofaces :=
  fun hD ↦ hne (Option.some_injective _ (hD.2.symm.trans h))

/-- **The repaired coface exists**: a received type `q₁` that agrees with the face `D₁` of a legal
`D` at a cap `c ≤ α` self-visible at `n + 2` has a coface that agrees with `D` at `c`. -/
example (hα : Order.IsSuccPrelimit α) {n : ℕ} {D : StageType.{u} α (n + 2)}
    {D₁ q₁ : StageType.{u} α (n + 1)} (hD : D.IsLegal)
    (h : restrictFace Fin.castSuccEmb D = some D₁) {c : Label.{u}} (hc : IsSelfVisible (n + 2) c)
    (hcα : c ≤ α) (hq₁ : q₁ ∈ receivingFamily D₁ c) :
    (q₁.cofaces ∩ receivingFamily D c).Nonempty :=
  let ⟨d, hd, hdq, hdD⟩ := exists_restrictFace_eq_mem_receivingFamily hα hD h hc hcα hq₁
  ⟨d, ⟨hd, hdq⟩, hdD⟩

/-- The cutoff `0` of stage `ω` is not self-visible at arity `1`, so it is no repair cap. -/
example : ¬ IsSelfVisible 1 (0 : Label.{0}) := by
  simp

/-- The block stages `λ_η = ω + ω · η`, the cutoffs of the transfer, are self-visible at no
positive arity: their finite part is `0`. -/
example (η : Ordinal.{0}) {k : ℕ} (hk : 0 < k) :
    ¬ IsSelfVisible k ((blockStage η : Ordinal.{0}) : Label.{0}) := by
  rw [isSelfVisible_coe, blockStage_eq_mul,
    Ordinal.mod_eq_zero_of_dvd (dvd_mul_right Ordinal.omega0 _)]
  exact_mod_cast hk.not_ge

/-- **The auxiliary cap at the first block stage**: for the cutoff `λ_0 = ω` at the stage
`λ_1 = ω · 2` and a donor on two points, `ω + 3` lies strictly between them and is self-visible
at `2`. -/
example : Ordinal.omega0 < Ordinal.omega0 + 3 ∧ Ordinal.omega0 + 3 < blockStage (1 : Ordinal.{0}) ∧
    IsSelfVisible 2 (((Ordinal.omega0 + 3 : Ordinal.{0})) : Label.{0}) := by
  refine ⟨lt_add_of_pos_right _ (by simp), ?_,
    isSelfVisible_coe_add (K := 3) Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega)⟩
  rw [blockStage, mul_one]
  exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 3)

/-! ### A non-closed intermediate face -/

/-- In the interval plan on three points, the pair `{0, 2}` is not a closed face. -/
example : ({0, 2} : Finset (Fin 3)) ∉ Geometry.intervalPlan (univ : Finset (Fin 3)) := by
  decide

/-- In the interval plan on three points, adding `1` to `{0}` gives a closed face. -/
example : insert (1 : Fin 3) {0} ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) := by
  decide

/-- Under exact consistency, a tuple on a face of an occurrence that is not closed is untyped:
no receiving step produces it, so the chain adds points along closed faces of the donor's plan. -/
example (hR : R.IsConsistent) (x : R.Occurrence) {m : ℕ} (f : Fin m ↪ Fin x.arity)
    (hf : univ.map f ∉ x.type.toCellScheme.faces) : R.eval (f.trans x.tuple) = none :=
  Option.not_isSome_iff_eq_none.mp fun h ↦ hf ((isSome_eval_face_iff hR x f).mp h)

/-! ### The empty root -/

/-- **The empty root**: in an exactly consistent realization with finite-cut receiving at a stage
that is zero or a limit, every legal stage type is received over a typed empty tuple at every
permitted cutoff.  Its face on no points is always defined, and equal to the type of the root. -/
example (h : R.HasFiniteCutReceiving) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α)
    {t : Fin 0 ↪ M} {p : StageType.{u} α 0} (ht : R.eval t = some p) {m : ℕ}
    {D : StageType.{u} α m} (hD : D.IsLegal) (g : Fin 0 ↪ Fin m) {c : Label.{u}}
    (hc : IsPermittedCutoff α c) :
    ∃ u : Fin m ↪ M, ∃ q ∈ receivingFamily D c, R.eval u = some q := by
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (D.isSome_restrictFace_of_zero g)
  obtain ⟨u, -, q, hq, hu⟩ := h.hasFiniteExtensionReceiving hR hα t p ht D g hD
    (hp'.trans (congrArg some (eq_of_zero p' p))) c hc
  exact ⟨u, q, hq, hu⟩

/-! ### Descent along stage reduction -/

/-- **Descent to `ω`**: the reduction to `ω` of a realization with finite-cut receiving at a limit
stage `α ≥ ω` has finite-cut receiving, cutoff by cutoff. -/
example (h : R.HasFiniteCutReceiving) (hα : Order.IsSuccPrelimit α) (hωα : Ordinal.omega0 ≤ α) :
    (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).HasFiniteCutReceiving :=
  h.reduce hα _ hωα

/-- **Descent to `ω`, several new points**: the reduction is exactly consistent as well, so it has
finite-extension receiving. -/
example (h : R.HasFiniteCutReceiving) (hR : R.IsConsistent) (hα : Order.IsSuccPrelimit α)
    (hωα : Ordinal.omega0 ≤ α) :
    (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).HasFiniteExtensionReceiving :=
  (h.reduce hα _ hωα).hasFiniteExtensionReceiving (hR.reduce _)
    Ordinal.isSuccLimit_omega0.isSuccPrelimit

/-- **Stage `0`**: there is no permitted cutoff at stage `0`, so the reduction of every realization
to stage `0` has finite-cut receiving, vacuously. -/
example : (R.reduce Ordinal.isSuccPrelimit_zero).HasFiniteCutReceiving := fun _ _ _ c hc ↦ by
  obtain ⟨δ, hδ, -⟩ := isPermittedCutoff_iff.mp hc
  exact (not_lt_zero hδ).elim

end VaughtConjecture.Realization

/-! ### Stage `ω` -/

namespace VaughtConjecture.baseLanguage

universe u' v'

/-- **Finite-extension receiving at stage `ω`, unconditionally**: every structure satisfying the
density sentence has finite-extension receiving.  The density sentence states finite-cut
receiving and exact consistency, and `ω` is a limit. -/
example {M : Type v'} [baseLanguage.{u'}.Structure M] (h : densitySentence.Realize M) :
    (toRealization M).HasFiniteExtensionReceiving := by
  obtain ⟨-, -, hcons, -, hr⟩ := (realize_densitySentence_iff M).mp h
  exact hr.hasFiniteExtensionReceiving hcons Ordinal.isSuccLimit_omega0.isSuccPrelimit

end VaughtConjecture.baseLanguage

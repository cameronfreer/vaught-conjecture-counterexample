/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecovery
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.Expansion.ReceivingModels
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem

/-!
# Cutoff stable recovery: (R4) for receiving models through the model's own receiving

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.2–3.4 ((R4) of the table of Layer 3); semantic contract, item 8.

(R4) for receiving models (`Expansion.ReceivingStableCappedReceiving`) is asked only of models `R`
with the finite-cut receiving property.  In the evaluation step of (R4)
(`Realization.stablyReceivesAt_of_isStableRecoveryScheme`) a coface of `T⁺↓λ_ξ` is realized over
an occurrence `w` by generalized saturation, so recovery is asked of every stage type at
`λ_{ξ+1}` on the scheme with face `T⁺`.  Realizing it instead by the receiving of `R`, at a
permitted cutoff `δ`, the candidate type `Q'` of the realized tuple has face `T⁺` and its reduction
`Q'↓λ_ξ` lies in the receiving family of the realized coface at `δ`.  So recovery is needed only
for those `Q'`.  Each item below is compiled in this repository (theorem named), unless marked
otherwise.

**Cutoff stable recovery** (`StageType.IsCutoffStableRecovery`): a coface `q` of `T⁺↓λ_ξ` and a
permitted cutoff `δ` such that every stage type `Q'` at `λ_{ξ+1}` with face `T⁺` and with `Q'↓λ_ξ`
in the receiving family of `q` at `δ` has, along `f` followed by the new point, a face equal to `D`
off the formal top and above `γ` at the formal top.  `StageType.HasCutoffStableRecoverySchemes ξ C`
(open for the calibrations of interest) asks for one at every input of the calibration `C`: for
every input, one `(q, δ)` is chosen, and then recovery is asked of every `Q'` in the class.  A
stable recovery scheme gives cutoff stable recovery at every permitted cutoff
(`StageType.IsStableRecoveryScheme.exists_isCutoffStableRecovery`,
`StageType.HasStableRecoverySchemes.hasCutoffStableRecoverySchemes`); no converse is claimed.

**The evaluation step and the composition**
(`Realization.stablyReceivesAt_of_isCutoffStableRecovery`,
`Realization.stablyReceivesAt_of_acquiresCalibratedContexts_of_hasFiniteCutReceiving`,
`Expansion.ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes`,
`Expansion.ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes_gradedCap`).  In a
model with finite-cut receiving, acquisition of calibrated contexts and cutoff stable recovery give
(R4) at every occurrence.  For the graded cap calibration the acquisition is compiled
(`Realization.IsModel.acquiresCalibratedContexts_gradedCap`), so (R4) for receiving models follows
from cutoff stable recovery for the graded cap calibration at every `ξ < ω₁`.

**The calibration margin** (`StageType.GradedCapMarginCalibration`,
`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`).  The graded cap calibration
gives a cap of grade `N` with `γ < λ_ξ + N`.  A reading of the new formal-top cells of `D` through
a marker labelled `λ_ξ + i` at an offset `R` below the grade of the cap gives values at least
`λ_ξ + R`, which exceed `γ` only if `γ < λ_ξ + R` (argued here; no such reading is compiled in
this module).  The margin calibration adds to the graded cap calibration, for the same cap:
* (M1) an offset `R < N` with `γ < λ_ξ + R`;
* (M2) a **marker in the block of `λ_ξ`**: a cell labelled `λ_ξ + i` with `i < N` and of grade at
  most `N`, whether or not `D` has a label in that block (the reference clause gives one only when
  it has).
Its acquisition is compiled, in every model that is not cover-hollow and has unbounded growth,
from the argument of `Realization.IsModel.acquiresCalibratedContexts_gradedCap`: there the marker
of non-hollowness is acquired with `i < N` and grade at most `N`, and the grade `N` of the cap
exceeds `K + |x|` for `γ ≤ λ_ξ + K`, so `R = K + 1` works.  So (R4) for receiving models follows
from cutoff stable recovery for the margin calibration
(`Expansion.ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes_gradedCapMargin`),
whose inputs are among those of the graded cap calibration
(`StageType.GradedCapMarginCalibration.gradedCapCalibration`).

**The semantic coatom completion** (`StageType.HasCutoffCoatomCompletions`, a statement about stage
types, open; `StageType.HasCutoffCoatomCompletions.hasCutoffStableRecoverySchemes`).  For a legal
`T⁺` on `m + 1` points, a closed coatom `g` of `T⁺` with face `p`, a legal coface `tb` of `p`, and a
donor `D` that is the face of `tb` along `f` followed by the new point, it asks for a coface `q` of
`T⁺↓λ_ξ` with face `tb↓λ_ξ` along `g` followed by the new point (a completion of the reduced
coatom pair) and a permitted cutoff `δ` with cutoff stable recovery for `T⁺`, `f.trans g`, `D` and
`γ`.  For a calibration that forces a private point, the compiled coatom extension property at
`λ_{ξ+1}` (`StageType.hasCoatomExtensions`) and these completions give cutoff stable recovery: the
root lies in a closed coatom (`StageType.exists_coatom_trans_eq`), and the exact pinned extension
gives `tb` (`StageType.exists_pinned_extension`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label StageType
open Ordinal hiding univ

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-! ### Cutoff stable recovery -/

/-- **Cutoff stable recovery** for a stage type `T⁺` at `λ_{ξ+1}` on `m` points, an embedding `f`
of `k` points into them, a stage type `D` on `k + 1` points and an ordinal `γ`, carried by a stage
type `q` at `λ_ξ` on `m + 1` points and a label `δ`: `q` is a coface of `T⁺↓λ_ξ`, `δ` is a
permitted cutoff at `λ_ξ`, and every stage type `Q'` at `λ_{ξ+1}` whose face along the first `m`
points is `T⁺` and whose reduction to `λ_ξ` lies in the receiving family of `q` at `δ` has, along
`f` followed by the new point, a face `Q` on the scheme of `D` that equals `D` at every cell where
`D` is not the formal top and exceeds `γ` at every cell where `D` is the formal top. -/
def IsCutoffStableRecovery (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u})
    (q : StageType.{u} (blockStage ξ) (m + 1)) (δ : Label.{u}) : Prop :=
  q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces ∧ IsPermittedCutoff (blockStage ξ) δ ∧
    ∀ Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1),
      Q'.reduce (isSuccPrelimit_blockStage ξ) ∈ receivingFamily q δ →
      restrictFace Fin.castSuccEmb Q' = some Tp →
        ∃ Q, restrictFace (extendByLast f) Q' = some Q ∧ Q.toScheme = D.toScheme ∧
          ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
            (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
              (D.label j = ⊤ → (γ : Label.{u}) < Q.label i)

variable (ξ) in
/-- **Cutoff stable recovery for a calibration `C`**, a finite statement about stage types with no
realization: every input of `StageType.HasStableRecoverySchemes ξ C` has a carrier `(q, δ)` of
cutoff stable recovery.  The carrier is chosen for the input, before any stage type of the class.
Open for the calibrations of interest. -/
def HasCutoffStableRecoverySchemes
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      C Tp f D γ → ∃ (q : StageType.{u} (blockStage ξ) (m + 1)) (δ : Label.{u}),
        Tp.IsCutoffStableRecovery f D γ q δ

/-- **A stable recovery scheme gives cutoff stable recovery** at every permitted cutoff: the
coface of `T⁺↓λ_ξ` on the scheme carries it, since every stage type whose reduction lies in its
receiving family is on the scheme. -/
theorem IsStableRecoveryScheme.isCutoffStableRecovery {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {E : Scheme.{u} (m + 1)} (hE : Tp.IsStableRecoveryScheme f D γ E)
    {q : StageType.{u} (blockStage ξ) (m + 1)}
    (hq : q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces) (hqE : q.toScheme = E)
    {δ : Label.{u}} (hδ : IsPermittedCutoff (blockStage ξ) δ) :
    Tp.IsCutoffStableRecovery f D γ q δ :=
  ⟨hq, hδ, fun Q' hQ' hQ'T ↦ hE.2 Q' (hQ'.1.trans hqE) hQ'T⟩

/-- **A stable recovery scheme gives a carrier of cutoff stable recovery.** -/
theorem IsStableRecoveryScheme.exists_isCutoffStableRecovery
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {E : Scheme.{u} (m + 1)}
    (hE : Tp.IsStableRecoveryScheme f D γ E) :
    ∃ (q : StageType.{u} (blockStage ξ) (m + 1)) (δ : Label.{u}),
      Tp.IsCutoffStableRecovery f D γ q δ := by
  obtain ⟨q, hq, hqE⟩ := hE.1
  exact ⟨q, _, hE.isCutoffStableRecovery hq hqE
    (isPermittedCutoff_coe.mpr (isSuccLimit_blockStage ξ).bot_lt)⟩

/-- **Stable recovery schemes give cutoff stable recovery**, for every calibration. -/
theorem HasStableRecoverySchemes.hasCutoffStableRecoverySchemes
    {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (h : HasStableRecoverySchemes ξ C) : HasCutoffStableRecoverySchemes ξ C :=
  fun _ _ Tp f P hT hk hP D hD γ hγ hC ↦
    let ⟨_, hE⟩ := h Tp f P hT hk hP D hD γ hγ hC
    hE.exists_isCutoffStableRecovery

/-! ### The calibration margin -/

variable (ξ) in
/-- The **graded cap calibration with a margin**: the graded cap calibration
(`StageType.GradedCapCalibration`) with, for the same cap `b` of grade `N`, (M1) an offset `R < N`
with `γ < λ_ξ + R`, and (M2) a marker in the block of `λ_ξ`: a cell `a` labelled `λ_ξ + i` with
`i < N` and of grade at most `N`. -/
def GradedCapMarginCalibration ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (_ : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  ∃ b : Fin Tp.card,
    ((blockStage ξ + Tp.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤ Tp.label b ∧
    k < Tp.toCellScheme.grade b ∧
    (∃ R : ℕ, R < Tp.toCellScheme.grade b ∧ γ < blockStage ξ + R) ∧
    (∃ (a : Fin Tp.card) (i : ℕ), i < Tp.toCellScheme.grade b ∧
      Tp.toCellScheme.grade a ≤ Tp.toCellScheme.grade b ∧
      Tp.label a = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})) ∧
    ∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
      ∃ (μ : Ordinal.{u}) (n i : ℕ) (a : Fin Tp.card), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade a ≤ Tp.toCellScheme.grade b ∧
        Tp.label a = ((μ + i : Ordinal.{u}) : Label.{u})

/-- **The margin calibration is a graded cap calibration**: `γ < λ_ξ + R < λ_ξ + N`. -/
theorem GradedCapMarginCalibration.gradedCapCalibration
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibration ξ Tp f D γ) : GradedCapCalibration ξ Tp f D γ := by
  obtain ⟨b, hb, hk, ⟨R, hR, hγ⟩, -, href⟩ := h
  exact ⟨b, hb, hk, hγ.trans (add_lt_add_right (Nat.cast_lt.mpr hR) _), href⟩

/-! ### The semantic coatom completion -/

variable (ξ) in
/-- **Cutoff coatom completions for a calibration `C`** (a named statement; open): for every legal
`T⁺` at `λ_{ξ+1}` on `m + 1` points, closed coatom `g` of `T⁺` with face `p`, legal coface `tb` of
`p`, embedding `f` of `k > 0` points into the coatom with face `P` of `p`, coface `D` of `P` that is
the face of `tb` along `f` followed by the new point, and `γ < λ_{ξ+1}` with `C T⁺ (f.trans g) D γ`,
there are a coface `q` of `T⁺↓λ_ξ` whose face along `g` followed by the new point is `tb↓λ_ξ` and a
cutoff `δ` carrying cutoff stable recovery for `T⁺`, `f.trans g`, `D` and `γ`.  The carrier is
chosen for the input, before any stage type of the class; the intermediate coface `tb` is
arbitrary. -/
def HasCutoffCoatomCompletions
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (g : Fin m ↪ Fin (m + 1))
    (p : StageType.{u} (blockStage (ξ + 1)) m) (tb : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (f : Fin k ↪ Fin m) (P : StageType.{u} (blockStage (ξ + 1)) k),
    Tp.IsLegal → restrictFace g Tp = some p → tb ∈ p.cofaces → 0 < k →
    restrictFace f p = some P → ∀ D ∈ P.cofaces, restrictFace (extendByLast f) tb = some D →
      ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) → C Tp (f.trans g) D γ →
        ∃ (q : StageType.{u} (blockStage ξ) (m + 2)) (δ : Label.{u}),
          restrictFace (extendByLast g) q = some (tb.reduce (isSuccPrelimit_blockStage ξ)) ∧
            Tp.IsCutoffStableRecovery (f.trans g) D γ q δ

/-- **Cutoff stable recovery from cutoff coatom completions**, for a calibration `C` that forces a
private point (`hC`, as `StageType.GradedCapCalibration.lt` does).  A closed coatom `g` of `T⁺`
contains the root (`StageType.exists_coatom_trans_eq`); the exact pinned extension over the face of
`T⁺` along `g` (`StageType.exists_pinned_extension`, with the compiled coatom extension property
at `λ_{ξ+1}`) gives an intermediate coface `tb` with face `D`; the cutoff coatom completion of
`(T⁺, tb)` carries cutoff stable recovery. -/
theorem HasCutoffCoatomCompletions.hasCutoffStableRecoverySchemes
    {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (hC : ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
      (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}), C Tp f D γ → k < m)
    (h : HasCutoffCoatomCompletions ξ C) : HasCutoffStableRecoverySchemes ξ C := by
  intro m k Tp f P hT hk hP D hD γ hγ hCf
  have hkm : k < m := hC Tp f D γ hCf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfT : univ.map f ∈ Tp.toCellScheme.faces := ((restrictFace_eq_some_iff Tp f).mp hP).1
  obtain ⟨g, f', hg, rfl⟩ := Tp.exists_coatom_trans_eq f hfT (by omega)
  have hTp : restrictFace g Tp = some (Tp.comap g hg) := restrictFace_of_mem Tp g hg
  have hpP : restrictFace f' (Tp.comap g hg) = some P := (restrictFace_trans Tp g f' hTp).trans hP
  obtain ⟨tb, htb, htbp, htbD⟩ := exists_pinned_extension
    (hasCoatomExtensions (isSuccPrelimit_blockStage (ξ + 1))) (hT.restrictFace g hTp) hpP hD.1 hD.2
  obtain ⟨q, δ, -, hq⟩ := h Tp g _ tb f' P hT hTp ⟨htb, htbp⟩ hk hpP D hD htbD γ hγ hCf
  exact ⟨q, δ, hq⟩

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}
  {hlaw : R.IsStablyLawful} {x : (R.stableCandidate hlaw).Occurrence}
  {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)} {γ : Ordinal.{u}}

/-! ### The evaluation step through receiving -/

/-- **The evaluation step of (R4) through receiving**: for a model `R` with finite-cut receiving,
if an occurrence `w` of `R` contains the tuple of `x` along `f` and `(q, δ)` carries cutoff stable
recovery for the stable type of `w`, `f`, `D` and `γ`, then (R4) holds at `(x, D, γ)`.  The
receiving of `R` realizes a member of the receiving family of `q` at `δ` over `w`; the candidate
type of the realized tuple has face the stable type of `w` and reduces to that member. -/
theorem stablyReceivesAt_of_isCutoffStableRecovery (hR : R.IsModel)
    (hrec : R.HasFiniteCutReceiving) (w : R.Occurrence) {f : Fin x.arity ↪ Fin w.arity}
    (hf : f.trans w.tuple = x.tuple) {q : StageType.{u} (blockStage ξ) (w.arity + 1)}
    {δ : Label.{u}}
    (hq : (R.stableType hlaw w.tuple w.type w.eval_tuple).IsCutoffStableRecovery f D γ q δ) :
    R.StablyReceivesAt hlaw x D γ := by
  obtain ⟨hqc, hδ, hrecov⟩ := hq
  rw [reduce_stableType] at hqc
  obtain ⟨v, hv, q', hq', hvq⟩ := hrec w q hqc δ hδ
  have hcons := isConsistent_stableCandidate (hlaw := hlaw) hR.isConsistent hR.isCovering
  have hQ'v := stableCandidate_eval_of_eval (hlaw := hlaw) hvq
  have hface : restrictFace Fin.castSuccEmb (R.stableType hlaw v q' hvq) =
      some (R.stableType hlaw w.tuple w.type w.eval_tuple) := by
    rw [← hcons v _ Fin.castSuccEmb hQ'v, hv]
    exact stableCandidate_eval_of_eval w.eval_tuple
  obtain ⟨Q, hQ, hS, hl⟩ := hrecov (R.stableType hlaw v q' hvq)
    (by rw [reduce_stableType]; exact hq') hface
  refine ⟨(extendByLast f).trans v, ?_, Q, ?_, hS, hl⟩
  · rw [← hf, ← hv, ← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc]
  · rw [hcons v _ _ hQ'v, hQ]

/-- **(R4) at a receiving model from acquisition and cutoff stable recovery**: for a model `R`
with finite-cut receiving and a calibration `C`, acquisition of calibrated contexts in `R` and
cutoff stable recovery for `C` give (R4) at every occurrence of the candidate of positive arity,
every coface and every `γ < λ_{ξ+1}`. -/
theorem stablyReceivesAt_of_acquiresCalibratedContexts_of_hasFiniteCutReceiving
    {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (hR : R.IsModel) (hrec : R.HasFiniteCutReceiving)
    (hS : StageType.HasCutoffStableRecoverySchemes ξ C)
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
  obtain ⟨q, δ, hq⟩ := hS _ f x.type (hR.hasLegalTypes w.tuple w.type w.eval_tuple) hx hface D hD
    γ hγ hC
  exact stablyReceivesAt_of_isCutoffStableRecovery hR hrec w hf hq

/-- **Acquisition of the margin calibration**: a model `R` at `λ_ξ` that is not cover-hollow and
has top-grade supremum `⊤` acquires calibrated contexts for the graded cap calibration with a
margin.  The argument of `Realization.IsModel.acquiresCalibratedContexts_gradedCap`, which already
acquires the marker of non-hollowness (`Realization.exists_stableCandidate_label_eq_coe_add`) with
its offset and grade below the grade `N` of the cap; for `γ ≤ λ_ξ + K` the cap is chosen of grade
above `K + |x|` with `|x| > 0`, so the offset `R = K + 1` gives (M1). -/
theorem IsModel.acquiresCalibratedContexts_gradedCapMargin (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapMarginCalibration ξ) R hR.isStablyLawful := by
  classical
  intro x hx D _ γ hγ
  have hlim := isSuccPrelimit_blockStage ξ
  have hpos : (0 : Ordinal.{u}) < blockStage ξ :=
    Ordinal.omega0_pos.trans_le (omega0_le_blockStage ξ)
  obtain ⟨K, hK⟩ := exists_le_blockStage_add_natCast hγ
  obtain ⟨t, ht, -⟩ := exists_eq_stableType_of_stableCandidate_eval x.eval_tuple
  -- the block of each label of `D`: below `λ_ξ` (a reference cell by uniformity) or `λ_ξ` itself
  have hblock (j : Fin D.card) : ∃ ν : Ordinal.{u}, (Order.IsSuccPrelimit ν ∧ ν < blockStage ξ) ∧
      ∃ B : ℕ, ∀ o : Ordinal.{u}, D.label j = o →
        ∃ n < B, o = ν + n ∨ o = blockStage ξ + n := by
    rcases atStage_iff.mp (D.atStage j) with h | ⟨o, ho, h⟩ | h
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, 0, fun o ho ↦ by simp [h] at ho⟩
    · rw [blockStage_add_one] at ho
      rcases lt_or_ge o (blockStage ξ) with hlt | hge
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
          (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
        refine ⟨ω * (o / ω), ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
          (Ordinal.mul_div_le o ω).trans_lt hlt⟩, n + 1,
          fun o' ho' ↦ ⟨n, n.lt_succ_self, Or.inl ?_⟩⟩
        rw [← h] at ho'
        exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hn
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hge ho
        refine ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, n + 1,
          fun o' ho' ↦ ⟨n, n.lt_succ_self, Or.inr ?_⟩⟩
        rw [← h] at ho'
        exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hn
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, 0, fun o ho ↦ by simp [h] at ho⟩
  choose ν hν B hB using hblock
  -- reference cells for the blocks below `λ_ξ`, in an occurrence `y` containing `x`
  obtain ⟨y, fy, K₁, B₁, hfy, -, -, hanc⟩ :=
    hR.exists_extend_uniformity ⟨x.arity, x.tuple, t, ht⟩ hpos (List.ofFn ν) fun μ hμ ↦ by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hμ
      exact hν j
  -- a marker, in an occurrence `z₀` of the candidate
  obtain ⟨z₀, a₀, i₀, ha₀⟩ := exists_stableCandidate_label_eq_coe_add hnh hR.isStablyLawful
  -- a cap, in an occurrence `z₁` of the candidate, of grade above everything involved
  obtain ⟨z₁, b₁, hgb₁, hb₁⟩ := exists_coe_add_grade_le_stableCandidate_label hgrow
    hR.isStablyLawful (K + x.arity + K₁ + i₀ + univ.sup B + y.arity + z₀.arity)
  -- one occurrence `w` containing `y`, `z₀` and `z₁`
  obtain ⟨w, hw⟩ := hR.isCovering.exists_subset_support
    (univ.map y.tuple ∪ univ.map z₀.tuple ∪ univ.map z₁.tuple)
  obtain ⟨g, hg⟩ := w.exists_trans_eq (subset_union_left.trans (subset_union_left.trans hw))
  obtain ⟨f₀, hf₀⟩ := w.exists_trans_eq (subset_union_right.trans (subset_union_left.trans hw))
  obtain ⟨f₁, hf₁⟩ := w.exists_trans_eq (subset_union_right.trans hw)
  -- the marker and the cap move to the stable type of `w` with their labels and grades
  have hcons := isConsistent_stableCandidate (hlaw := hR.isStablyLawful) hR.isConsistent
    hR.isCovering
  let W : (R.stableCandidate hR.isStablyLawful).Occurrence :=
    ⟨w.arity, w.tuple, _, stableCandidate_eval_of_eval w.eval_tuple⟩
  obtain ⟨a', ha'l, ha'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₀ a₀
  obtain ⟨b', hb'l, hb'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₁ b₁
  have hN : K + x.arity + K₁ + i₀ + univ.sup B + y.arity + z₀.arity <
      W.type.toCellScheme.grade b' :=
    hgb₁.trans_eq hb'g.symm
  -- the bounds on the grade of the cap, stated for `W.type`, the stable type of `w`
  have hkN : x.arity < W.type.toCellScheme.grade b' := by omega
  have hRN : K + 1 < W.type.toCellScheme.grade b' := by omega
  have hBN : univ.sup B < W.type.toCellScheme.grade b' := by omega
  have hiN : i₀ < W.type.toCellScheme.grade b' := by omega
  have hK₁N : K₁ < W.type.toCellScheme.grade b' := by omega
  have hyN : y.arity < W.type.toCellScheme.grade b' := by omega
  have ha'N : W.type.toCellScheme.grade a' ≤ W.type.toCellScheme.grade b' := by
    have := z₀.type.grade_le a₀
    omega
  refine ⟨w, fy.trans g, by rw [Function.Embedding.trans_assoc, hg, hfy], b', ?_, hkN,
    ⟨K + 1, hRN, hK.trans_lt (add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self K)) _)⟩,
    ⟨a', i₀, hiN, ha'N, ha'l.trans ha₀⟩, fun j o ho ↦ ?_⟩
  · -- the cap: its label in `W.type` is its label in `z₁.type`
    change _ ≤ W.type.label b'
    rw [hb'l, hb'g]
    exact hb₁
  · have hBj : B j ≤ univ.sup B := le_sup (mem_univ j)
    obtain ⟨n, hn, h | h⟩ := hB j o ho
    · -- a block below `λ_ξ`: the reference cell of `y`, moved to `w` with its label and grade
      obtain ⟨z, k, hk, hz, -⟩ := hanc (ν j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
      obtain ⟨z', hz', hz'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hR.isConsistent hg z
      have hne : w.type.label z' ≠ ⊤ := by
        rw [hz', hz]
        exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
      refine ⟨ν j, n, k, z', (hν j).1, h, (hn.trans_le hBj).trans hBN,
        hk.trans hK₁N, hz'g.trans_le ((y.type.grade_le z).trans hyN.le), ?_⟩
      -- the label of the stable type at `z'` is the stable section there
      change R.stableSection w.tuple w.type z' = _
      rw [stableSection_of_ne_top hne, hz', hz]
    · -- the block `λ_ξ`: the marker
      exact ⟨blockStage ξ, n, i₀, a', hlim, h, (hn.trans_le hBj).trans hBN, hiN, ha'N,
        ha'l.trans ha₀⟩

end Realization

namespace Expansion

/-- **(R4) for receiving models from cutoff stable recovery**, for a calibration `C ξ` at each
`ξ < ω₁` with cutoff stable recovery (`hS`) that every receiving model at `λ_ξ` which is not
cover-hollow and has top-grade supremum `⊤` acquires (`hA`). -/
theorem ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes
    (C : ∀ ξ : Ordinal.{0}, ∀ ⦃m k : ℕ⦄, StageType.{0} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{0} (blockStage (ξ + 1)) (k + 1) → Ordinal.{0} → Prop)
    (hS : ∀ ξ < ω₁, StageType.HasCutoffStableRecoverySchemes ξ (C ξ))
    (hA : ∀ ξ < ω₁, ∀ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) (hR : R.IsModel),
      R.HasFiniteCutReceiving → ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
        Realization.AcquiresCalibratedContexts ξ (C ξ) R hR.isStablyLawful) :
    ReceivingStableCappedReceiving.{w} :=
  ⟨fun ξ _ R hξ hR hrec hnh hgrow x hx D hD γ hγ ↦
    Realization.stablyReceivesAt_of_acquiresCalibratedContexts_of_hasFiniteCutReceiving hR hrec
      (hS ξ hξ) (hA ξ hξ R hR hrec hnh hgrow) x hx D hD γ hγ⟩

/-- **(R4) for receiving models from cutoff stable recovery for the graded cap calibration** at
every `ξ < ω₁`, a finite statement about stage types (open); the acquisition is compiled
(`Realization.IsModel.acquiresCalibratedContexts_gradedCap`). -/
theorem ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes_gradedCap
    (h : ∀ ξ < ω₁,
      StageType.HasCutoffStableRecoverySchemes.{0} ξ (StageType.GradedCapCalibration.{0} ξ)) :
    ReceivingStableCappedReceiving.{w} :=
  .of_hasCutoffStableRecoverySchemes (fun ξ ↦ StageType.GradedCapCalibration ξ) h
    fun _ _ _ _ hR _ hnh hgrow ↦ hR.acquiresCalibratedContexts_gradedCap hnh hgrow

/-- **(R4) for receiving models from cutoff stable recovery for the margin calibration** at every
`ξ < ω₁`, a finite statement about stage types (open), whose inputs are among those of the graded
cap calibration; the acquisition is compiled
(`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`). -/
theorem ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes_gradedCapMargin
    (h : ∀ ξ < ω₁, StageType.HasCutoffStableRecoverySchemes.{0} ξ
      (StageType.GradedCapMarginCalibration.{0} ξ)) :
    ReceivingStableCappedReceiving.{w} :=
  .of_hasCutoffStableRecoverySchemes (fun ξ ↦ StageType.GradedCapMarginCalibration ξ) h
    fun _ _ _ _ hR _ hnh hgrow ↦ hR.acquiresCalibratedContexts_gradedCapMargin hnh hgrow

end Expansion

end VaughtConjecture

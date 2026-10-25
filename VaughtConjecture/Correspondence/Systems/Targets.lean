/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.QualifyingSystem
import VaughtConjecture.MainTheorem.Scatteredness

/-!
# The abstract theorems of [AFK26, §2.5–2.6], stated

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  Each theorem
of [AFK26, §2.5–2.6] about weak and qualifying systems is stated here as a proposition
`…Target`, for an arbitrary geometry signature, invariance diagram, invariant system and base
sublanguage.  **None is proved here**; the only theorems of this file are one-line compositions of
stated targets with existing results.

| Target | Printed | Premises beyond the printed ones |
|---|---|---|
| `WeakSystem.BFEquivOfMatchedTarget` | Proposition 2.18, closed tuples | — |
| `WeakSystem.BFEquivOfCommonInvariantTarget` | Proposition 2.18, as printed | — |
| `WeakSystem.CountableBFClassesTarget` | Theorem 2.19, back-and-forth content | coded on `ℕ` |
| `WeakSystem.ThinnessTarget` | Theorem 2.19 | coded on `ℕ` |
| `WeakSystem.ExistsRankBoundTarget` | Lemma 2.22 | — |
| `WeakSystem.FewMaximalCodingTarget` | Definition 2.20, coding passage | carriers in universe `0` |
| `QualifyingSystem.MkClassesLeAlephOneTarget` | Theorem 2.25 (a), `≤ ℵ₁` | coded on `ℕ` |
| `QualifyingSystem.MkClassesEqAlephOneTarget` | Theorem 2.25 (a) | coded; infinite members |
| `QualifyingSystem.CountableClassesWithoutLiftTarget` | proof of Theorem 2.25 (b) | coded |
| `QualifyingSystem.NoPerfectSetTarget` | Theorem 2.25 (b) | coded |
| `QualifyingSystem.HasThinAlephOneSpectrumTarget` | Theorem 2.27 | coded; infinite members |

"Coded on `ℕ`" means: the class is read through a sentence `φ` of `L_c` whose models coded on `ℕ`
are the members of the base on `ℕ` (`WeakSystem.IsBaseSentence`,
`QualifyingSystem.IsQualifyingSentence`), and the conclusion is about InfinitaryLogic's coded
models (`isoSetoid φ`, `bfEquivSetoid φ`, `HasPerfectSetOfPairwiseNonisomorphicNatModels`).
Carriers of the system are then in universe `0`.  The countable relational language `L_c` is an
explicit instance premise of every coded statement.

## Design decisions

1. **Indices.**  Levels are `SystemLevel = {β : Ordinal.{0} // β < ω₁}`, the index type of
   `InvariantSystem.{0}`; raw ordinals appear only in the conclusions about `bfEquivSetoid`, whose
   levels are raw (`η < ω₁`).
2. **Occurrence and carriers.**  Condition (d) is the printed existential occurrence on a countable
   nonempty carrier; no infiniteness is part of any structure.  "Few maximal models"
   (`WeakSystem.HasFewMaximal`) allows finite carriers, as printed; its passage to the canonical
   carriers `Fin (n + 1)` and `ℕ` is the separate `WeakSystem.HasFewMaximalOnCanonicalCarriers`
   with `WeakSystem.FewMaximalCodingTarget`.  The statements that count only models on `ℕ` and
   need it display `WeakSystem.CountableMembersInfinite` as an explicit premise: the lower bound of
   Theorem 2.25 (a) realizes an invariant of high rank in a member of `K`, and that member must be
   moved to `ℕ`.
3. **Countability.**  A premise, not a clause of `K`; every membership assertion and every
   theorem carries `[Countable _]` on its carriers; nonemptiness is explicit (the field
   `WeakSystem.nonempty` and condition (d)).  Lemma 2.22 uses the countability of the carrier
   directly, to bound the thresholds of **all** closed tuples by one countable ordinal, and not
   only through closure under projection.
4. **Back-and-forth.**  The repository does not formalize [AFK26, Definition 2.15] (back-and-forth
   systems of closed tuples, `≡_β`) or [AFK26, Proposition 2.16]; it uses InfinitaryLogic's
   Karp-style `BFEquiv` and `bfEquivSetoid` and the existing thinness theorem
   `MainTheorem.isThinOnNatModels_of_countable_bfClasses` in their place.  Proposition 2.18 is
   stated with the conclusion `BFEquiv β`, not the printed `≡_β`; no correspondence between the
   two is claimed or stated.
5. **Universes.**  Ordinals in universe `0`; carriers in an arbitrary universe `v` for the
   uncoded statements and in universe `0` for the coded ones; `L` and `L_c` in arbitrary universes,
   except `L_c : Language.{0, 1}` in Theorem 2.27, the universes of
   `MainTheorem.HasThinAlephOneSpectrum`.  The base sublanguage is explicit: its inclusion, the
   characterization of its range as the non-invariant symbols, and the reduct
   (`GeometrySignature.BaseSublanguage`).

## Departures from the printed text

* Definition 2.15 and Proposition 2.16 are replaced, not formalized (decision 4).  The printed
  closed-tuple relation `≡_β` is not an equivalence relation ([AFK26, §2.4] says so); `BFEquiv` at
  the empty tuple is (`bfEquivSetoid`), and the thinness theorem counts its classes, where the
  printed Theorem 2.19 bounds `≡_β`-antichains.
* The coded statements see only the models on `ℕ`; the finite members of the base are seen by
  `WeakSystem.IsBaseSentenceOnCarriers` and by `WeakSystem.HasFewMaximal`.
* Reconstruction, uniqueness of maximal lifts and successor strictness are not assumed anywhere
  (`VaughtConjecture.Correspondence.Systems.QualifyingSystem`).
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}
variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

namespace WeakSystem

/-! ### Proposition 2.18 -/

/-- **Target: [AFK26, Proposition 2.18], for closed tuples**: on countable carriers `M` and `N`,
for `G ∈ K_β` on `M` and `H ∈ K_β` on `N`, tuples `a` and `b` of the same length with one common
invariant (`InvariantSystem.IsMatchedAt` at `β`; then `a`, `b` are closed) are back-and-forth
equivalent at level `β` in the reducts: `BFEquiv β` of `(G↾L_c, a)` and `(H↾L_c, b)`,
InfinitaryLogic's Karp-style relation, in place of the printed `≡_β` (Definition 2.15 is not
formalized).  The printed proof: the relations `I_ι`, `ι ≤ β`, and `ι`-density of
`τ_j(H) ∈ K_j`.  Stated.  Correspondence with the printed definitions. -/
def BFEquivOfMatchedTarget (W : WeakSystem.{w, w', v} D S) : Prop :=
  ∀ (M N : Type v) [Countable M] [Countable N] (β : SystemLevel) (G : L.Structure M)
    (H : L.Structure N), G ∈ W.K β M → H ∈ W.K β N →
    ∀ ⦃n : ℕ⦄ (a : Fin n → M) (b : Fin n → N), S.IsMatchedAt β G H a b →
      @BFEquiv Lc M (E.reduct G) N (E.reduct H) β.1 n a b

/-- **Target: [AFK26, Proposition 2.18], as printed**: (a) a weak system; (b) `G ∈ K_β` and
`H ∈ K_β`, on countable carriers; (c) some invariant `Q` with `G ⊨ ∃x̄ Q(x̄)` and `H ⊨ ∃x̄ Q(x̄)`.
Then `G↾L_c` and `H↾L_c` are back-and-forth equivalent at level `β` at the empty tuple
(`BFEquiv β 0`), in place of the printed `G↾L_c ≡_β H↾L_c`.  Stated.  Correspondence with the
printed definitions. -/
def BFEquivOfCommonInvariantTarget (W : WeakSystem.{w, w', v} D S) : Prop :=
  ∀ (M N : Type v) [Countable M] [Countable N] (β : SystemLevel) (G : L.Structure M)
    (H : L.Structure N), G ∈ W.K β M → H ∈ W.K β N →
    (∃ (n : ℕ) (Q : σ.Invariant n) (a : Fin n → M) (b : Fin n → N),
      RelMap (L := L) (self := G) Q.1 a ∧ RelMap (L := L) (self := H) Q.1 b) →
    @BFEquiv Lc M (E.reduct G) N (E.reduct H) β.1 0 Fin.elim0 Fin.elim0

/-! ### Theorem 2.19 -/

section Coded

variable [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)]

/-- **The coded classes with a member without a lift at `β`** (the set `A_β` of the proofs of
[AFK26, Theorems 2.19 and 2.25 (b)], coded): the isomorphism classes of models of `φ` coded on
`ℕ` that contain a code whose structure has no lift in `K_β` on `ℕ`.  Correspondence with the
printed definitions. -/
def classesWithoutLift (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) (β : SystemLevel) :
    Set (Quotient (isoSetoid φ)) :=
  {q | ∃ c : ModelsOf φ, Quotient.mk (isoSetoid φ) c = q ∧
    ∀ G : L.Structure ℕ, ¬ W.IsLiftAt E β G c.1.toStructure}

/-- **Target: [AFK26, Theorem 2.19], its back-and-forth content, coded**: if `φ` axiomatizes the
base on the codes on `ℕ` and, for every countable `β`, the coded classes with a member without a
lift in `K_β` are countably many (printed hypothesis (b)), then for every `η < ω₁` the coded models
of `φ` fall into countably many classes of `bfEquivSetoid φ η`.  Printed route: the invariants
realized in `K_β` are `β`-invariants, countably many (`InvariantSystem.countable`), and
Proposition 2.18.  Stated.  Correspondence with the printed definitions. -/
def CountableBFClassesTarget (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) : Prop :=
  W.IsBaseSentence E φ → (∀ β : SystemLevel, (W.classesWithoutLift E φ β).Countable) →
    ∀ η : Ordinal.{0}, η < ω₁ → Countable (Quotient (bfEquivSetoid φ η))

/-- **Target: [AFK26, Theorem 2.19], coded**: under the hypotheses of `CountableBFClassesTarget`,
there is no perfect set of pairwise nonisomorphic models of `φ` coded on `ℕ`.  Stated; a
composition of `CountableBFClassesTarget` with the thinness theorem
(`thinnessTarget_of_countableBFClassesTarget`).  Correspondence with the printed definitions. -/
def ThinnessTarget (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) : Prop :=
  W.IsBaseSentence E φ → (∀ β : SystemLevel, (W.classesWithoutLift E φ β).Countable) →
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

/-- **Theorem 2.19 from its back-and-forth content**: `CountableBFClassesTarget` and
`MainTheorem.isThinOnNatModels_of_countable_bfClasses` (in place of [AFK26, Proposition 2.16]).
Correspondence with the printed definitions. -/
theorem thinnessTarget_of_countableBFClassesTarget {W : WeakSystem.{w, w', 0} D S}
    {φ : Lc.Sentenceω} (h : W.CountableBFClassesTarget E φ) : W.ThinnessTarget E φ :=
  fun hφ hA ↦ MainTheorem.isThinOnNatModels_of_countable_bfClasses (h hφ hA)

end Coded

/-! ### Lemma 2.22 -/

/-- **Target: [AFK26, Lemma 2.22]**: on a countable carrier, an eventually determined
`L_c`-structure `B` has a countable bound `α` on the ranks of all its lifts: every lift of `B` in
any `K_β` is fixed at `α`.  The countability of the carrier is used **directly**: the closed tuples
of `B` are countably many, so the thresholds `α_ā` of all of them (each from
`IsEventuallyDeterminedTuple`) have a countable supremum `α = sup (α_ā + 1)`; it is used again in
closure under projection (`WeakSystem.projection_mem`, for `τ_α` of a lift above `α`).  The strict
inequality of [AFK26, Definition 2.21] is why the bound is `α_ā + 1`.  Stated.  Correspondence
with the printed definitions. -/
def ExistsRankBoundTarget (W : WeakSystem.{w, w', v} D S) : Prop :=
  ∀ (M : Type v) [Countable M] (B : Lc.Structure M), W.IsEventuallyDetermined E B →
    ∃ α : SystemLevel, ∀ (β : SystemLevel) (G : L.Structure M), W.IsLiftAt E β G B →
      S.IsFixedAt α G

/-! ### The coding passage for few maximal models -/

/-- **Target: the coding passage for few maximal models** ([AFK26, Definition 2.20], carriers in
universe `0`): few maximal models, over all countable carriers, is equivalent to countably many
classes on each positive finite carrier `Fin (n + 1)` and on `ℕ` (every countable nonempty carrier
is in bijection with one of them, members are nonempty, and `K_β` is closed under isomorphism).
Stated.  Correspondence with the printed definitions. -/
def FewMaximalCodingTarget (W : WeakSystem.{w, w', 0} D S) : Prop :=
  W.HasFewMaximal ↔ W.HasFewMaximalOnCanonicalCarriers

end WeakSystem

namespace QualifyingSystem

variable {E}
variable [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)]

/-! ### Theorem 2.25 -/

/-- **Target: [AFK26, Theorem 2.25 (a)], the upper bound, coded**: for a qualifying sentence `φ`,
the models of `φ` coded on `ℕ` have at most `ℵ₁` isomorphism classes.  Printed route: each member of
the base is the reduct of a maximal structure (condition (a)), and the structures maximal at each
countable level are countably many up to isomorphism (condition (b)); an isomorphism restricts to
the reducts.  No infiniteness premise.  Stated.  Correspondence with the printed definitions. -/
def MkClassesLeAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : Prop :=
  W.IsQualifyingSentence φ → Cardinal.mk (Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1

/-- **Target: [AFK26, Theorem 2.25 (a)], coded**: for a qualifying sentence `φ`, the models of `φ`
coded on `ℕ` have exactly `ℵ₁` isomorphism classes, **under the explicit extra hypothesis**
`CountableMembersInfinite` (members of `K` on countable carriers are infinite).  The lower bound
follows the printed route — Lemma 2.22, condition (d) and `InvariantSystem.ne_univ`: the bounds
`α_B` of the members of the base are cofinal in `ω₁` — and the extra hypothesis moves the member of
`K` given by condition (d) to `ℕ`.  It does not use Reconstruction, uniqueness of maximal lifts or
successor strictness.  Stated.  Correspondence with the printed definitions. -/
def MkClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : Prop :=
  W.IsQualifyingSentence φ → W.CountableMembersInfinite →
    Cardinal.mk (Quotient (isoSetoid φ)) = Cardinal.aleph 1

/-- **Target: the countable part `A_β`** (proof of [AFK26, Theorem 2.25 (b)], coded): for a
qualifying sentence `φ` and every countable `β`, the coded classes with a member without a lift in
`K_β` are countably many.  Printed route: such a member has no lift maximal at any `δ ≥ β`, so its
maximal lift (condition (a)) is maximal at some `δ < β`, and condition (b) at each of the countably
many `δ < β`.  Stated.  Correspondence with the printed definitions. -/
def CountableClassesWithoutLiftTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : Prop :=
  W.IsQualifyingSentence φ →
    ∀ β : SystemLevel, (W.toWeakSystem.classesWithoutLift E φ β).Countable

/-- **Target: [AFK26, Theorem 2.25 (b)], coded**: for a qualifying sentence `φ`, there is no perfect
set of pairwise nonisomorphic models of `φ` coded on `ℕ`.  No infiniteness premise.  Stated; a
composition of `CountableClassesWithoutLiftTarget` and Theorem 2.19
(`noPerfectSetTarget_of_thinnessTarget`).  Correspondence with the printed definitions. -/
def NoPerfectSetTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) (φ : Lc.Sentenceω) :
    Prop :=
  W.IsQualifyingSentence φ → ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

/-- **Theorem 2.25 (b) from Theorem 2.19 and the countable part.**  Correspondence with the printed
definitions. -/
theorem noPerfectSetTarget_of_thinnessTarget {W : QualifyingSystem.{w, w', wc, wc', 0} D S E}
    {φ : Lc.Sentenceω} (h219 : W.toWeakSystem.ThinnessTarget E φ)
    (hA : W.CountableClassesWithoutLiftTarget φ) : W.NoPerfectSetTarget φ :=
  fun hφ ↦ h219 hφ (hA hφ)

end QualifyingSystem

/-! ### Theorem 2.27 -/

namespace QualifyingSystem

variable {Lc₀ : Language.{0, 1}} [Lc₀.IsRelational] [Countable (Σ n, Lc₀.Relations n)]
variable {E₀ : σ.BaseSublanguage Lc₀}

/-- **Target: [AFK26, Theorem 2.27], coded**: for a qualifying sentence `φ` of a language `L_c` in
the universes `Language.{0, 1}`, countable and relational, and under the explicit extra hypothesis
`CountableMembersInfinite`, `φ` has a thin `ℵ₁` spectrum (`MainTheorem.HasThinAlephOneSpectrum`):
exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic coded
models.  Stated; a composition of Theorem 2.25 (a) and (b)
(`hasThinAlephOneSpectrumTarget_of`).  Correspondence with the printed definitions. -/
def HasThinAlephOneSpectrumTarget (W : QualifyingSystem.{w, w', 0, 1, 0} D S E₀)
    (φ : Lc₀.Sentenceω) : Prop :=
  W.IsQualifyingSentence φ → W.CountableMembersInfinite → MainTheorem.HasThinAlephOneSpectrum φ

/-- **Theorem 2.27 from Theorem 2.25 (a) and (b).**  Correspondence with the printed definitions. -/
theorem hasThinAlephOneSpectrumTarget_of {W : QualifyingSystem.{w, w', 0, 1, 0} D S E₀}
    {φ : Lc₀.Sentenceω} (ha : W.MkClassesEqAlephOneTarget φ) (hb : W.NoPerfectSetTarget φ) :
    W.HasThinAlephOneSpectrumTarget φ :=
  fun hφ hinf ↦ ⟨ha hφ hinf, hb hφ⟩

end QualifyingSystem

end VaughtConjecture.Correspondence

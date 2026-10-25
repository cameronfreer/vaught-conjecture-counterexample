/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.WeakSystem

/-!
# Qualifying systems: [AFK26, Definitions 2.23, 2.24, 2.26]

Numbering as in the current draft of [AFK26] (the published v1 reads identically).
[AFK26, Definition 2.23] singles out the weak systems satisfying four conditions (the manuscript's
term for them is "Knight system"; no identifier here uses that name).  They are
`QualifyingSystem D S E`, a structure extending `WeakSystem D S`, with one field per condition:

* `base_maximal` (a): every member of the base, on a countable carrier, is the reduct of a
  maximal structure on the same carrier (the reverse inclusion of the printed equality
  `K_{-∞} = {M↾L_c : M ∈ K maximal}` holds for every weak system, since a maximal structure at `β`
  is in `K_β`);
* `fewMaximal` (b): few maximal models (`WeakSystem.HasFewMaximal`, finite carriers allowed);
* `eventuallyDetermined` (c): every member of the base, on a countable carrier, is eventually
  determined (`WeakSystem.IsEventuallyDetermined`, strict inequality as printed);
* `invariant_occurs` (d): every invariant holds of some tuple of some member of `K`, on a
  countable nonempty carrier — the printed existential occurrence, with **no** infiniteness.

A sentence of `L_c` whose models form the base ([AFK26, Definitions 2.24 and 2.26]) is
`QualifyingSystem.IsQualifyingSentence`, on the codes on `ℕ`.

**What is not assumed.**  None of the following is a field or a hypothesis of any abstract
statement in `VaughtConjecture.Correspondence.Systems`: Reconstruction (base-isomorphic maximal
structures are isomorphic), uniqueness of the maximal lift of a member of the base, and successor
strictness of the levels.  They are inputs of the existing count for `K[L]`, not conditions of
[AFK26, Definition 2.23]; the abstract count follows the printed route instead
(`VaughtConjecture.Correspondence.Systems.Targets`).
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

/-- **A qualifying system** [AFK26, Definition 2.23]: a weak system for `D` and `S`, with a base
sublanguage `E`, satisfying the four printed conditions (a)–(d), one field each.  Countability of
the carriers is an explicit premise of (a) and (c) and an explicit part of the witness of (d);
nonemptiness is explicit in (d) and a consequence of membership elsewhere.  Reconstruction,
uniqueness of maximal lifts and successor strictness are **not** fields.  Correspondence with the
printed definitions. -/
structure QualifyingSystem (D : InvarianceDiagram σ) (S : InvariantSystem.{0} σ)
    {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc) extends WeakSystem.{w, w', v} D S where
  /-- (a) Every member of the base on a countable carrier is the reduct of a maximal structure on
  the same carrier. -/
  base_maximal (M : Type v) [Countable M] (B : Lc.Structure M) :
    toWeakSystem.IsInBase E B → ∃ G : L.Structure M, toWeakSystem.IsMaximal G ∧ E.reduct G = B
  /-- (b) Few maximal models. -/
  fewMaximal : toWeakSystem.HasFewMaximal
  /-- (c) Every member of the base on a countable carrier is eventually determined. -/
  eventuallyDetermined (M : Type v) [Countable M] (B : Lc.Structure M) :
    toWeakSystem.IsInBase E B → toWeakSystem.IsEventuallyDetermined E B
  /-- (d) Every invariant holds of some tuple of some member of `K`, on a countable nonempty
  carrier. -/
  invariant_occurs ⦃n : ℕ⦄ (Q : σ.Invariant n) :
    ∃ (M : Type v) (_ : Countable M) (_ : Nonempty M) (β : SystemLevel) (G : L.Structure M),
      G ∈ K β M ∧ ∃ x : Fin n → M, RelMap (L := L) (self := G) Q.1 x

namespace QualifyingSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}
variable {Lc : Language.{wc, wc'}} {E : σ.BaseSublanguage Lc}

/-- **A qualifying sentence for a qualifying system** ([AFK26, Definitions 2.24 and 2.26], coded):
the models of `φ` coded on `ℕ` are exactly the members of the base on `ℕ`
(`WeakSystem.IsBaseSentence`).  The printed definition asks for some diagram, invariant system and
system; the statements of `VaughtConjecture.Correspondence.Systems.Targets` quantify over all of
them, which is the same.  The instance premises are those of InfinitaryLogic's `ModelsOf`; the
universes `Language.{0, 1}` are imposed only where `MainTheorem.HasThinAlephOneSpectrum` is used.
Correspondence with the printed definitions. -/
def IsQualifyingSentence (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) [Lc.IsRelational]
    [Countable (Σ n, Lc.Relations n)] (φ : Lc.Sentenceω) : Prop :=
  W.toWeakSystem.IsBaseSentence E φ

end QualifyingSystem

end VaughtConjecture.Correspondence

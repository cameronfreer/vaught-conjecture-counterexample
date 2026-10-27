/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Count
import VaughtConjecture.Correspondence.Systems.Thinness

/-!
# [AFK26, Theorem 2.25 (a)] for a sentence, and [AFK26, Theorem 2.27]

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a
qualifying system `W` (carriers in universe `0`) and a sentence `φ` of `L_c`, the general count
`QualifyingSystem.mkBaseClassesEqAlephOneTarget` is read on InfinitaryLogic's coded models.

**Codes and members of the base.**  On a carrier `X`, decoding (`StructureSpaceOn.toStructure`)
and encoding (`StructureSpaceOn.ofStructure`) are inverse
(`StructureSpaceOn.ofStructure_toStructure`, `BaseSublanguage.toStructure_ofStructure`); when the
codes of a set are exactly the codes of members of the base, decoding is a bijection onto the
members of the base on `X` (`WeakSystem.codedBaseEquiv`), and coded isomorphism is isomorphism of
the decoded structures, so the coded classes are the classes of the base on `X`
(`WeakSystem.isoSetoidOnQuotientEquiv` on `Fin (n + 1)`, `WeakSystem.isoSetoidQuotientEquiv`
on `ℕ`).

**[AFK26, Theorem 2.25 (a)], for a sentence**
(`QualifyingSystem.mkModelClassesEqAlephOneTarget`,
`QualifyingSystem.MkModelClassesEqAlephOneTarget`): for `φ` axiomatizing the base on all countable
nonempty carriers, the coded classes on every `Fin (n + 1)` and on `ℕ` together are in bijection
with `WeakSystem.BaseClasses` (`WeakSystem.modelClassesEquiv`), so they number exactly `ℵ₁`.  The
finite carriers are kept; no infiniteness.

**The specializations coded on `ℕ`**:

* `QualifyingSystem.mkClassesLeAlephOneTarget` (`QualifyingSystem.MkClassesLeAlephOneTarget`): for
  a qualifying sentence, at most `ℵ₁` coded classes on `ℕ`: they are the classes of the base on
  `ℕ`, one summand of `WeakSystem.BaseClasses`.  No infiniteness.
* `QualifyingSystem.mkClassesEqAlephOneTarget` (`QualifyingSystem.MkClassesEqAlephOneTarget`):
  exactly `ℵ₁`, under the explicit extra hypothesis `WeakSystem.CountableMembersInfinite`, which
  empties the finite summands of `WeakSystem.BaseClasses` (a member of the base on `Fin (n + 1)`
  has a lift in `K` on `Fin (n + 1)`, which would be infinite).
* `QualifyingSystem.hasThinAlephOneSpectrumTarget`
  (`QualifyingSystem.HasThinAlephOneSpectrumTarget`, [AFK26, Theorem 2.27], coded): a composition
  of `mkClassesEqAlephOneTarget` and Theorem 2.25 (b) (`QualifyingSystem.noPerfectSetTarget`) by
  `QualifyingSystem.hasThinAlephOneSpectrumTarget_of`, under the same extra hypothesis.
-/

universe w w' wc wc'

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}
variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}

/-! ### Codes and members of the base -/

namespace GeometrySignature.BaseSublanguage

variable {Lc : Language.{wc, wc'}} [Lc.IsRelational]

/-- **Decoding the code of a structure gives the structure back**, on any carrier
(`StructureSpaceOn.toStructure_ofStructure`).  Correspondence with the printed definitions. -/
theorem toStructure_ofStructure (E : σ.BaseSublanguage Lc) {X : Type} (B : Lc.Structure X) :
    (StructureSpaceOn.ofStructure B).toStructure = B :=
  E.structure_ext fun _ r x ↦ StructureSpaceOn.toStructure_ofStructure B r x

end GeometrySignature.BaseSublanguage

/-- **Membership in `ModelsOfOn` is realization**, on the carrier `Fin n` (as
InfinitaryLogic's `mem_modelsOf_iff_realize` on `ℕ`: the empty valuation is unique).
Correspondence with the printed definitions. -/
theorem mem_modelsOfOn_fin_iff_realize {Lc : Language.{wc, wc'}} [Lc.IsRelational] {n : ℕ}
    (c : StructureSpaceOn Lc (Fin n)) (φ : Lc.Sentenceω) :
    c ∈ ModelsOfOn (α := Fin n) φ ↔ @Sentenceω.Realize Lc φ (Fin n) c.toStructure := by
  change @BoundedFormulaω.Realize Lc (Fin n) c.toStructure Empty 0 φ Empty.elim Fin.elim0 ↔
    @BoundedFormulaω.Realize Lc (Fin n) c.toStructure Empty 0 φ Empty.elim _
  exact iff_of_eq (congrArg (@BoundedFormulaω.Realize Lc (Fin n) c.toStructure Empty 0 φ
    Empty.elim) (Subsingleton.elim _ _))

namespace WeakSystem

variable (W : WeakSystem.{w, w', 0} D S)
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc) [Lc.IsRelational]

/-- **Decoding is a bijection onto the members of the base**: for a set `P` of codes on a carrier
`X` whose members are exactly the codes of members of the base, decoding
(`StructureSpaceOn.toStructure`) is a bijection from `P` to the members of the base on `X`, with
inverse the encoding (`StructureSpaceOn.ofStructure`).  Correspondence with the printed
definitions. -/
noncomputable def codedBaseEquiv {X : Type} (P : Set (StructureSpaceOn Lc X))
    (hP : ∀ c, c ∈ P ↔ W.IsInBase E c.toStructure) :
    P ≃ {B : Lc.Structure X // W.IsInBase E B} where
  toFun c := ⟨c.1.toStructure, (hP c.1).mp c.2⟩
  invFun B := ⟨StructureSpaceOn.ofStructure B.1,
    (hP _).mpr ((E.toStructure_ofStructure B.1).symm ▸ B.2)⟩
  left_inv c := Subtype.ext (StructureSpaceOn.ofStructure_toStructure c.1)
  right_inv B := Subtype.ext (E.toStructure_ofStructure B.1)

variable [Countable (Σ n, Lc.Relations n)]

/-- **The coded classes on `Fin (n + 1)` are the classes of the base there**, for a sentence
axiomatizing the base on all countable nonempty carriers: `codedBaseEquiv` on the models of `φ`
coded on `Fin (n + 1)` (`mem_modelsOfOn_fin_iff_realize`), and coded isomorphism is isomorphism of
the decoded structures.  Correspondence with the printed definitions. -/
noncomputable def isoSetoidOnQuotientEquiv {φ : Lc.Sentenceω}
    (hφ : W.IsBaseSentenceOnCarriers E φ) (n : ℕ) :
    Quotient (isoSetoidOn φ (n + 1)) ≃ Quotient (W.baseIsoSetoid E (Fin (n + 1))) :=
  Quotient.congr (W.codedBaseEquiv E (ModelsOfOn (α := Fin (n + 1)) φ)
    fun c ↦ (mem_modelsOfOn_fin_iff_realize c φ).trans (hφ (Fin (n + 1)) c.toStructure))
    fun _ _ ↦ Iff.rfl

/-- **The coded classes on `ℕ` are the classes of the base there**, for a sentence axiomatizing the
base on the codes on `ℕ`: `codedBaseEquiv` on the models of `φ` coded on `ℕ`.  Correspondence
with the printed definitions. -/
noncomputable def isoSetoidQuotientEquiv {φ : Lc.Sentenceω} (hφ : W.IsBaseSentence E φ) :
    Quotient (isoSetoid φ) ≃ Quotient (W.baseIsoSetoid E ℕ) :=
  Quotient.congr (W.codedBaseEquiv E (X := ℕ) (ModelsOf φ) hφ) fun _ _ ↦ Iff.rfl

/-- **The coded classes on all canonical carriers are the classes of the base**: for a sentence
axiomatizing the base on all countable nonempty carriers, the coded classes on every
`Fin (n + 1)` and on `ℕ` are in bijection with `WeakSystem.BaseClasses`
(`isoSetoidOnQuotientEquiv`, `isoSetoidQuotientEquiv` with
`isBaseSentence_of_isBaseSentenceOnCarriers`).  Correspondence with the printed definitions. -/
noncomputable def modelClassesEquiv {φ : Lc.Sentenceω} (hφ : W.IsBaseSentenceOnCarriers E φ) :
    ((Σ n : ℕ, Quotient (isoSetoidOn φ (n + 1))) ⊕ Quotient (isoSetoid φ)) ≃ W.BaseClasses E :=
  Equiv.sumCongr (Equiv.sigmaCongrRight fun n ↦ W.isoSetoidOnQuotientEquiv E hφ n)
    (W.isoSetoidQuotientEquiv E (isBaseSentence_of_isBaseSentenceOnCarriers E hφ))

end WeakSystem

/-! ### Theorem 2.25 (a) for a sentence, and its specializations coded on `ℕ` -/

namespace QualifyingSystem

variable {Lc : Language.{wc, wc'}} {E : σ.BaseSublanguage Lc}
variable [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)]

/-- **[AFK26, Theorem 2.25 (a)], for a sentence** (`MkModelClassesEqAlephOneTarget`): for `φ`
axiomatizing the base on all countable nonempty carriers, the coded classes on every
`Fin (n + 1)` and on `ℕ` number exactly `ℵ₁`: they are in bijection with
`WeakSystem.BaseClasses` (`WeakSystem.modelClassesEquiv`), which has `ℵ₁` elements
(`mkBaseClassesEqAlephOneTarget`).  No infiniteness.  Correspondence with the printed
definitions. -/
theorem mkModelClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.MkModelClassesEqAlephOneTarget E φ := by
  intro hφ
  have h := Cardinal.lift_mk_eq'.mpr ⟨W.toWeakSystem.modelClassesEquiv E hφ⟩
  rw [W.mkBaseClassesEqAlephOneTarget] at h
  exact Cardinal.lift_eq_aleph_one.mp (h.trans (Cardinal.lift_eq_aleph_one.mpr rfl))

/-- **[AFK26, Theorem 2.25 (a)], the upper bound, coded on `ℕ`** (`MkClassesLeAlephOneTarget`):
for a qualifying sentence `φ`, the coded classes on `ℕ` are the classes of the base on `ℕ`
(`WeakSystem.isoSetoidQuotientEquiv`), one summand of `WeakSystem.BaseClasses`, which has at most
`ℵ₁` elements (`mk_baseClasses_le_aleph_one`).  No infiniteness.  Correspondence with the printed
definitions. -/
theorem mkClassesLeAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.MkClassesLeAlephOneTarget φ := by
  intro hφ
  have h := Cardinal.lift_mk_le'.mpr
    ⟨(W.toWeakSystem.isoSetoidQuotientEquiv E hφ).toEmbedding.trans
      (Function.Embedding.inr (α := Σ n : ℕ,
        Quotient (W.toWeakSystem.baseIsoSetoid E (Fin (n + 1)))))⟩
  exact Cardinal.lift_le_aleph_one.mp
    (h.trans (Cardinal.lift_le_aleph_one.mpr W.mk_baseClasses_le_aleph_one))

omit [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)] in
/-- **Under `CountableMembersInfinite` the base has no member on a finite canonical carrier**: a
member of the base on `Fin (n + 1)` has a lift in some `K_β` on `Fin (n + 1)`, which would be
infinite.  Correspondence with the printed definitions. -/
theorem isEmpty_finClasses (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (hinf : W.CountableMembersInfinite) :
    IsEmpty (Σ n : ℕ, Quotient (W.toWeakSystem.baseIsoSetoid E (Fin (n + 1)))) := by
  refine ⟨fun ⟨n, q⟩ ↦ ?_⟩
  obtain ⟨β, G, hG, -⟩ := q.out.2
  exact (hinf β (Fin (n + 1)) G hG).not_finite inferInstance

/-- **[AFK26, Theorem 2.25 (a)], coded on `ℕ`, under `CountableMembersInfinite`**
(`MkClassesEqAlephOneTarget`): for a qualifying sentence `φ`, the coded classes on `ℕ` are the
classes of the base on `ℕ` (`WeakSystem.isoSetoidQuotientEquiv`); under the explicit extra
hypothesis the finite summands of `WeakSystem.BaseClasses` are empty (`isEmpty_finClasses`), so
the classes on `ℕ` are all of `WeakSystem.BaseClasses`, which has `ℵ₁` elements
(`mkBaseClassesEqAlephOneTarget`).  Correspondence with the printed definitions. -/
theorem mkClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.MkClassesEqAlephOneTarget φ := by
  intro hφ hinf
  have := W.isEmpty_finClasses hinf
  have h := Cardinal.lift_mk_eq'.mpr
    ⟨(W.toWeakSystem.isoSetoidQuotientEquiv E hφ).trans
      (Equiv.emptySum (Σ n : ℕ, Quotient (W.toWeakSystem.baseIsoSetoid E (Fin (n + 1))))
        (Quotient (W.toWeakSystem.baseIsoSetoid E ℕ))).symm⟩
  rw [W.mkBaseClassesEqAlephOneTarget] at h
  exact Cardinal.lift_eq_aleph_one.mp (h.trans (Cardinal.lift_eq_aleph_one.mpr rfl))

end QualifyingSystem

/-! ### Theorem 2.27 -/

namespace QualifyingSystem

variable {Lc₀ : Language.{0, 1}} [Lc₀.IsRelational] [Countable (Σ n, Lc₀.Relations n)]
variable {E₀ : σ.BaseSublanguage Lc₀}

/-- **[AFK26, Theorem 2.27], coded** (`HasThinAlephOneSpectrumTarget`): for a qualifying sentence
`φ` of a countable relational `L_c` in the universes `Language.{0, 1}`, and under the explicit
extra hypothesis `CountableMembersInfinite`, `φ` has a thin `ℵ₁` spectrum: exactly `ℵ₁` coded
classes (`mkClassesEqAlephOneTarget`) and no perfect set of pairwise nonisomorphic coded models
(`noPerfectSetTarget`), by `hasThinAlephOneSpectrumTarget_of`.  Correspondence with the printed
definitions. -/
theorem hasThinAlephOneSpectrumTarget (W : QualifyingSystem.{w, w', 0, 1, 0} D S E₀)
    (φ : Lc₀.Sentenceω) : W.HasThinAlephOneSpectrumTarget φ :=
  hasThinAlephOneSpectrumTarget_of (W.mkClassesEqAlephOneTarget φ) (W.noPerfectSetTarget φ)

end QualifyingSystem

end VaughtConjecture.Correspondence

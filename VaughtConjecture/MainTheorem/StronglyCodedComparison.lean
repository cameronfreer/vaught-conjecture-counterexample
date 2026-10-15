/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.StronglyCodedTerminalProperty

/-!
# The exact-age comparison without modelhood, and the rigid-core comparison in the class

Roadmap, Layer 4 (terminal classification by exact ages; the rigid-core comparison) and
Correspondence, item 1 (the strongly coded legal stage types).

**The language of stage types.**  `stageTypeLanguage α` is the relational language whose symbols
of arity `n` are the stage types at `α` on `n` points.  A realization `R` on `M` gives the
structure `Realization.coverStructure R`, in which a symbol `p` holds of a tuple `c` exactly when
`c` covers `p` (`Realization.Covers`).  An isomorphism of these structures is an isomorphism of
the realizations (`Realization.eq_map_of_equiv_coverStructure`): a tuple is typed `p` in `R`
exactly when its image covers `p` in the other.

**Atomic agreement without modelhood** (`Realization.CoverMatch.sameAtomicType_coverStructure`).
Tuples matched through covers (`Realization.CoverMatch`) are selections `x ∘ s` and `y ∘ s` of
covers `x` and `y` of one stage type `t`.  Under exact consistency, a selection `x ∘ g` covers `p`
exactly when `g` is injective and the face of `t` along `g` is `p`
(`Realization.covers_comp_iff`); so the matched tuples satisfy the same atomic formulas.  This
replaces `Realization.Covers.sameAtomicType`, which reads the base relations from the base reduct
of an expansion (`IsExpansionOf`).

**The exact-age comparison** (`Realization.exactAgeIsoTarget`, proved: native construction).  The
argument of `Realization.exists_equiv_comp_eq_of_exactReceivingWithinAt`, with the forth and back
steps `Realization.CoverMatch.exists_snoc` (which already use only exact consistency and covering),
the atomic agreement above in place of the base reduct, and InfinitaryLogic's countable
back-and-forth construction (`PotentialIso.ofExtensionFamily`,
`PotentialIso.countable_toEquiv_graph`).  The conclusion is an isomorphism of realizations carrying
the core to the core.

| model-level use (`exists_equiv_comp_eq_of_exactReceivingWithinAt`) | replacement here |
|---|---|
| `he.isModel.isConsistent`, `he'.isModel.isConsistent` | exact consistency premises |
| `he.isModel.isCovering`, `he'.isModel.isCovering` | covering premises |
| `CoverMatch.sameAtomicType he he'` (base reduct) | `CoverMatch.sameAtomicType_coverStructure` |
| isomorphism of base structures | isomorphism of realizations |

**The rigid-core comparison** (`Realization.stronglyCodedRigidCoreIsoTarget`, proved: native
construction): the exact-age comparison for the strongly coded pointed age of a rigid core, with
age inclusion `Realization.IsGloballyRigidCore.mem_stronglyCodedRigidCoreAge` and exact receiving
`Realization.IsStronglyCodedReceiving.exactReceivingWithinAt_stronglyCodedRigidCoreAge`.  No premise
beyond the class.

**The class-language reading** (`Realization.classReadingEquivTarget`, proved: native
construction).  An isomorphism of realizations `R.Iso S` is an isomorphism, in the class language
`templateLanguage`, of the structures of the class readings: the class reading of `R.map e` at
the image of a tuple is that of `R` at the tuple.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open FirstOrder Language Structure

/-- The **language of stage types** at `α`: relational, with the stage types at `α` on `n` points
as the symbols of arity `n`. -/
def stageTypeLanguage (α : Ordinal.{u}) : Language.{0, u + 1} where
  Functions _ := Empty
  Relations n := StageType.{u} α n

instance (α : Ordinal.{u}) : (stageTypeLanguage.{u} α).IsRelational :=
  fun _ ↦ inferInstanceAs (IsEmpty Empty)

namespace Realization

variable {α : Ordinal.{u}} {M N : Type w}

/-- The **structure of covers** of a realization in the language of stage types: a symbol `p`
holds of a tuple exactly when the tuple covers `p`. -/
@[instance_reducible] def coverStructure (R : Realization.{u, w} α M) :
    (stageTypeLanguage.{u} α).Structure M where
  funMap f := Empty.elim f
  RelMap p c := R.Covers p c

variable {R : Realization.{u, w} α M} {S : Realization.{u, w} α N}

/-- **Selections of a cover** (native construction): under exact consistency, a selection `x ∘ g`
of the coordinates of a cover `x` of `t` covers `p` exactly when `g` is injective and the face of
`t` along `g` is `p`. -/
theorem covers_comp_iff (hR : R.IsConsistent) {k l : ℕ} {t : StageType.{u} α k} {x : Fin k → M}
    (hx : R.Covers t x) (g : Fin l → Fin k) (p : StageType.{u} α l) :
    R.Covers p (x ∘ g) ↔ ∃ hg : Function.Injective g, StageType.restrictFace ⟨g, hg⟩ t = some p :=
  ⟨fun ⟨hxg, he⟩ ↦ ⟨hxg.of_comp, (hx.eval_comp hR hxg.of_comp).symm.trans he⟩,
    fun ⟨hg, he⟩ ↦ ⟨hx.injective.comp hg, (hx.eval_comp hR hg).trans he⟩⟩

/-- **Matched tuples have the same atomic type in the language of stage types** (native
construction), for exactly consistent realizations: both are selections, along one selector, of
covers of one stage type (`Realization.covers_comp_iff`).  No base structure is used. -/
theorem CoverMatch.sameAtomicType_coverStructure (hR : R.IsConsistent) (hS : S.IsConsistent)
    {k₀ n : ℕ} {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N} {a : Fin n → M} {b : Fin n → N}
    (h : CoverMatch R S x₀ y₀ n a b) :
    letI := R.coverStructure
    letI := S.coverStructure
    SameAtomicType (L := stageTypeLanguage.{u} α) a b := by
  let := R.coverStructure
  let := S.coverStructure
  obtain ⟨k, t, x, y, ι, s, hx, hy, -, -, rfl, rfl⟩ := h
  intro idx
  cases idx with
  | eq i j => exact hx.injective.eq_iff.trans hy.injective.eq_iff.symm
  | rel p f =>
    exact (covers_comp_iff hR hx (s ∘ f) p).trans (covers_comp_iff hS hy (s ∘ f) p).symm

/-- **An isomorphism of the structures of covers is an isomorphism of realizations** (native
construction): a tuple is typed `p` in `R` exactly when it covers `p`, exactly when its image
covers `p` in `S`. -/
theorem eq_map_of_equiv_coverStructure :
    letI := R.coverStructure
    letI := S.coverStructure
    ∀ e : M ≃[stageTypeLanguage.{u} α] N, R.map e.toEquiv = S := by
  let := R.coverStructure
  let := S.coverStructure
  intro e
  refine (eq_map_of_eval_trans (R := R) (e := e.toEquiv) fun {n} t ↦ ?_).symm
  have key (p : StageType.{u} α n) :
      S.eval (t.trans e.toEquiv.toEmbedding) = some p ↔ R.eval t = some p :=
    ((covers_iff_eval (R := S) (t.trans e.toEquiv.toEmbedding)).symm.trans
      (e.map_rel p t)).trans (covers_iff_eval t)
  cases h : R.eval t with
  | some p => exact (key p).mpr h
  | none =>
    cases h' : S.eval (t.trans e.toEquiv.toEmbedding) with
    | none => rfl
    | some q => exact absurd ((key q).mp h') (by simp [h])

/-- **The exact-age comparison without modelhood, pointed** (native construction).  The argument
of `Realization.exists_equiv_comp_eq_of_exactReceivingWithinAt` in the language of stage types,
with exact consistency and covering in place of the expansions. -/
theorem exists_iso_comp_eq_of_exactReceivingWithinAt [Countable M] [Countable N] {k₀ : ℕ}
    {p : StageType.{u} α k₀} {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N}
    {A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)}
    (hR : R.IsConsistent) (hRc : R.IsCovering) (hS : S.IsConsistent) (hSc : S.IsCovering)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R.eval s = some D → ⇑s ∘ ι = x₀ → D ∈ A m ι)
    (hage' : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      S.eval s = some D → ⇑s ∘ ι = y₀ → D ∈ A m ι)
    (hr : R.ExactReceivingWithinAt x₀ A) (hr' : S.ExactReceivingWithinAt y₀ A)
    (h₀ : R.Covers p x₀) (h₀' : S.Covers p y₀) : ∃ i : R.Iso S, ⇑i.1 ∘ x₀ = y₀ := by
  let := R.coverStructure
  let := S.coverStructure
  let P : PotentialIso (stageTypeLanguage.{u} α) M N :=
    PotentialIso.ofExtensionFamily (CoverMatch R S x₀ y₀) (CoverMatch.zero h₀ h₀')
      (fun h ↦ h.sameAtomicType_coverStructure hR hS)
      (fun h m ↦ h.exists_snoc hR hRc hage hr' m)
      (fun h m' ↦ (h.symm.exists_snoc hS hSc hage' hr m').imp fun _ h' ↦ h'.symm)
  obtain ⟨e, hgraph⟩ := P.countable_toEquiv_graph
  refine ⟨⟨e.toEquiv, eq_map_of_equiv_coverStructure e⟩, funext fun j ↦ ?_⟩
  obtain ⟨⟨n, a, b⟩, hp, i, hai, hbi⟩ := hgraph (x₀ j)
  obtain ⟨k, t, x, y, ι, s, hx, hy, hxι, hyι, ha, hb⟩ := hp
  simp only at hai hbi ha hb
  have hsi : s i = ι j :=
    hx.injective ((congrFun ha i).symm.trans (hai.trans (congrFun hxι j).symm))
  change e (x₀ j) = y₀ j
  rw [← hbi, congrFun hb i, ← congrFun hyι j]
  exact congrArg y hsi

/-- **Target (c): the exact-age comparison without modelhood** (native construction):
`Realization.exists_iso_comp_eq_of_exactReceivingWithinAt`. -/
theorem exactAgeIsoTarget (α : Ordinal.{u}) (M N : Type w) : ExactAgeIsoTarget α M N :=
  fun _ _ _ _ _ _ _ _ _ hR hRc hS hSc hage hage' hr hr' h₀ h₀' ↦
    exists_iso_comp_eq_of_exactReceivingWithinAt hR hRc hS hSc hage hage' hr hr' h₀ h₀'

/-- **Target (b): the rigid-core comparison in the strongly coded receiving class** (native
construction): the exact-age comparison for the strongly coded pointed age of a rigid core
(`StageType.stronglyCodedRigidCoreAge`), with age inclusion from the globally rigid cores
(`Realization.IsGloballyRigidCore.mem_stronglyCodedRigidCoreAge`) and exact receiving from the
class (`Realization.IsStronglyCodedReceiving.exactReceivingWithinAt_stronglyCodedRigidCoreAge`). -/
theorem stronglyCodedRigidCoreIsoTarget (ξ : Ordinal.{0}) (M N : Type w) :
    StronglyCodedRigidCoreIsoTarget ξ M N := by
  intro _ _ R S _ p x₀ y₀ hR hS hc hc' hcore hcore'
  exact exists_iso_comp_eq_of_exactReceivingWithinAt hR.isConsistent hR.isCovering
    hS.isConsistent hS.isCovering
    (fun _ _ ι _ hs hsι ↦ hcore.mem_stronglyCodedRigidCoreAge hR hc ι hs hsι)
    (fun _ _ ι _ hs hsι ↦ hcore'.mem_stronglyCodedRigidCoreAge hS hc' ι hs hsι)
    (hR.exactReceivingWithinAt_stronglyCodedRigidCoreAge x₀ p)
    (hS.exactReceivingWithinAt_stronglyCodedRigidCoreAge y₀ p) hc hc'

/-! ### The class-language reading of an isomorphism of realizations -/

/-- The class reading of a transport at the image of a tuple is the class reading at the tuple. -/
theorem classReading_map_eval_comp (e : M ≃ N) {n : ℕ} {x : Fin n → M}
    (h : Function.Injective (e ∘ x)) :
    (R.map e).classReading.eval ⟨e ∘ x, h⟩ =
      R.classReading.eval ⟨x, Function.Injective.of_comp h⟩ := by
  simp only [classReading_eval, map_eval]
  congr 3
  ext i
  simp

/-- **An isomorphism of realizations is an isomorphism of the class-reading structures** (native
construction): the class-language structure of the class reading of `R.map e` at the image of a
tuple is that of `R` at the tuple (`Realization.classReading_map_eval_comp`). -/
def Iso.classReadingEquiv (i : R.Iso S) :
    @Language.Equiv templateLanguage.{u} M N R.classReading.toStructure
      S.classReading.toStructure := by
  obtain ⟨e, he⟩ := i
  letI := R.classReading.toStructure
  letI := S.classReading.toStructure
  refine ⟨e, fun f ↦ Empty.elim f, fun {n} r x ↦ ?_⟩
  subst he
  change (∃ h : Function.Injective (e ∘ x), ∃ c, (R.map e).classReading.eval ⟨e ∘ x, h⟩ = some c ∧
      r.Reads c.globalClass) ↔ ∃ h : Function.Injective x, ∃ c,
        R.classReading.eval ⟨x, h⟩ = some c ∧ r.Reads c.globalClass
  constructor
  · rintro ⟨h, c, hc, hr⟩
    exact ⟨h.of_comp, c, (classReading_map_eval_comp e h).symm.trans hc, hr⟩
  · rintro ⟨h, c, hc, hr⟩
    exact ⟨e.injective.comp h, c, (classReading_map_eval_comp e (e.injective.comp h)).trans hc,
      hr⟩

/-- **Target (c), the class-language reading of the conclusion** (native construction):
`Realization.Iso.classReadingEquiv`. -/
theorem classReadingEquivTarget (α : Ordinal.{u}) (M N : Type w) :
    ClassReadingEquivTarget α M N :=
  fun _ _ ⟨i⟩ ↦ ⟨i.classReadingEquiv⟩

end Realization

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Count
import VaughtConjecture.ProcessRank.RankConventions
import VaughtConjecture.ProcessRank.RankInvariance
import VaughtConjecture.ProcessRank.RankTopLabel
import VaughtConjecture.ProcessRank.Reconstruction
import VaughtConjecture.Realization.ClosureCardinality

/-!
# Scott classes of process rank `ω₁`: the count statements

Companion programme over the density sentence `baseLanguage.densitySentence`.  For a structure
`M` and a tuple `a` of `M` (repeated coordinates allowed), `r(a) = orbitRank a`,
`R(M) = sup_a (r(a))` (the **process rank**) and `S(M) = sup_a (r(a) + 1) = internalScottRank M`,
as in `VaughtConjecture.ProcessRank.RankConventions`.

**What is counted.**  Classes of models of the density sentence under **potential isomorphism**
(`Nonempty (PotentialIso baseLanguage M N)`, equivalently `L_{∞,ω}` equivalence by Karp's
theorem), not isomorphism classes.  Three predicates on a structure `M : Type w`:

* `IsProcessRankOmegaOneModel M`: `M` satisfies the density sentence and `R(M)` is the lift of
  `ω₁`;
* `IsInternalRankOmegaOneModel M`: the density sentence and `S(M)` is the lift of `ω₁`;
* `IsInternalRankOmegaOneAddOneModel M`: the density sentence and `S(M)` is the lift of
  `ω₁ + 1`.

At the limit `ω₁`, `R(M) = ω₁` iff `S(M) = ω₁` (no tuple attains the supremum) or `S(M) = ω₁ + 1`
(some tuple attains it) (`ProcessRank.iSup_orbitRank_eq_iff_of_isSuccLimit`), so the third class
set is the second removed from the first.  All three predicates are invariant under potential
isomorphism, across universes (`ProcessRank.RealizeIffOfPotentialIsoTarget`,
`ProcessRank.RanksLiftEqOfPotentialIsoTarget`), so a class meets a predicate exactly when all its
members do.

**Two presentations.**

* All carriers in one universe: `ScottClasses L Q` is the quotient of the sigma type of a carrier
  `M : Type w` and a structure on it satisfying `Q` by potential isomorphism
  (`potentialIsoSetoid`).  The count targets `ProcessRankOmegaOneScottClassesCardTarget`,
  `InternalRankOmegaOneScottClassesCardTarget` and
  `InternalRankOmegaOneAddOneScottClassesCardTarget` are stated for every universe `w`.
* Codes on the carrier `ω₁.ToType` (`AlephOne.Code`, in `Type`): `CodeScottClasses P` is the
  quotient of the codes satisfying `P` by potential isomorphism of their decoded structures.  The
  count targets `CodeProcessRankOmegaOneCardTarget`, `CodeInternalRankOmegaOneCardTarget` and
  `CodeInternalRankOmegaOneAddOneCardTarget`.

**Scope and transport.**  Every model `M` of the density sentence with `R(M) ≥ ω₁` has exactly
`ℵ₁` points (`mk_eq_aleph_one_of_lift_omegaOne_le`, proved: at most `ℵ₁` for every model,
`Realization.mkLeAlephOneOfRealizeDensitySentenceTarget`; a countable structure has countable
`R(M)`, `ProcessRank.iSup_orbitRank_lt_omegaOne_of_countable`).  So each such model, on a carrier
in any universe, is isomorphic to a decoded code (`StructureCode.existsIsoCodeTarget`), and each
decoded code has an isomorphic copy on a carrier in any universe.  The transport
(`ScottClassesCodeTransportTarget`, stated) turns such a two-sided correspondence into equal
lifted cardinalities of the classes; so the code counts give the counts on all carriers in every
universe.  No model is identified with a code except through these isomorphisms.

**The class of internal rank `ω₁`, in two milestones.**

1. Among models admitting a receiving expansion at `ω₁`
   (`ReceivingInternalRankOmegaOnePotentialIsoTarget`): two receiving model expansions at `ω₁`,
   on carriers in any two universes, whose base structures have `S = ω₁`, have potentially
   isomorphic base structures.  Proved from the top-label obstruction alone
   (`receivingInternalRankOmegaOnePotentialIsoTarget_of_orbitRankGe`): `S(M) = ω₁` makes every
   `r(a) < ω₁`, so every chart is top-free (`isTopFree_of_internalScottRank_eq_omegaOne`), and the
   top-free comparison applies (`AlephOne.receivingModelsPotentialIsoTarget`).
2. Among all models of the density sentence (`InternalRankOmegaOnePotentialIsoTarget`): proved
   from milestone 1 and the reconstruction (`internalRankOmegaOnePotentialIsoTarget_of`), since
   `S(M) = ω₁` gives `R(M) = ω₁`.

Existence of a model with `S = ω₁` on a carrier in `Type` is
`AlephOne.existsAlephOneModelScottRankOmegaOneTarget` (proved).

**Results.**

* `nonempty_potentialIso_trans`, `potentialIsoSetoid`, `codePotentialIsoSetoid` (proved).
* `mk_eq_aleph_one_of_lift_omegaOne_le` (proved).
* `isTopFree_of_internalScottRank_eq_omegaOne`,
  `receivingInternalRankOmegaOnePotentialIsoTarget_of_orbitRankGe`,
  `internalRankOmegaOnePotentialIsoTarget_of` (proved, conditional on the named targets).
* The count targets, `ScottClassesCodeTransportTarget`,
  `ReceivingInternalRankOmegaOnePotentialIsoTarget`, `InternalRankOmegaOnePotentialIsoTarget`
  (stated).
-/

universe u v w w'

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order Cardinal FirstOrder Language

/-! ### Classes under potential isomorphism -/

section Classes

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Potential isomorphism is transitive** on carriers in one universe: through back-and-forth
equivalence of the empty tuples at every level (InfinitaryLogic's `potentialIso_iff_BFEquiv_all`)
and `BFEquiv.trans`. -/
theorem nonempty_potentialIso_trans {M N P : Type w} [L.Structure M] [L.Structure N]
    [L.Structure P] (h₁ : Nonempty (PotentialIso L M N)) (h₂ : Nonempty (PotentialIso L N P)) :
    Nonempty (PotentialIso L M P) :=
  potentialIso_iff_BFEquiv_all.2 fun α ↦
    (potentialIso_iff_BFEquiv_all.1 h₁ α).trans (potentialIso_iff_BFEquiv_all.1 h₂ α)

variable (L)

/-- **Potential isomorphism** on the structures on carriers in `Type w` satisfying a predicate
`Q`: two members of the sigma type are related when there is a potential isomorphism between
them. -/
def potentialIsoSetoid (Q : ∀ (M : Type w) [L.Structure M], Prop) :
    Setoid (Σ M : Type w, {inst : L.Structure M // @Q M inst}) where
  r x y := Nonempty (@PotentialIso L _ x.1 y.1 x.2.1 y.2.1)
  iseqv :=
    ⟨fun x ↦ ⟨@PotentialIso.refl L _ x.1 x.2.1⟩,
      fun {x y} ⟨e⟩ ↦ ⟨@PotentialIso.symm L _ x.1 x.2.1 y.1 y.2.1 e⟩,
      fun {x y z} h₁ h₂ ↦
        @nonempty_potentialIso_trans L _ x.1 y.1 z.1 x.2.1 y.2.1 z.2.1 h₁ h₂⟩

/-- **The Scott classes of the structures satisfying `Q`** on carriers in `Type w`: the quotient
of the sigma type of a carrier and a structure on it satisfying `Q` by potential isomorphism
(`potentialIsoSetoid`). -/
def ScottClasses (Q : ∀ (M : Type w) [L.Structure M], Prop) : Type (max u v (w + 1)) :=
  Quotient (potentialIsoSetoid L Q)

end Classes

/-- **Potential isomorphism of decoded structures** on the codes on the carrier `ω₁.ToType`. -/
def codePotentialIsoSetoid : Setoid AlephOne.Code where
  r c d := Nonempty (PotentialIso baseLanguage.{0} c.Decoded d.Decoded)
  iseqv :=
    ⟨fun c ↦ ⟨PotentialIso.refl c.Decoded⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
      fun h₁ h₂ ↦ nonempty_potentialIso_trans h₁ h₂⟩

/-- **The Scott classes of the codes satisfying `P`**: the quotient of the codes on `ω₁.ToType`
satisfying `P` by potential isomorphism of their decoded structures. -/
def CodeScottClasses (P : AlephOne.Code → Prop) : Type 1 :=
  Quotient (codePotentialIsoSetoid.comap (Subtype.val : {c // P c} → AlephOne.Code))

/-! ### The predicates counted -/

/-- A **model of process rank `ω₁`**: `M` satisfies the density sentence and
`R(M) = sup_a (r(a))` is the lift of `ω₁`. -/
def IsProcessRankOmegaOneModel (M : Type w) [baseLanguage.{0}.Structure M] : Prop :=
  Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) =
      Ordinal.lift.{w} (ω₁ : Ordinal.{0})

/-- A **model of internal Scott rank `ω₁`**: `M` satisfies the density sentence and
`S(M) = sup_a (r(a) + 1)` is the lift of `ω₁`. -/
def IsInternalRankOmegaOneModel (M : Type w) [baseLanguage.{0}.Structure M] : Prop :=
  Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
    internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} (ω₁ : Ordinal.{0})

/-- A **model of internal Scott rank `ω₁ + 1`**: `M` satisfies the density sentence and
`S(M) = sup_a (r(a) + 1)` is the lift of `ω₁` plus one. -/
def IsInternalRankOmegaOneAddOneModel (M : Type w) [baseLanguage.{0}.Structure M] : Prop :=
  Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
    internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} (ω₁ : Ordinal.{0}) + 1

/-! ### The counts on all carriers of a universe -/

/-- **Target: `ℵ₀` Scott classes of process rank `ω₁`.**  The models of the density sentence on
carriers in `Type w` with `R(M) = ω₁` fall into exactly `ℵ₀` classes under potential
isomorphism.  Stated. -/
def ProcessRankOmegaOneScottClassesCardTarget : Prop :=
  #(ScottClasses baseLanguage.{0} fun (M : Type w) [baseLanguage.{0}.Structure M] ↦
      IsProcessRankOmegaOneModel M) = ℵ₀

/-- **Target: one Scott class of internal Scott rank `ω₁`.**  The models of the density sentence
on carriers in `Type w` with `S(M) = ω₁` form exactly one class under potential isomorphism.
Stated. -/
def InternalRankOmegaOneScottClassesCardTarget : Prop :=
  #(ScottClasses baseLanguage.{0} fun (M : Type w) [baseLanguage.{0}.Structure M] ↦
      IsInternalRankOmegaOneModel M) = 1

/-- **Target: `ℵ₀` Scott classes of internal Scott rank `ω₁ + 1`.**  The models of the density
sentence on carriers in `Type w` with `S(M) = ω₁ + 1` fall into exactly `ℵ₀` classes under
potential isomorphism.  Stated. -/
def InternalRankOmegaOneAddOneScottClassesCardTarget : Prop :=
  #(ScottClasses baseLanguage.{0} fun (M : Type w) [baseLanguage.{0}.Structure M] ↦
      IsInternalRankOmegaOneAddOneModel M) = ℵ₀

/-! ### The counts on codes -/

/-- **Target: `ℵ₀` Scott classes of process rank `ω₁`, on codes.**  The codes on `ω₁.ToType`
whose decoded structures are models of process rank `ω₁` fall into exactly `ℵ₀` classes under
potential isomorphism.  Stated. -/
def CodeProcessRankOmegaOneCardTarget : Prop :=
  #(CodeScottClasses fun c ↦ IsProcessRankOmegaOneModel c.Decoded) = ℵ₀

/-- **Target: one Scott class of internal Scott rank `ω₁`, on codes.**  Stated. -/
def CodeInternalRankOmegaOneCardTarget : Prop :=
  #(CodeScottClasses fun c ↦ IsInternalRankOmegaOneModel c.Decoded) = 1

/-- **Target: `ℵ₀` Scott classes of internal Scott rank `ω₁ + 1`, on codes.**  Stated. -/
def CodeInternalRankOmegaOneAddOneCardTarget : Prop :=
  #(CodeScottClasses fun c ↦ IsInternalRankOmegaOneAddOneModel c.Decoded) = ℵ₀

/-! ### Scope: cardinality and transport -/

/-- **A model of uncountable process rank has exactly `ℵ₁` points**: at most `ℵ₁` as a model of
the density sentence (`Realization.mkLeAlephOneOfRealizeDensitySentenceTarget`), and not
countable, since a countable structure has `R(M)` below the lift of `ω₁`
(`ProcessRank.iSup_orbitRank_lt_omegaOne_of_countable`). -/
theorem mk_eq_aleph_one_of_lift_omegaOne_le {M : Type w} [baseLanguage.{0}.Structure M]
    (hΦ : Sentenceω.Realize baseLanguage.densitySentence.{0} M)
    (hR : Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤
      ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) :
    #M = ℵ₁ := by
  refine le_antisymm (Realization.mkLeAlephOneOfRealizeDensitySentenceTarget hΦ)
    (le_of_not_gt fun hlt ↦ ?_)
  rw [← Cardinal.succ_aleph0, Order.lt_succ_iff] at hlt
  have : Countable M := Cardinal.mk_le_aleph0_iff.1 hlt
  exact (iSup_orbitRank_lt_omegaOne_of_countable (L := baseLanguage.{0})).not_ge hR

/-- **Target: transport of Scott classes between all carriers of a universe and codes.**  For a
predicate `Q` on structures on carriers in `Type w` and a predicate `P` on codes on `ω₁.ToType`,
if every structure satisfying `Q` is isomorphic to a decoded code satisfying `P`, and every
decoded code satisfying `P` is isomorphic to a structure on a carrier in `Type w` satisfying `Q`,
then the classes under potential isomorphism have equal cardinalities after lifting to a common
universe.  For the three predicates counted, the first hypothesis is
`mk_eq_aleph_one_of_lift_omegaOne_le` with `StructureCode.existsIsoCodeTarget` and invariance
under isomorphism; the second is a copy of the decoded structure on a carrier in `Type w`.
Stated. -/
def ScottClassesCodeTransportTarget : Prop :=
  ∀ (Q : ∀ (M : Type w) [baseLanguage.{0}.Structure M], Prop) (P : AlephOne.Code → Prop),
    (∀ (M : Type w) [baseLanguage.{0}.Structure M], Q M →
      ∃ c : AlephOne.Code, P c ∧ Nonempty (M ≃[baseLanguage.{0}] c.Decoded)) →
    (∀ c : AlephOne.Code, P c → ∃ (M : Type w) (_ : baseLanguage.{0}.Structure M),
      Q M ∧ Nonempty (c.Decoded ≃[baseLanguage.{0}] M)) →
    Cardinal.lift.{1} #(ScottClasses baseLanguage.{0} Q) =
      Cardinal.lift.{w + 1} #(CodeScottClasses P)

/-! ### The class of internal Scott rank `ω₁` -/

/-- **Internal Scott rank `ω₁` makes every chart top-free**, given the top-label obstruction: in
a receiving model expansion at `ω₁` with `S(M) = ω₁`, every `r(a)` is below `ω₁`
(`ProcessRank.internalScottRank_eq_iff_of_isSuccLimit`), while a cover of a chart with a top
cell has `r(a) ≥ ω₁` (`OrbitRankGeOmegaOneOfCoversTarget`). -/
theorem isTopFree_of_internalScottRank_eq_omegaOne (h : OrbitRankGeOmegaOneOfCoversTarget.{w})
    {M : Type w} [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁)
    (hR : R.1.IsReceivingModel)
    (hS : internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} (ω₁ : Ordinal.{0}))
    ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{0} ω₁ n) (hp : R.1.eval t = some p) :
    p.IsTopFree := by
  by_contra htop
  have hlim : IsSuccLimit (Ordinal.lift.{w} (ω₁ : Ordinal.{0})) :=
    Ordinal.isSuccLimit_lift.2 (Cardinal.isSuccLimit_omega 1)
  have hlt := ((internalScottRank_eq_iff_of_isSuccLimit hlim).1 hS).2 n t
  exact (h R hR p t (Realization.covers_of_eval t hp) htop).not_gt hlt

/-- **Target (milestone 1): one class of internal Scott rank `ω₁` among the models admitting a
receiving expansion at `ω₁`.**  For receiving model expansions `R` of `M` and `S` of `N` to `ω₁`,
on carriers in any two universes, with `S(M)` and `S(N)` the lift of `ω₁`, there is a potential
isomorphism between `M` and `N`.  Given-model statement.  Stated; proved from the top-label
obstruction by `receivingInternalRankOmegaOnePotentialIsoTarget_of_orbitRankGe`. -/
def ReceivingInternalRankOmegaOnePotentialIsoTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁), R.1.IsReceivingModel →
    S.1.IsReceivingModel →
    internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} (ω₁ : Ordinal.{0}) →
    internalScottRank (L := baseLanguage.{0}) N = Ordinal.lift.{w'} (ω₁ : Ordinal.{0}) →
      Nonempty (PotentialIso baseLanguage.{0} M N)

/-- **Milestone 1 from the top-label obstruction**: both models have only top-free charts
(`isTopFree_of_internalScottRank_eq_omegaOne`), and the top-free comparison gives the potential
isomorphism (`AlephOne.receivingModelsPotentialIsoTarget`). -/
theorem receivingInternalRankOmegaOnePotentialIsoTarget_of_orbitRankGe
    (h : OrbitRankGeOmegaOneOfCoversTarget.{w}) (h' : OrbitRankGeOmegaOneOfCoversTarget.{w'}) :
    ReceivingInternalRankOmegaOnePotentialIsoTarget.{w, w'} := by
  intro M N _ _ R S hR hS hM hN
  obtain ⟨P, -⟩ := AlephOne.receivingModelsPotentialIsoTarget R S hR
    (isTopFree_of_internalScottRank_eq_omegaOne h R hR hM) hS
    (isTopFree_of_internalScottRank_eq_omegaOne h' S hS hN)
  exact ⟨P⟩

/-- **Target (milestone 2): one class of internal Scott rank `ω₁` among all models.**  Any two
models of the density sentence, on carriers in any two universes, with `S(M)` and `S(N)` the lift
of `ω₁`, are potentially isomorphic.  Given-model statement.  Stated; proved from milestone 1 and
the reconstruction by `internalRankOmegaOnePotentialIsoTarget_of`. -/
def InternalRankOmegaOnePotentialIsoTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N],
    IsInternalRankOmegaOneModel M → IsInternalRankOmegaOneModel N →
      Nonempty (PotentialIso baseLanguage.{0} M N)

/-- **Milestone 2 from milestone 1 and the reconstruction**: `S(M) = ω₁` gives `R(M) = ω₁`
(`ProcessRank.internalScottRank_eq_iff_of_isSuccLimit`), so the reconstruction gives receiving
expansions at `ω₁`, and milestone 1 applies. -/
theorem internalRankOmegaOnePotentialIsoTarget_of
    (hrec : ExistsReceivingExpansionOfProcessRankTarget.{w})
    (hrec' : ExistsReceivingExpansionOfProcessRankTarget.{w'})
    (h : ReceivingInternalRankOmegaOnePotentialIsoTarget.{w, w'}) :
    InternalRankOmegaOnePotentialIsoTarget.{w, w'} := by
  intro M N _ _ ⟨hΦ, hM⟩ ⟨hΦ', hN⟩
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  obtain ⟨R, hR⟩ := hrec hΦ
    ((internalScottRank_eq_iff_of_isSuccLimit (Ordinal.isSuccLimit_lift.2 hω)).1 hM).1.ge
  obtain ⟨S, hS⟩ := hrec' hΦ'
    ((internalScottRank_eq_iff_of_isSuccLimit (Ordinal.isSuccLimit_lift.2 hω)).1 hN).1.ge
  exact h R S hR hS hM hN

end VaughtConjecture.ProcessRank

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Language.Satisfaction

/-!
# The density sentence

Roadmap, Layer 2 (the density sentence: the structural clauses and the one-point capped-extension
clause, the preferred presentation of the sentence of the main theorem; its equivalence with the
four-family sentence) and Layer 3 (receiving over a root at a permitted cutoff; the finite-cut
receiving property; the cap-to-model theorem); semantic contract, items 3 and 5.

**Receiving.**  The **receiving family** of a stage type `d` at a cutoff `c`
(`StageType.receivingFamily d c`) consists of the stage types on the scheme of `d` with the
observation of `d` at `c`: `min (q.label i) c = min (d.label i) c` at every cell.  A realization
`R` at stage `α` has the **finite-cut receiving property** (`Realization.HasFiniteCutReceiving`)
when over every occurrence (a *root*, the empty root included), for every coface `d` of its type
(a one-point *donor type*) and every permitted cutoff `c` (`⊥ < c < α`), some point extends the
root to an occurrence with a type in the receiving family of `d` at `c`.  The quantifiers are in
the order root, donor, cutoff, point: different cutoffs may be served by different points.
Receiving at a cutoff does not separate a large proper label from the formal top.  The property is
invariant under transport along bijections of carriers
(`Realization.hasFiniteCutReceiving_map_iff`).

**The density sentence.**  The receiving clause (`receivingClause`) is an extension clause whose
parameters over a relation symbol `p` are a coface `d` of the stage type of `p` and a permitted
cutoff `c` at stage `ω`, a natural number (`ReceivingIndex`), with family the receiving family of
`d` at `c`.  The **density sentence** (`densitySentence`) is the conjunction of the structural
sentence and the receiving clause.  It holds in a structure exactly when the structure is a type
assignment on a nonempty carrier whose realization is exactly consistent and covering and has the
finite-cut receiving property (`realize_densitySentence_iff`), and it holds in the structure of a
realization with legal types exactly when the realization has a nonempty carrier, is exactly
consistent and covering, and has the finite-cut receiving property
(`realize_toStructure_densitySentence_iff`).

**Fidelity.**  The equivalence of the density sentence with the four-family sentence rests on two
theorems about realizations that are not proved here, and which appear as explicit hypotheses,
stated for the realizations at stage `ω` on the carrier at hand:

* **finite-cut receiving** (row 1 of the table of extension statements of Layer 3 of the roadmap):
  every model has the finite-cut receiving property.  It gives the direction from the four-family
  sentence to the density sentence (`realize_densitySentence_of_realize_fourFamilySentence`);
* **the cap-to-model theorem**: a realization with legal types on a nonempty carrier that is
  exactly consistent, covering, and has the finite-cut receiving property is a model.  It gives the
  direction from the density sentence to the four-family sentence
  (`realize_fourFamilySentence_of_realize_densitySentence`), and with it the density sentence has
  no finite models (`infinite_of_realize_densitySentence`).

With both hypotheses the two sentences are equivalent
(`realize_densitySentence_iff_realize_fourFamilySentence`).

## Placement

`StageType.receivingFamily` and its lemmas belong in `VaughtConjecture.Realization.Families`,
beside `StageType.dominanceFamily`, and `Realization.HasFiniteCutReceiving` with its transport in
the file of the finite extension statements of Layer 3.  They are stated here so that those files
are unchanged.

## References

The density sentence is not in the source; it is a second presentation of the models of
[Kni26, Definition 3.2.1] at stage `ω`, whose four-family presentation is the sentence `T` of
[Kni26, Definition 3.3.3], for R. W. Knight, *A counterexample to Vaught's Conjecture using
generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal Label StageType baseLanguage

variable {α : Ordinal.{u}} {M : Type v} {N : Type w} {n : ℕ}

/-! ### Receiving -/

namespace StageType

/-- The **receiving family** of a stage type `d` at a cutoff `c`: the stage types on the scheme of
`d` with the observation of `d` at `c`. -/
def receivingFamily (d : StageType.{u} α n) (c : Label.{u}) : Set (StageType.{u} α n) :=
  {q | q.toScheme = d.toScheme ∧
    ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = j → min (q.label i) c = min (d.label j) c}

/-- Membership in the receiving family: the scheme and the observation at the cutoff. -/
theorem mem_receivingFamily {d q : StageType.{u} α n} {c : Label.{u}} :
    q ∈ receivingFamily d c ↔ q.toScheme = d.toScheme ∧
      ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = j → min (q.label i) c = min (d.label j) c :=
  Iff.rfl

/-- A stage type is in each of its receiving families. -/
theorem self_mem_receivingFamily (d : StageType.{u} α n) (c : Label.{u}) :
    d ∈ receivingFamily d c :=
  ⟨rfl, fun _ _ h ↦ by rw [Fin.ext h]⟩

end StageType

namespace Realization

variable (R : Realization.{u, v} α M)

/-- The **finite-cut receiving property**: over every occurrence, for every coface `d` of its type
and every permitted cutoff `c`, some point extends the occurrence to one with a type on the scheme
of `d` with the observation of `d` at `c`. -/
def HasFiniteCutReceiving : Prop :=
  ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, ∀ c : Label.{u}, IsPermittedCutoff α c →
    R.RealizesOver x.tuple (receivingFamily d c)

variable {R}

/-- **Transport of receiving**: the finite-cut receiving property is preserved and reflected by
transport along a bijection of carriers. -/
theorem hasFiniteCutReceiving_map_iff (e : M ≃ N) :
    (R.map e).HasFiniteCutReceiving ↔ R.HasFiniteCutReceiving := by
  refine ⟨fun h x d hd c hc ↦ ?_, fun h y d hd c hc ↦
    (realizesOver_map_iff e).mpr (h (y.comap e) d hd c hc)⟩
  have key : (x.map e).tuple.trans e.symm.toEmbedding = x.tuple := by
    ext
    exact e.symm_apply_apply _
  exact key ▸ (realizesOver_map_iff (R := R) e).mp (h (x.map e) d hd c hc)

/-- Isomorphic realizations have the finite-cut receiving property together. -/
theorem IsIso.hasFiniteCutReceiving_iff {S : Realization.{u, w} α N} (h : R.IsIso S) :
    R.HasFiniteCutReceiving ↔ S.HasFiniteCutReceiving := by
  obtain ⟨e, rfl⟩ := h
  exact (hasFiniteCutReceiving_map_iff e).symm

end Realization

namespace baseLanguage

/-! ### The density sentence -/

/-- The permitted cutoffs at stage `ω` are countably many: they are the natural numbers. -/
instance countable_permittedCutoff :
    Countable {c : Label.{u} // IsPermittedCutoff (ω : Ordinal.{u}) c} :=
  Set.Countable.to_subtype <|
    (countable_Iio_omega0.image fun δ : Ordinal.{u} ↦ (δ : Label.{u})).mono
      fun _ hc ↦ isPermittedCutoff_iff.mp hc

/-- The parameters of the receiving clause over a relation symbol `p`: a coface of the stage type
of `p` (the donor) and a permitted cutoff. -/
def ReceivingIndex (p : baseLanguage.{u}.Relations n) : Type (u + 1) :=
  {d : StageType.{u} ω (n + 1) // d ∈ (type p).cofaces} ×
    {c : Label.{u} // IsPermittedCutoff (ω : Ordinal.{u}) c}

/-- The parameters of the receiving clause are countably many. -/
instance (p : baseLanguage.{u}.Relations n) : Countable (ReceivingIndex p) :=
  have := StageType.countable countable_Iio_omega0 (n + 1)
  inferInstanceAs (Countable (_ × _))

/-- The **receiving clause**: over a tuple of type `p`, for every coface `d` of `p` and every
permitted cutoff `c`, a point realizing the receiving family of `d` at `c`. -/
noncomputable def receivingClause : baseLanguage.{u}.Sentenceω :=
  extensionClause (fun _ p ↦ ReceivingIndex p) fun _ _ a ↦ receivingFamily a.1.1 a.2.1

/-- The **density sentence**: the structural sentence and the receiving clause. -/
noncomputable def densitySentence : baseLanguage.{u}.Sentenceω :=
  structuralSentence ⊓ receivingClause

section Structure

variable (M) [baseLanguage.{u}.Structure M]

/-- The receiving clause, realized: root, donor, cutoff, then a point. -/
theorem realize_receivingClause : receivingClause.Realize M ↔
    ∀ ⦃n : ℕ⦄ (p : baseLanguage.{u}.Relations n) (xs : Fin n → M), RelMap p xs →
      ∀ d ∈ (type p).cofaces, ∀ c : Label.{u}, IsPermittedCutoff ω c →
        RealizesOver xs (receivingFamily d c) := by
  rw [receivingClause, realize_extensionClause]
  exact ⟨fun h _ p xs hp d hd c hc ↦ h p xs hp (⟨d, hd⟩, ⟨c, hc⟩),
    fun h _ p xs hp a ↦ h p xs hp a.1.1 a.1.2 a.2.1 a.2.2⟩

/-- **Satisfaction of the density sentence**: it holds in a structure exactly when the structure is
a type assignment on a nonempty carrier whose realization is exactly consistent and covering and
has the finite-cut receiving property. -/
theorem realize_densitySentence_iff : densitySentence.Realize M ↔ IsTypeAssignment M ∧
    Nonempty M ∧ (toRealization M).IsConsistent ∧ (toRealization M).IsCovering ∧
      (toRealization M).HasFiniteCutReceiving := by
  have h : densitySentence.Realize M ↔
      structuralSentence.Realize M ∧ receivingClause.Realize M := by
    simp only [densitySentence, Sentenceω.realize_def, BoundedFormulaω.realize_inf]
  rw [h, realize_structuralSentence_iff_isConsistent, realize_receivingClause]
  refine ⟨fun ⟨⟨hT, hne, hcons, hcov⟩, hr⟩ ↦ ⟨hT, hne, hcons, hcov, fun x d hd c hc ↦ ?_⟩,
    fun ⟨hT, hne, hcons, hcov, hr⟩ ↦ ⟨⟨hT, hne, hcons, hcov⟩, fun n p xs hp d hd c hc ↦ ?_⟩⟩
  · exact (hT.realizesOver_iff x.tuple _).mp (hr _ _ (relMap_occurrence x) d hd c hc)
  · exact (hT.realizesOver_iff ⟨xs, hT.injective p xs hp⟩ _).mpr
      (hr (hT.occurrence p xs hp) d hd c hc)

end Structure

/-- **Satisfaction by the structure of a realization**: for a realization with legal types, its
structure satisfies the density sentence exactly when its carrier is nonempty and it is exactly
consistent, covering, and has the finite-cut receiving property. -/
theorem realize_toStructure_densitySentence_iff {R : Realization.{u, v} ω M}
    (hR : R.HasLegalTypes) : @Sentenceω.Realize _ densitySentence M R.toStructure ↔
      Nonempty M ∧ R.IsConsistent ∧ R.IsCovering ∧ R.HasFiniteCutReceiving := by
  rw [@realize_densitySentence_iff M R.toStructure, toRealization_toStructure hR]
  exact and_iff_right (isTypeAssignment_toStructure R)

/-! ### Fidelity -/

section Fidelity

variable [baseLanguage.{u}.Structure M]

/-- **From the four-family sentence to the density sentence**, given finite-cut receiving for the
models at stage `ω` on the carrier. -/
theorem realize_densitySentence_of_realize_fourFamilySentence
    (hreceiving : ∀ R : Realization.{u, v} ω M, R.IsModel → R.HasFiniteCutReceiving)
    (h : fourFamilySentence.Realize M) : densitySentence.Realize M := by
  obtain ⟨hT, hM⟩ := (baseLanguage.realize_fourFamilySentence_iff M).mp h
  exact (realize_densitySentence_iff M).mpr
    ⟨hT, hM.nonempty, hM.isConsistent, hM.isCovering, hreceiving _ hM⟩

/-- **From the density sentence to the four-family sentence**, given the cap-to-model theorem for
the realizations at stage `ω` on the carrier. -/
theorem realize_fourFamilySentence_of_realize_densitySentence
    (hcap : ∀ R : Realization.{u, v} ω M, Nonempty M → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel)
    (h : densitySentence.Realize M) : fourFamilySentence.Realize M := by
  obtain ⟨hT, hne, hcons, hcov, hr⟩ := (realize_densitySentence_iff M).mp h
  exact (baseLanguage.realize_fourFamilySentence_iff M).mpr
    ⟨hT, hcap _ hne hasLegalTypes_toRealization hcons hcov hr⟩

/-- **Fidelity of the density sentence**: given finite-cut receiving for the models and the
cap-to-model theorem for the realizations at stage `ω` on the carrier, the density sentence and
the four-family sentence hold in the same structures. -/
theorem realize_densitySentence_iff_realize_fourFamilySentence
    (hreceiving : ∀ R : Realization.{u, v} ω M, R.IsModel → R.HasFiniteCutReceiving)
    (hcap : ∀ R : Realization.{u, v} ω M, Nonempty M → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel) :
    densitySentence.Realize M ↔ fourFamilySentence.Realize M :=
  ⟨realize_fourFamilySentence_of_realize_densitySentence hcap,
    realize_densitySentence_of_realize_fourFamilySentence hreceiving⟩

/-- Given the cap-to-model theorem for the realizations at stage `ω` on the carrier, a structure
satisfying the density sentence is infinite. -/
theorem infinite_of_realize_densitySentence
    (hcap : ∀ R : Realization.{u, v} ω M, Nonempty M → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel)
    (h : densitySentence.Realize M) : Infinite M :=
  infinite_of_realize_fourFamilySentence
    (realize_fourFamilySentence_of_realize_densitySentence hcap h)

end Fidelity

end baseLanguage

end VaughtConjecture

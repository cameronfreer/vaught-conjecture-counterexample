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
receiving property; the statement of the cap-to-model theorem, as a hypothesis only); semantic
contract, items 3 and 5.

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

**Fidelity, conditionally.**  The equivalence of the density sentence with the four-family
sentence (the fidelity theorem, checkpoint 4 of the roadmap), and the absence of finite models of
the density sentence, rest on two theorems about realizations that are not proved here.  They
appear as explicit hypotheses, stated for the realizations at stage `ω` on the carrier at hand:

* **finite-cut receiving** (row 1 of the table of extension statements of Layer 3 of the roadmap):
  every model has the finite-cut receiving property;
* **the cap-to-model theorem** (Layer 3): a realization with legal types on a nonempty carrier that
  is exactly consistent, covering, and has the finite-cut receiving property is a model.

The theorems of the section `Fidelity` are wiring from these hypotheses, and are named by them:
from the four-family sentence to the density sentence given finite-cut receiving
(`realize_densitySentence_of_realize_fourFamilySentence_of_hasFiniteCutReceiving`); from the
density sentence to the four-family sentence given the cap-to-model theorem
(`realize_fourFamilySentence_of_realize_densitySentence_of_capToModel`); the equivalence given
both (`realize_densitySentence_iff_fourFamilySentence_of_hasFiniteCutReceiving_of_capToModel`);
and no finite models of the density sentence given the cap-to-model theorem
(`infinite_of_realize_densitySentence_of_capToModel`).  They do **not** discharge the fidelity
theorem or the absence of finite models for the density sentence: the former needs both row 1 and
the cap-to-model theorem, and the latter the cap-to-model theorem, all of Layer 3.

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

namespace baseLanguage

/-! ### The density sentence -/

/-- The parameters of the receiving clause over a relation symbol `p`: a coface of the stage type
of `p` (the donor) and a permitted cutoff. -/
def ReceivingIndex (p : baseLanguage.{u}.Relations n) : Type (u + 1) :=
  {d : StageType.{u} ω (n + 1) // d ∈ (type p).cofaces} ×
    {c : Label.{u} // IsPermittedCutoff (ω : Ordinal.{u}) c}

/-- The parameters of the receiving clause are countably many. -/
instance (p : baseLanguage.{u}.Relations n) : Countable (ReceivingIndex p) :=
  have := StageType.countable_of_lt_omega_one (α := (ω : Ordinal.{u})) omega0_lt_omega_one (n + 1)
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
  rw [h, realize_structuralSentence_iff_toRealization, realize_receivingClause]
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

/-! The theorems of this section are wiring from their hypotheses, finite-cut receiving for the
models (row 1 of Layer 3) and the cap-to-model theorem (Layer 3); they do not discharge the
fidelity theorem (checkpoint 4) or the absence of finite models for the density sentence. -/

variable [baseLanguage.{u}.Structure M]

/-- **From the four-family sentence to the density sentence, given finite-cut receiving**: if
every model at stage `ω` on the carrier has the finite-cut receiving property, a structure
satisfying the four-family sentence satisfies the density sentence.  This is wiring from the
hypothesis, which is row 1 of Layer 3; it does not discharge the fidelity theorem. -/
theorem realize_densitySentence_of_realize_fourFamilySentence_of_hasFiniteCutReceiving
    (hreceiving : ∀ R : Realization.{u, v} ω M, R.IsModel → R.HasFiniteCutReceiving)
    (h : fourFamilySentence.Realize M) : densitySentence.Realize M := by
  obtain ⟨hT, hM⟩ := (baseLanguage.realize_fourFamilySentence_iff M).mp h
  exact (realize_densitySentence_iff M).mpr
    ⟨hT, hM.nonempty, hM.isConsistent, hM.isCovering, hreceiving _ hM⟩

/-- **From the density sentence to the four-family sentence, given the cap-to-model theorem**
for the realizations at stage `ω` on the carrier.  This is wiring from the hypothesis, which is
the cap-to-model theorem of Layer 3; it does not discharge the fidelity theorem. -/
theorem realize_fourFamilySentence_of_realize_densitySentence_of_capToModel
    (hcap : ∀ R : Realization.{u, v} ω M, Nonempty M → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel)
    (h : densitySentence.Realize M) : fourFamilySentence.Realize M := by
  obtain ⟨hT, hne, hcons, hcov, hr⟩ := (realize_densitySentence_iff M).mp h
  exact (baseLanguage.realize_fourFamilySentence_iff M).mpr
    ⟨hT, hcap _ hne hasLegalTypes_toRealization hcons hcov hr⟩

/-- **The density sentence and the four-family sentence, given finite-cut receiving and the
cap-to-model theorem**: under both hypotheses, for the models and the realizations at stage `ω` on
the carrier, the two sentences hold in the same structures.  This is wiring from the hypotheses,
row 1 and the cap-to-model theorem of Layer 3; it does not discharge the fidelity theorem
(checkpoint 4). -/
theorem realize_densitySentence_iff_fourFamilySentence_of_hasFiniteCutReceiving_of_capToModel
    (hreceiving : ∀ R : Realization.{u, v} ω M, R.IsModel → R.HasFiniteCutReceiving)
    (hcap : ∀ R : Realization.{u, v} ω M, Nonempty M → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel) :
    densitySentence.Realize M ↔ fourFamilySentence.Realize M :=
  ⟨realize_fourFamilySentence_of_realize_densitySentence_of_capToModel hcap,
    realize_densitySentence_of_realize_fourFamilySentence_of_hasFiniteCutReceiving hreceiving⟩

/-- **No finite models of the density sentence, given the cap-to-model theorem** for the
realizations at stage `ω` on the carrier: a structure satisfying the density sentence is infinite.
This is wiring from the hypothesis, the cap-to-model theorem of Layer 3; it does not discharge the
absence of finite models for the density sentence. -/
theorem infinite_of_realize_densitySentence_of_capToModel
    (hcap : ∀ R : Realization.{u, v} ω M, Nonempty M → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel)
    (h : densitySentence.Realize M) : Infinite M :=
  infinite_of_realize_fourFamilySentence
    (realize_fourFamilySentence_of_realize_densitySentence_of_capToModel hcap h)

end Fidelity

end baseLanguage

end VaughtConjecture

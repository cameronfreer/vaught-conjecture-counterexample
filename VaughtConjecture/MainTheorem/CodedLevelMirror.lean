/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CodedLevel
import VaughtConjecture.MainTheorem.ReplicatedLevelMirror

/-!
# Strong coding of the replicated coded levels

Roadmap, Layer 3 ((R3) and (R4), the replication of the full-scope cells into the mixed faces) and
Correspondence, item 1 (the strongly coded legal stage types).  All results here are native
constructions of this repository.

* `Scheme.isStronglyCoded_mirror`: every cell of the replicated scheme (`Scheme.mirror`) reads the
  row of its original, at the grade of its original; so the replicated scheme of a strongly coded
  scheme is strongly coded.
* `Seed.ALvl.CodedGood.isStronglyCoded_rep`: the replicated level (`Seed.ALvl.Good.rep`) of a coded
  good level is strongly coded.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

namespace Scheme

variable {n : ℕ} {T : Scheme.{u} n} {𝒰 : Finset (Finset (Fin n))}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ Finset.univ → ∀ U ∈ 𝒰, ¬ U ⊆ T.toCellScheme.scope c}

/-- **The replicated scheme of a strongly coded scheme is strongly coded** (native construction):
a cell reads the row of its original at the originals of the cells below it, and has the grade of
its original. -/
theorem isStronglyCoded_mirror (hT : T.rows.IsStronglyCoded) : (mirror hmix).rows.IsStronglyCoded :=
  fun _ _ ↦ hT _ _

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B j : ℕ}
  {N : I.ALvl g H j} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}

/-- **The replicated level of a coded good level is strongly coded** (native construction): the
copies of its cells of full scope at the mixed faces read the rows of their originals
(`Scheme.isStronglyCoded_mirror`). -/
theorem ALvl.CodedGood.isStronglyCoded_rep (hN : N.CodedGood B A) :
    hN.toGood.rep.rows.IsStronglyCoded :=
  Scheme.isStronglyCoded_mirror hN.stronglyCoded

end Seed

end VaughtConjecture

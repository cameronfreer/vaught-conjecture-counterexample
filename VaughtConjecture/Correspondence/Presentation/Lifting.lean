/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Correspondence.Presentation.CoherentRenaming

/-!
# Stable labels under coherent renaming: the target of the lifting step

Native construction throughout.  Write `λ_η = blockStage η`.

The lifting target (`LiftingTarget`, in `VaughtConjecture.Correspondence.Presentation.Targets`)
asks that a coherent renaming of the reductions to `λ_η` of two realizations at `λ_{η+1}` be a
coherent renaming of the realizations themselves.  Under the restricted next-block determination
(`Realization.eq_stableCandidate_stronglyCoded`) each realization is the stable candidate of its
reduction: a label at `λ_{η+1}` of a cell reducing to the formal top is the **stable label** of
the reduction (`Realization.stableLabel`), the supremum over the rooted covers of the tuple
(`Realization.ExtendsToCover`) of the provisional offsets (`StageType.provisionalOffset`).

The input the lifting step needs is the invariance of stable labels under coherent renaming,
stated here as a target (`StableLabelInvarianceTarget`).  It is not obtained merely by rewriting
equality of class readings or literal equality of the reductions (alignment gives coherent
renamings under its hypotheses; what remains is the invariance of stable labels under them): it
requires transporting each rooted cover `(m, D, f)` of the tuple in one reduction, with its
witness `s : Fin m → M`, to the rooted cover `(m, D', f)` in the other, where `D'` is the type of
`s` there, together with the cell maps along `f`: the renaming at `s` restricts along `f` to the
renaming at the tuple (`Realization.CoherentRenaming.faceCellMap_comm`), and forcing a threshold
(`StageType.ForcesThreshold`) at a cell is then to be compared at the renamed cell.
-/

universe u v

namespace VaughtConjecture

/-- **Target: stable labels are invariant under coherent renaming** (native construction).  For
exactly consistent realizations `S`, `S'` at `λ_η` and a coherent renaming `c` of `S` into `S'`,
at every tuple `u` typed by `p` in `S` and by `q` in `S'`, the stable label in `S` of a cell `d` of
`p` is the stable label in `S'` of the cell `c.cellEquiv u hp hq d` of `q`.  Stated, not proved.
-/
def StableLabelInvarianceTarget (η : Ordinal.{u}) (M : Type v) : Prop :=
  ∀ S S' : Realization.{u, v} (blockStage η) M, S.IsConsistent → S'.IsConsistent →
    ∀ (c : Realization.CoherentRenaming S S') ⦃k : ℕ⦄ (u : Fin k ↪ M)
      ⦃p q : StageType.{u} (blockStage η) k⦄ (hp : S.eval u = some p) (hq : S'.eval u = some q)
      (d : Fin p.card),
      S.stableLabel (blockStage (η + 1)) (isSuccPrelimit_blockStage η) u p d =
        S'.stableLabel (blockStage (η + 1)) (isSuccPrelimit_blockStage η) u q
          (c.cellEquiv u hp hq d)

end VaughtConjecture

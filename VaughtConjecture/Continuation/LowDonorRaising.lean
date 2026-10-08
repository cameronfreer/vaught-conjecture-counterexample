/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralRaise
import VaughtConjecture.Continuation.LowDisplay

/-!
# Donor raising at a LOW family

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the donor side of a lift);
semantic contract, items 4 and 8.

**Donor raising with the gap at a LOW family** (`StageType.IsLowFamily.donorRaisingGap`, compiled
in this repository): the donor raising with the gap on the grade-`K` faces at every arity
(`H2.donorRaisingAt`) at the source-gap context `t'` and the donor `tb` of a LOW family, with the
proper donor cells (of grade at most `K`) as low cells and every donor top of grade at most `K`
off the root and not determined by the root as a designated top.  For a private face `f` and a
donor face `R` agreeing at the root capped at `h`, with the root tops of `f` at least `c` and the
gap hypothesis, it gives a donor face `W` equal to `f` at the root, agreeing with `R` capped at
`h`, whose designated tops at least `h` in `R` are at least `c` or at most the replacement at `K`
of the low maximum of `W`.  With `c` the frontier of the private face, the second branch puts such
a top exactly at the cap (`Label.le_or_eq_of_raise`), where the LOW clause at cutoff `h` asks that
the frontier be at most `h` (`Label.max_le_of_raise`); that is what the lowering of the lost top
provides (`StageType.IsSourceGapContextAt.exists_lowering`), and it is open when the private face
is prescribed (a lift from the private coatom face).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label H2 FieldAdmission

variable {α : Ordinal.{u}} {k K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
  {o r : Fin t'.card}

/-- **Donor raising with the gap at a LOW family** (`H2.donorRaisingAt`). -/
theorem IsLowFamily.donorRaisingGap (hF : IsLowFamily K t' tb p o r) {Tops : Finset (Fin tb.card)}
    (hTops : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops) :
    DonorRaisingGap (faceCell hF.face_private) (faceCell hF.face_donor) K (LawfulAt t' K)
      (LawfulAt tb K) (rootTops' hF.face_private)
      ((univ.filter fun x ↦ tb.label x ≠ ⊤).filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops := by
  have hs : t'.IsSourceGapContextAt K ((Function.Embedding.refl (Fin k)).trans Fin.castSuccEmb)
      (Fin.last k) o r := by
    convert hF.isSourceGapContextAt
    exact Function.Embedding.ext fun _ ↦ rfl
  intro h c hh hc R f hR hf hagr hA hgap
  exact donorRaisingAt k t' hF.isLegal_private (Function.Embedding.refl (Fin k)) hs
    hF.face_private hF.isLegal_donor hF.face_donor
    (fun x hx ↦ mem_filter.mpr ⟨mem_univ x, hx⟩) hTops hh hc hR hf hagr hA hgap

end VaughtConjecture.StageType

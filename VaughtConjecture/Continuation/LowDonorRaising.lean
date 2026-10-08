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

/-- **Donor raising with the gap at a LOW family** (`H2.donorRaisingAt`).

The premises, and their status at a LOW family (a legal source-gap context with the lost point
last and a legal donor of top grade at most `K`).  `#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`; `H2.donorRaisingAt` has no hypothesis, and no extension-above,
top-grade or owner-lowering input enters it.

* the family `hF`: the input;
* the designation of `Tops` (`hTops`): met by the filter of its predicate; it leaves out the
  donor tops determined by the root (`H2.RootDetAt`) and the root tops;
* the designation of the low cells: proved (the proper donor cells of grade at most `K`);
* capped lifts from the root into the grade-`K` faces: proved (`H2.hasCappedLifts_lawfulAt'`, from
  the legality of the donor);
* closure of the grade-`K` faces under witnesses above the identity: proved (`H2.lawfulAt_map`);
* every donor cell low, designated, a root cell, or determined by the root: proved;
* the caps `h`, `c` self-visible at `K`: given by the caps of the lift;
* the faces `R`, `f` lawful at `K` and bottom above `K`: the splices of the ambient and of the
  prescription; not compiled at a LOW lift;
* the root of `f` agreeing with that of `R` capped at `h`: the capped agreement of the lift;
* the root tops of `f` at least `c`, for `c` the frontier of `f`: proved
  (`H2.frontier_le_lawfulAt`);
* the gap, every designated top of `R` above the replaced low maximum at least `min c h`: not
  compiled; argued from an active serving anchor (tops at least its cutoff, at least `h`).

The conclusion leaves a designated top at least `c` or at most the replaced low maximum of `W`
(exactly `h` at the tie, `Label.le_or_eq_of_raise`), and says nothing at the donor tops determined
by the root.  At the LOW clause of the serving profile the tie asks a frontier at most `h`
(`Label.frontier_le_of_min_eq`), and the tops determined by the root ask to be at least the
frontier.  So donor raising does not by itself give the LOW step from the private coatom. -/
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

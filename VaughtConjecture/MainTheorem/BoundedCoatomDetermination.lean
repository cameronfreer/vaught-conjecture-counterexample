/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SourceGapLastRoute

/-!
# Bounded pinned extensions and the bounded coatom form of (R2)

Roadmap, Layer 3 ((R2) of the table of 3.4, and 3.4: the exact pinned extension); semantic
contract, item 5.

**The bounded pinned extension** (`StageType.exists_pinned_extension_topGrade_le`, in
`VaughtConjecture.MainTheorem.CoatomExtensionTheorem`).  At a limit stage, for a legal `P` of top
grade at most `K`, a closed face `f` of `P` with restriction `p`, and a legal coface `d` of `p` of
top grade at most `K`, some legal one-point extension `Q` of `P` of top grade at most `K` has the
face `d` along `extendByLast f`: the exact pinned extension truncated above `K`
(`StageType.exists_truncation_topGrade_le`, in `VaughtConjecture.Continuation.TopGradeTruncation`:
capping above `K`, `StageType.capAbove`, at a cap above every label other than `⊤`, keeps both
faces literally, labels above `K` included).  Nothing about the coding of the rows is used.

**The bounded coatom form of (R2)** (`Realization.BoundedCoatomCutoffDetermination`).  The coatom
form (`Realization.CoatomCutoffDetermination`) asks determination for every legal coface `tb` of
the coatom face, also of top grade above `K`.  The bounded form asks it only for `tb` of top grade
at most `K`; it is implied by the coatom form
(`Realization.CoatomCutoffDetermination.boundedCoatom`), and no converse is claimed.  The
reduction of the coatom form uses one `tb` only, the exact pinned extension of the coatom face
along the root and the donor (`Realization.exists_mem_cofaces_restrictFace_eq`), and does not use
that the chosen coface has face `tb` (the clause is dropped in
`Realization.CoatomCutoffDetermination.exists_coface_castSucc`).  So the bounded pinned extension
replaces that `tb` by one of top grade at most `K` whenever the coatom face has top grade at most
`K` (`Realization.exists_mem_cofaces_restrictFace_eq_topGrade_le`), and the bounded form gives
cutoff determination at the first coatom for every predicate `P` whose contexts have top grade at
most `K` (`Realization.BoundedCoatomCutoffDetermination.firstCoatom`); the coatom face of such a
context has top grade at most `K` (`StageType.topGrade_le_of_restrictFace`).  Cutoff
determination follows by relabelling as for the coatom form
(`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination`).

**Source-gap contexts.**  A source-gap context of grade `K` has top grade `K`
(`StageType.IsSourceGapContext.topGrade_eq`, in `VaughtConjecture.Continuation.SourceGapContext`),
so its coatom face has top grade at most `K`
(`StageType.IsSourceGapContext.topGrade_le_of_restrictFace`).  Hence:
* the bounded coatom form with the lost point last gives cutoff determination with the coatom off
  the lost point closed
  (`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`, by the
  transposition of
  `Realization.FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`), and (R2)
  for receiving models through the compiled acquisition with the first coatom closed
  (`Realization.receivingResidualReceiving_of_boundedCoatom_sourceGapLast`);
* the bounded coatom form for source-gap contexts gives cutoff determination for them
  (`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_sourceGap`);
* the main theorem with (R2) in the bounded form with the lost point last
  (`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_boundedCoatom_sourceGapLast_markedCap`).

**Not claimed.**  That the bounded coatom form holds for the source-gap contexts: that is the
finite construction of the carrier, open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace Realization

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-! ### The bounded coatom form -/

/-- **A coface of top grade at most `K` of the coatom face through the donor**: the statement of
`exists_mem_cofaces_restrictFace_eq` with a coface of top grade at most `K`, when the coatom face
and the donor have top grade at most `K` (the bounded pinned extension). -/
theorem exists_mem_cofaces_restrictFace_eq_topGrade_le (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} (ht' : t'.IsLegal) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {K : ℕ} (hpK : p.topGrade ≤ K) (hdK : d.topGrade ≤ K) :
    ∃ tb ∈ p.cofaces, restrictFace (extendByLast g) tb = some d ∧ tb.topGrade ≤ K := by
  have hpt : restrictFace g p = some t := (restrictFace_trans t' _ g hp).trans ht
  obtain ⟨tb, htb, htbp, htbd, htbK⟩ := exists_pinned_extension_topGrade_le hα
    (ht'.restrictFace _ hp) hpt hd.1 hd.2 hpK hdK
  exact ⟨tb, ⟨htb, htbp⟩, htbd, htbK⟩

/-- **Bounded coatom cutoff determination** for `P`: the statement of
`CoatomCutoffDetermination` with the coface `tb` of the coatom face of top grade at most `K`.  At
a limit stage, over every legal `t'` on `k + 1` points with `P K t' (g.trans Fin.castSuccEmb)` and
face `p` along `Fin.castSuccEmb`, for every legal coface `tb` of `p` of top grade at most `K` whose
face along `g` followed by the new point is a donor `d` (of top grade at most `K`, as a face of
`tb`, `StageType.topGrade_le_of_restrictFace`), some coface `D'`
of `t'` with face `tb` along `extendByLast Fin.castSuccEmb` and some permitted cutoff `δ`
determine `d` over `t'` along `g.trans Fin.castSuccEmb` within the receiving family of `D'` at
`δ`.  The order of the quantifiers: the context `t'`, the root `g` and the coatom face `p` first;
then the coface `tb` with its bound; then the donor `d`; and only then the coface
`D'` and the cutoff `δ`, which may depend on all of them, and not on any member of the receiving
family.  Implied by the coatom form (`CoatomCutoffDetermination.boundedCoatom`).  Not proved for
any `P` here. -/
structure BoundedCoatomCutoffDetermination
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop) :
    Prop where
  /-- Every donor through a coface of top grade at most `K` of the coatom face is determined at a
  cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → P K t' (g.trans Fin.castSuccEmb) →
      restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, tb.topGrade ≤ K →
        ∀ d : StageType.{u} α (n + 1), restrictFace (extendByLast g) tb = some d →
          ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
            ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
              IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

variable {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}

/-- **The coatom form implies the bounded coatom form**: forget the cofaces `tb` of top grade
above `K`; the donor, a face of `tb`, has top grade at most `K`. -/
theorem CoatomCutoffDetermination.boundedCoatom (hdet : CoatomCutoffDetermination.{u} P) :
    BoundedCoatomCutoffDetermination.{u} P where
  exists_coface _ _ _ _ t' g p hα ht' hP hp tb htb htbK d htbd :=
    hdet.exists_coface t' g p hα ht' hP hp tb htb d htbd
      ((topGrade_le_of_restrictFace htbd).trans htbK)

/-- **Cutoff determination at the first coatom from the bounded coatom form**, for a predicate
`P` whose contexts of grade `K` have top grade at most `K` (`hK`).  For each input of cutoff
determination at the first coatom (context `t'`, root `g`, coatom face `p`, face `t` along the
root, donor `d` of top grade at most `K`): the coatom face has top grade at most `K` (by `hK` and
`StageType.topGrade_le_of_restrictFace`), so the bounded pinned extension gives one coface `tb` of
`p` of top grade at most `K` with face `d`; the bounded form at that `tb` gives `D'` and `δ`, and
the clause that `D'` has face `tb` is dropped. -/
theorem BoundedCoatomCutoffDetermination.firstCoatom
    (hdet : BoundedCoatomCutoffDetermination.{u} P)
    (hK : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P K t' h → t'.topGrade ≤ K) :
    FirstCoatomCutoffDetermination.{u} P where
  exists_coface _ _ _ _ t' g p hα ht' hP hp _ ht d hd hdK := by
    obtain ⟨tb, htb, htbd, htbK⟩ := exists_mem_cofaces_restrictFace_eq_topGrade_le hα ht' hp ht hd
      ((topGrade_le_of_restrictFace hp).trans (hK _ _ hP)) hdK
    obtain ⟨D', hD', -, hrest⟩ := hdet.exists_coface t' g p hα ht' hP hp tb htb htbK d htbd
    exact ⟨D', hD', hrest⟩

/-- **Cutoff determination from the bounded coatom form**, for a predicate `P` whose contexts of
grade `K` have top grade at most `K` (`hK`), whose roots are never onto (`hns`), and which is
invariant under relabelling the points of the context, with the root relabelled along (`hinv`). -/
theorem BoundedCoatomCutoffDetermination.cutoffDetermination
    (hdet : BoundedCoatomCutoffDetermination.{u} P)
    (hK : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P K t' h → t'.topGrade ≤ K)
    (hns : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P K t' h → ¬ Function.Surjective h)
    (hinv : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P K t' h → P K (t'.reindex σ) (h.trans σ.symm.toEmbedding)) :
    CutoffDetermination.{u} P :=
  (hdet.firstCoatom hK).cutoffDetermination hns hinv

/-! ### Source-gap contexts -/

/-- **Cutoff determination with the coatom off the lost point closed, from the bounded coatom form
with the lost point last**: the contexts have top grade `K`, and the lost point is transposed with
the last point (`FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`). -/
theorem BoundedCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff
    (hdet : BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h :=
  FirstCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff
    (hdet.firstCoatom fun _ _ _ _ _ _ hs ↦ hs.topGrade_eq.le)

/-- **Cutoff determination for source-gap contexts from the bounded coatom form.** -/
theorem BoundedCoatomCutoffDetermination.cutoffDetermination_sourceGap
    (hdet : BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h :=
  hdet.cutoffDetermination (fun _ _ _ _ _ _ hs ↦ hs.topGrade_eq.le)
    (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
    fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ

/-- **(R2) for receiving models from the bounded coatom form with the lost point last**: the
acquisition with the first coatom closed (`residualAcquisition_isSourceGapContextOff`) and
`BoundedCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`. -/
theorem receivingResidualReceiving_of_boundedCoatom_sourceGapLast
    (hdet : BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    ReceivingResidualReceiving.{u, w} :=
  receivingResidualReceiving_of_cutoffDetermination residualAcquisition_isSourceGapContextOff
    hdet.cutoffDetermination_isSourceGapContextOff

end Realization

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType
open Ordinal hiding univ

/-- **The thin `ℵ₁` spectrum from three finite statements, (R2) bounded with the lost point
last**: as
`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGapLast_markedCap`, with
(R2) asked only for the cofaces of the coatom face of top grade at most `K`:
* (R4): cutoff completions at the first coatom for the graded cap calibration at every `ξ < ω₁`
  (`h4`);
* (R2): bounded coatom cutoff determination for the source-gap context with the lost point last
  (`h2`);
* (R3): hollow coatom cutoff determination for the marked-cap context (`h3`).
None of the three is proved here.  The reduction of (R2) is
`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_isSourceGapContextOff`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_boundedCoatom_sourceGapLast_markedCap
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletions.{0} ξ (GradedCapCalibration.{0} ξ))
    (h2 : BoundedCoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContextLast K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_determinations
    (fun ξ hξ ↦ (h4 ξ hξ).hasCutoffStableRecoverySchemes_gradedCap)
    residualAcquisition_isSourceGapContextOff h2.cutoffDetermination_isSourceGapContextOff
    hollowAcquisition_isMarkedCapContext
    (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
      fun _ _ _ _ _ σ ht ↦ ht.reindex σ)

end MainTheorem

end VaughtConjecture

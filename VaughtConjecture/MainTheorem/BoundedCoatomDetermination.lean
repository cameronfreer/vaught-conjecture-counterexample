/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.CapGrade
import VaughtConjecture.MainTheorem.SourceGapLastRoute

/-!
# Bounded pinned extensions and the bounded coatom form of (R2)

Roadmap, Layer 3 ((R2) of the table of 3.4, and 3.4: the exact pinned extension); semantic
contract, item 5.

**Truncation above a grade** (`StageType.exists_truncation`).  At a limit stage, every stage type
`Q₀` and every grade `K` give a stage type `Q` with the scheme of `Q₀` (so legal exactly when `Q₀`
is), of top grade at most `K`, and with every face of `Q₀` of top grade at most `K` as a face
along the same embedding, literally.  It is `Q₀` capped above `K` (`StageType.capAbove`, in
`VaughtConjecture.Stage.CapGrade`) at a cap above every label of `Q₀` other than `⊤`
(`StageType.exists_cap_ne_top`): the cells of grade above `K` form an upper set and availability
relates cells of equal grades, so the capped section is lawful by [Kni26, Lemma 2.5.8] with no
side condition; the labels other than `⊤` are kept, and the cells labelled `⊤` of the capped type
are those of `Q₀` of grade at most `K` (`StageType.capAbove_label_eq_top_iff`).  Nothing about the
coding of the rows is used: the scheme is not changed.

**The bounded pinned extension** (`StageType.exists_pinned_extension_topGrade_le`).  At a limit
stage, for a legal `P` of top grade at most `K`, a closed face `f` of `P` with restriction `p`,
and a legal coface `d` of `p` of top grade at most `K`, some legal one-point extension `Q` of `P`
of top grade at most `K` has the face `d` along `extendByLast f`: truncate the exact pinned
extension (`StageType.exists_pinned_extension_of_isSuccPrelimit`) above `K`; its two faces have
top grade at most `K`, so both are kept.

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
(`StageType.IsSourceGapContextAt.topGrade_eq`), so its coatom face has top grade at most `K`
(`StageType.IsSourceGapContextLast.topGrade_le_of_restrictFace`).  Hence:
* the bounded coatom form with the lost point last gives cutoff determination with the lost point
  off the coatom (`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_off`, by the
  transposition of `Realization.FirstCoatomCutoffDetermination.cutoffDetermination_off`), and (R2)
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

## References

Capping a lawful section is [Kni26, Lemma 2.5.8].
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-! ### Truncation above a grade -/

/-- **A type capped above `K` has top grade at most `K`.** -/
theorem topGrade_capAbove_le {t : StageType.{u} α n} {K : ℕ} {c : Ordinal.{u}}
    {hc : IsSelfVisible n (c : Label)} {hcα : c < α} :
    (t.capAbove K c hc hcα).topGrade ≤ K :=
  topGrade_le_iff.mpr fun d hd ↦ (capAbove_label_eq_top_iff (t := t) (d := d)).mp hd |>.2

/-- **Truncation above a grade**: at a limit stage, a stage type `t` and a grade `K` give a stage
type with the scheme of `t`, legal exactly when `t` is, of top grade at most `K`, and with every
face of `t` of top grade at most `K` as a face along the same embedding, labels included. -/
theorem exists_truncation (hα : Order.IsSuccLimit α) (t : StageType.{u} α n) (K : ℕ) :
    ∃ q : StageType.{u} α n, q.toScheme = t.toScheme ∧ (q.IsLegal ↔ t.IsLegal) ∧
      q.topGrade ≤ K ∧ ∀ ⦃m : ℕ⦄ (f : Fin m ↪ Fin n) (p : StageType.{u} α m),
        restrictFace f t = some p → p.topGrade ≤ K → restrictFace f q = some p := by
  obtain ⟨c, hcα, hc, hct⟩ := exists_cap_ne_top hα t n
  exact ⟨t.capAbove K c hc hcα, rfl, Iff.rfl, topGrade_capAbove_le,
    fun _ _ _ hp hpK ↦ restrictFace_capAbove hct hp fun _ hi ↦ (grade_le_topGrade hi).trans hpK⟩

/-! ### The bounded pinned extension -/

/-- **The bounded pinned extension**: at a limit stage, for a legal `P` of top grade at most `K`, a
closed face `f` of `P` with restriction `p`, and a legal coface `d` of `p` of top grade at most `K`,
some legal one-point extension `Q` of `P` of top grade at most `K` has the face `d` along
`extendByLast f`.  The exact pinned extension, truncated above `K`. -/
theorem exists_pinned_extension_topGrade_le (hα : Order.IsSuccLimit α) {P : StageType.{u} α n}
    (hP : P.IsLegal) {f : Fin m ↪ Fin n} {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)}
    (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) {K : ℕ} (hPK : P.topGrade ≤ K)
    (hdK : d.topGrade ≤ K) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d ∧ Q.topGrade ≤ K := by
  obtain ⟨Q₀, hQ₀, hQP, hQd⟩ :=
    exists_pinned_extension_of_isSuccPrelimit hα.isSuccPrelimit hP hPf hd hdp
  obtain ⟨Q, -, hQl, hQK, hQf⟩ := exists_truncation hα Q₀ K
  exact ⟨Q, hQl.mpr hQ₀, hQf _ _ hQP hPK, hQf _ _ hQd hdK, hQK⟩

/-! ### The top grade of source-gap contexts -/

variable {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}

/-- A source-gap context of grade `K` has top grade `K`. -/
theorem IsSourceGapContext.topGrade_eq (hs : t'.IsSourceGapContext K h) : t'.topGrade = K :=
  let ⟨_, _, _, hs⟩ := hs
  hs.topGrade_eq

/-- A source-gap context of grade `K` with the lost point last has top grade `K`. -/
theorem IsSourceGapContextLast.topGrade_eq (hs : t'.IsSourceGapContextLast K h) :
    t'.topGrade = K :=
  let ⟨_, _, _, _, hs⟩ := hs
  hs.topGrade_eq

/-- **The faces of a source-gap context have top grade at most `K`**, the coatom face in
particular. -/
theorem IsSourceGapContextLast.topGrade_le_of_restrictFace (hs : t'.IsSourceGapContextLast K h)
    {f : Fin m ↪ Fin k} {p : StageType.{u} α m} (hp : restrictFace f t' = some p) :
    p.topGrade ≤ K :=
  (StageType.topGrade_le_of_restrictFace hp).trans hs.topGrade_eq.le

end StageType

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
face along `g` followed by the new point is a donor `d` of top grade at most `K`, some coface `D'`
of `t'` with face `tb` along `extendByLast Fin.castSuccEmb` and some permitted cutoff `δ`
determine `d` over `t'` along `g.trans Fin.castSuccEmb` within the receiving family of `D'` at
`δ`.  Implied by the coatom form (`CoatomCutoffDetermination.boundedCoatom`).  Not proved for any
`P` here. -/
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
          d.topGrade ≤ K →
            ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
              ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
                IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

variable {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}

/-- **The coatom form implies the bounded coatom form**: forget the cofaces `tb` of top grade
above `K`. -/
theorem CoatomCutoffDetermination.boundedCoatom (hdet : CoatomCutoffDetermination.{u} P) :
    BoundedCoatomCutoffDetermination.{u} P where
  exists_coface _ _ _ _ t' g p hα ht' hP hp tb htb _ d htbd hdK :=
    hdet.exists_coface t' g p hα ht' hP hp tb htb d htbd hdK

/-- **Cutoff determination at the first coatom from the bounded coatom form**, for a predicate
`P` whose contexts of grade `K` have top grade at most `K` (`hK`): the coatom face has top grade
at most `K`, so the bounded pinned extension gives a coface `tb` of top grade at most `K` through
the donor. -/
theorem BoundedCoatomCutoffDetermination.firstCoatom
    (hdet : BoundedCoatomCutoffDetermination.{u} P)
    (hK : ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P K t' h → t'.topGrade ≤ K) :
    FirstCoatomCutoffDetermination.{u} P where
  exists_coface _ _ _ _ t' g p hα ht' hP hp _ ht d hd hdK := by
    obtain ⟨tb, htb, htbd, htbK⟩ := exists_mem_cofaces_restrictFace_eq_topGrade_le hα ht' hp ht hd
      ((topGrade_le_of_restrictFace hp).trans (hK _ _ hP)) hdK
    obtain ⟨D', hD', -, hrest⟩ := hdet.exists_coface t' g p hα ht' hP hp tb htb htbK d htbd hdK
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

/-- **Cutoff determination with the lost point off the coatom, from the bounded coatom form with
the lost point last**: the contexts have top grade `K`, and the lost point is transposed with the
last point (`FirstCoatomCutoffDetermination.cutoffDetermination_off`). -/
theorem BoundedCoatomCutoffDetermination.cutoffDetermination_off
    (hdet : BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h :=
  (hdet.firstCoatom fun _ _ _ _ _ _ hs ↦ hs.topGrade_eq.le).cutoffDetermination_off

/-- **Cutoff determination for source-gap contexts from the bounded coatom form.** -/
theorem BoundedCoatomCutoffDetermination.cutoffDetermination_sourceGap
    (hdet : BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h :=
  hdet.cutoffDetermination (fun _ _ _ _ _ _ hs ↦ hs.topGrade_eq.le)
    (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
    fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ

/-- **(R2) for receiving models from the bounded coatom form with the lost point last**: the
acquisition with the first coatom closed (`residualAcquisition_isSourceGapContextOff`) and
`BoundedCoatomCutoffDetermination.cutoffDetermination_off`. -/
theorem receivingResidualReceiving_of_boundedCoatom_sourceGapLast
    (hdet : BoundedCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    ReceivingResidualReceiving.{u, w} :=
  receivingResidualReceiving_of_cutoffDetermination residualAcquisition_isSourceGapContextOff
    hdet.cutoffDetermination_off

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
`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_off`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_boundedCoatom_sourceGapLast_markedCap
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletions.{0} ξ (GradedCapCalibration.{0} ξ))
    (h2 : BoundedCoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContextLast K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_determinations
    (fun ξ hξ ↦ (h4 ξ hξ).hasCutoffStableRecoverySchemes_gradedCap)
    residualAcquisition_isSourceGapContextOff h2.cutoffDetermination_off
    hollowAcquisition_isMarkedCapContext
    (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
      fun _ _ _ _ _ σ ht ↦ ht.reindex σ)

end MainTheorem

end VaughtConjecture

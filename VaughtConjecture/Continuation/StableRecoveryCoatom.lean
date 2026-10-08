/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCapRow

/-!
# Reading coatom completions: (R4) from the coatom extension property and the last step

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)) with 3.4 (the exact pinned extension); semantic
contract, items 4 and 8.

`VaughtConjecture.Continuation.StableRecoveryFullCap` reduces (R4) to cap-reading extensions
(`StageType.HasCapReadingExtensions`, open): for a legal `T⁺` with a full-scope graded cap `b` of
grade `N` and a coface `D` of the face of `T⁺` along `f`, a legal scheme on one more point with the
schemes of `T⁺` and `D` as faces whose cells at `(univ, N)` read the new cells of `D` through the
cap.  This file splits such an extension into a chain of coatom steps, all but the last given by
the coatom extension property, and isolates the last step as a new named statement.  Each item
below is compiled in this repository (theorem named), unless marked otherwise.

**A closed coatom through a closed face** (`StageType.exists_coatom_trans_eq`, in
`VaughtConjecture.Extension.PinnedExtension`).  In a stage type on
`n + 1` points, a closed face `f` of `k ≤ n` points lies in a closed face `g` of `n` points (a
coatom): `f = f'.trans g`.  Points are added one at a time, each keeping the face closed (the
faces form a plan, `Geometry.IsPlan.exists_insert_mem`).

**The reading coatom completion** (`StageType.IsReadingCoatomCompletion`,
`StageType.HasReadingCoatomCompletions`, a new named statement, open).  Let `T⁺` be legal on
`m + 1` points, `g` a closed coatom of `T⁺` with face `p`, `tb` a legal coface of `p` (an
**intermediate coface**), `f` an embedding of `k > 0` points into the coatom with face `P` of `p`,
`D` a coface of `P` that is the face of `tb` along `f` followed by the new point, `γ < λ_{ξ+1}`,
and `b` a full-scope graded cap of `T⁺` for `D` and `γ`.  A reading coatom completion is a stage
type `Q` on `m + 2` points with the literal faces `T⁺` (along the first points) and `tb` (along
`g` followed by the new point), labels included, whose scheme is a cap-reading extension of `T⁺`
along `f.trans g` for `D` and `b` (`StageType.IsCapReadingExtension`).  So it is the coatom
extension of the pair `(T⁺, tb)` over `p`, with the extra clause that its cells at `(univ, N)`
read the new cells of `D` through the cap.  `StageType.HasReadingCoatomCompletions ξ` asks for one
at every such input; `tb` is arbitrary, in particular not controlled by the construction that
produced it.

**The reduction** (`StageType.HasReadingCoatomCompletions.hasCapReadingExtensions`).  The coatom
extension property at `λ_{ξ+1}` (`StageType.HasCoatomExtensions`, implied by hypothesis 8, the
coatom extension property with apex `StageType.HasApexCoatomExtensions`; both are compiled at the
block stages, `StageType.hasCoatomExtensions`, `StageType.hasApexCoatomExtensions_blockStage`) and
reading coatom completions at `ξ` give cap-reading extensions at `ξ`.  Take a closed coatom `g` of
`T⁺` through the face `f` of the root; the exact pinned extension
(`StageType.exists_pinned_extension`, one coatom extension for each point of the coatom outside the
root) gives a legal coface `tb` of the face of `T⁺` along `g` whose face along the root followed by
the new point is `D`; the last step is the reading coatom completion of `(T⁺, tb)`.  When `f` is
itself a coatom no coatom extension is used.

**(R4) and the continuation criterion** (`StableCappedReceiving.of_hasReadingCoatomCompletions`;
`ContinuationCriterion.of_hasReadingCoatomCompletions`, in
`VaughtConjecture.MainTheorem.ReadingCoatomCompletions`, so that this file does not import
`VaughtConjecture.MainTheorem.CapToModel`).  With
`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap` and
`StageType.HasCapReadingExtensions.hasStableRecoverySchemes`, (R4) follows from the coatom
extension property at every `λ_{ξ+1}` and reading coatom completions at every `ξ < ω₁`; with
`ContinuationCriterion.of_hasApexCoatomExtensions`, the continuation criterion follows from
hypothesis 8 at every `λ_{ξ+1}` and reading coatom completions at every `ξ < ω₁`.  So (R4) is
reduced, by a compiled implication, to hypothesis 8 (already among the named hypotheses, and
compiled, `StageType.hasApexCoatomExtensions_blockStage`; no statement that uses its proof in place
of the hypothesis is stated here) and the new named statement
`StageType.HasReadingCoatomCompletions`.  The new statement is proved at no
general input; its clause holds at two inputs, one and two coatom steps
(`VaughtConjecture.Continuation.StableRecoveryCoatomExamples`), and its reading rows exist on the
cells of the coatoms at every input (`StageType.exists_codedReadingLabelling`).

**Why the last step is stated separately** (argued, not formalized). The reading clause quantifies
over every cell at `(univ, N)`, a graded face of full scope; in a coatom extension these cells are
not cells of either coatom, so the coatom extension property says nothing about their rows. Adding
to a given coatom extension one more cell at `(univ, N)` that reads through the cap does not
obviously help: availability then picks some cell at `(univ, N)` above the cap, possibly an old one,
and making the new cell dominate the old ones asks each old row to read the new cell like the cap,
which ties the new row to the old, uncontrolled ones. So the reading coatom completion asks for a
completion of the amalgam of the last coatom pair with the rows at `(univ, N)` prescribed; none of
these arguments establishes whether it follows from hypothesis 8, and no implication either way is
compiled. On the cells of every labelled extension, in particular of the two coatoms, a reading row
exists (compiled): the coded copy of the labels capped at the label of the cap is lawful below
`(univ, N)` and reads the reference cells and the new cells of `D` in one block per label block, the
formal top like the cap and `⊥` as `⊥` (`StageType.exists_codedReadingLabelling`, in
`VaughtConjecture.Continuation.StableRecoveryCodedReading`, whatever the intermediate coface); the
cap row of `VaughtConjecture.Continuation.StableRecoveryCapRow` is another reading row on the cells
of `T⁺`. The open part is the completion at the cells of full scope.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label StageType
open Ordinal hiding univ

namespace StageType

/-! ### The reading coatom completion -/

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- A **reading coatom completion** of `T⁺` (on `m + 1` points) and an intermediate coface `tb` of
its face along the closed coatom `g`, for the coface `D` of the face of `tb` along `f` followed by
the new point and the cap `b`: a stage type `Q` on `m + 2` points whose faces along the first
points and along `g` followed by the new point are `T⁺` and `tb`, labels included, and whose scheme
is a cap-reading extension of `T⁺` along `f.trans g` for `D` and `b`
(`StageType.IsCapReadingExtension`: its cells at `(univ, N)` read the new cells of `D` through the
cap). -/
def IsReadingCoatomCompletion {α : Ordinal.{u}} (Tp : StageType.{u} α (m + 1))
    (g : Fin m ↪ Fin (m + 1)) (tb : StageType.{u} α (m + 1)) (f : Fin k ↪ Fin m)
    (D : StageType.{u} α (k + 1)) (b : Fin Tp.card) (Q : StageType.{u} α (m + 2)) : Prop :=
  restrictFace Fin.castSuccEmb Q = some Tp ∧ restrictFace (extendByLast g) Q = some tb ∧
    IsCapReadingExtension Tp (f.trans g) D b Q.toScheme

variable (ξ) in
/-- **Reading coatom completions at `ξ`** (a new named statement; open): for every legal `T⁺` at
`λ_{ξ+1}` on `m + 1` points, closed coatom `g` of `T⁺` with face `p`, legal coface `tb` of `p`,
embedding `f` of `k > 0` points into the coatom with face `P` of `p`, coface `D` of `P` that is
the face of `tb` along `f` followed by the new point, `γ < λ_{ξ+1}`, and full-scope graded cap `b`
of `T⁺` for `D` and `γ` (`StageType.IsGradedCap`), there is a reading coatom completion
(`StageType.IsReadingCoatomCompletion`).

It is the completion of the amalgam of the coatom pair `(T⁺, tb)` over `p`, with the rows of its
cells at `(univ, N)` reading the new cells of `D` through the cap.  The intermediate coface `tb` is
arbitrary.  With the coatom extension property it implies cap-reading extensions
(`StageType.HasReadingCoatomCompletions.hasCapReadingExtensions`).  It is not proved, and no
implication from or to the coatom extension property with apex (`StageType.HasApexCoatomExtensions`)
is compiled; that property does not prescribe the rows of its cells of full scope. -/
def HasReadingCoatomCompletions : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (g : Fin m ↪ Fin (m + 1))
    (p : StageType.{u} (blockStage (ξ + 1)) m) (tb : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (f : Fin k ↪ Fin m) (P : StageType.{u} (blockStage (ξ + 1)) k),
    Tp.IsLegal → restrictFace g Tp = some p → tb ∈ p.cofaces → 0 < k →
    restrictFace f p = some P → ∀ D ∈ P.cofaces, restrictFace (extendByLast f) tb = some D →
      ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
        ∀ b : Fin Tp.card, Tp.toCellScheme.scope b = univ → IsGradedCap ξ Tp D γ b →
          ∃ Q : StageType.{u} (blockStage (ξ + 1)) (m + 2),
            IsReadingCoatomCompletion Tp g tb f D b Q

/-- **Cap-reading extensions from the coatom extension property and reading coatom completions**.
At an input of `StageType.HasCapReadingExtensions ξ` the calibration forces `k < m`
(`StageType.GradedCapCalibration.lt`); a closed coatom `g` of `T⁺` contains the root
(`StageType.exists_coatom_trans_eq`); the exact pinned extension over the face of `T⁺` along `g`
(`StageType.exists_pinned_extension`, from the coatom extension property `hext`) gives an
intermediate coface `tb` with face `D`; and the reading coatom completion of `(T⁺, tb)` is a
cap-reading extension.  Both hypotheses are explicit; the coatom extension property at the block
stages is compiled (`StageType.hasCoatomExtensions`), reading coatom completions are not
proved. -/
theorem HasReadingCoatomCompletions.hasCapReadingExtensions
    (hext : HasCoatomExtensions.{u} (blockStage (ξ + 1))) (h : HasReadingCoatomCompletions ξ) :
    HasCapReadingExtensions ξ := by
  intro m k Tp f P hT hk hP D hD γ hγ b hbu hcap
  have hkm : k < m := (gradedCapCalibration_iff (f := f).mpr ⟨b, hcap⟩).lt
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfT : univ.map f ∈ Tp.toCellScheme.faces := ((restrictFace_eq_some_iff Tp f).mp hP).1
  obtain ⟨g, f', hg, rfl⟩ := Tp.exists_coatom_trans_eq f hfT (by omega)
  have hTp : restrictFace g Tp = some (Tp.comap g hg) := restrictFace_of_mem Tp g hg
  have hpP : restrictFace f' (Tp.comap g hg) = some P := (restrictFace_trans Tp g f' hTp).trans hP
  obtain ⟨tb, htb, htbp, htbD⟩ :=
    exists_pinned_extension hext (hT.restrictFace g hTp) hpP hD.1 hD.2
  obtain ⟨Q, -, -, hQ⟩ :=
    h Tp g _ tb f' P hT hTp ⟨htb, htbp⟩ hk hpP D hD htbD γ hγ b hbu hcap
  exact ⟨Q.toScheme, hQ⟩

end StageType

/-! ### (R4) and the continuation criterion -/

/-- **(R4) from the coatom extension property and reading coatom completions**: if the coatom
extension property holds at every `λ_{ξ+1}` and reading coatom completions exist at every
`ξ < ω₁`, then (R4) holds.  Through cap-reading extensions
(`StageType.HasReadingCoatomCompletions.hasCapReadingExtensions`), stable recovery schemes for the
graded cap calibration (`StageType.HasCapReadingExtensions.hasStableRecoverySchemes`) and their
acquisition (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`).  Both hypotheses are
explicit; the first is compiled (`StageType.hasCoatomExtensions` at the block stages), reading
coatom completions are not proved. -/
theorem StableCappedReceiving.of_hasReadingCoatomCompletions
    (hext : ∀ ξ < ω₁, StageType.HasCoatomExtensions.{0} (blockStage (ξ + 1)))
    (h : ∀ ξ < ω₁, StageType.HasReadingCoatomCompletions.{0} ξ) : StableCappedReceiving.{w} :=
  .of_hasStableRecoverySchemes_gradedCap fun ξ hξ ↦
    ((h ξ hξ).hasCapReadingExtensions (hext ξ hξ)).hasStableRecoverySchemes

end VaughtConjecture

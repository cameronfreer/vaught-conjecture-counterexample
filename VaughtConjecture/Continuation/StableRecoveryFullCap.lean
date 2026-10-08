/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecovery

/-!
# Stable recovery schemes with a full-scope cap

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap and the decoder of (R4)); semantic contract, item 8.

(R4) (`StableCappedReceiving`) follows from stable recovery schemes for the graded cap calibration
at every `ξ < ω₁` (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite
statement that is open.  The calibration (`StageType.GradedCapCalibration`) asks for a cell `b` of
`T⁺` (the **cap**) of grade `N > k`, labelled at least `λ_ξ + N`, with `γ < λ_ξ + N`, and for
**reference cells** of `T⁺` of grade at most `N` in the blocks of the ordinal labels of the coface
`D`; it puts no condition on the scope of the cap.  A cap has **full scope** when its scope is the
set of all points of `T⁺`.  This file shows that at a legal `T⁺` the cap can be taken of full
scope, that a full-scope cap leaves one graded face for the reading, and that the open statement
follows from a new named statement about legal extensions (one implication, compiled).  Each item
below is compiled in this repository (theorem named), unless marked otherwise.

**The cap can be taken of full scope** (`StageType.GradedCapCalibration.exists_univ_cap`).  For a
legal `T⁺`, `(univ, N)` is a graded face (a pair of a face and a grade between `1` and its number
of points); completeness (every graded face is the graded index of a cell) gives a cell there, and
availability (the third law of a lawful labelling) gives one labelled at least the cap.  It is a
cap of the same grade, with the same reference cells (`StageType.IsGradedCap`, the clauses of the
calibration at one cell).

**One graded face of grade `N`** (`Scheme.setOf_gradedFaces_univCap_eq_singleton`).  In a well
formed scheme `E` on the points of `T⁺` and a new point, for a full-scope cap of grade `N` and a
cell `e` of grade at most `N` whose scope contains the new point, `(univ, N)` is the only graded
face of grade `N` containing the cap and `e` (a face containing the first `m` points and the new
point is the ground set, `Scheme.eq_univ_of_map_castSuccEmb_subset`).  So for a full-scope cap the
informal remark of `VaughtConjecture.Continuation.StableRecovery` (the reading through the cap is
not confined to one graded index, and constrains every graded face of grade `N` containing the cap,
a reference cell and a new cell) ranges over the single graded face `(univ, N)`; that the reading
forces labels there stays argued, not formalized.

**A stable recovery scheme from the cells at `(univ, N)`**
(`StageType.IsStableRecoveryScheme.of_readsThroughCap_univ`).  This is
`StageType.IsStableRecoveryScheme.of_readsThroughCap` with the reading cell taken at the graded
face `(univ, N)`: completeness of the scheme of the coface gives such a cell, every new cell lies
below it since its grade is at most `k + 1 ≤ N`, and the cap lies below it whatever its scope.  The
remaining hypothesis: every cell at `(univ, N)` reads every new cell of `D` through the cap
(`StageType.ReadsThroughCap`).  This theorem does not use the scope of the cap; the full scope
enters through the uniqueness of the graded face above.

**The coface from legality** (`StageType.exists_mem_cofaces_reduce_of_isLegal`,
`StageType.IsStableRecoveryScheme.of_isLegal`).  A legal scheme `E` whose face along the first `m`
points is the scheme of `T⁺` carries a coface of `T⁺↓λ_ξ`: the labels of `T⁺` extend to a lawful
section of `E` (bountifulness at the cap `⊥`).  This is the first clause of
`StageType.IsStableRecoveryScheme`.

**Cap-reading extensions** (`StageType.HasCapReadingExtensions`, a new named statement, open). Every
legal `T⁺` with a full-scope cap `b` satisfying the clauses of the calibration, and every embedding
`f`, coface `D` and `γ` as in `StageType.HasStableRecoverySchemes`, has a **cap-reading extension**
(`StageType.IsCapReadingExtension`): a legal scheme `E` with face `T⁺` along the first points and
face `D` along `f` followed by the new point, in which every cell at `(univ, N)` reads every new
cell of `D` through the cap.  A cap-reading extension for a graded cap is a stable recovery scheme
(`StageType.IsCapReadingExtension.isStableRecoveryScheme`), so the new statement implies stable
recovery schemes for the graded cap calibration
(`StageType.HasCapReadingExtensions.hasStableRecoverySchemes`).  Reading through a cap depends on
the cap only through its grade, away from the formal top (`StageType.ReadsThroughCap.of_grade_eq`).
No implication from or to the coatom extension property with apex
(`StageType.HasApexCoatomExtensions`: two legal cofaces of one stage type are two faces of one legal
stage type on one more point, with a cell of full scope and full grade carrying its largest label;
still to be proved) is compiled or stated.

Tests of these statements at the twin donors and at the interior cap are in
`VaughtConjecture.Continuation.StableRecoveryFullCapExamples`.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

/-! ### The graded face of a full-scope cap -/

namespace Scheme

variable {m : ℕ}

/-- **The only graded face of a full-scope cap**.  Let `E` be a well formed scheme on `m + 1`
points, `b` a cell of its face along the first `m` points with scope all of them (a full-scope cap)
and grade `N`, and `e` a cell of `E` of grade at most `N` whose scope contains the new point
`Fin.last m`.  Then the graded faces of `E` of grade `N` below which both the cap and `e` lie are
exactly `(univ, N)`.  A reference cell of `T⁺` lies on the first `m` points, so adding it changes
nothing.  So for a full-scope cap the graded faces over which the informal remark of
`VaughtConjecture.Continuation.StableRecovery` ranges reduce to `(univ, N)`.  This is a statement
about faces only: the claim of that remark that the reading forces the labels of the new cells below
those faces stays argued, not formalized. -/
theorem setOf_gradedFaces_univCap_eq_singleton {E : Scheme.{u} (m + 1)} (hE : E.IsWellFormed)
    {b : Fin (E.comap Fin.castSuccEmb).card}
    (hbu : (E.comap Fin.castSuccEmb).toCellScheme.scope b = univ) {e : Fin E.card}
    (he : Fin.last m ∈ E.toCellScheme.scope e)
    (heb : E.toCellScheme.grade e ≤ E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b)) :
    {X | X ∈ E.toCellScheme.gradedFaces ∧
        X.2 = E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
        E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below X ∧ e ∈ E.toCellScheme.below X} =
      {((univ : Finset (Fin (m + 1))), E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b))} := by
  have hscope : E.toCellScheme.scope (E.cellMap Fin.castSuccEmb b) =
      univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
    rw [← map_comap_scope, hbu]
  ext ⟨F, j⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨-, rfl, hbX, heX⟩
    refine ⟨eq_univ_of_map_castSuccEmb_subset ?_ (heX.1 he), rfl⟩
    rw [← hscope]
    exact hbX.1
  · rintro ⟨rfl, rfl⟩
    have hgf := hE.isWellFormed.gradedIndex_mem (E.cellMap Fin.castSuccEmb b)
    refine ⟨⟨hE.univ_mem_faces, hgf.2.1, ?_⟩, rfl, ⟨subset_univ _, le_rfl⟩,
      ⟨subset_univ _, heb⟩⟩
    exact (hE.isWellFormed.grade_le_card _).trans (card_le_card (subset_univ _))

end Scheme

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-! ### A full-scope cap for the graded cap calibration -/

variable (ξ) in
/-- A **graded cap** of `T⁺` for `D` and `γ`: the clauses of `StageType.GradedCapCalibration` at
one cell `b` of `T⁺`.  The cell `b` has grade `N > k` and is labelled at least `λ_ξ + N`, with
`γ < λ_ξ + N`; every ordinal label of `D` is `μ + n` with `μ` zero or a limit and `n < N`, and
`T⁺` has a reference cell of grade at most `N` labelled `μ + i` with `i < N`. -/
def IsGradedCap (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) (b : Fin Tp.card) : Prop :=
  ((blockStage ξ + Tp.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤ Tp.label b ∧
    k < Tp.toCellScheme.grade b ∧ γ < blockStage ξ + Tp.toCellScheme.grade b ∧
    ∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
      ∃ (μ : Ordinal.{u}) (n i : ℕ) (a : Fin Tp.card), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade a ≤ Tp.toCellScheme.grade b ∧
        Tp.label a = ((μ + i : Ordinal.{u}) : Label.{u})

/-- The graded cap calibration is the existence of a graded cap. -/
theorem gradedCapCalibration_iff {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} :
    GradedCapCalibration ξ Tp f D γ ↔ ∃ b, IsGradedCap ξ Tp D γ b :=
  Iff.rfl

/-- **A graded cap can be taken of full scope, with the same grade.**  For a legal `T⁺` and a graded
cap `b` of grade `N`, the pair `(univ, N)` is a graded face (`1 ≤ N ≤ m`, since `k < N` and
`StageType.grade_le`), completeness gives a cell `s` there, and availability of the labels of `T⁺`
(the scope of `b` lies in that of `s` and the grades agree) gives a cell `u` at `(univ, N)`
labelled at least `b`.  So `u` is a graded cap of full scope, of grade `N`, with the same reference
cells. -/
theorem IsGradedCap.exists_univ_cap {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {b : Fin Tp.card}
    (hT : Tp.IsLegal) (h : IsGradedCap ξ Tp D γ b) :
    ∃ u, Tp.toCellScheme.scope u = univ ∧ Tp.toCellScheme.grade u = Tp.toCellScheme.grade b ∧
      Tp.label b ≤ Tp.label u ∧ IsGradedCap ξ Tp D γ u := by
  obtain ⟨hb, hk, hγ, href⟩ := h
  obtain ⟨s, hs⟩ := hT.isComplete ((univ : Finset (Fin m)), Tp.toCellScheme.grade b)
    ⟨Tp.univ_mem_faces, show 0 < Tp.toCellScheme.grade b by omega, by
      rw [card_univ, Fintype.card_fin]
      exact Tp.grade_le b⟩
  obtain ⟨u, hu, hbu⟩ := Tp.isLawful.availability b s
    (by rw [show Tp.toCellScheme.scope s = univ from congrArg Prod.fst hs]; exact subset_univ _)
    (congrArg Prod.snd hs).symm
  have hus : Tp.toCellScheme.gradedIndex u = ((univ : Finset (Fin m)), Tp.toCellScheme.grade b) :=
    hu.trans hs
  have hg : Tp.toCellScheme.grade u = Tp.toCellScheme.grade b := congrArg Prod.snd hus
  refine ⟨u, congrArg Prod.fst hus, hg, hbu, ?_⟩
  rw [IsGradedCap, hg]
  exact ⟨hb.trans hbu, hk, hγ, href⟩

/-- **The cap of the graded cap calibration can be taken of full scope**: for a legal `T⁺`, the
calibration holds with a cap whose scope is all points of `T⁺`
(`StageType.IsGradedCap.exists_univ_cap`, at any cap of the calibration). -/
theorem GradedCapCalibration.exists_univ_cap {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (hT : Tp.IsLegal) (h : GradedCapCalibration ξ Tp f D γ) :
    ∃ b, Tp.toCellScheme.scope b = univ ∧ IsGradedCap ξ Tp D γ b := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨u, hu, -, -, hcap⟩ := IsGradedCap.exists_univ_cap hT hb
  exact ⟨u, hu, hcap⟩

/-! ### The coface from legality -/

/-- **A legal extension carries a coface of `T⁺↓λ_ξ`**: if `E` is a legal scheme on `m + 1` points
whose first `m` points span a face with the scheme of `T⁺`, then some coface of `T⁺↓λ_ξ` lies on
`E`.  The labels of `T⁺↓λ_ξ` extend from the face to a lawful section of `E`
(`StageType.exists_isLawful_extend_label`, bountifulness at the cap `⊥`), read at `λ_ξ`. -/
theorem exists_mem_cofaces_reduce_of_isLegal {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {E : Scheme.{u} (m + 1)} (hE : E.IsLegal)
    (hc : univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces)
    (hT : E.comap Fin.castSuccEmb = Tp.toScheme) :
    ∃ q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces, q.toScheme = E := by
  obtain ⟨ρ, hρ, hext⟩ :=
    exists_isLawful_extend_label (p := Tp.reduce (isSuccPrelimit_blockStage ξ)) hE hc hT
  exact ⟨ofIsLawful (isSuccPrelimit_blockStage ξ) E hE.isWellFormed hE.isCoded ρ hρ,
    ⟨hE, restrictFace_ofIsLawful _ hc hT hext⟩, rfl⟩

/-- **A stable recovery scheme from a legal extension and recovery**: the first clause of
`StageType.IsStableRecoveryScheme` (a coface of `T⁺↓λ_ξ` on `E`) holds for every legal `E` whose
face along the first `m` points has the scheme of `T⁺`
(`StageType.exists_mem_cofaces_reduce_of_isLegal`), so only the recovery clause remains.  It has
no caller in the library yet: the cap-reading route uses
`StageType.exists_mem_cofaces_reduce_of_isLegal` directly. -/
theorem IsStableRecoveryScheme.of_isLegal {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {E : Scheme.{u} (m + 1)} (hE : E.IsLegal)
    (hc : univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces)
    (hT : E.comap Fin.castSuccEmb = Tp.toScheme)
    (hrec : ∀ Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1), Q'.toScheme = E →
      restrictFace Fin.castSuccEmb Q' = some Tp →
        ∃ Q, restrictFace (extendByLast f) Q' = some Q ∧ Q.toScheme = D.toScheme ∧
          ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
            (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
              (D.label j = ⊤ → (γ : Label.{u}) < Q.label i)) :
    Tp.IsStableRecoveryScheme f D γ E :=
  ⟨exists_mem_cofaces_reduce_of_isLegal hE hc hT, hrec⟩

/-! ### Reading at the full-scope graded face -/

/-- **A stable recovery scheme from the cells at `(univ, N)`**: the theorem
`StageType.IsStableRecoveryScheme.of_readsThroughCap` with the reading cell taken at the graded
face `(univ, N)`, `N` the grade of the cap `b`.  Let `E` carry a coface of `T⁺↓λ_ξ` and have the
scheme of `D` as its face along `f` followed by the new point; let the cap be labelled at least
`λ_ξ + N`, with `k < N` and `γ < λ_ξ + N`.  If every cell of `E` at `(univ, N)` reads every new
cell of `D` through the cap (`StageType.ReadsThroughCap`), then `E` is a stable recovery scheme.
Completeness of `E` (the scheme of a legal coface) gives a cell at `(univ, N)`; the cap lies below
it, and so does every new cell, whose grade is at most `k + 1 ≤ N`.  The scope of the cap is not
used here: for a full-scope cap, `(univ, N)` is the only graded face of grade `N` containing the
cap and a new cell (`Scheme.setOf_gradedFaces_univCap_eq_singleton`), and every graded cap can be
taken of full scope (`StageType.GradedCapCalibration.exists_univ_cap`). -/
theorem IsStableRecoveryScheme.of_readsThroughCap_univ
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {P : StageType.{u} (blockStage (ξ + 1)) k} (hP : restrictFace f Tp = some P)
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} (hD : D ∈ P.cofaces) {γ : Ordinal.{u}}
    {E : Scheme.{u} (m + 1)}
    (hq : ∃ q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces, q.toScheme = E)
    (hf : univ.map (extendByLast f) ∈ E.toCellScheme.faces)
    (hED : E.comap (extendByLast f) = D.toScheme) {b : Fin (E.comap Fin.castSuccEmb).card}
    {b₀ : Fin Tp.card} (hbb₀ : (b : ℕ) = b₀)
    (hb : ((blockStage ξ + E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) : Ordinal.{u}) :
      Label.{u}) ≤ Tp.label b₀)
    (hk : k < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b))
    (hγ : γ < blockStage ξ + E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b))
    (hread : ∀ u, E.toCellScheme.gradedIndex u =
        ((univ : Finset (Fin (m + 1))), E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b)) →
      ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
        Fin.last k ∈ D.toCellScheme.scope j →
          Tp.ReadsThroughCap E b u (E.cellMap (extendByLast f) i) (D.label j)) :
    Tp.IsStableRecoveryScheme f D γ E := by
  obtain ⟨q, ⟨hql, -⟩, hqE⟩ := id hq
  have hE : E.IsLegal := hqE ▸ hql
  set N := E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) with hN
  -- a cell `s` at the full-scope graded face of grade `N`
  obtain ⟨s, hs⟩ := hE.isComplete ((univ : Finset (Fin (m + 1))), N)
    ⟨hE.isWellFormed.univ_mem_faces, show 0 < N by omega,
      (hE.isWellFormed.isWellFormed.grade_le_card _).trans (card_le_card (subset_univ _))⟩
  have hbelow (d : Fin E.card) (hd : E.toCellScheme.grade d ≤ N) :
      d ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex s) := by
    rw [CellScheme.mem_below, hs]
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, hd⟩
  have hwf := hE.isWellFormed.comap (extendByLast f) hf
  refine of_readsThroughCap hP hD hq hf hED hbb₀ hb hγ (hbelow _ le_rfl)
    (congrArg Prod.snd hs) fun i j hij hj ↦ ⟨hbelow _ ?_, fun u hu ↦ hread u (hu.trans hs) i j
      hij hj⟩
  -- a new cell has grade at most `k + 1 ≤ N`: its grade is that of a cell of the face along `f`
  -- followed by the new point
  change (E.comap (extendByLast f)).toCellScheme.grade i ≤ N
  have := (hwf.isWellFormed.grade_le_card i).trans
    ((card_le_univ _).trans_eq (Fintype.card_fin (k + 1)))
  omega

/-! ### Cap-reading extensions -/

/-- **Reading through a cap depends on the cap only through its grade**, away from the formal top:
if the row of `u` reads `e` through the cap `b` as a cell labelled `ℓ ≠ ⊤`, then it reads `e`
through every cap `b'` of the same grade, provided `b` lies below the graded index of `u`.  Only
the clause at the formal top of `StageType.ReadsThroughCap` mentions the row of `u` at the cap. -/
theorem ReadsThroughCap.of_grade_eq {α : Ordinal.{u}} {Tp : StageType.{u} α m}
    {E : Scheme.{u} (m + 1)} {b b' : Fin (E.comap Fin.castSuccEmb).card} {u e : Fin E.card}
    {ℓ : Label.{u}} (h : Tp.ReadsThroughCap E b u e ℓ) (hℓ : ℓ ≠ ⊤)
    (hg : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b') =
      E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b))
    (hb : E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u)) :
    Tp.ReadsThroughCap E b' u e ℓ := by
  intro he _
  obtain ⟨hbot, -, hord⟩ := h he hb
  refine ⟨hbot, fun h ↦ absurd h hℓ, fun μ n hμ hℓ' ↦ ?_⟩
  rw [hg]
  exact hord μ n hμ hℓ'

/-- A **cap-reading extension** of `T⁺` along `f` for `D` and a cell `b` of `T⁺` of grade `N`: a
legal scheme `E` on `m + 1` points such that

* the first `m` points span a face of `E`, with the scheme of `T⁺`;
* `f` followed by the new point spans a face of `E`, with the scheme of `D`; and
* every cell of `E` at the graded face `(univ, N)` reads every new cell of `D` (a cell whose scope
  contains the new point) through the cap (`StageType.ReadsThroughCap`, with the cell of the face
  of `E` at the position of `b` as the cap). -/
def IsCapReadingExtension {α : Ordinal.{u}} (Tp : StageType.{u} α m) (f : Fin k ↪ Fin m)
    (D : StageType.{u} α (k + 1)) (b : Fin Tp.card) (E : Scheme.{u} (m + 1)) : Prop :=
  E.IsLegal ∧ univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces ∧
    E.comap Fin.castSuccEmb = Tp.toScheme ∧ univ.map (extendByLast f) ∈ E.toCellScheme.faces ∧
    E.comap (extendByLast f) = D.toScheme ∧
    ∃ b' : Fin (E.comap Fin.castSuccEmb).card, (b' : ℕ) = b ∧
      ∀ u, E.toCellScheme.gradedIndex u =
          ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b) →
        ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
          Fin.last k ∈ D.toCellScheme.scope j →
            Tp.ReadsThroughCap E b' u (E.cellMap (extendByLast f) i) (D.label j)

/-- **A cap-reading extension for a graded cap is a stable recovery scheme**: it carries a coface
of `T⁺↓λ_ξ` (`StageType.exists_mem_cofaces_reduce_of_isLegal`), and its cells at `(univ, N)` read
the new cells of `D` through the cap
(`StageType.IsStableRecoveryScheme.of_readsThroughCap_univ`).  The scope of `b` is not used. -/
theorem IsCapReadingExtension.isStableRecoveryScheme {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {P : StageType.{u} (blockStage (ξ + 1)) k}
    (hP : restrictFace f Tp = some P) {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)}
    (hD : D ∈ P.cofaces) {γ : Ordinal.{u}} {b : Fin Tp.card} (hcap : IsGradedCap ξ Tp D γ b)
    {E : Scheme.{u} (m + 1)} (h : IsCapReadingExtension Tp f D b E) :
    Tp.IsStableRecoveryScheme f D γ E := by
  obtain ⟨hE, hc, hcT, hf, hED, b', hb'b, hread⟩ := h
  obtain ⟨hb, hkb, hγb, -⟩ := hcap
  -- the grade of the cap in `E` is its grade in `T⁺`
  have hg : E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b') = Tp.toCellScheme.grade b :=
    Scheme.grade_congr hcT hb'b
  refine IsStableRecoveryScheme.of_readsThroughCap_univ hP hD
    (exists_mem_cofaces_reduce_of_isLegal hE hc hcT) hf hED hb'b ?_ ?_ ?_ ?_
  · rw [hg]
    exact hb
  · rw [hg]
    exact hkb
  · rw [hg]
    exact hγb
  · rw [hg]
    exact hread

variable (ξ) in
/-- **Cap-reading extensions at `ξ`** (a new named statement; open): for every legal stage type
`T⁺` at `λ_{ξ+1}` on `m` points, every embedding `f` of `k > 0` points with face `P`, every coface
`D` of `P`, every `γ < λ_{ξ+1}` and every graded cap `b` of `T⁺` for `D` and `γ`
(`StageType.IsGradedCap`) of full scope, there is a cap-reading extension of `T⁺` along `f` for
`D` and `b` (`StageType.IsCapReadingExtension`).

It is a finite statement about stage types and schemes, with no realization.  It implies stable
recovery schemes for the graded cap calibration
(`StageType.HasCapReadingExtensions.hasStableRecoverySchemes`).  Its legality and face clauses hold
for every stable recovery scheme (argued, not formalized); its reading clause, a condition on the
rows of `E` at `(univ, N)`, replaces the recovery clause over every stage type on `E`: sufficient
(`StageType.IsStableRecoveryScheme.of_readsThroughCap_univ`), not known to be necessary, and asked
for every full-scope graded cap: a strengthening at the level of rows, not a reformulation.  It is
not proved, and no implication from or to the coatom
extension property with apex (`StageType.HasApexCoatomExtensions`, still to be proved) is compiled.
-/
def HasCapReadingExtensions : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      ∀ b : Fin Tp.card, Tp.toCellScheme.scope b = univ → IsGradedCap ξ Tp D γ b →
        ∃ E : Scheme.{u} (m + 1), IsCapReadingExtension Tp f D b E

/-- **Cap-reading extensions give stable recovery schemes for the graded cap calibration.**  Given
the calibration, take a full-scope graded cap (`StageType.GradedCapCalibration.exists_univ_cap`)
and a cap-reading extension for it, a stable recovery scheme
(`StageType.IsCapReadingExtension.isStableRecoveryScheme`).  Both statements are open; this is the
implication between them only. -/
theorem HasCapReadingExtensions.hasStableRecoverySchemes (h : HasCapReadingExtensions ξ) :
    HasStableRecoverySchemes ξ (GradedCapCalibration ξ) := by
  intro m k Tp f P hT hk hP D hD γ hγ hC
  obtain ⟨b, hbu, hcap⟩ := hC.exists_univ_cap hT
  obtain ⟨E, hE⟩ := h Tp f P hT hk hP D hD γ hγ b hbu hcap
  exact ⟨E, hE.isStableRecoveryScheme hP hD hcap⟩

end StageType

end VaughtConjecture

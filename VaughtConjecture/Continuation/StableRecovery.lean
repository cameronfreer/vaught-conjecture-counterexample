/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableReceiving
import VaughtConjecture.Realization.PrivateContext

/-!
# Stable recovery schemes: over the whole occurrence, and through a reading cell

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private context, its private cap, marker and reference cells, and the decoder of (R4));
semantic contract, item 8.

(R4) (`StableCappedReceiving`) follows from acquisition of calibrated contexts and stable recovery
schemes for one calibration `C` (`StableCappedReceiving.of_stableRecoveryContexts`, in
`VaughtConjecture.Continuation.StableReceiving`).  A stable recovery scheme `E` for `T⁺`, `f`, `D`
and `γ` (`StageType.IsStableRecoveryScheme`) carries a coface of `T⁺↓λ_ξ`, and every stage type
at `λ_{ξ+1}` on `E` with face `T⁺` has, along `f` followed by the new point, a face equal to `D` off
the formal top and above `γ` at the formal top.

**The recovery clause is not vacuous** (`StageType.IsStableRecoveryScheme.exists_stageType`): the
labels of `T⁺` extend from the face to a lawful section of the scheme of the coface, so some stage
type at `λ_{ξ+1}` on `E` has face `T⁺`.

**Over the whole occurrence** (`f` the identity, no private point) a stable recovery scheme is the
scheme of `D` (`StageType.IsStableRecoveryScheme.eq_toScheme_of_refl`), and it exists only if every
stage type on that scheme with face `T⁺` agrees with `D` off the formal top
(`StageType.IsStableRecoveryScheme.label_eq_of_refl`).  Twins of `D` whose order is not fixed by
the face refute this; the marker and cap calibration (`StageType.MarkerCapCalibration`) allows
this case, and stable recovery schemes for it fail at every `ξ`
(`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`).

**The decoder at one reading cell** (`Label.TransformsTo.eq_coe_add_of_reading`,
`CellScheme.Rows.IsLawful.label_eq_of_reading`, `CellScheme.Rows.IsLawful.le_label_of_reading`,
`CellScheme.Rows.IsLawful.label_eq_bot_of_reading`).  In a lawful section `p`, let `s` be a cell
whose label is at least that of a cap `b`, and let the row of `s` read a reference cell `a` and a
new cell `e` in one block, at `ω · c + i` and `ω · c + o`, with the grades of `a` and `e` at most
that of `b`, `i < grade b` and `o ≤ grade b`.  If `p a = μ + i` (`μ` zero or a limit) and `μ + i`,
`μ + o` lie strictly below `p b`, then `p e = μ + o`.  The cap keeps the suppressor of the
witness of locality at `s` above the reference value, so the shifter sends `ω · c + i` to `μ + i`
exactly; the reference offset `i` is below the threshold `grade b`, so the guard holds at that
threshold, and visibility replacement there turns `i` into `o`.  A new cell read like the cap is
at least the cap, and a new cell read as `⊥` is `⊥`.  By availability, some cell at the graded
index of a cell of the scope and grade of the cap has a label at least the cap; so a scheme `E` all
of whose cells at one such graded index read the reference cells, the cap and the new cells of `D`
in this way recovers `D` in every stage type on `E` with face `T⁺`.  This is the decoder of the
roadmap (Layer 3, 3.3) at one row; it needs a cap whose grade exceeds the reference offsets and
the finite parts of the labels of `D`, labelled at least `λ_ξ` plus its grade, and a reference
cell for each block of a proper label of `D`.

**The graded cap calibration** (`StageType.GradedCapCalibration`): a cap `b` of grade `N > k`
labelled at least `λ_ξ + N`, with `γ < λ_ξ + N`, and for every ordinal label `μ + n` of `D`
(`μ` zero or a limit) `n < N` and a reference cell labelled `μ + i` with `i < N` (for `μ = λ_ξ`, a
marker).  It forces a private point, `k < m` (`StageType.GradedCapCalibration.lt`), so it excludes
the refutation over the whole occurrence.  The cap need not have full scope.  Its acquisition is
proved for every model that is not cover-hollow and has top-grade supremum `⊤`
(`Realization.IsModel.acquiresCalibratedContexts_gradedCap`): reference cells below `λ_ξ` by
uniformity (`Realization.IsModel.exists_extend_uniformity`), the marker by non-hollowness, the cap
by unbounded growth (`Realization.exists_coe_add_grade_le_stableCandidate_label`: a cell labelled
the formal top in `R` of grade `N` has stable label at least `λ_ξ + N`, by the order law), and one
occurrence containing them by covering, with exact consistency to carry labels and grades
(`Realization.Occurrence.exists_label_grade_eq_of_trans_eq`).  No premise beyond the hypotheses of
(R4) and the clauses of a model is used.  So (R4) follows from stable recovery schemes for the
graded cap calibration at every `ξ < ω₁`
(`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite statement that is open:
by the decoder it holds wherever a legal scheme with the coface of `T⁺↓λ_ξ`, the face of `D` along
`f` followed by the new point, and one graded index all of whose cells read as above exists, and
that existence is not proved.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Ordinal Label StageType

/-! ### Reading a new cell through a reference cell and a cap -/

namespace Label

variable {ι : Type*} {grade : ι → ℕ} {r q : ι → Label.{u}}

/-- **Reading through a reference cell under a cap** (the decoder at one row).  Let the labelling
`r` transform to `q` over the grades `grade`, and let `a`, `b`, `e` be three cells, with the
grades of `a` and `e` at most that of `b` and `i < grade b`, `o ≤ grade b`.  If `r` reads `a` and
`e` in one block, at `ω · c + i` and `ω · c + o`, and `q a = μ + i` for `μ` zero or a limit, with
`μ + i` and `μ + o` strictly below `q b`, then `q e = μ + o`.  The cap `b` keeps the suppressor
above the reference value at the grade of `a` and above `μ + o` at the grade of `e`, so the
shifter sends `ω · c + i` to `μ + i` exactly; under the guard at the threshold `grade b` it
commutes with the visibility replacement that turns `i` into `o`. -/
theorem TransformsTo.eq_coe_add_of_reading (h : TransformsTo grade r q) {μ c : Ordinal.{u}}
    (hμ : Order.IsSuccPrelimit μ) {a b e : ι} {i o : ℕ} (hab : grade a ≤ grade b)
    (hi : i < grade b) (ho : o ≤ grade b) (heb : grade e ≤ grade b)
    (hra : r a = ((ω * c + i : Ordinal.{u}) : Label.{u}))
    (hre : r e = ((ω * c + o : Ordinal.{u}) : Label.{u}))
    (hqa : q a = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hib : ((μ + i : Ordinal.{u}) : Label.{u}) < q b)
    (hob : ((μ + o : Ordinal.{u}) : Label.{u}) < q b) :
    q e = ((μ + o : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨g, σ, hw, heq⟩ := h
  have hgb : q b ≤ g (grade b) := (heq b).trans_le (min_le_right _ _)
  have hσa : σ (r a) = ((μ + i : Ordinal.{u}) : Label.{u}) := by
    have h1 := heq a
    rw [hqa] at h1
    have hg : ((μ + i : Ordinal.{u}) : Label.{u}) < g (grade a) :=
      (hib.trans_le hgb).trans_le (hw.antitone hab)
    rcases le_total (σ (r a)) (g (grade a)) with h2 | h2
    · rw [min_eq_left h2] at h1
      exact h1.symm
    · rw [min_eq_right h2] at h1
      exact absurd h1 hg.ne
  have hcm := hw.visibilityReplace_comm (r a) (grade b) (hσa ▸ (hib.trans_le hgb).le) o ho
  have hc : Order.IsSuccPrelimit (ω * c) :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)
  rw [hσa, visibilityReplace_coe_add_natCast hμ hi, hra,
    visibilityReplace_coe_add_natCast hc hi, ← hre] at hcm
  rw [heq e, hcm]
  exact min_eq_left ((hob.trans_le hgb).le.trans (hw.antitone heb))

end Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p : ι → Label.{u}}

/-- **Recovery of a proper label at a reading cell**: in a lawful section `p`, let `s` be a cell
whose label is at least that of a cell `b` (the cap), and let the row of `s` read a reference cell
`a` and a cell `e` in one block, at `ω · c + i` and `ω · c + o`, with the grades of `a` and `e` at
most that of `b` and `i < grade b`, `o ≤ grade b`.  If `p a = μ + i` (`μ` zero or a limit) and
`μ + i`, `μ + o` lie strictly below `p b`, then `p e = μ + o`. -/
theorem IsLawful.label_eq_of_reading (h : R.IsLawful p) {s a b e : ι}
    (ha : a ∈ D.below (D.gradedIndex s)) (hb : b ∈ D.below (D.gradedIndex s))
    (he : e ∈ D.below (D.gradedIndex s)) {μ c : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    {i o : ℕ} (hab : D.grade a ≤ D.grade b) (hi : i < D.grade b) (ho : o ≤ D.grade b)
    (heb : D.grade e ≤ D.grade b) (hra : R.row s ⟨a, ha⟩ = ((ω * c + i : Ordinal.{u}) : Label.{u}))
    (hre : R.row s ⟨e, he⟩ = ((ω * c + o : Ordinal.{u}) : Label.{u}))
    (hpa : p a = ((μ + i : Ordinal.{u}) : Label.{u})) (hbs : p b ≤ p s)
    (hib : ((μ + i : Ordinal.{u}) : Label.{u}) < p b)
    (hob : ((μ + o : Ordinal.{u}) : Label.{u}) < p b) :
    p e = ((μ + o : Ordinal.{u}) : Label.{u}) := by
  have hqb : min (p b) (p s) = p b := min_eq_left hbs
  have key := (h.locality s).eq_coe_add_of_reading (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (e := ⟨e, he⟩)
    hμ hab hi ho heb hra hre (by
      change min (p a) (p s) = _
      rw [min_eq_left ((hpa ▸ hib).le.trans hbs), hpa]) (by
      change _ < min (p b) (p s)
      rwa [hqb]) (by
      change _ < min (p b) (p s)
      rwa [hqb])
  change min (p e) (p s) = _ at key
  rcases le_total (p e) (p s) with h1 | h1
  · rwa [min_eq_left h1] at key
  · rw [min_eq_right h1] at key
    exact absurd key (hob.trans_le hbs).ne'

/-- **A cell read like the cap is at least the cap**: in a lawful section `p`, if the row of a cell
`s` with label at least that of `b` reads `e` as it reads `b`, and the grade of `e` is at most that
of `b`, then `p b ≤ p e`. -/
theorem IsLawful.le_label_of_reading (h : R.IsLawful p) {s b e : ι}
    (hb : b ∈ D.below (D.gradedIndex s)) (he : e ∈ D.below (D.gradedIndex s))
    (heb : D.grade e ≤ D.grade b) (hre : R.row s ⟨e, he⟩ = R.row s ⟨b, hb⟩) (hbs : p b ≤ p s) :
    p b ≤ p e := by
  have key := (h.locality s).le_of_le (d := ⟨b, hb⟩) (d' := ⟨e, he⟩) hre.symm.le heb
  change min (p b) (p s) ≤ min (p e) (p s) at key
  rw [min_eq_left hbs] at key
  exact key.trans (min_le_left _ _)

/-- **A cell read as bottom is bottom**: in a lawful section `p`, if the row of a cell `s` with a
label other than bottom reads `e` as `⊥`, then `p e = ⊥`. -/
theorem IsLawful.label_eq_bot_of_reading (h : R.IsLawful p) {s e : ι}
    (he : e ∈ D.below (D.gradedIndex s)) (hre : R.row s ⟨e, he⟩ = ⊥) (hs : p s ≠ ⊥) :
    p e = ⊥ := by
  have key := (h.locality s).eq_bot (d := ⟨e, he⟩) hre
  change min (p e) (p s) = ⊥ at key
  rcases min_eq_iff.mp key with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 hs

end CellScheme.Rows

/-- `extendByLast` of the identity is the identity. -/
theorem extendByLast_refl {m : ℕ} : extendByLast (Function.Embedding.refl (Fin m)) =
    Function.Embedding.refl (Fin (m + 1)) :=
  Function.Embedding.ext fun i ↦ by
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-! ### The recovery clause is not vacuous -/

/-- **A stable recovery scheme carries a stage type with the given face**: if `E` is a stable
recovery scheme for `T⁺`, some stage type at `λ_{ξ+1}` on `E` has face `T⁺` along the first
points, so the recovery clause is never vacuous.  The labels of `T⁺` extend from the face to a
lawful section of the scheme of the coface of `T⁺↓λ_ξ` on `E` (bountifulness of that legal coface
at the cap `⊥`), read at `λ_{ξ+1}`. -/
theorem IsStableRecoveryScheme.exists_stageType {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {E : Scheme.{u} (m + 1)} (h : Tp.IsStableRecoveryScheme f D γ E) :
    ∃ Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1), Q'.toScheme = E ∧
      restrictFace Fin.castSuccEmb Q' = some Tp := by
  obtain ⟨⟨q, ⟨hql, hqf⟩, rfl⟩, -⟩ := h
  obtain ⟨hf, hcomap⟩ := (restrictFace_eq_some_iff _ _).mp hqf
  have hp : q.toScheme.comap Fin.castSuccEmb = Tp.toScheme := congrArg StageType.toScheme hcomap
  obtain ⟨ρ, hρ, hext⟩ := exists_isLawful_extend_label hql hf hp
  exact ⟨ofIsLawful (isSuccPrelimit_blockStage (ξ + 1)) q.toScheme q.isWellFormed q.isCoded ρ hρ,
    rfl, restrictFace_ofIsLawful _ hf hp hext⟩

/-! ### The root without a private point -/

section Refl

variable {Tp : StageType.{u} (blockStage (ξ + 1)) m}
  {D : StageType.{u} (blockStage (ξ + 1)) (m + 1)} {γ : Ordinal.{u}} {E : Scheme.{u} (m + 1)}

/-- **Over the whole occurrence the recovery scheme is the scheme of the donor**: a stable recovery
scheme for `T⁺`, the identity of its points and `D` is the scheme of `D`. -/
theorem IsStableRecoveryScheme.eq_toScheme_of_refl
    (h : Tp.IsStableRecoveryScheme (Function.Embedding.refl (Fin m)) D γ E) : E = D.toScheme := by
  obtain ⟨Q', hQ'E, hQ'f⟩ := h.exists_stageType
  obtain ⟨Q, hQ, hS, -⟩ := h.2 Q' hQ'E hQ'f
  rw [extendByLast_refl, restrictFace_refl, Option.some_inj] at hQ
  rw [← hQ'E, hQ, hS]

/-- **Over the whole occurrence recovery is rigidity of the donor**: if a stable recovery scheme
exists for `T⁺`, the identity of its points and `D`, then every stage type at `λ_{ξ+1}` on the
scheme of `D` with face `T⁺` along the first points agrees with `D` at every cell where `D` is not
the formal top.  The scheme leaves no room for a private cell above the new cells. -/
theorem IsStableRecoveryScheme.label_eq_of_refl
    (h : Tp.IsStableRecoveryScheme (Function.Embedding.refl (Fin m)) D γ E)
    (Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (hQ'S : Q'.toScheme = D.toScheme)
    (hQ'f : restrictFace Fin.castSuccEmb Q' = some Tp) (i : Fin Q'.card) (j : Fin D.card)
    (hij : (i : ℕ) = j) (hj : D.label j ≠ ⊤) : Q'.label i = D.label j := by
  obtain ⟨Q, hQ, -, hl⟩ := h.2 Q' (hQ'S.trans h.eq_toScheme_of_refl.symm) hQ'f
  rw [extendByLast_refl, restrictFace_refl, Option.some_inj] at hQ
  subst hQ
  exact (hl i j hij).1 hj

end Refl

/-! ### The graded cap calibration -/

variable (ξ) in
/-- The **graded cap calibration**: a stage type `T⁺` at `λ_{ξ+1}` on `m` points has a cell `b`
(the **cap**) of grade `N` above `k`, labelled at least `λ_ξ + N`, with `γ < λ_ξ + N`; and every
ordinal label of `D` is `μ + n` with `μ` zero or a limit and `n < N`, and `T⁺` has a **reference
cell** labelled `μ + i` with `i < N` (for `μ = λ_ξ`, a **marker**).  Since the grades of `T⁺` are
at most `m`, it asks for a point outside the range of `f` (`GradedCapCalibration.lt`).  The cap
need not have full scope. -/
def GradedCapCalibration ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (_ : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  ∃ b : Fin Tp.card,
    ((blockStage ξ + Tp.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤ Tp.label b ∧
    k < Tp.toCellScheme.grade b ∧ γ < blockStage ξ + Tp.toCellScheme.grade b ∧
    ∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
      ∃ (μ : Ordinal.{u}) (n i : ℕ) (a : Fin Tp.card), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i < Tp.toCellScheme.grade b ∧
        Tp.label a = ((μ + i : Ordinal.{u}) : Label.{u})

/-- **The graded cap calibration asks for a private point**: it forces `k < m`, so it never holds
over the whole occurrence (`f` a bijection), where the marker and cap calibration fails
(`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`). -/
theorem GradedCapCalibration.lt {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapCalibration ξ Tp f D γ) : k < m := by
  obtain ⟨b, -, hk, -⟩ := h
  exact hk.trans_le (Tp.grade_le b)

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Literal faces keep labels and grades**: if `x` is the face of `y` along `f`, every cell of
the type of `x` has a cell of the type of `y` with the same label and the same grade. -/
theorem Occurrence.exists_label_grade_eq_of_trans_eq {α : Ordinal.{u}}
    {R : Realization.{u, v} α M} (hR : R.IsConsistent) {x y : R.Occurrence}
    {f : Fin x.arity ↪ Fin y.arity} (hf : f.trans y.tuple = x.tuple) (j : Fin x.type.card) :
    ∃ z : Fin y.type.card, y.type.label z = x.type.label j ∧
      y.type.toCellScheme.grade z = x.type.toCellScheme.grade j := by
  obtain ⟨hmem, h⟩ :=
    (StageType.restrictFace_eq_some_iff _ _).mp (Occurrence.restrictFace_eq_some_of_trans_eq hR hf)
  have hgrade : ∀ {t t' : StageType.{u} α x.arity} (_ : t = t') (i : Fin t.card) (i' : Fin t'.card),
      (i : ℕ) = i' → t.toCellScheme.grade i = t'.toCellScheme.grade i' := by
    rintro t _ rfl i i' hii'
    rw [Fin.ext hii']
  exact ⟨_, StageType.label_congr h (i := Fin.cast (congrArg (·.card) h).symm j) rfl,
    hgrade h (Fin.cast (congrArg (·.card) h).symm j) j rfl⟩

/-- **Unbounded growth gives a cap of every grade**: if the top-grade supremum of `R` is `⊤`, then
for every `K : ℕ` some type of the candidate has a cell of grade above `K` labelled at least
`λ_ξ + grade`: a cell labelled the formal top in `R`, whose stable label is self-visible at its
grade (the order law). -/
theorem exists_coe_add_grade_le_stableCandidate_label (hgrow : R.topGradeSup = ⊤)
    (hlaw : R.IsStablyLawful) (K : ℕ) : ∃ (x : (R.stableCandidate hlaw).Occurrence)
      (b : Fin x.type.card), K < x.type.toCellScheme.grade b ∧
        ((blockStage ξ + x.type.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤
          x.type.label b := by
  obtain ⟨x, hx⟩ : ∃ x : R.Occurrence, K < x.type.topGrade := by
    by_contra! h
    have hle : R.topGradeSup ≤ K := iSup_le fun x ↦ Nat.cast_le.mpr (h x)
    simp [hgrow] at hle
  obtain ⟨d, hd, hKd⟩ : ∃ d, x.type.label d = ⊤ ∧ K < x.type.toCellScheme.grade d := by
    by_contra! h
    exact hx.not_ge (topGrade_le_iff.mpr h)
  refine ⟨⟨x.arity, x.tuple, _, stableCandidate_eval_of_eval x.eval_tuple⟩, d, hKd, ?_⟩
  -- the label of the stable type at `d` is the stable section there
  change _ ≤ R.stableSection x.tuple x.type d
  rcases stableSection_eq_top_or_exists x.eval_tuple hd with h | ⟨i, hi, h⟩
  · rw [h]
    exact le_top
  · rw [h]
    exact_mod_cast add_le_add_right (Nat.cast_le.mpr hi) _

/-- **Acquisition of the graded cap calibration**: a model `R` at `λ_ξ` that is not cover-hollow
and has top-grade supremum `⊤` acquires calibrated contexts for the graded cap calibration.  Over
an occurrence `x` of the candidate, for a coface `D` of its type and `γ ≤ λ_ξ + K`: uniformity
gives reference cells for the blocks below `λ_ξ` of the labels of `D`
(`Realization.IsModel.exists_extend_uniformity`), non-hollowness a marker
(`Realization.exists_stableCandidate_label_eq_coe_add`), unbounded growth a cap of grade above
every finite part involved, `K` and the arity of `x`
(`Realization.exists_coe_add_grade_le_stableCandidate_label`), and covering one occurrence `w`
containing them; exact consistency of `R` and of the candidate carries the labels and the grade of
the cap to the stable type of `w`. -/
theorem IsModel.acquiresCalibratedContexts_gradedCap (hR : R.IsModel) (hnh : ¬ R.IsCoverHollow)
    (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapCalibration ξ) R hR.isStablyLawful := by
  classical
  intro x _ D _ γ hγ
  have hlim := isSuccPrelimit_blockStage ξ
  have hpos : (0 : Ordinal.{u}) < blockStage ξ :=
    Ordinal.omega0_pos.trans_le (omega0_le_blockStage ξ)
  obtain ⟨K, hK⟩ := exists_le_blockStage_add_natCast hγ
  obtain ⟨t, ht, -⟩ := exists_eq_stableType_of_stableCandidate_eval x.eval_tuple
  -- the block of each label of `D`: below `λ_ξ` (a reference cell by uniformity) or `λ_ξ` itself
  have hblock (j : Fin D.card) : ∃ ν : Ordinal.{u}, (Order.IsSuccPrelimit ν ∧ ν < blockStage ξ) ∧
      ∃ B : ℕ, ∀ o : Ordinal.{u}, D.label j = o →
        ∃ n < B, o = ν + n ∨ o = blockStage ξ + n := by
    rcases atStage_iff.mp (D.atStage j) with h | ⟨o, ho, h⟩ | h
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, 0, fun o ho ↦ by simp [h] at ho⟩
    · rw [blockStage_add_one] at ho
      rcases lt_or_ge o (blockStage ξ) with hlt | hge
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
          (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
        refine ⟨ω * (o / ω), ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
          (Ordinal.mul_div_le o ω).trans_lt hlt⟩, n + 1,
          fun o' ho' ↦ ⟨n, n.lt_succ_self, Or.inl ?_⟩⟩
        rw [← h] at ho'
        exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hn
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hge ho
        refine ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, n + 1,
          fun o' ho' ↦ ⟨n, n.lt_succ_self, Or.inr ?_⟩⟩
        rw [← h] at ho'
        exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hn
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, 0, fun o ho ↦ by simp [h] at ho⟩
  choose ν hν B hB using hblock
  obtain ⟨y, fy, K₁, B₁, hfy, -, -, hanc⟩ :=
    hR.exists_extend_uniformity ⟨x.arity, x.tuple, t, ht⟩ hpos (List.ofFn ν) fun μ hμ ↦ by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hμ
      exact hν j
  obtain ⟨z₀, a₀, i₀, ha₀⟩ := exists_stableCandidate_label_eq_coe_add hnh hR.isStablyLawful
  obtain ⟨z₁, b₁, hgb₁, hb₁⟩ := exists_coe_add_grade_le_stableCandidate_label hgrow
    hR.isStablyLawful (K + x.arity + K₁ + i₀ + univ.sup B)
  obtain ⟨w, hw⟩ := hR.isCovering.exists_subset_support
    (univ.map y.tuple ∪ univ.map z₀.tuple ∪ univ.map z₁.tuple)
  obtain ⟨g, hg⟩ := w.exists_trans_eq (subset_union_left.trans (subset_union_left.trans hw))
  obtain ⟨f₀, hf₀⟩ := w.exists_trans_eq (subset_union_right.trans (subset_union_left.trans hw))
  obtain ⟨f₁, hf₁⟩ := w.exists_trans_eq (subset_union_right.trans hw)
  have hcons := isConsistent_stableCandidate (hlaw := hR.isStablyLawful) hR.isConsistent
    hR.isCovering
  let W : (R.stableCandidate hR.isStablyLawful).Occurrence :=
    ⟨w.arity, w.tuple, _, stableCandidate_eval_of_eval w.eval_tuple⟩
  obtain ⟨a', ha'⟩ := Occurrence.exists_label_eq_of_trans_eq hcons (y := W) hf₀ a₀
  obtain ⟨b', hb'l, hb'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₁ b₁
  have hN : K + x.arity + K₁ + i₀ + univ.sup B <
      (R.stableType hR.isStablyLawful w.tuple w.type w.eval_tuple).toCellScheme.grade b' :=
    hgb₁.trans_eq hb'g.symm
  refine ⟨w, fy.trans g, by rw [Function.Embedding.trans_assoc, hg, hfy], b', ?_, by omega, ?_,
    fun j o ho ↦ ?_⟩
  · change _ ≤ W.type.label b'
    change _ ≤ W.type.toCellScheme.grade b' at hN
    rw [hb'l, show W.type.toCellScheme.grade b' = z₁.type.toCellScheme.grade b₁ from hb'g]
    exact hb₁
  · exact hK.trans_lt (add_lt_add_right (Nat.cast_lt.mpr (by omega)) _)
  · have hBj : B j ≤ univ.sup B := le_sup (mem_univ j)
    obtain ⟨n, hn, h | h⟩ := hB j o ho
    · obtain ⟨z, k, hk, hz, -⟩ := hanc (ν j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
      obtain ⟨z', hz'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hg z
      have hne : w.type.label z' ≠ ⊤ := by
        rw [hz', hz]
        exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
      refine ⟨ν j, n, k, z', (hν j).1, h, by omega, by omega, ?_⟩
      change R.stableSection w.tuple w.type z' = _
      rw [stableSection_of_ne_top hne, hz', hz]
    · exact ⟨blockStage ξ, n, i₀, a', hlim, h, by omega, by omega, ha'.trans ha₀⟩

end Realization

/-- **(R4) from stable recovery schemes for the graded cap calibration**: stable recovery schemes
for `StageType.GradedCapCalibration` at every `ξ < ω₁`, a finite statement about stage types
(open), give (R4); the acquisition is proved
(`Realization.IsModel.acquiresCalibratedContexts_gradedCap`). -/
theorem StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap
    (h : ∀ ξ < ω₁,
      StageType.HasStableRecoverySchemes.{0} ξ (StageType.GradedCapCalibration.{0} ξ)) :
    StableCappedReceiving.{w} :=
  StableCappedReceiving.of_stableRecoveryContexts ⟨fun ξ hξ ↦ ⟨_, h ξ hξ,
    fun _ _ hR hnh hgrow ↦ Realization.IsModel.acquiresCalibratedContexts_gradedCap hR hnh hgrow⟩⟩

end VaughtConjecture

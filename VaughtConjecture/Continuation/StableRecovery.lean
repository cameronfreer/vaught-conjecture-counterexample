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
at least the cap, and a new cell read as `⊥` is `⊥`.  This is the decoder of the roadmap (Layer 3,
3.3) at one row.

**A stable recovery scheme from cells reading through the cap**
(`StageType.IsStableRecoveryScheme.of_readsThroughCap`).  Let a scheme `E` carry a coface of
`T⁺↓λ_ξ` and have the scheme of `D` as its face along `f` followed by the new point, let `b` be a
cell of `T⁺` (the cap) labelled at least `λ_ξ` plus its grade `N`, with `γ < λ_ξ + N`, and let `s`
be a cell of `E` of grade `N` whose scope contains that of `b`.  If every new cell of `D` lies below
the graded index of `s`, and every cell of that graded index reads it through the cap
(`StageType.ReadsThroughCap`: as `⊥`, as the cap, or in the block of a reference cell of `T⁺`
labelled `μ + i`, with `i` and the finite part of the label below `N`), then `E` is a stable
recovery scheme for `T⁺`, `f`, `D` and `γ`.  The old cells of `D` take their labels from the face
of `T⁺` (`StageType.label_eq_of_mem_visibleCells`); at a new cell, availability against the cap
gives a cell of the graded index of `s` labelled at least the cap, and the decoder at it recovers
the label of `D`.  A reference cell read there lies below a graded index of grade `N`, so its grade
is at most `N`.  (Informal; not compiled: the hypothesis is not confined to the graded index of
`s`.  By bountifulness at the cap `⊥` and completeness, the reading forces the label of a new cell
for the lawful labellings below every graded face of grade `N` of `E` containing the cap, a
reference cell and that new cell.)

**The graded cap calibration** (`StageType.GradedCapCalibration`): a cap `b` of grade `N > k`
labelled at least `λ_ξ + N`, with `γ < λ_ξ + N`, and for every ordinal label `μ + n` of `D`
(`μ` zero or a limit) `n < N` and a reference cell of grade at most `N` labelled `μ + i` with
`i < N` (for `μ = λ_ξ`, a marker).  These are the data that a scheme reading through the cap reads.
It forces a private point, `k < m` (`StageType.GradedCapCalibration.lt`), so it excludes the
refutation over the whole occurrence.  The cap need not have full scope.  Its acquisition is
proved for every model that is not cover-hollow and has top-grade supremum `⊤`
(`Realization.IsModel.acquiresCalibratedContexts_gradedCap`): reference cells below `λ_ξ` by
uniformity (`Realization.IsModel.exists_extend_uniformity`), the marker by non-hollowness, the cap
by unbounded growth (`Realization.exists_coe_add_grade_le_stableCandidate_label`: a cell labelled
the formal top in `R` of grade `N` has stable label at least `λ_ξ + N`, by the order law) with `N`
above the arities of the occurrences of the reference cells and the marker, which bound their
grades, and one occurrence containing them by covering, with exact consistency to carry labels and
grades (`Realization.Occurrence.exists_label_grade_eq_of_trans_eq`).  No premise beyond the
hypotheses of (R4) and the clauses of a model is used.  So (R4) follows from stable recovery
schemes for the graded cap calibration at every `ξ < ω₁`
(`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite statement that is open.
By `StageType.IsStableRecoveryScheme.of_readsThroughCap` it holds at every instance at which some
scheme satisfies the hypotheses of that theorem; the calibration supplies a cap and reference cells
for such a scheme to read.  Such a scheme exists at one input, at every `ξ`
(`Continuation.StableRecoveryReading.exists_isStableRecoveryScheme_gradedCap`, in
`VaughtConjecture.Continuation.StableRecoveryReading`); its existence at every input with the
calibration is not proved.

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
      -- the labelling of locality at `s` is `d ↦ min (p d) (p s)`
      change min (p a) (p s) = _
      rw [min_eq_left ((hpa ▸ hib).le.trans hbs), hpa]) (by
      -- the same labelling, at the cap
      change _ < min (p b) (p s)
      rwa [hqb]) (by
      -- the same labelling, at the cap
      change _ < min (p b) (p s)
      rwa [hqb])
  -- the same labelling, at the new cell
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
  -- the labelling of locality at `s` is `d ↦ min (p d) (p s)`
  change min (p b) (p s) ≤ min (p e) (p s) at key
  rw [min_eq_left hbs] at key
  exact key.trans (min_le_left _ _)

/-- **A cell read as bottom is bottom**: in a lawful section `p`, if the row of a cell `s` with a
label other than bottom reads `e` as `⊥`, then `p e = ⊥`. -/
theorem IsLawful.label_eq_bot_of_reading (h : R.IsLawful p) {s e : ι}
    (he : e ∈ D.below (D.gradedIndex s)) (hre : R.row s ⟨e, he⟩ = ⊥) (hs : p s ≠ ⊥) :
    p e = ⊥ := by
  have key := (h.locality s).eq_bot (d := ⟨e, he⟩) hre
  -- the labelling of locality at `s` is `d ↦ min (p d) (p s)`
  change min (p e) (p s) = ⊥ at key
  rcases min_eq_iff.mp key with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 hs

end CellScheme.Rows

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
cell** of grade at most `N` labelled `μ + i` with `i < N` (for `μ = λ_ξ`, a **marker**).  The
decoder reads a reference cell at a cell of grade `N`
(`CellScheme.Rows.IsLawful.label_eq_of_reading` asks for its grade to be at most that of the cap);
a cell of grade above `N` lies below no graded index of grade `N`.  Since the grades of `T⁺` are
at most `m`, the calibration asks for a point outside the range of `f`
(`GradedCapCalibration.lt`).  The cap need not have full scope. -/
def GradedCapCalibration ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (_ : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  ∃ b : Fin Tp.card,
    ((blockStage ξ + Tp.toCellScheme.grade b : Ordinal.{u}) : Label.{u}) ≤ Tp.label b ∧
    k < Tp.toCellScheme.grade b ∧ γ < blockStage ξ + Tp.toCellScheme.grade b ∧
    ∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
      ∃ (μ : Ordinal.{u}) (n i : ℕ) (a : Fin Tp.card), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade a ≤ Tp.toCellScheme.grade b ∧
        Tp.label a = ((μ + i : Ordinal.{u}) : Label.{u})

/-- **The graded cap calibration asks for a private point**: it forces `k < m`, so it never holds
over the whole occurrence (`f` a bijection), where the marker and cap calibration fails
(`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`). -/
theorem GradedCapCalibration.lt {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapCalibration ξ Tp f D γ) : k < m := by
  obtain ⟨b, -, hk, -⟩ := h
  exact hk.trans_le (Tp.grade_le b)

/-! ### A stable recovery scheme from cells reading through the cap -/

/-- **A cell reads a new cell through the cap**: in a scheme `E` on `m + 1` points carrying `T⁺`
on its first points (the cells of `E.comap Fin.castSuccEmb` matched with the cells of `T⁺` at
equal positions), the row of the cell `u` reads the cell `e` as a cell labelled `ℓ`, relative to
the cap `b`: as `⊥` if `ℓ = ⊥`; as it reads `b` if `ℓ = ⊤`; and, if `ℓ = μ + n` with `μ` zero or
a limit, with `n` below the grade of `b` and at `ω · c + n`, where it reads at `ω · c + i` a
**reference cell** of `T⁺` labelled `μ + i`, with `i` below the grade of `b`. -/
def ReadsThroughCap {α : Ordinal.{u}} (Tp : StageType.{u} α m) (E : Scheme.{u} (m + 1))
    (b : Fin (E.comap Fin.castSuccEmb).card) (u e : Fin E.card) (ℓ : Label.{u}) : Prop :=
  ∀ (he : e ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u))
    (hb : E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex u)),
    (ℓ = ⊥ → E.rows.row u ⟨e, he⟩ = ⊥) ∧
    (ℓ = ⊤ → E.rows.row u ⟨e, he⟩ = E.rows.row u ⟨_, hb⟩) ∧
    ∀ (μ : Ordinal.{u}) (n : ℕ), Order.IsSuccPrelimit μ →
      ℓ = ((μ + n : Ordinal.{u}) : Label.{u}) →
        n < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
        ∃ (a : Fin (E.comap Fin.castSuccEmb).card) (a₀ : Fin Tp.card) (i : ℕ) (c : Ordinal.{u}),
          (a : ℕ) = a₀ ∧ Tp.label a₀ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
          i < E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) ∧
          ∃ ha : E.cellMap Fin.castSuccEmb a ∈
              E.toCellScheme.below (E.toCellScheme.gradedIndex u),
            E.rows.row u ⟨_, ha⟩ = ((ω * c + i : Ordinal.{u}) : Label.{u}) ∧
            E.rows.row u ⟨e, he⟩ = ((ω * c + n : Ordinal.{u}) : Label.{u})

/-- **A stable recovery scheme from cells reading through the cap** (the decoder at one row, with
availability).  Let `E` carry a coface of `T⁺↓λ_ξ` and have the scheme of `D` as its face along
`f` followed by the new point; let `b` be a cell of `T⁺` (the cap), labelled at least `λ_ξ` plus
its grade `N`, with `γ < λ_ξ + N`; and let `s` be a cell of `E` of grade `N` whose scope contains
that of `b`, such that every new cell `e` of `D` (a cell whose scope contains the new point) lies
below the graded index of `s` and every cell of that graded index reads `e` through the cap
(`StageType.ReadsThroughCap`) as a cell labelled as in `D`.  Then `E` is a stable recovery scheme
for `T⁺`, `f`, `D` and `γ`.  The old cells of `D` take their labels from the face `P` of `T⁺`;
at a new cell, availability against the cap gives a cell `u` of the graded index of `s` labelled
at least the cap, and the decoder at `u` recovers the label of `D`
(`CellScheme.Rows.IsLawful.label_eq_of_reading`, `CellScheme.Rows.IsLawful.le_label_of_reading`,
`CellScheme.Rows.IsLawful.label_eq_bot_of_reading`). -/
theorem IsStableRecoveryScheme.of_readsThroughCap {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {P : StageType.{u} (blockStage (ξ + 1)) k}
    (hP : restrictFace f Tp = some P) {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)}
    (hD : D ∈ P.cofaces) {γ : Ordinal.{u}} {E : Scheme.{u} (m + 1)}
    (hq : ∃ q ∈ (Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces, q.toScheme = E)
    (hf : univ.map (extendByLast f) ∈ E.toCellScheme.faces)
    (hED : E.comap (extendByLast f) = D.toScheme) {b : Fin (E.comap Fin.castSuccEmb).card}
    {b₀ : Fin Tp.card} (hbb₀ : (b : ℕ) = b₀)
    (hb : ((blockStage ξ + E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b) : Ordinal.{u}) :
      Label.{u}) ≤ Tp.label b₀)
    (hγ : γ < blockStage ξ + E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b)) {s : Fin E.card}
    (hbs : E.cellMap Fin.castSuccEmb b ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex s))
    (hgs : E.toCellScheme.grade s = E.toCellScheme.grade (E.cellMap Fin.castSuccEmb b))
    (hread : ∀ (i : Fin (E.comap (extendByLast f)).card) (j : Fin D.card), (i : ℕ) = j →
      Fin.last k ∈ D.toCellScheme.scope j →
        E.cellMap (extendByLast f) i ∈ E.toCellScheme.below (E.toCellScheme.gradedIndex s) ∧
        ∀ u, E.toCellScheme.gradedIndex u = E.toCellScheme.gradedIndex s →
          Tp.ReadsThroughCap E b u (E.cellMap (extendByLast f) i) (D.label j)) :
    Tp.IsStableRecoveryScheme f D γ E := by
  refine ⟨hq, fun Q' hQ'E hQ'f ↦ ?_⟩
  subst hQ'E
  refine ⟨Q'.comap (extendByLast f) hf, restrictFace_of_mem _ _ hf, hED, fun i j hij ↦ ?_⟩
  -- the labels of `Q'` at the cells of `T⁺`
  obtain ⟨_, hcT⟩ := (restrictFace_eq_some_iff _ _).mp hQ'f
  have hlab {a : Fin (Q'.toScheme.comap Fin.castSuccEmb).card} {a₀ : Fin Tp.card}
      (h : (a : ℕ) = a₀) : Q'.label (Q'.cellMap Fin.castSuccEmb a) = Tp.label a₀ :=
    label_congr hcT h
  by_cases hj : Fin.last k ∈ D.toCellScheme.scope j
  swap
  · -- an old cell: the face along `f` followed by the new point and `D` have the face `P`
    have hQP : restrictFace Fin.castSuccEmb (Q'.comap (extendByLast f) hf) = some P := by
      rw [restrictFace_trans Q' _ _ (restrictFace_of_mem Q' _ hf),
        castSuccEmb_trans_extendByLast, ← restrictFace_trans Q' _ _ hQ'f, hP]
    have hvis : j ∈ D.visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      intro x hx
      induction x using Fin.lastCases with
      | last => exact absurd hx hj
      | cast x => exact ⟨x, rfl⟩
    have hl := label_eq_of_mem_visibleCells hED hQP hD.2 hij hvis
    refine ⟨fun _ ↦ hl, fun h ↦ ?_⟩
    rw [hl, h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  -- a new cell `e`: availability against the cap `b` gives a cell `u` at the graded index of `s`
  obtain ⟨he, hread⟩ := hread i j hij hj
  have hpb := hb.trans_eq (hlab hbb₀).symm
  obtain ⟨u, hu, hbu⟩ := Q'.isLawful.availability _ s hbs.1 hgs.symm
  have hgu : Q'.toCellScheme.grade u = Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb b) :=
    (congrArg Prod.snd hu).trans hgs
  have he' : Q'.cellMap (extendByLast f) i ∈
      Q'.toCellScheme.below (Q'.toCellScheme.gradedIndex u) := by
    rwa [hu]
  have hb' : Q'.cellMap Fin.castSuccEmb b ∈
      Q'.toCellScheme.below (Q'.toCellScheme.gradedIndex u) := by
    rwa [hu]
  have heb : Q'.toCellScheme.grade (Q'.cellMap (extendByLast f) i) ≤
      Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb b) :=
    he.2.trans hgs.le
  have hpu : Q'.label u ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (hpb.trans hbu)
  obtain ⟨hbot, htop, hord⟩ := hread u hu he' hb'
  -- the label of the face at `i` is the label of `Q'` at `e`
  change (D.label j ≠ ⊤ → Q'.label (Q'.cellMap (extendByLast f) i) = D.label j) ∧
    (D.label j = ⊤ → (γ : Label.{u}) < Q'.label (Q'.cellMap (extendByLast f) i))
  rcases atStage_iff.mp (D.atStage j) with h | ⟨o, ho, h⟩ | h
  · -- `D` is `⊥` at `j`: the row reads `e` as `⊥`
    refine ⟨fun _ ↦ ?_, fun h' ↦ absurd (h.symm.trans h') bot_ne_top⟩
    rw [h]
    exact CellScheme.Rows.IsLawful.label_eq_bot_of_reading Q'.isLawful he' (hbot h) hpu
  · -- `D` is an ordinal `μ + n` at `j`: the decoder through a reference cell
    obtain ⟨μ, n, hμ, rfl, hμξ⟩ : ∃ (μ : Ordinal.{u}) (n : ℕ), Order.IsSuccPrelimit μ ∧
        o = μ + n ∧ (μ < blockStage ξ ∨ μ = blockStage ξ) := by
      rcases lt_or_ge o (blockStage ξ) with hlt | hge
      · obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
          (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
        exact ⟨ω * (o / ω), n, Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
          hn, Or.inl ((Ordinal.mul_div_le o ω).trans_lt hlt)⟩
      · rw [blockStage_add_one] at ho
        obtain ⟨n, hn⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hge ho
        exact ⟨blockStage ξ, n, isSuccPrelimit_blockStage ξ, hn, Or.inr rfl⟩
    obtain ⟨hnN, a, a₀, i', c, haa₀, ha₀, hiN, ha, hra, hre⟩ := hord μ n hμ h.symm
    -- every `μ + x` with `x` below the grade of the cap lies below the cap
    have hlt (x : ℕ) (hx : x < Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb b)) :
        ((μ + x : Ordinal.{u}) : Label.{u}) < Q'.label (Q'.cellMap Fin.castSuccEmb b) := by
      refine lt_of_lt_of_le ?_ hpb
      have : μ + x < blockStage ξ + Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb b) := by
        rcases hμξ with hμξ | rfl
        · exact ((isSuccPrelimit_blockStage ξ).add_natCast_lt hμξ x).trans_le
            le_self_add
        · exact add_lt_add_right (Nat.cast_lt.mpr hx) _
      exact_mod_cast this
    refine ⟨fun _ ↦ ?_, fun h' ↦ absurd (h.trans h') (WithBot.coe_lt_coe.mpr
      (WithTop.coe_lt_top _)).ne⟩
    rw [← h]
    exact CellScheme.Rows.IsLawful.label_eq_of_reading Q'.isLawful ha hb' he' hμ
      (ha.2.trans hgu.le) hiN hnN.le heb hra hre ((hlab haa₀).trans ha₀) hbu (hlt i' hiN)
      (hlt n hnN)
  · -- `D` is the formal top at `j`: the row reads `e` as the cap
    refine ⟨fun h' ↦ absurd h h', fun _ ↦ ?_⟩
    have hγ' : (γ : Label.{u}) <
        ((blockStage ξ + Q'.toCellScheme.grade (Q'.cellMap Fin.castSuccEmb b) : Ordinal.{u}) :
          Label.{u}) := by
      exact_mod_cast hγ
    exact hγ'.trans_le (hpb.trans (CellScheme.Rows.IsLawful.le_label_of_reading Q'.isLawful hb'
      he' heb (htop h) hbu))

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

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
gives reference cells for the blocks below `λ_ξ` of the labels of `D` in an occurrence `y`
(`Realization.IsModel.exists_extend_uniformity`), non-hollowness a marker in an occurrence `z₀`
(`Realization.exists_stableCandidate_label_eq_coe_add`), unbounded growth a cap of grade above
every finite part involved, `K`, the arity of `x` and the arities of `y` and `z₀`
(`Realization.exists_coe_add_grade_le_stableCandidate_label`), and covering one occurrence `w`
containing them; exact consistency of `R` and of the candidate carries the labels and the grades
to the stable type of `w`.  The grades of the reference cells are at most the arities of `y` and
`z₀` (`StageType.grade_le`), hence at most that of the cap. -/
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
  -- reference cells for the blocks below `λ_ξ`, in an occurrence `y` containing `x`
  obtain ⟨y, fy, K₁, B₁, hfy, -, -, hanc⟩ :=
    hR.exists_extend_uniformity ⟨x.arity, x.tuple, t, ht⟩ hpos (List.ofFn ν) fun μ hμ ↦ by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hμ
      exact hν j
  -- a marker, in an occurrence `z₀` of the candidate
  obtain ⟨z₀, a₀, i₀, ha₀⟩ := exists_stableCandidate_label_eq_coe_add hnh hR.isStablyLawful
  -- a cap, in an occurrence `z₁` of the candidate, of grade above everything involved
  obtain ⟨z₁, b₁, hgb₁, hb₁⟩ := exists_coe_add_grade_le_stableCandidate_label hgrow
    hR.isStablyLawful (K + x.arity + K₁ + i₀ + univ.sup B + y.arity + z₀.arity)
  -- one occurrence `w` containing `y`, `z₀` and `z₁`
  obtain ⟨w, hw⟩ := hR.isCovering.exists_subset_support
    (univ.map y.tuple ∪ univ.map z₀.tuple ∪ univ.map z₁.tuple)
  obtain ⟨g, hg⟩ := w.exists_trans_eq (subset_union_left.trans (subset_union_left.trans hw))
  obtain ⟨f₀, hf₀⟩ := w.exists_trans_eq (subset_union_right.trans (subset_union_left.trans hw))
  obtain ⟨f₁, hf₁⟩ := w.exists_trans_eq (subset_union_right.trans hw)
  -- the marker and the cap move to the stable type of `w` with their labels and grades
  have hcons := isConsistent_stableCandidate (hlaw := hR.isStablyLawful) hR.isConsistent
    hR.isCovering
  let W : (R.stableCandidate hR.isStablyLawful).Occurrence :=
    ⟨w.arity, w.tuple, _, stableCandidate_eval_of_eval w.eval_tuple⟩
  obtain ⟨a', ha'l, ha'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₀ a₀
  obtain ⟨b', hb'l, hb'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hcons (y := W) hf₁ b₁
  have hN : K + x.arity + K₁ + i₀ + univ.sup B + y.arity + z₀.arity <
      W.type.toCellScheme.grade b' :=
    hgb₁.trans_eq hb'g.symm
  -- the bounds on the grade of the cap, stated for `W.type`, the stable type of `w`
  have hkN : x.arity < W.type.toCellScheme.grade b' := by omega
  have hKN : K < W.type.toCellScheme.grade b' := by omega
  have hBN : univ.sup B < W.type.toCellScheme.grade b' := by omega
  have hiN : i₀ < W.type.toCellScheme.grade b' := by omega
  have hK₁N : K₁ < W.type.toCellScheme.grade b' := by omega
  have hyN : y.arity < W.type.toCellScheme.grade b' := by omega
  have ha'N : W.type.toCellScheme.grade a' ≤ W.type.toCellScheme.grade b' := by
    have := z₀.type.grade_le a₀
    omega
  refine ⟨w, fy.trans g, by rw [Function.Embedding.trans_assoc, hg, hfy], b', ?_, hkN, ?_,
    fun j o ho ↦ ?_⟩
  · -- the cap: its label in `W.type` is its label in `z₁.type`
    change _ ≤ W.type.label b'
    rw [hb'l, hb'g]
    exact hb₁
  · exact hK.trans_lt (add_lt_add_right (Nat.cast_lt.mpr hKN) _)
  · have hBj : B j ≤ univ.sup B := le_sup (mem_univ j)
    obtain ⟨n, hn, h | h⟩ := hB j o ho
    · -- a block below `λ_ξ`: the reference cell of `y`, moved to `w` with its label and grade
      obtain ⟨z, k, hk, hz, -⟩ := hanc (ν j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
      obtain ⟨z', hz', hz'g⟩ := Occurrence.exists_label_grade_eq_of_trans_eq hR.isConsistent hg z
      have hne : w.type.label z' ≠ ⊤ := by
        rw [hz', hz]
        exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne
      refine ⟨ν j, n, k, z', (hν j).1, h, (hn.trans_le hBj).trans hBN,
        hk.trans hK₁N, hz'g.trans_le ((y.type.grade_le z).trans hyN.le), ?_⟩
      -- the label of the stable type at `z'` is the stable section there
      change R.stableSection w.tuple w.type z' = _
      rw [stableSection_of_ne_top hne, hz', hz]
    · -- the block `λ_ξ`: the marker
      exact ⟨blockStage ξ, n, i₀, a', hlim, h, (hn.trans_le hBj).trans hBN, hiN, ha'N,
        ha'l.trans ha₀⟩

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

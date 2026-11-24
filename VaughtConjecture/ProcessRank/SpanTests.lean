/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanRankGlue
import VaughtConjecture.ProcessRank.SpanTargets

/-!
# The first concrete tests of the span construction

Process rank `ω₁`, the finite span of mutual rigidity: two concrete pairs on one scheme, to be
compiled through the construction before the general theorem.

**The test scheme** (`ProcessRank.testScheme`).  Two points; every subset is a face; four cells
`c₀ = ({0}, 1)`, `c₁ = ({1}, 1)`, `c₀₁ = ({0, 1}, 1)` and the apex `a = ({0, 1}, 2)`, in this
order.  Every row reads the cells below its owner through the one coded vector
`(ω * 2 + 1, ω + 1, ω * 2 + 1, ω * 2 + 2)` (`ProcessRank.testRow`).

**The pair with `K = 2`** (`ProcessRank.k2Left`, `ProcessRank.k2Right`): labels `(⊤, λ, ⊤, ⊤)`
with `λ = ω + 1` on the left and `λ = ω * 2 + 1` on the right.  The top cells are `c₀`, `c₀₁`
(grade one) and `a` (grade two); `⊤` at `c₀₁` is forced by availability from `c₀`.  This pair
exercises the mixed grades; admission at the grade one is automatic for it, since `K = 2`.

**The pair with `K = 1`** (`ProcessRank.k1Left`, `ProcessRank.k1Right`): labels `(⊤, λ, ⊤, μ)`
with `(λ, μ) = (ω + 1, ω * 3 + 2)` on the left and `(ω * 2 + 1, ω * 4 + 2)` on the right.  The top
cells are `c₀` and `c₀₁`, both of grade one, so admission is imposed on the ranks at the grade one.
The apex is proper.

**The grade-one test** (`ProcessRank.K1RankGlueTestTarget`).  In the restricted catalogue over the
test scheme with the top cells `{c₀, c₀₁}`, `K = 1` and `H = 8`, take the ambient ranks
`(3, 1, 3, 2)` on both sides (`ProcessRank.k1Ranks`; the apex, of grade two, is a field above the
cut with rank `2`), the positive table `⊥, ω + 1, ω + 1, ω * 2 + 1, …` (`ProcessRank.k1Table`;
the ranks `1` and `2` have the same value), the cap `ω * 2 + 1` (first reached at the rank `3`),
and the prescription `ω * 3 + 1` at `c₀` on the right side.  Keeping the left side and ranking the
new right values densely from `3` gives the ranks `(4, 1, 4, 2)` on the right
(`ProcessRank.k1NaiveRanks`), which is separated with unequal designated ranks, hence **not
admitted** (`ProcessRank.not_isAdmitted_k1NaiveRanks`, proved).  The target asks for the
conclusion of the restricted rank glue at this instance.

Stated: the existence and legality of the two pairs, their spans of mutual rigidity on four points
along embeddings with disjoint ranges, and the grade-one test.  Proved: the ambient ranks are
admitted, the kept-side ranks are not.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- The coded vector read by every row of the test scheme. -/
noncomputable def testRow : Fin 4 → Label.{u} :=
  ![((ω * 2 + 1 : Ordinal.{u}) : Label.{u}), ((ω + 1 : Ordinal.{u}) : Label.{u}),
    ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}), ((ω * 2 + 2 : Ordinal.{u}) : Label.{u})]

/-- **The test scheme**: two points, every subset a face, the cells `({0}, 1)`, `({1}, 1)`,
`({0, 1}, 1)` and `({0, 1}, 2)`, every row reading `testRow`. -/
noncomputable def testScheme : Scheme.{u} 2 where
  card := 4
  toCellScheme := ⟨univ, univ, ![{0}, {1}, univ, univ], ![1, 1, 1, 2]⟩
  rows := ⟨fun _ t ↦ testRow t.1⟩

/-- A stage type on two points is the **test type** with labels `ℓ`: its scheme is the test
scheme and its labels are `ℓ`, at equal positions. -/
def IsTestType {α : Ordinal.{u}} (t : StageType.{u} α 2) (ℓ : Fin 4 → Label.{u}) : Prop :=
  t.toScheme = testScheme ∧ ∀ (i : Fin t.card) (j : Fin 4), (i : ℕ) = j → t.label i = ℓ j

/-- The left labels of the pair with `K = 2`: `(⊤, ω + 1, ⊤, ⊤)`. -/
noncomputable def k2Left : Fin 4 → Label.{u} := ![⊤, ((ω + 1 : Ordinal.{u}) : Label.{u}), ⊤, ⊤]

/-- The right labels of the pair with `K = 2`: `(⊤, ω * 2 + 1, ⊤, ⊤)`. -/
noncomputable def k2Right : Fin 4 → Label.{u} :=
  ![⊤, ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}), ⊤, ⊤]

/-- The left labels of the pair with `K = 1`: `(⊤, ω + 1, ⊤, ω * 3 + 2)`. -/
noncomputable def k1Left : Fin 4 → Label.{u} :=
  ![⊤, ((ω + 1 : Ordinal.{u}) : Label.{u}), ⊤, ((ω * 3 + 2 : Ordinal.{u}) : Label.{u})]

/-- The right labels of the pair with `K = 1`: `(⊤, ω * 2 + 1, ⊤, ω * 4 + 2)`. -/
noncomputable def k1Right : Fin 4 → Label.{u} :=
  ![⊤, ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}), ⊤, ((ω * 4 + 2 : Ordinal.{u}) : Label.{u})]

/-- **Target: the test pair with labels `ℓp` and `ℓq` exists and is legal**, at the stage
`ω ^ 2`.  Stated. -/
def TestPairTarget (ℓp ℓq : Fin 4 → Label.{u}) : Prop :=
  ∃ p q : StageType.{u} (ω ^ 2) 2, IsTestType p ℓp ∧ IsTestType q ℓq ∧ p.IsLegal ∧ q.IsLegal

/-- **Target: the test pair with labels `ℓp` and `ℓq` has a span of mutual rigidity** on four
points along embeddings with disjoint ranges, at the stage `ω ^ 2`.  Stated. -/
def TestSpanTarget (ℓp ℓq : Fin 4 → Label.{u}) : Prop :=
  ∀ p q : StageType.{u} (ω ^ 2) 2, IsTestType p ℓp → IsTestType q ℓq → p.IsLegal → q.IsLegal →
    ∃ (D : StageType.{u} (ω ^ 2) (2 + 2)) (i j : Fin 2 ↪ Fin (2 + 2)),
      Disjoint (Set.range i) (Set.range j) ∧ StageType.IsMutualRigidSpan p q D i j

/-- **Target: the pair with `K = 2` exists and is legal.**  Stated. -/
def K2PairTarget : Prop := TestPairTarget.{u} k2Left k2Right

/-- **Target: the span of the pair with `K = 2`.**  Stated. -/
def K2SpanTarget : Prop := TestSpanTarget.{u} k2Left k2Right

/-- **Target: the pair with `K = 1` exists and is legal.**  Stated. -/
def K1PairTarget : Prop := TestPairTarget.{u} k1Left k1Right

/-- **Target: the span of the pair with `K = 1`.**  Stated. -/
def K1SpanTarget : Prop := TestSpanTarget.{u} k1Left k1Right

/-! ### The grade-one test -/

/-- The top cells of the pair with `K = 1`: `c₀` and `c₀₁`. -/
def k1Tops : Set (Fin 4) := {0, 2}

/-- The ambient ranks: `(3, 1, 3, 2)` on both sides. -/
def k1Ranks : Fin 4 ⊕ Fin 4 → ℕ := Sum.elim ![3, 1, 3, 2] ![3, 1, 3, 2]

/-- The ranks obtained by keeping the left side and ranking the new right values from `3`:
`(3, 1, 3, 2)` on the left, `(4, 1, 4, 2)` on the right. -/
def k1NaiveRanks : Fin 4 ⊕ Fin 4 → ℕ := Sum.elim ![3, 1, 3, 2] ![4, 1, 4, 2]

/-- The positive table of the test: `⊥` at `0`, `ω + 1` at `1` and `2`, `ω * 2 + 1` above. -/
noncomputable def k1Table (i : ℕ) : Label.{u} :=
  if i = 0 then ⊥ else if i ≤ 2 then ((ω + 1 : Ordinal.{u}) : Label.{u})
    else ((ω * 2 + 1 : Ordinal.{u}) : Label.{u})

/-- The cap of the test, `ω * 2 + 1`. -/
noncomputable def k1Cap : Label.{u} := ((ω * 2 + 1 : Ordinal.{u}) : Label.{u})

/-- The graded face of the prescription: `({0}, 1)`. -/
def k1Face : Finset (Fin 2) × ℕ := ({0}, 1)

/-- The prescription: `ω * 3 + 1` at `c₀`, on the right side. -/
noncomputable def k1Prescription : testScheme.{u}.toCellScheme.below k1Face → Label.{u} :=
  fun _ ↦ ((ω * 3 + 1 : Ordinal.{u}) : Label.{u})

/-- **Target: the restricted rank glue at the grade-one test**: the ambient ranks are a member of
the restricted catalogue over the test scheme (top cells `{c₀, c₀₁}`, `K = 1`, `H = 8`), and some
member and positive table keep the ranks and the table below `3`, agree with the table capped at
the cap, agree with the ambient state capped at the cap at every field, and read the prescription
on the right side.  Stated. -/
def K1RankGlueTestTarget : Prop :=
  IsSpanRankMember testScheme.{u} 8 k1Tops 1 k1Ranks ∧
    ∃ (a' : Fin 4 ⊕ Fin 4 → ℕ) (F' : ℕ → Label.{u}),
      IsSpanRankMember testScheme.{u} 8 k1Tops 1 a' ∧ IsPositiveTable 8 F' ∧
      (∀ x, min (k1Ranks x) 3 = min (a' x) 3) ∧ (∀ i < 3, F' i = k1Table i) ∧
      (∀ i ≤ 8, min (F' i) k1Cap = min (k1Table i) k1Cap) ∧
      (∀ x, min (F' (a' x)) k1Cap = min (k1Table (k1Ranks x)) k1Cap) ∧
      ∀ d : testScheme.{u}.toCellScheme.below k1Face,
        F' (a' (sideField true d.1)) = k1Prescription d

/-- A field is designated for the test top cells exactly when its cell is `c₀` or `c₀₁`. -/
theorem isDesignated_k1Tops_iff (x : Fin 4 ⊕ Fin 4) :
    IsDesignated k1Tops x ↔ fieldCell x = 0 ∨ fieldCell x = 2 :=
  Iff.rfl

/-- The ambient ranks are separated: the designated ranks `3` are above the others. -/
theorem isSeparated_k1Ranks : IsSeparated k1Tops k1Ranks := by
  unfold IsSeparated
  simp only [isDesignated_k1Tops_iff]
  decide

/-- **The ambient ranks are admitted** at the grade one. -/
theorem isAdmitted_k1Ranks : IsAdmitted k1Tops 1 1 k1Ranks := by
  rintro - - d hd
  fin_cases d <;> simp_all [k1Tops, k1Ranks]

/-- The kept-side ranks are separated. -/
theorem isSeparated_k1NaiveRanks : IsSeparated k1Tops k1NaiveRanks := by
  unfold IsSeparated
  simp only [isDesignated_k1Tops_iff]
  decide

/-- **Keeping the other side breaks admission**: the kept-side ranks are separated, and the two
copies of `c₀` have the ranks `3` and `4`. -/
theorem not_isAdmitted_k1NaiveRanks : ¬ IsAdmitted k1Tops 1 1 k1NaiveRanks := fun h ↦ by
  have := h le_rfl isSeparated_k1NaiveRanks 0 (by simp [k1Tops])
  simp [k1NaiveRanks] at this

end VaughtConjecture.ProcessRank

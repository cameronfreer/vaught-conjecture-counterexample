/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanRankGlue
import VaughtConjecture.ProcessRank.SpanTargets
import VaughtConjecture.Geometry.IntervalPlan

/-!
# The first concrete tests of the span construction

Process rank `ω₁`, the finite span of mutual rigidity: two concrete pairs on one scheme, to be
compiled through the construction before the general theorem.

**The test scheme** (`ProcessRank.testScheme`).  Two points; every subset is a face (the interval
plan of `Fin 2`); four cells
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

Stated: the spans of mutual rigidity of the two pairs on four points along embeddings with
disjoint ranges.  Proved: the existence and legality of the two pairs (`ProcessRank.k2Pair` and
`ProcessRank.k1Pair`, in `VaughtConjecture.ProcessRank.SpanTestLegal`); the ambient ranks are
admitted, the kept-side ranks are not; the test scheme is well formed and the test row is a lawful
section of it (`ProcessRank.isLawful_testRow`, by the identity witness); the ambient ranks are a
member of the restricted catalogue (`ProcessRank.isSpanRankMember_k1Ranks`, lawful tables by order
interpolation against the test row); and the grade-one test (`ProcessRank.k1RankGlueTest`): the
ambient ranks themselves, with the table kept below the rank `3` and equal to the prescribed
`ω * 3 + 1` from the rank `3` on, meet the conclusion of the restricted rank glue.
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
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, ![{0}, {1}, univ, univ], ![1, 1, 1, 2]⟩
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

/-- **Target: the pair with `K = 2` exists and is legal.**  Proved (`ProcessRank.k2Pair`). -/
def K2PairTarget : Prop := TestPairTarget.{u} k2Left k2Right

/-- **Target: the span of the pair with `K = 2`.**  Stated. -/
def K2SpanTarget : Prop := TestSpanTarget.{u} k2Left k2Right

/-- **Target: the pair with `K = 1` exists and is legal.**  Proved (`ProcessRank.k1Pair`). -/
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
on the right side.  Proved (`ProcessRank.k1RankGlueTest`). -/
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

/-! ### The ambient ranks are a member of the restricted catalogue -/

/-- The scopes of the cells of the test scheme. -/
def testScope : Fin 4 → Finset (Fin 2) := ![{0}, {1}, univ, univ]

/-- The grades of the cells of the test scheme. -/
def testGrade : Fin 4 → ℕ := ![1, 1, 1, 2]

theorem mem_below_testScheme {d : Fin 4} {X : Finset (Fin 2) × ℕ} :
    d ∈ testScheme.{u}.toCellScheme.below X ↔ testScope d ⊆ X.1 ∧ testGrade d ≤ X.2 :=
  Iff.rfl

theorem gradedIndex_testScheme (d : Fin 4) :
    testScheme.{u}.toCellScheme.gradedIndex d = (testScope d, testGrade d) :=
  rfl

/-- The test scheme is well formed. -/
theorem isWellFormed_testScheme : testScheme.{u}.IsWellFormed :=
  ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    change (testScope d ∈ Geometry.intervalPlan univ ∧ 0 < testGrade d ∧
      testGrade d ≤ #(testScope d))
    fin_cases d <;> decide⟩⟩

/-- `ω * k` is zero or a limit. -/
theorem isSuccPrelimit_omega0_mul (k : ℕ) : Order.IsSuccPrelimit (ω * k : Ordinal.{u}) :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)

/-- `ω * k + j` is self-visible at `i ≤ j`. -/
theorem isSelfVisible_omega0_mul_add {i j : ℕ} (k : ℕ) (h : i ≤ j) :
    IsSelfVisible i ((ω * k + j : Ordinal.{u}) : Label.{u}) :=
  (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul k)).mpr h

theorem isSelfVisible_omega0_add_one : IsSelfVisible 1 ((ω + 1 : Ordinal.{u}) : Label.{u}) := by
  simpa using isSelfVisible_omega0_mul_add.{u} (i := 1) (j := 1) 1 le_rfl

theorem omega0_add_one_lt :
    ((ω + 1 : Ordinal.{u}) : Label.{u}) < ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) := by
  refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
  have hlt : (ω : Ordinal.{u}) < ω * 2 := by simp
  have h := (isSuccPrelimit_omega0_mul.{u} 2).succ_lt (by exact_mod_cast hlt)
  rw [Order.succ_eq_add_one] at h
  exact_mod_cast h.trans_le le_self_add

theorem omega0_mul_two_add_one_le :
    ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) ≤ ((ω * 2 + 2 : Ordinal.{u}) : Label.{u}) := by
  refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
  gcongr
  exact one_le_two

theorem omega0_mul_two_add_one_le_three :
    ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) ≤ ((ω * 3 + 1 : Ordinal.{u}) : Label.{u}) := by
  refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
  gcongr
  exact_mod_cast (by decide : (2 : ℕ) ≤ 3)

theorem isSelfVisible_omega0_mul_two_add_one :
    IsSelfVisible 1 ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) := by
  simpa using isSelfVisible_omega0_mul_add.{u} (i := 1) (j := 1) 2 le_rfl

theorem isSelfVisible_omega0_mul_two_add_two :
    IsSelfVisible 2 ((ω * 2 + 2 : Ordinal.{u}) : Label.{u}) := by
  simpa using isSelfVisible_omega0_mul_add.{u} (i := 2) (j := 2) 2 le_rfl

theorem isSelfVisible_omega0_mul_three_add_one :
    IsSelfVisible 1 ((ω * 3 + 1 : Ordinal.{u}) : Label.{u}) := by
  simpa using isSelfVisible_omega0_mul_add.{u} (i := 1) (j := 1) 3 le_rfl

/-- Every value of the test row is self-visible at the grade of its cell. -/
theorem isSelfVisible_testRow (d : Fin 4) : IsSelfVisible (testGrade d) (testRow.{u} d) := by
  fin_cases d
  · exact isSelfVisible_omega0_mul_two_add_one
  · exact isSelfVisible_omega0_add_one
  · exact isSelfVisible_omega0_mul_two_add_one
  · exact isSelfVisible_omega0_mul_two_add_two

/-- Every value of the test row read below a cell is at most the value of the cell. -/
theorem testRow_le_of_mem_below {s d : Fin 4} (hd : testScope d ⊆ testScope s ∧
    testGrade d ≤ testGrade s) : testRow.{u} d ≤ testRow s := by
  have h₁ := omega0_add_one_lt.{u}
  have h₂ := omega0_mul_two_add_one_le.{u}
  revert hd
  fin_cases s <;> fin_cases d <;>
    first
    | exact fun _ ↦ le_rfl
    | exact fun hd ↦ absurd hd (by decide)
    | exact fun _ ↦ h₁.le
    | exact fun _ ↦ h₂
    | exact fun _ ↦ h₁.le.trans h₂

/-- **The test row is a lawful section** of the test scheme, by the identity witness. -/
theorem isLawful_testRow : testScheme.{u}.rows.IsLawful testRow where
  orderly d := isSelfVisible_testRow d
  locality s := ⟨fun _ ↦ ⊤, id, IsWitness.id_top, fun d ↦ by
    simp only [id, min_top_right]
    exact min_eq_left (testRow_le_of_mem_below d.2)⟩
  availability s t hst hg := ⟨t, rfl, testRow_le_of_mem_below ⟨hst, hg.le⟩⟩

/-- The ambient ranks of one side, `(3, 1, 3, 2)`. -/
def k1SideRanks : Fin 4 → ℕ := ![3, 1, 3, 2]

theorem k1Ranks_sideField (b : Bool) (d : Fin 4) : k1Ranks (sideField b d) = k1SideRanks d := by
  cases b <;> rfl

/-- On the cells of grade one, the ranks follow the order of the test row. -/
theorem k1SideRanks_le_of_testRow_le {d e : Fin 4} (hd : testGrade d = 1) (he : testGrade e = 1)
    (h : testRow.{u} e ≤ testRow d) : k1SideRanks e ≤ k1SideRanks d := by
  have h₁ := omega0_add_one_lt.{u}
  revert hd he h
  fin_cases d <;> fin_cases e <;>
    first
    | exact fun _ _ _ ↦ by decide
    | exact fun hd ↦ absurd hd (by decide)
    | exact fun _ he ↦ absurd he (by decide)
    | exact fun _ _ h ↦ absurd h (not_le.mpr h₁)

/-- The test row is never `⊥`. -/
theorem testRow_ne_bot (d : Fin 4) : testRow.{u} d ≠ ⊥ := by
  fin_cases d <;> exact WithBot.coe_ne_bot

/-- At the cells of grade one, the ambient ranks are positive. -/
theorem k1SideRanks_ne_zero {d : Fin 4} (hd : testGrade d = 1) : k1SideRanks d ≠ 0 := by
  revert hd
  fin_cases d <;> decide

/-- **The ambient ranks have lawful tables**, by order interpolation
(`Scheme.hasLawfulTables_of_order`) against the lawful test row. -/
theorem hasLawfulTables_k1SideRanks :
    Scheme.HasLawfulTables.{u} testScheme 8 fun d ↦ k1SideRanks d := by
  have hgrade (d : Fin 4) : testScheme.{u}.toCellScheme.grade d = testGrade d := rfl
  refine Scheme.hasLawfulTables_of_order isWellFormed_testScheme (fun d _ ↦ by
    fin_cases d <;> decide) isLawful_testRow (fun d hd ↦ ?_) (fun s hs d e hde ↦ ?_)
    (fun s t hs ht hst ↦ ⟨t, rfl, ?_⟩)
  · change testGrade d = 1 at hd
    exact iff_of_false (k1SideRanks_ne_zero hd) (testRow_ne_bot d)
  · have hv (x : Fin 4) : visibilityReplace 1 1 (testRow.{u} x) = testRow x :=
      ((isSelfVisible_testRow x).mono (by fin_cases x <;> decide)).visibilityReplace_eq 1
    have hde' : testRow.{u} e.1 ≤ testRow d.1 := hde.trans_eq (hv _)
    have hg1 (x : testScheme.{u}.toCellScheme.below
        (testScheme.{u}.toCellScheme.gradedIndex s)) : testGrade x.1 = 1 := by
      have h₁ : testGrade x.1 ≤ 1 := hs ▸ x.2.2
      have h₂ : 1 ≤ testGrade x.1 := (by decide : ∀ y : Fin 4, 1 ≤ testGrade y) x.1
      omega
    exact min_le_min_right _ (k1SideRanks_le_of_testRow_le (hg1 d) (hg1 e) hde')
  · revert hst
    change testScope s ⊆ testScope t → _
    change testGrade s = 1 at hs
    change testGrade t = 1 at ht
    revert hs ht
    fin_cases s <;> fin_cases t <;> decide

/-- **The ambient ranks are a member of the restricted catalogue** over the test scheme. -/
theorem isSpanRankMember_k1Ranks : IsSpanRankMember testScheme.{u} 8 k1Tops 1 k1Ranks := by
  refine ⟨fun x ↦ ?_, fun i hi x hix ↦ ?_, fun b ↦ ?_, isAdmitted_k1Ranks⟩
  · rcases x with d | d <;> fin_cases d <;> decide
  · have hx : k1Ranks x ≤ 3 := by rcases x with d | d <;> fin_cases d <;> decide
    have : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl
    exacts [⟨Sum.inl ⟨1, by decide⟩, rfl⟩, ⟨Sum.inl ⟨3, by decide⟩, rfl⟩,
      ⟨Sum.inl ⟨0, by decide⟩, rfl⟩]
  · cases b <;> exact hasLawfulTables_k1SideRanks

/-! ### The grade-one test -/

/-- The new table of the test: the old table below the rank `3`, and the prescribed `ω * 3 + 1`
from the rank `3` on. -/
noncomputable def k1NewTable (i : ℕ) : Label.{u} :=
  if i < 3 then k1Table i else ((ω * 3 + 1 : Ordinal.{u}) : Label.{u})

theorem k1NewTable_of_lt {i : ℕ} (hi : i < 3) : k1NewTable.{u} i = k1Table i := ite_eq_left hi

theorem k1NewTable_of_le {i : ℕ} (hi : 3 ≤ i) :
    k1NewTable.{u} i = ((ω * 3 + 1 : Ordinal.{u}) : Label.{u}) := ite_eq_right (by omega)

theorem k1Table_of_le {i : ℕ} (hi : 3 ≤ i) :
    k1Table.{u} i = ((ω * 2 + 1 : Ordinal.{u}) : Label.{u}) := by
  unfold k1Table
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **The grade-one test**: the ambient ranks with the new table (old below `3`, the prescribed
value from `3` on) satisfy the conclusion of the restricted rank glue.  The distinct ranks `1`
and `2` keep their common value; both copies of `c₀` keep the rank `3`. -/
theorem k1RankGlueTest : K1RankGlueTestTarget.{u} := by
  have h₁ := omega0_add_one_lt.{u}
  have h₂₃ := omega0_mul_two_add_one_le_three.{u}
  have hcap (i : ℕ) : min (k1NewTable.{u} i) k1Cap = min (k1Table i) k1Cap := by
    rcases lt_or_ge i 3 with hi | hi
    · rw [k1NewTable_of_lt hi]
    · rw [k1NewTable_of_le hi, k1Table_of_le hi, k1Cap, min_self, min_eq_right h₂₃]
  have hmono : Monotone k1NewTable.{u} := by
    intro i j hij
    rcases lt_or_ge j 3 with hj | hj
    · rw [k1NewTable_of_lt (by omega), k1NewTable_of_lt hj]
      unfold k1Table
      split_ifs <;> first | exact le_rfl | exact bot_le | omega
    · rw [k1NewTable_of_le hj]
      rcases lt_or_ge i 3 with hi | hi
      · rw [k1NewTable_of_lt hi]
        unfold k1Table
        split_ifs
        · exact bot_le
        · exact h₁.le.trans h₂₃
        · omega
      · rw [k1NewTable_of_le hi]
  refine ⟨isSpanRankMember_k1Ranks, k1Ranks, k1NewTable, isSpanRankMember_k1Ranks,
    ⟨hmono, ?_, fun i ↦ ?_, fun i hi _ ↦ ?_⟩, fun _ ↦ rfl,
    fun i hi ↦ k1NewTable_of_lt hi, fun i _ ↦ hcap i, fun _ ↦ hcap _, fun d ↦ ?_⟩
  · rw [k1NewTable_of_lt (by omega)]
    simp [k1Table]
  · rcases lt_or_ge i 3 with hi | hi
    · rw [k1NewTable_of_lt hi]
      unfold k1Table
      split_ifs
      · exact isSelfVisible_bot _
      · exact isSelfVisible_omega0_add_one
      · omega
    · rw [k1NewTable_of_le hi]
      exact isSelfVisible_omega0_mul_three_add_one
  · rcases lt_or_ge i 3 with hi' | hi'
    · rw [k1NewTable_of_lt hi']
      unfold k1Table
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      exact WithBot.coe_ne_bot
    · rw [k1NewTable_of_le hi']
      exact WithBot.coe_ne_bot
  · obtain ⟨d, hd⟩ := d
    change testScope d ⊆ ({0} : Finset (Fin 2)) ∧ testGrade d ≤ 1 at hd
    revert hd
    fin_cases d
    · intro _
      exact k1NewTable_of_le le_rfl
    all_goals decide

end VaughtConjecture.ProcessRank

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalMultiScheme
import VaughtConjecture.Extension.ThinCompletionSeed4
import VaughtConjecture.Extension.ThinCompletionMirrorExamples
import VaughtConjecture.Extension.ThinCompletionTLTL
import VaughtConjecture.Extension.CrossedCouplingCompletion

/-!
# The product clause of the canonical multi-layer scheme fails at the compiled seeds

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the product clause, a sufficient hypothesis for the step of the canonical multi-layer scheme,
refuted at the six compiled seeds); semantic contract, items 2–4.

The canonical multi-layer scheme (`VaughtConjecture.Extension.CanonicalMultiScheme`) puts, at each
`(univ, k)`, two copies of the cells at `(C, k)` and `(D, k)`, each reading every cell through its
base by its copy row.  Its *product clause* `Seed.CanonicalProduct I R j` asks that every labelling
of the amalgam lawful below both coatoms at the grade `j`, read through the bases, be lawful below
`(univ, j)`: the lawful labellings below `(univ, j)` would then be exactly the pairs of coatom
labellings agreeing on the common face, and the lifts into the full scope would be the lifts from
the common face (`OrderedLayer.cappedLift_of_canonicalProduct`).  This module shows that no copy
rows give the product clause at the compiled seeds.  Each refutation fixes one copy `κ` and two
labellings of the amalgam lawful below both coatoms, both `⊤` at the original of `κ`; under the
product clause both, read through the bases, are lawful, so the one row of `κ` transforms to both
(locality at `κ`, where the cap `⊤` caps nothing).  Two obstructions to one row:

* **Crossing** (`OrderedLayer.not_canonicalProduct_of_crossing`): two cells of one grade, the first
  below the second in one labelling and above it in the other.  A row reading the first cell at
  most as the second forces the first labelling at most the second there
  (`Label.TransformsTo.le_of_le`), and the reverse reading forces the reverse.  At the grades
  `j = 2, 3`, with `κ` the copy of `(C, 2)`, the cells `({3}, 1)` and `({4}, 1)` carry the
  parameters of grade `1` of the two coatoms, which take the values `1, 2` and `2, 1` below a
  parameter of grade `2` equal to `⊤`, for the seeds of the types `T4`, `T5`, `TL` in every
  combination (`OrderedLayer.not_canonicalProduct_of_crossed_cells`).
* **Decoding at the top grade** (`OrderedLayer.not_canonicalProduct_of_decoding`, from
  `Label.TransformsTo.false_of_decoding`): if a cell of grade at least `3` is `⊤` in both
  targets, the suppressor is `⊤` at the grade `3`, so the shifter commutes with visibility
  replacement at the threshold `3`; every label is fixed by one of the replacements with values
  `0`, `1`, `2` (`Label.visibilityReplace_three_fixed`), so one row value is not read as `1` in one
  target and as `2` in the other.  At the grade `4`, with `κ` the copy of `(C, 4)`, for a seed with
  bottom apexes the labelling `⊤` at the apex of `C`, `⊥` elsewhere on `C`, and a labelling of `D`
  with the apex `⊥` is lawful below both coatoms (`OrderedLayer.isLawfulBelow_four_of_three`), and
  the parameter of grade `1` of `D` takes the values `1` and `2` there
  (`OrderedLayer.not_canonicalProduct_four_of_bottomApexes`).

**The six compiled seeds** (compiled, for every copy rows): the product clause fails at the grades
`2`, `3` and `4` for `seed4`, `seed5`, `seedL`, `seedLM` and `seedLL`
(`Seed.not_canonicalProduct_seed4`, `Seed.not_canonicalProduct_seed5`,
`Seed.not_canonicalProduct_seedL`, `Seed.not_canonicalProduct_seedLM`,
`Seed.not_canonicalProduct_seedLL`), and at the grade `4` for `seedHG`
(`Seed.not_canonicalProduct_seedHG`); for `seedHG` it holds at the grades `1`, `2`, `3`
(`VaughtConjecture.Extension.CanonicalMultiSchemeExamples`).  This refutes, at those seeds and
grades, the canonical family *as a fibre product*: the classification of its lawful labellings as
the pairs agreeing on the common face, and so the lifts as the lifts from the common face.  The
product clause is sufficient for the step of the family, not necessary, so this refutes neither
the family's step (for `seedHG` it holds at the grade `4`, where the clause fails:
`Seed.canonicalMultiStep_of_TH_TG`, the grade `4` coming from the top row through
`OrderedLayer.cappedLift_four_of_oldCells`) nor a completion of those seeds (each has one).  Nor
does it refute the family with rows restricting the pairs: by the labelling of `Ω` alone at the
grade `4`, as `Seed.canonicalMultiStep_of_productBelowTop` does (under which the labellings of the
decoding refutation are not lawful, `OrderedLayer.eq_bot_of_grade_four_canonical`), by the
oriented rows of an oriented ordered-layer step, which give the family a step at the five seeds
above (`VaughtConjecture.Extension.CanonicalMultiSchemeOriented`; an exact reformulation of their
ordered-layer steps, which already complete them), or by rows under which each copy of
`(B, k)` reads the parameters of its own coatom above those of the other.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.Label

/-! ### One row value cannot be read as `1` and as `2` above the grade `3` -/

/-- **Every label is fixed by visibility replacement at the threshold `3`** with one of the values
`0`, `1`, `2`: its finite part when that is below `3`, and any value otherwise. -/
theorem visibilityReplace_three_fixed (x : Label.{u}) :
    visibilityReplace 3 0 x = x ∨ visibilityReplace 3 1 x = x ∨ visibilityReplace 3 2 x = x := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
    simp only [visibilityReplace_coe_add hμ]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj
    · exact .inl (by simp)
    · exact .inr (.inl (by simp))
    · exact .inr (.inr (by simp))
    · exact .inl (by rw [ite_eq_right (by omega)])

variable {D : Type*} {grade : D → ℕ} {p q₁ q₂ : D → Label.{u}}

/-- **Decoding above the grade `3`**: one source cannot transform to two targets that are `⊤` at a
cell `s` of grade at least `3` and are `1` and `2` at a cell `e` of grade at most that of `s`.
The suppressors are `⊤` up to the grade of `s`, so the shifters commute with visibility
replacement at the threshold `3` at the source value of `e`. -/
theorem TransformsTo.false_of_decoding (h₁ : TransformsTo grade p q₁)
    (h₂ : TransformsTo grade p q₂) {s e : D} (hs : 3 ≤ grade s) (hes : grade e ≤ grade s)
    (h₁s : q₁ s = ⊤) (h₂s : q₂ s = ⊤) (h₁e : q₁ e = 1) (h₂e : q₂ e = 2) : False := by
  have key (q : D → Label.{u}) (h : TransformsTo grade p q) (hqs : q s = ⊤) :
      ∃ σ : Label.{u} → Label.{u}, (∀ i ≤ 3, σ (visibilityReplace 3 i (p e)) =
        visibilityReplace 3 i (σ (p e))) ∧ σ (p e) = q e := by
    obtain ⟨g, σ, hw, heq⟩ := h
    have hgs : g (grade s) = ⊤ := by
      have := heq s
      rw [hqs] at this
      exact (min_eq_top.mp this.symm).2
    have hg3 : g 3 = ⊤ := top_le_iff.mp (hgs ▸ hw.antitone hs)
    have hge : g (grade e) = ⊤ := top_le_iff.mp (hgs ▸ hw.antitone hes)
    refine ⟨σ, fun i hi ↦ hw.visibilityReplace_comm _ 3 (by rw [hg3]; exact le_top) i hi, ?_⟩
    rw [heq e, hge, min_top_right]
  obtain ⟨σ₁, c₁, e₁⟩ := key q₁ h₁ h₁s
  obtain ⟨σ₂, c₂, e₂⟩ := key q₂ h₂ h₂s
  rw [h₁e] at e₁
  rw [h₂e] at e₂
  rcases visibilityReplace_three_fixed (p e) with h | h | h
  · have := c₁ 0 (by omega)
    rw [h, e₁] at this
    simp at this
  · have := c₂ 1 (by omega)
    rw [h, e₂] at this
    simp at this
  · have := c₁ 2 (by omega)
    rw [h, e₁] at this
    simp at this

end VaughtConjecture.Label

namespace VaughtConjecture.OrderedLayer

open Finset Label CellScheme

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (R : CopyRows I)

/-! ### Two obstructions to one row at a copy -/

/-- Under the product clause at the grade `j`, the row of a copy of grade at most `j` transforms to
every labelling of the amalgam lawful below both coatoms at the grade `j`, read through the bases
and capped at the label of the original. -/
theorem transformsTo_copy_of_canonicalProduct {j : ℕ} (hP : I.CanonicalProduct R j) {k : Fin 4}
    (i : Fin 2) (hkj : (k : ℕ) + 1 ≤ j) {v : Fin I.amalgam.card → Label.{u}}
    (hC : I.amalgam.rows.IsLawfulBelow (coatomC, j) fun d ↦ v d)
    (hD : I.amalgam.rows.IsLawfulBelow (coatomD, j) fun d ↦ v d) :
    TransformsTo (fun t : (canonicalMultiScheme I R).toCellScheme.below
        ((canonicalMultiScheme I R).toCellScheme.gradedIndex (multiNewCell I canonicalMult k i)) ↦
        (canonicalMultiScheme I R).toCellScheme.grade t)
      ((canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult k i))
      fun t ↦ min (v (copyBase I t)) (v (copyOrig I k i)) := by
  have := (Rows.isLawfulBelow_iff_forall (w := fun z ↦ v (copyBase I z)) |>.mp
    (hP v hC hD)).2.1 _
    (multiNewCell_mem_below (r := canonicalRows I R) i hkj)
  simpa only [copyBase_multiNewCell] using this

/-- An old cell of grade at most `k + 1` is below each copy of grade `k + 1`. -/
private theorem multiOldCell_mem_below_copy {k : Fin 4} (i : Fin 2) {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ (k : ℕ) + 1) :
    multiOldCell I canonicalMult d ∈ (canonicalMultiScheme I R).toCellScheme.below
      ((canonicalMultiScheme I R).toCellScheme.gradedIndex (multiNewCell I canonicalMult k i)) := by
  rw [gradedIndex_multiNewCell]
  exact multiOldCell_mem_below ⟨subset_univ _, hd⟩

/-- **Crossing refutes the product clause.**  If two labellings of the amalgam lawful below both
coatoms at the grade `j` are `⊤` at the original of a copy of grade `k + 1 ≤ j`, and two cells `d`,
`e` of one grade at most `k + 1` are ordered `d < e` in the first and `e < d` in the second, no
copy rows satisfy the product clause at the grade `j`: the one row of the copy would read `d` and
`e` in both orders. -/
theorem not_canonicalProduct_of_crossing {j : ℕ} {k : Fin 4} (i : Fin 2) (hkj : (k : ℕ) + 1 ≤ j)
    {v₁ v₂ : Fin I.amalgam.card → Label.{u}}
    (h₁C : I.amalgam.rows.IsLawfulBelow (coatomC, j) fun d ↦ v₁ d)
    (h₁D : I.amalgam.rows.IsLawfulBelow (coatomD, j) fun d ↦ v₁ d)
    (h₂C : I.amalgam.rows.IsLawfulBelow (coatomC, j) fun d ↦ v₂ d)
    (h₂D : I.amalgam.rows.IsLawfulBelow (coatomD, j) fun d ↦ v₂ d)
    (h₁ : v₁ (copyOrig I k i) = ⊤) (h₂ : v₂ (copyOrig I k i) = ⊤) {d e : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ (k : ℕ) + 1)
    (hde : I.amalgam.toCellScheme.grade d = I.amalgam.toCellScheme.grade e)
    (c₁ : v₁ d < v₁ e) (c₂ : v₂ e < v₂ d) : ¬ I.CanonicalProduct R j := by
  intro hP
  have L₁ := transformsTo_copy_of_canonicalProduct R hP i hkj h₁C h₁D
  have L₂ := transformsTo_copy_of_canonicalProduct R hP i hkj h₂C h₂D
  have md := multiOldCell_mem_below_copy R i hd
  have me := multiOldCell_mem_below_copy R i (hde ▸ hd)
  have rd : (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult k i) ⟨_, md⟩ =
      R k i d := by
    rw [row_canonical]; exact congrArg (R k i) (copyBase_multiOldCell I d)
  have re : (canonicalMultiScheme I R).rows.row (multiNewCell I canonicalMult k i) ⟨_, me⟩ =
      R k i e := by
    rw [row_canonical]; exact congrArg (R k i) (copyBase_multiOldCell I e)
  have gde : (canonicalMultiScheme I R).toCellScheme.grade (multiOldCell I canonicalMult d) =
      (canonicalMultiScheme I R).toCellScheme.grade (multiOldCell I canonicalMult e) := by
    rw [grade_multiOldCell, grade_multiOldCell, hde]
  rcases le_total (R k i d) (R k i e) with h | h
  · have := L₂.le_of_le (d := ⟨_, md⟩) (d' := ⟨_, me⟩) (by rw [rd, re]; exact h) gde.ge
    simp only [copyBase_multiOldCell, h₂, min_top_right] at this
    exact absurd this (not_le.mpr c₂)
  · have := L₁.le_of_le (d := ⟨_, me⟩) (d' := ⟨_, md⟩) (by rw [rd, re]; exact h) gde.le
    simp only [copyBase_multiOldCell, h₁, min_top_right] at this
    exact absurd this (not_le.mpr c₁)

/-- **Decoding refutes the product clause.**  If two labellings of the amalgam lawful below both
coatoms at the grade `j` are `⊤` at the original of a copy of grade `3 ≤ k + 1 ≤ j`, and a cell `e`
of grade at most `k + 1` is `1` in the first and `2` in the second, no copy rows satisfy the product
clause at the grade `j`: the one row of the copy would read `e` as `1` and as `2` under a suppressor
`⊤` at the grade `3`. -/
theorem not_canonicalProduct_of_decoding {j : ℕ} {k : Fin 4} (i : Fin 2) (hk : 3 ≤ (k : ℕ) + 1)
    (hkj : (k : ℕ) + 1 ≤ j) {v₁ v₂ : Fin I.amalgam.card → Label.{u}}
    (h₁C : I.amalgam.rows.IsLawfulBelow (coatomC, j) fun d ↦ v₁ d)
    (h₁D : I.amalgam.rows.IsLawfulBelow (coatomD, j) fun d ↦ v₁ d)
    (h₂C : I.amalgam.rows.IsLawfulBelow (coatomC, j) fun d ↦ v₂ d)
    (h₂D : I.amalgam.rows.IsLawfulBelow (coatomD, j) fun d ↦ v₂ d)
    (h₁ : v₁ (copyOrig I k i) = ⊤) (h₂ : v₂ (copyOrig I k i) = ⊤) {e : Fin I.amalgam.card}
    (he : I.amalgam.toCellScheme.grade e ≤ (k : ℕ) + 1) (e₁ : v₁ e = 1) (e₂ : v₂ e = 2) :
    ¬ I.CanonicalProduct R j := by
  intro hP
  have L₁ := transformsTo_copy_of_canonicalProduct R hP i hkj h₁C h₁D
  have L₂ := transformsTo_copy_of_canonicalProduct R hP i hkj h₂C h₂D
  have me := multiOldCell_mem_below_copy R i he
  have ms := (canonicalMultiScheme I R).toCellScheme.mem_below_gradedIndex
    (multiNewCell I canonicalMult k i)
  refine TransformsTo.false_of_decoding L₁ L₂ (s := ⟨_, ms⟩) (e := ⟨_, me⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · -- The grade of the subtype element is that of the copy.
    change 3 ≤ (canonicalMultiScheme I R).toCellScheme.grade (multiNewCell I canonicalMult k i)
    rw [grade_multiNewCell]; exact hk
  · -- The grades of the subtype elements are those of the old cell and the copy.
    change (canonicalMultiScheme I R).toCellScheme.grade (multiOldCell I canonicalMult e) ≤
      (canonicalMultiScheme I R).toCellScheme.grade (multiNewCell I canonicalMult k i)
    rw [grade_multiOldCell, grade_multiNewCell]; exact he
  · simp only [copyBase_multiNewCell, h₁, min_self]
  · simp only [copyBase_multiNewCell, h₂, min_self]
  · simp only [copyBase_multiOldCell, h₁, e₁, min_top_right]
  · simp only [copyBase_multiOldCell, h₂, e₂, min_top_right]

/-! ### The grade `4` for seeds with bottom apexes -/

/-- **Lawfulness at the grade `4` below a coatom, for a seed with bottom apexes**: a labelling
lawful below `(B, 3)` is lawful below `(B, 4)` when its value at the cell of grade `4` of scope `B`
(the apex of `B`) is `⊥`, or is self-visible at `4` with the labelling `⊥` below `(B, 3)`. -/
theorem isLawfulBelow_four_of_three (hI : I.HasBottomApexes) {B : Finset (Fin 5)}
    (hB : B = coatomC ∨ B = coatomD) {w : Fin I.amalgam.card → Label.{u}}
    (h3 : I.amalgam.rows.IsLawfulBelow (B, 3) fun d ↦ w d)
    (htop : ∀ a, I.amalgam.toCellScheme.grade a = 4 → I.amalgam.toCellScheme.scope a = B →
      w a = ⊥ ∨ (IsSelfVisible 4 (w a) ∧
        ∀ d ∈ I.amalgam.toCellScheme.below (B, 3), w d = ⊥)) :
    I.amalgam.rows.IsLawfulBelow (B, 4) fun d ↦ w d := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp h3
  have hcard : #B = 4 := by rcases hB with rfl | rfl <;> decide
  -- A cell below `(B, 4)` is below `(B, 3)` or is the apex of `B`.
  have cases (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (B, 4)) :
      d ∈ I.amalgam.toCellScheme.below (B, 3) ∨
        (I.amalgam.toCellScheme.grade d = 4 ∧ I.amalgam.toCellScheme.scope d = B) := by
    by_cases h : I.amalgam.toCellScheme.grade d ≤ 3
    · exact .inl ⟨hd.1, h⟩
    · have hg : I.amalgam.toCellScheme.grade d = 4 := by
        have : I.amalgam.toCellScheme.grade d ≤ 4 := hd.2
        omega
      refine .inr ⟨hg, eq_of_subset_of_card_le hd.1 ?_⟩
      rw [hcard, ← hg]
      exact I.amalgam.isWellFormed.isWellFormed.grade_le_card d
  have hgr (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d ≤ 4 :=
    Nat.lt_succ_iff.mp (I.grade_lt d)
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · rcases cases d hd with h | ⟨hg, hsc⟩
    · exact ho d h
    · rcases htop d hg hsc with h | ⟨h, -⟩
      · rw [h]; exact isSelfVisible_bot _
      · rw [hg]; exact h
  · rcases cases s hs with h | ⟨hg, hsc⟩
    · exact hl s h
    · rcases htop s hg hsc with h | ⟨hsv, hbot⟩
      · simp only [h, min_bot_right]
        exact TransformsTo.bot _ _
      · refine transformsTo_of_eq_bot_iff _
          (fun t : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) ↦ hgr t.1)
          hsv _ _ fun t ↦ ?_
        have key := hI.row_apex hg t
        have htsB : I.amalgam.toCellScheme.scope t.1 ⊆ B := fun x hx ↦ hsc ▸ t.2.1 hx
        by_cases ht4 : I.amalgam.toCellScheme.grade t.1 = 4
        · have hts : t.1 = s := hI.eq_of_grade_four ht4 hg
            (eq_of_subset_of_card_le (htsB.trans hsc.ge) (by
              rw [hsc, hcard, ← ht4]; exact I.amalgam.isWellFormed.isWellFormed.grade_le_card _))
          rw [hts, min_self, ite_eq_right (fun h ↦ key.mp h ht4)]
        · have htB : t.1 ∈ I.amalgam.toCellScheme.below (B, 3) :=
            ⟨htsB, by
              -- The grade bound of `t`, as a statement about the grade of its cell.
              change I.amalgam.toCellScheme.grade t.1 ≤ 3
              have : I.amalgam.toCellScheme.grade t.1 ≤ 4 := hgr t.1
              omega⟩
          rw [hbot _ htB, min_bot_left, ite_eq_left (key.mpr ht4)]
  · rcases cases t ht with h | ⟨hgt, hsc⟩
    · exact ha s t h hst hg
    · have hgs : I.amalgam.toCellScheme.grade s = 4 := hg.trans hgt
      have hss : I.amalgam.toCellScheme.scope s = B :=
        eq_of_subset_of_card_le (hst.trans hsc.le) (by
          rw [hcard, ← hgs]; exact I.amalgam.isWellFormed.isWellFormed.grade_le_card _)
      exact ⟨s, by rw [hI.eq_of_grade_four hgs hgt (hss.trans hsc.symm)], le_rfl⟩

/-- **The product clause fails at the grade `4` for a seed with bottom apexes** whose second
coatom carries a cell `e` of grade at most `3` (in practice `({4}, 1)`) at which labellings lawful
below both coatoms at the grade `3`, `⊥` below `(C, 3)`, take the values `1` and `2`.  Put `⊤` at
the apex of `C` and `⊥` at the apex of `D`; the copy of `(C, 4)` would read `e` as `1` and `2`. -/
theorem not_canonicalProduct_four_of_bottomApexes (hI : I.HasBottomApexes)
    {e : Fin I.amalgam.card} (he : I.amalgam.toCellScheme.grade e ≤ 3)
    (L : Label.{u} → Fin I.amalgam.card → Label.{u})
    (hL : ∀ b : Label.{u}, b = 1 ∨ b = 2 →
      I.amalgam.rows.IsLawfulBelow (coatomC, 3) (fun d ↦ L b d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, 3) (fun d ↦ L b d))
    (hLC : ∀ b d, d ∈ I.amalgam.toCellScheme.below (coatomC, 3) → L b d = ⊥)
    (hLe : ∀ b, L b e = b) : ¬ I.CanonicalProduct R 4 := by
  classical
  -- The labelling `⊤` at the apex of `C`, `⊥` at the apex of `D`, and `L b` below the grade `4`.
  set v : Label.{u} → Fin I.amalgam.card → Label.{u} := fun b d ↦
    if I.amalgam.toCellScheme.grade d = 4 then (if d = copyOrig I 3 0 then ⊤ else ⊥) else L b d
    with hv
  have hgo : I.amalgam.toCellScheme.grade (copyOrig I 3 0) = 4 := grade_copyOrig I 3 0
  have hso : I.amalgam.toCellScheme.scope (copyOrig I 3 0) = coatomC :=
    congrArg Prod.fst (gradedIndex_copyOrig I 3 0)
  have hv3 (b : Label.{u}) {B : Finset (Fin 5)} (hB : I.amalgam.rows.IsLawfulBelow (B, 3)
      (fun d ↦ L b d)) : I.amalgam.rows.IsLawfulBelow (B, 3) (fun d ↦ v b d) := by
    refine (Rows.isLawfulBelow_congr fun d hd ↦ ?_).mp hB
    have : I.amalgam.toCellScheme.grade d ≠ 4 := by
      have : I.amalgam.toCellScheme.grade d ≤ 3 := hd.2
      omega
    rw [hv]; dsimp only; rw [ite_eq_right this]
  have lawful (b : Label.{u}) (hb : b = 1 ∨ b = 2) :
      I.amalgam.rows.IsLawfulBelow (coatomC, 4) (fun d ↦ v b d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, 4) (fun d ↦ v b d) := by
    refine ⟨isLawfulBelow_four_of_three hI (.inl rfl) (hv3 b (hL b hb).1) fun a ha hsa ↦ ?_,
      isLawfulBelow_four_of_three hI (.inr rfl) (hv3 b (hL b hb).2) fun a ha hsa ↦ ?_⟩
    · have hao : a = copyOrig I 3 0 := hI.eq_of_grade_four ha hgo (hsa.trans hso.symm)
      refine .inr ⟨by
          rw [hv]; dsimp only; rw [ite_eq_left ha, ite_eq_left hao]; exact isSelfVisible_top 4,
        fun d hd ↦ ?_⟩
      have : I.amalgam.toCellScheme.grade d ≠ 4 := by
        have : I.amalgam.toCellScheme.grade d ≤ 3 := hd.2
        omega
      rw [hv]; dsimp only; rw [ite_eq_right this]; exact hLC b d hd
    · have hao : a ≠ copyOrig I 3 0 := fun h ↦ by
        rw [h, hso] at hsa; exact absurd hsa (by decide)
      exact .inl (by rw [hv]; dsimp only; rw [ite_eq_left ha, ite_eq_right hao])
  have htop (b : Label.{u}) : v b (copyOrig I 3 0) = ⊤ := by
    rw [hv]; dsimp only; rw [ite_eq_left hgo, ite_eq_left rfl]
  have hve (b : Label.{u}) : v b e = b := by
    rw [hv]; dsimp only; rw [ite_eq_right (by omega), hLe]
  exact not_canonicalProduct_of_decoding R (k := 3) 0 (by decide) le_rfl
    (lawful 1 (.inl rfl)).1 (lawful 1 (.inl rfl)).2 (lawful 2 (.inr rfl)).1
    (lawful 2 (.inr rfl)).2 (htop 1) (htop 2) (he.trans (by decide)) (hve 1) (hve 2)

/-- **The product clause fails at every grade `j ≥ 2`** for a seed whose amalgam has cells `d₃` at
`({3}, 1)` and `d₄` at `({4}, 1)` and labellings `L a b`, lawful below both coatoms at the grade
`j` for `a`, `b` in `{1, 2}`, that are `⊤` at the original of the copy of `(C, 2)` and `a` at `d₃`,
`b` at `d₄`: the copy of `(C, 2)` would read `d₃` and `d₄` in both orders. -/
theorem not_canonicalProduct_of_crossed_cells {j : ℕ} (h2 : 2 ≤ j) {d₃ d₄ : Fin I.amalgam.card}
    (h₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (h₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1))
    (L : Label.{u} → Label.{u} → Fin I.amalgam.card → Label.{u})
    (hL : ∀ a b : Label.{u}, (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) →
      I.amalgam.rows.IsLawfulBelow (coatomC, j) (fun d ↦ L a b d) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, j) (fun d ↦ L a b d))
    (hLC : ∀ a b, L a b (copyOrig I 1 0) = ⊤) (hL₃ : ∀ a b, L a b d₃ = a)
    (hL₄ : ∀ a b, L a b d₄ = b) : ¬ I.CanonicalProduct R j := by
  have g₃ : I.amalgam.toCellScheme.grade d₃ = 1 := congrArg Prod.snd h₃
  have g₄ : I.amalgam.toCellScheme.grade d₄ = 1 := congrArg Prod.snd h₄
  have h12 : (1 : Label.{u}) < 2 := by exact_mod_cast (one_lt_two : (1 : Ordinal.{u}) < 2)
  have l₁ := hL 1 2 (.inl ⟨rfl, rfl⟩)
  have l₂ := hL 2 1 (.inr ⟨rfl, rfl⟩)
  refine not_canonicalProduct_of_crossing R (k := 1) 0 h2 l₁.1 l₁.2 l₂.1 l₂.2 (hLC 1 2)
    (hLC 2 1) (d := d₃) (e := d₄) (by rw [g₃]; decide) (g₃.trans g₄.symm) ?_ ?_
  · rw [hL₃, hL₄]; exact h12
  · rw [hL₃, hL₄]; exact h12

end VaughtConjecture.OrderedLayer

/-! ### The labellings of graded indices of the compiled seeds -/

namespace VaughtConjecture.OrderedLayer

open Finset Label
open TwoFaceLiftCounterexample (liveC liveD pairKind pairLabelling)
open CaseSplitCounterexample (liveG tripleKind tripleLabelling)

/-- The live graded indices of the second coatom contain the point `4`. -/
private theorem four_mem_of_mem_liveD : ∀ X ∈ liveD, (4 : Fin 5) ∈ X.1 := by decide

/-- Off the point `4`, the pair labelling with the parameters of the first coatom `⊥` is `⊥`. -/
private theorem pairLabelling_eq_bot {X : Finset (Fin 5) × ℕ} (hX : (4 : Fin 5) ∉ X.1)
    (b : Label.{u}) : pairLabelling ⊥ ⊥ b ⊥ X = ⊥ := by
  have h : X ∉ liveD := fun h ↦ hX (four_mem_of_mem_liveD X h)
  simp only [pairLabelling, pairKind, h, ite_false]
  split_ifs <;> rfl

/-- Off the point `4`, the triple labelling with every parameter but `A_D` equal to `⊥` is `⊥`. -/
private theorem tripleLabelling_eq_bot {X : Finset (Fin 5) × ℕ} (hX : (4 : Fin 5) ∉ X.1)
    (b : Label.{u}) : tripleLabelling ⊥ ⊥ b ⊥ ⊥ X = ⊥ := by
  have h : X ∉ liveD := fun h ↦ hX (four_mem_of_mem_liveD X h)
  simp only [tripleLabelling, tripleKind, h, ite_false]
  split_ifs <;> rfl

/-- A cell below `(C, k)` does not contain the point `4`. -/
private theorem four_notMem_of_mem_below_C {α : Ordinal.{u}} {I : Seed.{u} α 3} {k : ℕ}
    {d : Fin I.amalgam.card} (hd : d ∈ I.amalgam.toCellScheme.below (coatomC, k)) :
    (4 : Fin 5) ∉ (I.amalgam.toCellScheme.gradedIndex d).1 := fun h ↦ by
  have := hd.1 h
  simp at this

end VaughtConjecture.OrderedLayer

namespace VaughtConjecture.Seed

open Finset Label OrderedLayer
open TwoFaceLiftCounterexample (T4 pairKind pairLabelling isLawfulBelow_pairLabelling)
open CaseSplitCounterexample (T5 tripleKind tripleLabelling)
open TwoFaceLiftExistsCounterexample (TL VisibilityReplaceFixedOfLT)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-! ### The six compiled seeds -/

/-- **The product clause fails at the grades `2`, `3` and `4` for a seed of `T4` with itself**, for
every copy rows. -/
theorem not_canonicalProduct_of_T4 (hIL : I.left = T4 α) (hIR : I.right = T4 α)
    (R : CopyRows I) : ∀ j, 2 ≤ j → j ≤ 4 → ¬ I.CanonicalProduct R j := by
  obtain ⟨d₃, h₃⟩ := Seed4.exists_cell_T4 (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := Seed4.exists_cell_T4 (hIR ▸ I.restrictFace_right) 3
  have e₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1) :=
    h₃.trans (by decide +kernel)
  have e₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1) :=
    h₄.trans (by decide +kernel)
  intro j h2 h4
  rcases (show j ≤ 3 ∨ j = 4 by omega) with h3 | rfl
  swap
  · refine not_canonicalProduct_four_of_bottomApexes R (hasBottomApexes_of_T4 hIL hIR)
      (e := d₄)
      (by rw [show I.amalgam.toCellScheme.grade d₄ = 1 from congrArg Prod.snd e₄]; omega)
      (fun b d ↦ pairLabelling ⊥ ⊥ b ⊥ (I.amalgam.toCellScheme.gradedIndex d))
      (fun b hb ↦ ?_) (fun b d hd ↦ pairLabelling_eq_bot (four_notMem_of_mem_below_C hd) b)
      (fun b ↦ ?_)
    · have hsv : IsSelfVisible 1 b := by rcases hb with rfl | rfl <;> simp
      exact isLawfulBelow_pairLabelling hIL hIR (isSelfVisible_bot 1) (isSelfVisible_bot 2) hsv
        (isSelfVisible_bot 2)
    · rw [e₄, pairLabelling, show pairKind (({4} : Finset (Fin 5)), 1) = 3 by decide]
      rfl
  refine not_canonicalProduct_of_crossed_cells R h2 e₃ e₄
    (fun a b d ↦ pairLabelling a ⊤ b ⊤ (I.amalgam.toCellScheme.gradedIndex d))
    (fun a b hab ↦ ?_) (fun a b ↦ ?_) (fun a b ↦ ?_) (fun a b ↦ ?_)
  · have hsv : IsSelfVisible 1 a ∧ IsSelfVisible 1 b := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have h := isLawfulBelow_pairLabelling hIL hIR hsv.1 (isSelfVisible_top 2) hsv.2
      (isSelfVisible_top 2)
    exact ⟨h.1.mono (X := (coatomC, j)) ⟨subset_rfl, h3⟩,
      h.2.mono (X := (coatomD, j)) ⟨subset_rfl, h3⟩⟩
  · rw [gradedIndex_copyOrig, pairLabelling,
      show pairKind (copyCoatom 0, ((1 : Fin 4) : ℕ) + 1) = 2 by decide]
    rfl
  · rw [e₃, pairLabelling, show pairKind (({3} : Finset (Fin 5)), 1) = 1 by decide]
    rfl
  · rw [e₄, pairLabelling, show pairKind (({4} : Finset (Fin 5)), 1) = 3 by decide]
    rfl

/-- **The product clause fails at the grades `2`, `3` and `4` for a seed with bottom apexes whose
triple labellings with `G = ⊥` are lawful below both coatoms**, with cells at `({3}, 1)` and
`({4}, 1)`, for every copy rows. -/
theorem not_canonicalProduct_of_triple (hI : I.HasBottomApexes) {d₃ d₄ : Fin I.amalgam.card}
    (e₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (e₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1))
    (hlaw : ∀ AC FC AD FD : Label.{u}, IsSelfVisible 1 AC → IsSelfVisible 2 FC →
      IsSelfVisible 1 AD → IsSelfVisible 2 FD →
      I.amalgam.rows.IsLawfulBelow (coatomC, 3)
          (fun d ↦ tripleLabelling AC FC AD FD ⊥ (I.amalgam.toCellScheme.gradedIndex d)) ∧
        I.amalgam.rows.IsLawfulBelow (coatomD, 3)
          (fun d ↦ tripleLabelling AC FC AD FD ⊥ (I.amalgam.toCellScheme.gradedIndex d)))
    (R : CopyRows I) : ∀ j, 2 ≤ j → j ≤ 4 → ¬ I.CanonicalProduct R j := by
  intro j h2 h4
  rcases (show j ≤ 3 ∨ j = 4 by omega) with h3 | rfl
  swap
  · refine not_canonicalProduct_four_of_bottomApexes R hI (e := d₄)
      (by rw [show I.amalgam.toCellScheme.grade d₄ = 1 from congrArg Prod.snd e₄]; omega)
      (fun b d ↦ tripleLabelling ⊥ ⊥ b ⊥ ⊥ (I.amalgam.toCellScheme.gradedIndex d))
      (fun b hb ↦ ?_) (fun b d hd ↦ tripleLabelling_eq_bot (four_notMem_of_mem_below_C hd) b)
      (fun b ↦ ?_)
    · have hsv : IsSelfVisible 1 b := by rcases hb with rfl | rfl <;> simp
      exact hlaw ⊥ ⊥ b ⊥ (isSelfVisible_bot 1) (isSelfVisible_bot 2) hsv (isSelfVisible_bot 2)
    · rw [e₄, tripleLabelling, show tripleKind (({4} : Finset (Fin 5)), 1) = 3 by decide]
      rfl
  refine not_canonicalProduct_of_crossed_cells R h2 e₃ e₄
    (fun a b d ↦ tripleLabelling a ⊤ b ⊤ ⊥ (I.amalgam.toCellScheme.gradedIndex d))
    (fun a b hab ↦ ?_) (fun a b ↦ ?_) (fun a b ↦ ?_) (fun a b ↦ ?_)
  · have hsv : IsSelfVisible 1 a ∧ IsSelfVisible 1 b := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have h := hlaw a ⊤ b ⊤ hsv.1 (isSelfVisible_top 2) hsv.2 (isSelfVisible_top 2)
    exact ⟨h.1.mono (X := (coatomC, j)) ⟨subset_rfl, h3⟩,
      h.2.mono (X := (coatomD, j)) ⟨subset_rfl, h3⟩⟩
  · rw [gradedIndex_copyOrig, tripleLabelling,
      show tripleKind (copyCoatom 0, ((1 : Fin 4) : ℕ) + 1) = 2 by decide]
    rfl
  · rw [e₃, tripleLabelling, show tripleKind (({3} : Finset (Fin 5)), 1) = 1 by decide]
    rfl
  · rw [e₄, tripleLabelling, show tripleKind (({4} : Finset (Fin 5)), 1) = 3 by decide]
    rfl

/-- The condition of `TL` on the finite part of `A` below `G` holds for `G = ⊥`. -/
private theorem visibilityReplaceFixedOfLT_bot (A : Label.{u}) : VisibilityReplaceFixedOfLT A ⊥ :=
  fun h ↦ absurd h (not_lt_bot)

/-- **The product clause fails at the grades `2`, `3` and `4` for a seed of `T5` with itself.** -/
theorem not_canonicalProduct_of_T5 (hIL : I.left = T5 α) (hIR : I.right = T5 α)
    (R : CopyRows I) : ∀ j, 2 ≤ j → j ≤ 4 → ¬ I.CanonicalProduct R j := by
  obtain ⟨d₃, h₃⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
  exact not_canonicalProduct_of_triple (hasBottomApexes_of_T5 hIL hIR)
    (h₃.trans (by decide +kernel)) (h₄.trans (by decide +kernel))
    (fun _ _ _ _ hAC hFC hAD hFD ↦ CaseSplitCounterexample.isLawfulBelow_tripleLabelling hIL hIR
      hAC hFC hAD hFD (isSelfVisible_bot 3) bot_le bot_le bot_le bot_le) R

/-- **The product clause fails at the grades `2`, `3` and `4` for a seed of `TL` and `T5`.** -/
theorem not_canonicalProduct_of_TL_T5 (hIL : I.left = TL α) (hIR : I.right = T5 α)
    (R : CopyRows I) : ∀ j, 2 ≤ j → j ≤ 4 → ¬ I.CanonicalProduct R j := by
  obtain ⟨d₃, h₃⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
  exact not_canonicalProduct_of_triple (hasBottomApexes_of_TL_T5 hIL hIR)
    (h₃.trans (by decide +kernel)) (h₄.trans (by decide +kernel))
    (fun AC _ _ _ hAC hFC hAD hFD ↦ TwoFaceLiftExistsCounterexample.isLawfulBelow_tripleLabelling
      hIL hIR hAC hFC hAD hFD (isSelfVisible_bot 3) bot_le (visibilityReplaceFixedOfLT_bot AC)
      bot_le bot_le) R

/-- **The product clause fails at the grades `2`, `3` and `4` for a seed of `T5` and `TL`.** -/
theorem not_canonicalProduct_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α)
    (R : CopyRows I) : ∀ j, 2 ≤ j → j ≤ 4 → ¬ I.CanonicalProduct R j := by
  obtain ⟨d₃, h₃⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 3
  exact not_canonicalProduct_of_triple (hasBottomApexes_of_T5_TL hIL hIR)
    (h₃.trans (by decide +kernel)) (h₄.trans (by decide +kernel))
    (fun _ _ AD _ hAC hFC hAD hFD ↦ Mirror.isLawfulBelow_tripleLabelling hIL hIR hAC hFC hAD hFD
      (isSelfVisible_bot 3) bot_le bot_le bot_le (visibilityReplaceFixedOfLT_bot AD)) R

/-- **The product clause fails at the grades `2`, `3` and `4` for a seed of `TL` with itself.** -/
theorem not_canonicalProduct_of_TL_TL (hIL : I.left = TL α) (hIR : I.right = TL α)
    (R : CopyRows I) : ∀ j, 2 ≤ j → j ≤ 4 → ¬ I.CanonicalProduct R j := by
  obtain ⟨d₃, h₃⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 3
  refine not_canonicalProduct_of_triple (hasBottomApexes_of_TL_TL hIL hIR)
    (h₃.trans (by decide +kernel)) (h₄.trans (by decide +kernel))
    (fun AC FC AD FD hAC hFC hAD hFD ↦ ?_) R
  have hC := SeedLL.isLawfulBelow_coatom_TL ⟨hAC, hFC, isSelfVisible_bot 3, bot_le,
    visibilityReplaceFixedOfLT_bot AC⟩ (hIL ▸ I.restrictFace_left)
    (CaseSplitCounterexample.tripleLabelling_left AC FC AD FD ⊥)
  have hD := SeedLL.isLawfulBelow_coatom_TL ⟨hAD, hFD, isSelfVisible_bot 3, bot_le,
    visibilityReplaceFixedOfLT_bot AD⟩ (hIR ▸ I.restrictFace_right)
    (CaseSplitCounterexample.tripleLabelling_right AC FC AD FD ⊥)
  rw [← coatomC_eq] at hC
  rw [← coatomD_eq] at hD
  exact ⟨hC, hD⟩

open CrossedCouplingCounterexample (TH TG kindOld kindD CellKind Coupled) in
/-- Off the point `4`, the labelling by kinds of `seedHG` with every parameter but `A_D` equal to
`⊥` is `⊥`: the kind `A_D` is read through the point `4`. -/
private theorem val_kindOld_eq_bot {X : Finset (Fin 5) × ℕ} (hX : (4 : Fin 5) ∉ X.1)
    (b : Label.{u}) :
    (kindOld X).val ⊥ b ⊥ ⊥ ⊥ = ⊥ := by
  have hD : kindD X = 1 → (4 : Fin 5) ∈ X.1 := by
    unfold kindD
    split_ifs with h
    · intro _
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl <;> decide
    all_goals intro h'; exact absurd h' (by decide)
  unfold kindOld
  split_ifs with h1 h2 h3
  all_goals first | rfl | exact absurd (hD h3) hX

open CrossedCouplingCounterexample (TH TG kindOld CellKind Coupled) in
/-- **The product clause fails at the grade `4` for a seed of `TH` and `TG`**, for every copy
rows: the parameter `A_D` of the second coatom takes the values `1` and `2` under a copy of `(C, 4)`
labelled `⊤`.  (At the grades `1`, `2`, `3` the parameters of grade `1` of the two coatoms never
cross below a copy, since `TH` couples `H ≤ A_C` and `TG` couples `G ≤ A_D`.) -/
theorem not_canonicalProduct_four_of_TH_TG (hIL : I.left = TH α) (hIR : I.right = TG α)
    (R : CopyRows I) : ¬ I.CanonicalProduct R 4 := by
  obtain ⟨-, d₄, -, h₄⟩ := CrossedCouplingCounterexample.exists_cells hIL hIR
  refine not_canonicalProduct_four_of_bottomApexes R
    (CrossedCouplingCounterexample.hasBottomApexes_HG hIL hIR)
    (e := d₄) (by rw [show I.amalgam.toCellScheme.grade d₄ = 1 from congrArg Prod.snd h₄]; omega)
    (fun b d ↦ (kindOld (I.amalgam.toCellScheme.gradedIndex d)).val ⊥ b ⊥ ⊥ ⊥)
    (fun b hb ↦ ?_) (fun b d hd ↦ val_kindOld_eq_bot (four_notMem_of_mem_below_C hd) b)
    (fun b ↦ ?_)
  · have hsv : IsSelfVisible 1 b := by rcases hb with rfl | rfl <;> simp
    have h := CrossedCouplingCounterexample.isLawful_amalgam_kindOld hIL hIR (isSelfVisible_bot 1)
      hsv (isSelfVisible_bot 2) (isSelfVisible_bot 3) (by simp [Coupled]) (by simp [Coupled])
    exact ⟨h.isLawfulBelow _, h.isLawfulBelow _⟩
  · rw [h₄, show kindOld (({4} : Finset (Fin 5)), 1) = .ad by decide]
    rfl

/-- **`seed4`**: for every copy rows, the product clause fails at the grades `2`, `3` and `4`. -/
theorem not_canonicalProduct_seed4 (R : CopyRows (TwoFaceLiftCounterexample.seed4 α)) :
    ∀ j, 2 ≤ j → j ≤ 4 → ¬ (TwoFaceLiftCounterexample.seed4 α).CanonicalProduct R j :=
  not_canonicalProduct_of_T4 rfl rfl R

/-- **`seed5`**: for every copy rows, the product clause fails at the grades `2`, `3` and `4`. -/
theorem not_canonicalProduct_seed5 (R : CopyRows (CaseSplitCounterexample.seed5 α)) :
    ∀ j, 2 ≤ j → j ≤ 4 → ¬ (CaseSplitCounterexample.seed5 α).CanonicalProduct R j :=
  not_canonicalProduct_of_T5 rfl rfl R

/-- **`seedL`**: for every copy rows, the product clause fails at the grades `2`, `3` and `4`. -/
theorem not_canonicalProduct_seedL (R : CopyRows (TwoFaceLiftExistsCounterexample.seedL α)) :
    ∀ j, 2 ≤ j → j ≤ 4 → ¬ (TwoFaceLiftExistsCounterexample.seedL α).CanonicalProduct R j :=
  not_canonicalProduct_of_TL_T5 rfl rfl R

/-- **`seedLM`**: for every copy rows, the product clause fails at the grades `2`, `3` and `4`. -/
theorem not_canonicalProduct_seedLM (R : CopyRows (seedLM α)) :
    ∀ j, 2 ≤ j → j ≤ 4 → ¬ (seedLM α).CanonicalProduct R j :=
  not_canonicalProduct_of_T5_TL rfl rfl R

/-- **`seedLL`**: for every copy rows, the product clause fails at the grades `2`, `3` and `4`. -/
theorem not_canonicalProduct_seedLL (R : CopyRows (seedLL α)) :
    ∀ j, 2 ≤ j → j ≤ 4 → ¬ (seedLL α).CanonicalProduct R j :=
  not_canonicalProduct_of_TL_TL rfl rfl R

/-- **`seedHG`**: for every copy rows, the product clause fails at the grade `4`. -/
theorem not_canonicalProduct_seedHG (R : CopyRows (CrossedCouplingCounterexample.seedHG α)) :
    ¬ (CrossedCouplingCounterexample.seedHG α).CanonicalProduct R 4 :=
  not_canonicalProduct_four_of_TH_TG rfl rfl R

end VaughtConjecture.Seed

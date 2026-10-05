/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample

/-!
# The separating cell: a necessary condition for every completion of the asymmetric seed

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here a condition that
every completion below the full grade of the asymmetric seed `seedL` meets, and which the tower of
the step does not meet); semantic contract, items 2–4.

Write `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}` for the two coatoms of a seed on five points,
`d₁` for its cell at `({3}, 1)` (on `C`) and `d₂` for its cell at `({4}, 1)` (on `D`).

**Separating cells.**  A cell `u` of a completion below the full grade, at `(univ, 2)`, is a
*separating cell* when its row reads `d₁` strictly below `d₂`.  Every completion below the full
grade of a seed whose coatom types are `TL` and `T5` (module
`VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample`) has one, at which a given lawful
labelling reaches a given cap (`exists_separating_cell`): for every cap `c` self-visible at `3`,
every `A ≠ ⊤` self-visible at `1` with `VisibilityReplaceFixedOfLT A ⊤`, and every labelling `q`
lawful below `(univ, 3)` that agrees capped at `c` with the prescription `tripleLabelling A ⊤ ⊤ ⊤ ⊤`
on `C`, some separating cell `u` has `c ≤ q u`.  The proof is the argument of the refutation of the
existential two-face lift at the grade `2` (`not_twoFaceLiftExists_two_of`, steps 4 and 5), with the
tower replaced by an arbitrary completion: bountifulness from `(C, 3)` to `(univ, 3)` lifts the
prescription to `w`; on `D`, `w` is lawful in `T5` and `⊤` at the cell of the common face of grade
`3`, hence `⊤` at `d₂` (the coupling `G ≤ A` of `T5`); availability from the cell `(C, 2)`, where
`w` is `⊤`, gives a cell `u` at `(univ, 2)` with `w u = ⊤ ≥ c`; and locality at `u` with
`w d₁ = A < ⊤ = w d₂` forces the row of `u` to read `d₁` below `d₂`.  With `c = ⊥` and `q = ⊥`:
every completion of `seedL` has a separating cell (`exists_separating_cell_seedL`).  In the tower of
the step, every new cell at `(univ, 2)` where the catalogue entry reaches the cap reads `d₁` and
`d₂` at the same value (step 3 of `not_twoFaceLiftExists_two_of`), so the tower never meets this
condition.

**Collisions.**  A *collision* at a cell `z` of grade `2` is a labelling that carries one label
`e = λ + 1`, of finite part `1` (not self-visible at `2`), at two cells of grade `1`, and a label
above `e` at `z`.  At a separating cell there is no collision (`le_of_separating`): every
labelling lawful below `(univ, 2)` with `x d₁ = x d₂ = λ + 1` has `x u ≤ λ + 1`.  This is the
collision lemma (`eq_of_transformsTo_collision`): if a row transforms to a labelling with a
collision at `z`, and its values at the two cells are self-visible at `1`, then those values are
equal.  The suppressor exceeds `e` at the grade `2`, so the shifter sends both row values to `e`;
if they differed, the commutation of the shifter with `visibilityReplace 2 2` at the smaller one
would give `visibilityReplace 2 2 e ≤ e`, which fails since `e` is not self-visible at `2`
(`visibilityReplace_two_two_le_of_lt`).

The separating cell is a necessary condition, not a refutation: the thin completion of
`VaughtConjecture.Extension.ThinCompletion` (the amalgam with one new cell at each graded face of
full scope) meets it, with one cell at `(univ, 2)`, and no labelling of it lawful below `(univ, 2)`
has a collision there.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ThinCompletion

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftExistsCounterexample
open CaseSplitCounterexample (tripleLabelling tripleKind)

/-! ### Labels of the form `ω * q + n` -/

/-- A label `ω * q + n` lies below `ω * m` exactly when `q < m`. -/
theorem coe_block_lt_iff {q m : Ordinal.{u}} {n : ℕ} :
    ((ω * q + n : Ordinal.{u}) : Label.{u}) < ((ω * m : Ordinal.{u}) : Label.{u}) ↔ q < m := by
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  constructor
  · intro h
    by_contra hmq
    rw [not_lt] at hmq
    exact absurd h (not_lt.mpr ((show ω * m ≤ ω * q by gcongr).trans le_self_add))
  · intro h
    simpa using omega0_mul_add_natCast_lt h n 0

/-- Visibility replacement on a label `ω * q + n` replaces the finite part `n` when `n < k`. -/
theorem visibilityReplace_block (q : Ordinal.{u}) (n k i : ℕ) :
    visibilityReplace k i ((ω * q + n : Ordinal.{u}) : Label.{u}) =
      ((ω * q + ((if n < k then i else n : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

/-- A label `ω * q + n` is self-visible at `k` exactly when `k ≤ n`. -/
theorem isSelfVisible_block {q : Ordinal.{u}} {n k : ℕ} :
    IsSelfVisible k ((ω * q + n : Ordinal.{u}) : Label.{u}) ↔ k ≤ n := by
  rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

/-- Every label other than `⊥` and `⊤` has the form `ω * q + n`. -/
theorem exists_block {x : Label.{u}} (hb : x ≠ ⊥) (ht : x ≠ ⊤) :
    ∃ (q : Ordinal.{u}) (n : ℕ), x = ((ω * q + n : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hb
  | top => exact absurd rfl ht
  | coe o =>
    obtain ⟨q, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    exact ⟨q, n, rfl⟩

/-- Two replacements at thresholds at most `2`. -/
theorem visibilityReplace_visibilityReplace_two {k : ℕ} (hk : k ≤ 2) (i j : ℕ)
    (A : Label.{u}) :
    visibilityReplace k i (visibilityReplace 2 j A) =
      visibilityReplace 2 (if j < k then i else j) A := by
  induction A using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    have key : (if (if n < 2 then j else n) < k then i else (if n < 2 then j else n)) =
        (if n < 2 then (if j < k then i else j) else n) := by split_ifs <;> omega
    rw [visibilityReplace_coe, visibilityReplace_coe, visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast,
      Ordinal.visibilityReplace_omega0_mul_add_natCast,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, key]

/-- A label self-visible at `1` is fixed by visibility replacement at `2` with value `1`. -/
theorem visibilityReplace_two_one_of_isSelfVisible {a : Label.{u}} (ha : IsSelfVisible 1 a) :
    visibilityReplace 2 1 a = a := by
  induction a using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    have hn : 1 ≤ n := isSelfVisible_block.mp ha
    have hif : (if n < 2 then 1 else n) = n := by split_ifs <;> omega
    rw [visibilityReplace_block, hif]

/-! ### The collision lemma -/

/-- **One step above a label of finite part `1`**: if `a` is self-visible at `1` and `a < b`,
then `visibilityReplace 2 2 a ≤ b`. -/
theorem visibilityReplace_two_two_le_of_lt {a b : Label.{u}} (ha : IsSelfVisible 1 a)
    (hab : a < b) :
    visibilityReplace 2 2 a ≤ b := by
  by_cases ha2 : IsSelfVisible 2 a
  · rw [ha2]; exact hab.le
  have hb : a ≠ ⊥ := fun h ↦ ha2 (h ▸ isSelfVisible_bot 2)
  have ht : a ≠ ⊤ := fun h ↦ ha2 (h ▸ isSelfVisible_top 2)
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn1 : 1 ≤ n := isSelfVisible_block.mp ha
  have hn2 : ¬ 2 ≤ n := fun h ↦ ha2 (isSelfVisible_block.mpr h)
  obtain rfl : n = 1 := by omega
  rw [visibilityReplace_block, ite_eq_left (by omega)]
  induction b using recBotCoeTop with
  | bot => exact absurd hab (not_lt.mpr bot_le)
  | top => exact le_top
  | coe o =>
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at hab
    rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
    have := Order.add_one_le_of_lt hab
    rw [add_assoc] at this
    simpa [one_add_one_eq_two] using this

/-- **The collision lemma.**  Let `p` transform to `q` over the grades `grade`, let `d₁`, `d₂` be
cells of grade `1` whose source values are self-visible at `1`, carrying one target value `e` not
self-visible at `2`, and let `z` be a cell of grade `2` with `e < q z`.  Then `p d₁ = p d₂`.

The suppressor exceeds `e` at the grade `2`, so the shifter sends both source values to `e`; if
`p d₁ < p d₂`, the guard at the grade `2` gives
`σ (visibilityReplace 2 2 (p d₁)) = visibilityReplace 2 2 e`, which is above `e` but at most
`σ (p d₂) = e`. -/
theorem eq_of_transformsTo_collision {D : Type*} {grade : D → ℕ} {p q : D → Label.{u}}
    (h : TransformsTo grade p q) {d₁ d₂ z : D} (hg₁ : grade d₁ = 1) (hg₂ : grade d₂ = 1)
    (hz : grade z = 2) (hp₁ : IsSelfVisible 1 (p d₁)) (hp₂ : IsSelfVisible 1 (p d₂))
    {e : Label.{u}} (he₁ : q d₁ = e) (he₂ : q d₂ = e) (hev : ¬ IsSelfVisible 2 e)
    (hez : e < q z) : p d₁ = p d₂ := by
  obtain ⟨g, σ, hw, hq⟩ := h
  have hg2 : e < g 2 := hez.trans_le (by rw [hq z, hz]; exact min_le_right _ _)
  have hg1 : e < g 1 := hg2.trans_le (hw.antitone (by omega))
  have hσ (d : D) (hd : grade d = 1) (he : q d = e) : σ (p d) = e := by
    rw [hq d, hd] at he
    rcases le_total (σ (p d)) (g 1) with hle | hle
    · rwa [min_eq_left hle] at he
    · rw [min_eq_right hle] at he; exact absurd he hg1.ne'
  have key : ∀ a b, IsSelfVisible 1 a → a < b → σ a = e → σ b = e → False := by
    intro a b ha hab hσa hσb
    have hcomm := hw.visibilityReplace_comm a 2 (by rw [hσa]; exact hg2.le) 2 le_rfl
    rw [hσa] at hcomm
    have hle : σ (visibilityReplace 2 2 a) ≤ σ b :=
      hw.monotone (visibilityReplace_two_two_le_of_lt ha hab)
    rw [hcomm, hσb] at hle
    exact hev (le_antisymm hle (le_visibilityReplace (by omega) e))
  rcases lt_trichotomy (p d₁) (p d₂) with hlt | heq | hgt
  · exact (key _ _ hp₁ hlt (hσ d₁ hg₁ he₁) (hσ d₂ hg₂ he₂)).elim
  · exact heq
  · exact (key _ _ hp₂ hgt (hσ d₂ hg₂ he₂) (hσ d₁ hg₁ he₁)).elim

/-! ### The two-strip shifter: the ordered cell at `(univ, 2)` -/


/-! ### Transport between a completion and the amalgam -/

section Transport

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)

/-- The old cells of a completion keep their graded indices. -/
theorem gradedIndex_embed (d : Fin I.amalgam.card) :
    F.scheme.toCellScheme.gradedIndex (F.embed d) = I.amalgam.toCellScheme.gradedIndex d :=
  Prod.ext (F.scope_embed d) (F.isLowerEmbedding.grade_eq d)

/-- Below a pair of scope other than the ground set, the cells of a completion are the old
cells. -/
theorem image_embed_below {X : Finset (Fin (m + 2)) × ℕ} (hX : X.1 ≠ univ) :
    F.embed '' I.amalgam.toCellScheme.below X = F.scheme.toCellScheme.below X := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    change F.scheme.toCellScheme.gradedIndex (F.embed d) ≤ X
    rw [gradedIndex_embed]
    exact hd
  · intro hz
    have hne : F.scheme.toCellScheme.scope z ≠ univ := fun h ↦
      hX (univ_subset_iff.mp (by rw [← h]; exact hz.1))
    obtain ⟨d, rfl⟩ := F.mem_range_embed z hne
    refine ⟨d, ?_, rfl⟩
    change I.amalgam.toCellScheme.gradedIndex d ≤ X
    rw [← gradedIndex_embed]
    exact hz

/-- Below a pair of scope other than the ground set, lawfulness in the completion is lawfulness
in the amalgam, along the old cells. -/
theorem isLawfulBelow_embed_iff {X : Finset (Fin (m + 2)) × ℕ} (hX : X.1 ≠ univ)
    {w : Fin F.scheme.card → Label.{u}} :
    F.scheme.rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (F.embed d)) := by
  have h := Rows.isLawfulBelow_comap_iff (R := F.scheme.rows) F.isLowerEmbedding
    (image_embed_below F hX) (r := fun z ↦ w z)
  rw [F.comap_rows] at h
  exact h.symm

end Transport

/-! ### The separating cell -/

section Separation

variable {α : Ordinal.{u}}

/-- A cell of `TL` carried into a stage type along an embedding whose face is `TL`. -/
theorem exists_cell_TL {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (TL α)) (d : Fin 19) :
    ∃ e : Fin Am.card, Am.toCellScheme.gradedIndex e =
      Prod.map (Finset.map f) id (TwoFaceLiftCounterexample.cells.gradedIndex d) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (TL α).toScheme := congrArg StageType.toScheme he
  obtain ⟨i, hi⟩ : ∃ i : Fin (Am.toScheme.comap f).card,
      (Am.toScheme.comap f).toCellScheme.gradedIndex i =
        TwoFaceLiftCounterexample.cells.gradedIndex d := by
    rw [heq]; exact ⟨Fin.castSucc d, gradedIndex_TL_castSucc d⟩
  exact ⟨Am.toScheme.cellMap f i, by rw [← Am.toScheme.map_comap_gradedIndex f i, hi]⟩

/-- **The necessary condition for every completion of the asymmetric seed.**  Let `F` be a
completion below the full grade of a seed whose coatom types are `TL` and `T5`, `c` a cap
self-visible at `3`, `A ≠ ⊤` a label self-visible at `1` with `VisibilityReplaceFixedOfLT A ⊤`
(finite part `1` or at least `3`), and `q` lawful below `(univ, 3)` in `F` agreeing capped at `c`
with the prescription `(A_C, F_C, G) = (A, ⊤, ⊤)` on `C`.  Then some cell `u` of `F` at `(univ, 2)`
has `c ≤ q u` and its row reads `d₁ = ({3}, 1)` strictly below `d₂ = ({4}, 1)`.

Bountifulness of `F` from `(C, 3)` to `(univ, 3)` gives a lift `w`; on `D`, `w` is lawful in
`T5` and `⊤` at the cell of the common face of grade `3`, so `⊤` at `d₂`; availability from the
cell `(C, 2)`, labelled `⊤`, gives `u` at `(univ, 2)` with `w u = ⊤`, hence `c ≤ q u`; locality at
`u` with `w d₁ = A < ⊤ = w d₂` forces the row of `u` to read `d₁` below `d₂`. -/
theorem exists_separating_cell {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) (F : CompletionBelowFullGrade I)
    {c : Label.{u}} (hc : IsSelfVisible 3 c) {A : Label.{u}} (hA : IsSelfVisible 1 A)
    (hAc : VisibilityReplaceFixedOfLT A ⊤) (hAtop : A ≠ ⊤) {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hqp : ∀ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.last 4), 3) →
      min (q (F.embed d)) c =
        min (tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d)) c)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1)) :
    ∃ u : Fin F.scheme.card, F.scheme.toCellScheme.gradedIndex u = (univ, 2) ∧ c ≤ q u ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ := by
  classical
  -- The cells `s_C = (C, 2)` and `g = (E, 3)`.
  obtain ⟨sC, hsC⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hk₁ : tripleKind (({3} : Finset (Fin 5)), 1) = 1 := by decide
  have hks : tripleKind (({0, 1, 2, 3} : Finset (Fin 5)), 2) = 2 := by decide
  have hkg : tripleKind (({0, 1, 2} : Finset (Fin 5)), 3) = 5 := by decide
  set X : Finset (Fin 5) × ℕ := (univ.erase (Fin.last 4), 3) with hX_def
  set Y : Finset (Fin 5) × ℕ := ((univ : Finset (Fin 5)), 3) with hY_def
  have hXne : X.1 ≠ univ := by decide
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  -- The prescription, lawful below `(C, 3)`.
  set P : Fin F.scheme.card → Label.{u} := fun z ↦
    tripleLabelling A ⊤ ⊤ ⊤ ⊤ (F.scheme.toCellScheme.gradedIndex z) with hP
  have hPe (d : Fin I.amalgam.card) :
      P (F.embed d) = tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) := by
    simp only [hP, gradedIndex_embed]
  have hPlaw : F.scheme.rows.IsLawfulBelow X fun z ↦ P z := by
    rw [isLawfulBelow_embed_iff F hXne]
    simp only [hPe]
    exact (isLawfulBelow_tripleLabelling (I := I) hIL hIR hA (isSelfVisible_top 2)
      (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 3) le_rfl hAc le_rfl
      le_rfl).1
  -- The capped lift from `(C, 3)` to `(univ, 3)`.
  have hXg : X ∈ F.scheme.toCellScheme.gradedFaces := by
    refine ⟨?_, by decide, by decide⟩
    rw [F.faces_eq]
    obtain ⟨hf, -⟩ := (StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left
    rw [Coatom.univ_map_left] at hf
    exact hf
  have hYg : Y ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, by decide, by simp [hY_def]⟩
  have hl := F.isLegalBelowFullGrade.isBountiful.cappedLift hXg hYg hXY
  obtain ⟨x', hx'law, hx'c, hx'p⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp hl c hc
    (fun z ↦ P z) (fun z ↦ q z) hPlaw hq (fun z ↦ by
      have hz : (z : Fin F.scheme.card) ∈ F.embed '' I.amalgam.toCellScheme.below X := by
        rw [image_embed_below F hXne]; exact z.2
      obtain ⟨e, he, hze⟩ := hz
      change min (q z) c = min (P z) c
      rw [← hze, hPe]
      exact hqp e he)
  set w := Rows.extendBot Y x' with hw_def
  have hw : F.scheme.rows.IsLawfulBelow Y fun z ↦ w z := Rows.isLawfulBelow_extendBot.mpr hx'law
  have hwX (z : Fin F.scheme.card) (hz : z ∈ F.scheme.toCellScheme.below X) : w z = P z := by
    rw [hw_def, Rows.extendBot_of_mem x' (F.scheme.toCellScheme.below_mono hXY hz)]
    exact hx'p ⟨z, hz⟩
  have hwc (z : Fin F.scheme.card) (hz : z ∈ F.scheme.toCellScheme.below Y) :
      min (w z) c = min (q z) c := by
    rw [hw_def, Rows.extendBot_of_mem x' hz]
    exact hx'c ⟨z, hz⟩
  have hmem (d : Fin I.amalgam.card) {Z : Finset (Fin 5) × ℕ}
      (h : I.amalgam.toCellScheme.gradedIndex d ≤ Z) :
      F.embed d ∈ F.scheme.toCellScheme.below Z := by
    change F.scheme.toCellScheme.gradedIndex (F.embed d) ≤ Z
    rw [gradedIndex_embed]
    exact h
  have hd₁X := hmem d₁ (Z := X) (by rw [hd₁]; decide +kernel)
  have hsCX := hmem sC (Z := X) (by rw [hsC]; decide +kernel)
  have hgX := hmem gE (Z := X) (by rw [hgE]; decide +kernel)
  have hw₁ : w (F.embed d₁) = A := by
    rw [hwX _ hd₁X, hPe, hd₁]; simp only [tripleLabelling, hk₁]; rfl
  have hwS : w (F.embed sC) = ⊤ := by
    rw [hwX _ hsCX, hPe, hsC]; simp only [tripleLabelling, hks]; rfl
  have hwG : w (F.embed gE) = ⊤ := by
    rw [hwX _ hgX, hPe, hgE]; simp only [tripleLabelling, hkg]; rfl
  -- On `D`: the coupling `G ≤ A` of `T5` gives `w d₂ = ⊤`.
  set Z : Finset (Fin 5) × ℕ := (univ.erase (Fin.castSucc (Fin.last 3)), 2 + 1) with hZ
  have hZne : Z.1 ≠ univ := by decide
  have hZY : Z ≤ Y := ⟨subset_univ _, le_rfl⟩
  have hwZ : F.scheme.rows.IsLawfulBelow Z fun z ↦ w z := hw.mono hZY
  have hwZ' := (isLawfulBelow_embed_iff F hZne).mp hwZ
  have hD := le_of_isLawfulBelow_right hIR (w := fun d ↦ w (F.embed d)) hwZ' hd₂ hgE
  have hw₂ : w (F.embed d₂) = ⊤ := top_le_iff.mp (hwG ▸ hD)
  -- Availability from `s_C` gives the cell `u` at `(univ, 2)`.
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨t0, ht0⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq ((univ : Finset (Fin 5)), 2)
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, by decide, by simp⟩ (by decide)
  have ht0Y : t0 ∈ F.scheme.toCellScheme.below Y := by
    change F.scheme.toCellScheme.gradedIndex t0 ≤ Y
    rw [ht0]
    exact ⟨subset_rfl, by decide⟩
  have hgsC : F.scheme.toCellScheme.grade (F.embed sC) = 2 :=
    (congrArg Prod.snd (gradedIndex_embed F sC)).trans (congrArg Prod.snd hsC)
  obtain ⟨u, hu, hle⟩ := havail (F.embed sC) t0 ht0Y
    (by rw [show F.scheme.toCellScheme.scope t0 = univ from congrArg Prod.fst ht0]
        exact subset_univ _)
    (by rw [hgsC]; exact (congrArg Prod.snd ht0).symm)
  have hu' : F.scheme.toCellScheme.gradedIndex u = (univ, 2) := hu.trans ht0
  have huY : u ∈ F.scheme.toCellScheme.below Y := by
    change F.scheme.toCellScheme.gradedIndex u ≤ Y
    rw [hu']
    exact ⟨subset_rfl, by decide⟩
  have hwu : w u = ⊤ := top_le_iff.mp (hwS ▸ hle)
  refine ⟨u, hu', ?_, fun h₁ h₂ ↦ ?_⟩
  · have := hwc u huY
    rw [hwu, min_top_left] at this
    exact min_eq_right_iff.mp this.symm
  · -- Locality at `u`.
    by_contra hcon
    rw [not_lt] at hcon
    have hg₁ : F.scheme.toCellScheme.grade (F.embed d₁) = 1 :=
      (congrArg Prod.snd (gradedIndex_embed F d₁)).trans (congrArg Prod.snd hd₁)
    have hg₂ : F.scheme.toCellScheme.grade (F.embed d₂) = 1 :=
      (congrArg Prod.snd (gradedIndex_embed F d₂)).trans (congrArg Prod.snd hd₂)
    have h21 := (hloc u huY).le_of_le (d := ⟨_, h₂⟩) (d' := ⟨_, h₁⟩) hcon
      (by simp only [hg₁, hg₂, le_refl])
    simp only at h21
    rw [hw₂, hw₁, hwu, min_top_right, min_top_right] at h21
    exact hAtop (top_le_iff.mp h21)

/-- **Every completion of the asymmetric seed has a separating cell at `(univ, 2)`**: a cell whose
row reads `({3}, 1)` strictly below `({4}, 1)`.  (The case `c = ⊥`, `q = ⊥`, `A = 1` of
`exists_separating_cell`.) -/
theorem exists_separating_cell_of_completion {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) (F : CompletionBelowFullGrade I) :
    ∃ (d₁ d₂ : Fin I.amalgam.card) (u : Fin F.scheme.card),
      I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, 2) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ := by
  obtain ⟨d₁, hd₁⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨u, hu, -, hsep⟩ := exists_separating_cell hIL hIR F (c := ⊥) (isSelfVisible_bot 3)
    (A := TwoFaceLiftCounterexample.v1) (isSelfVisible_gridPoint 1 0)
    (fun _ ↦ by rw [TwoFaceLiftCounterexample.v1_eq, Label.visibilityReplace_natCast]; simp)
    (gridPoint_ne_top 1 0) (q := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
    (fun _ _ ↦ by simp) hd₁ hd₂
  exact ⟨d₁, d₂, u, hd₁, hd₂, hu, hsep⟩

/-- **For the asymmetric seed `seedL`.** -/
theorem exists_separating_cell_seedL (F : CompletionBelowFullGrade (seedL α)) :
    ∃ (d₁ d₂ : Fin (seedL α).amalgam.card) (u : Fin F.scheme.card),
      (seedL α).amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      (seedL α).amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, 2) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ :=
  exists_separating_cell_of_completion rfl rfl F

end Separation


/-- **No collision at a separating cell of a completion.**  If the row of a cell `u` of a
completion at `(univ, 2)` reads `d₁` strictly below `d₂`, every labelling lawful below
`(univ, 2)` that carries one label `e` of finite part `1` (not self-visible at `2`) at `d₁` and
`d₂` has `x u ≤ e`. -/
theorem le_of_separating {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}
    (F : CompletionBelowFullGrade I) {u : Fin F.scheme.card}
    (hu : F.scheme.toCellScheme.gradedIndex u = (univ, 2)) {d₁ d₂ : Fin I.amalgam.card}
    (hg₁ : I.amalgam.toCellScheme.grade d₁ = 1) (hg₂ : I.amalgam.toCellScheme.grade d₂ = 1)
    (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
    (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
    (hsep : F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩)
    {x : Fin F.scheme.card → Label.{u}}
    (hx : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 2) fun z ↦ x z)
    {e : Label.{u}} (hx₁ : x (F.embed d₁) = e) (hx₂ : x (F.embed d₂) = e)
    (hev : ¬ IsSelfVisible 2 e) : x u ≤ e := by
  by_contra hlt
  rw [not_le] at hlt
  have huY : u ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), 2) := by
    change F.scheme.toCellScheme.gradedIndex u ≤ _; rw [hu]
  have hloc := (Rows.isLawfulBelow_iff_forall.mp hx).2.1 u huY
  have hG₁ : F.scheme.toCellScheme.grade (F.embed d₁) = 1 :=
    (F.isLowerEmbedding.grade_eq d₁).trans hg₁
  have hG₂ : F.scheme.toCellScheme.grade (F.embed d₂) = 1 :=
    (F.isLowerEmbedding.grade_eq d₂).trans hg₂
  have hor := F.isLegalBelowFullGrade.isConsistent.isOrderly u
  have heq := eq_of_transformsTo_collision hloc (d₁ := ⟨_, h₁⟩) (d₂ := ⟨_, h₂⟩)
    (z := ⟨u, F.scheme.toCellScheme.mem_below_gradedIndex u⟩) hG₁ hG₂
    (congrArg Prod.snd hu) (hG₁ ▸ hor ⟨_, h₁⟩) (hG₂ ▸ hor ⟨_, h₂⟩)
    (by simp only; rw [hx₁, min_eq_left hlt.le]) (by simp only; rw [hx₂, min_eq_left hlt.le])
    hev (by simp only [min_self]; exact hlt)
  exact absurd heq hsep.ne


end VaughtConjecture.ThinCompletion

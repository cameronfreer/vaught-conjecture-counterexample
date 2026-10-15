/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Sentence.TemplateSentence

/-!
# Satisfaction of `σ[L]`, clause by clause

Numbering as in the current draft of [AFK26].  `IsTemplateSentenceModel M` states, one field for
each conjunct of `templateSentence`, the satisfaction of that conjunct in a structure of `L_c[L]`,
with the bound variables read as tuples (`realize_templateSentence_iff`).  The infinitary formula
`a ∈ cl({b_i})` of [AFK26, Definition 4.13] is `InClosure a b`.  Correspondence with the printed
definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal BoundedFormulaω TemplateSentence

variable {M : Type v} [baseTemplateLanguage.{u}.Structure M]

/-- `P_k(xs)` in a structure of `L_c[L]`, for `k ≥ 1`. -/
abbrev ClosedRel {k : ℕ} (hk : 0 < k) (xs : Fin k → M) : Prop :=
  RelMap (L := baseTemplateLanguage.{u}) (BaseSymbol.closed hk) xs

/-- **`a ∈ cl({b_i}_{i ∈ ι})`** [AFK26, Definition 4.13], read in a structure: there is a tuple
`e` on `m + 1 ≥ 1` points with `P_{m+1}(e)` containing `a` and every `b_i`, such that every
sequence `e ∘ i` of its places with `P(e ∘ i)` containing every `b_r` contains `a`.
Correspondence with the printed definitions. -/
def InClosure {ι : Type} (a : M) (b : ι → M) : Prop :=
  ∃ (m : ℕ) (e : Fin (m + 1) → M), (∀ r, b r ∈ Set.range e) ∧ a ∈ Set.range e ∧
    ClosedRel.{u} m.succ_pos e ∧ ∀ (k : ℕ) (i : Fin (k + 1) → Fin (m + 1)),
      ClosedRel.{u} k.succ_pos (e ∘ i) → (∀ r, b r ∈ Set.range (e ∘ i)) → a ∈ Set.range (e ∘ i)

/-- `R_t(xs)` in a structure of `L_c[L]`, for `t ∈ cR[L]^{n+1}`. -/
abbrev ClassRel {n : ℕ} (t : ClassSymbol.{u} (n + 1)) (xs : Fin (n + 1) → M) : Prop :=
  RelMap (L := baseTemplateLanguage.{u}) (t.toBaseSymbol n.succ_pos) xs

variable (M) in
/-- **Satisfaction of `σ[L]`, clause by clause** [AFK26, Definitions 2.1, 4.13 and 4.22]: one field
for each conjunct of `templateSentence`.  Correspondence with the printed definitions. -/
structure IsTemplateSentenceModel : Prop where
  /-- `Th_Geo`, first clause, first sentence. -/
  distinct : ∀ (n : ℕ) (x : Fin (n + 1) → M), ClosedRel.{u} n.succ_pos x →
    ∀ i j, i < j → x i ≠ x j
  /-- `Th_Geo`, first clause, second sentence. -/
  perm : ∀ (n : ℕ) (x : Fin (n + 1) → M) (σ : Equiv.Perm (Fin (n + 1))),
    ClosedRel.{u} n.succ_pos x ↔ ClosedRel.{u} n.succ_pos (x ∘ σ)
  /-- `Th_Geo`, second clause. -/
  extension : ∀ (n : ℕ) (x : Fin (n + 1) → M), (∀ i j, i < j → x i ≠ x j) →
    ∃ (k : ℕ) (y : Fin k → M), ClosedRel.{u} (Nat.lt_add_right k n.succ_pos) (Fin.append x y)
  /-- `Th_Geo`, third clause. -/
  inter : ∀ (n₀ n₁ k : ℕ) (x : Fin (n₀ + 1) → M) (y : Fin (n₁ + 1) → M) (z : Fin (k + 1) → M),
    ClosedRel.{u} n₀.succ_pos x → ClosedRel.{u} n₁.succ_pos y → (∀ l l', l < l' → z l ≠ z l') →
      (∀ l, (∃ i, z l = x i) ∧ ∃ j, z l = y j) → (∀ i j, x i = y j → ∃ l, x i = z l) →
        ClosedRel.{u} k.succ_pos z
  /-- (Singletons). -/
  singletons : ∀ x : M, ClosedRel.{u} Nat.one_pos ![x]
  /-- (Convexity). -/
  convexity : ∀ (n : ℕ) (x : Fin (n + 1) → M) (y z : M), ClosedRel.{u} n.succ_pos x → y ≠ z →
    (∀ i, x i ≠ y ∧ x i ≠ z) → InClosure.{u} y (fun o : Option (Fin (n + 1)) ↦ o.elim z x) →
      ¬ InClosure.{u} z (fun o : Option (Fin (n + 1)) ↦ o.elim y x)
  /-- (Extreme Points), first sentence. -/
  extremePoints : ∀ (m : ℕ) (x : Fin (m + 3) → M), ClosedRel.{u} (by omega) x →
    ∃ i j : Fin (m + 3), i < j ∧ ClosedRel.{u} (k := m + 2) (by omega) (x ∘ i.succAbove) ∧
      ClosedRel.{u} (k := m + 2) (by omega) (x ∘ j.succAbove)
  /-- (Extreme Points), second sentence. -/
  extremePointsExclusion : ∀ (m : ℕ) (x : Fin (m + 3) → M), ClosedRel.{u} (by omega) x →
    ¬ (ClosedRel.{u} (k := m + 2) (by omega) (x ∘ (0 : Fin (m + 3)).succAbove) ∧
      ClosedRel.{u} (k := m + 2) (by omega) (x ∘ (1 : Fin (m + 3)).succAbove) ∧
      ClosedRel.{u} (k := m + 2) (by omega) (x ∘ (2 : Fin (m + 3)).succAbove))
  /-- Clause (b), first sentence. -/
  typing : ∀ (n : ℕ) (x : Fin (n + 1) → M),
    ClosedRel.{u} n.succ_pos x ↔ ∃ t : ClassSymbol.{u} (n + 1), ClassRel t x
  /-- Clause (b), second sentence. -/
  exclusive : ∀ (n : ℕ) (t t' : ClassSymbol.{u} (n + 1)), t ≠ t' → ∀ x : Fin (n + 1) → M,
    ClassRel t x → ¬ ClassRel t' x
  /-- Clause (b), third sentence. -/
  determines : ∀ (n : ℕ) (t : ClassSymbol.{u} (n + 1)) (k : ℕ) (S : BaseSymbol.{u} k)
    (i : Fin k → Fin (n + 1)) (x y : Fin (n + 1) → M), ClassRel t x → ClassRel t y →
      (RelMap (L := baseTemplateLanguage.{u}) S (x ∘ i) ↔
        RelMap (L := baseTemplateLanguage.{u}) S (y ∘ i))
  /-- Clause (c), the positive and the negative pairs together. -/
  diagram : ∀ (n : ℕ) (t : ClassSymbol.{u} (n + 1)) (x : Fin (n + 1) → M), ClassRel t x →
    ∀ (k : ℕ) (S : BaseSymbol.{u} k) (i : Fin k → Fin (n + 1)),
      (RelMap (L := baseTemplateLanguage.{u}) S (x ∘ i) ↔ t.1.1.Holds S.toTemplateSymbol i)
  /-- Clause (d). -/
  density : ∀ (k n m : ℕ) (tt : DensityIndex.{u} n m) (x : Fin (n + 1) → M), ClassRel tt.1.1 x →
    ∃ (y : Fin m → M) (s : ClassSymbol.{u} (n + 1 + m)),
      s.1.1.TruncEquiv k tt.1.2.1.1 ∧
        RelMap (L := baseTemplateLanguage.{u}) (s.toBaseSymbol (Nat.lt_add_right m n.succ_pos))
          (Fin.append x y)

/-! ### Realization of the helpers -/

namespace TemplateSentence

variable {N : ℕ} {v : Empty → M} {xs : Fin N → M}

@[simp] theorem realize_atomAt {k : ℕ} (r : BaseSymbol.{u} k) (f : Fin k → Fin N) :
    (atomAt r f).Realize v xs ↔ RelMap (L := baseTemplateLanguage.{u}) r (xs ∘ f) :=
  Iff.rfl

@[simp] theorem realize_eqAt (i j : Fin N) : (eqAt.{u} i j).Realize v xs ↔ xs i = xs j :=
  Iff.rfl

@[simp] theorem realize_closedAt (k : ℕ) (hk : 0 < k) (f : Fin k → Fin N) :
    (closedAt.{u} k hk f).Realize v xs ↔ ClosedRel.{u} hk (xs ∘ f) :=
  Iff.rfl

@[simp] theorem realize_memAmong {m : ℕ} (a : Fin N) (e : Fin m → Fin N) :
    (memAmong.{u} a e).Realize v xs ↔ xs a ∈ Set.range (xs ∘ e) := by
  simp only [memAmong, realize_ciSup, realize_eqAt, Set.mem_range, Function.comp_apply]
  exact exists_congr fun _ ↦ eq_comm

@[simp] theorem realize_distinctAt {k : ℕ} (f : Fin k → Fin N) :
    (distinctAt.{u} f).Realize v xs ↔ ∀ i j, i < j → xs (f i) ≠ xs (f j) := by
  simp only [distinctAt, realize_ciInf, realize_not, realize_eqAt, Subtype.forall, Prod.forall]

omit [baseTemplateLanguage.{u}.Structure M] in
theorem comp_optionElim {n : ℕ} (p : Fin N) (f : Fin n → Fin N) :
    xs ∘ (fun o : Option (Fin n) ↦ o.elim p f) = fun o ↦ o.elim (xs p) (xs ∘ f) :=
  funext fun o ↦ by cases o <;> rfl

omit [baseTemplateLanguage.{u}.Structure M] in
theorem append_comp_castAdd {m : ℕ} (ys : Fin m → M) :
    Fin.append xs ys ∘ Fin.castAdd m = xs :=
  funext fun i ↦ Fin.append_left xs ys i

omit [baseTemplateLanguage.{u}.Structure M] in
theorem append_comp_natAdd {m : ℕ} (ys : Fin m → M) :
    Fin.append xs ys ∘ Fin.natAdd N = ys :=
  funext fun i ↦ Fin.append_right xs ys i

theorem realize_closureFormula {ι : Type} [Countable ι] (a : Fin N) (b : ι → Fin N) :
    (closureFormula.{u} a b).Realize v xs ↔ InClosure.{u} (xs a) (xs ∘ b) := by
  simp only [closureFormula, realize_ciSup, realize_existsBlock, realize_inf, realize_ciInf,
    realize_memAmong, realize_closedAt, realize_imp, Sigma.forall]
  refine exists_congr fun m ↦ ⟨fun ⟨e, ⟨⟨hb, ha⟩, hP⟩, hall⟩ ↦ ⟨e, fun r ↦ ?_, ?_, ?_, ?_⟩,
    fun ⟨e, hb, ha, hP, hall⟩ ↦ ⟨e, ⟨⟨fun r ↦ ?_, ?_⟩, ?_⟩, ?_⟩⟩
  · simpa [Fin.append_left, append_comp_natAdd] using hb r
  · simpa [Fin.append_left, append_comp_natAdd] using ha
  · simpa [append_comp_natAdd] using hP
  · intro k i hi hbi
    have := hall k i
    simp only [← Function.comp_assoc, append_comp_natAdd, Fin.append_left] at this
    exact this ⟨hi, hbi⟩
  · simpa [Fin.append_left, append_comp_natAdd] using hb r
  · simpa [Fin.append_left, append_comp_natAdd] using ha
  · simpa [append_comp_natAdd] using hP
  · intro k i
    simp only [← Function.comp_assoc, append_comp_natAdd, Fin.append_left]
    exact fun ⟨hi, hbi⟩ ↦ hall k i hi hbi

end TemplateSentence

/-! ### Realization of the clauses -/

section Clauses

variable (M)

theorem realize_geometryDistinctClause : geometryDistinctClause.{u}.Realize M ↔
    ∀ (n : ℕ) (x : Fin (n + 1) → M), ClosedRel.{u} n.succ_pos x → ∀ i j, i < j → x i ≠ x j := by
  simp [geometryDistinctClause, Sentenceω.realize_def, realize_ciInf]

theorem realize_geometryPermClause : geometryPermClause.{u}.Realize M ↔
    ∀ (n : ℕ) (x : Fin (n + 1) → M) (σ : Equiv.Perm (Fin (n + 1))),
      ClosedRel.{u} n.succ_pos x ↔ ClosedRel.{u} n.succ_pos (x ∘ σ) := by
  simp only [geometryPermClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_iff,
    realize_closedAt, Function.comp_id]
  exact ⟨fun h n x σ ↦ h n σ x, fun h n σ x ↦ h n x σ⟩

theorem realize_geometryExtensionClause : geometryExtensionClause.{u}.Realize M ↔
    ∀ (n : ℕ) (x : Fin (n + 1) → M), (∀ i j, i < j → x i ≠ x j) →
      ∃ (k : ℕ) (y : Fin k → M),
        ClosedRel.{u} (Nat.lt_add_right k n.succ_pos) (Fin.append x y) := by
  simp [geometryExtensionClause, Sentenceω.realize_def, realize_ciInf, realize_ciSup,
    realize_existsBlock]

theorem realize_geometryIntersectionClause : geometryIntersectionClause.{u}.Realize M ↔
    ∀ (n₀ n₁ k : ℕ) (x : Fin (n₀ + 1) → M) (y : Fin (n₁ + 1) → M) (z : Fin (k + 1) → M),
      ClosedRel.{u} n₀.succ_pos x → ClosedRel.{u} n₁.succ_pos y →
        (∀ l l', l < l' → z l ≠ z l') → (∀ l, (∃ i, z l = x i) ∧ ∃ j, z l = y j) →
          (∀ i j, x i = y j → ∃ l, x i = z l) → ClosedRel.{u} k.succ_pos z := by
  simp only [geometryIntersectionClause, Sentenceω.realize_def, realize_ciInf, realize_alls,
    realize_imp, realize_inf, realize_closedAt, realize_distinctAt, realize_memAmong,
    realize_eqAt, Prod.forall]
  constructor
  · intro h n₀ n₁ k x y z hx hy hz hzxy hxyz
    have := h n₀ n₁ k (Fin.append (Fin.append x y) z)
    simp only [Function.comp_def, Fin.append_left, Fin.append_right] at this
    refine this ⟨⟨hx, hy⟩, ⟨hz, fun l ↦ ⟨?_, ?_⟩⟩, fun i j hij ↦ ?_⟩
    · obtain ⟨i, hi⟩ := (hzxy l).1
      exact ⟨i, hi.symm⟩
    · obtain ⟨j, hj⟩ := (hzxy l).2
      exact ⟨j, hj.symm⟩
    · obtain ⟨l, hl⟩ := hxyz i j hij
      exact ⟨l, hl.symm⟩
  · rintro h a b c ys ⟨⟨hx, hy⟩, ⟨hz, hm⟩, hc⟩
    refine h a b c _ _ _ hx hy hz (fun l ↦ ?_) (fun i j hij ↦ ?_)
    · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hm l
      exact ⟨⟨i, hi.symm⟩, ⟨j, hj.symm⟩⟩
    · obtain ⟨l, hl⟩ := hc i j hij
      exact ⟨l, hl.symm⟩

theorem realize_singletonsClause : singletonsClause.{u}.Realize M ↔
    ∀ x : M, ClosedRel.{u} Nat.one_pos ![x] := by
  simp only [singletonsClause, Sentenceω.realize_def, realize_alls, realize_closedAt,
    Function.comp_id]
  refine ⟨fun h x ↦ h ![x], fun h ys ↦ ?_⟩
  have hys : ys = ![ys 0] := funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
  rw [hys]
  exact h _

theorem realize_convexityClause : convexityClause.{u}.Realize M ↔
    ∀ (n : ℕ) (x : Fin (n + 1) → M) (y z : M), ClosedRel.{u} n.succ_pos x → y ≠ z →
      (∀ i, x i ≠ y ∧ x i ≠ z) → InClosure.{u} y (fun o : Option (Fin (n + 1)) ↦ o.elim z x) →
        ¬ InClosure.{u} z (fun o : Option (Fin (n + 1)) ↦ o.elim y x) := by
  simp only [convexityClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_inf, realize_closedAt, realize_not, realize_eqAt, realize_closureFormula,
    comp_optionElim]
  constructor
  · intro h n x y z hx hyz hxyz
    have := h n (Fin.append x ![y, z])
    rw [append_comp_castAdd] at this
    simp only [Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact this ⟨⟨hx, hyz⟩, fun i ↦ ⟨by simpa using (hxyz i).1, by simpa using (hxyz i).2⟩⟩
  · intro h n ws hyp
    exact h n _ _ _ hyp.1.1 hyp.1.2 hyp.2

theorem realize_extremePointsClause : extremePointsClause.{u}.Realize M ↔
    ∀ (m : ℕ) (x : Fin (m + 3) → M), ClosedRel.{u} (by omega) x →
      ∃ i j : Fin (m + 3), i < j ∧ ClosedRel.{u} (k := m + 2) (by omega) (x ∘ i.succAbove) ∧
        ClosedRel.{u} (k := m + 2) (by omega) (x ∘ j.succAbove) := by
  simp only [extremePointsClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_ciSup, realize_inf, realize_closedAt, Function.comp_id, Subtype.exists, Prod.exists]
  exact ⟨fun h m x hx ↦ by
    obtain ⟨a, b, hab, h'⟩ := h m x hx
    exact ⟨a, b, hab, h'⟩, fun h m x hx ↦ by
    obtain ⟨a, b, hab, h'⟩ := h m x hx
    exact ⟨a, b, hab, h'⟩⟩

theorem realize_extremePointsExclusionClause : extremePointsExclusionClause.{u}.Realize M ↔
    ∀ (m : ℕ) (x : Fin (m + 3) → M), ClosedRel.{u} (by omega) x →
      ¬ (ClosedRel.{u} (k := m + 2) (by omega) (x ∘ (0 : Fin (m + 3)).succAbove) ∧
        ClosedRel.{u} (k := m + 2) (by omega) (x ∘ (1 : Fin (m + 3)).succAbove) ∧
        ClosedRel.{u} (k := m + 2) (by omega) (x ∘ (2 : Fin (m + 3)).succAbove)) := by
  simp only [extremePointsExclusionClause, Sentenceω.realize_def, realize_ciInf, realize_alls,
    realize_imp, realize_not, realize_inf, realize_closedAt, Function.comp_id, and_assoc]

theorem realize_typingClause : typingClause.{u}.Realize M ↔
    ∀ (n : ℕ) (x : Fin (n + 1) → M),
      ClosedRel.{u} n.succ_pos x ↔ ∃ t : ClassSymbol.{u} (n + 1), ClassRel t x := by
  simp only [typingClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_iff,
    realize_ciSup, realize_closedAt, realize_atomAt, Function.comp_id]

theorem realize_exclusivityClause : exclusivityClause.{u}.Realize M ↔
    ∀ (n : ℕ) (t t' : ClassSymbol.{u} (n + 1)), t ≠ t' → ∀ x : Fin (n + 1) → M,
      ClassRel t x → ¬ ClassRel t' x := by
  simp only [exclusivityClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_not, realize_atomAt, Function.comp_id, Subtype.forall, Prod.forall]

theorem realize_determinationClause : determinationClause.{u}.Realize M ↔
    ∀ (n : ℕ) (t : ClassSymbol.{u} (n + 1)) (k : ℕ) (S : BaseSymbol.{u} k)
      (i : Fin k → Fin (n + 1)) (x y : Fin (n + 1) → M), ClassRel t x → ClassRel t y →
        (RelMap (L := baseTemplateLanguage.{u}) S (x ∘ i) ↔
          RelMap (L := baseTemplateLanguage.{u}) S (y ∘ i)) := by
  simp only [determinationClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_inf, realize_iff, realize_atomAt, Sigma.forall, Prod.forall]
  constructor
  · intro h n t k S i x y hx hy
    have := h n t k S i (Fin.append x y)
    rw [← Function.comp_assoc, ← Function.comp_assoc, append_comp_castAdd,
      append_comp_natAdd] at this
    exact this ⟨hx, hy⟩
  · intro h n t k S i ws hxy
    rw [← Function.comp_assoc, ← Function.comp_assoc]
    exact h n t k S i _ _ hxy.1 hxy.2

theorem realize_diagramClause : diagramClause.{u}.Realize M ↔
    ∀ (n : ℕ) (t : ClassSymbol.{u} (n + 1)) (x : Fin (n + 1) → M), ClassRel t x →
      ∀ (k : ℕ) (S : BaseSymbol.{u} k) (i : Fin k → Fin (n + 1)),
        (RelMap (L := baseTemplateLanguage.{u}) S (x ∘ i) ↔ t.1.1.Holds S.toTemplateSymbol i) := by
  simp only [diagramClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_inf, realize_not, realize_atomAt, Function.comp_id, Subtype.forall, Sigma.forall,
    Prod.forall]
  constructor
  · intro h n t x hx k S i
    by_cases hh : t.1.1.Holds S.toTemplateSymbol i
    · exact iff_of_true ((h n t).1 k S i hh x hx) hh
    · exact iff_of_false ((h n t).2 k S i hh x hx) hh
  · intro h n t
    exact ⟨fun k S i hh x hx ↦ (h n t x hx k S i).mpr hh,
      fun k S i hh x hx hS ↦ hh ((h n t x hx k S i).mp hS)⟩

theorem realize_densityClause : densityClause.{u}.Realize M ↔
    ∀ (k n m : ℕ) (tt : DensityIndex.{u} n m) (x : Fin (n + 1) → M), ClassRel tt.1.1 x →
      ∃ (y : Fin m → M) (s : ClassSymbol.{u} (n + 1 + m)),
        s.1.1.TruncEquiv k tt.1.2.1.1 ∧
          RelMap (L := baseTemplateLanguage.{u}) (s.toBaseSymbol (Nat.lt_add_right m n.succ_pos))
            (Fin.append x y) := by
  simp only [densityClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_imp,
    realize_existsBlock, realize_ciSup, realize_atomAt, Function.comp_id, Subtype.exists,
    exists_prop]

/-- **Satisfaction of `σ[L]`**: a structure of `L_c[L]` satisfies `templateSentence` exactly when
it satisfies each clause (`IsTemplateSentenceModel`).
Correspondence with the printed definitions. -/
theorem realize_templateSentence_iff :
    templateSentence.{u}.Realize M ↔ IsTemplateSentenceModel.{u} M := by
  have hinf : ∀ φ ψ : baseTemplateLanguage.{u}.Sentenceω,
      (φ ⊓ ψ).Realize M ↔ φ.Realize M ∧ ψ.Realize M := fun φ ψ ↦ by
    simp only [Sentenceω.realize_def, realize_inf]
  simp only [templateSentence, planClause, structureClause, hinf,
    realize_geometryDistinctClause, realize_geometryPermClause, realize_geometryExtensionClause,
    realize_geometryIntersectionClause, realize_singletonsClause, realize_convexityClause,
    realize_extremePointsClause, realize_extremePointsExclusionClause, realize_typingClause,
    realize_exclusivityClause, realize_determinationClause, realize_diagramClause,
    realize_densityClause]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, ⟨⟨h9, h10⟩, h11⟩⟩, h12⟩, h13⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, ⟨⟨h9, h10⟩, h11⟩⟩, h12⟩, h13⟩

end Clauses

end VaughtConjecture

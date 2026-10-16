/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Sentence.Reduct

/-!
# Examples: the closure of the empty family

Tests of the closure formula `a ∈ cl({b_i})` of [AFK26, Definition 4.13] (`InClosure`) on an
empty family of generators.  Nothing here changes `templateSentence` or any of its clauses.

* **What the formula says** (`inClosure_of_isEmpty_iff`): with no generators, the clause on the
  generators is vacuous, and `a ∈ cl(∅)` says that some closed tuple `e` contains `a` and every
  closed subtuple of `e` contains `a`.
* **A closed singleton is enough** (`inClosure_of_isEmpty_of_closedRel`): the one-point tuple
  `(a)` (the witness with `m = 0`) is a witness as soon as `P₁(a)`.  So in a model of `σ[L]`,
  where (Singletons) gives `P₁(a)` for every `a`, every point lies in the closure of the empty
  family (`IsTemplateSentenceModel.inClosure_of_isEmpty`).
* **The comparison with the hull is claimed only for nonempty generators.**  The hull of `∅` in a
  plan is empty, because `∅` is a face (`not_mem_hull_empty_of_isPlan`).  On one point, every
  premise of `mem_hull_of_inClosure` other than `S.Nonempty` holds for `S = ∅`, and its
  conclusion fails (`IsTemplateSentenceModel.mem_hull_of_inClosure_fails_of_empty`): the premise
  `S.Nonempty` cannot be dropped.
* **The sentence never uses the empty case**: the families of (Convexity) are indexed by
  `Option (Fin (n + 1))`, which is nonempty.

Correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Finset

variable {M : Type v} [baseTemplateLanguage.{u}.Structure M]

/-! ### The closure formula on an empty family -/

/-- **`a ∈ cl(∅)`, unfolded**: for an empty index type, the clause on the generators is vacuous,
and `InClosure a b` says that some closed tuple `e` contains `a` and every closed subtuple of `e`
contains `a`. -/
theorem inClosure_of_isEmpty_iff {ι : Type} [IsEmpty ι] (a : M) (b : ι → M) :
    InClosure.{u} a b ↔ ∃ (m : ℕ) (e : Fin (m + 1) → M), a ∈ Set.range e ∧
      ClosedRel.{u} m.succ_pos e ∧ ∀ (k : ℕ) (i : Fin (k + 1) → Fin (m + 1)),
        ClosedRel.{u} k.succ_pos (e ∘ i) → a ∈ Set.range (e ∘ i) :=
  exists₂_congr fun _ _ ↦
    ⟨fun ⟨_, ha, hP, hall⟩ ↦ ⟨ha, hP, fun k i hi ↦ hall k i hi isEmptyElim⟩,
      fun ⟨ha, hP, hall⟩ ↦ ⟨isEmptyElim, ha, hP, fun k i hi _ ↦ hall k i hi⟩⟩

/-- The same, for the family indexed by `Fin 0`. -/
example (a : M) (b : Fin 0 → M) :
    InClosure.{u} a b ↔ ∃ (m : ℕ) (e : Fin (m + 1) → M), a ∈ Set.range e ∧
      ClosedRel.{u} m.succ_pos e ∧ ∀ (k : ℕ) (i : Fin (k + 1) → Fin (m + 1)),
        ClosedRel.{u} k.succ_pos (e ∘ i) → a ∈ Set.range (e ∘ i) :=
  inClosure_of_isEmpty_iff a b

/-- **A closed singleton lies in the closure of the empty family**: if `P₁(a)`, the one-point
tuple `(a)` witnesses `a ∈ cl(∅)` (with `m = 0`), since each of its subtuples is `(a)`. -/
theorem inClosure_of_isEmpty_of_closedRel {ι : Type} [IsEmpty ι] {a : M} (b : ι → M)
    (ha : ClosedRel.{u} Nat.one_pos ![a]) : InClosure.{u} a b :=
  (inClosure_of_isEmpty_iff a b).mpr
    ⟨0, ![a], ⟨0, rfl⟩, ha, fun _ i _ ↦ ⟨0, by simp⟩⟩

variable (M) in
/-- **In a model of `σ[L]` every point lies in the closure of the empty family**, by
(Singletons). -/
theorem IsTemplateSentenceModel.inClosure_of_isEmpty (hM : IsTemplateSentenceModel.{u} M)
    {ι : Type} [IsEmpty ι] (a : M) (b : ι → M) : InClosure.{u} a b :=
  inClosure_of_isEmpty_of_closedRel b (hM.singletons a)

/-! ### The hull comparison needs nonempty generators -/

/-- **The hull of `∅` in a plan is empty**, since `∅` is a face of every plan. -/
theorem not_mem_hull_empty_of_isPlan {N : ℕ} {A : Finset (Fin N)} {F : Finset (Finset (Fin N))}
    (hF : Geometry.IsPlan A F) (p : Fin N) : p ∉ Geometry.hull A F ∅ := fun h ↦
  Finset.notMem_empty p ((Geometry.mem_hull.mp h).2 ∅ hF.empty_mem (Finset.empty_subset _))

variable (M) in
/-- **`mem_hull_of_inClosure` fails for the empty family.**  In a model of `σ[L]`, take the
one-point tuple `w = (a)` and the faces `F = {∅, {0}}` of the plan on one point.  Every premise of
`mem_hull_of_inClosure` other than `S.Nonempty` holds for the empty family of generators, with
`S = ∅`, the witness `e' = (a)` and the position `0` of `a`: `w` is injective, its closed
subtuples are the faces of `F`, every closed subtuple of `e'` contains `a`, `e'` contains `w`,
and `S` contains every (absent) generator.  The conclusion fails: `0` is not in the hull of `∅`.
So the comparison of `cl` with the hull holds only for nonempty families of generators. -/
theorem IsTemplateSentenceModel.mem_hull_of_inClosure_fails_of_empty
    (hM : IsTemplateSentenceModel.{u} M) (a : M) :
    Geometry.IsPlan ({0} : Finset (Fin 1)) {∅, {0}} ∧
      Function.Injective ![a] ∧
      (∀ (k : ℕ) (e : Fin (k + 1) ↪ Fin 1),
        ClosedRel.{u} k.succ_pos (![a] ∘ e) ↔ univ.map e ∈ ({∅, {0}} : Finset (Finset (Fin 1)))) ∧
      (∀ (k : ℕ) (i : Fin (k + 1) → Fin 1), ClosedRel.{u} k.succ_pos (![a] ∘ i) →
        (∀ r : Fin 0, (Fin.elim0 r : M) ∈ Set.range (![a] ∘ i)) → a ∈ Set.range (![a] ∘ i)) ∧
      (∀ l : Fin 1, ![a] l ∈ Set.range ![a]) ∧
      (∀ r : Fin 0, ∃ s ∈ (∅ : Finset (Fin 1)), ![a] s = (Fin.elim0 r : M)) ∧
      ![a] 0 = a ∧
      (0 : Fin 1) ∉ Geometry.hull univ ({∅, {0}} : Finset (Finset (Fin 1))) ∅ := by
  refine ⟨Geometry.IsPlan.singleton 0, Function.injective_of_subsingleton _, fun k e ↦ ?_,
    fun _ i _ _ ↦ ⟨0, by simp⟩, fun l ↦ ⟨l, rfl⟩, fun r ↦ r.elim0, rfl, ?_⟩
  · obtain rfl : k = 0 := by simpa using Fintype.card_le_of_embedding e
    have he : ![a] ∘ e = ![a] := funext fun x ↦ by simp
    have hmap : univ.map e = {0} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_map.mpr ⟨0, mem_univ _, Subsingleton.elim _ _⟩, fun x _ ↦ Subsingleton.elim _ _⟩
    rw [he, hmap]
    simpa using hM.singletons a
  · have huniv : (univ : Finset (Fin 1)) = {0} := rfl
    rw [huniv]
    exact not_mem_hull_empty_of_isPlan (Geometry.IsPlan.singleton 0) 0

/-- **The sentence never uses the empty case**: the families of generators of (Convexity) are
indexed by `Option (Fin (n + 1))`, which is nonempty. -/
example (n : ℕ) : Nonempty (Option (Fin (n + 1))) :=
  ⟨none⟩

end VaughtConjecture

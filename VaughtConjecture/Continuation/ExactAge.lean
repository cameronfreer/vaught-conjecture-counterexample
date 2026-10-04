/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.CountableCorollary
import VaughtConjecture.Geometry.ConvexGeometry
import VaughtConjecture.Realization.Basic
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Hull
import VaughtConjecture.Realization.Model

/-!
# Exact receiving within an age, and the exact-age comparison

Roadmap, Layer 4 (terminal classification by exact ages: two countable exactly consistent
covering realizations with the same exact age and exact receiving are isomorphic, by
back-and-forth over literal roots, one point at a time along a chain of closed sets); semantic
contract, items 4, 8 and 12.  This file proves the form for expansions of base structures: the
isomorphism is one of the base structures, which is what the count of the successor losses needs;
an isomorphism of the realizations themselves is not proved here.  The chain of closed sets
enters through the passage from one-point to multi-point exact receiving, not in the
back-and-forth itself.

**Exact receiving within an age.**  Let `A m` be a set of stage types on `m` points, for every
`m`.  A realization `R` has **exact receiving within `A`** (`Realization.ExactReceivingWithin`)
when, over every cover `c` of a stage type `t` and for every `D ∈ A m` restricting to `t` along
an embedding `g` of coordinates, some cover `u` of `D` itself extends `c` along `g`
(`u ∘ g = c`).  The received type is the donor, with no cutoff: this is the exact form of
receiving, not finite-extension receiving at a permitted cutoff
(`Realization.HasFiniteExtensionReceiving`), whose received type only agrees with the donor below
the cutoff.  The donors may add several points at once.  When `R` is exactly consistent
(`Realization.IsConsistent`) and `A` is closed under the face maps, the one-point form (donors
on one more point, along the initial segment) gives the multi-point
form (`ExactReceivingWithin.of_one_point`): the image of `g` is a closed face of `D`, and the
closed faces form a convex geometry, so a chain of closed sets, each one point larger than the
last (`Geometry.IsConvexGeometry.exists_insert_mem`), leads from the image of `g` to all points
of `D`; each step is one-point receiving of a face of `D`, which lies in `A`.  Exact receiving is
invariant under transport along bijections of carriers (`exactReceivingWithin_map_iff`).

**The pointed form.**  For a **core** `x₀ : Fin k₀ → M`, the families are indexed also by the
position of the core: `A m ι` for `ι : Fin k₀ ↪ Fin m`.  Exact receiving within `A` at `x₀`
(`Realization.ExactReceivingWithinAt`) asks the same only over the covers `c` containing the core
at positions `ι` (`c ∘ ι = x₀`), for the donors in `A m (ι.trans g)`.  Exact receiving within
`A` gives exact receiving within `A` at every core
(`ExactReceivingWithin.exactReceivingWithinAt`).

**The comparison.**  Two tuples `a` of `M` and `b` of `N` are **matched through covers** at the
cores `x₀`, `y₀` (`Realization.CoverMatch`) when there are covers `x` in `R` and `y` in `R'` of
one common stage type, containing the cores at common positions, and a common selector `s` of
coordinates with `a = x ∘ s` and `b = y ∘ s`.  The selector need not be injective, so repeated
coordinates are matched, and the empty tuples are matched as soon as the cores cover a common
type.  For expansions `R` of `M` and `R'` of `N` (`Realization.IsExpansionOf`), matched tuples
have the same atomic type in the base language (`Realization.Covers.sameAtomicType`,
`SameAtomicType.relabel`).  If every actual type of a cover containing the core lies in the
pointed age (**age inclusion**) and `R'` has exact receiving within it at its core, a new point
`m` of `M` is matched (`CoverMatch.exists_snoc`): cover `x` followed by `m` by a typed tuple `u`
with this initial segment (`Realization.IsCovering.exists_castAdd`, as in the forth step of
condition 3 of the reduction of the main theorem to expansion domains, the comparison of two
models in one expansion domain, `Expansion.exists_extend_covers`); its type `D` is in the age
and restricts to the common type along the coordinates
of `x` (`Realization.Covers.eval_comp`), and exact receiving gives a cover of `D` in `R'`
extending `y`.  Symmetrically for a new point of `N`.  So the matched tuples form a
back-and-forth system, and InfinitaryLogic's countable back-and-forth construction
(`PotentialIso.ofExtensionFamily` and `PotentialIso.countable_toEquiv_graph`, the form of
`countable_extensionFamily_implies_iso` that records where each point is sent) gives an
isomorphism of the base structures of countable carriers, which carries the core `x₀` to `y₀`
because every matched pair does
(`exists_equiv_comp_eq_of_exactReceivingWithinAt`).  The unpointed form
(`exists_equiv_comp_eq_of_exactReceivingWithin`, `nonempty_equiv_of_exactReceivingWithin`) starts
from any two covers of one common type.

Age inclusion is needed: exact receiving within a family missing the actual types is no
constraint at all (the empty family, `VaughtConjecture.Continuation.ExactAgeExamples`).  A root
whose type lies outside a face-closed family has no coface in it, so the forth step has no donor.

**Chart homogeneity.**  For `M = N` the comparison gives an automorphism of the base structure
carrying any cover of a stage type to any other cover of the same type
(`exists_automorphism_comp_eq_of_exactReceivingWithin`).  Chart homogeneity is thus derived from
exact receiving and age inclusion, not assumed; it is a by-product, not an input of the
comparison.

Everything here is unconditional.  The comparisons that use it, for the rigid-core, residual,
and hollow terminal models, and the countability of the successor losses that follows from them
are still to be proved; so are the exact receiving statements they need ((R1), (R2), (R3) of the
table of Layer 3).  Nothing here concerns the uniqueness or coherence of expansions, and no
characteristic arity is used.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset FirstOrder Language Structure

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {N : Type w} {k₀ : ℕ}

/-! ### Exact receiving within an age -/

section Receiving

variable (R : Realization.{u, v} α M)

/-- **Exact receiving within `A`**: over every cover `c` of a stage type `t`, every donor `D ∈ A m`
restricting to `t` along an embedding `g` of coordinates is the type of a cover `u` with
`u ∘ g = c`. -/
def ExactReceivingWithin (A : ∀ m, Set (StageType.{u} α m)) : Prop :=
  ∀ ⦃n m : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
    ∀ (D : StageType.{u} α m) (g : Fin n ↪ Fin m), D ∈ A m →
      StageType.restrictFace g D = some t → ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c

/-- **Exact receiving within a pointed age at a core** `x₀`: exact receiving over the covers
containing the core at positions `ι`, for the donors in `A m (ι.trans g)`. -/
def ExactReceivingWithinAt (x₀ : Fin k₀ → M) (A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)) :
    Prop :=
  ∀ ⦃n m : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M) (ι : Fin k₀ ↪ Fin n), R.Covers t c →
    c ∘ ι = x₀ → ∀ (D : StageType.{u} α m) (g : Fin n ↪ Fin m), D ∈ A m (ι.trans g) →
      StageType.restrictFace g D = some t → ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c

variable {R} {A : ∀ m, Set (StageType.{u} α m)}

/-- Exact receiving within an age gives exact receiving within it at every core. -/
theorem ExactReceivingWithin.exactReceivingWithinAt (h : R.ExactReceivingWithin A)
    (x₀ : Fin k₀ → M) : R.ExactReceivingWithinAt x₀ fun m _ ↦ A m :=
  fun _ _ t c _ hc _ D g hD hg ↦ h t c hc D g hD hg

/-- A cover of a stage type `t` along a bijection `e` of coordinates covers the type that `t`
reindexes. -/
private theorem covers_comp_symm (hR : R.IsConsistent) {n : ℕ} {D t : StageType.{u} α n}
    {c : Fin n → M} (hc : R.Covers t c) (e : Fin n ≃ Fin n) (ht : D.reindex e = t) :
    R.Covers D (c ∘ e.symm) := by
  subst ht
  refine ⟨hc.injective.comp e.symm.injective, ?_⟩
  have h := eval_equiv_trans_of_eval hR hc.eval_eq e.symm
  rw [StageType.reindex_reindex, Equiv.symm_trans_self, StageType.reindex_refl] at h
  exact h

/-- The image of `Fin.snoc g x` is the image of `g` with `x` added. -/
private theorem map_univ_snoc {n m : ℕ} (g : Fin n ↪ Fin m) (x : Fin m)
    (h : Function.Injective (Fin.snoc (α := fun _ ↦ Fin m) g x)) :
    univ.map ⟨_, h⟩ = insert x (univ.map g) := by
  ext y
  simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_insert,
    Fin.exists_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]
  tauto

/-- One-point exact receiving along a chain of closed sets: by induction on the number of points
of the donor outside the image of `g`. -/
private theorem exists_covers_of_one_point (hR : R.IsConsistent)
    (hA : ∀ ⦃m k : ℕ⦄ (D : StageType.{u} α m) (f : Fin k ↪ Fin m) (p : StageType.{u} α k),
      D ∈ A m → StageType.restrictFace f D = some p → p ∈ A k)
    (h1 : ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
      ∀ D ∈ A (n + 1), StageType.restrictFace Fin.castSuccEmb D = some t →
        ∃ u : Fin (n + 1) → M, R.Covers D u ∧ u ∘ Fin.castSucc = c) {m : ℕ}
    (D : StageType.{u} α m) (hD : D ∈ A m) :
    ∀ (k n : ℕ), n + k = m → ∀ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
      ∀ g : Fin n ↪ Fin m, StageType.restrictFace g D = some t →
        ∃ u : Fin m → M, R.Covers D u ∧ u ∘ g = c := by
  intro k
  induction k with
  | zero =>
    intro n hn t c hc g hg
    subst hn
    -- `g` is a bijection; `t` is `D` reindexed along it
    have hb : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨g.injective, rfl⟩
    let e : Fin (n + 0) ≃ Fin (n + 0) := Equiv.ofBijective g hb
    have hge : g = e.toEmbedding := by ext; rfl
    rw [hge, StageType.restrictFace_equiv, Option.some_inj] at hg
    refine ⟨c ∘ e.symm, covers_comp_symm hR hc e hg, funext fun i ↦ ?_⟩
    simp [hge]
  | succ k ih =>
    intro n hn t c hc g hg
    obtain ⟨hgf, -⟩ := (StageType.restrictFace_eq_some_iff D g).mp hg
    have hlt : univ.map g ⊂ univ := by
      refine ssubset_univ_iff.mpr fun he ↦ ?_
      have := card_map (s := (univ : Finset (Fin n))) g
      rw [he, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at this
      omega
    obtain ⟨x, -, hx, hxf⟩ := D.isPlan.isConvexGeometry.exists_insert_mem hgf D.univ_mem_faces hlt
    have hxg : x ∉ Set.range g := fun ⟨i, hi⟩ ↦ hx (hi ▸ mem_map_of_mem g (mem_univ i))
    have hinj : Function.Injective (Fin.snoc (α := fun _ ↦ Fin m) g x) :=
      Fin.snoc_injective_of_injective g.injective hxg
    let g' : Fin (n + 1) ↪ Fin m := ⟨_, hinj⟩
    have hg'f : univ.map g' ∈ D.toCellScheme.faces := by rwa [map_univ_snoc g x hinj]
    have hcg : Fin.castSuccEmb.trans g' = g := by ext i; simp [g']
    have hD' : StageType.restrictFace Fin.castSuccEmb (D.comap g' hg'f) = some t := by
      rw [StageType.restrictFace_trans D g' _ (StageType.restrictFace_of_mem D g' hg'f), hcg, hg]
    obtain ⟨c', hc', hc'c⟩ :=
      h1 t c hc _ (hA D g' _ hD (StageType.restrictFace_of_mem D g' hg'f)) hD'
    obtain ⟨u, hu, hug⟩ := ih (n + 1) (by omega) _ c' hc' g'
      (StageType.restrictFace_of_mem D g' hg'f)
    refine ⟨u, hu, ?_⟩
    rw [← hcg, ← hc'c, ← hug]
    rfl

/-- **One-point exact receiving gives exact receiving** within a family closed under the face
maps.  The image of `g` is a closed face of the donor `D`; a chain of closed faces, each one point
larger than the last (`Geometry.IsConvexGeometry.exists_insert_mem`), leads to all points of `D`,
and each step receives the face of `D` on one more point, which lies in `A`.  At the end the
embedding is a bijection and the cover is reindexed (`Realization.eval_equiv_trans_of_eval`,
which uses exact consistency).  Closure under reindexing is not needed. -/
theorem ExactReceivingWithin.of_one_point (hR : R.IsConsistent)
    (hA : ∀ ⦃m k : ℕ⦄ (D : StageType.{u} α m) (f : Fin k ↪ Fin m) (p : StageType.{u} α k),
      D ∈ A m → StageType.restrictFace f D = some p → p ∈ A k)
    (h1 : ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
      ∀ D ∈ A (n + 1), StageType.restrictFace Fin.castSuccEmb D = some t →
        ∃ u : Fin (n + 1) → M, R.Covers D u ∧ u ∘ Fin.castSucc = c) :
    R.ExactReceivingWithin A := by
  intro n m t c hc D g hD hg
  have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
  exact exists_covers_of_one_point hR hA h1 D hD (m - n) n (by omega) t c hc g hg

/-! ### Transport -/

/-- Covers in a transport are the transports of covers. -/
theorem covers_map_iff (e : M ≃ N) {n : ℕ} {t : StageType.{u} α n} {c : Fin n → N} :
    (R.map e).Covers t c ↔ R.Covers t (e.symm ∘ c) := by
  refine ⟨fun ⟨hc, h⟩ ↦ ⟨e.symm.injective.comp hc, h⟩, fun ⟨hc, h⟩ ↦ ⟨?_, h⟩⟩
  exact (Function.Injective.of_comp (f := e.symm) hc)

/-- **Transport of exact receiving** along a bijection of carriers. -/
theorem ExactReceivingWithin.map (h : R.ExactReceivingWithin A) (e : M ≃ N) :
    (R.map e).ExactReceivingWithin A := by
  intro n m t c hc D g hD hg
  obtain ⟨u, hu, hug⟩ := h t _ ((covers_map_iff e).mp hc) D g hD hg
  refine ⟨e ∘ u, (covers_map_iff e).mpr ?_, ?_⟩
  · simpa [Function.comp_def] using hu
  · rw [Function.comp_assoc, hug, ← Function.comp_assoc, e.self_comp_symm, Function.id_comp]

/-- **Exact receiving is invariant under transport.** -/
@[simp] theorem exactReceivingWithin_map_iff (e : M ≃ N) :
    (R.map e).ExactReceivingWithin A ↔ R.ExactReceivingWithin A :=
  ⟨fun h ↦ map_symm_map R e ▸ h.map e.symm, fun h ↦ h.map e⟩

end Receiving

/-! ### Tuples matched through covers -/

section Match

variable (R : Realization.{u, v} α M) (R' : Realization.{u, w} α N)

/-- Tuples `a` of `M` and `b` of `N` are **matched through covers** at the cores `x₀` and `y₀`:
some covers `x` in `R` and `y` in `R'` of one common stage type contain the cores at common
positions `ι`, and a common selector `s` of coordinates gives `a = x ∘ s` and `b = y ∘ s`. -/
def CoverMatch (x₀ : Fin k₀ → M) (y₀ : Fin k₀ → N) (n : ℕ) (a : Fin n → M) (b : Fin n → N) :
    Prop :=
  ∃ (k : ℕ) (t : StageType.{u} α k) (x : Fin k → M) (y : Fin k → N) (ι : Fin k₀ ↪ Fin k)
    (s : Fin n → Fin k), R.Covers t x ∧ R'.Covers t y ∧ x ∘ ι = x₀ ∧ y ∘ ι = y₀ ∧ a = x ∘ s ∧
      b = y ∘ s

variable {R R'} {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N}

/-- The cores are matched, and with them the empty tuples, once they cover a common type. -/
theorem CoverMatch.zero {p : StageType.{u} α k₀} (h₀ : R.Covers p x₀) (h₀' : R'.Covers p y₀) :
    CoverMatch R R' x₀ y₀ 0 Fin.elim0 Fin.elim0 :=
  ⟨k₀, p, x₀, y₀, Function.Embedding.refl _, Fin.elim0, h₀, h₀', rfl, rfl,
    funext fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩

/-- Matching is symmetric. -/
theorem CoverMatch.symm {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : CoverMatch R R' x₀ y₀ n a b) : CoverMatch R' R y₀ x₀ n b a := by
  obtain ⟨k, t, x, y, ι, s, hx, hy, hxι, hyι, ha, hb⟩ := h
  exact ⟨k, t, y, x, ι, s, hy, hx, hyι, hxι, hb, ha⟩

/-- **Matched tuples have the same atomic type** in the base language, for expansions at a
common stage (`Realization.Covers.sameAtomicType`). -/
theorem CoverMatch.sameAtomicType [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : CoverMatch R R' x₀ y₀ n a b) : SameAtomicType (L := baseLanguage.{u}) a b := by
  obtain ⟨k, t, x, y, ι, s, hx, hy, -, -, rfl, rfl⟩ := h
  exact (Covers.sameAtomicType he he' hx hy).relabel s

/-- **Forth**: under exact consistency and covering of `R`, age inclusion for `R` and exact
receiving within the pointed age for `R'`, a matched pair extends by any point of `M`.  A point
among the coordinates of the cover is matched by the selector; any other is covered with the
cover by a typed tuple of `R`, whose type is received exactly in `R'`. -/
theorem CoverMatch.exists_snoc (hR : R.IsConsistent) (hc : R.IsCovering)
    {A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)}
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R.eval s = some D → ⇑s ∘ ι = x₀ → D ∈ A m ι)
    (hr' : R'.ExactReceivingWithinAt y₀ A) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : CoverMatch R R' x₀ y₀ n a b) (m : M) :
    ∃ m' : N, CoverMatch R R' x₀ y₀ (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  obtain ⟨k, t, x, y, ι, s, hx, hy, hxι, hyι, rfl, rfl⟩ := h
  by_cases hm : m ∈ Set.range x
  · obtain ⟨i, rfl⟩ := hm
    exact ⟨y i, k, t, x, y, ι, Fin.snoc s i, hx, hy, hxι, hyι, (Fin.comp_snoc x s i).symm,
      (Fin.comp_snoc y s i).symm⟩
  have hinj : Function.Injective (Fin.snoc x m : Fin (k + 1) → M) :=
    Fin.snoc_injective_of_injective hx.injective hm
  obtain ⟨k₂, u, hu, hsome⟩ := hc.exists_castAdd hR ⟨Fin.snoc x m, hinj⟩
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp hsome
  have hu' (i : Fin (k + 1)) : u (Fin.castAdd k₂ i) = (Fin.snoc x m : Fin (k + 1) → M) i :=
    DFunLike.congr_fun hu i
  -- the face of the coordinates of `x`
  let g : Fin k ↪ Fin (k + 1 + k₂) := Fin.castSuccEmb.trans (Fin.castAddEmb k₂)
  have hgu : ⇑u ∘ ⇑g = x := funext fun i ↦ by simpa [g] using hu' i.castSucc
  have hgD : StageType.restrictFace g D = some t := by
    rw [← hR u D g hD, ← hx.eval_eq]
    congr 1
    ext i
    exact congrFun hgu i
  have hDA : D ∈ A _ (ι.trans g) := hage u (ι.trans g) D hD (by
    rw [Function.Embedding.coe_trans, ← Function.comp_assoc, hgu, hxι])
  obtain ⟨u', hu'D, hgu'⟩ := hr' t y ι hy hyι D g hDA hgD
  refine ⟨u' (Fin.castAdd k₂ (Fin.last k)), k + 1 + k₂, D, u, u', ι.trans g,
    Fin.snoc (g ∘ s) (Fin.castAdd k₂ (Fin.last k)), covers_of_eval u hD, hu'D, ?_, ?_, ?_, ?_⟩
  · rw [Function.Embedding.coe_trans, ← Function.comp_assoc, hgu, hxι]
  · rw [Function.Embedding.coe_trans, ← Function.comp_assoc, hgu', hyι]
  · rw [Fin.comp_snoc, ← Function.comp_assoc, hgu]
    simpa using (hu' (Fin.last k)).symm
  · rw [Fin.comp_snoc, ← Function.comp_assoc, hgu']

end Match

/-! ### The exact-age comparison -/

section Comparison

variable {M N : Type w} [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
  [Countable M] [Countable N] {R : Realization.{u, w} α M} {R' : Realization.{u, w} α N}

/-- **The pointed exact-age comparison.**  Let `R` and `R'` be expansions of countable base
structures `M` and `N` at a common stage, with cores `x₀` and `y₀` covering a common stage type.
If every actual type of a cover containing the core at positions `ι` lies in `A m ι`, in both
(age inclusion), and both have exact receiving within `A` at their cores, then some isomorphism of
the base structures carries `x₀` to `y₀`.  The matched tuples (`Realization.CoverMatch`) form a
back-and-forth system; the isomorphism is InfinitaryLogic's countable back-and-forth
construction, and it carries the core to the core because every matched pair does. -/
theorem exists_equiv_comp_eq_of_exactReceivingWithinAt {p : StageType.{u} α k₀}
    {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N} {A : ∀ m, (Fin k₀ ↪ Fin m) → Set (StageType.{u} α m)}
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R.eval s = some D → ⇑s ∘ ι = x₀ → D ∈ A m ι)
    (hage' : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (ι : Fin k₀ ↪ Fin m) (D : StageType.{u} α m),
      R'.eval s = some D → ⇑s ∘ ι = y₀ → D ∈ A m ι)
    (hr : R.ExactReceivingWithinAt x₀ A) (hr' : R'.ExactReceivingWithinAt y₀ A)
    (h₀ : R.Covers p x₀) (h₀' : R'.Covers p y₀) :
    ∃ e : M ≃[baseLanguage.{u}] N, ⇑e ∘ x₀ = y₀ := by
  let P : PotentialIso baseLanguage.{u} M N :=
    PotentialIso.ofExtensionFamily (CoverMatch R R' x₀ y₀) (CoverMatch.zero h₀ h₀')
      (fun h ↦ h.sameAtomicType he he')
      (fun h m ↦ h.exists_snoc he.isModel.isConsistent he.isModel.isCovering hage hr' m)
      (fun h m' ↦ (h.symm.exists_snoc he'.isModel.isConsistent he'.isModel.isCovering hage' hr
        m').imp fun _ h' ↦ h'.symm)
  obtain ⟨e, hgraph⟩ := P.countable_toEquiv_graph
  refine ⟨e, funext fun j ↦ ?_⟩
  obtain ⟨⟨n, a, b⟩, hp, i, hai, hbi⟩ := hgraph (x₀ j)
  obtain ⟨k, t, x, y, ι, s, hx, hy, hxι, hyι, ha, hb⟩ := hp
  simp only at hai hbi ha hb
  have hsi : s i = ι j :=
    hx.injective ((congrFun ha i).symm.trans (hai.trans (congrFun hxι j).symm))
  rw [Function.comp_apply, ← hbi, congrFun hb i, ← congrFun hyι j]
  exact congrArg y hsi

/-- **The exact-age comparison, rooted.**  Two expansions of countable base structures at a
common stage, whose actual types all lie in `A`, with exact receiving within `A`, and with covers
`x₀` and `y₀` of one common stage type, have an isomorphism of their base structures carrying
`x₀` to `y₀`.  The initial match may be the covers of the stage type on no points. -/
theorem exists_equiv_comp_eq_of_exactReceivingWithin {t : StageType.{u} α k₀}
    {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N} {A : ∀ m, Set (StageType.{u} α m)}
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m)
    (hage' : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (D : StageType.{u} α m), R'.eval s = some D → D ∈ A m)
    (hr : R.ExactReceivingWithin A) (hr' : R'.ExactReceivingWithin A)
    (h₀ : R.Covers t x₀) (h₀' : R'.Covers t y₀) :
    ∃ e : M ≃[baseLanguage.{u}] N, ⇑e ∘ x₀ = y₀ :=
  exists_equiv_comp_eq_of_exactReceivingWithinAt (A := fun m _ ↦ A m) he he'
    (fun _ s _ D hD _ ↦ hage s D hD) (fun _ s _ D hD _ ↦ hage' s D hD)
    (hr.exactReceivingWithinAt x₀) (hr'.exactReceivingWithinAt y₀) h₀ h₀'

/-- **The exact-age comparison.**  Two expansions of countable base structures at a common
stage, whose actual types all lie in `A` and which have exact receiving within `A`, and which have
covers of one common stage type, have isomorphic base structures. -/
theorem nonempty_equiv_of_exactReceivingWithin {t : StageType.{u} α k₀}
    {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N} {A : ∀ m, Set (StageType.{u} α m)}
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m)
    (hage' : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ N) (D : StageType.{u} α m), R'.eval s = some D → D ∈ A m)
    (hr : R.ExactReceivingWithin A) (hr' : R'.ExactReceivingWithin A)
    (h₀ : R.Covers t x₀) (h₀' : R'.Covers t y₀) : Nonempty (M ≃[baseLanguage.{u}] N) :=
  let ⟨e, _⟩ := exists_equiv_comp_eq_of_exactReceivingWithin he he' hage hage' hr hr' h₀ h₀'
  ⟨e⟩

/-- **Chart homogeneity from exact receiving.**  In an expansion of a countable base structure
whose actual types all lie in `A` and which has exact receiving within `A`, any two covers of one
stage type are carried to each other by an automorphism of the base structure.  This derives
chart homogeneity, in the base language, from exact receiving and age inclusion; it is a
by-product of the comparison, not an input. -/
theorem exists_automorphism_comp_eq_of_exactReceivingWithin {t : StageType.{u} α k₀}
    {x₀ y₀ : Fin k₀ → M} {A : ∀ m, Set (StageType.{u} α m)} (he : R.IsExpansionOf)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m)
    (hr : R.ExactReceivingWithin A) (h₀ : R.Covers t x₀) (h₀' : R.Covers t y₀) :
    ∃ e : M ≃[baseLanguage.{u}] M, ⇑e ∘ x₀ = y₀ :=
  exists_equiv_comp_eq_of_exactReceivingWithin he he hage hage hr hr h₀ h₀'

end Comparison

end Realization

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Base

/-!
# Projections of structures: composition, the reduct, transport

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  General
lemmas about the projection `τ_β(G)` of [AFK26, Definition 2.7] (`InvariantSystem.projection`)
and the base sublanguage, for an arbitrary geometry signature and invariant system:

* `GeometrySignature.structure_ext`: structures of a relational language are equal when they have
  the same relations;
* `BaseSublanguage.countableRelationsTarget`: `L_c` is countable [AFK26, Convention 2.3];
* `InvariantSystem.relMap_projection_of_not_isInvariant`,
  `InvariantSystem.relMap_projection_of_isInvariant`: the two clauses of Definition 2.7;
* `InvariantSystem.projection_projection_of_le`, `InvariantSystem.projection_projection_of_ge`:
  for `α ≤ β`, `τ_α ∘ τ_β = τ_β ∘ τ_α = τ_α` on structures, from `InvariantSystem.comp`;
* `BaseSublanguage.reduct_projection`: a projection has the same reduct to `L_c`;
* transport along a bijection (`Equiv.inducedStructure`) commutes with projection and reduct
  (`InvariantSystem.projection_inducedStructure`, `BaseSublanguage.reduct_inducedStructure`), and
  an isomorphism is an isomorphism of the projections and of the reducts
  (`InvariantSystem.projectionEquiv`, `BaseSublanguage.reductEquiv`).
-/

universe w w' wc wc' v v'

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

/-- **Structures of a relational language are equal when they have the same relations.**
Correspondence with the printed definitions. -/
theorem GeometrySignature.structure_ext (σ : GeometrySignature L) {M : Type v}
    {G G' : L.Structure M}
    (h : ∀ ⦃n : ℕ⦄ (R : L.Relations n) (x : Fin n → M),
      RelMap (L := L) (self := G) R x ↔ RelMap (L := L) (self := G') R x) : G = G' :=
  Structure.ext (funext fun n ↦ funext fun f ↦ (σ.isEmpty_functions n).elim f)
    (funext fun _ ↦ funext fun R ↦ funext fun x ↦ propext (h R x))

namespace GeometrySignature.BaseSublanguage

variable {Lc : Language.{wc, wc'}}

/-- **`L_c` is countable** (`CountableRelationsTarget`, [AFK26, Convention 2.3]): in each arity
the inclusion maps the symbols of `L_c` injectively into the symbols of `L` that are not
invariants, a countable set (`GeometrySignature.countable_setOf_not_isInvariant`).
Correspondence with the printed definitions. -/
theorem countableRelationsTarget (E : σ.BaseSublanguage Lc) :
    CountableRelationsTarget (Lc := Lc) := by
  have h (n : ℕ) : Countable (Lc.Relations n) := by
    have := (σ.countable_setOf_not_isInvariant n).to_subtype
    exact Function.Injective.countable
      (f := fun r : Lc.Relations n ↦ (⟨E.incl.onRelation r, (E.mem_range_iff _).mp ⟨r, rfl⟩⟩ :
        {R : L.Relations n | ¬ σ.IsInvariant R}))
      fun a b hab ↦ E.incl_injective.onRelation (congrArg Subtype.val hab)
  exact (inferInstance : Countable (Σ n, Lc.Relations n))

/-- The image of a symbol of `L_c` is not an invariant.  Correspondence with the printed
definitions. -/
theorem not_isInvariant_incl (E : σ.BaseSublanguage Lc) {n : ℕ} (r : Lc.Relations n) :
    ¬ σ.IsInvariant (E.incl.onRelation r) :=
  (E.mem_range_iff _).mp ⟨r, rfl⟩

/-- **Structures of `L_c` are equal when they have the same relations.**  Correspondence with
the printed definitions. -/
theorem structure_ext (E : σ.BaseSublanguage Lc) {M : Type v} {B B' : Lc.Structure M}
    (h : ∀ ⦃n : ℕ⦄ (r : Lc.Relations n) (x : Fin n → M),
      RelMap (L := Lc) (self := B) r x ↔ RelMap (L := Lc) (self := B') r x) : B = B' :=
  Structure.ext (funext fun n ↦ funext fun f ↦ (E.isRelational n).elim f)
    (funext fun _ ↦ funext fun r ↦ funext fun x ↦ propext (h r x))

end GeometrySignature.BaseSublanguage

namespace InvariantSystem

variable (S : InvariantSystem.{0} σ)

/-- **The second clause of [AFK26, Definition 2.7]**: a symbol that is not an invariant holds in
`τ_β(G)` exactly as in `G`.  Correspondence with the printed definitions. -/
theorem relMap_projection_of_not_isInvariant (β : SystemLevel) {M : Type v} (G : L.Structure M)
    {n : ℕ} {R : L.Relations n} (hR : ¬ σ.IsInvariant R) (x : Fin n → M) :
    RelMap (L := L) (self := S.projection β G) R x ↔ RelMap (L := L) (self := G) R x :=
  ⟨fun h ↦ h.2 hR, fun h ↦ ⟨fun h' ↦ (hR h').elim, fun _ ↦ h⟩⟩

/-- **The third clause of [AFK26, Definition 2.7]**: an invariant `R` holds of `x` in `τ_β(G)`
exactly when some invariant `Q` with `τ_β(Q) = R` holds of `x` in `G`.  Correspondence with the
printed definitions. -/
theorem relMap_projection_of_isInvariant (β : SystemLevel) {M : Type v} (G : L.Structure M)
    {n : ℕ} {R : L.Relations n} (hR : σ.IsInvariant R) (x : Fin n → M) :
    RelMap (L := L) (self := S.projection β G) R x ↔
      ∃ Q : σ.Invariant n, (S.τ β Q).1 = R ∧ RelMap (L := L) (self := G) Q.1 x :=
  ⟨fun h ↦ h.1 hR, fun h ↦ ⟨fun _ ↦ h, fun h' ↦ (h' hR).elim⟩⟩

/-- **`τ_α ∘ τ_β = τ_α` on structures**, for `α ≤ β` ([AFK26, Definition 2.6 (c)] lifted to
structures by Definition 2.7).  Correspondence with the printed definitions. -/
theorem projection_projection_of_le {α β : SystemLevel} (hαβ : α ≤ β) {M : Type v}
    (G : L.Structure M) : S.projection α (S.projection β G) = S.projection α G := by
  refine σ.structure_ext fun n R x ↦ ?_
  by_cases hR : σ.IsInvariant R
  · rw [S.relMap_projection_of_isInvariant α _ hR, S.relMap_projection_of_isInvariant α _ hR]
    constructor
    · rintro ⟨Q, rfl, hQ⟩
      obtain ⟨Q', hQ', hx⟩ := (S.relMap_projection_of_isInvariant β G Q.2 x).mp hQ
      obtain rfl : S.τ β Q' = Q := Subtype.ext hQ'
      exact ⟨Q', by rw [(S.comp hαβ Q').1], hx⟩
    · rintro ⟨Q', rfl, hx⟩
      exact ⟨S.τ β Q', by rw [(S.comp hαβ Q').1],
        (S.relMap_projection_of_isInvariant β G (S.τ β Q').2 x).mpr ⟨Q', rfl, hx⟩⟩
  · rw [S.relMap_projection_of_not_isInvariant α _ hR,
      S.relMap_projection_of_not_isInvariant α _ hR, S.relMap_projection_of_not_isInvariant β _ hR]

/-- **`τ_β ∘ τ_α = τ_α` on structures**, for `α ≤ β` ([AFK26, Definition 2.6 (c)] lifted to
structures by Definition 2.7).  Correspondence with the printed definitions. -/
theorem projection_projection_of_ge {α β : SystemLevel} (hαβ : α ≤ β) {M : Type v}
    (G : L.Structure M) : S.projection β (S.projection α G) = S.projection α G := by
  refine σ.structure_ext fun n R x ↦ ?_
  by_cases hR : σ.IsInvariant R
  · rw [S.relMap_projection_of_isInvariant β _ hR, S.relMap_projection_of_isInvariant α _ hR]
    constructor
    · rintro ⟨Q, rfl, hQ⟩
      obtain ⟨Q', hQ', hx⟩ := (S.relMap_projection_of_isInvariant α G Q.2 x).mp hQ
      obtain rfl : S.τ α Q' = Q := Subtype.ext hQ'
      exact ⟨Q', by rw [(S.comp hαβ Q').2], hx⟩
    · rintro ⟨Q', rfl, hx⟩
      exact ⟨S.τ α Q', by rw [(S.comp hαβ Q').2],
        (S.relMap_projection_of_isInvariant α G (S.τ α Q').2 x).mpr ⟨Q', rfl, hx⟩⟩
  · exact S.relMap_projection_of_not_isInvariant β (S.projection α G) hR x

/-- **Transport commutes with projection**: projecting the structure induced along a bijection
`e : M ≃ N` is inducing the projection along `e`.  Correspondence with the printed definitions. -/
theorem projection_inducedStructure (β : SystemLevel) {M : Type v} {N : Type v'}
    (G : L.Structure M) (e : M ≃ N) :
    S.projection β (@Equiv.inducedStructure L M N G e) =
      @Equiv.inducedStructure L M N (S.projection β G) e :=
  σ.structure_ext fun _ _ _ ↦ Iff.rfl

/-- **An isomorphism is an isomorphism of the projections**, by the same bijection.
Correspondence with the printed definitions. -/
def projectionEquiv (β : SystemLevel) {M : Type v} {N : Type v'} {G : L.Structure M}
    {H : L.Structure N} (g : @Language.Equiv L M N G H) :
    @Language.Equiv L M N (S.projection β G) (S.projection β H) :=
  @Language.Equiv.mk L M N (S.projection β G) (S.projection β H)
    (@Language.Equiv.toEquiv L M N G H g) (fun {n} f ↦ (σ.isEmpty_functions n).elim f)
    (fun {n} R x ↦ by
      by_cases hR : σ.IsInvariant R
      · rw [S.relMap_projection_of_isInvariant β H hR, S.relMap_projection_of_isInvariant β G hR]
        exact exists_congr fun Q ↦ and_congr_right fun _ ↦
          @Language.Equiv.map_rel' L M N G H g n Q.1 x
      · rw [S.relMap_projection_of_not_isInvariant β H hR,
          S.relMap_projection_of_not_isInvariant β G hR]
        exact @Language.Equiv.map_rel' L M N G H g n R x)

end InvariantSystem

namespace GeometrySignature.BaseSublanguage

variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **A projection has the same reduct to `L_c`** ([AFK26, Definition 2.7]: `L_c` is unchanged):
`τ_β(G)↾L_c = G↾L_c`.  Correspondence with the printed definitions. -/
theorem reduct_projection (S : InvariantSystem.{0} σ) (β : SystemLevel) {M : Type v}
    (G : L.Structure M) : E.reduct (S.projection β G) = E.reduct G :=
  E.structure_ext fun _ r x ↦
    S.relMap_projection_of_not_isInvariant β G (E.not_isInvariant_incl r) x

/-- **Transport commutes with the reduct**.  Correspondence with the printed definitions. -/
theorem reduct_inducedStructure {M : Type v} {N : Type v'} (G : L.Structure M) (e : M ≃ N) :
    E.reduct (@Equiv.inducedStructure L M N G e) =
      @Equiv.inducedStructure Lc M N (E.reduct G) e :=
  E.structure_ext fun _ _ _ ↦ Iff.rfl

/-- **An isomorphism restricts to an isomorphism of the reducts**, by the same bijection.
Correspondence with the printed definitions. -/
def reductEquiv {M : Type v} {N : Type v'} {G : L.Structure M} {H : L.Structure N}
    (g : @Language.Equiv L M N G H) : @Language.Equiv Lc M N (E.reduct G) (E.reduct H) :=
  @Language.Equiv.mk Lc M N (E.reduct G) (E.reduct H)
    (@Language.Equiv.toEquiv L M N G H g) (fun {n} f ↦ (E.isRelational n).elim f)
    (fun {n} r x ↦ @Language.Equiv.map_rel' L M N G H g n (E.incl.onRelation r) x)

end GeometrySignature.BaseSublanguage

end VaughtConjecture.Correspondence

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.BackAndForth

/-!
# [AFK26, Theorem 2.19] for an arbitrary weak system

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a weak
system `W` (`WeakSystem D S`) and a base sublanguage `E`:

**Occurrence of a fixed invariant**:

* `WeakSystem.exists_relMap_fixed_invariant`: every member `G ∈ K_β` holds an invariant `Q` with
  `τ_β(Q) = Q` of some tuple.  A point of the (nonempty, `WeakSystem.nonempty`) carrier, the
  closure clause of the geometry on the one-point tuple (`IsGeometry.exists_closed`), an invariant
  of the closed tuple (`IsStructuredGeometry.closed_iff`), and `τ_β(G) = G` (`WeakSystem.fixed`):
  the invariant holds in `τ_β(G)`, so it is `τ_β(Q')` for some `Q'`, and `τ_β ∘ τ_β = τ_β`
  (`InvariantSystem.comp`).

**Lifts and base isomorphism**:

* `BaseSublanguage.eq_inducedStructure_of_equiv`: the target of an isomorphism of
  `L_c`-structures is the structure induced along its bijection;
* `WeakSystem.exists_isLiftAt_of_equiv`, `WeakSystem.exists_isLiftAt_iff_of_equiv`: on countable
  carriers, having a lift at `β` is invariant under isomorphism of `L_c`-structures.  A lift `G` of
  `B` is carried along the bijection of `g : B ≅ B'` (`WeakSystem.isoClosed`), and its reduct is
  the structure induced from `B`, which is `B'` (`BaseSublanguage.reduct_inducedStructure`);
* the partition of the coded classes: for a class `q` of `isoSetoid φ`, every member lacks a lift
  at `β` exactly when some member does (`WeakSystem.mem_classesWithoutLift_iff`), and otherwise
  every member, equivalently some member, has one (`WeakSystem.not_mem_classesWithoutLift_iff`,
  `WeakSystem.not_mem_classesWithoutLift_iff_exists`); so either `q ∈ classesWithoutLift E φ β`
  or every member of `q` has a lift at `β` on `ℕ` (`WeakSystem.mem_classesWithoutLift_or`).

**Theorem 2.19, its back-and-forth content** (`WeakSystem.countableBFClassesTarget`,
`WeakSystem.CountableBFClassesTarget`): for `η < ω₁`, take the level `β = η`.  A class `x` of
`bfEquivSetoid φ η` whose chosen code has a lift `G` at `β` on `ℕ`: `G` holds a `β`-invariant
(`exists_relMap_fixed_invariant`), a member of the countable set of the field
`InvariantSystem.countable`, and two such classes holding one invariant are equal by
[AFK26, Proposition 2.18] (`bfEquivOfCommonInvariantTarget`, through
`WeakSystem.bfEquivSetoid_r_of_isLiftAt`): a common invariant gives back-and-forth equivalence at
`β = η`, not isomorphism.  A class whose chosen code has no lift at `β` is the image of a class of
`classesWithoutLift E φ β` (countable by hypothesis) under the passage from isomorphism to
back-and-forth equivalence (`isoSetoid_refines_bfEquivSetoid`).  The hypothesis that `φ`
axiomatizes the base is not used.
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} (W : WeakSystem.{w, w', v} D S)

/-! ### Occurrence of a fixed invariant -/

/-- **Every member of `K_β` holds a `β`-invariant of some tuple**: for `G ∈ K_β` there are an
invariant `Q` with `τ_β(Q) = Q` (a member of the countable set of the field
`InvariantSystem.countable`) and a tuple `a` with `G ⊨ Q(a)`.  A point `p` of the carrier
(`nonempty`); the one-point tuple at `p` extends to a tuple `z` with `P_{1+l}`
(`IsGeometry.exists_closed`), which carries an invariant `P` (`IsStructuredGeometry.closed_iff`);
as `τ_β(G) = G` (`fixed`), `P = τ_β(Q')` for an invariant `Q'` of `G`, and
`τ_β(τ_β(Q')) = τ_β(Q')` (`InvariantSystem.comp`).  Correspondence with the printed
definitions. -/
theorem exists_relMap_fixed_invariant {β : SystemLevel} {M : Type v} {G : L.Structure M}
    (hG : G ∈ W.K β M) :
    ∃ Q : Σ n, σ.Invariant n, S.τ β Q.2 = Q.2 ∧
      ∃ a : Fin Q.1 → M, RelMap (L := L) (self := G) Q.2.1 a := by
  obtain ⟨p⟩ := W.nonempty hG
  have hsG : @IsStructuredGeometry L σ M G := (W.isCompatible hG).1
  obtain ⟨l, z, -, hz⟩ := hsG.isGeometry.exists_closed one_pos (fun _ : Fin 1 ↦ p)
    fun i j _ ↦ Subsingleton.elim i j
  obtain ⟨P, hP, hzP⟩ := (hsG.closed_iff _ z).mp hz
  have hzP' : RelMap (L := L) (self := S.projection β G) P z := by
    rw [W.fixed hG]
    exact hzP
  obtain ⟨Q', hQ', -⟩ := (S.relMap_projection_of_isInvariant β G hP z).mp hzP'
  have hQ : S.τ β Q' = ⟨P, hP⟩ := Subtype.ext hQ'
  refine ⟨⟨1 + l, ⟨P, hP⟩⟩, ?_, z, hzP⟩
  change S.τ β ⟨P, hP⟩ = ⟨P, hP⟩
  rw [← hQ, (S.comp le_rfl Q').1]

end WeakSystem

/-! ### Lifts and base isomorphism -/

namespace GeometrySignature.BaseSublanguage

variable {Lc : Language.{wc, wc'}}

/-- **The target of an isomorphism of `L_c`-structures is the structure induced along its
bijection.**  Correspondence with the printed definitions. -/
theorem eq_inducedStructure_of_equiv (E : σ.BaseSublanguage Lc) {M N : Type v}
    {B : Lc.Structure M} {B' : Lc.Structure N} (g : @Language.Equiv Lc M N B B') :
    B' = @Equiv.inducedStructure Lc M N B (@Language.Equiv.toEquiv Lc M N B B' g) := by
  refine E.structure_ext fun n r y ↦ ?_
  have h := @Language.Equiv.map_rel' Lc M N B B' g n r
    ((@Language.Equiv.toEquiv Lc M N B B' g).symm ∘ y)
  have hy : (@Language.Equiv.toEquiv Lc M N B B' g) ∘
      ((@Language.Equiv.toEquiv Lc M N B B' g).symm ∘ y) = y :=
    funext fun i ↦ (@Language.Equiv.toEquiv Lc M N B B' g).apply_symm_apply (y i)
  exact (iff_of_eq (congrArg _ hy.symm)).trans h

end GeometrySignature.BaseSublanguage

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} (W : WeakSystem.{w, w', v} D S)
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **A lift is carried along an isomorphism of `L_c`-structures**: if `B` has a lift at `β` and
`B ≅ B'` with the carrier of `B'` countable, then `B'` has a lift at `β`: the lift `G`, induced
along the bijection of the isomorphism, is in `K_β` (`isoClosed`) and its reduct is `B'`
(`BaseSublanguage.reduct_inducedStructure`, `BaseSublanguage.eq_inducedStructure_of_equiv`).
Correspondence with the printed definitions. -/
theorem exists_isLiftAt_of_equiv {β : SystemLevel} {M N : Type v} [Countable N]
    {B : Lc.Structure M} {B' : Lc.Structure N} (g : @Language.Equiv Lc M N B B')
    (h : ∃ G : L.Structure M, W.IsLiftAt E β G B) :
    ∃ G' : L.Structure N, W.IsLiftAt E β G' B' := by
  obtain ⟨G, hG, hGB⟩ := h
  let e : M ≃ N := @Language.Equiv.toEquiv Lc M N B B' g
  refine ⟨@Equiv.inducedStructure L M N G e,
    W.isoClosed hG ⟨@Equiv.inducedStructureEquiv L M N G e⟩, ?_⟩
  rw [E.reduct_inducedStructure, hGB]
  exact (E.eq_inducedStructure_of_equiv g).symm

/-- **Having a lift at `β` is invariant under isomorphism of `L_c`-structures**, on countable
carriers (`exists_isLiftAt_of_equiv` both ways).  Correspondence with the printed definitions. -/
theorem exists_isLiftAt_iff_of_equiv {β : SystemLevel} {M N : Type v} [Countable M]
    [Countable N] {B : Lc.Structure M} {B' : Lc.Structure N} (g : @Language.Equiv Lc M N B B') :
    (∃ G : L.Structure M, W.IsLiftAt E β G B) ↔ ∃ G' : L.Structure N, W.IsLiftAt E β G' B' :=
  ⟨W.exists_isLiftAt_of_equiv E g,
    W.exists_isLiftAt_of_equiv E (@Language.Equiv.symm Lc M N B B' g)⟩

section Coded

variable [Lc.IsRelational]
variable (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) (β : SystemLevel)

/-- **Isomorphic coded models have lifts at `β` together** (`exists_isLiftAt_iff_of_equiv` on
`ℕ`).  Correspondence with the printed definitions. -/
theorem exists_isLiftAt_iff_of_isoSetoid {c c' : ModelsOf φ} (h : (isoSetoid φ).r c c') :
    (∃ G : L.Structure ℕ, W.IsLiftAt E β G c.1.toStructure) ↔
      ∃ G : L.Structure ℕ, W.IsLiftAt E β G c'.1.toStructure := by
  obtain ⟨g⟩ := h
  exact W.exists_isLiftAt_iff_of_equiv E g

/-- **A class without a lift: some member lacks one exactly when every member does**: `q` is in
`classesWithoutLift E φ β` exactly when no member of `q` has a lift at `β` on `ℕ`
(`exists_isLiftAt_iff_of_isoSetoid`).  Correspondence with the printed definitions. -/
theorem mem_classesWithoutLift_iff (q : Quotient (isoSetoid φ)) :
    q ∈ W.classesWithoutLift E φ β ↔
      ∀ c : ModelsOf φ, Quotient.mk (isoSetoid φ) c = q →
        ∀ G : L.Structure ℕ, ¬ W.IsLiftAt E β G c.1.toStructure := by
  constructor
  · rintro ⟨c, rfl, hc⟩ c' hc' G hG
    exact (not_exists.mpr hc) ((W.exists_isLiftAt_iff_of_isoSetoid E φ β
      (Quotient.exact hc')).mp ⟨G, hG⟩)
  · intro h
    obtain ⟨c, hc⟩ := Quotient.exists_rep q
    exact ⟨c, hc, h c hc⟩

/-- **A class with a lift, for every member**: `q` is not in `classesWithoutLift E φ β` exactly when
every member of `q` has a lift at `β` on `ℕ`.  Correspondence with the printed definitions. -/
theorem not_mem_classesWithoutLift_iff (q : Quotient (isoSetoid φ)) :
    q ∉ W.classesWithoutLift E φ β ↔
      ∀ c : ModelsOf φ, Quotient.mk (isoSetoid φ) c = q →
        ∃ G : L.Structure ℕ, W.IsLiftAt E β G c.1.toStructure := by
  constructor
  · intro h c hc
    by_contra hno
    exact h ⟨c, hc, not_exists.mp hno⟩
  · rintro h ⟨c, hc, hno⟩
    obtain ⟨G, hG⟩ := h c hc
    exact hno G hG

/-- **A class with a lift, for some member**: `q` is not in `classesWithoutLift E φ β` exactly when
some member of `q` has a lift at `β` on `ℕ` (`mem_classesWithoutLift_iff`).  Correspondence with
the printed definitions. -/
theorem not_mem_classesWithoutLift_iff_exists (q : Quotient (isoSetoid φ)) :
    q ∉ W.classesWithoutLift E φ β ↔
      ∃ c : ModelsOf φ, Quotient.mk (isoSetoid φ) c = q ∧
        ∃ G : L.Structure ℕ, W.IsLiftAt E β G c.1.toStructure := by
  rw [W.not_mem_classesWithoutLift_iff E φ β]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Quotient.exists_rep q
    exact ⟨c, hc, h c hc⟩
  · rintro ⟨c, hc, hG⟩ c' hc'
    exact (W.exists_isLiftAt_iff_of_isoSetoid E φ β
      (Quotient.exact (hc.trans hc'.symm))).mp hG

/-- **The partition of the coded classes at `β`**: every class `q` of `isoSetoid φ` is in
`classesWithoutLift E φ β`, or every member of `q` has a lift at `β` on `ℕ`
(`not_mem_classesWithoutLift_iff`).  Correspondence with the printed definitions. -/
theorem mem_classesWithoutLift_or (q : Quotient (isoSetoid φ)) :
    q ∈ W.classesWithoutLift E φ β ∨
      ∀ c : ModelsOf φ, Quotient.mk (isoSetoid φ) c = q →
        ∃ G : L.Structure ℕ, W.IsLiftAt E β G c.1.toStructure := by
  by_cases h : q ∈ W.classesWithoutLift E φ β
  · exact Or.inl h
  · exact Or.inr ((W.not_mem_classesWithoutLift_iff E φ β q).mp h)

end Coded

/-! ### Theorem 2.19 -/

section Count

variable [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)]
variable (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω)

omit [Countable (Σ n, Lc.Relations n)] in
/-- **Coded models with lifts at `β` holding one invariant are back-and-forth equivalent at `β`**:
if `G` and `G'` are lifts at `β` on `ℕ` of the codes `c` and `c'` and hold one invariant `Q` of
some tuples, then `c` and `c'` are related by `bfEquivSetoid φ β` ([AFK26, Proposition 2.18],
`bfEquivOfCommonInvariantTarget`, with the reducts `G↾L_c = c` and `G'↾L_c = c'`).
Correspondence with the printed definitions. -/
theorem bfEquivSetoid_r_of_isLiftAt {β : SystemLevel} {c c' : ModelsOf φ}
    (Q : Σ n, σ.Invariant n)
    (h : ∃ G : L.Structure ℕ, W.IsLiftAt E β G c.1.toStructure ∧
      ∃ a : Fin Q.1 → ℕ, RelMap (L := L) (self := G) Q.2.1 a)
    (h' : ∃ G' : L.Structure ℕ, W.IsLiftAt E β G' c'.1.toStructure ∧
      ∃ a' : Fin Q.1 → ℕ, RelMap (L := L) (self := G') Q.2.1 a') :
    (bfEquivSetoid φ β.1).r c c' := by
  obtain ⟨G, ⟨hG, hGc⟩, a, ha⟩ := h
  obtain ⟨G', ⟨hG', hG'c⟩, a', ha'⟩ := h'
  have hbf := W.bfEquivOfCommonInvariantTarget E ℕ ℕ β G G' hG hG' ⟨Q.1, Q.2, a, a', ha, ha'⟩
  rw [hGc, hG'c] at hbf
  exact hbf

/-- **[AFK26, Theorem 2.19], its back-and-forth content, coded** (`CountableBFClassesTarget`): if,
for every countable `β`, the coded classes with a member without a lift at `β` are countably many,
then for every `η < ω₁` the models of `φ` coded on `ℕ` fall into countably many classes of
`bfEquivSetoid φ η`.  At the level `β = η`: the classes whose chosen code has a lift at `β` inject
into the countable set of `β`-invariants (`exists_relMap_fixed_invariant`,
`InvariantSystem.countable`, `bfEquivSetoid_r_of_isLiftAt`); the other classes are images of
classes of `classesWithoutLift E φ β` (`isoSetoid_refines_bfEquivSetoid`).  The hypothesis that
`φ` axiomatizes the base is not used.  Correspondence with the printed definitions. -/
theorem countableBFClassesTarget : W.CountableBFClassesTarget E φ := by
  intro _ hA η hη
  let β : SystemLevel := ⟨η, hη⟩
  let toBF : Quotient (isoSetoid φ) → Quotient (bfEquivSetoid φ η) :=
    Quotient.lift (fun c ↦ Quotient.mk (bfEquivSetoid φ η) c)
      fun _ _ h ↦ Quotient.sound (isoSetoid_refines_bfEquivSetoid _ _ h)
  -- the classes whose chosen code has no lift at `β`
  have hlow : (toBF '' W.classesWithoutLift E φ β).Countable := (hA β).image _
  -- the classes whose chosen code has a lift at `β`
  let F := {Q : Σ n, σ.Invariant n | S.τ β Q.2 = Q.2}
  have hF : F.Countable := S.countable β
  let A := {x : Quotient (bfEquivSetoid φ η) |
    ∃ G : L.Structure ℕ, W.IsLiftAt E β G x.out.1.toStructure}
  have hex (x : A) : ∃ Q ∈ F, ∃ G : L.Structure ℕ, W.IsLiftAt E β G x.1.out.1.toStructure ∧
      ∃ a : Fin Q.1 → ℕ, RelMap (L := L) (self := G) Q.2.1 a := by
    obtain ⟨G, hG⟩ := x.2
    obtain ⟨Q, hQ, a, ha⟩ := W.exists_relMap_fixed_invariant hG.1
    exact ⟨Q, hQ, G, hG, a, ha⟩
  have hAc : A.Countable := by
    have := hF.to_subtype
    refine Set.countable_coe_iff.mp (Function.Injective.countable
      (f := fun x : A ↦ (⟨(hex x).choose, (hex x).choose_spec.1⟩ : F)) fun x x' hxx' ↦ ?_)
    have hQ : (hex x).choose = (hex x').choose := congrArg Subtype.val hxx'
    refine Subtype.ext ?_
    rw [← Quotient.out_eq x.1, ← Quotient.out_eq x'.1]
    exact Quotient.sound (W.bfEquivSetoid_r_of_isLiftAt E φ (β := β) _ (hex x).choose_spec.2
      (hQ ▸ (hex x').choose_spec.2))
  -- every class is in one of the two parts
  have hcover : (Set.univ : Set (Quotient (bfEquivSetoid φ η))) ⊆
      A ∪ toBF '' W.classesWithoutLift E φ β := by
    rintro x -
    by_cases h : ∃ G : L.Structure ℕ, W.IsLiftAt E β G x.out.1.toStructure
    · exact Or.inl h
    · exact Or.inr ⟨Quotient.mk _ x.out, ⟨x.out, rfl, not_exists.mp h⟩, Quotient.out_eq x⟩
  exact Set.countable_univ_iff.mp ((hAc.union hlow).mono hcover)

end Count

end WeakSystem

end VaughtConjecture.Correspondence

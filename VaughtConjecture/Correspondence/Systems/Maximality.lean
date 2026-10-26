/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Rank
import VaughtConjecture.Correspondence.Systems.Targets

/-!
# Maximality under isomorphism, and the coding passage for few maximal models

Numbering as in the current draft of [AFK26] (the published v1 reads identically).

* `GeometrySignature.eq_inducedStructure_of_equiv`,
  `GeometrySignature.inducedStructure_symm_inducedStructure`: the target of an isomorphism is the
  structure induced along its bijection, and inducing along a bijection and back is the identity;
* `WeakSystem.IsMaximalAt.of_equiv`: on countable carriers, a structure isomorphic to one maximal
  at `β` is maximal at `β` ([AFK26, Definition 2.20]; `K_β` is closed under isomorphism and
  projection commutes with transport);
* `WeakSystem.fewMaximalCodingTarget`: few maximal models over all countable carriers is
  equivalent to countably many classes on each positive finite carrier `Fin (n + 1)` and on `ℕ`.
  The finite carriers are treated as the infinite ones: a countable nonempty carrier is in
  bijection with some `Fin (n + 1)` or with `ℕ`, and maximality is transported along the
  bijection.  The representatives produced in `HasFewMaximal` are maximal: a member of a countable
  set of the canonical form isomorphic to a maximal structure is itself maximal.
-/

universe w w' v v'

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

namespace GeometrySignature

/-- **The target of an isomorphism is the structure induced along its bijection.**
Correspondence with the printed definitions. -/
theorem eq_inducedStructure_of_equiv (σ : GeometrySignature L) {M : Type v} {N : Type v'}
    {G : L.Structure M} {H : L.Structure N} (g : @Language.Equiv L M N G H) :
    H = @Equiv.inducedStructure L M N G (@Language.Equiv.toEquiv L M N G H g) := by
  refine σ.structure_ext fun n R y ↦ ?_
  have h := @Language.Equiv.map_rel' L M N G H g n R
    ((@Language.Equiv.toEquiv L M N G H g).symm ∘ y)
  have hy : (@Language.Equiv.toEquiv L M N G H g) ∘
      ((@Language.Equiv.toEquiv L M N G H g).symm ∘ y) = y :=
    funext fun i ↦ (@Language.Equiv.toEquiv L M N G H g).apply_symm_apply (y i)
  exact (iff_of_eq (congrArg _ hy.symm)).trans h

/-- **Inducing along a bijection and back is the identity.**  Correspondence with the printed
definitions. -/
theorem inducedStructure_symm_inducedStructure (σ : GeometrySignature L) {M : Type v}
    {N : Type v'} (G : L.Structure M) (e : M ≃ N) :
    @Equiv.inducedStructure L N M (@Equiv.inducedStructure L M N G e) e.symm = G := by
  refine σ.structure_ext fun n R x ↦ ?_
  have hx : e.symm ∘ (e.symm.symm ∘ x) = x := funext fun i ↦ e.symm_apply_apply (x i)
  exact iff_of_eq (congrArg (RelMap (L := L) (self := G) R) hx)

end GeometrySignature

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}

/-- **Maximality is invariant under isomorphism** ([AFK26, Definition 2.20]), on countable
carriers: if `G` is maximal at `β` and `G ≅ H`, then `H` is maximal at `β`.  A lift `H'` of `H` at
a higher level is pulled back to a lift of `G` along the isomorphism (`WeakSystem.isoClosed`,
`InvariantSystem.projection_inducedStructure`), equal to `G` by maximality, so `H' = H`.
Correspondence with the printed definitions. -/
theorem IsMaximalAt.of_equiv {W : WeakSystem.{w, w', v} D S} {β : SystemLevel} {M N : Type v}
    [Countable M] [Countable N] {G : L.Structure M} {H : L.Structure N}
    (hG : W.IsMaximalAt β G) (g : @Language.Equiv L M N G H) : W.IsMaximalAt β H := by
  set e := @Language.Equiv.toEquiv L M N G H g
  have hH : H = @Equiv.inducedStructure L M N G e := σ.eq_inducedStructure_of_equiv g
  refine ⟨W.isoClosed hG.1 ⟨g⟩, fun β' hβ' H' hH' hproj ↦ ?_⟩
  have hG'mem : @Equiv.inducedStructure L N M H' e.symm ∈ W.K β' M :=
    W.isoClosed hH' ⟨@Equiv.inducedStructureEquiv L N M H' e.symm⟩
  have hG'proj : S.projection β (@Equiv.inducedStructure L N M H' e.symm) = G := by
    rw [S.projection_inducedStructure, hproj, hH, σ.inducedStructure_symm_inducedStructure]
  have hGG' := hG.2 β' hβ' _ hG'mem hG'proj
  rw [hH, hGG']
  exact σ.inducedStructure_symm_inducedStructure H' e.symm

/-- **Few maximal models from a countable family in any universe**: the index type of
`HasFewMaximal` is in universe `0`; a countable family of representatives indexed by a type in any
universe is reindexed by `Shrink`.  Correspondence with the printed definitions. -/
theorem hasFewMaximal_of_family.{u} {W : WeakSystem.{w, w', v} D S}
    (h : ∀ β : SystemLevel, ∃ (ι : Type u) (_ : Countable ι) (C : ι → Type v)
      (_ : ∀ i, Countable (C i)) (H : ∀ i, L.Structure (C i)),
      (∀ i, W.IsMaximalAt β (H i)) ∧
      ∀ (M : Type v) [Countable M] (G : L.Structure M), W.IsMaximalAt β G →
        ∃ i, Nonempty (@Language.Equiv L M (C i) G (H i))) :
    W.HasFewMaximal := by
  intro β
  obtain ⟨ι, hι, C, hC, H, hmax, hrep⟩ := h β
  let s := equivShrink.{0} ι
  refine ⟨Shrink.{0} ι, Countable.of_equiv ι s, fun j ↦ C (s.symm j), fun j ↦ hC (s.symm j),
    fun j ↦ H (s.symm j), fun j ↦ hmax (s.symm j), fun M _ G hG ↦ ?_⟩
  obtain ⟨i, hi⟩ := hrep M G hG
  refine ⟨s i, ?_⟩
  beta_reduce
  generalize hj : s.symm (s i) = j
  rw [Equiv.symm_apply_apply] at hj
  subst hj
  exact hi

/-- **The coding passage for few maximal models** (`FewMaximalCodingTarget`,
[AFK26, Definition 2.20], carriers in universe `0`), including the positive finite carriers.
Forward: the representatives isomorphic to a structure on a canonical carrier `X` are transported
to `X` along a chosen bijection, countably many.  Backward: the representatives are the maximal
members of the countable sets on `Fin (n + 1)` and on `ℕ`; a maximal structure on a countable
carrier is nonempty (`WeakSystem.nonempty`), so its carrier is in bijection with some `Fin (n + 1)`
or with `ℕ`; the transported structure is maximal (`IsMaximalAt.of_equiv`) and isomorphic to a
member of the countable set, which is then maximal too.  Correspondence with the printed
definitions. -/
theorem fewMaximalCodingTarget (W : WeakSystem.{w, w', 0} D S) : W.FewMaximalCodingTarget := by
  constructor
  · intro h β
    obtain ⟨ι, hι, C, hC, H, -, hrep⟩ := h β
    have key (X : Type) [Countable X] :
        IsCountableUpToIso fun G : L.Structure X ↦ W.IsMaximalAt β G := by
      refine ⟨Set.range fun i : {i : ι // Nonempty (C i ≃ X)} ↦
        @Equiv.inducedStructure L (C i.1) X (H i.1) (Classical.choice i.2),
        Set.countable_range _, fun G hG ↦ ?_⟩
      obtain ⟨i, ⟨g⟩⟩ := hrep X G hG
      have hi : Nonempty (C i ≃ X) := ⟨(@Language.Equiv.toEquiv L X (C i) G (H i) g).symm⟩
      exact ⟨@Equiv.inducedStructure L (C i) X (H i) (Classical.choice hi), ⟨⟨i, hi⟩, rfl⟩,
        ⟨@Language.Equiv.comp L X (C i) G (H i) X
          (@Equiv.inducedStructure L (C i) X (H i) (Classical.choice hi))
          (@Equiv.inducedStructureEquiv L (C i) X (H i) (Classical.choice hi)) g⟩⟩
    exact ⟨fun n ↦ key (Fin (n + 1)), key ℕ⟩
  · intro h
    refine hasFewMaximal_of_family fun β ↦ ?_
    obtain ⟨hfin, hnat⟩ := h β
    choose T hTc hT using hfin
    obtain ⟨T', hT'c, hT'⟩ := hnat
    have hcf (n : ℕ) :
        Countable {G : L.Structure (Fin (n + 1)) // G ∈ T n ∧ W.IsMaximalAt β G} :=
      ((hTc n).mono (s₁ := {G | G ∈ T n ∧ W.IsMaximalAt β G}) fun _ hG ↦ hG.1).to_subtype
    have hcn : Countable {G : L.Structure ℕ // G ∈ T' ∧ W.IsMaximalAt β G} :=
      (hT'c.mono (s₁ := {G | G ∈ T' ∧ W.IsMaximalAt β G}) fun _ hG ↦ hG.1).to_subtype
    let ι := (Σ n : ℕ, {G : L.Structure (Fin (n + 1)) // G ∈ T n ∧ W.IsMaximalAt β G}) ⊕
      {G : L.Structure ℕ // G ∈ T' ∧ W.IsMaximalAt β G}
    let C : ι → Type := Sum.elim (fun p ↦ Fin (p.1 + 1)) fun _ ↦ ℕ
    let H : ∀ i, L.Structure (C i) :=
      Sum.rec (motive := fun i ↦ L.Structure (C i)) (fun p ↦ p.2.1) fun q ↦ q.1
    have hC (i : ι) : Countable (C i) := by
      cases i
      · exact (inferInstance : Countable (Fin _))
      · exact (inferInstance : Countable ℕ)
    refine ⟨ι, inferInstance, C, hC, H, ?_, fun M _ G hG ↦ ?_⟩
    · rintro (p | q)
      · exact p.2.2.2
      · exact q.2.2
    · have hne : Nonempty M := W.nonempty hG.1
      rcases finite_or_infinite M with hM | hM
      · obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin M
        cases k with
        | zero => exact Fin.elim0 (e (Classical.arbitrary M))
        | succ n =>
          have hG' : W.IsMaximalAt β (@Equiv.inducedStructure L M (Fin (n + 1)) G e) :=
            hG.of_equiv (@Equiv.inducedStructureEquiv L M (Fin (n + 1)) G e)
          obtain ⟨H', hH'T, ⟨g⟩⟩ := hT n _ hG'
          exact ⟨Sum.inl ⟨n, H', hH'T, hG'.of_equiv g⟩,
            ⟨@Language.Equiv.comp L M (Fin (n + 1)) G
              (@Equiv.inducedStructure L M (Fin (n + 1)) G e) (Fin (n + 1)) H' g
              (@Equiv.inducedStructureEquiv L M (Fin (n + 1)) G e)⟩⟩
      · obtain ⟨d⟩ := nonempty_denumerable M
        let e : M ≃ ℕ := @Denumerable.eqv M d
        have hG' : W.IsMaximalAt β (@Equiv.inducedStructure L M ℕ G e) :=
          hG.of_equiv (@Equiv.inducedStructureEquiv L M ℕ G e)
        obtain ⟨H', hH'T, ⟨g⟩⟩ := hT' _ hG'
        exact ⟨Sum.inr ⟨H', hH'T, hG'.of_equiv g⟩,
          ⟨@Language.Equiv.comp L M ℕ G (@Equiv.inducedStructure L M ℕ G e) ℕ H' g
            (@Equiv.inducedStructureEquiv L M ℕ G e)⟩⟩

end WeakSystem

end VaughtConjecture.Correspondence

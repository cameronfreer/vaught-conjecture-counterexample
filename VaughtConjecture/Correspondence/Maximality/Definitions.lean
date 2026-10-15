/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Density

/-!
# Maximality at a level, and transport along a bijection of carriers

Numbering as in the current draft of [AFK26].  Write `λ_β = blockStage β = ω + ω · β`.  `τ_β` is
`projectStructure β`, `K_β[L]` is `templateStageClass M β`, and `N↾L_c[L]` is `baseReduct N`.

**Maximality** [AFK26, Definition 2.20] (correspondence with the printed definitions).  For the
system of classes `⟨K_β⟩_{β ∈ ω₁}` and `β ∈ ω₁`, a structure `M ∈ K_β` is maximal at level `β`
"if whenever `β* > β` and `M* ∈ K_{β*}` and `τ_β(M*) = M`, then `M = M*`".  `IsMaximalAt β G` is
this clause for clause: `G ∈ K_β[L]`, and for every `β' < ω₁` (the index set of the system) with
`β < β'` and every `G' ∈ K_{β'}[L]` on the same carrier with `τ_β(G') = G`, `G = G'`.  The
printed definition **allows an unchanged higher lift**: a structure `G' = G` lying in `K_{β'}[L]`
does not contradict maximality.  No comparison with "no successor at `β + 1`" is made here; that
comparison needs a strictness statement (`VaughtConjecture.Correspondence.Maximality.Targets`),
which is not a consequence of "the rank is at most the stage" (`rankLeStageTarget`).  The range
`β < ω₁` is a hypothesis of the statements that use it.

**Transport along a bijection of carriers** (native construction).  For `e : M ≃ N`,
`transportStructure e G` is the structure induced on `N` by `e` (Mathlib's
`Equiv.inducedStructure`): a symbol holds of a tuple of `N` exactly when it holds in `G` of its
pullback along `e`, and `e` is an isomorphism `G ≃ transportStructure e G`
(`Equiv.inducedStructureEquiv`).  Proved here, directly from the definitions and with no
countability:

* the base reduct of a transport is the transport of the base reduct
  (`baseReduct_transportStructure`), and `τ_β` commutes with transport
  (`projectStructure_transportStructure`);
* the clauses of `K_β[L]` are invariant under isomorphism: the structured geometry
  (`Correspondence.IsStructuredGeometry.of_equiv`), the pairs of the diagram
  (`Correspondence.SatisfiesPairs.of_equiv`), compatibility (`IsTemplateCompatible.of_equiv`) and
  density `D[α]` (`SatisfiesDensityAt.of_equiv`), for every isomorphism, not only an induced one;
* hence membership in `K_β[L]` (`mem_templateStageClass_transportStructure_iff`) and maximality at
  `β` (`isMaximalAt_transportStructure_iff`) transport along `e`, in both directions, for every
  ordinal `β`.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

variable {M : Type v} {N : Type w}

/-! ### Maximality -/

/-- **Maximal at level `β`** [AFK26, Definition 2.20]: `G ∈ K_β[L]`, and whenever `β < β' < ω₁`
and `G' ∈ K_{β'}[L]` (on the same carrier) has `τ_β(G') = G`, then `G = G'`.  An unchanged higher
lift (`G' = G` in `K_{β'}[L]`) is allowed.  Correspondence with the printed definitions. -/
def IsMaximalAt (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  G ∈ templateStageClass M β ∧
    ∀ β' : Ordinal.{u}, β' < ω₁ → β < β' → ∀ G' ∈ templateStageClass M β',
      projectStructure β G' = G → G = G'

/-- A structure maximal at `β` is in `K_β[L]`.  Correspondence with the printed definitions. -/
theorem IsMaximalAt.mem_templateStageClass {β : Ordinal.{u}}
    {G : templateLanguage.{u}.Structure M} (hG : IsMaximalAt β G) :
    G ∈ templateStageClass M β :=
  hG.1

/-- A lift of a structure maximal at `β`, at a higher countable level, is the structure itself.
Correspondence with the printed definitions. -/
theorem IsMaximalAt.eq_of_projectStructure_eq {β β' : Ordinal.{u}}
    {G G' : templateLanguage.{u}.Structure M} (hG : IsMaximalAt β G) (hβ' : β' < ω₁)
    (hββ' : β < β') (hG' : G' ∈ templateStageClass M β') (h : projectStructure β G' = G) :
    G = G' :=
  hG.2 β' hβ' hββ' G' hG' h

/-! ### Invariance of the clauses under isomorphism -/

namespace Correspondence

variable {L : Language} {σ : GeometrySignature L} [L.Structure M] [L.Structure N]

/-- **A structured geometry is invariant under isomorphism** ([AFK26, Definition 2.2]).
Native construction. -/
theorem IsStructuredGeometry.of_equiv (g : M ≃[L] N) (h : IsStructuredGeometry σ M) :
    IsStructuredGeometry σ N := by
  have hr : ∀ {n : ℕ} (r : L.Relations n) (x : Fin n → N),
      RelMap r x ↔ RelMap r (g.symm ∘ x) := fun r x ↦ (g.symm.map_rel r x).symm
  refine ⟨⟨fun n hn x hx ↦ ?_, fun n hn x e ↦ ?_, fun n hn x hx ↦ ?_,
    fun n₀ n₁ k h₀ h₁ hk x y z hx hy hz hxyz ↦ ?_⟩, fun n hn x ↦ ?_,
    fun n Q Q' hQ hQ' hne x hx hx' ↦ ?_, fun n k Q R i hQ x y hx hy ↦ ?_⟩
  · exact (Function.Injective.of_comp_iff g.symm.injective x).mp
      (h.isGeometry.injective hn _ ((hr _ x).mp hx))
  · rw [hr, hr]
    exact h.isGeometry.perm hn (g.symm ∘ x) e
  · obtain ⟨k, y, hy, hP⟩ := h.isGeometry.exists_closed hn (g.symm ∘ x)
      (g.symm.injective.comp hx)
    refine ⟨k, g ∘ y, funext fun i ↦ ?_, (g.map_rel _ y).mpr hP⟩
    have hi := congrFun hy i
    simp only [Function.comp_apply] at hi ⊢
    rw [hi, Language.Equiv.apply_symm_apply]
  · rw [hr]
    refine h.isGeometry.inter h₀ h₁ hk (g.symm ∘ x) (g.symm ∘ y) (g.symm ∘ z)
      ((hr _ x).mp hx) ((hr _ y).mp hy) (g.symm.injective.comp hz) ?_
    rw [Set.range_comp, Set.range_comp, Set.range_comp, hxyz,
      Set.image_inter g.symm.injective]
  · rw [hr, h.closed_iff]
    exact exists_congr fun Q ↦ and_congr_right fun _ ↦ (hr Q x).symm
  · exact h.exclusive Q Q' hQ hQ' hne (g.symm ∘ x) ((hr _ x).mp hx) ((hr _ x).mp hx')
  · rw [hr R (x ∘ i), hr R (y ∘ i)]
    exact h.determines Q R i hQ (g.symm ∘ x) (g.symm ∘ y) ((hr _ x).mp hx) ((hr _ y).mp hy)

/-- **The pairs of a diagram are invariant under isomorphism** ([AFK26, Definition 2.5], second
clause).  Native construction. -/
theorem SatisfiesPairs.of_equiv {D : Set (DiagramPair L)} (g : M ≃[L] N)
    (h : SatisfiesPairs D M) : SatisfiesPairs D N := fun π hπ x hx ↦
  (StrongHomClass.realize_formula g.symm π.2.2).mp
    (h π hπ (g.symm ∘ x) ((g.symm.map_rel _ x).mpr hx))

end Correspondence

/-- **Compatibility with `ID[L]` is invariant under isomorphism** ([AFK26, Definition 2.5]).
Native construction. -/
theorem IsTemplateCompatible.of_equiv {G : templateLanguage.{u}.Structure M}
    {G' : templateLanguage.{u}.Structure N} (g : @Language.Equiv templateLanguage.{u} M N G G')
    (h : IsTemplateCompatible G) : IsTemplateCompatible G' :=
  ⟨h.isStructuredGeometry.of_equiv g, h.satisfiesPairs.of_equiv g⟩

/-- **Density `D[α]` is invariant under isomorphism** ([AFK26, Definition 4.20]).
Native construction. -/
theorem SatisfiesDensityAt.of_equiv {α : Ordinal.{u}} {G : templateLanguage.{u}.Structure M}
    {G' : templateLanguage.{u}.Structure N} (g : @Language.Equiv templateLanguage.{u} M N G G')
    (h : SatisfiesDensityAt α G) : SatisfiesDensityAt α G' := by
  intro n m hn t u hpair x hx
  obtain ⟨y, s, hs, hxy⟩ := h hn t u hpair (g.symm ∘ x) ((g.symm.map_rel _ x).mpr hx)
  refine ⟨g ∘ y, s, hs, ?_⟩
  have he : Fin.append x (g ∘ y) = g ∘ Fin.append (g.symm ∘ x) y := by
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;> simp
  rw [he]
  exact (g.map_rel _ _).mpr hxy

/-! ### Transport along a bijection of carriers -/

/-- **The transport of a structure along a bijection of carriers** `e : M ≃ N`: the structure
induced on `N` (Mathlib's `Equiv.inducedStructure`).  Native construction. -/
@[instance_reducible] def transportStructure (e : M ≃ N) (G : templateLanguage.{u}.Structure M) :
    templateLanguage.{u}.Structure N :=
  @Equiv.inducedStructure templateLanguage.{u} M N G e

/-- A symbol holds of a tuple in the transport exactly when it holds in `G` of the pullback.
Native construction. -/
theorem relMap_transportStructure (e : M ≃ N) (G : templateLanguage.{u}.Structure M) {k : ℕ}
    (r : TemplateSymbol.{u} k) (xs : Fin k → N) :
    RelMap (L := templateLanguage.{u}) (self := transportStructure e G) r xs ↔
      RelMap (L := templateLanguage.{u}) (self := G) r (e.symm ∘ xs) :=
  Iff.rfl

/-- **The bijection is an isomorphism onto the transport** (`Equiv.inducedStructureEquiv`).
Native construction. -/
def transportEquiv (e : M ≃ N) (G : templateLanguage.{u}.Structure M) :
    @Language.Equiv templateLanguage.{u} M N G (transportStructure e G) :=
  @Equiv.inducedStructureEquiv templateLanguage.{u} M N G e

/-- The underlying bijection of `transportEquiv e G` is `e`.  Native construction. -/
@[simp] theorem toEquiv_transportEquiv (e : M ≃ N) (G : templateLanguage.{u}.Structure M) :
    @Language.Equiv.toEquiv templateLanguage.{u} M N G (transportStructure e G)
      (transportEquiv e G) = e :=
  rfl

/-- **Transport back along the inverse bijection gives the structure back.**
Native construction. -/
@[simp] theorem transportStructure_symm_transportStructure (e : M ≃ N)
    (G : templateLanguage.{u}.Structure M) :
    transportStructure e.symm (transportStructure e G) = G :=
  templateStructure_ext fun r xs ↦ by
    change RelMap (L := templateLanguage.{u}) (self := G) r (e.symm ∘ (e.symm.symm ∘ xs)) ↔ _
    rw [Equiv.symm_symm, ← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp]

/-- **Transport along the inverse bijection and back gives the structure back.**
Native construction. -/
@[simp] theorem transportStructure_transportStructure_symm (e : M ≃ N)
    (H : templateLanguage.{u}.Structure N) :
    transportStructure e (transportStructure e.symm H) = H := by
  simpa using transportStructure_symm_transportStructure e.symm H

/-- **The isomorphism class is the class of transports**: if `g : G ≃ H` is an isomorphism with
underlying bijection `e`, then `H` is the transport of `G` along `e`
(`FirstOrder.Language.Equiv.inducedStructure_eq`).  Native construction. -/
theorem transportStructure_eq_of_equiv {G : templateLanguage.{u}.Structure M}
    {H : templateLanguage.{u}.Structure N} (g : @Language.Equiv templateLanguage.{u} M N G H) :
    transportStructure (@Language.Equiv.toEquiv templateLanguage.{u} M N G H g) G = H :=
  templateStructure_ext fun r xs ↦ by
    change RelMap (L := templateLanguage.{u}) (self := G) r (g.symm ∘ xs) ↔ _
    exact g.symm.map_rel r xs

/-- **The base reduct of a transport is the transport of the base reduct**: both read each base
symbol of a tuple of `N` at its pullback.  Correspondence with the printed definitions. -/
theorem baseReduct_transportStructure (e : M ≃ N) (G : templateLanguage.{u}.Structure M) :
    baseReduct (transportStructure e G) =
      @Equiv.inducedStructure baseTemplateLanguage.{u} M N (baseReduct G) e :=
  baseStructure_ext fun _ _ ↦ Iff.rfl

/-- **Projection commutes with transport**: `τ_β` of a transport is the transport of `τ_β`.
Correspondence with the printed definitions. -/
theorem projectStructure_transportStructure (β : Ordinal.{u}) (e : M ≃ N)
    (G : templateLanguage.{u}.Structure M) :
    projectStructure β (transportStructure e G) = transportStructure e (projectStructure β G) :=
  templateStructure_ext fun r _ ↦ by cases r <;> exact Iff.rfl

/-- **Membership in `K_β[L]` transports along a bijection** (one direction).
Correspondence with the printed definitions. -/
theorem mem_templateStageClass_transportStructure {β : Ordinal.{u}} (e : M ≃ N)
    {G : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M β) :
    transportStructure e G ∈ templateStageClass N β := by
  obtain ⟨hM, hc, hfix, hd⟩ := hG
  exact ⟨hM.map e, hc.of_equiv (transportEquiv e G),
    by rw [projectStructure_transportStructure, hfix],
    fun α hα ↦ (hd α hα).of_equiv (transportEquiv e G)⟩

/-- **Membership in `K_β[L]` transports along a bijection**, for every ordinal `β`.
Correspondence with the printed definitions. -/
theorem mem_templateStageClass_transportStructure_iff {β : Ordinal.{u}} (e : M ≃ N)
    (G : templateLanguage.{u}.Structure M) :
    transportStructure e G ∈ templateStageClass N β ↔ G ∈ templateStageClass M β :=
  ⟨fun h ↦ by simpa using mem_templateStageClass_transportStructure e.symm h,
    mem_templateStageClass_transportStructure e⟩

/-- **Maximality at `β` transports along a bijection** (one direction): a lift on `N` of the
transport pulls back to a lift on `M` of `G`.  Correspondence with the printed definitions. -/
theorem IsMaximalAt.transportStructure {β : Ordinal.{u}} (e : M ≃ N)
    {G : templateLanguage.{u}.Structure M} (hG : IsMaximalAt β G) :
    IsMaximalAt β (transportStructure e G) := by
  refine ⟨mem_templateStageClass_transportStructure e hG.1, fun β' hβ' hββ' H hH hHG ↦ ?_⟩
  have hpull : G = VaughtConjecture.transportStructure e.symm H :=
    hG.2 β' hβ' hββ' _ (mem_templateStageClass_transportStructure e.symm hH) (by
      rw [projectStructure_transportStructure, hHG, transportStructure_symm_transportStructure])
  rw [hpull, transportStructure_transportStructure_symm]

/-- **Maximality at `β` transports along a bijection**, for every ordinal `β`.
Correspondence with the printed definitions. -/
theorem isMaximalAt_transportStructure_iff {β : Ordinal.{u}} (e : M ≃ N)
    (G : templateLanguage.{u}.Structure M) :
    IsMaximalAt β (transportStructure e G) ↔ IsMaximalAt β G :=
  ⟨fun h ↦ by simpa using h.transportStructure e.symm, (·.transportStructure e)⟩

end

end VaughtConjecture

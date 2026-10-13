/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ClassRealization

/-!
# The structure of a well-formed class realization is compatible, and `ID[L]` is an invariance
diagram

Numbering as in the current draft of [AFK26].

**Compatibility** (`ClassRealization.IsWellFormed.isTemplateCompatible`, native construction):
the structure `R.toStructure` of a consistent, covering class realization with legal types, at any
stage, is compatible with `ID[L]` ([AFK26, Definitions 2.5 and 4.18]).  Each clause:

* the pairs: a tuple with the invariant `Q_c` has exactly the relations `c` prescribes along
  every sequence of its places (`ClassRealization.relMap_comp_iff_holds`), by consistency and the
  commutation of faces with stage reduction;
* [AFK26, Definition 2.1], `Th_Geo`: `P_n` holds only of injective tuples; it is invariant under
  permutations of places (a face along a bijection is always defined); every injective tuple
  extends to a closed one with the old points first (covering, then a bijection of places putting
  the covered tuple first, `exists_equiv_castAdd`); and the common points of two closed tuples
  form a closed tuple (both are faces of one typed tuple covering their union, and the faces of a
  stage type are closed under intersection);
* [AFK26, Definition 2.2] (b)–(d): `P_n` holds exactly when some invariant does, invariants are
  exclusive (one class per tuple), and an invariant determines the relations along its places
  (from the pairs).

**Finite charts realize every invariant** ([AFK26, Definition 2.4 (c)], correspondence with the
printed definitions): the chart of a strongly coded legal stage type `t` at stage `ω₁`, the
structure `StageType.Holds` on `Fin n` of `VaughtConjecture.Correspondence.Charts.Chart`, is the
structure of the class realization of the faces of `t`
(`StageType.toStructure_faceClassRealization`),
which is well formed; so it is compatible with `ID[L]` (`StageType.isTemplateCompatible_chart`)
and `Q_{[t]}` holds of the identity tuple.  Hence `templateDiagram`, the pairs of `ID[L]` with
the three clauses of [AFK26, Definition 2.4] (`mem_pairs`, `exactlyOne`, `realized`), is an
`InvarianceDiagram` for `templateSignature`, and compatibility with it is `IsTemplateCompatible`
(`isCompatible_templateDiagram_iff`).

**B.T5 and B.T6** (`decoderRoundTrip`, `densityDecoderEquivalence`).
Uses compatibility — structured geometry and pair satisfaction — but not Definition 2.4(c), nor a
positional presentation.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Faces of classes -/

namespace TemplateClass

open StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- The identity face of a class is the class.  Native construction. -/
@[simp] theorem restrictFace_refl (c : TemplateClass.{u} α n) :
    c.restrictFace (Function.Embedding.refl _) = some c :=
  Quotient.inductionOn c fun t ↦ by
    rw [restrictFace_toClass, StageType.restrictFace_refl, Option.map_some]

/-- **Faces of faces are faces**, including definedness.  Native construction. -/
theorem restrictFace_trans {c : TemplateClass.{u} α n} {d : TemplateClass.{u} α m}
    {f : Fin m ↪ Fin n} (h : c.restrictFace f = some d) (g : Fin k ↪ Fin m) :
    d.restrictFace g = c.restrictFace (g.trans f) := by
  induction c using Quotient.inductionOn with
  | h t =>
    rw [restrictFace_toClass] at h
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [restrictFace_toClass, restrictFace_toClass, StageType.restrictFace_trans t f g hs]

/-- The face of a class along a bijection of places is defined.  Native construction. -/
theorem isSome_restrictFace_equiv (c : TemplateClass.{u} α n) (e : Fin m ≃ Fin n) :
    (c.restrictFace e.toEmbedding).isSome :=
  Quotient.inductionOn c fun t ↦ by
    rw [restrictFace_toClass, Option.isSome_map, StageType.isSome_restrictFace_iff,
      Finset.map_univ_equiv]
    exact t.univ_mem_faces

/-- **Faces of legal classes are legal** (the hereditary property of [AFK26, Proposition 4.32] on
classes).  Native construction. -/
theorem IsStronglyCodedLegal.restrictFace {c : TemplateClass.{u} α n}
    (hc : c.IsStronglyCodedLegal) {f : Fin m ↪ Fin n} {d : TemplateClass.{u} α m}
    (h : c.restrictFace f = some d) : d.IsStronglyCodedLegal := by
  induction c using Quotient.inductionOn with
  | h t =>
    rw [restrictFace_toClass] at h
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hc.1.restrictFace f hs, isStronglyCoded_of_restrictFace hs hc.2⟩

/-- The class of a stage type at stage `ω₁` is its own class at `ω₁`.  Native construction. -/
@[simp] theorem globalClass_omega_one (c : TemplateClass.{u} ω₁ n) : c.globalClass = c :=
  reduce_self _ c

/-- **The common places of two defined faces span a defined face**: the faces of a stage type
are closed under intersection.  Native construction. -/
theorem isSome_restrictFace_inter {c : TemplateClass.{u} α n} {n₀ n₁ : ℕ} {a : Fin n₀ ↪ Fin n}
    {b : Fin n₁ ↪ Fin n} {g : Fin k ↪ Fin n} (ha : (c.restrictFace a).isSome)
    (hb : (c.restrictFace b).isSome) (h : Set.range g = Set.range a ∩ Set.range b) :
    (c.restrictFace g).isSome := by
  induction c using Quotient.inductionOn with
  | h T =>
    simp only [restrictFace_toClass, Option.isSome_map, StageType.isSome_restrictFace_iff]
      at ha hb ⊢
    have hg : Finset.univ.map g = Finset.univ.map a ⊓ Finset.univ.map b := by
      ext j
      have := Set.ext_iff.mp h j
      simpa [Set.mem_range, Set.mem_inter_iff] using this
    rw [hg]
    exact T.isPlan.infClosed ha hb

end TemplateClass

/-! ### Embeddings of places -/

/-- **An embedding of places extends to a bijection putting its image first**.  Native
construction. -/
theorem exists_equiv_castAdd {n m : ℕ} (f : Fin n ↪ Fin m) :
    ∃ (k : ℕ) (σ : Fin (n + k) ≃ Fin m), ∀ i, σ (Fin.castAdd k i) = f i := by
  classical
  let A : Set (Fin m) := Set.range f
  let e₁ : Fin n ≃ A := Equiv.ofInjective f f.injective
  let e₂ : ↥Aᶜ ≃ Fin (Fintype.card ↥Aᶜ) := Fintype.equivFin _
  refine ⟨Fintype.card ↥Aᶜ, finSumFinEquiv.symm.trans
    ((Equiv.sumCongr e₁ e₂.symm).trans (Equiv.Set.sumCompl A)), fun i ↦ ?_⟩
  simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
  rfl

/-- **A tuple of points of a tuple factors through an embedding of places**.  Native
construction. -/
theorem exists_embedding_comp_eq {M : Type v} {n m : ℕ} (u : Fin m ↪ M) {x : Fin n → M}
    (hx : Function.Injective x) (h : ∀ i, ∃ a, u a = x i) :
    ∃ a : Fin n ↪ Fin m, ∀ i, u (a i) = x i := by
  choose a ha using h
  exact ⟨⟨a, fun i j hij ↦ hx (by rw [← ha i, ← ha j, hij])⟩, ha⟩

/-! ### The structure of a class realization -/

namespace ClassRealization

variable {α : Ordinal.{u}} {M : Type v} {R : ClassRealization.{u, v} α M} {n k : ℕ}

/-- Consistency along a sequence of places, for tuples given as injective maps.  Native
construction. -/
theorem eval_comp (hR : R.IsConsistent) {x : Fin n → M} (hx : Function.Injective x)
    {c : TemplateClass.{u} α n} (h : R.eval ⟨x, hx⟩ = some c) (i : Fin k ↪ Fin n)
    (hxi : Function.Injective (x ∘ i)) : R.eval ⟨x ∘ i, hxi⟩ = c.restrictFace i :=
  hR ⟨x, hx⟩ c i h

/-- **Every finite set of points lies in a typed tuple** of a covering class realization.
Native construction. -/
theorem IsCovering.exists_finset (hc : R.IsCovering) (s : Finset M) :
    ∃ (m : ℕ) (u : Fin m ↪ M) (c : TemplateClass.{u} α m), R.eval u = some c ∧
      ∀ p ∈ s, p ∈ Set.range u := by
  let w : Fin s.card ↪ M := ⟨fun i ↦ (s.equivFin.symm i : M), fun i j hij ↦
    s.equivFin.symm.injective (Subtype.ext hij)⟩
  obtain ⟨m, u, f, hfu, hu⟩ := hc w
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hu
  refine ⟨m, u, c, hc, fun p hp ↦ ⟨f (s.equivFin ⟨p, hp⟩), ?_⟩⟩
  have := congrArg (fun g : Fin s.card ↪ M ↦ g (s.equivFin ⟨p, hp⟩)) hfu
  change u (f _) = ((s.equivFin.symm (s.equivFin ⟨p, hp⟩) : s) : M) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

/-- `P_k` holds in the structure of a class realization exactly at the injective typed tuples.
Native construction. -/
theorem relMap_closed_iff {hk : 0 < k} {x : Fin k → M} :
    RelMap (L := templateLanguage.{u}) (self := R.toStructure) (TemplateSymbol.closed hk) x ↔
      ∃ h : Function.Injective x, (R.eval ⟨x, h⟩).isSome := by
  refine exists_congr fun h ↦ ?_
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨c, hc, _⟩ ↦ ⟨c, hc⟩, fun ⟨c, hc⟩ ↦ ⟨c, hc, trivial⟩⟩

/-- **The pairs of `ID[L]` hold in the structure of a consistent class realization**: a tuple
with the invariant `Q_c` has, along every sequence `i` of its places, exactly the relations `r`
with `c.Holds r i`.  Native construction. -/
theorem relMap_comp_iff_holds (hR : R.IsConsistent) {hn : 0 < n} {c : LegalClass.{u} n}
    {x : Fin n → M}
    (hx : RelMap (L := templateLanguage.{u}) (self := R.toStructure)
      (TemplateSymbol.invariant c hn) x) (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) :
    RelMap (L := templateLanguage.{u}) (self := R.toStructure) r (x ∘ i) ↔ c.1.Holds r i := by
  obtain ⟨hinj, d, hd, hdc⟩ := hx
  change d.globalClass = c.1 at hdc
  constructor
  · rintro ⟨hxi, e, he, hr⟩
    have hi : Function.Injective i := hxi.of_comp
    replace he : d.restrictFace ⟨i, hi⟩ = some e := (eval_comp hR hinj hd ⟨i, hi⟩ hxi).symm.trans he
    refine ⟨hi, e.globalClass, ?_, hr⟩
    rw [← hdc, TemplateClass.globalClass, TemplateClass.restrictFace_reduce, he, Option.map_some]
    rfl
  · rintro ⟨hi, s, hs, hr⟩
    rw [← hdc, TemplateClass.globalClass, TemplateClass.restrictFace_reduce] at hs
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨hinj.comp hi, e, (eval_comp hR hinj hd ⟨i, hi⟩ (hinj.comp hi)).trans he, hr⟩

/-- `P_k` holds of `x ∘ e` for a bijection `e` of places when it holds of `x`.  Native
construction. -/
private theorem relMap_closed_comp_equiv (hR : R.IsConsistent) {hk : 0 < k} {x : Fin k → M}
    (hx : RelMap (L := templateLanguage.{u}) (self := R.toStructure)
      (TemplateSymbol.closed hk) x) (e : Fin k ≃ Fin k) :
    RelMap (L := templateLanguage.{u}) (self := R.toStructure) (TemplateSymbol.closed hk)
      (x ∘ e) := by
  obtain ⟨h, hs⟩ := relMap_closed_iff.mp hx
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  have hxe : Function.Injective (x ∘ e) := h.comp e.injective
  refine relMap_closed_iff.mpr ⟨hxe, ?_⟩
  change (R.eval (e.toEmbedding.trans ⟨x, h⟩)).isSome
  rw [hR _ c _ hc]
  exact c.isSome_restrictFace_equiv e

/-- **The structure of a well-formed class realization satisfies `Th_Geo`** ([AFK26,
Definition 2.1]).  Native construction. -/
theorem IsWellFormed.isGeometry (hR : R.IsWellFormed) :
    letI := R.toStructure
    Correspondence.IsGeometry templateSignature.{u} M := by
  let _inst : templateLanguage.{u}.Structure M := R.toStructure
  refine ⟨fun n hn x hx ↦ (relMap_closed_iff.mp hx).1, fun n hn x e ↦ ?_,
    fun n hn x hx ↦ ?_, fun n₀ n₁ k h₀ h₁ hk x y z hx hy hz hzxy ↦ ?_⟩
  · refine ⟨fun h ↦ relMap_closed_comp_equiv hR.isConsistent h e, fun h ↦ ?_⟩
    have := relMap_closed_comp_equiv hR.isConsistent h e.symm
    rw [Function.comp_assoc, e.self_comp_symm, Function.comp_id] at this
    exact this
  · obtain ⟨m, u, f, hfu, hu⟩ := hR.isCovering ⟨x, hx⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hu
    obtain ⟨k, σ, hσ⟩ := exists_equiv_castAdd f
    refine ⟨k, u ∘ σ, funext fun i ↦ ?_, relMap_closed_iff.mpr ⟨u.injective.comp σ.injective, ?_⟩⟩
    · change u (σ (Fin.castAdd k i)) = x i
      rw [hσ]
      exact congrArg (fun g : Fin n ↪ M ↦ g i) hfu
    · change (R.eval (σ.toEmbedding.trans u)).isSome
      rw [hR.isConsistent u c _ hc]
      exact c.isSome_restrictFace_equiv σ
  · classical
    obtain ⟨hxi, hxs⟩ := relMap_closed_iff.mp hx
    obtain ⟨hyi, hys⟩ := relMap_closed_iff.mp hy
    obtain ⟨m, u, c, hc, hsub⟩ := hR.isCovering.exists_finset
      (Finset.univ.image x ∪ Finset.univ.image y)
    obtain ⟨a, ha⟩ := exists_embedding_comp_eq u hxi fun i ↦ hsub _ (by simp)
    obtain ⟨b, hb⟩ := exists_embedding_comp_eq u hyi fun i ↦ hsub _ (by simp)
    obtain ⟨g, hg⟩ := exists_embedding_comp_eq u hz fun i ↦ by
      have hzi : z i ∈ Set.range x ∩ Set.range y := hzxy ▸ Set.mem_range_self i
      obtain ⟨j, hj⟩ := hzi.1
      exact ⟨a j, (ha j).trans hj⟩
    obtain rfl : x = u ∘ a := funext fun i ↦ (ha i).symm
    obtain rfl : y = u ∘ b := funext fun i ↦ (hb i).symm
    obtain rfl : z = u ∘ g := funext fun i ↦ (hg i).symm
    change (R.eval (a.trans u)).isSome at hxs
    change (R.eval (b.trans u)).isSome at hys
    rw [hR.isConsistent u c a hc] at hxs
    rw [hR.isConsistent u c b hc] at hys
    have hrange : Set.range g = Set.range a ∩ Set.range b := by
      rw [Set.range_comp, Set.range_comp, Set.range_comp, ← Set.image_inter u.injective] at hzxy
      exact Set.image_injective.mpr u.injective hzxy
    refine relMap_closed_iff.mpr ⟨hz, ?_⟩
    change (R.eval (g.trans u)).isSome
    rw [hR.isConsistent u c g hc]
    exact TemplateClass.isSome_restrictFace_inter hxs hys hrange

/-- **The structure of a well-formed class realization has a structured geometry**
([AFK26, Definition 2.2]).  Native construction. -/
theorem IsWellFormed.isStructuredGeometry (hR : R.IsWellFormed) :
    letI := R.toStructure
    Correspondence.IsStructuredGeometry templateSignature.{u} M := by
  let _inst : templateLanguage.{u}.Structure M := R.toStructure
  refine ⟨hR.isGeometry, fun n hn x ↦ ⟨fun h ↦ ?_, fun ⟨Q, hQ, hx⟩ ↦ ?_⟩,
    fun n Q Q' hQ hQ' hne x hx hx' ↦ ?_, fun n k Q r i hQ x y hx hy ↦ ?_⟩
  · obtain ⟨hinj, hs⟩ := relMap_closed_iff.mp h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨TemplateSymbol.invariant ⟨d.globalClass,
      (TemplateClass.isStronglyCodedLegal_reduce_iff _ d).mpr (hR.hasLegalTypes _ d hd)⟩ hn,
      trivial, hinj, d, hd, rfl⟩
  · rcases Q with _ | ⟨c, _⟩ | _ <;> try exact hQ.elim
    obtain ⟨hinj, d, hd, -⟩ := hx
    exact relMap_closed_iff.mpr ⟨hinj, by rw [hd]; rfl⟩
  · rcases Q with _ | ⟨c, _⟩ | _ <;> try exact hQ.elim
    rcases Q' with _ | ⟨c', _⟩ | _ <;> try exact hQ'.elim
    obtain ⟨h₁, d, hd, hdc⟩ := hx
    obtain ⟨h₂, d', hd', hdc'⟩ := hx'
    obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    obtain rfl : c = c' := Subtype.ext
      ((show d.globalClass = c.1 from hdc).symm.trans hdc')
    exact hne rfl
  · rcases Q with _ | ⟨c, _⟩ | _ <;> try exact hQ.elim
    exact (relMap_comp_iff_holds hR.isConsistent hx r i).trans
      (relMap_comp_iff_holds hR.isConsistent hy r i).symm

/-- **The structure of a well-formed class realization is compatible with `ID[L]`** ([AFK26,
Definitions 2.5 and 4.18]), at every stage.  Native construction. -/
theorem IsWellFormed.isTemplateCompatible (hR : R.IsWellFormed) :
    IsTemplateCompatible R.toStructure :=
  ⟨hR.isStructuredGeometry, (satisfiesPairs_templateDiagramPairs_iff R.toStructure).mpr
    fun _ _ _ _ hx _ r i ↦ relMap_comp_iff_holds hR.isConsistent hx r i⟩

end ClassRealization

/-! ### Charts realize every invariant -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The class realization of the faces of a stage type**, on its points: a tuple of places has
the class of the face of `t` along it, if that face is defined.  Native construction. -/
def faceClassRealization (t : StageType.{u} α n) : ClassRealization.{u, 0} α (Fin n) where
  eval s := (restrictFace s t).map toClass

/-- **The class realization of the faces of a strongly coded legal stage type is well formed.**
Native construction. -/
theorem IsStronglyCodedLegal.isWellFormed_faceClassRealization {t : StageType.{u} α n}
    (ht : t.IsStronglyCodedLegal) : t.faceClassRealization.IsWellFormed where
  isConsistent := by
    intro m k s c f h
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    change (restrictFace (f.trans s) t).map toClass = _
    rw [← StageType.restrictFace_trans t s f hs', TemplateClass.restrictFace_toClass]
  isCovering := by
    intro k s
    exact ⟨n, Function.Embedding.refl _, s, rfl, by simp [faceClassRealization]⟩
  hasLegalTypes := by
    intro k s c h
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ht.1.restrictFace s hs', isStronglyCoded_of_restrictFace hs' ht.2⟩

/-- **The chart of a stage type** (`StageType.Holds`, the structure of
[AFK26, Definition 4.31]) **is the structure of the class realization of its faces.**  Native
construction. -/
theorem toStructure_faceClassRealization (t : StageType.{u} α n) :
    t.faceClassRealization.toStructure =
      (inferInstance : templateLanguage.{u}.Structure t.TemplateChart) := by
  refine templateStructure_ext fun r xs ↦ exists_congr fun h ↦ ?_
  constructor
  · rintro ⟨c, hc, hr⟩
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact ⟨s, hs, hr⟩
  · rintro ⟨s, hs, hr⟩
    refine ⟨s.toClass, ?_, hr⟩
    change (restrictFace _ t).map toClass = _
    rw [hs]
    rfl

/-- **The chart of a strongly coded legal stage type is compatible with `ID[L]`** ([AFK26,
Definitions 2.5, 4.18 and 4.31]).  Correspondence with the printed definitions. -/
theorem IsStronglyCodedLegal.isTemplateCompatible_chart {t : StageType.{u} α n}
    (ht : t.IsStronglyCodedLegal) :
    IsTemplateCompatible (inferInstance : templateLanguage.{u}.Structure t.TemplateChart) := by
  have h := ht.isWellFormed_faceClassRealization.isTemplateCompatible
  rw [toStructure_faceClassRealization] at h
  exact h

end StageType

/-- **Every invariant is realized in a finite compatible structure** ([AFK26, Definition 2.4 (c)]
for `ID[L]`): for a legal class `c` on `n ≥ 1` points, the chart of a representative is a finite
structure compatible with `ID[L]` in which `Q_c` holds of the identity tuple.  Correspondence
with the printed definitions. -/
theorem exists_isTemplateCompatible_relMap_invariant {n : ℕ} (hn : 0 < n)
    (c : LegalClass.{u} n) :
    ∃ (M : Type) (G : templateLanguage.{u}.Structure M), Finite M ∧ IsTemplateCompatible G ∧
      ∃ x : Fin n → M, RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) x := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep c.1
  have hl : t.IsStronglyCodedLegal := by
    have := c.2
    rw [← ht] at this
    exact this
  refine ⟨Fin n, t.faceClassRealization.toStructure, inferInstance,
    hl.isWellFormed_faceClassRealization.isTemplateCompatible, id, Function.injective_id,
    t.toClass, by simp [StageType.faceClassRealization], ?_⟩
  change t.toClass.globalClass = c.1
  rw [TemplateClass.globalClass_omega_one]
  exact ht

/-! ### The invariance diagram `ID[L]` -/

section Diagram

open Correspondence

variable {n k : ℕ}

/-- **A negative pair of `ID[L]`**: `(Q_c(x), ¬r(x_i)) ∈ ID[L]` exactly when not `c.Holds r i`.
Correspondence with the printed definitions. -/
theorem mk_not_atom_mem_templateDiagramPairs_iff (hn : 0 < n) (c : LegalClass.{u} n)
    (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) :
    (⟨n, TemplateSymbol.invariant c hn, (atom (L := templateLanguage) r i).not⟩ :
      DiagramPair templateLanguage.{u}) ∈ templateDiagramPairs ↔ ¬ c.1.Holds r i := by
  constructor
  · rintro ⟨n', hn', c', k', r', i', ⟨_, he⟩ | ⟨hh, he⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp he
      have he₂ := (Prod.mk.inj (eq_of_heq he)).2
      simp only [atom, Relations.formula, Relations.boundedFormula, Formula.not,
        BoundedFormula.not] at he₂
      cases he₂
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp he
      obtain ⟨he₁, he₂⟩ := Prod.mk.inj (eq_of_heq he)
      have he₃ : atom (L := templateLanguage) r i = atom (L := templateLanguage) r' i' := by
        simp only [Formula.not, BoundedFormula.not] at he₂
        injection he₂
      have hk : k = k' := by
        simp only [atom, Relations.formula, Relations.boundedFormula] at he₃
        injection he₃
      subst hk
      obtain ⟨rfl, rfl⟩ := atom_templateLanguage_injective he₃
      obtain rfl : c = c' := by injection he₁
      exact hh
  · exact fun h ↦ ⟨n, hn, c, k, r, i, .inr ⟨h, rfl⟩⟩

/-- **The template diagram `ID[L]` is an invariance diagram** ([AFK26, Definitions 2.4 and 4.18]):
its pairs have an invariant and a literal (clause (a)), exactly one of `(Q_c(x), r(x_i))` and
`(Q_c(x), ¬r(x_i))` is a pair (clause (b)), and every invariant is realized in a finite compatible
structure, its chart (clause (c), `exists_isTemplateCompatible_relMap_invariant`).
Correspondence with the printed definitions. -/
def templateDiagram : InvarianceDiagram templateSignature.{u} where
  pairs := templateDiagramPairs
  mem_pairs := by
    rintro π ⟨n, hn, c, k, r, i, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · exact ⟨trivial, .inl (BoundedFormula.IsAtomic.rel _ _)⟩
    · exact ⟨trivial, .inr ⟨_, BoundedFormula.IsAtomic.rel _ _, rfl⟩⟩
  exactlyOne n k P R j hP := by
    rcases P with _ | ⟨c, hn⟩ | _ <;> try exact hP.elim
    have h₁ := mk_atom_mem_templateDiagramPairs_iff hn c R j
    have h₂ := mk_not_atom_mem_templateDiagramPairs_iff hn c R j
    by_cases h : c.1.Holds R j
    · exact .inl ⟨h₁.mpr h, fun h' ↦ h₂.mp h' h⟩
    · exact .inr ⟨h₂.mpr h, fun h' ↦ h (h₁.mp h')⟩
  realized n Q hQ := by
    rcases Q with _ | ⟨c, hn⟩ | _ <;> try exact hQ.elim
    obtain ⟨M, G, hM, hG, x, hx⟩ := exists_isTemplateCompatible_relMap_invariant hn c
    exact ⟨M, G, Finite.to_countable, hG.1, ⟨x, hx⟩, hG.2⟩

/-- **Compatibility with the invariance diagram `ID[L]` is `IsTemplateCompatible`.**
Correspondence with the printed definitions. -/
theorem isCompatible_templateDiagram_iff {M : Type v} (G : templateLanguage.{u}.Structure M) :
    templateDiagram.IsCompatible M ↔ IsTemplateCompatible G :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end Diagram

end

end VaughtConjecture

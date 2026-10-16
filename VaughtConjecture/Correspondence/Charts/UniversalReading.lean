/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.UniversalModel

/-!
# The universal chart model: reading charts in a structure

Native construction throughout.  The statements are in
`VaughtConjecture.Correspondence.Charts.UniversalModel`.

* **Closed range** (`chartEmbeddingClosedRangeTarget`): a chart `C` satisfies `P_n` of its
  enumeration (the face of its template along the identity is the template,
  `StageType.restrictFace_refl`), and an embedding preserves it; so the range of a chart embedding
  is closed.  Closedness is derived from the preservation of this one relation, not assumed.
* **The invariant of the image tuple** (`relMap_invariant_embedding_iff`): for an embedding
  `e : D ↪ G` of a chart presented by `t` with enumeration `eD` into **any** structure `G`, the
  invariants holding of `eD ; e` in `G` are exactly `Q_{[t]}`, the class of `t` at `ω₁`.
* **Exact realization from an embedding** (`realizesChartExactly_of_embedding`): hence the decoder
  reads `eD ; e` as the class of `t` at the block stage, for `β < ω₁`, with no compatibility of `G`
  used; `exactRealizationOfEmbeddingTarget` follows.
* **Independence of the presentation** (`realizesChartExactly_iff`): exact realization along `e`
  is equivalent to the reading at any single presentation; and a presentation by `t` is a
  presentation by every cell renaming of `t` (`isChartPresentation_renameCells_iff`), which has
  the same class.
* **The chart reading of a consistent realization** (`classReadingChartEmbeddingTarget`): for an
  exactly consistent realization `R` at `λ_β`, a tuple `x` carries an embedding of the chart
  presented by `t` with point map `x` on the enumeration exactly when the class of the type of `x`
  is the class of `t`.  Relations at a sequence of places of `x` are read through the face of the
  type of `x` (`relMap_classReading_comp_iff`), and the chart relations of renamings agree
  (`StageType.holds_iff_of_isCellRenaming`).
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal StageType

noncomputable section

/-! ### Holds, along the identity and under renaming -/

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **The chart relations of a renaming are those of the type.**  Native construction. -/
theorem holds_iff_of_isCellRenaming {s t : StageType.{u} α n} (h : s.IsCellRenaming t)
    (r : TemplateSymbol.{u} k) (ys : Fin k → Fin n) : t.Holds r ys ↔ s.Holds r ys :=
  exists_congr fun hy ↦ exists_restrictFace_iff_of_isCellRenaming h ⟨ys, hy⟩ r.Reads

/-- **The invariant of the identity tuple in the chart of `t`** is the class of `t` at `ω₁`.
Native construction. -/
theorem holds_invariant_id_iff (t : StageType.{u} α n) (hn : 0 < n) (c : LegalClass.{u} n) :
    t.Holds (TemplateSymbol.invariant c hn) id ↔ t.globalClass = c.1 := by
  constructor
  · rintro ⟨_, s, hs, hr⟩
    have hst : s = t := Option.some.inj (hs.symm.trans (restrictFace_refl t))
    subst hst
    exact hr
  · intro h
    exact ⟨Function.injective_id, t, restrictFace_refl t, h⟩

end StageType

/-! ### Presentations -/

section Presentation

variable {β : Ordinal.{u}} {P : Type w} {D : templateLanguage.{u}.Structure P} {n : ℕ}
  {t : StageType.{u} (blockStage β) n} {eD : Fin n ≃ P}

/-- The template of a presentation has a strongly coded legal class at `ω₁`, for `β < ω₁`.
Native construction. -/
theorem IsChartPresentation.isStronglyCodedLegal_globalClass (hβ : β < ω₁)
    (hp : IsChartPresentation β D t eD) : t.globalClass.IsStronglyCodedLegal :=
  (TemplateClass.isStronglyCodedLegal_reduce_iff _ t.toClass).mpr
    ((isLegalTemplate_omega_one_iff_of_le (blockStage_lt_omega_one hβ).le).mp hp.2.1)

/-- **A presentation by `t` is a presentation by every cell renaming of `t`**, for `β < ω₁`.
Native construction. -/
theorem isChartPresentation_renameCells_iff (hβ : β < ω₁) {k : ℕ} (π : Fin k ≃ Fin t.card) :
    IsChartPresentation β D (t.renameCells π) eD ↔ IsChartPresentation β D t eD := by
  have hle := (blockStage_lt_omega_one hβ).le
  have hren : t.IsCellRenaming (t.renameCells π) := ⟨_, π, rfl⟩
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · rw [isLegalTemplate_omega_one_iff_of_le hle, isLegalTemplate_omega_one_iff_of_le hle,
      isStronglyCodedLegal_renameCells_iff]
  · exact ⟨fun h _ r xs ↦ (h r xs).trans (holds_iff_of_isCellRenaming hren r xs),
      fun h _ r xs ↦ (h r xs).trans (holds_iff_of_isCellRenaming hren r xs).symm⟩

end Presentation

/-! ### The invariant of the image of a chart -/

section Image

variable {β : Ordinal.{u}} {M : Type v} {P : Type w} [G : templateLanguage.{u}.Structure M]
  [D : templateLanguage.{u}.Structure P] {n : ℕ} {t : StageType.{u} (blockStage β) n}
  {eD : Fin n ≃ P}

/-- **The invariants of the image tuple of a chart** in any structure: along an embedding
`e : D ↪ G`, `Q_c` holds of `eD ; e` exactly when `c` is the class of `t` at `ω₁`.
Native construction. -/
theorem relMap_invariant_embedding_iff (hp : IsChartPresentation β D t eD)
    (e : P ↪[templateLanguage.{u}] M) (c : LegalClass.{u} n) :
    RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hp.1)
        (eD.toEmbedding.trans e.toEmbedding) ↔
      t.globalClass = c.1 :=
  ((e.map_rel _ (eD ∘ id)).trans (hp.2.2 _ id)).trans (t.holds_invariant_id_iff hp.1 c)

/-- **Exact realization from an embedding**: for `β < ω₁`, every embedding of a chart into any
structure realizes it exactly; no compatibility of `G` is used.  Native construction. -/
theorem realizesChartExactly_of_embedding (hβ : β < ω₁) (e : P ↪[templateLanguage.{u}] M) :
    RealizesChartExactly β G D e := by
  intro n t eD hp
  have hle := (blockStage_lt_omega_one hβ).le
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hp.1; omega⟩
  rw [decode_eval_succ]
  split_ifs with h
  · have hc := (relMap_invariant_embedding_iff hp e h.choose).mp h.choose_spec
    rw [← hc, ← TemplateClass.globalClass_toClass, TemplateClass.reduce_globalClass _ hle]
  · exact absurd ⟨⟨t.globalClass, hp.isStronglyCodedLegal_globalClass hβ⟩,
      (relMap_invariant_embedding_iff hp e _).mpr rfl⟩ h

/-- **Exact realization does not depend on the presentation**: along an embedding, it is
equivalent to the reading at any single presentation (both hold, for `β < ω₁`).
Native construction. -/
theorem realizesChartExactly_iff (hβ : β < ω₁) (hp : IsChartPresentation β D t eD)
    (e : P ↪[templateLanguage.{u}] M) :
    RealizesChartExactly β G D e ↔
      (decode β G).eval (eD.toEmbedding.trans e.toEmbedding) = some t.toClass :=
  ⟨fun h ↦ h n t eD hp, fun _ ↦ realizesChartExactly_of_embedding hβ e⟩

end Image

/-- **`ExactRealizationOfEmbeddingTarget β M` holds**, without using compatibility
(`realizesChartExactly_of_embedding`).  Native construction. -/
theorem exactRealizationOfEmbeddingTarget (β : Ordinal.{u}) (M : Type v) :
    ExactRealizationOfEmbeddingTarget.{u, v, w} β M :=
  fun hβ G _ _ D _ e ↦ realizesChartExactly_of_embedding (G := G) (D := D) hβ e

/-! ### Closed range -/

/-- **`ChartEmbeddingClosedRangeTarget β` holds**: a chart satisfies `P_n` of its enumeration,
and an embedding preserves it.  Native construction. -/
theorem chartEmbeddingClosedRangeTarget (β : Ordinal.{u}) :
    ChartEmbeddingClosedRangeTarget.{u, w} β := by
  intro N C P D hC ι
  obtain ⟨n, t, e, hn, -, hte⟩ := hC
  have hCP : RelMap (L := templateLanguage.{u}) (self := C) (TemplateSymbol.closed hn) (e ∘ id) :=
    (hte (TemplateSymbol.closed hn) id).mpr ⟨Function.injective_id, t, restrictFace_refl t, trivial⟩
  refine Or.inr ⟨n, hn, ι ∘ e, (ι.map_rel _ (e ∘ id)).mpr hCP, ?_⟩
  rw [Set.range_comp, e.range_eq_univ, Set.image_univ]
  rfl

/-! ### The chart reading of a consistent realization -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Relations at a sequence of places of a typed tuple, in the class-reading structure**: for
an exactly consistent realization with `R.eval x = some s`, a symbol holds of `x ∘ ys` exactly
when it holds of `ys` in the chart of `s`.  Native construction. -/
theorem relMap_classReading_comp_iff (hR : R.IsConsistent) {n : ℕ} {x : Fin n ↪ M}
    {s : StageType.{u} α n} (hs : R.eval x = some s) {k : ℕ} (r : TemplateSymbol.{u} k)
    (ys : Fin k → Fin n) :
    RelMap (L := templateLanguage.{u}) (self := R.classReading.toStructure) r (x ∘ ys) ↔
      s.Holds r ys := by
  constructor
  · rintro ⟨hinj, c, hc, hr⟩
    have hys : Function.Injective ys := hinj.of_comp
    change (R.eval ((⟨ys, hys⟩ : Fin k ↪ Fin n).trans x)).map StageType.toClass = some c at hc
    rw [hR x s _ hs] at hc
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact ⟨hys, s', hs', hr⟩
  · rintro ⟨hys, s', hs', hr⟩
    refine ⟨x.injective.comp hys, s'.toClass, ?_, hr⟩
    change (R.eval ((⟨ys, hys⟩ : Fin k ↪ Fin n).trans x)).map StageType.toClass =
      some s'.toClass
    rw [hR x s _ hs, hs', Option.map_some]

end Realization

/-- **`ClassReadingChartEmbeddingTarget β M` holds**: for an exactly consistent realization at
`λ_β`, `β < ω₁`, the point maps of the embeddings of a chart presented by `t` into the
class-reading structure are the tuples whose class is the class of `t`.  Native construction. -/
theorem classReadingChartEmbeddingTarget (β : Ordinal.{u}) (M : Type v) :
    ClassReadingChartEmbeddingTarget.{u, v, w} β M := by
  intro hβ R hR P D n t eD hp x
  let G : templateLanguage.{u}.Structure M := R.classReading.toStructure
  have hle := (blockStage_lt_omega_one hβ).le
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨hinj, c, hc, hr⟩ := (relMap_invariant_embedding_iff hp e
      ⟨t.globalClass, hp.isStronglyCodedLegal_globalClass hβ⟩).mpr rfl
    rw [show c = t.toClass from
      TemplateClass.globalClass_injective (isSuccPrelimit_blockStage β) hle hr] at hc
    exact hc
  · intro hx
    obtain ⟨s, hs, hst⟩ := Option.map_eq_some_iff.mp hx
    have hren : s.IsCellRenaming t := toClass_eq_toClass_iff.mp hst
    refine ⟨{ toEmbedding := eD.symm.toEmbedding.trans x
              map_fun' := fun g ↦ Empty.elim g
              map_rel' := fun r xs ↦ ?_ }, ?_⟩
    · have hxs : eD ∘ (eD.symm ∘ xs) = xs := by
        rw [← Function.comp_assoc, Equiv.self_comp_symm, Function.id_comp]
      calc RelMap (L := templateLanguage.{u}) r (x ∘ (eD.symm ∘ xs)) ↔ s.Holds r (eD.symm ∘ xs) :=
            Realization.relMap_classReading_comp_iff hR hs r _
        _ ↔ t.Holds r (eD.symm ∘ xs) := (holds_iff_of_isCellRenaming hren r _).symm
        _ ↔ RelMap (L := templateLanguage.{u}) r (eD ∘ (eD.symm ∘ xs)) := (hp.2.2 r _).symm
        _ ↔ RelMap (L := templateLanguage.{u}) r xs := by rw [hxs]
    · exact Function.Embedding.ext fun i ↦ congrArg x (eD.symm_apply_apply i)

end

end VaughtConjecture

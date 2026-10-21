/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.UniversalConstruction
import VaughtConjecture.Correspondence.Charts.UniversalReading
import VaughtConjecture.Correspondence.Density.ReceivingIn

/-!
# The universal chart model ([AFK26, Lemma 4.33])

Native construction throughout.  Write `λ_β = blockStage β`.

**The chart-reading theorem** (`stronglyCodedUniversalReadingTarget`).  For `β < ω₁` on a
nonempty carrier, the class-reading structure `G = R.classReading.toStructure` of a realization
`R` at `λ_β` in the strongly coded receiving class with exact receiving of every strongly coded
legal donor is in `K_β[L]` and satisfies the chart clauses:

* membership, as for the successor reading (`successorReadingTarget`), at `β`: the class reading
  is well formed and has donor density, and B.T5/B.T6 (`decoderRoundTrip`,
  `mem_templateStageClass_iff`) give membership;
* over a positive root: an embedding `e : C ↪ G` reads, at the enumeration of `C`, a tuple `x`
  whose type `s` is a renaming of the template of `C` (`classReadingChartEmbeddingTarget`); the
  chart embedding `ι : C ↪ D` reads a face `f` of the template of `D` that is a renaming of the
  template of `C` (`exists_restrictFace_of_chartEmbedding`); the template of `D` is renamed so
  that its face along `f` is `s` literally (`StageType.exists_restrictFace_renameCells`), exact
  receiving extends `x` along `f` to a cover of the renamed template, and the reading of chart
  embeddings turns it into `e' : D ↪ G` with `ι ; e' = e` (`exists_embedsAlong_extend`);
* over the empty root: the empty tuple has the type on no points (covering and consistency), and
  exact receiving realizes the template of every chart over it;
* exact realization along every embedding (`realizesChartExactly_of_embedding`).

**Universality implies density** (`universalityDensityTarget`).  For `β < ω₁`, a compatible
structure fixed by `τ_β` with the positive-root clause satisfies `D[α]` for **every** `α < λ_β`,
`α = 0` included.  For a root `Q_t(x)` and a donor `u` of **any** rank with
`(Q_u(x y), Q_t(x)) ∈ ID[L]`:

* the root class is fixed by `τ_β` (`IsTemplateCompatible.project_eq_of_relMap_invariant`), so
  the reduction `T` to `λ_β` of a representative of `t` has class `t` at `ω₁`, and `x` carries an
  embedding of the chart of `T` (compatibility, `IsTemplateCompatible.relMap_comp_iff`, and
  `StageType.globalClass_holds_iff`);
* **the arbitrary-rank donor passage** (`LegalClass.truncEquiv_project_of_le`, proved): the
  projection `τ_β(u)` has the same raw truncation at every `α ≤ λ_β` as `u`, since
  `trunc_α ∘ trunc_{λ_β} = trunc_α` on labels (`Label.reduce_reduce_of_le`) and projection keeps
  the scheme; the reduction `U` to `λ_β` of a representative of `u` has class `τ_β(u)` at `ω₁`
  and its face along the first `n` places is a renaming of `T`;
* the positive-root clause, for the charts of `T` and `U` on `ULift (Fin _)`
  (`StageType.liftChart`, in the universe of the clause), extends `x` to `x y` with
  `G ⊨ Q_{τ_β(u)}(x y)` (`exists_append_of_extendsOverChartRoots`).

**The universal model theorem** (`universalChartModelTarget`): for `β < ω₁` and a countably
infinite carrier `M`, one structure `G ∈ K_β[L]` on `M`, chosen before any request, with clauses
(a) and (b); `G` is the class-reading structure of the positional realization of
`stronglyCodedUniversalRealizationTarget`.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal StageType

noncomputable section

/-! ### Faces of chart embeddings -/

section Faces

variable {β : Ordinal.{u}} {N : Type w} {P : Type w} [C : templateLanguage.{u}.Structure N]
  [D : templateLanguage.{u}.Structure P]

/-- **The face read by a chart embedding**: for presentations of `C` by `tC` and of `D` by `tD`,
an embedding `ι : C ↪ D` reads a face of `tD`, along the map of places of `ι`, that is a cell
renaming of `tC`.  Native construction. -/
theorem exists_restrictFace_of_chartEmbedding (hβ : β < ω₁) {nC nD : ℕ}
    {tC : StageType.{u} (blockStage β) nC} {tD : StageType.{u} (blockStage β) nD}
    {eC : Fin nC ≃ N} {eD : Fin nD ≃ P} (hpC : IsChartPresentation β C tC eC)
    (hpD : IsChartPresentation β D tD eD) (ι : N ↪[templateLanguage.{u}] P) :
    ∃ (f : Fin nC ↪ Fin nD) (s' : StageType.{u} (blockStage β) nC),
      (∀ i, eD (f i) = ι.toEmbedding (eC i)) ∧ restrictFace f tD = some s' ∧
        s'.IsCellRenaming tC := by
  have hle := (blockStage_lt_omega_one hβ).le
  have hcl := hpC.isStronglyCodedLegal_globalClass hβ
  have h1 : RelMap (L := templateLanguage.{u})
      (TemplateSymbol.invariant ⟨tC.globalClass, hcl⟩ hpC.1) (eC ∘ id) :=
    (hpC.2.2 _ id).mpr ((tC.holds_invariant_id_iff hpC.1 _).mpr rfl)
  have h2 := (ι.map_rel _ _).mpr h1
  have h3 : ⇑ι ∘ (⇑eC ∘ id) = ⇑eD ∘ (⇑eD.symm ∘ ⇑ι ∘ ⇑eC) := by
    funext i
    simp
  rw [h3, hpD.2.2] at h2
  obtain ⟨hinj, s', hs', hr⟩ := h2
  exact ⟨⟨_, hinj⟩, s', fun i ↦ by simp; rfl, hs', (globalClass_eq_iff hle).mp hr⟩

end Faces

/-! ### Extending a cover to an embedding of a chart -/

section Extend

variable {β : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage β) M}

/-- **A cover extends to an embedding of a chart**: for an exactly consistent realization with
exact receiving of the strongly coded legal donors, a tuple `x` of type `s` and a chart presented
by `tD`, whose face along `f` is a renaming of `s`, there is a tuple `v` extending `x` along `f`
that carries an embedding of the chart into the class-reading structure.  Native construction. -/
theorem exists_embedsAlong_extend (hβ : β < ω₁) (hR : R.IsConsistent)
    (hex : R.ExactReceivingWithin
      fun m ↦ {D : StageType.{u} (blockStage β) m | D.IsStronglyCodedLegal})
    {P : Type w} {D : templateLanguage.{u}.Structure P} {nD : ℕ}
    {tD : StageType.{u} (blockStage β) nD} {eD : Fin nD ≃ P} (hpD : IsChartPresentation β D tD eD)
    {k : ℕ} {x : Fin k ↪ M} {s : StageType.{u} (blockStage β) k} (hs : R.eval x = some s)
    {f : Fin k ↪ Fin nD} {s' : StageType.{u} (blockStage β) k} (hf : restrictFace f tD = some s')
    (hss : s'.IsCellRenaming s) :
    ∃ v : Fin nD ↪ M, f.trans v = x ∧ EmbedsAlong R.classReading.toStructure D eD v := by
  have hle := (blockStage_lt_omega_one hβ).le
  obtain ⟨π, hπ⟩ := tD.exists_restrictFace_renameCells f hf hss
  have hsc : (tD.renameCells π).IsStronglyCodedLegal :=
    (tD.isStronglyCodedLegal_renameCells_iff π).mpr
      ((isLegalTemplate_omega_one_iff_of_le hle).mp hpD.2.1)
  obtain ⟨v, hv, hvf⟩ := hex s x (Realization.covers_of_eval x hs) (tD.renameCells π) f hsc hπ
  refine ⟨⟨v, hv.injective⟩, Function.Embedding.ext fun i ↦ congrFun hvf i, ?_⟩
  refine (classReadingChartEmbeddingTarget β M hβ R hR P D nD tD eD hpD _).mpr ?_
  rw [Realization.classReading_eval, hv.eval_eq, Option.map_some, toClass_renameCells]

end Extend

/-! ### The chart-reading theorem -/

/-- **The chart-reading theorem** (`StronglyCodedUniversalReadingTarget β M` holds): the
class-reading structure of a strongly coded receiving realization at `λ_β` with exact receiving
of every strongly coded legal donor is in `K_β[L]`, every chart embeds into it, and every chart
embedding extends every embedding of its root, with a commuting square and exact realization,
over positive roots and over the empty root.  `Nonempty M` is used for membership only.
Native construction. -/
theorem stronglyCodedUniversalReadingTarget (β : Ordinal.{u}) (M : Type v) :
    StronglyCodedUniversalReadingTarget.{u, v, w} β M := by
  intro hβ hM R hR hex
  let G : templateLanguage.{u}.Structure M := R.classReading.toStructure
  -- the empty root
  have hempty : ExtendsOverEmptyRoot.{u, v, w} β R.classReading.toStructure := by
    intro P D hD
    obtain ⟨nD, tD, eD, hpD⟩ := hD
    let x₀ : Fin 0 ↪ M := Function.Embedding.ofIsEmpty
    obtain ⟨m, u', f', hf'u, hu'⟩ := hR.isCovering x₀
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hu'
    have hs0 : R.eval x₀ = restrictFace f' q := by
      rw [← hf'u]
      exact hR.isConsistent u' q f' hq
    obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp (q.isSome_restrictFace_of_zero f')
    rw [hp₀] at hs0
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp
      (tD.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin nD))
    obtain ⟨v, -, e', -⟩ := exists_embedsAlong_extend hβ hR.isConsistent hex hpD hs0 hs'
      (by rw [eq_of_zero s' p₀]; exact IsCellRenaming.refl p₀)
    exact ⟨e', realizesChartExactly_of_embedding hβ e'⟩
  refine ⟨?_, fun P D hD ↦ ?_, ?_, hempty⟩
  · -- membership in `K_β[L]`
    have hwf : R.classReading.IsWellFormed :=
      ⟨hR.isConsistent.classReading, hR.isCovering.classReading,
        Realization.classReading_hasLegalTypes fun _ t p hp ↦
          And.intro (hR.hasLegalTypes t p hp) (hR.isStronglyCoded t p hp)⟩
    have hdd : R.classReading.HasDonorDensity :=
      ((Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff hR.isConsistent
        (isSuccPrelimit_blockStage _)).mpr hR.receiving).hasDonorDensity_classReading
    obtain ⟨hcomp, hfix, hdec⟩ := (decoderRoundTrip hβ).2 _ hwf
    exact (mem_templateStageClass_iff hβ _).mpr ⟨hM, hcomp, hfix, by rw [hdec]; exact hdd⟩
  · -- clause (a), from the empty root
    obtain ⟨e', -⟩ := hempty P D hD
    exact ⟨e'⟩
  · -- positive roots
    intro N C P D hC hD ι e
    obtain ⟨nC, tC, eC, hpC⟩ := hC
    obtain ⟨nD, tD, eD, hpD⟩ := hD
    let x : Fin nC ↪ M := eC.toEmbedding.trans e.toEmbedding
    have hx : R.classReading.eval x = some tC.toClass :=
      (classReadingChartEmbeddingTarget β M hβ R hR.isConsistent N C nC tC eC hpC x).mp ⟨e, rfl⟩
    obtain ⟨s, hs, hst⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨f, s', hfι, hf, hs'⟩ := exists_restrictFace_of_chartEmbedding hβ hpC hpD ι
    have hss : s'.IsCellRenaming s :=
      toClass_eq_toClass_iff.mp ((toClass_eq_toClass_iff.mpr hs').trans hst.symm)
    obtain ⟨v, hfv, e', he'⟩ :=
      exists_embedsAlong_extend hβ hR.isConsistent hex hpD hs hf hss
    refine ⟨e', Function.Embedding.ext fun p ↦ ?_, realizesChartExactly_of_embedding hβ e'⟩
    obtain ⟨i, rfl⟩ := eC.surjective p
    change e'.toEmbedding (ι.toEmbedding (eC i)) = e.toEmbedding (eC i)
    rw [← hfι i]
    exact (DFunLike.congr_fun he' (f i)).trans (DFunLike.congr_fun hfv i)

/-! ### Charts on `ULift (Fin n)` -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- **The chart of a stage type on `ULift (Fin n)`**: the relations `Holds`, read through
`ULift.down`; it lets a chart live in any universe.  Native construction. -/
@[instance_reducible] def liftChart (T : StageType.{u} α n) :
    templateLanguage.{u}.Structure (ULift.{w} (Fin n)) where
  funMap f := Empty.elim f
  RelMap r xs := T.Holds r (ULift.down ∘ xs)

/-- The chart of a legal template on `ULift (Fin n)` is a chart.  Native construction. -/
theorem isTemplateChart_liftChart {β : Ordinal.{u}} {T : StageType.{u} (blockStage β) n}
    (hn : 0 < n) (hT : T.IsLegalTemplate ω₁) : IsTemplateChart β (T.liftChart.{u, w}) :=
  ⟨n, T, Equiv.ulift.symm, hn, hT, fun _ _ ↦ Iff.rfl⟩

/-- **The embedding of charts on `ULift` along a face up to renaming.**  Native construction. -/
def liftChartEmbedding {T : StageType.{u} α m} {U : StageType.{u} α n} {s' : StageType.{u} α m}
    {f : Fin m ↪ Fin n} (hf : restrictFace f U = some s') (hss : T.IsCellRenaming s') :
    @Language.Embedding templateLanguage.{u} (ULift.{w} (Fin m)) (ULift.{w} (Fin n))
      T.liftChart U.liftChart :=
  letI := T.liftChart.{u, w}
  letI := U.liftChart.{u, w}
  { toEmbedding := Equiv.ulift.toEmbedding.trans (f.trans Equiv.ulift.symm.toEmbedding)
    map_fun' := fun g ↦ Empty.elim g
    map_rel' := fun r xs ↦ U.holds_comp_iff hf hss r (ULift.down ∘ xs) }

/-- **The chart relations of the class at `ω₁` of a stage type are those of the stage type.**
Native construction. -/
theorem globalClass_holds_iff (T : StageType.{u} α n) {k : ℕ} (r : TemplateSymbol.{u} k)
    (i : Fin k → Fin n) : T.globalClass.Holds r i ↔ T.Holds r i := by
  refine exists_congr fun h ↦ ?_
  rw [StageType.globalClass, TemplateClass.restrictFace_toClass, StageType.restrictFace_reduce,
    Option.map_map]
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨s', hs', hr⟩
  · rintro ⟨s', hs', hr⟩
    exact ⟨_, by rw [hs', Option.map_some]; rfl, hr⟩

end StageType

/-! ### Universality implies density -/

/-- **The arbitrary-rank donor passage**: the projection `τ_β(u)` of a legal class `u` of any rank
has the raw truncation of `u` at every `α ≤ λ_β`.  Native construction; correspondence with the
printed truncation through `TemplateClass.TruncEquiv`. -/
theorem LegalClass.truncEquiv_project_of_le {β α : Ordinal.{u}} (hβ : β < ω₁)
    (hα : α ≤ blockStage β) {n : ℕ} (u : LegalClass.{u} n) :
    (u.project β).1.TruncEquiv α u.1 := by
  have hle := (blockStage_lt_omega_one hβ).le
  obtain ⟨v, hv⟩ := Quotient.exists_rep u.1
  refine ⟨v.project (isSuccPrelimit_blockStage β), v, ?_, hv, rfl, fun i j hij ↦ ?_⟩
  · rw [LegalClass.coe_project, ← hv]
    rfl
  · change Label.reduce α _ = Label.reduce α _
    rw [label_project v (isSuccPrelimit_blockStage β) hle i, Label.reduce_reduce_of_le hα]
    exact congrArg (fun d ↦ Label.reduce α (v.label d)) (Fin.ext hij)

section Density

variable {β : Ordinal.{u}} {M : Type v} {G : templateLanguage.{u}.Structure M}

/-- **The positive-root clause along the first `n` places**: if `x` carries the chart relations
of `T` in `G`, and the face of `U` along the first `n` places is a renaming of `T`, then `x`
extends to `Fin.append x y` carrying the chart relations of `U`.  The charts are taken on
`ULift (Fin _)` in the universe of the clause.  Native construction. -/
theorem exists_append_of_extendsOverChartRoots (hext : ExtendsOverChartRoots.{u, v, w} β G)
    {n m : ℕ} (hn : 0 < n) {T : StageType.{u} (blockStage β) n}
    {U : StageType.{u} (blockStage β) (n + m)} (hT : T.IsLegalTemplate ω₁)
    (hU : U.IsLegalTemplate ω₁) {s' : StageType.{u} (blockStage β) n}
    (hf : restrictFace (Fin.castAddEmb m) U = some s') (hss : T.IsCellRenaming s')
    {x : Fin n → M} (hxinj : Function.Injective x)
    (hx : ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n),
      RelMap (L := templateLanguage.{u}) (self := G) r (x ∘ xs) ↔ T.Holds r xs) :
    ∃ y : Fin m → M, ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (zs : Fin k → Fin (n + m)),
      RelMap (L := templateLanguage.{u}) (self := G) r (Fin.append x y ∘ zs) ↔ U.Holds r zs := by
  let _ : templateLanguage.{u}.Structure (ULift.{w} (Fin n)) := T.liftChart
  let _ : templateLanguage.{u}.Structure (ULift.{w} (Fin (n + m))) := U.liftChart
  let e : @Language.Embedding templateLanguage.{u} (ULift.{w} (Fin n)) M T.liftChart G :=
    { toEmbedding := ⟨x ∘ ULift.down, hxinj.comp ULift.down_injective⟩
      map_fun' := fun g ↦ Empty.elim g
      map_rel' := fun r xs ↦ hx r (ULift.down ∘ xs) }
  obtain ⟨e', hcomm, -⟩ := hext (ULift.{w} (Fin n)) T.liftChart (ULift.{w} (Fin (n + m)))
    U.liftChart (isTemplateChart_liftChart hn hT)
    (isTemplateChart_liftChart (Nat.lt_add_right m hn) hU) (liftChartEmbedding hf hss) e
  let z : Fin (n + m) → M := fun j ↦ e'.toEmbedding (ULift.up j)
  have hz : Fin.append x (fun j ↦ z (Fin.natAdd n j)) = z := by
    funext j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · rw [Fin.append_left]
      exact (DFunLike.congr_fun hcomm (ULift.up i)).symm
    · rw [Fin.append_right]
  refine ⟨fun j ↦ z (Fin.natAdd n j), fun r zs ↦ ?_⟩
  rw [hz]
  exact @Language.Embedding.map_rel' templateLanguage.{u} _ _ U.liftChart G e' _ r
    (ULift.up ∘ zs)

variable (β M)

/-- **Universality implies density** (`UniversalityDensityTarget β M` holds): for `β < ω₁`, a
compatible structure fixed by `τ_β` with the positive-root clause satisfies `D[α]` for every
`α < λ_β`, `α = 0` included; the donor of any rank is replaced by its projection `τ_β(u)`, which
has the same truncation (`LegalClass.truncEquiv_project_of_le`).  Correspondence with the printed
definitions. -/
theorem universalityDensityTarget : UniversalityDensityTarget.{u, v, w} β M := by
  intro hβ G hG hfix hext α hα
  have hle := (blockStage_lt_omega_one hβ).le
  have hlam := isSuccPrelimit_blockStage β
  rw [satisfiesDensityAt_iff]
  intro n m hn t u hu x hx
  obtain ⟨w₀, hw₀⟩ := Quotient.exists_rep t.1
  obtain ⟨v, hv⟩ := Quotient.exists_rep u.1
  -- the root: its class is fixed by `τ_β`
  have htfix : t.1.project hlam = t.1 :=
    congrArg Subtype.val (hG.project_eq_of_relMap_invariant hfix hx)
  let T : StageType.{u} (blockStage β) n := w₀.reduce hlam
  let U : StageType.{u} (blockStage β) (n + m) := v.reduce hlam
  have hTg : T.globalClass = t.1 := by
    rw [← htfix, ← hw₀]
    rfl
  have hUg : U.globalClass = (u.project β).1 := by
    rw [LegalClass.coe_project, ← hv]
    rfl
  have hT : T.IsLegalTemplate ω₁ := by
    refine (isLegalTemplate_omega_one_iff_of_le hle).mpr ?_
    have h := t.2
    rw [← hw₀] at h
    exact h
  have hU : U.IsLegalTemplate ω₁ := by
    refine (isLegalTemplate_omega_one_iff_of_le hle).mpr ?_
    have h := u.2
    rw [← hv] at h
    exact h
  -- the face of the donor along the first `n` places
  obtain ⟨hinj, s, hs, hst⟩ := hu
  rw [← hv, TemplateClass.restrictFace_toClass] at hs
  obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hfU : restrictFace (Fin.castAddEmb m) U = some (s₀.reduce hlam) := by
    change restrictFace (Fin.castAddEmb m) (v.reduce hlam) = _
    rw [StageType.restrictFace_reduce]
    exact congrArg (Option.map (reduce · hlam)) hs₀
  have hren : w₀.IsCellRenaming s₀ := by
    refine toClass_eq_toClass_iff.mp ?_
    change s₀.toClass = t.1 at hst
    rw [hst]
    exact hw₀
  obtain ⟨k, σ, hσ⟩ := hren
  have hTs : T.IsCellRenaming (s₀.reduce hlam) := ⟨k, σ, by rw [← hσ]; rfl⟩
  -- the root carries the chart of `T`
  have hxT : ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n),
      RelMap (L := templateLanguage.{u}) (self := G) r (x ∘ xs) ↔ T.Holds r xs := by
    intro k r xs
    rw [hG.relMap_comp_iff hx r xs, ← hTg]
    exact T.globalClass_holds_iff r xs
  obtain ⟨y, hy⟩ := exists_append_of_extendsOverChartRoots hext hn hT hU hfU hTs
    (hG.injective_of_relMap_invariant hx) hxT
  refine ⟨y, u.project β, LegalClass.truncEquiv_project_of_le hβ hα.le u, ?_⟩
  exact (hy _ id).mpr ((U.holds_invariant_id_iff (Nat.lt_add_right m hn) _).mpr hUg)

end Density

/-! ### The universal model theorem -/

/-- **The universal model theorem** (`UniversalChartModelTarget β M` holds, [AFK26, Lemma 4.33]):
for `β < ω₁` and a countably infinite carrier `M`, one structure `G ∈ K_β[L]` on `M`, chosen before
any request, into which every chart embeds and over which every chart embedding extends every
embedding of its root, with a commuting square and exact realization, over positive roots and
over the empty root.  `G` is the class-reading structure of the positional realization
(`stronglyCodedUniversalRealizationTarget`), read by `stronglyCodedUniversalReadingTarget`.
Native construction. -/
theorem universalChartModelTarget (β : Ordinal.{u}) (M : Type v) :
    UniversalChartModelTarget.{u, v, w} β M := by
  intro hβ hc hM
  obtain ⟨R, hR, hex⟩ := stronglyCodedUniversalRealizationTarget β M hβ hc hM
  obtain ⟨hmem, ha, hb, he⟩ := stronglyCodedUniversalReadingTarget.{u, v, w} β M hβ
    (Infinite.nonempty M) R hR hex
  exact ⟨_, hmem, ha, hb, he⟩

end

end VaughtConjecture

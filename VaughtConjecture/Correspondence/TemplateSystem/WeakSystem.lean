/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.Conditions
import VaughtConjecture.Correspondence.Density.Structure

/-!
# The weak-system interface of `K[L]`: [AFK26, Theorem 4.23]

Numbering as in the current draft of [AFK26].  `K_β[L]` is `templateStageClass M β`, `τ_β` is
`projectStructure β` on structures and `LegalClass.project β` on legal classes, `ID[L]` is
`templateDiagram` (an `InvarianceDiagram` for `templateSignature`), and `σ[L]` is
`templateSentence`.

The abstract theorem [AFK26, Theorem 2.25] is about a weak system ([AFK26, Definition 2.17]) for
an invariance diagram and a compatible invariant system ([AFK26, Definitions 2.4, 2.6, 2.8]).  This
file proves what the route through that theorem needs from the invariance-diagram side, for
`K[L]`, separately from the four conditions
(`VaughtConjecture.Correspondence.TemplateSystem.Conditions`) and from the spectrum statement
(`VaughtConjecture.Correspondence.TemplateSystem.Theorem436`).

* `TemplateBaseModelsTarget` ([AFK26, Theorem 4.23], second half): on a countable **nonempty**
  carrier, the base of `K[L]` is the class of models of `σ[L]`.  Proved.
* `TemplateInvariantSystemTarget` ([AFK26, Definitions 2.6, 2.8 and 4.16, Lemma 4.19]): the
  projections `τ_β` of the legal classes form an invariant system on `L_b[L]`
  (`templateInvariantSystem`, every field proved: composition, countably many `β`-invariants, not
  every invariant a `β`-invariant, a fixing stage for every invariant) compatible with `ID[L]`
  (`isCompatibleWith_templateInvariantSystem`).  Proved.
* **The projection of a structure** [AFK26, Definition 2.7], for an arbitrary invariant system
  (`Correspondence.InvariantSystem.projection`), is `projectStructure` for the invariant system of
  the legal classes (`templateInvariantSystem_projection`).  Proved.
* `WeakSystemClausesTarget` ([AFK26, Definition 2.17] for `K[L]`, the first half of
  [AFK26, Theorem 4.23]): isomorphism closure, compatibility with `ID[L]`, rank at most `β`,
  `α`-density for `α < β` in the form of [AFK26, Definition 2.10 (c)] (`ProjectedDensityAt`), and
  closure under `τ_α`.  Proved.  The class `K_β[L]` is defined by the axioms `D[δ]`,
  `δ < ω + ω · β` ([AFK26, Definitions 4.20 and 4.21]); the passage from `D[λ_α]` to `α`-density,
  for donors of every rank, is `projectedDensityAt_of_satisfiesDensityAt`, through the lemma that
  raw truncation at a block stage up to renaming determines the projection to it
  (`TemplateClass.project_eq_project_of_truncEquiv`).

**Carriers.**  Members of `K_β[L]` have nonempty carriers by definition; models of `σ[L]` need not
(`realize_templateSentence_of_isEmpty`), so `TemplateBaseModelsTarget` assumes `Nonempty M`.
-/

universe u v w w'

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The base and the models of the sentence -/

/-- **Target: the base is the class of models of `σ[L]`** [AFK26, Theorem 4.23, for `K[L]`]: on a
countable **nonempty** carrier, `B` is in the base exactly when `B ⊨ σ[L]`.  The premise
`Nonempty M` is the convention of [AFK26, §1]: on an empty carrier `σ[L]` holds
(`realize_templateSentence_of_isEmpty`) and the base is empty.  Proved; route:
`realize_templateSentence_iff_exists_lift`, `projectionTarget` to the level `0`,
`baseReduct_projectStructure`.  Correspondence with the printed definitions. -/
def TemplateBaseModelsTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    IsInTemplateBase B ↔ @Sentenceω.Realize _ templateSentence.{u} M B

/-- **The base is the class of models of `σ[L]`** (`TemplateBaseModelsTarget M` for every `M`):
a member of `K_β[L]` projects to `K_0[L]` with the same base reduct (`projectionTarget`,
`baseReduct_projectStructure`), and the models of `σ[L]` on a nonempty carrier are the base
reducts of `K_0[L]` (`realize_templateSentence_iff_exists_lift`).  Correspondence with the
printed definitions. -/
theorem templateBaseModelsTarget (M : Type v) : TemplateBaseModelsTarget.{u} M := by
  intro hc hne B
  have := hne
  rw [realize_templateSentence_iff_exists_lift]
  constructor
  · rintro ⟨β, hβ, G, hG, rfl⟩
    exact ⟨projectStructure 0 G, projectionTarget β 0 M hc hβ zero_le G hG,
      baseReduct_projectStructure G⟩
  · rintro ⟨G, hG, rfl⟩
    exact ⟨0, (Cardinal.isSuccLimit_omega 1).pos, G, hG, rfl⟩

/-! ### The invariants of `L_b[L]` -/

/-- **Every invariant of `L_b[L]` is a symbol `Q_c`**, for a legal class `c` on `n > 0` points.
Correspondence with the printed definitions. -/
theorem templateInvariant_eq {n : ℕ} (Q : templateSignature.{u}.Invariant n) :
    ∃ (c : LegalClass.{u} n) (hn : 0 < n), Q = ⟨TemplateSymbol.invariant c hn, trivial⟩ := by
  obtain ⟨_ | ⟨c, hn⟩ | _, hQ⟩ := Q
  · exact (hQ : False).elim
  · exact ⟨c, hn, rfl⟩
  · exact (hQ : False).elim

/-- **The legal class of an invariant** `Q_c` of `L_b[L]`: `c`.  Correspondence with the printed
definitions. -/
def templateInvariantClass : ∀ {n : ℕ}, templateSignature.{u}.Invariant n → LegalClass.{u} n
  | _, ⟨TemplateSymbol.invariant c _, _⟩ => c
  | _, ⟨TemplateSymbol.closed _, h⟩ => (h : False).elim
  | _, ⟨TemplateSymbol.base _ _ _, h⟩ => (h : False).elim

/-- An invariant is `Q_c` for its class `c`.  Correspondence with the printed definitions. -/
theorem eq_invariant_templateInvariantClass {n : ℕ} (Q : templateSignature.{u}.Invariant n) :
    Q.1 = TemplateSymbol.invariant (templateInvariantClass Q) (TemplateSymbol.pos Q.1) := by
  obtain ⟨c, hn, rfl⟩ := templateInvariant_eq Q
  rfl

/-- The class of `Q_c` is `c`.  Correspondence with the printed definitions. -/
@[simp] theorem templateInvariantClass_mk {n : ℕ} (c : LegalClass.{u} n) (hn : 0 < n)
    (h : templateSignature.{u}.IsInvariant (TemplateSymbol.invariant c hn)) :
    templateInvariantClass ⟨TemplateSymbol.invariant c hn, h⟩ = c :=
  rfl

/-- **Two invariants are equal exactly when their classes are.**  Correspondence with the printed
definitions. -/
theorem templateInvariant_ext_iff {n : ℕ} {Q Q' : templateSignature.{u}.Invariant n} :
    Q = Q' ↔ templateInvariantClass Q = templateInvariantClass Q' := by
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext ?_⟩
  rw [eq_invariant_templateInvariantClass Q, eq_invariant_templateInvariantClass Q', h]

/-- **The projection `τ_β` of an invariant** [AFK26, Definition 4.16]: `τ_β(Q_c) = Q_{τ_β(c)}`.
Correspondence with the printed definitions. -/
noncomputable def templateInvariantProject (β : Ordinal.{u}) {n : ℕ}
    (Q : templateSignature.{u}.Invariant n) : templateSignature.{u}.Invariant n :=
  ⟨TemplateSymbol.invariant ((templateInvariantClass Q).project β) (TemplateSymbol.pos Q.1),
    trivial⟩

/-- The class of `τ_β(Q)` is `τ_β` of the class of `Q`.  Correspondence with the printed
definitions. -/
@[simp] theorem templateInvariantClass_project (β : Ordinal.{u}) {n : ℕ}
    (Q : templateSignature.{u}.Invariant n) :
    templateInvariantClass (templateInvariantProject β Q) = (templateInvariantClass Q).project β :=
  templateInvariantClass_mk _ _ _

/-- `Q` is a `β`-invariant (fixed by `τ_β`) exactly when its class is fixed by `τ_β`.
Correspondence with the printed definitions. -/
theorem templateInvariantProject_eq_self_iff (β : Ordinal.{u}) {n : ℕ}
    (Q : templateSignature.{u}.Invariant n) :
    templateInvariantProject β Q = Q ↔
      (templateInvariantClass Q).project β = templateInvariantClass Q := by
  rw [templateInvariant_ext_iff, templateInvariantClass_project]

/-! ### The invariant system of the legal classes -/

/-- **A legal class not fixed by `τ_β`**, for `β < ω₁`: the class at `ω₁` of a strongly coded
uniformity donor at `λ_{β+1}` for `λ_β` (`hasStronglyCodedUniformityDonors`) has a label in
`[λ_β, λ_β + ω)`, while every label of a class fixed by `τ_β` is below `λ_β` or `⊤`
(`TemplateClass.mem_labels_project`).  Native construction. -/
theorem exists_legalClass_project_ne {β : Ordinal.{u}} (hβ : β < ω₁) :
    ∃ c : LegalClass.{u} 1, c.project β ≠ c := by
  obtain ⟨d, hdl, j, hj⟩ :=
    hasStronglyCodedUniformityDonors.{u} (Order.lt_add_one_iff.mpr le_rfl : β < β + 1)
  have hω : blockStage (β + 1) ≤ ω₁ := (blockStage_lt_omega_one (add_one_lt_omega_one hβ)).le
  refine ⟨⟨d.globalClass, (TemplateClass.isStronglyCodedLegal_reduce_iff _ d.toClass).mpr hdl⟩,
    fun hfix ↦ ?_⟩
  have hl : d.label j ∈ d.globalClass.labels := by
    rw [StageType.globalClass, TemplateClass.labels_toClass]
    exact ⟨j, d.reduce_label_of_le _ hω j⟩
  have hl' : d.label j ∈ (d.globalClass.project (isSuccPrelimit_blockStage β)).labels := by
    rw [show d.globalClass.project _ = d.globalClass from congrArg Subtype.val hfix]
    exact hl
  rcases TemplateClass.mem_labels_project _ _ hl' with h | h
  · exact (not_lt.mpr hj.1) h
  · rw [h] at hj
    exact not_top_lt hj.2

/-- **The invariant system of the legal classes** [AFK26, Definitions 2.6 and 4.16]: `τ_β(Q_c) =
Q_{τ_β(c)}` for `β < ω₁` (`templateInvariantProject`).  Its fields:

* (a), (b) `τ_β` maps `L_b[L]^n` to `L_b[L]^n` (by definition);
* (c) `τ_α ∘ τ_β = τ_β ∘ τ_α = τ_α` for `α ≤ β` (`LegalClass.project_project_of_le`,
  `LegalClass.project_project_of_ge`);
* (d)(i) countably many `β`-invariants: a legal class fixed by `τ_β` is the class at `ω₁` of its
  reduction to the countable stage `λ_β` (`LegalClass.globalClass_reduce_of_project_eq`), and the
  classes at `λ_β` are countably many (`StageType.countable_of_lt_omega_one`);
* (d)(ii) not every invariant is a `β`-invariant (`exists_legalClass_project_ne`);
* (d)(iii) every invariant is a `β`-invariant for some `β < ω₁`
  (`legalClassFixingStageTarget`).

Correspondence with the printed definitions. -/
noncomputable def templateInvariantSystem : Correspondence.InvariantSystem.{u} templateSignature.{u}
    where
  τ β _ Q := templateInvariantProject β.1 Q
  comp α β hαβ n Q := by
    refine ⟨templateInvariant_ext_iff.mpr ?_, templateInvariant_ext_iff.mpr ?_⟩
    · simp only [templateInvariantClass_project]
      exact (templateInvariantClass Q).project_project_of_le hαβ
    · simp only [templateInvariantClass_project]
      exact (templateInvariantClass Q).project_project_of_ge hαβ
  countable β := by
    have hlt := blockStage_lt_omega_one β.2
    have (n : ℕ) : Countable (StageType.{u} (blockStage β.1) n) :=
      StageType.countable_of_lt_omega_one hlt n
    refine Set.MapsTo.countable_of_injOn (Set.mapsTo_univ (fun Q : Σ n,
      templateSignature.{u}.Invariant n ↦ (⟨Q.1, (templateInvariantClass Q.2).1.reduce
        (isSuccPrelimit_blockStage β.1)⟩ : Σ n, TemplateClass.{u} (blockStage β.1) n)) _) ?_
      Set.countable_univ
    rintro ⟨n, Q⟩ hQ ⟨n', Q'⟩ hQ' h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    have hc : templateInvariantClass Q = templateInvariantClass Q' := by
      have e := (templateInvariantProject_eq_self_iff β.1 Q).mp hQ
      have e' := (templateInvariantProject_eq_self_iff β.1 Q').mp hQ'
      refine Subtype.ext ?_
      rw [← LegalClass.globalClass_reduce_of_project_eq e,
        ← LegalClass.globalClass_reduce_of_project_eq e', eq_of_heq h]
    exact congrArg (Sigma.mk n) (templateInvariant_ext_iff.mpr hc)
  ne_univ β h := by
    obtain ⟨c, hc⟩ := exists_legalClass_project_ne β.2
    have hmem : (⟨1, ⟨TemplateSymbol.invariant c one_pos, trivial⟩⟩ :
        Σ n, templateSignature.{u}.Invariant n) ∈
        {Q : Σ n, templateSignature.{u}.Invariant n | templateInvariantProject β.1 Q.2 = Q.2} :=
      h ▸ Set.mem_univ _
    exact hc ((templateInvariantProject_eq_self_iff β.1 _).mp hmem)
  exists_fixed n Q := by
    obtain ⟨β, hβ, h⟩ := legalClassFixingStageTarget.{u} (templateInvariantClass Q)
    exact ⟨⟨β, hβ⟩, (templateInvariantProject_eq_self_iff β Q).mpr h⟩

/-- The map `τ_β` of `templateInvariantSystem` on `Q_c`.  Correspondence with the printed
definitions. -/
theorem templateInvariantSystem_τ_mk (β : {β : Ordinal.{u} // β < ω₁}) {n : ℕ}
    (c : LegalClass.{u} n) (hn : 0 < n) :
    (templateInvariantSystem.τ β ⟨TemplateSymbol.invariant c hn, trivial⟩).1 =
      TemplateSymbol.invariant (c.project β.1) hn :=
  rfl

/-- **The reading of a symbol of `L_c[L]` does not see a projection**: for a symbol `R` that is not
an invariant (`P_n` or `R_c`) and `λ_β`, `R` reads `τ_β(s)` exactly when it reads `s`
(`TemplateClass.project_project_of_le` at `λ_0 ≤ λ_β` for `R_c`).  Correspondence with the
printed definitions. -/
theorem TemplateSymbol.reads_project_iff {k : ℕ} {R : TemplateSymbol.{u} k}
    (hR : ¬ R.IsInvariant) (β : Ordinal.{u}) (s : TemplateClass.{u} ω₁ k) :
    R.Reads (s.project (isSuccPrelimit_blockStage β)) ↔ R.Reads s := by
  cases R with
  | closed => exact Iff.rfl
  | invariant => exact (hR trivial).elim
  | base c h0 hn =>
    change (s.project _).project _ = c.1 ↔ s.project _ = c.1
    rw [s.project_project_of_le _ _ (blockStage_mono zero_le)]

/-- **A symbol of `L_c[L]` holds on a template exactly when it holds on its projection**.
Correspondence with the printed definitions. -/
theorem TemplateClass.holds_project_iff {n k : ℕ} {R : TemplateSymbol.{u} k}
    (hR : ¬ R.IsInvariant) (β : Ordinal.{u}) (c : TemplateClass.{u} ω₁ n) (j : Fin k → Fin n) :
    (c.project (isSuccPrelimit_blockStage β)).Holds R j ↔ c.Holds R j := by
  refine exists_congr fun h ↦ ?_
  rw [TemplateClass.restrictFace_project]
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨s₀, hs₀, (TemplateSymbol.reads_project_iff hR β s₀).mp hr⟩
  · rintro ⟨s, hs, hr⟩
    exact ⟨_, by rw [hs, Option.map_some], (TemplateSymbol.reads_project_iff hR β s).mpr hr⟩

/-- **`ID[L]` is compatible with the invariant system of the legal classes** [AFK26, Definition 2.8
and Lemma 4.19].  First clause: a pair `(Q_p(x), Q_q(x_j))` gives `(Q_{τ_β p}(x), Q_{τ_β q}(x_j))`,
since the face of `τ_β(p)` along `j` is `τ_β` of the face of `p`
(`TemplateClass.restrictFace_project`).
Second clause: for `R ∈ L_c[L]`, `(Q_p(x), R(x_j))` is a pair exactly when `(Q_{τ_β p}(x), R(x_j))`
is (`TemplateClass.holds_project_iff`).  Correspondence with the printed definitions. -/
theorem isCompatibleWith_templateInvariantSystem :
    templateDiagram.IsCompatibleWith templateInvariantSystem.{u} where
  invariant β n k P Q j h := by
    obtain ⟨p, hn, rfl⟩ := templateInvariant_eq P
    obtain ⟨q, hk, rfl⟩ := templateInvariant_eq Q
    obtain ⟨hj, s, hs, hr⟩ := (mk_atom_mem_templateDiagramPairs_iff hn p _ j).mp h
    refine (mk_atom_mem_templateDiagramPairs_iff hn (p.project β.1) _ j).mpr
      ⟨hj, s.project (isSuccPrelimit_blockStage β.1), ?_, ?_⟩
    · rw [LegalClass.coe_project, TemplateClass.restrictFace_project, hs, Option.map_some]
    · change s.project _ = (q.project β.1).1
      rw [show s = q.1 from hr]
      rfl
  base β n k P R j hR := by
    obtain ⟨p, hn, rfl⟩ := templateInvariant_eq P
    exact (mk_atom_mem_templateDiagramPairs_iff hn p R j).trans
      ((TemplateClass.holds_project_iff hR β.1 p.1 j).symm.trans
        (mk_atom_mem_templateDiagramPairs_iff hn (p.project β.1) R j).symm)

/-- **Target: the projections of the legal classes form an invariant system compatible with
`ID[L]`** [AFK26, Definitions 2.6, 2.8 and 4.16, Lemma 4.19]: an invariant system `S` on the
invariants `L_b[L]` of `templateSignature` whose map `τ_β`, `β < ω₁`, sends `Q_c` to `Q_{τ_β(c)}`,
and which is compatible with `templateDiagram`.  Proved (`templateInvariantSystemTarget`).
Correspondence with the printed definitions. -/
def TemplateInvariantSystemTarget : Prop :=
  ∃ S : Correspondence.InvariantSystem.{u} templateSignature.{u},
    (∀ (β : {β : Ordinal.{u} // β < ω₁}) {n : ℕ} (c : LegalClass.{u} n) (hn : 0 < n),
      (S.τ β ⟨TemplateSymbol.invariant c hn, trivial⟩).1 =
        TemplateSymbol.invariant (c.project β.1) hn) ∧
    templateDiagram.IsCompatibleWith S

/-- **The invariant system of the legal classes, compatible with `ID[L]`**
(`TemplateInvariantSystemTarget`): `templateInvariantSystem`, `templateInvariantSystem_τ_mk` and
`isCompatibleWith_templateInvariantSystem`.  Correspondence with the printed definitions. -/
theorem templateInvariantSystemTarget : TemplateInvariantSystemTarget.{u} :=
  ⟨templateInvariantSystem, fun β _ c hn ↦ templateInvariantSystem_τ_mk β c hn,
    isCompatibleWith_templateInvariantSystem⟩

/-! ### The projection of a structure -/

namespace Correspondence

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

/-- **The `β`-projection of a structure** [AFK26, Definition 2.7], for an invariant system `S` on
`L_b`: the same carrier; a symbol of `L_c` holds as in `G`; an invariant `R` holds of `x` exactly
when some invariant `R*` with `τ_β(R*) = R` holds of `x` in `G`.  Correspondence with the printed
definitions. -/
@[instance_reducible] def InvariantSystem.projection (S : InvariantSystem.{u} σ)
    (β : {β : Ordinal.{u} // β < ω₁}) {M : Type v} (G : L.Structure M) : L.Structure M where
  funMap {n} f := (σ.isEmpty_functions n).elim f
  RelMap {n} R xs := (σ.IsInvariant R → ∃ Q : σ.Invariant n, (S.τ β Q).1 = R ∧
      RelMap (L := L) (self := G) Q.1 xs) ∧
    (¬ σ.IsInvariant R → RelMap (L := L) (self := G) R xs)

end Correspondence

/-- **The projection of a structure for the invariant system of the legal classes is
`projectStructure`** [AFK26, Definitions 2.7 and 4.16]: for `β < ω₁`, the `β`-projection of `G`
for `templateInvariantSystem` is `projectStructure β G`.  Correspondence with the printed
definitions. -/
theorem templateInvariantSystem_projection {M : Type v} (β : {β : Ordinal.{u} // β < ω₁})
    (G : templateLanguage.{u}.Structure M) :
    templateInvariantSystem.projection β G = projectStructure β.1 G := by
  refine templateStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk =>
    exact ⟨fun h ↦ h.2 id, fun h ↦ ⟨fun h' ↦ (h' : False).elim, fun _ ↦ h⟩⟩
  | base c h0 hk =>
    exact ⟨fun h ↦ h.2 id, fun h ↦ ⟨fun h' ↦ (h' : False).elim, fun _ ↦ h⟩⟩
  | invariant c hk =>
    rw [relMap_projectStructure_invariant]
    constructor
    · rintro ⟨h, -⟩
      obtain ⟨Q, hQ, hx⟩ := h trivial
      obtain ⟨c', hn', rfl⟩ := templateInvariant_eq Q
      exact ⟨c', TemplateSymbol.invariant.inj hQ, hx⟩
    · rintro ⟨c', rfl, hx⟩
      exact ⟨fun _ ↦ ⟨⟨TemplateSymbol.invariant c' hk, trivial⟩,
        templateInvariantSystem_τ_mk β c' hk, hx⟩, fun h ↦ (h trivial).elim⟩

/-! ### Density -/

/-- **Raw truncation at a block stage up to renaming determines the projection to it**: for
`λ ≤ ω₁` zero or a limit, if `trunc_λ(c) ≅_ren trunc_λ(d)` then `τ_λ(c) = τ_λ(d)`.  Representatives
with the same scheme have the same labels after reduction to `λ` (`StageType.label_project`).
Correspondence with the printed definitions. -/
theorem TemplateClass.project_eq_project_of_truncEquiv {γ : Ordinal.{u}}
    (hγ : Order.IsSuccPrelimit γ) (hγω : γ ≤ ω₁) {n : ℕ} {c d : TemplateClass.{u} ω₁ n}
    (h : c.TruncEquiv γ d) : c.project hγ = d.project hγ := by
  induction c using Quotient.inductionOn with | h s => ?_
  induction d using Quotient.inductionOn with | h t => ?_
  obtain ⟨s', hss', hS, hl⟩ := TemplateClass.truncEquiv_toClass_iff.mp h
  change s.toClass.project hγ = t.toClass.project hγ
  rw [show s.toClass = s'.toClass from StageType.toClass_eq_toClass_iff.mpr hss',
    TemplateClass.project_toClass, TemplateClass.project_toClass]
  refine congrArg StageType.toClass (StageType.ext ?_ fun i j hij ↦ ?_)
  · rw [StageType.project_toScheme, StageType.project_toScheme]
    exact hS
  · exact (s'.label_project hγ hγω i).trans ((hl i j hij).trans (t.label_project hγ hγω j).symm)

/-- **`α`-density in the form of [AFK26, Definition 2.10 (c)]**, for the invariants of `K[L]`:
whenever `(Q_u(x̄ ȳ), Q_t(x̄)) ∈ ID[L]` and `G ⊨ Q_t(x̄)`, there are `ȳ` and an invariant `Q_s`
with `τ_α(s) = τ_α(u)` and `G ⊨ Q_s(x̄ ȳ)`.  The classes `u` and `s` are of any rank.
Correspondence with the printed definitions. -/
def ProjectedDensityAt {M : Type v} (α : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) :
    Prop :=
  ∀ ⦃n m : ℕ⦄ (hn : 0 < n) (t : LegalClass.{u} n) (u : LegalClass.{u} (n + m)),
    (⟨n + m, TemplateSymbol.invariant u (Nat.lt_add_right m hn),
      Correspondence.atom (L := templateLanguage) (TemplateSymbol.invariant t hn)
        (Fin.castAdd m)⟩ : Correspondence.DiagramPair templateLanguage.{u}) ∈
        templateDiagramPairs →
    ∀ x : Fin n → M, RelMap (L := templateLanguage.{u}) (self := G)
        (TemplateSymbol.invariant t hn) x →
      ∃ (y : Fin m → M) (s : LegalClass.{u} (n + m)), s.project α = u.project α ∧
        RelMap (L := templateLanguage.{u}) (self := G)
          (TemplateSymbol.invariant s (Nat.lt_add_right m hn)) (Fin.append x y)

/-- **From `D[λ_α]` to `α`-density**: for `α < ω₁`, the scalar density axiom at the block cutoff
`λ_α = ω + ω · α` gives `α`-density in the form of [AFK26, Definition 2.10 (c)], for donors of
every rank: the witness `s` of `D[λ_α]` has `trunc_{λ_α}(s) ≅_ren trunc_{λ_α}(u)`, hence
`τ_α(s) = τ_α(u)` (`TemplateClass.project_eq_project_of_truncEquiv`).  Correspondence with the
printed definitions. -/
theorem projectedDensityAt_of_satisfiesDensityAt {M : Type v} {α : Ordinal.{u}} (hα : α < ω₁)
    {G : templateLanguage.{u}.Structure M} (h : SatisfiesDensityAt (blockStage α) G) :
    ProjectedDensityAt α G := by
  intro n m hn t u hp x hx
  obtain ⟨y, s, hsu, hs⟩ := h hn t u hp x hx
  exact ⟨y, s, Subtype.ext (TemplateClass.project_eq_project_of_truncEquiv _
    (blockStage_lt_omega_one hα).le hsu), hs⟩

/-! ### The clauses of a weak system -/

/-- **Target: the clauses of a weak system for `K[L]`** [AFK26, Definition 2.17 and Theorem 4.23,
first half]: on a countable carrier, for `β < ω₁` and `G ∈ K_β[L]`: every structure isomorphic to
`G` in `L_b[L] ∪ L_c[L]`, on a carrier in the same universe, is in `K_β[L]`; `G` is compatible with
`ID[L]` (`IsTemplateCompatible`, equivalently `templateDiagram.IsCompatible`); `G` has rank at most
`β` (`τ_β(G) = G`); `G` is `α`-dense (`ProjectedDensityAt α G`) for every `α < β`; and
`τ_α(G) ∈ K_α[L]` for every `α ≤ β`.  Proved (`weakSystemClausesTarget`).  Correspondence with
the printed definitions. -/
def WeakSystemClausesTarget (M : Type v) : Prop :=
  Countable M → ∀ β : Ordinal.{u}, β < ω₁ → ∀ G ∈ templateStageClass M β,
    (∀ (N : Type v) (H : templateLanguage.{u}.Structure N),
      Nonempty (@Language.Equiv templateLanguage.{u} M N G H) → H ∈ templateStageClass N β) ∧
    IsTemplateCompatible G ∧ projectStructure β G = G ∧
    (∀ α < β, ProjectedDensityAt α G) ∧
    ∀ α ≤ β, projectStructure α G ∈ templateStageClass M α

/-- **The clauses of a weak system for `K[L]`** (`WeakSystemClausesTarget M` for every `M`):
isomorphism closure by transport (`transportStructure_eq_of_equiv`,
`mem_templateStageClass_transportStructure`); compatibility and rank from the clauses of
`templateStageClass`; `α`-density from `D[λ_α]`, `λ_α < λ_β` (`blockStage_strictMono`,
`projectedDensityAt_of_satisfiesDensityAt`); closure under `τ_α` (`projectionTarget`).
Correspondence with the printed definitions. -/
theorem weakSystemClausesTarget (M : Type v) : WeakSystemClausesTarget.{u} M := by
  intro hc β hβ G hG
  refine ⟨fun N H ⟨g⟩ ↦ ?_, hG.2.1, hG.2.2.1, fun α hα ↦ ?_,
    fun α hα ↦ projectionTarget β α M hc hβ hα G hG⟩
  · rw [← transportStructure_eq_of_equiv g]
    exact mem_templateStageClass_transportStructure _ hG
  · exact projectedDensityAt_of_satisfiesDensityAt (hα.trans hβ)
      (hG.2.2.2 _ (blockStage_strictMono hα))

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.UniversalTheorem
import VaughtConjecture.Correspondence.Maximality.Completion
import VaughtConjecture.Correspondence.Maximality.Count

/-!
# The four conditions of a Knight system for the template system: [AFK26, Definition 2.23]

Numbering as in the current draft of [AFK26].  `K_β[L]` is `templateStageClass M β`, `τ_β` is
`projectStructure β`, `N↾L_c[L]` is `baseReduct N`, maximality at a level is `IsMaximalAt`
([AFK26, Definition 2.20]), and `σ[L]` is `templateSentence` ([AFK26, Definition 4.22]).  The
system is `K[L] = ⋃_{β<ω₁} K_β[L]`, read on each carrier separately; its **base** `K_{-∞}[L]`
([AFK26, Definition 2.17]) on a carrier `M` is `IsInTemplateBase`.

[AFK26, Definition 2.23]: a weak Knight system `K` is a Knight system if
(a) `K_{-∞} = {M↾L_c : M ∈ K maximal}`; (b) `K` has few maximal models ([AFK26, Definition 2.20]:
for every `β ∈ ω₁`, countably many models maximal at `β` up to isomorphism); (c) every member of
`K_{-∞}` is eventually determined ([AFK26, Definition 2.21]); (d) every invariant `Q ∈ L_b` has
some `M ∈ K` with `M ⊨ ∃x̄ Q(x̄)`.  This file states each condition for `K[L]` and records the
status of each.  The weak-Knight clauses ([AFK26, Theorem 4.23]) are not restated here: closure
under `τ_α` is `projectionTarget`, invariance under isomorphism is
`mem_templateStageClass_transportStructure_iff` and `IsTemplateCompatible.of_equiv`, and the
remaining clauses are the defining clauses of `templateStageClass`.

## Carrier conventions, explicitly

* **Members of `K_β[L]`** have nonempty carriers by definition: `Nonempty M` is the first clause
  of `templateStageClass` (`nonempty_of_mem_templateStageClass`, [AFK26, §1]), and for `β < ω₁` they
  are even infinite (`infinitudeTarget`).  So conditions (a)–(c), quantified over members of the
  system or of its base, carry **no** `Nonempty M` premise: nonemptiness is a consequence.
* **Models of `σ[L]`** need not have nonempty carriers: the structure on an empty carrier
  satisfies `σ[L]` (`realize_templateSentence_of_isEmpty`) and is not in the base
  (`templateStageClass_eq_empty_of_isEmpty`).  The identification of the base with the models of
  `σ[L]` (`TemplateBaseModelsTarget`, [AFK26, Theorem 4.23]) therefore assumes `Nonempty M`.
* **Countability**: every carrier of (a)–(c) is countable (`Countable M`, the premise of the
  completion results of `Correspondence/Maximality/Completion`); (d) assumes a countably infinite
  carrier (`Countable M`, `Infinite M`, the premises of `universalChartModelTarget`).
* **Universes**: the ordinals and the language are in universe `u` in (a), (c), (d), and in
  universe `0` in (b) (as `maximalCountTarget`); the carriers are in any universe `v`.  The
  bundle `IsKnightSystemTarget` is at universe `0` for the ordinals.

## The conditions, every input named

**(a) Maximal coverage** (`MaximalCoverageTarget M`, proved by composition): on a countable
carrier, every `G ∈ K_β[L]`, `β < ω₁`, has a maximal completion `(γ, H)` (`IsMaximalCompletion`):
`β ≤ γ < ω₁`, `H` maximal at `γ` on the same carrier, and `τ_β(H) = G`.  So `G` is a projection of
a maximal structure.  Input: `maximalCompletionTarget`.  The printed set equality,
`K_{-∞} = {H↾L_c : H maximal}` (`MaximalCoverageBaseTarget M`), follows with
`baseReduct_projectStructure`.  The other lifts of the base are projections of `H`
(`lowerLiftsAreProjectionsTarget`) and the maximal lift is unique (`maximalLiftUniqueTarget`);
these are not part of the printed clause.

**(b) Uniform countable maximal representatives** (`UniformMaximalRepresentativesTarget`, proved
by composition): one family `S β` of sets of structures on `ℕ`, indexed by the ordinals, such that
for every `β < ω₁`, `S β` is countable, consists of structures maximal at `β`, and every structure
maximal at `β` on a countable carrier is isomorphic to a member of `S β` in the **full** template
language `L_b[L] ∪ L_c[L]`.  Input: `maximalCountTarget` (`MaximalCountTarget`, without a
nonemptiness premise, which is automatic for maximal structures; the printed headline form with
`[Nonempty M]` is `proposition435Target`).

*What "uniform" adds.*  Only a choice: the per-`β` statement `maximalCountTarget β` gives, for each
`β < ω₁`, a countable set; uniformity selects them into one function `S` of `β` (by choice; no new
mathematics).  In each `S β` the set is chosen before the source carrier `M` and the structure `G`
(as already in `MaximalCountTarget`).  The union `⋃_{β<ω₁} S β` is a union of `ℵ₁` countable sets
and is **not** asserted to be countable; it is not used.  The count of [AFK26, Theorem 4.36] uses
the per-`β` countability, through the fibres of the maximal stage
(`VaughtConjecture.Correspondence.KnightSystem.Theorem436`).

**(c) Attained eventual determination** (`AttainedEventualDeterminationTarget M`, proved by
composition): on a countable carrier, for every member `B` of the base and every closed tuple `t`
of `B` (`B ⊨ P_n(t)`, `n > 0`), the maximal lift `(γ, H)` of `B` gives the invariant `Q_c` of `t`
in `H`, and an **attained** threshold `ξ ≤ γ`: the actual projection `τ_ξ(H) ∈ K_ξ[L]` has
`Q_c(t)`, and every lift of `B` in `K_ζ[L]`, `ξ ≤ ζ < ω₁`, has `Q_c(t)`.  Inputs:
`maximalCompletionTarget`, `Correspondence.IsStructuredGeometry.closed_iff`,
`eventualDeterminationTarget` (whose threshold is moreover least, `IsLeast`, and which also uses
`relMap_projectStructure_invariant_iff_project_eq`).  The printed clause
(`IsEventuallyDetermined`, [AFK26, Definition 2.21], with `ζ ≥ ξ` in place of the printed
`ζ > ξ`, a strengthening) is `EventualDeterminationOfBaseTarget M`, a consequence.

**(d) Invariant occurrence** (`InvariantOccurrenceTarget M`, stated; **open**): on a countably
infinite carrier, every legal class `c` on `n > 0` points (every invariant `Q_c ∈ L_b[L]`) is fixed
by `τ_β` for some `β < ω₁`, and **the witness is a universal chart model at `β`**: a structure
`G ∈ K_β[L]` on that carrier into which every chart of `C_β[L]` embeds (`EmbedsEveryChart`), with
an injective tuple `t` such that `G ⊨ Q_c(t)`.  This is the printed route ("(d) follows
immediately from" [AFK26, Lemma 4.33]).  Inputs: `universalChartModelTarget` (proved), and two
new lemmas, stated here and not proved:

* `LegalClassFixingStageTarget`: every legal class is fixed by `τ_β` for some `β < ω₁` (its
  finitely many labels lie below some block stage `λ_β`; the counterpart for stage types is the
  field `exists_fixed` of the invariant system of the block stages);
* `UniversalModelOccurrenceTarget M`: for `β < ω₁` and `c` fixed by `τ_β`, every `G ∈ K_β[L]` in
  which every chart embeds has a tuple with `Q_c` (the chart on a legal template at `λ_β` of class
  `c`, `StageType.liftChart` and `StageType.isTemplateChart_liftChart`, embeds, and an embedding
  preserves the relation `Q_c` of the enumeration of the chart).

Given both, (d) is a composition (`invariantOccurrenceTarget_of`).

**The bundle** (`IsKnightSystemTarget`): (a), (b), (c), (d) at universe `0` for the ordinals and
the language, with carriers in the universe `v`; `isKnightSystemTarget_of` derives it from the two
new lemmas of (d).
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The base of the system -/

/-- **The base `K_{-∞}[L]` on a carrier** [AFK26, Definition 2.17, for `K[L]`]: `B` is the base
reduct of a member of `K_β[L]`, for some `β < ω₁`, on the same carrier.  Equivalently,
`liftStages M B` is nonempty.  Correspondence with the printed definitions. -/
def IsInTemplateBase {M : Type v} (B : baseTemplateLanguage.{u}.Structure M) : Prop :=
  ∃ β < ω₁, ∃ G ∈ templateStageClass M β, baseReduct G = B

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

/-! ### (a) Maximal coverage -/

/-- **Target (a): maximal coverage** [AFK26, Definition 2.23 (a), for `K[L]`]: on a countable
carrier, every `G ∈ K_β[L]`, `β < ω₁`, is the projection `τ_β(H)` of a structure `H` maximal at a
level `γ` with `β ≤ γ < ω₁`, on the same carrier (`IsMaximalCompletion β G γ H`).  No `Nonempty M`
premise: a member of `K_β[L]` has a nonempty carrier by definition.  Proved; route:
`maximalCompletionTarget`.  Correspondence with the printed definitions. -/
def MaximalCoverageTarget (M : Type v) : Prop :=
  Countable M → ∀ β : Ordinal.{u}, β < ω₁ → ∀ G ∈ templateStageClass M β,
    ∃ γ H, IsMaximalCompletion β G γ H

/-- **(a) Maximal coverage** (`MaximalCoverageTarget M` for every `M`): the maximal completion
(`maximalCompletionTarget`).  Correspondence with the printed definitions. -/
theorem maximalCoverageTarget (M : Type v) : MaximalCoverageTarget.{u} M :=
  fun hc β hβ G hG ↦
    (maximalCompletionTarget β M hc hβ G hG).imp fun _ ⟨H, h, _⟩ ↦ ⟨H, h⟩

/-- **Target (a), as printed** [AFK26, Definition 2.23 (a), for `K[L]`]: on a countable carrier,
`K_{-∞}[L] = {H↾L_c[L] : H ∈ K[L] maximal}`: a base structure is in the base exactly when it is
the base reduct of a structure maximal at some level `γ < ω₁` on the same carrier.  Proved; route:
`MaximalCoverageTarget` and `baseReduct_projectStructure`; the converse inclusion is the first
clause of `IsMaximalAt`.  Correspondence with the printed definitions. -/
def MaximalCoverageBaseTarget (M : Type v) : Prop :=
  Countable M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    IsInTemplateBase B ↔ ∃ γ < ω₁, ∃ H : templateLanguage.{u}.Structure M,
      IsMaximalAt γ H ∧ baseReduct H = B

/-- **(a) as printed** (`MaximalCoverageBaseTarget M` for every `M`), from
`maximalCoverageTarget`.  Correspondence with the printed definitions. -/
theorem maximalCoverageBaseTarget (M : Type v) : MaximalCoverageBaseTarget.{u} M := by
  intro hc B
  constructor
  · rintro ⟨β, hβ, G, hG, rfl⟩
    obtain ⟨γ, H, -, hγ, -, hHG, hH⟩ := maximalCoverageTarget M hc β hβ G hG
    exact ⟨γ, hγ, H, hH, by rw [← hHG, baseReduct_projectStructure]⟩
  · rintro ⟨γ, hγ, H, hH, rfl⟩
    exact ⟨γ, hγ, H, hH.1, rfl⟩

/-! ### (b) Uniform countable maximal representatives -/

/-- **Target (b): uniform countable maximal representatives** [AFK26, Definition 2.23 (b) and
Definition 2.20, "few maximal models", for `K[L]`; Proposition 4.35]: one family `S` indexed by
the ordinals such that, for every `β < ω₁`, `S β` is a countable set of structures on `ℕ`, each
maximal at `β`, and every structure maximal at `β` on a countable carrier `M` (in the universe
`v`) is isomorphic to a member of `S β` in the full language `L_b[L] ∪ L_c[L]`.  Uniformity in `β`
is a choice of the per-`β` sets; the union over `β < ω₁` is not asserted to be countable.  No
`Nonempty M` premise: a maximal structure is in `K_β[L]`, whose carriers are nonempty.  Proved;
route: `maximalCountTarget`.  Correspondence with the printed definitions. -/
def UniformMaximalRepresentativesTarget : Prop :=
  ∃ S : Ordinal.{0} → Set (templateLanguage.{0}.Structure ℕ), ∀ β : Ordinal.{0}, β < ω₁ →
    (S β).Countable ∧ (∀ H ∈ S β, IsMaximalAt β H) ∧
    ∀ (M : Type v) [Countable M] (G : templateLanguage.{0}.Structure M), IsMaximalAt β G →
      ∃ H ∈ S β, Nonempty (@Language.Equiv templateLanguage.{0} M ℕ G H)

/-- **(b) Uniform countable maximal representatives** (`UniformMaximalRepresentativesTarget`):
the sets of `maximalCountTarget β` for `β < ω₁`, chosen into one family (empty at `β ≥ ω₁`).
Correspondence with the printed definitions. -/
theorem uniformMaximalRepresentativesTarget : UniformMaximalRepresentativesTarget.{v} := by
  refine ⟨fun β ↦ if hβ : β < ω₁ then (maximalCountTarget.{v} β hβ).choose else ∅,
    fun β hβ ↦ ?_⟩
  simp only [hβ, ↓reduceDIte]
  exact (maximalCountTarget.{v} β hβ).choose_spec

/-! ### (c) Attained eventual determination -/

/-- **A closed tuple is eventually determined** [AFK26, Definition 2.21, for `K[L]`]: there are
`ξ < ω₁` and an invariant `Q_c` such that some lift of `B` in `K_ξ[L]` has `Q_c(t)`, and every
lift of `B` in `K_ζ[L]`, `ξ ≤ ζ < ω₁`, has `Q_c(t)`.  The printed clause asks this for `ζ > ξ`;
`ξ ≤ ζ` strengthens it.  Correspondence with the printed definitions. -/
def IsEventuallyDetermined {M : Type v} (B : baseTemplateLanguage.{u}.Structure M) {n : ℕ}
    (hn : 0 < n) (t : Fin n → M) : Prop :=
  ∃ ξ < ω₁, ∃ c : LegalClass.{u} n,
    (∃ G ∈ templateStageClass M ξ, baseReduct G = B ∧
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t) ∧
    ∀ ζ, ξ ≤ ζ → ζ < ω₁ → ∀ G ∈ templateStageClass M ζ, baseReduct G = B →
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t

/-- **Target (c): attained eventual determination** [AFK26, Definition 2.23 (c), for `K[L]`;
Theorem 4.36, from Claim 4.37]: on a countable carrier, for every member `B` of the base and every
closed tuple `t` of `B` on `n > 0` points, the maximal lift `(γ, H)` of `B` (`γ < ω₁`, `H` maximal
at `γ`, `H↾L_c[L] = B`) gives an invariant `Q_c` with `H ⊨ Q_c(t)` and an attained threshold
`ξ ≤ γ`: the actual projection `τ_ξ(H)` is in `K_ξ[L]` and has `Q_c(t)`, and every lift of `B` in
`K_ζ[L]`, `ξ ≤ ζ < ω₁`, has `Q_c(t)`.  No `Nonempty M` premise: a member of the base has a
nonempty carrier.  Proved; route: `maximalCompletionTarget`,
`Correspondence.IsStructuredGeometry.closed_iff`, `eventualDeterminationTarget` (whose threshold
is the least one).  Correspondence with the printed definitions. -/
def AttainedEventualDeterminationTarget (M : Type v) : Prop :=
  Countable M → ∀ B : baseTemplateLanguage.{u}.Structure M, IsInTemplateBase B →
    ∀ {n : ℕ} (hn : 0 < n) (t : Fin n → M),
      RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.closed hn) t →
        ∃ (γ : Ordinal.{u}) (H : templateLanguage.{u}.Structure M), γ < ω₁ ∧
          IsMaximalAt γ H ∧ baseReduct H = B ∧ ∃ c : LegalClass.{u} n,
            RelMap (L := templateLanguage.{u}) (self := H) (TemplateSymbol.invariant c hn) t ∧
            ∃ ξ ≤ γ, projectStructure ξ H ∈ templateStageClass M ξ ∧
              RelMap (L := templateLanguage.{u}) (self := projectStructure ξ H)
                (TemplateSymbol.invariant c hn) t ∧
              ∀ ζ, ξ ≤ ζ → ζ < ω₁ → ∀ G ∈ templateStageClass M ζ, baseReduct G = B →
                RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t

/-- **(c) Attained eventual determination** (`AttainedEventualDeterminationTarget M` for every
`M`): the maximal completion of a member of `K_β[L]` with base `B` (`maximalCompletionTarget`), the
invariant of the closed tuple in it (`Correspondence.IsStructuredGeometry.closed_iff`), and
`eventualDeterminationTarget`.  Correspondence with the printed definitions. -/
theorem attainedEventualDeterminationTarget (M : Type v) :
    AttainedEventualDeterminationTarget.{u} M := by
  intro hc B hB n hn t ht
  obtain ⟨β, hβ, G, hG, hGB⟩ := hB
  obtain ⟨γ, H, ⟨-, hγ, -, hHG, hmax⟩, -⟩ := maximalCompletionTarget β M hc hβ G hG
  have hHB : baseReduct H = B := by
    rw [← hGB, ← hHG, baseReduct_projectStructure]
  subst hHB
  have hcl : RelMap (L := templateLanguage.{u}) (self := H) (TemplateSymbol.closed hn) t := ht
  obtain ⟨Q, hQ, hQt⟩ := (hmax.1.2.1.1.closed_iff hn t).mp hcl
  rcases Q with _ | ⟨c, hn'⟩ | _ <;> try exact hQ.elim
  obtain ⟨ξ, hξγ, -, hmem, hrel, -, hall⟩ :=
    eventualDeterminationTarget M hc γ H hγ hmax hn c t hQt
  exact ⟨γ, H, hγ, hmax, rfl, c, hQt, ξ, hξγ, hmem, hrel, hall⟩

/-- **Target (c), as printed** [AFK26, Definition 2.23 (c) and Definition 2.21, for `K[L]`]: on a
countable carrier, every closed tuple of every member of the base is eventually determined
(`IsEventuallyDetermined`).  Proved; route: `AttainedEventualDeterminationTarget`, with the lift
`τ_ξ(H)` at the threshold.  Correspondence with the printed definitions. -/
def EventualDeterminationOfBaseTarget (M : Type v) : Prop :=
  Countable M → ∀ B : baseTemplateLanguage.{u}.Structure M, IsInTemplateBase B →
    ∀ {n : ℕ} (hn : 0 < n) (t : Fin n → M),
      RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.closed hn) t →
        IsEventuallyDetermined B hn t

/-- **(c) as printed** (`EventualDeterminationOfBaseTarget M` for every `M`), from
`attainedEventualDeterminationTarget`.  Correspondence with the printed definitions. -/
theorem eventualDeterminationOfBaseTarget (M : Type v) :
    EventualDeterminationOfBaseTarget.{u} M := by
  intro hc B hB n hn t ht
  obtain ⟨γ, H, hγ, -, rfl, c, -, ξ, hξγ, hmem, hrel, hall⟩ :=
    attainedEventualDeterminationTarget M hc B hB hn t ht
  exact ⟨ξ, hξγ.trans_lt hγ, c, ⟨projectStructure ξ H, hmem, baseReduct_projectStructure H, hrel⟩,
    hall⟩

/-! ### (d) Invariant occurrence -/

/-- **Target (d): invariant occurrence** [AFK26, Definition 2.23 (d), for `K[L]`, through
Lemma 4.33]: on a countably infinite carrier `M`, for every legal class `c` on `n > 0` points
there is `β < ω₁` with `τ_β(c) = c` and a universal chart model at `β` on `M` — a structure
`G ∈ K_β[L]` into which every chart of `C_β[L]` embeds (`EmbedsEveryChart`, charts on carriers in
the universe `w`) — with an injective tuple `t` such that `G ⊨ Q_c(t)`.  Stated; open.  Route:
`LegalClassFixingStageTarget` (new lemma), `universalChartModelTarget` (proved), and
`UniversalModelOccurrenceTarget` (new lemma); `invariantOccurrenceTarget_of`.  Correspondence
with the printed definitions. -/
def InvariantOccurrenceTarget (M : Type v) : Prop :=
  Countable M → Infinite M → ∀ {n : ℕ} (hn : 0 < n) (c : LegalClass.{u} n),
    ∃ β < ω₁, c.project β = c ∧ ∃ G ∈ templateStageClass M β, EmbedsEveryChart.{u, v, w} β G ∧
      ∃ t : Fin n ↪ M,
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t

/-- **Target: a fixing stage of every legal class** (a new lemma for (d)): every legal class `c`
is fixed by `τ_β` for some `β < ω₁`.  Its finitely many labels lie in `{-∞} ∪ ω₁ ∪ {∞}`, hence at
a block stage `λ_β` for some `β < ω₁`; the counterpart for stage types is the field
`exists_fixed` of `blockSystem`.  Stated; not proved.  Correspondence with the printed
definitions. -/
def LegalClassFixingStageTarget : Prop :=
  ∀ {n : ℕ} (c : LegalClass.{u} n), ∃ β < ω₁, c.project β = c

/-- **Target: a universal chart model realizes every invariant fixed at its level** (a new lemma
for (d)): for `β < ω₁` and a legal class `c` on `n > 0` points with `τ_β(c) = c`, every
`G ∈ K_β[L]` into which every chart of `C_β[L]` embeds has an injective tuple `t` with
`G ⊨ Q_c(t)`.  Route: a legal template at `λ_β` of class `c`, its chart on `ULift (Fin n)`
(`StageType.liftChart`, in `C_β[L]` by `StageType.isTemplateChart_liftChart`), an embedding into
`G`, and preservation of the relation `Q_c` of the enumeration of the chart.  Stated; not proved.
Native construction. -/
def UniversalModelOccurrenceTarget (M : Type v) : Prop :=
  ∀ β : Ordinal.{u}, β < ω₁ → ∀ {n : ℕ} (hn : 0 < n) (c : LegalClass.{u} n), c.project β = c →
    ∀ G ∈ templateStageClass M β, EmbedsEveryChart.{u, v, w} β G →
      ∃ t : Fin n ↪ M,
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t

/-- **(d) from its two new lemmas**: a fixing stage `β` of `c` (`LegalClassFixingStageTarget`), the
universal chart model at `β` on `M` (`universalChartModelTarget`), and the occurrence of `Q_c` in
it (`UniversalModelOccurrenceTarget`).  Correspondence with the printed definitions. -/
theorem invariantOccurrenceTarget_of {M : Type v} (hfix : LegalClassFixingStageTarget.{u})
    (hocc : UniversalModelOccurrenceTarget.{u, v, w} M) :
    InvariantOccurrenceTarget.{u, v, w} M := by
  intro hc hM n hn c
  obtain ⟨β, hβ, hcβ⟩ := hfix c
  obtain ⟨G, hG, ha, -, -⟩ := universalChartModelTarget.{u, v, w} β M hβ hc hM
  exact ⟨β, hβ, hcβ, G, hG, ha, hocc β hβ hn c hcβ G hG ha⟩

/-! ### The bundle -/

/-- **Target: `K[L]` satisfies the four conditions of a Knight system** [AFK26, Definition 2.23
(a)–(d), for `K[L]`]: at universe `0` for the ordinals and the language, with carriers in the
universe `v` (charts of (d) on carriers in universe `0`): (a) `MaximalCoverageTarget` on every
carrier, (b) `UniformMaximalRepresentativesTarget`, (c) `AttainedEventualDeterminationTarget` on
every carrier, (d) `InvariantOccurrenceTarget` on every carrier.  The weak-Knight clauses
([AFK26, Theorem 4.23]) are not part of the bundle; see the module docstring.  Stated; (a)–(c)
proved, (d) open (`isKnightSystemTarget_of`).  Correspondence with the printed definitions. -/
def IsKnightSystemTarget : Prop :=
  (∀ M : Type v, MaximalCoverageTarget.{0} M) ∧ UniformMaximalRepresentativesTarget.{v} ∧
    (∀ M : Type v, AttainedEventualDeterminationTarget.{0} M) ∧
    ∀ M : Type v, InvariantOccurrenceTarget.{0, v, 0} M

/-- **The four conditions from the two new lemmas of (d)**: (a), (b), (c) are proved
(`maximalCoverageTarget`, `uniformMaximalRepresentativesTarget`,
`attainedEventualDeterminationTarget`), and (d) is `invariantOccurrenceTarget_of`.
Correspondence with the printed definitions. -/
theorem isKnightSystemTarget_of (hfix : LegalClassFixingStageTarget.{0})
    (hocc : ∀ M : Type v, UniversalModelOccurrenceTarget.{0, v, 0} M) :
    IsKnightSystemTarget.{v} :=
  ⟨maximalCoverageTarget, uniformMaximalRepresentativesTarget,
    attainedEventualDeterminationTarget, fun M ↦ invariantOccurrenceTarget_of hfix (hocc M)⟩

end VaughtConjecture

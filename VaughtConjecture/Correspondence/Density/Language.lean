/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.Chart

/-!
# The template diagram, the base sublanguage, and the projection of a structure

Numbering as in the current draft of [AFK26].  The language `templateLanguage` of
`VaughtConjecture.Correspondence.Charts.Chart` is `L_b[L] ∪ L_c[L]` ([AFK26, Definitions 4.12,
4.15 and 4.17]): the symbols `P_n`, one invariant `Q_c` for each legal class `c` (the template
system `L` keeps one template per class, [AFK26, Definition 4.11 and Proposition 4.30]), and one
`R_c` for each legal class fixed by `τ₀`.  This file states, for that language:

* **The setting** [AFK26, Convention 2.3] (correspondence with the printed definitions):
  `templateSignature`, the `GeometrySignature` with `L_a = {P_n}`, `L_b = {Q_c}` and
  `L_c = {P_n} ∪ {R_c}`.  Its clauses `|L_b^n| > 0` and `|L_c^n| ≤ ω` are proved: an interval
  type is strongly coded legal (`exists_legalClass`), and the symbols `R_c` inject into the
  classes at stage `ω`, a countable type (`countable_setOf_not_isInvariant`).
* **The template diagram** `ID[L]` [AFK26, Definition 4.18] (correspondence with the printed
  definitions): `TemplateClass.Holds c r i` is the truth of `r(x_{i_0}, …, x_{i_{k-1}})` on the
  template of class `c`, clause by clause:
  - `P_k`: the `i_j` are distinct and `{i_j}` is closed in the geometry of `t`;
  - `Q_{t*}`: moreover `i_j ↦ j` is an isomorphism from a renaming of `t↾{i_j}` to `t*`, that is,
    `t*` is the class of the face of `t` along `i`;
  - `R_{t⁻}`: moreover `t⁻ ≅_ren trunc_ω(t⁺)` for the class `t⁺` of that face.
  The pairs of `ID[L]` (`templateDiagramPairs`) are `(Q_c(x), r(x_i))` when `c.Holds r i`, and
  `(Q_c(x), ¬r(x_i))` otherwise: the negative pairs are forced by clause (b) of
  [AFK26, Definition 2.4].  A pair `(Q_c(x), r(x_i))` is in `ID[L]` exactly when
  `c.Holds r i` (`mk_atom_mem_templateDiagramPairs_iff`).  For a stage type,
  `TemplateClass.Holds` on its class at `ω₁` is `StageType.Holds` (`holds_toClass`).
* **Compatibility with `ID[L]`** [AFK26, Definition 2.5, for the diagram of Definition 4.18]
  (correspondence with the printed definitions): `IsTemplateCompatible G`, with the two printed
  clauses, the structured geometry of [AFK26, Definition 2.2] (`Correspondence.IsStructuredGeometry`
  for `templateSignature`) and the pairs (`Correspondence.SatisfiesPairs`).  The pairs hold
  exactly when every tuple with an invariant `Q_c` has the relations that `c` prescribes
  (`satisfiesPairs_templateDiagramPairs_iff`).  The third clause of [AFK26, Definition 2.4] (each
  invariant realized in a compatible countable structure) is not used by Definition 2.5; it is
  proved, by the finite charts, in `VaughtConjecture.Correspondence.Density.Structure`
  (`exists_isTemplateCompatible_relMap_invariant`, `templateDiagram`).
* **The base sublanguage** `L_c[L]` [AFK26, Definition 4.17] (correspondence with the printed
  definitions): `baseTemplateLanguage`, with the symbols `P_n` and `R_c` (`BaseSymbol`), its
  inclusion `baseInclusion` into `templateLanguage` (injective, `baseInclusion_injective`), and
  the **literal same-carrier reduct** `baseReduct G = G↾L_c[L]`, the Mathlib reduct along the
  inclusion: a structure on the same carrier `M`, no point renamed, each base symbol read as its
  image (`relMap_baseReduct`, `isExpansionOn_baseReduct`).
* **The projection** `τ_β` [AFK26, Definitions 4.16 and 2.7] (correspondence with the printed
  definitions): on a legal class, `LegalClass.project β` is the projection to the block stage
  `ω + ω · β` (`TemplateClass.project`); on a structure, `projectStructure β G` keeps the carrier
  and the symbols of `L_c[L]` and makes `Q_c` hold of `x` exactly when `Q_{c*}` holds of `x` in
  `G` for some `c*` with `τ_β(c*) = c`.  `fixingStages G` is the set of printed indices
  `β < ω₁` with `τ_β(G) = G`, whose least element is `rank_τ(G)`.

**Well-definedness** (native construction): the projection of a class is legal
(`LegalClass.project`); projections compose to the lower one in either order
(`LegalClass.project_project_of_le`, `LegalClass.project_project_of_ge`, for every pair of
indices, without a bound by `ω₁`), so `projectStructure` is idempotent
(`projectStructure_projectStructure`) and the fixing stages are closed upward
(`projectStructure_eq_of_le`); projection does not change the base reduct
(`baseReduct_projectStructure`).
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Projection of classes -/

namespace StageType

variable {n : ℕ} {γ : Ordinal.{u}}

/-- **The labels of a projection** to a stage `γ` that is zero or a limit, for every `γ`: the
labels reduced to `min γ ω₁`.  Native construction. -/
theorem label_project_eq_reduce_min (p : StageType.{u} ω₁ n) (hγ : Order.IsSuccPrelimit γ)
    (d : Fin p.card) : (p.project hγ).label d = Label.reduce (min γ ω₁) (p.label d) := by
  change Label.reduce ω₁ (Label.reduce γ (p.label d)) = _
  rcases le_total γ ω₁ with h | h
  · rw [min_eq_left h, Label.reduce_reduce_of_ge h]
  · rw [min_eq_right h, Label.reduce_reduce_of_le h, (p.atStage d).reduce_eq]

/-- **Projections compose to the lower one**, for every pair of stages.  Native construction. -/
theorem project_project_of_le' (p : StageType.{u} ω₁ n) {δ : Ordinal.{u}}
    (hγ : Order.IsSuccPrelimit γ) (hδ : Order.IsSuccPrelimit δ) (hγδ : γ ≤ δ) :
    (p.project hδ).project hγ = p.project hγ :=
  ext rfl fun i j hij ↦ by
    have hij' : (i : Fin p.card) = j := Fin.ext hij
    rw [label_project_eq_reduce_min (p.project hδ) hγ i, label_project_eq_reduce_min p hδ i,
      label_project_eq_reduce_min p hγ j, Label.reduce_reduce_of_le (min_le_min_right _ hγδ)]
    exact congrArg _ (congrArg p.label hij')

/-- **Projecting to a higher stage after a lower one gives the lower one**, for every pair of
stages.  Native construction. -/
theorem project_project_of_ge' (p : StageType.{u} ω₁ n) {δ : Ordinal.{u}}
    (hγ : Order.IsSuccPrelimit γ) (hδ : Order.IsSuccPrelimit δ) (hγδ : γ ≤ δ) :
    (p.project hγ).project hδ = p.project hγ :=
  ext rfl fun i j hij ↦ by
    have hij' : (i : Fin p.card) = j := Fin.ext hij
    rw [label_project_eq_reduce_min (p.project hγ) hδ i, label_project_eq_reduce_min p hγ i,
      label_project_eq_reduce_min p hγ j, Label.reduce_reduce_of_ge (min_le_min_right _ hγδ)]
    exact congrArg _ (congrArg p.label hij')

/-- Projection keeps strongly coded legality (it keeps the scheme and the rows).
Native construction. -/
theorem isStronglyCodedLegal_project_iff (p : StageType.{u} ω₁ n) (hγ : Order.IsSuccPrelimit γ) :
    (p.project hγ).IsStronglyCodedLegal ↔ p.IsStronglyCodedLegal :=
  Iff.rfl

end StageType

namespace TemplateClass

variable {n : ℕ} {γ δ : Ordinal.{u}}

/-- The projection of a class at `ω₁` is its reduction, read again at `ω₁`.  Native construction. -/
theorem project_eq_reduce_reduce (hγ : Order.IsSuccPrelimit γ) (c : TemplateClass.{u} ω₁ n) :
    c.project hγ = (c.reduce hγ).reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit :=
  Quotient.inductionOn c fun _ ↦ rfl

/-- Projection keeps strongly coded legality.  Native construction. -/
theorem IsStronglyCodedLegal.project {c : TemplateClass.{u} ω₁ n}
    (hc : c.IsStronglyCodedLegal) (hγ : Order.IsSuccPrelimit γ) :
    (c.project hγ).IsStronglyCodedLegal := by
  induction c using Quotient.inductionOn
  exact hc

/-- Projections of classes compose to the lower one, for every pair of stages.
Correspondence with the printed definitions. -/
theorem project_project_of_le (c : TemplateClass.{u} ω₁ n) (hγ : Order.IsSuccPrelimit γ)
    (hδ : Order.IsSuccPrelimit δ) (hγδ : γ ≤ δ) : (c.project hδ).project hγ = c.project hγ := by
  induction c using Quotient.inductionOn
  exact congrArg StageType.toClass (StageType.project_project_of_le' _ hγ hδ hγδ)

/-- Projecting a class to a higher stage after a lower one gives the lower one.
Correspondence with the printed definitions. -/
theorem project_project_of_ge (c : TemplateClass.{u} ω₁ n) (hγ : Order.IsSuccPrelimit γ)
    (hδ : Order.IsSuccPrelimit δ) (hγδ : γ ≤ δ) : (c.project hγ).project hδ = c.project hγ := by
  induction c using Quotient.inductionOn
  exact congrArg StageType.toClass (StageType.project_project_of_ge' _ hγ hδ hγδ)

end TemplateClass

/-! ### The setting -/

/-- **A legal class on every number of points**: the class of the complete interval scheme with
every label bottom, whose rows are bottom and hence strongly coded.
Correspondence with the printed definitions. -/
theorem exists_legalClass (n : ℕ) : Nonempty (LegalClass.{u} n) :=
  ⟨⟨((Correspondence.isLegal_intervalScheme n).toStageType ω₁).toClass,
    (Correspondence.isLegal_intervalScheme n).isLegal_toStageType ω₁,
    fun _ _ ↦ Label.isStronglyCoded_bot _⟩⟩

namespace TemplateSymbol

variable {k : ℕ}

/-- The invariants `L_b[L]`: the symbols `Q_c`.  Correspondence with the printed definitions. -/
def IsInvariant : TemplateSymbol.{u} k → Prop
  | invariant _ _ => True
  | closed _ => False
  | base _ _ _ => False

/-- Every symbol has positive arity.  Correspondence with the printed definitions. -/
theorem pos : TemplateSymbol.{u} k → 0 < k
  | closed hn => hn
  | invariant _ hn => hn
  | base _ _ hn => hn

/-- The symbols of `L_c[L]` of arity `n`, read as `none` for `P_n` and as the reduction of the
class to `ω` for `R_c`.  Native construction. -/
private def baseCode : TemplateSymbol.{u} k → Option (TemplateClass.{u} (blockStage 0) k)
  | closed _ => none
  | invariant _ _ => none
  | base c _ _ => some (c.1.reduce (isSuccPrelimit_blockStage 0))

private theorem baseCode_injOn :
    Set.InjOn (baseCode (k := k)) {r : TemplateSymbol.{u} k | ¬ r.IsInvariant} := by
  intro r hr r' hr' h
  cases r with
  | invariant => exact (hr trivial).elim
  | closed =>
    cases r' with
    | closed => rfl
    | invariant => exact (hr' trivial).elim
    | base => simp [baseCode] at h
  | base c h0 hn =>
    cases r' with
    | closed => simp [baseCode] at h
    | invariant => exact (hr' trivial).elim
    | base c' h0' hn' =>
      simp only [baseCode, Option.some.injEq] at h
      have hcc : c.1 = c'.1 := by
        rw [← h0, ← h0', TemplateClass.project_eq_reduce_reduce,
          TemplateClass.project_eq_reduce_reduce, h]
      obtain rfl : c = c' := Subtype.ext hcc
      rfl

/-- `|L_c[L]^n| ≤ ω`: the symbols that are not invariants are countably many.
Correspondence with the printed definitions. -/
theorem countable_setOf_not_isInvariant (n : ℕ) :
    {r : TemplateSymbol.{u} n | ¬ r.IsInvariant}.Countable := by
  have : Countable (StageType.{u} (blockStage 0) n) :=
    StageType.countable_of_lt_omega_one
      (by rw [blockStage_zero]; exact omega0_lt_omega_one) n
  exact (Set.mapsTo_univ _ _).countable_of_injOn baseCode_injOn Set.countable_univ

end TemplateSymbol

/-- **The setting of [AFK26, Convention 2.3] for `L_b[L] ∪ L_c[L]`**: `L_a = {P_n}`,
`L_b = {Q_c}`, `L_c = {P_n} ∪ {R_c}`.  Correspondence with the printed definitions. -/
def templateSignature : Correspondence.GeometrySignature templateLanguage.{u} where
  closed _ hn := TemplateSymbol.closed hn
  IsInvariant _ r := TemplateSymbol.IsInvariant r
  isEmpty_functions _ := inferInstanceAs (IsEmpty Empty)
  pos_of_relations _ r := TemplateSymbol.pos r
  not_isInvariant_closed _ _ h := h
  exists_isInvariant n hn := ⟨TemplateSymbol.invariant (exists_legalClass n).some hn, trivial⟩
  countable_setOf_not_isInvariant n := TemplateSymbol.countable_setOf_not_isInvariant n

/-! ### The template diagram -/

namespace TemplateClass

variable {n k : ℕ}

/-- **The truth of `r(x_{i_0}, …, x_{i_{k-1}})` on the template of class `c`** ([AFK26,
Definition 4.18], its three clauses through `TemplateSymbol.Reads`): the places `i_j` are
distinct, they span a closed set of the template (the face along `i` is defined), and the symbol
reads the class of that face.  Correspondence with the printed definitions. -/
def Holds (c : TemplateClass.{u} ω₁ n) (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) : Prop :=
  ∃ h : Function.Injective i, ∃ s, c.restrictFace ⟨i, h⟩ = some s ∧ r.Reads s

/-- On the class of a stage type at `ω₁`, `Holds` is the relation of its chart.
Native construction. -/
theorem holds_toClass (t : StageType.{u} ω₁ n) (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) :
    t.toClass.Holds r i ↔ t.Holds r i := by
  refine exists_congr fun h ↦ ?_
  rw [restrictFace_toClass]
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨s', hs', ?_⟩
    rwa [StageType.globalClass, StageType.reduce_self]
  · rintro ⟨s', hs', hr⟩
    refine ⟨s'.toClass, by rw [hs', Option.map_some], ?_⟩
    rwa [StageType.globalClass, StageType.reduce_self] at hr

end TemplateClass

open Correspondence in
/-- **The template diagram `ID[L]`** [AFK26, Definition 4.18], with the negative pairs that
clause (b) of [AFK26, Definition 2.4] requires: `(Q_c(x), r(x_i))` when `c.Holds r i`, and
`(Q_c(x), ¬r(x_i))` otherwise, for every legal class `c` on `n ≥ 1` points, every symbol `r`, and
every sequence `i` of places.  Correspondence with the printed definitions. -/
def templateDiagramPairs : Set (DiagramPair templateLanguage.{u}) :=
  {π | ∃ (n : ℕ) (hn : 0 < n) (c : LegalClass.{u} n) (k : ℕ) (r : TemplateSymbol.{u} k)
    (i : Fin k → Fin n),
    (c.1.Holds r i ∧ π = ⟨n, TemplateSymbol.invariant c hn, atom (L := templateLanguage) r i⟩) ∨
    (¬ c.1.Holds r i ∧
      π = ⟨n, TemplateSymbol.invariant c hn, (atom (L := templateLanguage) r i).not⟩)}

section Diagram

open Correspondence

variable {n k : ℕ}

/-- An atomic formula `r(x_i)` holds of `x` exactly when `r` holds of `x ∘ i`.
Native construction. -/
theorem realize_atom_templateLanguage {M : Type v} [templateLanguage.{u}.Structure M]
    (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) (x : Fin n → M) :
    (atom (L := templateLanguage) r i).Realize x ↔
      RelMap (L := templateLanguage.{u}) r (x ∘ i) :=
  Iff.rfl

/-- The atomic formulas `r(x_i)` of `L_b[L] ∪ L_c[L]` determine the symbol and the places.
Native construction. -/
theorem atom_templateLanguage_injective {r r' : TemplateSymbol.{u} k} {i i' : Fin k → Fin n}
    (h : atom (L := templateLanguage) r i = atom (L := templateLanguage) r' i') :
    r = r' ∧ i = i' := by
  simp only [atom, Relations.formula, Relations.boundedFormula] at h
  injection h with _ _ hr hi
  refine ⟨hr, funext fun j ↦ ?_⟩
  simpa using congrFun hi j

/-- **A positive pair of `ID[L]`**: `(Q_c(x), r(x_i)) ∈ ID[L]` exactly when `c.Holds r i`.
Correspondence with the printed definitions. -/
theorem mk_atom_mem_templateDiagramPairs_iff (hn : 0 < n) (c : LegalClass.{u} n)
    (r : TemplateSymbol.{u} k) (i : Fin k → Fin n) :
    (⟨n, TemplateSymbol.invariant c hn, atom (L := templateLanguage) r i⟩ :
      DiagramPair templateLanguage.{u}) ∈ templateDiagramPairs ↔ c.1.Holds r i := by
  constructor
  · rintro ⟨n', hn', c', k', r', i', ⟨hh, he⟩ | ⟨_, he⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp he
      obtain ⟨he₁, he₂⟩ := Prod.mk.inj (eq_of_heq he)
      have hk : k = k' := by
        simp only [atom, Relations.formula, Relations.boundedFormula] at he₂
        injection he₂
      subst hk
      obtain ⟨rfl, rfl⟩ := atom_templateLanguage_injective he₂
      obtain rfl : c = c' := by injection he₁
      exact hh
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp he
      have he₂ := (Prod.mk.inj (eq_of_heq he)).2
      simp only [atom, Relations.formula, Relations.boundedFormula, Formula.not,
        BoundedFormula.not] at he₂
      cases he₂
  · exact fun h ↦ ⟨n, hn, c, k, r, i, .inl ⟨h, rfl⟩⟩

variable {M : Type v}

/-- **The pairs of `ID[L]` hold in `G`** exactly when every tuple `x` with an invariant `Q_c` has,
along every sequence `i` of its places, exactly the relations `r` with `c.Holds r i`.
Correspondence with the printed definitions. -/
theorem satisfiesPairs_templateDiagramPairs_iff (G : templateLanguage.{u}.Structure M) :
    SatisfiesPairs templateDiagramPairs M ↔
      ∀ ⦃n : ℕ⦄ (hn : 0 < n) (c : LegalClass.{u} n) (x : Fin n → M),
        RelMap (L := templateLanguage.{u}) (TemplateSymbol.invariant c hn) x →
          ∀ ⦃k : ℕ⦄ (r : TemplateSymbol.{u} k) (i : Fin k → Fin n),
            (RelMap (L := templateLanguage.{u}) r (x ∘ i) ↔ c.1.Holds r i) := by
  constructor
  · intro h n hn c x hx k r i
    by_cases hh : c.1.Holds r i
    · have := h _ ⟨n, hn, c, k, r, i, .inl ⟨hh, rfl⟩⟩ x hx
      exact iff_of_true ((realize_atom_templateLanguage r i x).mp this) hh
    · have := h _ ⟨n, hn, c, k, r, i, .inr ⟨hh, rfl⟩⟩ x hx
      simp only [Formula.realize_not] at this
      exact iff_of_false (fun h' ↦ this ((realize_atom_templateLanguage r i x).mpr h')) hh
  · rintro h π ⟨n, hn, c, k, r, i, ⟨hh, rfl⟩ | ⟨hh, rfl⟩⟩ x hx
    · exact (realize_atom_templateLanguage r i x).mpr ((h hn c x hx r i).mpr hh)
    · simp only [Formula.realize_not]
      exact fun h' ↦ hh ((h hn c x hx r i).mp ((realize_atom_templateLanguage r i x).mp h'))

end Diagram

/-- **Compatibility with the template diagram** [AFK26, Definition 2.5 for the diagram `ID[L]` of
Definition 4.18], one field for each printed clause: a structure with an
`(L_a, L_b[L], L_c[L])`-structured geometry ([AFK26, Definition 2.2]) satisfying every pair of
`ID[L]`.  [AFK26, Definition 4.18] calls such a structure an `L`-structure.
Correspondence with the printed definitions. -/
structure IsTemplateCompatible {M : Type v} (G : templateLanguage.{u}.Structure M) : Prop where
  /-- First clause: `M ⊨ Th_StrGeo(L_a, L_b[L], L_c[L])`. -/
  isStructuredGeometry : Correspondence.IsStructuredGeometry templateSignature.{u} M
  /-- Second clause: `M ⊨ ∀ x, Q(x) → ψ(x_j)` for every pair `(Q(x), ψ(x_j)) ∈ ID[L]`. -/
  satisfiesPairs : Correspondence.SatisfiesPairs templateDiagramPairs.{u} M

/-! ### The base sublanguage and the reduct -/

/-- **The relation symbols of `L_c[L]`** [AFK26, Definitions 4.12 and 4.17]: `P_n`, and `R_c` for
each legal class `c` with `τ₀(c) = c`.  Correspondence with the printed definitions. -/
inductive BaseSymbol : ℕ → Type (u + 1)
  /-- `P_n ∈ L_a`. -/
  | closed {n : ℕ} (hn : 0 < n) : BaseSymbol n
  /-- `R_c ∈ L_c[L]`, for a legal class `c` with `τ₀(c) = c`. -/
  | base {n : ℕ} (c : LegalClass.{u} n) (h0 : c.1.project (isSuccPrelimit_blockStage 0) = c.1)
      (hn : 0 < n) : BaseSymbol n

/-- **The base sublanguage `L_c[L]`** [AFK26, Definition 4.17]: relational, with the symbols
`BaseSymbol`.  Correspondence with the printed definitions. -/
def baseTemplateLanguage : Language.{0, u + 1} where
  Functions _ := Empty
  Relations := BaseSymbol.{u}

instance : baseTemplateLanguage.{u}.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- A symbol of `L_c[L]` as a symbol of `L_b[L] ∪ L_c[L]`.
Correspondence with the printed definitions. -/
def BaseSymbol.toTemplateSymbol {k : ℕ} : BaseSymbol.{u} k → TemplateSymbol.{u} k
  | closed hn => TemplateSymbol.closed hn
  | base c h0 hn => TemplateSymbol.base c h0 hn

/-- **The inclusion `L_c[L] ⊆ L_b[L] ∪ L_c[L]`.**  Correspondence with the printed definitions. -/
def baseInclusion : baseTemplateLanguage.{u} →ᴸ templateLanguage.{u} where
  onFunction _ f := Empty.elim f
  onRelation _ r := BaseSymbol.toTemplateSymbol r

/-- The inclusion is injective on symbols.  Native construction. -/
theorem baseInclusion_injective : baseInclusion.{u}.Injective where
  onFunction {_} f _ _ := Empty.elim f
  onRelation {_} := by
    rintro (_ | _) (_ | _) h <;> cases h <;> rfl

/-- The symbols of `L_c[L]` are not invariants.  Correspondence with the printed definitions. -/
theorem not_isInvariant_toTemplateSymbol {k : ℕ} (r : BaseSymbol.{u} k) :
    ¬ (BaseSymbol.toTemplateSymbol r).IsInvariant := by
  cases r <;> exact id

variable {M : Type v}

/-- **The base reduct `G↾L_c[L]`** ([AFK26, Definition 2.2]: `G` is a lift of `G↾L_c`): the
reduct of `G` along the inclusion, a structure on the same carrier `M`.
Correspondence with the printed definitions. -/
@[instance_reducible] def baseReduct (G : templateLanguage.{u}.Structure M) :
    baseTemplateLanguage.{u}.Structure M :=
  @LHom.reduct _ _ baseInclusion M G

/-- **The reduct reads each base symbol as its image.**
Correspondence with the printed definitions. -/
@[simp] theorem relMap_baseReduct (G : templateLanguage.{u}.Structure M) {k : ℕ}
    (r : BaseSymbol.{u} k) (xs : Fin k → M) :
    RelMap (L := baseTemplateLanguage.{u}) (self := baseReduct G) r xs ↔
      RelMap (L := templateLanguage.{u}) (self := G) (BaseSymbol.toTemplateSymbol r) xs :=
  Iff.rfl

/-- **The reduct is a reduct**: `G` is an expansion of `baseReduct G` along the inclusion.
Correspondence with the printed definitions. -/
theorem isExpansionOn_baseReduct (G : templateLanguage.{u}.Structure M) :
    @LHom.IsExpansionOn _ _ baseInclusion M (baseReduct G) G :=
  @LHom.isExpansionOn_reduct _ _ baseInclusion M G

/-- Two structures of `L_c[L]` on `M` are equal when they have the same relations.
Native construction. -/
theorem baseStructure_ext {B B' : baseTemplateLanguage.{u}.Structure M}
    (h : ∀ {k : ℕ} (r : BaseSymbol.{u} k) (xs : Fin k → M),
      RelMap (L := baseTemplateLanguage.{u}) (self := B) r xs ↔
        RelMap (L := baseTemplateLanguage.{u}) (self := B') r xs) : B = B' := by
  obtain ⟨f, R⟩ := B
  obtain ⟨f', R'⟩ := B'
  have hf : @f = @f' := funext fun _ ↦ funext fun g ↦ Empty.elim g
  subst hf
  congr
  funext k r xs
  exact propext (h r xs)

/-- Two structures of `L_b[L] ∪ L_c[L]` on `M` are equal when they have the same relations.
Native construction. -/
theorem templateStructure_ext {G G' : templateLanguage.{u}.Structure M}
    (h : ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → M),
      RelMap (L := templateLanguage.{u}) (self := G) r xs ↔
        RelMap (L := templateLanguage.{u}) (self := G') r xs) : G = G' := by
  obtain ⟨f, R⟩ := G
  obtain ⟨f', R'⟩ := G'
  have hf : @f = @f' := funext fun _ ↦ funext fun g ↦ Empty.elim g
  subst hf
  congr
  funext k r xs
  exact propext (h r xs)

/-! ### The projection of a structure -/

/-- **The projection `τ_β` of a legal class** [AFK26, Definition 4.16]: the class of the
truncation at the block stage `ω + ω · β`.  It is legal.
Correspondence with the printed definitions. -/
def LegalClass.project (β : Ordinal.{u}) {n : ℕ} (c : LegalClass.{u} n) : LegalClass.{u} n :=
  ⟨c.1.project (isSuccPrelimit_blockStage β), c.2.project _⟩

namespace LegalClass

variable {n : ℕ} {α β : Ordinal.{u}}

@[simp] theorem coe_project (c : LegalClass.{u} n) :
    (c.project β).1 = c.1.project (isSuccPrelimit_blockStage β) :=
  rfl

/-- `τ_α ∘ τ_β = τ_α` for `α ≤ β` ([AFK26, Definition 2.6 (c)], every pair of indices).
Correspondence with the printed definitions. -/
theorem project_project_of_le (c : LegalClass.{u} n) (h : α ≤ β) :
    (c.project β).project α = c.project α :=
  Subtype.ext (c.1.project_project_of_le _ _ (blockStage_mono h))

/-- `τ_β ∘ τ_α = τ_α` for `α ≤ β` ([AFK26, Definition 2.6 (c)], every pair of indices).
Correspondence with the printed definitions. -/
theorem project_project_of_ge (c : LegalClass.{u} n) (h : α ≤ β) :
    (c.project α).project β = c.project α :=
  Subtype.ext (c.1.project_project_of_ge _ _ (blockStage_mono h))

/-- Projection is idempotent.  Correspondence with the printed definitions. -/
@[simp] theorem project_project (c : LegalClass.{u} n) :
    (c.project β).project β = c.project β :=
  c.project_project_of_le le_rfl

end LegalClass

/-- The relations of the projection: `P_n` and `R_c` as in `G`, and `Q_c` when some `Q_{c*}` with
`τ_β(c*) = c` holds in `G`.  Correspondence with the printed definitions. -/
def projectRelMap (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) :
    ∀ {k : ℕ}, TemplateSymbol.{u} k → (Fin k → M) → Prop
  | _, TemplateSymbol.closed hn, xs =>
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.closed hn) xs
  | _, TemplateSymbol.invariant c hn, xs => ∃ c' : LegalClass.{u} _, c'.project β = c ∧
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c' hn) xs
  | _, TemplateSymbol.base c h0 hn, xs =>
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.base c h0 hn) xs

/-- **The `β`-projection of a structure** `τ_β(G)` [AFK26, Definition 2.7]: the same carrier;
every symbol of `L_c[L]` (`P_n`, `R_c`) holds as in `G`; `Q_c` holds of `x` exactly when there is
`c*` with `τ_β(c*) = c` and `G ⊨ Q_{c*}(x)`.  Correspondence with the printed definitions. -/
@[instance_reducible] def projectStructure (β : Ordinal.{u})
    (G : templateLanguage.{u}.Structure M) : templateLanguage.{u}.Structure M where
  funMap f := Empty.elim f
  RelMap r xs := projectRelMap β G r xs

section Projection

variable {α β : Ordinal.{u}} (G : templateLanguage.{u}.Structure M) {k : ℕ}

@[simp] theorem relMap_projectStructure_closed (hk : 0 < k) (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := projectStructure β G) (TemplateSymbol.closed hk)
      xs ↔ RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.closed hk) xs :=
  Iff.rfl

@[simp] theorem relMap_projectStructure_base (c : LegalClass.{u} k)
    (h0 : c.1.project (isSuccPrelimit_blockStage 0) = c.1) (hk : 0 < k) (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := projectStructure β G)
      (TemplateSymbol.base c h0 hk) xs ↔
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.base c h0 hk) xs :=
  Iff.rfl

@[simp] theorem relMap_projectStructure_invariant (c : LegalClass.{u} k) (hk : 0 < k)
    (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := projectStructure β G)
      (TemplateSymbol.invariant c hk) xs ↔ ∃ c' : LegalClass.{u} k, c'.project β = c ∧
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c' hk) xs :=
  Iff.rfl

/-- **Projections of structures compose to the lower one**: `τ_α(τ_β(G)) = τ_α(G)` for
`α ≤ β`.  Correspondence with the printed definitions. -/
theorem projectStructure_projectStructure_of_le (h : α ≤ β) :
    projectStructure α (projectStructure β G) = projectStructure α G := by
  refine templateStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk => exact Iff.rfl
  | base c h0 hk => exact Iff.rfl
  | invariant c hk =>
    simp only [relMap_projectStructure_invariant]
    constructor
    · rintro ⟨c', rfl, c'', rfl, hx⟩
      exact ⟨c'', (c''.project_project_of_le h).symm, hx⟩
    · rintro ⟨c', rfl, hx⟩
      exact ⟨c'.project β, c'.project_project_of_le h, c', rfl, hx⟩

/-- **Projecting to a higher stage after a lower one gives the lower one**:
`τ_β(τ_α(G)) = τ_α(G)` for `α ≤ β`.  Correspondence with the printed definitions. -/
theorem projectStructure_projectStructure_of_ge (h : α ≤ β) :
    projectStructure β (projectStructure α G) = projectStructure α G := by
  refine templateStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk => exact Iff.rfl
  | base c h0 hk => exact Iff.rfl
  | invariant c hk =>
    simp only [relMap_projectStructure_invariant]
    constructor
    · rintro ⟨c', rfl, c'', rfl, hx⟩
      exact ⟨c'', (c''.project_project_of_ge h).symm, hx⟩
    · rintro ⟨c', rfl, hx⟩
      exact ⟨c'.project α, c'.project_project_of_ge h, c', rfl, hx⟩

/-- **Projection of structures is idempotent.**  Correspondence with the printed definitions. -/
@[simp] theorem projectStructure_projectStructure :
    projectStructure β (projectStructure β G) = projectStructure β G :=
  projectStructure_projectStructure_of_le G le_rfl

/-- **The fixing stages are closed upward**: a structure fixed by `τ_α` is fixed by `τ_β` for
`α ≤ β`.  Correspondence with the printed definitions. -/
theorem projectStructure_eq_of_le (h : α ≤ β) (hG : projectStructure α G = G) :
    projectStructure β G = G := by
  rw [← hG]
  exact projectStructure_projectStructure_of_ge G h

/-- **Projection does not change the base reduct** ([AFK26, Definition 2.7], second clause).
Correspondence with the printed definitions. -/
@[simp] theorem baseReduct_projectStructure :
    baseReduct (projectStructure β G) = baseReduct G :=
  baseStructure_ext fun r _ ↦ by cases r <;> exact Iff.rfl

end Projection

/-- **The fixing stages** of a structure ([AFK26, Definitions 2.6 and 2.7]): the printed indices
`β < ω₁` with `τ_β(G) = G`.  `rank_τ(G)` is the least of them, when there is one.
Correspondence with the printed definitions. -/
def fixingStages (G : templateLanguage.{u}.Structure M) : Set Ordinal.{u} :=
  {β | β < ω₁ ∧ projectStructure β G = G}

/-- The fixing stages below `ω₁` are closed upward.  Correspondence with the printed definitions. -/
theorem mem_fixingStages_of_le {G : templateLanguage.{u}.Structure M} {α β : Ordinal.{u}}
    (hα : α ∈ fixingStages G) (h : α ≤ β) (hβ : β < ω₁) : β ∈ fixingStages G :=
  ⟨hβ, projectStructure_eq_of_le G h hα.2⟩

end

end VaughtConjecture

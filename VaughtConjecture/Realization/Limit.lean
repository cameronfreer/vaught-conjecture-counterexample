/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Expansion

/-!
# Gluing coherent model expansions at a limit block stage

Roadmap, Layer 2 (reduction of models) and the reduction of the main theorem to expansion
domains (condition 1, continuity at nonzero countable limits; output 5 of higher-stage
reconstruction, limit existence, in Layer 4); semantic contract, items 5 and 9.

Throughout, `δ` is a limit ordinal and `λ_ξ = ω + ω · ξ` is the block stage of index `ξ`
(`blockStage`).

**Block stages at a limit.**  Block stages form a normal function (`isNormal_blockStage`), so an
ordinal is below `λ_δ` exactly when it is below some earlier `λ_ξ` (`lt_blockStage_iff`), and so
is a label (`exists_lt_blockStage_of_lt`).

**Separation.**  A label occurring at `λ_δ` is determined by its reductions to the earlier block
stages (`Label.eq_of_forall_reduce_blockStage_eq`): a label below `λ_δ` is below some `λ_ξ`,
where reduction keeps it, and the formal top reduces to the formal top.  Hence a stage type at
`λ_δ` (`StageType.eq_of_forall_reduce_eq`), an optional stage type
(`StageType.option_eq_of_forall_map_reduce_eq`), and a realization at `λ_δ`
(`Realization.eq_of_forall_reduce_eq`) are determined by their stage reductions to the earlier
block stages.

**Coherent families and their stabilization.**  A family of stage types `t ξ` at `λ_ξ`, for
`ξ < δ`, is a **coherent family** (`StageType.IsCoherentFamily`) when `t ξ` reduces to `t ζ` for
every `ζ ≤ ξ`; likewise for realizations (`Realization.IsCoherentFamily`) and for model
expansions (the hypothesis `hcoh` of `ModelExpansion.nonempty_of_coherent`).  A coherent family
of stage types is eventually constant up to the reading of the stage
(`StageType.IsCoherentFamily.eq_castLE`): each cell either has the formal top as its label at
every index, or has a label below `λ_ξ` at some index `ξ` (its below-top index,
`StageType.belowTopIndex`) and the same label from there on; there are finitely many cells, so
from the largest below-top index (the stabilization index, `StageType.stableIndex`, below `δ`) on,
the types are the type at the stabilization index read at the larger stage (`StageType.castLE`).
The **glued type** (`StageType.glue`) is that type read at `λ_δ`; it reduces to every member of
the family (`StageType.IsCoherentFamily.glue_reduce`).  No label is constructed pointwise, so
lawfulness and well-formedness come with the type at the stabilization index.

**The glued realization.**  The glued realization of a family of realizations
(`Realization.glue`) types a tuple by the glued type of its types when it is typed at every
earlier block stage, and leaves it untyped otherwise; for a coherent family its stage reductions
are the members of the family (`Realization.IsCoherentFamily.glue_reduce`).  This gluing along a
limit of stages is unrelated to the gluing of lawful labellings of one cell scheme in
`VaughtConjecture.Extension.Gluing` (`Rows.IsLawfulBelow.glue`).

**Modelhood.**  A realization at `λ_δ` is a model exactly when its reductions to the earlier
block stages are (`Realization.isModel_iff_forall_reduce`).  The backward direction
(`Realization.IsModel.of_forall_reduce`) checks every clause of a model at `λ_δ`: legality and
covering from the reduction to `λ_0`, since reduction keeps the scheme and definedness; exact
consistency by separation of optional types, since reduction commutes with face maps; the
generalized-saturation and bottom-pattern clauses from the reduction to `λ_0`, since a coface
reduces to a coface and membership in those families depends only on the scheme and on which
labels are bottom (`StageType.reduce_mem_bottomPatternFamily_iff`); uniformity and dominance at
`γ < λ_δ` from the reduction to a block stage `λ_ξ > γ`, where reduction changes no label below
`γ + ω ≤ λ_ξ` (`StageType.mem_uniformityFamily_of_reduce`) and raises a label to the formal top
only from at least `λ_ξ > γ` (`StageType.mem_dominanceFamily_of_reduce`).  So the glued
realization of a coherent family of models is a model (`Realization.IsModel.glue`), and the
**glued expansion** of a coherent family of model expansions of a base structure
(`ModelExpansion.glue`) is a model expansion at `λ_δ` reducing to every member of the family
(`ModelExpansion.glue_reduceBlock`, `ModelExpansion.nonempty_of_coherent`).

This glues models and proves every clause of a model for the result; modelhood is not inferred
from the coherence of types (`roadmap/README.md`, Layer 4: coherent assignments are not models by
themselves).  Coherence is a hypothesis here.  It is not assumed in the definition of the
expansion domains (`VaughtConjecture.Expansion.Domains`); for the limit clause of condition 1 it
is to be derived from uniqueness of expansions (output 4 of higher-stage reconstruction), whose
successor step is the next-block uniqueness of models, a consequence of normalization (output 2 of
higher-stage reconstruction), still to be proved.  Countability of `δ` is not used.

## Placement

This file belongs to Layer 2 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Ordinal Label

variable {δ ξ : Ordinal.{u}} {n : ℕ}

/-! ### Block stages at a limit -/

/-- Block stages form a normal function: `ξ ↦ ω + ω · ξ`. -/
theorem isNormal_blockStage : Order.IsNormal (blockStage : Ordinal.{u} → Ordinal.{u}) :=
  (isNormal_add_right ω).comp (isNormal_mul_right omega0_pos)

/-- **Continuity of block stages at a limit**: below the block stage of a limit index `δ` are
exactly the ordinals below some earlier block stage. -/
theorem lt_blockStage_iff (hδ : Order.IsSuccLimit δ) {o : Ordinal.{u}} :
    o < blockStage δ ↔ ∃ ξ < δ, o < blockStage ξ :=
  isNormal_blockStage.lt_iff_exists_lt hδ

/-- A label below the block stage of a limit index is below some earlier block stage. -/
theorem exists_lt_blockStage_of_lt (hδ : Order.IsSuccLimit δ) {x : Label.{u}}
    (hx : x < (blockStage δ : Label.{u})) : ∃ ξ < δ, x < (blockStage ξ : Label.{u}) := by
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨0, hδ.pos, WithBot.bot_lt_coe _⟩
  | coe x =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd hx (not_lt.mpr (by exact_mod_cast le_top))
    | coe o =>
      obtain ⟨ξ, hξ, ho⟩ := (lt_blockStage_iff hδ).mp (by exact_mod_cast hx)
      exact ⟨ξ, hξ, by exact_mod_cast ho⟩

namespace Label

/-- **Labels at a limit block stage are separated by their reductions**: two labels occurring at
`λ_δ`, for a limit `δ`, with the same reduction to every earlier block stage are equal. -/
theorem eq_of_forall_reduce_blockStage_eq (hδ : Order.IsSuccLimit δ) {x y : Label.{u}}
    (hx : AtStage (blockStage δ) x) (hy : AtStage (blockStage δ) y)
    (h : ∀ ξ < δ, reduce (blockStage ξ) x = reduce (blockStage ξ) y) : x = y := by
  have key {x y : Label.{u}} (hx : x < (blockStage δ : Label.{u}))
      (h : ∀ ξ < δ, reduce (blockStage ξ) x = reduce (blockStage ξ) y) : x = y := by
    obtain ⟨ξ, hξ, hxξ⟩ := exists_lt_blockStage_of_lt hδ hx
    have hx' := reduce_of_lt hxξ
    have hy : y < (blockStage ξ : Label.{u}) := by
      rw [← reduce_lt_iff, ← h ξ hξ, hx']
      exact hxξ
    rw [← hx', h ξ hξ, reduce_of_lt hy]
  rcases hx with hx | rfl
  · exact key hx h
  rcases hy with hy | rfl
  · exact (key hy fun ξ hξ ↦ (h ξ hξ).symm).symm
  · rfl

end Label

namespace StageType

/-- **Separation at a limit block stage**: two stage types at `λ_δ`, for a limit `δ`, with the
same reduction to every earlier block stage are equal. -/
theorem eq_of_forall_reduce_eq (hδ : Order.IsSuccLimit δ)
    {t t' : StageType.{u} (blockStage δ) n}
    (h : ∀ ξ < δ,
      t.reduce (isSuccPrelimit_blockStage ξ) = t'.reduce (isSuccPrelimit_blockStage ξ)) :
    t = t' :=
  ext (congrArg (·.toScheme) (h 0 hδ.pos)) fun i j hij ↦
    Label.eq_of_forall_reduce_blockStage_eq hδ (t.atStage i) (t'.atStage j) fun ξ hξ ↦
      label_congr (h ξ hξ) hij

/-- **Separation of optional types at a limit block stage**: two optional stage types at `λ_δ`
with the same reduction to every earlier block stage are equal. -/
theorem option_eq_of_forall_map_reduce_eq (hδ : Order.IsSuccLimit δ)
    {a b : Option (StageType.{u} (blockStage δ) n)}
    (h : ∀ ξ < δ, a.map (reduce · (isSuccPrelimit_blockStage ξ)) =
      b.map (reduce · (isSuccPrelimit_blockStage ξ))) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some q => simpa using h 0 hδ.pos
  | some p => cases b with
    | none => simpa using h 0 hδ.pos
    | some q =>
      exact congrArg some (eq_of_forall_reduce_eq hδ fun ξ hξ ↦ by simpa using h ξ hξ)

/-! ### Coherent families of stage types -/

section Coherent

variable (hδ : Order.IsSuccLimit δ) (t : ∀ ξ < δ, StageType.{u} (blockStage ξ) n)

open Classical in
/-- The **below-top index** of the cell at position `k` in a family of stage types below `δ`: an
index at which the label of that cell is not the formal top, if there is one, and `0`
otherwise. -/
noncomputable def belowTopIndex (k : ℕ) : Ordinal.{u} :=
  if h : ∃ ξ, ∃ hξ : ξ < δ, ∃ i : Fin (t ξ hξ).card, (i : ℕ) = k ∧ (t ξ hξ).label i ≠ ⊤ then
    h.choose else 0

include hδ in
/-- A below-top index is below `δ`. -/
theorem belowTopIndex_lt (k : ℕ) : belowTopIndex t k < δ := by
  unfold belowTopIndex
  split_ifs with h
  · exact h.choose_spec.1
  · exact hδ.pos

/-- If the cell at position `k` has a label other than the formal top at some index, it has one at
its below-top index. -/
theorem belowTopIndex_spec {k : ℕ}
    (h : ∃ ξ, ∃ hξ : ξ < δ, ∃ i : Fin (t ξ hξ).card, (i : ℕ) = k ∧ (t ξ hξ).label i ≠ ⊤) :
    ∃ hξ : belowTopIndex t k < δ, ∃ i : Fin (t _ hξ).card, (i : ℕ) = k ∧ (t _ hξ).label i ≠ ⊤ := by
  have e : belowTopIndex t k = h.choose := by simp only [belowTopIndex, h, ↓reduceDIte]
  rw [e]
  exact h.choose_spec

/-- The **stabilization index** of a family of stage types below a limit `δ`: the largest
below-top index of a cell of the type at `0`. -/
noncomputable def stableIndex : Ordinal.{u} :=
  (Finset.range (t 0 hδ.pos).card).sup (belowTopIndex t)

/-- The stabilization index is below `δ`. -/
theorem stableIndex_lt : stableIndex hδ t < δ :=
  (Finset.sup_lt_iff (by simpa [Ordinal.bot_eq_zero] using hδ.pos)).mpr fun k _ ↦
    belowTopIndex_lt hδ t k

/-- A family of stage types below `δ` is a **coherent family** when the type at `ξ` reduces to
the type at every `ζ ≤ ξ`. -/
def IsCoherentFamily : Prop :=
  ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ), ζ ≤ ξ → (t ξ hξ).reduce (isSuccPrelimit_blockStage ζ) = t ζ hζ

variable {hδ t}

/-- The types of a coherent family have the same number of cells. -/
theorem IsCoherentFamily.card_eq (hc : IsCoherentFamily t) {ξ : Ordinal.{u}} (hξ : ξ < δ) :
    (t ξ hξ).card = (t 0 hδ.pos).card :=
  congrArg (·.card) (hc 0 hδ.pos ξ hξ zero_le)

/-- **Eventual stabilization of a coherent family**: from the stabilization index on, the types
of a coherent family below a limit are the type at the stabilization index, read at the larger
stage. -/
theorem IsCoherentFamily.eq_castLE (hc : IsCoherentFamily t) {ξ : Ordinal.{u}} (hξ : ξ < δ)
    (h : stableIndex hδ t ≤ ξ) :
    t ξ hξ = (t _ (stableIndex_lt hδ t)).castLE (blockStage_strictMono.le_iff_le.mpr h) := by
  set ξ₀ := stableIndex hδ t
  have h₀ := stableIndex_lt hδ t
  refine (ext (congrArg (·.toScheme) (hc ξ₀ h₀ ξ hξ h)) fun j i hji ↦ ?_)
  -- `j` a cell of `t ξ`, `i` the cell of `t ξ₀` at the same position
  have hred : Label.reduce (blockStage ξ₀) ((t ξ hξ).label j) = (t ξ₀ h₀).label i :=
    label_congr (hc ξ₀ h₀ ξ hξ h) hji
  -- `castLE` keeps the labels (`castLE_label`, by `rfl`); `rw [castLE_label]` does not apply,
  -- since `i` indexes the cells of the relabelled type
  change (t ξ hξ).label j = (t ξ₀ h₀).label i
  by_cases htop : (t ξ hξ).label j = ⊤
  · rw [← hred, htop, reduce_top]
  · rw [← hred, eq_comm, reduce_eq_self_iff]
    by_contra hns
    have hlt : ¬ (t ξ hξ).label j < (blockStage ξ₀ : Label.{u}) := fun hlt ↦ hns (.inl hlt)
    have htop₀ : (t ξ₀ h₀).label i = ⊤ := by
      rw [← hred]; exact reduce_of_le (not_lt.mp hlt)
    obtain ⟨hk, i', hi', hne⟩ := belowTopIndex_spec t ⟨ξ, hξ, j, rfl, htop⟩
    have hle : belowTopIndex t j ≤ ξ₀ :=
      Finset.le_sup (f := belowTopIndex t) (Finset.mem_range.mpr (hc.card_eq (hδ := hδ) hξ ▸ j.2))
    have h' := label_congr (hc _ hk ξ₀ h₀ hle) (i := i) (j := i') (by rw [hi', ← hji])
    exact hne (h'.symm.trans (show Label.reduce _ ((t ξ₀ h₀).label i) = ⊤ by
      rw [htop₀, reduce_top]))

/-- The **glued type** of a family of stage types below a limit `δ`: the type at the
stabilization index, read at the block stage `λ_δ`. -/
noncomputable def glue (hδ : Order.IsSuccLimit δ) (t : ∀ ξ < δ, StageType.{u} (blockStage ξ) n) :
    StageType.{u} (blockStage δ) n :=
  (t _ (stableIndex_lt hδ t)).castLE (blockStage_strictMono.le_iff_le.mpr (stableIndex_lt hδ t).le)

/-- **The glued type reduces to the family**: the reduction of the glued type of a coherent
family to an earlier block stage is the type of the family there. -/
theorem IsCoherentFamily.glue_reduce (hc : IsCoherentFamily t) {ξ : Ordinal.{u}} (hξ : ξ < δ) :
    (glue hδ t).reduce (isSuccPrelimit_blockStage ξ) = t ξ hξ := by
  rw [glue, reduce_castLE]
  rcases le_total ξ (stableIndex hδ t) with h | h
  · exact hc ξ hξ _ _ h
  · rw [reduce_eq_castLE _ _ (blockStage_strictMono.le_iff_le.mpr h), hc.eq_castLE hξ h]

end Coherent

/-! ### Stage reduction of the families, read backwards -/

variable {α β γ : Ordinal.{u}} {q : StageType.{u} α (n + 1)}

/-- A type is in a bottom-pattern family exactly when its stage reduction is: reduction keeps
the scheme and the bottom labels. -/
theorem reduce_mem_bottomPatternFamily_iff (hβ : Order.IsSuccPrelimit β)
    {S : Scheme.{u} (n + 1)} {ρ : Fin S.card → Label.{u}} :
    q.reduce hβ ∈ bottomPatternFamily S ρ ↔ q ∈ bottomPatternFamily S ρ :=
  ⟨fun h ↦ ⟨h.1, fun i j hij hg ↦ reduce_eq_bot_iff.symm.trans (h.2 i j hij hg)⟩,
    reduce_mem_bottomPatternFamily hβ⟩

/-- A type whose stage reduction to `β` is in the uniformity family of `γ < β` is in it: the
interval `[γ, γ + ω)` lies below `β`, where reduction changes no label. -/
theorem mem_uniformityFamily_of_reduce (hβ : Order.IsSuccPrelimit β) (hγ : γ < β)
    (h : q.reduce hβ ∈ uniformityFamily γ) : q ∈ uniformityFamily γ := by
  obtain ⟨d, hγd, hdγ⟩ := h
  -- the labels of `q.reduce hβ` are, by definition, the reductions of the labels of `q`
  change (γ : Label.{u}) ≤ Label.reduce β (q.label d) at hγd
  change Label.reduce β (q.label d) < ((γ + ω : Ordinal.{u}) : Label.{u}) at hdγ
  have hlt : Label.reduce β (q.label d) < β :=
    hdγ.trans_le (by exact_mod_cast Ordinal.add_omega0_le_of_isSuccPrelimit hβ hγ)
  rw [reduce_lt_iff] at hlt
  rw [reduce_of_lt hlt] at hγd hdγ
  exact ⟨d, hγd, hdγ⟩

/-- A type whose stage reduction to `β` is in the dominance family of `γ < β` is in it: a label
that reduction raises to the formal top is at least `β`, hence above `γ`. -/
theorem mem_dominanceFamily_of_reduce (hβ : Order.IsSuccPrelimit β) (hγ : γ < β)
    (h : q.reduce hβ ∈ dominanceFamily γ) : q ∈ dominanceFamily γ := by
  obtain ⟨d, hg, hd⟩ := h
  -- the labels of `q.reduce hβ` are, by definition, the reductions of the labels of `q`
  change (γ : Label.{u}) < Label.reduce β (q.label d) at hd
  refine ⟨d, hg, ?_⟩
  by_cases hlt : q.label d < β
  · rwa [reduce_of_lt hlt] at hd
  · exact (show (γ : Label.{u}) < β by exact_mod_cast hγ).trans_le (not_lt.mp hlt)

end StageType

namespace Realization

variable {M : Type v}

/-! ### Separation of realizations -/

/-- **Separation of realizations at a limit block stage**: two realizations at `λ_δ`, for a limit
`δ`, with the same stage reduction to every earlier block stage are equal. -/
theorem eq_of_forall_reduce_eq (hδ : Order.IsSuccLimit δ)
    {R R' : Realization.{u, v} (blockStage δ) M}
    (h : ∀ ξ < δ,
      R.reduce (isSuccPrelimit_blockStage ξ) = R'.reduce (isSuccPrelimit_blockStage ξ)) :
    R = R' :=
  ext fun t ↦ StageType.option_eq_of_forall_map_reduce_eq hδ fun ξ hξ ↦ by
    simpa using congrArg (fun R ↦ R.eval t) (h ξ hξ)

/-! ### Modelhood at a limit block stage -/

/-- Realizing a family in a stage reduction: if every type whose reduction is in `U'` is in `U`,
a realization of `U'` over `t` in the stage reduction of `R` is a realization of `U` in `R`. -/
theorem RealizesOver.of_reduce {α β : Ordinal.{u}} {R : Realization.{u, v} α M}
    (hβ : Order.IsSuccPrelimit β) {t : Fin n ↪ M} {U : Set (StageType.{u} α (n + 1))}
    {U' : Set (StageType.{u} β (n + 1))} (h : (R.reduce hβ).RealizesOver t U')
    (hU : ∀ q, q.reduce hβ ∈ U' → q ∈ U) : R.RealizesOver t U := by
  obtain ⟨u, hu, q', hq', he⟩ := h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
  exact ⟨u, hu, q, hU q hq', hq⟩

/-- **A realization at a limit block stage is a model when its reductions are**: if the stage
reduction of `R` to every earlier block stage is a model, `R` is a model.  Every clause is
checked at `λ_δ`: legality, covering and the guarded clauses from the reduction to `λ_0`;
exact consistency by separation of optional types; uniformity and dominance at `γ < λ_δ` from the
reduction to a block stage above `γ`, where reduction changes no label below `γ + ω` and raises a
label to the formal top only from above `γ`. -/
theorem IsModel.of_forall_reduce (hδ : Order.IsSuccLimit δ)
    {R : Realization.{u, v} (blockStage δ) M}
    (h : ∀ ξ < δ, (R.reduce (isSuccPrelimit_blockStage ξ)).IsModel) : R.IsModel := by
  have h0 := h 0 hδ.pos
  have hb0 := isSuccPrelimit_blockStage (0 : Ordinal.{u})
  refine ⟨h0.nonempty, fun n t p hp ↦ ?_, fun m n t p f hp ↦ ?_, ?_, fun x S hne ↦ ?_,
    fun x S ρ hne ↦ ?_, fun x γ hγ hγδ ↦ ?_, fun x γ hγδ ↦ ?_⟩
  · exact (StageType.isLegal_reduce_iff _).mp
      (h0.isLegal t _ (by rw [reduce_eval, hp, Option.map_some]))
  · refine StageType.option_eq_of_forall_map_reduce_eq hδ fun ξ hξ ↦ ?_
    rw [← reduce_eval, ← StageType.restrictFace_reduce]
    exact (h ξ hξ).isConsistent t _ f (by rw [reduce_eval, hp, Option.map_some])
  · exact (isCovering_reduce_iff _).mp h0.isCovering
  · obtain ⟨w, hw, hwS⟩ := hne
    exact (h0.saturation (x.reduce hb0) S ⟨w.reduce hb0, StageType.reduce_mem_cofaces hb0 hw,
      hwS⟩).of_reduce hb0 fun q hq ↦ hq
  · obtain ⟨w, hw, hwS⟩ := hne
    exact (h0.bottomPattern (x.reduce hb0) S ρ ⟨w.reduce hb0, StageType.reduce_mem_cofaces hb0 hw,
      StageType.reduce_mem_bottomPatternFamily hb0 hwS⟩).of_reduce hb0 fun q hq ↦
        (StageType.reduce_mem_bottomPatternFamily_iff hb0).mp hq
  · obtain ⟨ξ, hξ, hγξ⟩ := (lt_blockStage_iff hδ).mp hγδ
    exact ((h ξ hξ).uniformity (x.reduce _) γ hγ hγξ).of_reduce _ fun q hq ↦
      StageType.mem_uniformityFamily_of_reduce _ hγξ hq
  · obtain ⟨ξ, hξ, hγξ⟩ := (lt_blockStage_iff hδ).mp hγδ
    exact ((h ξ hξ).dominance (x.reduce _) γ hγξ).of_reduce _ fun q hq ↦
      StageType.mem_dominanceFamily_of_reduce _ hγξ hq

/-- **Modelhood at a limit block stage is modelhood of the reductions**: a realization at `λ_δ`,
for a limit `δ`, is a model exactly when its stage reduction to every earlier block stage is. -/
theorem isModel_iff_forall_reduce (hδ : Order.IsSuccLimit δ)
    {R : Realization.{u, v} (blockStage δ) M} :
    R.IsModel ↔ ∀ ξ < δ, (R.reduce (isSuccPrelimit_blockStage ξ)).IsModel :=
  ⟨fun hR ξ hξ ↦ hR.reduce (isSuccPrelimit_blockStage δ) (isSuccLimit_blockStage ξ)
    (blockStage_strictMono hξ).le, IsModel.of_forall_reduce hδ⟩

/-! ### Gluing a coherent family of realizations -/

section Glue

variable (R : ∀ ξ < δ, Realization.{u, v} (blockStage ξ) M)

/-- A family of realizations below `δ` is a **coherent family** when the realization at `ξ`
reduces to the realization at every `ζ ≤ ξ`. -/
def IsCoherentFamily : Prop :=
  ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ), ζ ≤ ξ → (R ξ hξ).reduce (isSuccPrelimit_blockStage ζ) = R ζ hζ

open Classical in
/-- The **glued realization** of a family of realizations below a limit `δ`: a tuple typed at
every earlier block stage has the glued type of its types, and any other tuple is untyped. -/
noncomputable def glue (hδ : Order.IsSuccLimit δ) : Realization.{u, v} (blockStage δ) M where
  eval t := if h : ∀ ξ (hξ : ξ < δ), ((R ξ hξ).eval t).isSome then
    some (StageType.glue hδ fun ξ hξ ↦ ((R ξ hξ).eval t).get (h ξ hξ)) else none

variable {R} {hδ : Order.IsSuccLimit δ}

/-- In a coherent family, a tuple is typed at one stage exactly when it is typed at `λ_0`. -/
theorem IsCoherentFamily.isSome_eval (hc : IsCoherentFamily R) {ξ : Ordinal.{u}} (hξ : ξ < δ)
    {n : ℕ} (t : Fin n ↪ M) :
    ((R ξ hξ).eval t).isSome = ((R 0 (hξ.trans_le' zero_le)).eval t).isSome := by
  rw [← hc 0 _ ξ hξ zero_le, isSome_reduce_eval]

/-- **The glued realization reduces to the family**: the stage reduction of the glued realization
of a coherent family to an earlier block stage is the realization of the family there. -/
theorem IsCoherentFamily.glue_reduce (hc : IsCoherentFamily R) {ξ : Ordinal.{u}} (hξ : ξ < δ) :
    (glue R hδ).reduce (isSuccPrelimit_blockStage ξ) = R ξ hξ := by
  ext n t : 1
  rw [reduce_eval]
  by_cases h : ∀ ζ (hζ : ζ < δ), ((R ζ hζ).eval t).isSome
  · have hcoh : StageType.IsCoherentFamily fun ζ hζ ↦ ((R ζ hζ).eval t).get (h ζ hζ) := by
      intro ζ hζ ξ' hξ' hle
      have := congrArg (fun R ↦ R.eval t) (hc ζ hζ ξ' hξ' hle)
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (h ξ' hξ')
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (h ζ hζ)
      simp only [reduce_eval, hp, hq, Option.map_some, Option.some_inj] at this
      simpa only [hp, hq, Option.get_some] using this
    simp only [glue, h, implies_true, ↓reduceDIte, Option.map_some, hcoh.glue_reduce hξ,
      Option.some_get]
  · have hn : (R ξ hξ).eval t = none := by
      push Not at h
      obtain ⟨ζ, hζ, hn⟩ := h
      rw [← Option.not_isSome_iff_eq_none, hc.isSome_eval hξ, ← hc.isSome_eval hζ]
      simpa using hn
    simp only [glue, h, ↓reduceDIte, Option.map_none, hn]

/-- **Gluing a coherent family of models**: the glued realization of a coherent family of models
below a limit `δ` is a model.  Its stage reductions are the models of the family
(`IsCoherentFamily.glue_reduce`), and every clause of a model is checked at `λ_δ`
(`IsModel.of_forall_reduce`). -/
theorem IsModel.glue (hc : IsCoherentFamily R) (hR : ∀ ξ (hξ : ξ < δ), (R ξ hξ).IsModel) :
    (glue R hδ).IsModel :=
  IsModel.of_forall_reduce hδ fun ξ hξ ↦ hc.glue_reduce hξ ▸ hR ξ hξ

end Glue

end Realization

/-! ### Gluing coherent model expansions -/

section ModelExpansion

variable {M : Type v} [baseLanguage.{u}.Structure M]

/-- The **glued expansion** of a coherent family of model expansions of `M` below a limit `δ`:
the glued realization, a model whose base reduct is that of the expansion at `λ_0`. -/
noncomputable def ModelExpansion.glue (hδ : Order.IsSuccLimit δ)
    (e : ∀ ξ < δ, ModelExpansion M (blockStage ξ))
    (hcoh : ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ) :
    ModelExpansion M (blockStage δ) :=
  have hc : Realization.IsCoherentFamily fun ξ hξ ↦ (e ξ hξ).1 :=
    fun ζ hζ ξ hξ h ↦ congrArg Subtype.val (hcoh ζ hζ ξ hξ h)
  ⟨Realization.glue (fun ξ hξ ↦ (e ξ hξ).1) hδ, Realization.IsModel.glue hc fun ξ hξ ↦
    (e ξ hξ).2.isModel, by
    rw [← Realization.reduce_reduce _ (isSuccPrelimit_blockStage 0) _ (omega0_le_blockStage 0),
      hc.glue_reduce hδ.pos]
    exact (e 0 hδ.pos).2.toStructure_reduce⟩

/-- **The glued expansion reduces to the family**: its reduction to an earlier block stage is the
expansion of the family there. -/
theorem ModelExpansion.glue_reduceBlock {hδ : Order.IsSuccLimit δ}
    {e : ∀ ξ < δ, ModelExpansion M (blockStage ξ)}
    (hcoh : ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ)
    {ξ : Ordinal.{u}} (hξ : ξ < δ) :
    (ModelExpansion.glue hδ e hcoh).reduceBlock hξ.le = e ξ hξ :=
  Subtype.ext (Realization.IsCoherentFamily.glue_reduce
    (fun ζ hζ ξ hξ h ↦ congrArg Subtype.val (hcoh ζ hζ ξ hξ h)) hξ)

/-- **A coherent family of model expansions below a limit glues to a model expansion at the
limit**: for a limit `δ` and model expansions `e ξ` of `M` to `λ_ξ`, `ξ < δ`, each reducing to the
earlier ones, `M` has a model expansion to `λ_δ`, the glued expansion (`ModelExpansion.glue`),
reducing to every `e ξ`.

This glues models and proves every clause of a model for the result
(`Realization.IsModel.of_forall_reduce`); it does not infer modelhood from the coherence of types
(`roadmap/README.md`, Layer 4: coherent assignments are not models by themselves).  Coherence
(`hcoh`) is a hypothesis here, stated for an arbitrary coherent family; it is not assumed in the
expansion domains, and for the limit clause of condition 1 it is to be derived from uniqueness of
expansions, whose successor step is the next-block uniqueness of models (to be stated as
`NextBlockUniqueness`; a consequence of normalization, output 2 of higher-stage reconstruction,
Layer 4, still to be proved).  Countability of `δ` is not used. -/
theorem ModelExpansion.nonempty_of_coherent (hδ : Order.IsSuccLimit δ)
    (e : ∀ ξ < δ, ModelExpansion M (blockStage ξ))
    (hcoh : ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ) :
    Nonempty (ModelExpansion M (blockStage δ)) :=
  ⟨ModelExpansion.glue hδ e hcoh⟩

end ModelExpansion

end VaughtConjecture

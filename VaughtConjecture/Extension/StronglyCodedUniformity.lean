/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.StronglyCodedForcingDonors
import VaughtConjecture.Realization.CapToModel

/-!
# Strongly coded uniformity donors

Roadmap, Layer 3, 3.4 (the uniformity instances) and Correspondence, item 1 (the strongly coded
legal stage types); semantic contract, item 5.  All results here are native constructions of this
repository.

Write `λ_η = blockStage η`.  The unrestricted coface instances
(`StageType.HasNonemptyCofaceInstances`, from the coatom extension property with apex,
`StageType.HasNonemptyCofaceInstances.of_hasApexCoatomExtensions`) give, over every legal stage
type, cofaces with a label in each block `[γ, γ + ω)` below the stage, but say nothing about
strong coding of their rows.  This file states and proves their strongly coded counterparts.

**Targets.**

* **The strongly coded uniformity donor** (`StageType.StronglyCodedUniformityDonorTarget η`): for
  every `ξ < η`, a strongly coded legal stage type on one point at `λ_η` with a label in
  `[λ_ξ, λ_ξ + ω)`.
* **Strongly coded uniformity cofaces** (`StageType.StronglyCodedUniformityCofaceTarget η`): for
  every strongly coded legal `Tp` at `λ_η` on `n` points and every `ξ < η`, a coface `d` of `Tp`
  (legal, with literal face `Tp` along `Fin.castSuccEmb`) with strongly coded rows and a **new**
  cell, of graded index `({Fin.last n}, 1)`, labelled in `[λ_ξ, λ_ξ + ω)`.  A cell whose scope
  contains the new point is not a cell of the face `Tp`.
* **The strongly coded coface instances** (`StageType.HasStronglyCodedCofaceInstances α`): the
  three fields of `StageType.HasNonemptyCofaceInstances α`, with strongly coded legal inputs and
  outputs with strongly coded rows (the outputs are legal by membership in the cofaces).
* **Uniformity from strongly coded receiving**
  (`Realization.StronglyCodedReceivingUniformityTarget α`): at a stage that is zero or a limit,
  a realization with strongly coded legal types and finite-cut receiving for the cofaces with
  strongly coded rows realizes, over every occurrence, a member of the uniformity family of every
  `γ < α` that is zero or a limit; the clause `Realization.IsModel.uniformity`, without
  modelhood.
* **Reference cells from strongly coded receiving**
  (`Realization.StronglyCodedReferenceCellsTarget α`): as
  `Realization.IsModel.exists_extend_uniformity`, the step of the acquisition of calibrated
  contexts that uses uniformity, for an exactly consistent realization with the premises of the
  previous target.

All five are proved here (`StageType.stronglyCodedUniformityDonorTarget`,
`StageType.stronglyCodedUniformityCofaceTarget`,
`StageType.HasStronglyCodedCofaceInstances.of_isSuccPrelimit`,
`Realization.stronglyCodedReceivingUniformityTarget`,
`Realization.stronglyCodedReferenceCellsTarget`), with no hypothesis beyond those displayed.

**The donor and its label.**  The donor at the block `[γ, γ + ω)` is the strongly coded legal
one-point stage type `StageType.exists_stronglyCoded_onePoint_label` (the strongly coded apex over
the cellless scheme, capped) with the label `γ + 1`
(`StageType.exists_stronglyCodedLegal_onePoint_add_one`).  Strong coding is a property of the
rows, not of the labels: the one row of the donor is the strongly coded apex row, strongly coded at
grade `1` whatever the label.  The condition on the label is self-visibility at `1`, which the
cap needs to be lawful: the block start `γ` is not self-visible at `1` and is excluded; `γ + 1`
is.  This is a condition on the label alone, separate from the bound of the range clause on the
finite parts of the row entries, which strong coding of the rows imposes and which the apex row
satisfies.  The
coface is the strongly coded pinned extension over the empty face
(`StageType.exists_stronglyCoded_pinned_extension_empty`); its new cell is the image of the donor's
cell, of scope the new point (`StageType.exists_gradedIndex_last_of_restrictFace`).

**Dominance and the amalgam over the empty face**, the other two instance fields: the strongly
coded pinned extension over the empty face, closed for dominance by the strongly coded tied apex
at the donor's cell (`StageType.exists_stronglyCoded_coface_mem_dominanceFamily`).

**Receiving.**  Uniformity and dominance follow from finite-cut receiving in any class containing
the instance (`Realization.HasFiniteCutReceivingIn.uniformity`,
`Realization.HasFiniteCutReceivingIn.dominance`), as in
`VaughtConjecture.Realization.CapToModel`.  The reference cells of
`Realization.IsModel.exists_extend_uniformity` need only exact consistency and the uniformity
clause (`Realization.exists_extend_uniformity_of_realizesOver`).  Generalized saturation and the
bottom pattern for schemes that are not strongly coded are not obtained, so modelhood is not
concluded.

## Placement

This file belongs to Layer 3, 3.4, of `roadmap/README.md`.

## References

The uniformity clause is [Kni26, Definition 3.2.1, clause 4(b)]; the nonemptiness of its instances
is [Kni26, Lemma 4.4.2].  The range clause is that of [AFK26, Definition "legal"].
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace StageType

/-! ### Targets -/

/-- **Target: the strongly coded uniformity donor** at `λ_η` (B.P1): for every `ξ < η`, a strongly
coded legal stage type on one point at `λ_η` in the uniformity family of `λ_ξ`, that is, with a
label in `[λ_ξ, λ_ξ + ω)`. -/
def StronglyCodedUniformityDonorTarget (η : Ordinal.{u}) : Prop :=
  ∀ ξ < η, ∃ d : StageType.{u} (blockStage η) (0 + 1), d.IsStronglyCodedLegal ∧
    d ∈ uniformityFamily (blockStage ξ)

/-- **Target: strongly coded uniformity cofaces** at `λ_η`, over an occurrence's type: for every
strongly coded legal `Tp` at `λ_η` on `n` points and every `ξ < η`, a coface `d` of `Tp` (legal,
with face `Tp` along `Fin.castSuccEmb`) with strongly coded rows and a new cell, of graded index
`({Fin.last n}, 1)`, labelled in `[λ_ξ, λ_ξ + ω)`. -/
def StronglyCodedUniformityCofaceTarget (η : Ordinal.{u}) : Prop :=
  ∀ ⦃n : ℕ⦄ (Tp : StageType.{u} (blockStage η) n), Tp.IsStronglyCodedLegal → ∀ ξ < η,
    ∃ d ∈ Tp.cofaces, d.rows.IsStronglyCoded ∧ ∃ j : Fin d.card,
      d.toCellScheme.gradedIndex j = ({Fin.last n}, 1) ∧
      ((blockStage ξ : Ordinal.{u}) : Label.{u}) ≤ d.label j ∧
      d.label j < ((blockStage ξ + Ordinal.omega0 : Ordinal.{u}) : Label.{u})

variable (α : Ordinal.{u}) in
/-- **The strongly coded coface instances** at a stage `α`: the three statements of
`StageType.HasNonemptyCofaceInstances α`, for strongly coded legal inputs, with outputs whose rows
are strongly coded.  The outputs are legal, as cofaces. -/
structure HasStronglyCodedCofaceInstances : Prop where
  /-- **The strongly coded amalgam over the empty face**: a strongly coded legal `P` on `n` points
  and a strongly coded legal `d` on one point are the faces, along the first `n` points and along
  the last point, of one coface of `P` with strongly coded rows. -/
  exists_amalgam_empty ⦃n : ℕ⦄ (P : StageType.{u} α n) (d : StageType.{u} α 1) :
    P.IsStronglyCodedLegal → d.IsStronglyCodedLegal →
      ∃ Q ∈ P.cofaces, Q.rows.IsStronglyCoded ∧ restrictFace (Fin.natAddEmb n) Q = some d
  /-- **Strongly coded uniformity instances**: for `γ` zero or a limit below `α`, some coface of a
  strongly coded legal stage type with strongly coded rows has a label in `[γ, γ + ω)`. -/
  uniformity ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsStronglyCodedLegal → ∀ γ : Ordinal.{u},
    Order.IsSuccPrelimit γ → γ < α →
      ∃ q ∈ p.cofaces ∩ uniformityFamily γ, q.rows.IsStronglyCoded
  /-- **Strongly coded dominance instances**: for `γ` below `α`, some coface of a strongly coded
  legal stage type on `n` points with strongly coded rows has a label above `γ` at a cell of grade
  `n + 1`. -/
  dominance ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsStronglyCodedLegal → ∀ γ : Ordinal.{u},
    γ < α → ∃ q ∈ p.cofaces ∩ dominanceFamily γ, q.rows.IsStronglyCoded

/-! ### The strongly coded pinned extension over the empty face -/

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The embedding of the one point as the last of `n + 1` points. -/
private theorem univ_map_extendByLast_ofIsEmpty :
    univ.map (extendByLast (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n)) = {Fin.last n} := by
  have h0 : (univ : Finset (Fin 1)) = {Fin.last 0} := rfl
  rw [h0, map_singleton, extendByLast_last]

/-- **The strongly coded pinned extension over the empty face** (native construction): at a stage
that is zero or a limit, a strongly coded legal `P` and a strongly coded legal one-point `d` are the
faces, along the initial segment and along the last point, of a coface of `P` with strongly coded
rows (`StageType.exists_stronglyCoded_pinned_extension`). -/
theorem exists_stronglyCoded_pinned_extension_empty (hα : Order.IsSuccPrelimit α)
    {P : StageType.{u} α n} (hP : P.IsStronglyCodedLegal) {d : StageType.{u} α 1}
    (hd : d.IsStronglyCodedLegal) :
    ∃ Q ∈ P.cofaces, Q.rows.IsStronglyCoded ∧
      restrictFace (extendByLast Function.Embedding.ofIsEmpty) Q = some d := by
  obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.mp
    (P.isSome_restrictFace_of_zero (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n))
  obtain ⟨Q, hQ, hQP, hQd⟩ := exists_stronglyCoded_pinned_extension
    (hasStronglyCodedApexCoatomExtensions hα) hP hp0 hd (mem_cofaces_of_zero hd.1).2
  exact ⟨Q, ⟨hQ.1, hQP⟩, hQ.2, hQd⟩

/-- **A cell of full scope of the face along the last point is a new cell**: if `d` is the face of
`Q` along the last point and the cell `i` of `d` has graded index `(univ, k)`, then `Q` has a cell
of graded index `({Fin.last n}, k)` with the label of `i`. -/
theorem exists_gradedIndex_last_of_restrictFace {Q : StageType.{u} α (n + 1)}
    {d : StageType.{u} α 1}
    (h : restrictFace (extendByLast (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n)) Q = some d)
    {i : Fin d.card} (hi : d.toCellScheme.gradedIndex i = (univ, k)) :
    ∃ j : Fin Q.card, Q.toCellScheme.gradedIndex j = ({Fin.last n}, k) ∧ Q.label j = d.label i := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff Q _).mp h
  refine ⟨Q.cellMap _ i, ?_, rfl⟩
  rw [← Q.toScheme.map_comap_gradedIndex _ i]
  change Prod.map _ id ((Q.comap _ hf).toCellScheme.gradedIndex i) = _
  rw [hi, Prod.map_apply, univ_map_extendByLast_ofIsEmpty]
  rfl

/-! ### The strongly coded uniformity donor -/

/-- **The strongly coded uniformity donor at the label `γ + 1`** (native construction): for `γ`
zero or a limit with `γ < α` and `α` zero or a limit, a strongly coded legal stage type on one point
with a cell of graded index `(univ, 1)` labelled `γ + 1`.  It is
`StageType.exists_stronglyCoded_onePoint_label` (the strongly coded apex over the cellless scheme,
capped at `γ + 1`): the label `γ + 1` is self-visible at `1`, which the cap needs; the label `γ`
is not self-visible at `1`.  This condition on the label is separate from the bound on the finite
parts of the row entries, which strong coding of the rows imposes: the one row is the strongly
coded apex row, whatever the label. -/
theorem exists_stronglyCodedLegal_onePoint_add_one (hα : Order.IsSuccPrelimit α)
    {γ : Ordinal.{u}} (hγ : Order.IsSuccPrelimit γ) (hγα : γ < α) :
    ∃ d : StageType.{u} α 1, d.IsStronglyCodedLegal ∧ ∃ i : Fin d.card,
      d.toCellScheme.gradedIndex i = (univ, 1) ∧
        d.label i = ((γ + 1 : Ordinal.{u}) : Label.{u}) := by
  have hv : IsSelfVisible 1 ((γ + 1 : Ordinal.{u}) : Label.{u}) := by
    simpa using isSelfVisible_coe_add (K := 1) hγ le_rfl
  obtain ⟨d, hd, i, hgi, hdi⟩ :=
    exists_stronglyCoded_onePoint_label hv (by simpa using hα.add_natCast_lt hγα 1)
  exact ⟨d, hd, i, gradedIndex_eq_univ_of_grade_eq d hgi, hdi⟩

/-- The label `γ + 1` lies in the block `[γ, γ + ω)`. -/
theorem coe_add_one_mem_block (γ : Ordinal.{u}) :
    ((γ : Ordinal.{u}) : Label.{u}) ≤ ((γ + 1 : Ordinal.{u}) : Label.{u}) ∧
      ((γ + 1 : Ordinal.{u}) : Label.{u}) < ((γ + Ordinal.omega0 : Ordinal.{u}) : Label.{u}) := by
  refine ⟨by exact_mod_cast (le_self_add : γ ≤ γ + 1), ?_⟩
  exact_mod_cast (add_lt_add_iff_left γ).mpr Ordinal.one_lt_omega0

/-- **Strongly coded uniformity cofaces at a new cell** (native construction): at a stage `α` that
is zero or a limit, for a strongly coded legal `p` on `n` points and `γ < α` zero or a limit, a
coface of `p` with strongly coded rows and a new cell, of graded index `({Fin.last n}, 1)`,
labelled `γ + 1`: the strongly coded pinned extension of `p` over the empty face with the donor
`StageType.exists_stronglyCodedLegal_onePoint_add_one`. -/
theorem exists_stronglyCoded_coface_label_add_one (hα : Order.IsSuccPrelimit α)
    {p : StageType.{u} α n} (hp : p.IsStronglyCodedLegal) {γ : Ordinal.{u}}
    (hγ : Order.IsSuccPrelimit γ) (hγα : γ < α) :
    ∃ q ∈ p.cofaces, q.rows.IsStronglyCoded ∧ ∃ j : Fin q.card,
      q.toCellScheme.gradedIndex j = ({Fin.last n}, 1) ∧
      q.label j = ((γ + 1 : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨d, hd, i, hgi, hdi⟩ := exists_stronglyCodedLegal_onePoint_add_one hα hγ hγα
  obtain ⟨q, hq, hqs, hqd⟩ := exists_stronglyCoded_pinned_extension_empty hα hp hd
  obtain ⟨j, hj, hjl⟩ := exists_gradedIndex_last_of_restrictFace hqd hgi
  exact ⟨q, hq, hqs, j, hj, hjl.trans hdi⟩

/-- **Target B.P1, the strongly coded uniformity donor** (native construction), at every block
index: the donor of `StageType.exists_stronglyCodedLegal_onePoint_add_one` at `γ = λ_ξ`, labelled
`λ_ξ + 1`. -/
theorem stronglyCodedUniformityDonorTarget (η : Ordinal.{u}) :
    StronglyCodedUniformityDonorTarget η := fun ξ hξ ↦ by
  obtain ⟨d, hd, i, -, hdi⟩ := exists_stronglyCodedLegal_onePoint_add_one
    (isSuccPrelimit_blockStage η) (isSuccPrelimit_blockStage ξ) (blockStage_strictMono hξ)
  exact ⟨d, hd, i, hdi ▸ coe_add_one_mem_block _⟩

/-- **Target: strongly coded uniformity cofaces** (native construction), at every block index:
`StageType.exists_stronglyCoded_coface_label_add_one` at `γ = λ_ξ`, with the new cell labelled
`λ_ξ + 1`. -/
theorem stronglyCodedUniformityCofaceTarget (η : Ordinal.{u}) :
    StronglyCodedUniformityCofaceTarget η := fun _ _ hTp ξ hξ ↦ by
  obtain ⟨d, hd, hds, j, hj, hjl⟩ := exists_stronglyCoded_coface_label_add_one
    (isSuccPrelimit_blockStage η) hTp (isSuccPrelimit_blockStage ξ) (blockStage_strictMono hξ)
  exact ⟨d, hd, hds, j, hj, hjl ▸ coe_add_one_mem_block _⟩

/-! ### The strongly coded coface instances -/

/-- The initial segment is a proper face. -/
private theorem univ_map_castSuccEmb_ne : univ.map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) ≠ univ :=
  fun he ↦ by
    have h := mem_univ (Fin.last n)
    rw [← he] at h
    simp at h

/-- The last point is a proper face of at least two points. -/
private theorem univ_map_extendByLast_ofIsEmpty_ne :
    univ.map (extendByLast (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin (k + 1))) ≠ univ := by
  rw [univ_map_extendByLast_ofIsEmpty]
  intro he
  have h := mem_univ (0 : Fin (k + 2))
  rw [← he, mem_singleton] at h
  exact absurd (congrArg Fin.val h) (by simp)

/-- **Strongly coded dominance instances** (native construction): at a stage `α` that is zero or a
limit, for a strongly coded legal `p` on `n` points and `γ < α`, a coface of `p` with strongly coded
rows and a cell of grade `n + 1` labelled above `γ`.  The donor is a strongly coded legal one-point
type labelled `c ∈ (γ, α)` self-visible at `n + 1`; for `n = 0` it is the coface.  Otherwise the
strongly coded pinned extension of `p` over the empty face with that donor is closed by the
strongly coded tied apex at the donor's cell (`StageType.exists_stronglyCodedLegal_tiedApex`),
which keeps the proper faces, the initial segment among them. -/
theorem exists_stronglyCoded_coface_mem_dominanceFamily (hα : Order.IsSuccPrelimit α)
    {p : StageType.{u} α n} (hp : p.IsStronglyCodedLegal) {γ : Ordinal.{u}} (hγα : γ < α) :
    ∃ q ∈ p.cofaces ∩ dominanceFamily γ, q.rows.IsStronglyCoded := by
  obtain ⟨c, hγc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα hγα (n + 1)
  obtain ⟨d, hd, i, hgi, hdi⟩ :=
    exists_stronglyCoded_onePoint_label (hc.mono (by omega : 1 ≤ n + 1)) hcα
  have hγd : (γ : Label.{u}) < d.label i := by rw [hdi]; exact_mod_cast hγc
  cases n with
  | zero => exact ⟨d, ⟨mem_cofaces_of_zero hd.1, i, hgi, hγd⟩, hd.2⟩
  | succ n =>
    obtain ⟨Q, hQ, hQs, hQd⟩ := exists_stronglyCoded_pinned_extension_empty hα hp hd
    obtain ⟨U, hU, hface, x, hx, hxl⟩ := exists_stronglyCodedLegal_tiedApex ⟨hQ.1, hQs⟩
      univ_map_extendByLast_ofIsEmpty_ne hQd i (by rw [hdi]; exact hc)
    refine ⟨U, ⟨⟨hU.1, ?_⟩, x, hx, hxl ▸ hγd⟩, hU.2⟩
    rw [hface _ univ_map_castSuccEmb_ne]
    exact hQ.2

/-- **The strongly coded coface instances** (native construction) at every stage that is zero or a
limit: the amalgam over the empty face is the strongly coded pinned extension over the empty face,
read along the last point; uniformity is
`StageType.exists_stronglyCoded_coface_label_add_one` (label `γ + 1`); dominance is
`StageType.exists_stronglyCoded_coface_mem_dominanceFamily`. -/
theorem HasStronglyCodedCofaceInstances.of_isSuccPrelimit (hα : Order.IsSuccPrelimit α) :
    HasStronglyCodedCofaceInstances α where
  exists_amalgam_empty n _ _ hP hd := by
    obtain ⟨Q, hQ, hQs, hQd⟩ := exists_stronglyCoded_pinned_extension_empty hα hP hd
    have he : Fin.natAddEmb n = extendByLast (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n) :=
      Function.Embedding.ext fun i ↦ by
        obtain rfl : i = Fin.last 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
        rw [extendByLast_last]
        rfl
    exact ⟨Q, hQ, hQs, he ▸ hQd⟩
  uniformity _ _ hp γ hγ hγα := by
    obtain ⟨q, hq, hqs, j, -, hjl⟩ := exists_stronglyCoded_coface_label_add_one hα hp hγ hγα
    exact ⟨q, ⟨hq, j, hjl ▸ coe_add_one_mem_block γ⟩, hqs⟩
  dominance _ _ hp _ hγα := exists_stronglyCoded_coface_mem_dominanceFamily hα hp hγα

end StageType

namespace Realization

open StageType

variable (α : Ordinal.{u}) (M : Type v)

/-- **Target: uniformity from strongly coded receiving** at a stage `α` that is zero or a limit:
every realization `R` on `M` with strongly coded legal types and finite-cut receiving for the
cofaces with strongly coded rows realizes, over every occurrence `x`, a member of the uniformity
family of every `γ < α` that is zero or a limit. -/
def StronglyCodedReceivingUniformityTarget : Prop :=
  Order.IsSuccPrelimit α → ∀ R : Realization.{u, v} α M,
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ∀ (x : R.Occurrence) (γ : Ordinal.{u}), Order.IsSuccPrelimit γ → γ < α →
      R.RealizesOver x.tuple (uniformityFamily γ)

/-- **Target: reference cells from strongly coded receiving** at a stage `α` that is zero or a
limit: as `Realization.IsModel.exists_extend_uniformity`, for an exactly consistent realization
`R` with strongly coded legal types and finite-cut receiving for the cofaces with strongly coded
rows.  For a list `L` of ordinals that are zero or limits below `α` and `γ < α`, an occurrence `y`
containing `x` as a literal face along `f`, with a bound `K` on finite parts and a floor `B`,
`γ ≤ B < α`, and for every `μ ∈ L` a cell of the type of `y` labelled `μ + k`, `k < K`,
`μ + k ≤ B`. -/
def StronglyCodedReferenceCellsTarget : Prop :=
  Order.IsSuccPrelimit α → ∀ R : Realization.{u, v} α M, R.IsConsistent →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ∀ (x : R.Occurrence) {γ : Ordinal.{u}}, γ < α → ∀ (L : List Ordinal.{u}),
      (∀ μ ∈ L, Order.IsSuccPrelimit μ ∧ μ < α) →
      ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (K : ℕ) (B : Ordinal.{u}),
        f.trans y.tuple = x.tuple ∧ γ ≤ B ∧ B < α ∧
          ∀ μ ∈ L, ∃ z, ∃ k < K,
            y.type.label z = ((μ + k : Ordinal.{u}) : Label.{u}) ∧ μ + k ≤ B

/-! ### Uniformity and dominance from receiving in a class -/

section Receiving

variable {α M} {R : Realization.{u, v} α M}
  {𝒮 : ∀ {α : Ordinal.{u}} {n : ℕ}, StageType.{u} α n → Prop}

/-- **Uniformity from receiving in a class** (native construction): as
`Realization.HasFiniteCutReceiving.uniformity`, for finite-cut receiving in a class `𝒮` and a
coface in `𝒮` with a label `L` in `[γ, γ + ω)`, received at the cutoff `L + 1`. -/
theorem HasFiniteCutReceivingIn.uniformity (hr : R.HasFiniteCutReceivingIn 𝒮)
    (hα : Order.IsSuccPrelimit α) (x : R.Occurrence) (γ : Ordinal.{u})
    (hne : ∃ d ∈ x.type.cofaces ∩ uniformityFamily γ, 𝒮 d) :
    R.RealizesOver x.tuple (uniformityFamily γ) := by
  obtain ⟨d, ⟨hd, j, hγj, hjγ⟩, hd𝒮⟩ := hne
  induction h : d.label j using recBotCoeTop with
  | bot => rw [h] at hγj; exact absurd hγj (not_le.mpr (WithBot.bot_lt_coe _))
  | top => rw [h] at hjγ; exact absurd hjγ (not_lt.mpr le_top)
  | coe L =>
    rw [h] at hγj hjγ
    have hLα : L < α := atStage_coe.mp (h ▸ d.atStage j)
    exact (hr x d hd hd𝒮 _
      (isPermittedCutoff_coe.mpr (by simpa using hα.add_natCast_lt hLα 1))).mono
      (receivingFamily_subset_uniformityFamily h (by exact_mod_cast hγj) (by exact_mod_cast hjγ))

/-- **High-arity dominance from receiving in a class** (native construction): as
`Realization.HasFiniteCutReceiving.dominance`, for finite-cut receiving in a class `𝒮` and a
coface in `𝒮` with a label above `γ` at a cell of full grade, received at the cutoff `γ + 1`. -/
theorem HasFiniteCutReceivingIn.dominance (hr : R.HasFiniteCutReceivingIn 𝒮)
    (hα : Order.IsSuccPrelimit α) (x : R.Occurrence) {γ : Ordinal.{u}} (hγα : γ < α)
    (hne : ∃ d ∈ x.type.cofaces ∩ dominanceFamily γ, 𝒮 d) :
    R.RealizesOver x.tuple (dominanceFamily γ) := by
  obtain ⟨d, ⟨hd, hdγ⟩, hd𝒮⟩ := hne
  exact (hr x d hd hd𝒮 _
    (isPermittedCutoff_coe.mpr (by simpa using hα.add_natCast_lt hγα 1))).mono
    (receivingFamily_subset_dominanceFamily hdγ)

/-- **The uniformity clause from strongly coded receiving and the strongly coded instances**
(native construction): for a realization with strongly coded legal types and finite-cut receiving
for the cofaces with strongly coded rows, the uniformity field of
`StageType.HasStronglyCodedCofaceInstances α` at the type of an occurrence takes the place of the
uniformity field of `StageType.HasNonemptyCofaceInstances α`. -/
theorem HasFiniteCutReceivingIn.uniformity_of_hasStronglyCodedCofaceInstances
    (hinst : HasStronglyCodedCofaceInstances α) (hα : Order.IsSuccPrelimit α)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal)
    (hr : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded) (x : R.Occurrence)
    (γ : Ordinal.{u}) (hγ : Order.IsSuccPrelimit γ) (hγα : γ < α) :
    R.RealizesOver x.tuple (uniformityFamily γ) :=
  hr.uniformity hα x γ (hinst.uniformity x.type (hsc _ _ x.eval_tuple) γ hγ hγα)

/-- **The dominance clause from strongly coded receiving and the strongly coded instances**
(native construction): as
`Realization.HasFiniteCutReceivingIn.uniformity_of_hasStronglyCodedCofaceInstances`, for the
dominance field. -/
theorem HasFiniteCutReceivingIn.dominance_of_hasStronglyCodedCofaceInstances
    (hinst : HasStronglyCodedCofaceInstances α) (hα : Order.IsSuccPrelimit α)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal)
    (hr : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded) (x : R.Occurrence)
    {γ : Ordinal.{u}} (hγα : γ < α) : R.RealizesOver x.tuple (dominanceFamily γ) :=
  hr.dominance hα x hγα (hinst.dominance x.type (hsc _ _ x.eval_tuple) γ hγα)

/-- **Reference cells from uniformity** (native construction): as
`Realization.IsModel.exists_extend_uniformity`, for an exactly consistent realization that
realizes, over every occurrence, a member of the uniformity family of every `μ < α` that is zero
or a limit (`hunif`); no other clause of a model is used. -/
theorem exists_extend_uniformity_of_realizesOver (hR : R.IsConsistent)
    (hunif : ∀ (x : R.Occurrence) (μ : Ordinal.{u}), Order.IsSuccPrelimit μ → μ < α →
      R.RealizesOver x.tuple (uniformityFamily μ))
    (x : R.Occurrence) {γ : Ordinal.{u}} (hγ : γ < α) (L : List Ordinal.{u})
    (hL : ∀ μ ∈ L, Order.IsSuccPrelimit μ ∧ μ < α) :
    ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (K : ℕ) (B : Ordinal.{u}),
      f.trans y.tuple = x.tuple ∧ γ ≤ B ∧ B < α ∧
        ∀ μ ∈ L, ∃ z, ∃ k < K,
          y.type.label z = ((μ + k : Ordinal.{u}) : Label.{u}) ∧ μ + k ≤ B := by
  induction L generalizing x with
  | nil => exact ⟨x, Function.Embedding.refl _, 0, γ, rfl, le_rfl, hγ, by simp⟩
  | cons μ L ih =>
    obtain ⟨hμ, hμα⟩ := hL μ List.mem_cons_self
    obtain ⟨u, hu, q, ⟨c, hc₁, hc₂⟩, he⟩ := hunif x μ hμ hμα
    obtain ⟨o, ho, hco⟩ : ∃ o < α, (o : Label.{u}) = q.label c := by
      rcases atStage_iff.mp (q.atStage c) with h | h | h
      · exact absurd hc₁ (by simp [h])
      · exact h
      · exact absurd hc₂ (by simp [h])
    rw [← hco] at hc₁ hc₂
    obtain ⟨k, rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
      (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hc₁))
      (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hc₂))
    obtain ⟨y, f, K, B, hf, hγB, hBα, hanc⟩ :=
      ih ⟨_, u, q, he⟩ fun ν hν ↦ hL ν (List.mem_cons_of_mem _ hν)
    obtain ⟨z, hz⟩ := Occurrence.exists_label_eq_of_trans_eq hR hf c
    refine ⟨y, Fin.castSuccEmb.trans f, K + k + 1, max B (μ + k), ?_, le_max_of_le_left hγB,
      max_lt hBα ho, fun ν hν ↦ ?_⟩
    · rw [Function.Embedding.trans_assoc, hf, ← hu]
    rcases List.mem_cons.mp hν with rfl | hν
    · exact ⟨z, k, by omega, hz.trans hco.symm, le_max_right _ _⟩
    · obtain ⟨z', k', hk', hz', hB⟩ := hanc ν hν
      exact ⟨z', k', by omega, hz', le_max_of_le_left hB⟩

end Receiving

/-- **Target: uniformity from strongly coded receiving** (native construction):
`Realization.HasFiniteCutReceivingIn.uniformity_of_hasStronglyCodedCofaceInstances` with the
instances `StageType.HasStronglyCodedCofaceInstances.of_isSuccPrelimit`. -/
theorem stronglyCodedReceivingUniformityTarget : StronglyCodedReceivingUniformityTarget α M :=
  fun hα _ hsc hr x γ hγ hγα ↦
    hr.uniformity_of_hasStronglyCodedCofaceInstances
      (HasStronglyCodedCofaceInstances.of_isSuccPrelimit hα) hα hsc x γ hγ hγα

/-- **Target: reference cells from strongly coded receiving** (native construction):
`Realization.exists_extend_uniformity_of_realizesOver` with the uniformity of
`Realization.stronglyCodedReceivingUniformityTarget`. -/
theorem stronglyCodedReferenceCellsTarget : StronglyCodedReferenceCellsTarget α M :=
  fun hα R hR hsc hr x _ hγ L hL ↦
    exists_extend_uniformity_of_realizesOver hR
      (stronglyCodedReceivingUniformityTarget α M hα R hsc hr) x hγ L hL

end Realization

end VaughtConjecture

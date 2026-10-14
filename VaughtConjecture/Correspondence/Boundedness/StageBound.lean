/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Boundedness.Targets
import VaughtConjecture.Correspondence.Reconstruction.Reconstruction
import VaughtConjecture.Extension.StronglyCodedUniformity

/-!
# The stage bound

Numbering as in the current draft of [AFK26].  Write `λ_ξ = blockStage ξ = ω + ω · ξ`.  `τ_ξ` is
`projectStructure ξ`, `K_β[L]` is `templateStageClass M β`, and `N↾L_c[L]` is `baseReduct N`.

**The donors** (native construction).  The premise `HasStronglyCodedUniformityDonors` of the
conditional stage bound holds (`hasStronglyCodedUniformityDonors`): it is
`StageType.stronglyCodedUniformityDonorTarget η` at every `η`, with no bound on `η`.

**The cell count and the labels of a class** (native construction).  A class of stage types up to
cell renaming has a number of cells (`TemplateClass.cellCount`) and a set of labels
(`TemplateClass.labels`), read from any representative: a renaming is a bijection of cells that
carries the labels along.  Stage reduction keeps the cell count
(`TemplateClass.cellCount_reduce`) and keeps every label below the stage of the reduction
(`TemplateClass.mem_labels_of_mem_labels_reduce`).  An observation at a cutoff `x` keeps every
label of the donor below `x` (`TemplateClass.ObservesAt.mem_labels`).  No cell is identified by
its grade or by its position: cells are compared only through the labels of one representative,
and the bijection of cells behind an equality of classes is never fixed.

**Statements of this file.**

* `TemplateClass.cellCount_reduce`, `ClassRealization.cellCount_eq_of_reduce_eval_eq`: the cell
  count of the class of a tuple does not change under stage reduction of the class realization.
* `exists_onePoint_isInBlock`: for a lift `G ∈ K_γ[L]`, `γ < ω₁`, and `ξ + 1 < γ`, some point of
  the carrier has a one-point class in the decoded class realization of `G` with a label in the
  block `[λ_ξ, λ_ξ + ω)`.  Donor density (`mem_templateStageClass_iff`) at the cutoff
  `λ_ξ + ω = λ_{ξ+1} < λ_γ` with a strongly coded uniformity donor at `λ_γ`; the label `λ_ξ` itself
  is not used.
* `decode_reduce_eq_decode_of_baseReduct_eq`, `reduce_eq_of_baseReduct_eq`,
  `cellCount_eq_of_baseReduct_eq` (correspondence with the printed definitions): on a countable
  carrier, of two lifts of one base structure at stages `ξ ≤ ζ < ω₁`, the decoded class
  realization of the higher one reduces at `λ_ξ` to that of the lower one (B.T9 and B.T10), so the
  class of a tuple in the lower lift is the reduction of its class in the higher lift, with the
  same cell count.
* `stageBoundOfDonorsTarget`, `stageBoundTarget`, `boundednessTarget` (correspondence with the
  printed definitions): the stage bound, conditional on the donors and then unconditional, and
  B.T15, Boundedness [AFK26, Proposition 4.34], for every carrier `M` (the targets carry
  `Countable M` as a premise).

**The pigeonhole.**  If the lift stages of `B` were unbounded below `ω₁`, each block
`[λ_ξ, λ_ξ + ω)`, `ξ < ω₁`, would be witnessed by a label of the one-point class of some point in
some lift; the carrier being countable and `ω₁` not, one point `x` witnesses infinitely many
blocks.  The cell count `N` of the class of `x` is the same in every lift.  Finitely many of the
witnessing lifts, for `N + 1` blocks, are reductions of the one at the largest of their stages, and
each witnessed label lies below the stage of its own lift, so it is a label of the one class of
`x` in that largest lift: `N + 1` distinct labels of a class with `N` cells.

**Rank and stage.**  Boundedness uses only that the rank of a lift is at most its stage
(`rankLeStageTarget`); the rank is never identified with the stage, and no Scott rank enters.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### The donors -/

/-- **The strongly coded uniformity donors exist** (native construction): for `ξ < η`, the donor
of `StageType.stronglyCodedUniformityDonorTarget η` at `ξ`, a strongly coded legal stage type on
one point at `λ_η` with a label in `[λ_ξ, λ_ξ + ω)`.  No bound on `η`. -/
theorem hasStronglyCodedUniformityDonors : HasStronglyCodedUniformityDonors.{u} :=
  fun ξ η hξη ↦ StageType.stronglyCodedUniformityDonorTarget η ξ hξη

/-- **Boundedness from the conditional stage bound**: B.T15 holds on `M` as soon as the stage
bound conditional on the strongly coded uniformity donors does, the donors being
`hasStronglyCodedUniformityDonors`.  Correspondence with the printed definitions. -/
theorem boundednessTarget_of_stageBoundOfDonorsTarget {M : Type v}
    (h : StageBoundOfDonorsTarget.{u} M) : BoundednessTarget.{u} M :=
  boundednessTarget_of_hasStronglyCodedUniformityDonors h hasStronglyCodedUniformityDonors

/-! ### The cell count and the labels of a class -/

namespace TemplateClass

open StageType

variable {α β : Ordinal.{u}} {n : ℕ}

/-- **The cell count of a class**: the number of cells of any representative.  Well defined since
a cell renaming has as many cells (`StageType.IsCellRenaming.card_eq`).  Native construction. -/
def cellCount (c : TemplateClass.{u} α n) : ℕ :=
  Quotient.lift (fun t : StageType.{u} α n ↦ t.card)
    (fun _ _ h ↦ (IsCellRenaming.card_eq h).symm) c

@[simp] theorem cellCount_toClass (t : StageType.{u} α n) : t.toClass.cellCount = t.card :=
  rfl

/-- **Stage reduction keeps the cell count.**  Native construction. -/
@[simp] theorem cellCount_reduce (hβ : Order.IsSuccPrelimit β) (c : TemplateClass.{u} α n) :
    (c.reduce hβ).cellCount = c.cellCount :=
  Quotient.inductionOn c fun _ ↦ rfl

/-- **The labels of a class**: the labels of the cells of any representative.  Well defined since
a renaming carries the labels along its bijection of cells (`StageType.range_label_renameCells`).
Native construction. -/
def labels (c : TemplateClass.{u} α n) : Set Label.{u} :=
  Quotient.lift (fun t : StageType.{u} α n ↦ Set.range t.label) (fun a _ h ↦ by
    obtain ⟨_, σ, rfl⟩ := h
    exact (range_label_renameCells a σ).symm) c

@[simp] theorem labels_toClass (t : StageType.{u} α n) : t.toClass.labels = Set.range t.label :=
  rfl

/-- **Stage reduction keeps the labels below the stage**: a label `ℓ < β` of the reduction of a
class to `β` is a label of the class.  A label at or above `β` reduces to `⊤`.
Native construction. -/
theorem mem_labels_of_mem_labels_reduce (hβ : Order.IsSuccPrelimit β) {c : TemplateClass.{u} α n}
    {ℓ : Label.{u}} (h : ℓ ∈ (c.reduce hβ).labels) (hℓ : ℓ < (β : Label.{u})) : ℓ ∈ c.labels := by
  induction c using Quotient.inductionOn with
  | h t =>
    change ℓ ∈ Set.range (t.reduce hβ).label at h
    obtain ⟨i, rfl⟩ := h
    exact ⟨i, (Label.reduce_of_lt (Label.reduce_lt_iff.mp hℓ)).symm⟩

/-- **An observation keeps the labels of the donor below the cutoff**: if `q` observes `D` at `x`
up to renaming, every label `ℓ < x` of `D` is a label of `q`.  Native construction. -/
theorem ObservesAt.mem_labels {x ℓ : Label.{u}} {q D : TemplateClass.{u} α n}
    (h : q.ObservesAt x D) (hℓ : ℓ ∈ D.labels) (hℓx : ℓ < x) : ℓ ∈ q.labels := by
  obtain ⟨s, u, rfl, rfl, hS, hl⟩ := h
  obtain ⟨j, rfl⟩ := hℓ
  have hc : s.card = u.card := congrArg Scheme.card hS
  have hj : min (s.label (Fin.cast hc.symm j)) x = min (u.label j) x := hl _ j rfl
  rw [min_eq_left hℓx.le] at hj
  refine ⟨Fin.cast hc.symm j, ?_⟩
  rcases le_total (s.label (Fin.cast hc.symm j)) x with h' | h'
  · rwa [min_eq_left h'] at hj
  · rw [min_eq_right h'] at hj
    exact absurd hj hℓx.ne'

/-- **Labels in distinct places bound the cell count**: if `f` is injective on a finite set `T`
and sends `T` into the labels of a class, then `T` has at most as many elements as the class has
cells.  Native construction. -/
theorem card_le_cellCount {ι : Type*} {T : Finset ι} {f : ι → Label.{u}} (hf : Set.InjOn f T)
    {c : TemplateClass.{u} α n} (hT : ∀ i ∈ T, f i ∈ c.labels) : T.card ≤ c.cellCount := by
  classical
  induction c using Quotient.inductionOn with
  | h t =>
    change ∀ i ∈ T, f i ∈ Set.range t.label at hT
    calc T.card = (T.image f).card := (Finset.card_image_of_injOn hf).symm
      _ ≤ (Finset.univ.image t.label).card := Finset.card_le_card fun a ha ↦ by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨j, hj⟩ := hT i hi
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = t.card := by simp

end TemplateClass

namespace ClassRealization

variable {α β : Ordinal.{u}} {M : Type v} {n : ℕ}

/-- **The class of a tuple in a reduction is the reduction of its class**, and has the same cell
count.  Native construction. -/
theorem exists_eval_eq_some_of_reduce_eval_eq {S : ClassRealization.{u, v} α M}
    (hβ : Order.IsSuccPrelimit β) {t : Fin n ↪ M} {d : TemplateClass.{u} β n}
    (h : (S.reduce hβ).eval t = some d) :
    ∃ c, S.eval t = some c ∧ c.reduce hβ = d ∧ d.cellCount = c.cellCount := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c, hc, rfl, TemplateClass.cellCount_reduce hβ c⟩

/-- **Stage reduction keeps the cell count of the class of a tuple.**  Native construction. -/
theorem cellCount_eq_of_reduce_eval_eq {S : ClassRealization.{u, v} α M}
    (hβ : Order.IsSuccPrelimit β) {t : Fin n ↪ M} {c : TemplateClass.{u} α n}
    {d : TemplateClass.{u} β n} (hc : S.eval t = some c) (hd : (S.reduce hβ).eval t = some d) :
    d.cellCount = c.cellCount := by
  obtain ⟨c', hc', -, hcount⟩ := exists_eval_eq_some_of_reduce_eval_eq hβ hd
  rw [hc] at hc'
  rw [hcount, Option.some.inj hc']

end ClassRealization

/-! ### A label in each block -/

/-- **A label in the block** `[λ_ξ, λ_ξ + ω)`.  Native construction. -/
def IsInBlock (ξ : Ordinal.{u}) (ℓ : Label.{u}) : Prop :=
  (blockStage ξ : Label.{u}) ≤ ℓ ∧ ℓ < ((blockStage ξ + ω : Ordinal.{u}) : Label.{u})

/-- **The blocks are pairwise disjoint.**  Native construction. -/
theorem IsInBlock.eq {ξ ξ' : Ordinal.{u}} {ℓ : Label.{u}} (h : IsInBlock ξ ℓ)
    (h' : IsInBlock ξ' ℓ) : ξ = ξ' := by
  have key : ∀ {a b : Ordinal.{u}}, a < b → IsInBlock a ℓ → IsInBlock b ℓ → False :=
    fun {a b} hab ha hb ↦ by
      have hle : blockStage a + ω ≤ blockStage b := by
        rw [← blockStage_add_one]
        exact blockStage_mono (Order.add_one_le_of_lt hab)
      have hle' : ((blockStage a + ω : Ordinal.{u}) : Label.{u}) ≤ (blockStage b : Label.{u}) :=
        WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hle)
      exact (ha.2.trans_le (hle'.trans hb.1)).false
  rcases lt_trichotomy ξ ξ' with hlt | heq | hgt
  · exact (key hlt h h').elim
  · exact heq
  · exact (key hgt h' h).elim

/-- **The one-point tuple** of a point.  Native construction. -/
def onePoint {M : Type v} (x : M) : Fin 1 ↪ M :=
  ⟨fun _ ↦ x, fun i j _ ↦ Subsingleton.elim i j⟩

/-- Every one-point tuple is the one-point tuple of its point.  Native construction. -/
theorem onePoint_apply_zero {M : Type v} (a : Fin 1 ↪ M) : onePoint (a 0) = a :=
  Function.Embedding.ext fun i ↦ by rw [Subsingleton.elim i 0]; rfl

variable {M : Type v}

/-- **A one-point class with a label in a given block** (native construction): for a lift
`G ∈ K_γ[L]` with `γ < ω₁`, and `ξ + 1 < γ`, some point `a` has a one-point class `c` in the
decoded class realization of `G` with a label in `[λ_ξ, λ_ξ + ω)`.  Donor density of
`decode γ G` (`mem_templateStageClass_iff`) over the empty tuple, with the strongly coded
uniformity donor `d` at `λ_γ` for `ξ < γ` (the premise `hd`), at the permitted cutoff
`λ_ξ + ω = λ_{ξ+1} < λ_γ`, which lies above the label of `d` in the block; the observation keeps
that label (`TemplateClass.ObservesAt.mem_labels`).  The label `λ_ξ` itself is not used. -/
theorem exists_onePoint_isInBlock (hd : HasStronglyCodedUniformityDonors.{u})
    {γ ξ : Ordinal.{u}} (hγ : γ < ω₁) (hξγ : ξ + 1 < γ) {G : templateLanguage.{u}.Structure M}
    (hG : G ∈ templateStageClass M γ) :
    ∃ (a : Fin 1 ↪ M) (c : TemplateClass.{u} (blockStage γ) 1),
      (decode γ G).eval a = some c ∧ ∃ ℓ ∈ c.labels, IsInBlock ξ ℓ := by
  have hdd := ((mem_templateStageClass_iff hγ G).mp hG).2.2.2
  obtain ⟨d, hdl, j, hj⟩ := hd ((Order.lt_add_one_iff.mpr le_rfl).trans hξγ)
  have hx : Label.IsPermittedCutoff (blockStage γ)
      ((blockStage ξ + ω : Ordinal.{u}) : Label.{u}) := by
    rw [Label.isPermittedCutoff_coe, ← blockStage_add_one]
    exact blockStage_strictMono hξγ
  obtain ⟨a, -, q, hq, hobs⟩ := hdd Function.Embedding.ofIsEmpty (TemplateClass.empty _)
    (decode_eval_zero γ G _) d.toClass Function.Embedding.ofIsEmpty hdl
    (TemplateClass.restrictFace_zero _ _) _ hx
  exact ⟨a, q, hq, d.label j, hobs.mem_labels ⟨j, rfl⟩ hj.2, hj⟩

/-! ### Lifts at different stages -/

/-- **A lift at a higher stage reduces to a lift at a lower stage** (correspondence with the
printed definitions): for `ξ ≤ ζ < ω₁` on a countable carrier, if `G ∈ K_ζ[L]` and `H ∈ K_ξ[L]`
have the same base reduct, the decoded class realization of `G` reduces at `λ_ξ` to that of `H`.
By projection (`projectionTarget`, B.T9) `τ_ξ(G) ∈ K_ξ[L]`; it has the base reduct of `G`
(`baseReduct_projectStructure`); Reconstruction (`reconstructionTarget`, B.T10) at `ξ` gives
`τ_ξ(G) = H`; and `τ_ξ(G)` is the structure of the reduction
(`projectStructure_eq_toStructure_decode_reduce`), which the decoder gives back
(`decode_toStructure`). -/
theorem decode_reduce_eq_decode_of_baseReduct_eq (hc : Countable M) {ζ ξ : Ordinal.{u}}
    (hζ : ζ < ω₁) (hξζ : ξ ≤ ζ) {G H : templateLanguage.{u}.Structure M}
    (hG : G ∈ templateStageClass M ζ) (hH : H ∈ templateStageClass M ξ)
    (h : baseReduct G = baseReduct H) :
    (decode ζ G).reduce (isSuccPrelimit_blockStage ξ) = decode ξ H := by
  have hτ : projectStructure ξ G = H :=
    reconstructionTarget ξ M hc (hξζ.trans_lt hζ) _ (projectionTarget ζ ξ M hc hζ hξζ G hG) H hH
      (by rw [baseReduct_projectStructure, h])
  rw [← hτ, projectStructure_eq_toStructure_decode_reduce hζ hξζ hG,
    decode_toStructure (hξζ.trans_lt hζ) (hG.2.1.isWellFormed_decode.reduce _)]

/-- **The class of a tuple in a lower lift is the reduction of its class in a higher lift**, for
lifts as in `decode_reduce_eq_decode_of_baseReduct_eq`.  Correspondence with the printed
definitions. -/
theorem reduce_eq_of_baseReduct_eq (hc : Countable M) {ζ ξ : Ordinal.{u}} (hζ : ζ < ω₁)
    (hξζ : ξ ≤ ζ) {G H : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M ζ)
    (hH : H ∈ templateStageClass M ξ) (h : baseReduct G = baseReduct H) {n : ℕ} {a : Fin n ↪ M}
    {c : TemplateClass.{u} (blockStage ζ) n} {d : TemplateClass.{u} (blockStage ξ) n}
    (hca : (decode ζ G).eval a = some c) (hda : (decode ξ H).eval a = some d) :
    c.reduce (isSuccPrelimit_blockStage ξ) = d := by
  have he := congrArg (fun S : ClassRealization.{u, v} (blockStage ξ) M ↦ S.eval a)
    (decode_reduce_eq_decode_of_baseReduct_eq hc hζ hξζ hG hH h)
  simp only [ClassRealization.reduce_eval, hca, hda, Option.map_some] at he
  exact Option.some.inj he

/-- **The cell count of the class of a tuple is the same in every lift of a base structure**, for
lifts as in `decode_reduce_eq_decode_of_baseReduct_eq` (`TemplateClass.cellCount_reduce`).
Correspondence with the printed definitions. -/
theorem cellCount_eq_of_baseReduct_eq (hc : Countable M) {ζ ξ : Ordinal.{u}} (hζ : ζ < ω₁)
    (hξζ : ξ ≤ ζ) {G H : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M ζ)
    (hH : H ∈ templateStageClass M ξ) (h : baseReduct G = baseReduct H) {n : ℕ} {a : Fin n ↪ M}
    {c : TemplateClass.{u} (blockStage ζ) n} {d : TemplateClass.{u} (blockStage ξ) n}
    (hca : (decode ζ G).eval a = some c) (hda : (decode ξ H).eval a = some d) :
    c.cellCount = d.cellCount := by
  rw [← reduce_eq_of_baseReduct_eq hc hζ hξζ hG hH h hca hda, TemplateClass.cellCount_reduce]

/-! ### The stage bound -/

/-- The countable ordinals do not form a countable set: the supremum of a countable set of
countable ordinals is countable (`Ordinal.iSup_lt_omega_one`), and so is its successor. -/
theorem not_countable_Iio_omega_one : ¬ (Set.Iio (ω₁ : Ordinal.{u})).Countable := fun hc ↦ by
  have := hc.to_subtype
  have hs := Ordinal.iSup_lt_omega_one fun x : Set.Iio (ω₁ : Ordinal.{u}) ↦ x.2
  have h1 := (Cardinal.isSuccLimit_omega 1).succ_lt hs
  exact (Order.lt_succ _).not_ge
    (Ordinal.le_iSup (fun x : Set.Iio (ω₁ : Ordinal.{u}) ↦ x.1) ⟨_, h1⟩)

/-- **A witness of the block `ξ` at the point `x` over `B`**: a lift `G ∈ K_γ[L]` of `B` at a
stage `ξ + 1 < γ < ω₁` in whose decoded class realization the one-point tuple of `x` has a class
with a label in `[λ_ξ, λ_ξ + ω)`.  Native construction. -/
def IsBlockWitness (B : baseTemplateLanguage.{u}.Structure M) (ξ : Ordinal.{u}) (x : M)
    (γ : Ordinal.{u}) : Prop :=
  γ < ω₁ ∧ ξ + 1 < γ ∧ ∃ G ∈ templateStageClass M γ, baseReduct G = B ∧
    ∃ c : TemplateClass.{u} (blockStage γ) 1, (decode γ G).eval (onePoint x) = some c ∧
      ∃ ℓ ∈ c.labels, IsInBlock ξ ℓ

/-- **The stage bound from strongly coded uniformity donors** (`StageBoundOfDonorsTarget M`, for
every `M`): on a countable carrier, the lift stages of every base structure `B` are bounded below
`ω₁`.  Suppose not.  Then every `ξ < ω₁` has a lift of `B` at a stage `γ > ξ + 1`, and so a point
`f ξ` witnessing the block `[λ_ξ, λ_ξ + ω)` (`exists_onePoint_isInBlock`).  The carrier being
countable and the countable ordinals not, some point `x` witnesses infinitely many blocks.  Fix
one of them, `ξ₀`, with its lift, and let `N` be the cell count of the class of `x` there.  Take
`N + 1` further blocks witnessed at `x`, and among the `N + 2` witnessing lifts the one at the
largest stage: every other lift is its reduction (`reduce_eq_of_baseReduct_eq`, through B.T9 and
B.T10), so the class `c` of `x` there has cell count `N`
(`cellCount_eq_of_baseReduct_eq`) and every witnessed label, being below the stage of its own
lift, is a label of `c` (`TemplateClass.mem_labels_of_mem_labels_reduce`).  The `N + 1` labels lie
in pairwise disjoint blocks (`IsInBlock.eq`), so they are distinct labels of `c`, which has
`N` cells (`TemplateClass.card_le_cellCount`): a contradiction.  Correspondence with the printed
definitions. -/
theorem stageBoundOfDonorsTarget (M : Type v) : StageBoundOfDonorsTarget.{u} M := by
  intro hd hc B
  by_contra hne
  push Not at hne
  have hsucc : ∀ o : Ordinal.{u}, o < ω₁ → o + 1 < ω₁ := fun o ho ↦ by
    simpa [Order.succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt ho
  -- every countable `ξ` has a witness point
  have hW : ∀ ξ ∈ Set.Iio (ω₁ : Ordinal.{u}), ∃ x : M, ∃ γ, IsBlockWitness B ξ x γ := by
    intro ξ hξ
    obtain ⟨β, ⟨hβ, G, hG, hGB⟩, hle⟩ := hne _ (hsucc _ (hsucc ξ hξ))
    have hξβ : ξ + 1 < β := (Order.lt_add_one_iff.mpr le_rfl).trans_le hle
    obtain ⟨a, c, hca, hl⟩ := exists_onePoint_isInBlock hd hβ hξβ hG
    exact ⟨a 0, β, hβ, hξβ, G, hG, hGB, c, by rwa [onePoint_apply_zero], hl⟩
  have hM : Nonempty M := by
    obtain ⟨_, ⟨_, G, hG, _⟩, _⟩ := hne 0 (omega0_pos.trans omega0_lt_omega_one)
    exact nonempty_of_mem_templateStageClass hG
  choose! f hf using hW
  -- some point witnesses infinitely many blocks
  have hfib : ∃ x : M, ¬ {ξ | ξ < ω₁ ∧ f ξ = x}.Countable := by
    by_contra! hall
    have : Countable M := hc
    refine not_countable_Iio_omega_one ?_
    have he : Set.Iio (ω₁ : Ordinal.{u}) = ⋃ x : M, {ξ | ξ < ω₁ ∧ f ξ = x} := by
      ext ξ
      simp
    rw [he]
    exact Set.countable_iUnion hall
  obtain ⟨x, hx⟩ := hfib
  set F := {ξ | ξ < ω₁ ∧ f ξ = x} with hFdef
  have hF : F.Infinite := fun hfin ↦ hx hfin.countable
  have hFW : ∀ ξ ∈ F, ∃ γ, IsBlockWitness B ξ x γ := fun ξ hξ ↦ by
    have := hf ξ hξ.1
    rwa [hξ.2] at this
  choose! γ hγ using hFW
  -- the cell count at one witnessing lift
  obtain ⟨ξ₀, hξ₀⟩ := hF.nonempty
  obtain ⟨-, -, G₀, hG₀, hB₀, c₀, hc₀, -⟩ := hγ ξ₀ hξ₀
  -- `N + 1` further witnessed blocks, and the lift at the largest stage
  obtain ⟨T, hTF, hTcard⟩ := hF.exists_subset_card_eq (c₀.cellCount + 1)
  obtain ⟨ξs, hξs, hmax⟩ :=
    (insert ξ₀ T).exists_max_image γ (Finset.insert_nonempty ξ₀ T)
  have hξsF : ξs ∈ F := by
    rcases Finset.mem_insert.mp hξs with rfl | h
    · exact hξ₀
    · exact hTF h
  obtain ⟨hγs, -, Gs, hGs, hBs, cs, hcs, -⟩ := hγ ξs hξsF
  have hN : cs.cellCount = c₀.cellCount :=
    cellCount_eq_of_baseReduct_eq hc hγs (hmax ξ₀ (Finset.mem_insert_self ξ₀ T)) hGs hG₀
      (hBs.trans hB₀.symm) hcs hc₀
  have hlab : ∀ ξ ∈ T, ∃ ℓ ∈ cs.labels, IsInBlock ξ ℓ := by
    intro ξ hξ
    obtain ⟨-, hξγ, G, hG, hB, c, hcx, ℓ, hℓ, hblk⟩ := hγ ξ (hTF hξ)
    have hred := reduce_eq_of_baseReduct_eq hc hγs (hmax ξ (Finset.mem_insert_of_mem hξ)) hGs hG
      (hBs.trans hB.symm) hcs hcx
    have hlt : ℓ < (blockStage (γ ξ) : Label.{u}) := by
      refine hblk.2.trans (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_))
      rw [← blockStage_add_one]
      exact blockStage_strictMono hξγ
    exact ⟨ℓ, TemplateClass.mem_labels_of_mem_labels_reduce _ (by rw [hred]; exact hℓ) hlt, hblk⟩
  choose! ℓ hℓ hblk using hlab
  have hinj : Set.InjOn ℓ T := fun ξ hξ ξ' hξ' h ↦ (hblk ξ hξ).eq (h ▸ hblk ξ' hξ')
  have hcard := TemplateClass.card_le_cellCount hinj hℓ
  omega

/-- **The stage bound** (`StageBoundTarget M`, for every `M`): on a countable carrier, the lift
stages of every base structure are bounded below `ω₁`.  `stageBoundOfDonorsTarget` with the
donors `hasStronglyCodedUniformityDonors`.  Correspondence with the printed definitions. -/
theorem stageBoundTarget (M : Type v) : StageBoundTarget.{u} M :=
  stageBoundOfDonorsTarget M hasStronglyCodedUniformityDonors

/-- **B.T15, Boundedness** [AFK26, Proposition 4.34] (`BoundednessTarget M`, for every `M`): on a
countable carrier, the ranks of the lifts of every base structure form a countable set bounded
below `ω₁`.  The stage bound (`stageBoundTarget`) and the rank at most the stage
(`boundednessTarget_of_stageBoundTarget`); the rank is never identified with the stage.
Correspondence with the printed definitions. -/
theorem boundednessTarget (M : Type v) : BoundednessTarget.{u} M :=
  boundednessTarget_of_stageBoundOfDonorsTarget (stageBoundOfDonorsTarget M)

end

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Maximality.Definitions
import VaughtConjecture.Correspondence.Presentation.Scheduler
import VaughtConjecture.Correspondence.Reconstruction.Reconstruction
import VaughtConjecture.MainTheorem.StronglyCodedSuccessor

/-!
# Targets of maximality and of the count of maximal structures

Numbering as in the current draft of [AFK26].  Write `λ_β = blockStage β = ω + ω · β`.  `τ_β` is
`projectStructure β`, `K_β[L]` is `templateStageClass M β`, `N↾L_c[L]` is `baseReduct N`, and
maximality at `β` is the printed [AFK26, Definition 2.20] (`IsMaximalAt`, with its allowance for
an unchanged higher lift).  The statements serve [AFK26, Proposition 4.35] ("for each `β` there
are only countably many `(L_b[L] ∪ L_c[L])`-structures up to isomorphism that are maximal at
`β`").  Every premise is visible; for each target the file says whether it is proved, proved from
a named open target, or open.

## Strictness and the comparison with "no successor"

* `StrictnessTarget β M` (**open**): a structure of `K_{β'}[L]`, `β < β' < ω₁`, is not fixed by
  `τ_β`.  `SuccessorStrictnessTarget β M` (**open**) is its instance `β' = β + 1`.  On a countable
  carrier the two are equivalent: the instance gives the general statement by projection to
  `β + 1` (`strictnessTarget_of_successorStrictnessTarget`, proved from B.T9).  The general form
  says that the least fixing stage (`rank_τ`) of a member of `K_{β'}[L]` is `β'`; it is **not** a
  consequence of "the rank is at most the stage" (`rankLeStageTarget`), which bounds the rank from
  above only.
* `MaximalNoSuccessorTarget β M`: maximality at `β` is `G ∈ K_β[L]` and no `H ∈ K_{β+1}[L]` with
  `τ_β(H) = G`.  The direction from "no successor" to maximality is **proved** with no
  strictness (`isMaximalAt_of_not_exists_succ`): a lift at `β' > β` projects to a lift at `β + 1`
  (B.T9).  The other direction is **proved from `SuccessorStrictnessTarget`**
  (`maximalNoSuccessorTarget_of_successorStrictnessTarget`): maximality turns a successor `H` into
  `H = G`, an unchanged successor, fixed by `τ_β`, and strictness excludes exactly this.
* `MaximalSuccessorComparisonTarget β M`: maximality is `G ∈ K_β[L]` and every `H ∈ K_{β+1}[L]`
  with `τ_β(H) = G` equals `G` (the printed clause at `β + 1` only, unchanged successor allowed).
  Maximality gives it (`IsMaximalAt.forall_succ`, **proved**).  The converse is **proved from
  `SuccessorStrictnessTarget`**; without it, an unchanged successor `G ∈ K_{β+1}[L]` would have to
  be continued to every `β' > β + 1`, which nothing here provides.

**What strictness needs** (route, estimated, not compiled).  Let `H ∈ K_{β+1}[L]` with
`τ_β(H) = H`.  The strongly coded uniformity donor at `λ_{β+1}` for `β`
(`hasStronglyCodedUniformityDonors`) is a strongly coded legal stage type on one point with a
label `ℓ` in the block `[λ_β, λ_β + ω)`.  Donor density of `decode (β + 1) H`
(`mem_templateStageClass_iff`) over the empty tuple at the permitted cutoff `ℓ + 1 < λ_{β+1}` gives
a point whose one-point class has the label `ℓ` (`TemplateClass.ObservesAt.mem_labels`).  Since
`τ_β(H) = H`, every invariant holding in `H` is a class fixed by `τ_β`, whose labels are below
`λ_β` or formal tops, a contradiction.  The existing `exists_onePoint_isInBlock` does not apply as
stated: its cutoff `λ_{ξ+1}` must lie below `λ_γ`, so it needs `ξ + 1 < γ`, which fails at
`γ = β + 1`, `ξ = β`; the cutoff `ℓ + 1` is the change.  The missing lemma is the computation of the
labels of a class fixed by `τ_β`.

## Transport (C.T5), proved

`StageClassTransportTarget`, `BaseReductTransportTarget`, `ProjectionTransportTarget` and
`MaximalTransportTarget`: along a bijection `e : M ≃ N` of carriers, membership in `K_β[L]`, the
base reduct, the projection `τ_β` and maximality at `β` transport, for every `β`, with no
countability and no nonemptiness premise (`VaughtConjecture.Correspondence.Maximality.Definitions`).

## Infinitude (C.T11)

`InfinitudeTarget β M`: for `β < ω₁`, a carrier with a structure of `K_β[L]` is infinite.  Fresh
points are forced **inside one structure**: `FreshPointTarget β M` says that every typed tuple `t`
of `decode β G` on `n` points extends to a typed tuple `u` on `n + 1` points with
`Fin.castSuccEmb.trans u = t` (the old tuple is kept, literally); `u` is injective, so its last
point is not a point of `t` (`apply_last_not_mem_range`).  The input is a strongly coded legal
class on `n + 1` points whose face along `Fin.castSuccEmb` is the class of `t`
(`exists_isStronglyCodedLegal_restrictFace_castSuccEmb`, from the exact pinned extension
`StageType.exists_stronglyCoded_pinned_extension` over the empty face with a one-point legal
class), used as a donor in the donor density of `decode β G`.  Joint embedding alone would not do:
an amalgam of the class of `t` with a one-point class may put the new point on an old one.  All
three are **proved** (`freshPointTarget`, `infinitudeTarget`).

## Maximal implies terminal presentation (C.T9)

* `StronglyCodedPresentationTarget β M` (**proved**, B.T7 with the decoder): for `β < ω₁` on a
  countable carrier, a structure `G ∈ K_β[L]` has a realization `R` at `λ_β` in the strongly coded
  receiving class with class reading `decode β G`.
* `SuccessorReadingTarget β M` (**proved**): the class reading of a realization `R'` in the class at
  `λ_{β+1}` gives a structure `H = R'.classReading.toStructure ∈ K_{β+1}[L]`, and the projection
  `τ_β(H)` is the structure of the class reading of the **literal** stage reduction of `R'` to
  `λ_β`.
* `MaximalToTerminalTarget β M`: for `β < ω₁`, if `G` is maximal at `β` and `R` is in the class at
  `λ_β` with class reading `decode β G`, then `R` is terminal in the class at `β`
  (`Realization.IsStronglyCodedTerminalAt`).  **Proved from `SuccessorStrictnessTarget`**
  (`maximalToTerminalTarget_of_successorStrictnessTarget`): a successor `R'` of `R`, with
  `R'.reduce = R`, gives `H ∈ K_{β+1}[L]` with `τ_β(H) = G`; maximality gives `G = H`, an unchanged
  successor; strictness excludes it.  This is the only use of strictness.  The converse (terminal
  presentation implies maximal) is not stated.

## Same-stage injectivity (C.T6), proved

`SameStageInjectivityTarget β M N`: for `β < ω₁` and a countable carrier `M`, two structures maximal
at `β`, `G` on `M` and `H` on `N`, with an isomorphism `e` of base reducts, are isomorphic in the
full language `L_b[L] ∪ L_c[L]`, by the same bijection.  Transport `H` to `M` along `e⁻¹`; the base
reducts are then equal (`FirstOrder.Language.Equiv.inducedStructure_eq`); Reconstruction at `β`
(`reconstructionTarget`) gives equality on `M`.  Maximality is not used beyond membership in
`K_β[L]` (`nonempty_equiv_of_baseReduct_equiv`), and no uniqueness of maximal pairs across stages
is used.

## The count (C.T10), stated

`MaximalCountTarget β`: a countable set of structures on `ℕ`, each maximal at `β`, representing
every structure maximal at `β` on every countable carrier, up to isomorphism in the full language
`L_b[L] ∪ L_c[L]` (never only of base reducts).  Open.  The intended assembly, each input with its
status:

1. infinitude, `infinitudeTarget` (proved): the carrier is countably infinite, so `M ≃ ℕ`;
2. transport, `isMaximalAt_transportStructure_iff` and `transportEquiv` (proved): `G` is isomorphic
   to a structure maximal at `β` on `ℕ`;
3. presentation, `stronglyCodedPresentationTarget` (proved): a realization `R` in the strongly
   coded receiving class with class reading `decode β G`;
4. maximal implies terminal, `MaximalToTerminalTarget` (proved from the open
   `SuccessorStrictnessTarget`): `R` is terminal in the class at `β`;
5. countably many terminal realizations on `ℕ` up to isomorphism of realizations,
   `Realization.StronglyCodedTerminalCountTarget` (universe `0`), a composition of compiled
   results (`Realization.stronglyCodedTerminalCountTarget_of_isoTarget`,
   `Realization.stronglyCodedTerminalIsoTarget_of_comparisons` and the rigid-core, residual and
   hollow comparisons) whose premises, restricted (R2) and (R3) on `ℕ`
   (`Realization.StronglyCodedResidualReceiving`, `Realization.StronglyCodedHollowReceiving`), are
   open;
6. an isomorphism of realizations is an isomorphism of class-reading structures in the full
   language, `Realization.Iso.classReadingEquiv` (proved), and the class-reading structure of
   `decode β G` is `G` (`IsTemplateCompatible.toStructure_decode`, proved).  This is one input of
   the count, not the count;
7. choose one maximal structure on `ℕ` for each terminal class reached.

Same-stage injectivity (C.T6) is the alternative to 6 when the counted classes are classes of
base structures.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-- `β + 1 < ω₁` for `β < ω₁`. -/
theorem add_one_lt_omega_one {β : Ordinal.{u}} (hβ : β < ω₁) : β + 1 < ω₁ :=
  (Cardinal.isSuccLimit_omega 1).add_one_lt hβ

/-! ### Strictness and the comparison with "no successor" -/

section Strictness

variable (β : Ordinal.{u}) (M : Type v)

/-- **Target: strictness of the levels.**  For `β < β' < ω₁`, a structure of `K_{β'}[L]` is not
fixed by `τ_β`; equivalently, `β` is not a fixing stage of it, so its least fixing stage
(`rank_τ`) is `β'`.  Not a consequence of `rankLeStageTarget`.  Open.  Native construction. -/
def StrictnessTarget : Prop :=
  ∀ β' : Ordinal.{u}, β' < ω₁ → β < β' →
    ∀ H ∈ templateStageClass M β', projectStructure β H ≠ H

/-- **Target: strictness at the successor level.**  For `β < ω₁`, a structure of `K_{β+1}[L]` is
not fixed by `τ_β`: there is no unchanged successor.  This is the instance of `StrictnessTarget`
used by `MaximalToTerminalTarget`.  Open.  Native construction. -/
def SuccessorStrictnessTarget : Prop :=
  β < ω₁ → ∀ H ∈ templateStageClass M (β + 1), projectStructure β H ≠ H

/-- **Target: maximality is the absence of a successor.**  On a countable carrier, for `β < ω₁`,
`G` is maximal at `β` exactly when `G ∈ K_β[L]` and no `H ∈ K_{β+1}[L]` has `τ_β(H) = G`.
Correspondence with the printed definitions. -/
def MaximalNoSuccessorTarget : Prop :=
  Countable M → β < ω₁ → ∀ G : templateLanguage.{u}.Structure M,
    IsMaximalAt β G ↔ G ∈ templateStageClass M β ∧
      ¬ ∃ H ∈ templateStageClass M (β + 1), projectStructure β H = G

/-- **Target: maximality is the printed clause at the successor level.**  On a countable carrier,
for `β < ω₁`, `G` is maximal at `β` exactly when `G ∈ K_β[L]` and every `H ∈ K_{β+1}[L]` with
`τ_β(H) = G` is `G` (an unchanged successor allowed).  Correspondence with the printed
definitions. -/
def MaximalSuccessorComparisonTarget : Prop :=
  Countable M → β < ω₁ → ∀ G : templateLanguage.{u}.Structure M,
    IsMaximalAt β G ↔ G ∈ templateStageClass M β ∧
      ∀ H ∈ templateStageClass M (β + 1), projectStructure β H = G → G = H

variable {β M}

/-- **Strictness at the successor level gives strictness**, on a countable carrier: a structure
`H ∈ K_{β'}[L]` fixed by `τ_β` projects to `τ_{β+1}(H) = H ∈ K_{β+1}[L]` (B.T9,
`projectionTarget`; the fixing stages are closed upward).  Proved from `SuccessorStrictnessTarget`.
Correspondence with the printed definitions. -/
theorem strictnessTarget_of_successorStrictnessTarget (hc : Countable M)
    (h : SuccessorStrictnessTarget β M) : StrictnessTarget β M := by
  intro β' hβ' hββ' H hH hfix
  have hH1 : projectStructure (β + 1) H = H :=
    projectStructure_eq_of_le H (Order.lt_add_one_iff.mpr le_rfl).le hfix
  have hmem := projectionTarget β' (β + 1) M hc hβ' (Order.add_one_le_of_lt hββ') H hH
  rw [hH1] at hmem
  exact h (hββ'.trans hβ') H hmem hfix

/-- **Strictness gives strictness at the successor level.**  Native construction. -/
theorem successorStrictnessTarget_of_strictnessTarget (h : StrictnessTarget β M) :
    SuccessorStrictnessTarget β M :=
  fun hβ ↦ h (β + 1) (add_one_lt_omega_one hβ) (Order.lt_add_one_iff.mpr le_rfl)

/-- **No successor gives maximality**, with no strictness: on a countable carrier, for `β < ω₁`,
if `G ∈ K_β[L]` has no `H ∈ K_{β+1}[L]` with `τ_β(H) = G`, then `G` is maximal at `β`, the
printed clause holding vacuously.  A lift `G'` at `β' > β` would give the successor
`τ_{β+1}(G') ∈ K_{β+1}[L]` (B.T9, `projectionTarget`), with `τ_β(τ_{β+1}(G')) = τ_β(G') = G`.
Correspondence with the printed definitions. -/
theorem isMaximalAt_of_not_exists_succ (hc : Countable M) {G : templateLanguage.{u}.Structure M}
    (hG : G ∈ templateStageClass M β)
    (h : ¬ ∃ H ∈ templateStageClass M (β + 1), projectStructure β H = G) : IsMaximalAt β G := by
  refine ⟨hG, fun β' hβ' hββ' G' hG' hG'G ↦ (h ⟨projectStructure (β + 1) G', ?_, ?_⟩).elim⟩
  · exact projectionTarget β' (β + 1) M hc hβ' (Order.add_one_le_of_lt hββ') G' hG'
  · rw [projectStructure_projectStructure_of_le G' (Order.lt_add_one_iff.mpr le_rfl).le, hG'G]

/-- **Maximality gives the printed clause at the successor level** (an unchanged successor
allowed).  Correspondence with the printed definitions. -/
theorem IsMaximalAt.forall_succ (hβ : β < ω₁) {G : templateLanguage.{u}.Structure M}
    (hG : IsMaximalAt β G) :
    ∀ H ∈ templateStageClass M (β + 1), projectStructure β H = G → G = H :=
  fun H hH hHG ↦ hG.2 (β + 1) (add_one_lt_omega_one hβ) (Order.lt_add_one_iff.mpr le_rfl) H hH hHG

/-- **Strictness excludes the successors of a maximal structure**: for `β < ω₁`, a structure
maximal at `β` has no `H ∈ K_{β+1}[L]` with `τ_β(H) = G`.  Maximality makes such an `H` equal to
`G`, so fixed by `τ_β`.  Proved from `SuccessorStrictnessTarget`.  Correspondence with the printed
definitions. -/
theorem IsMaximalAt.not_exists_succ (hs : SuccessorStrictnessTarget β M) (hβ : β < ω₁)
    {G : templateLanguage.{u}.Structure M} (hG : IsMaximalAt β G) :
    ¬ ∃ H ∈ templateStageClass M (β + 1), projectStructure β H = G := by
  rintro ⟨H, hH, hHG⟩
  exact hs hβ H hH (hHG.trans (hG.forall_succ hβ H hH hHG))

/-- **`MaximalNoSuccessorTarget` from `SuccessorStrictnessTarget`.**  Correspondence with the
printed definitions. -/
theorem maximalNoSuccessorTarget_of_successorStrictnessTarget
    (hs : SuccessorStrictnessTarget β M) : MaximalNoSuccessorTarget β M :=
  fun hc hβ _ ↦ ⟨fun hG ↦ ⟨hG.1, hG.not_exists_succ hs hβ⟩,
    fun ⟨hG, h⟩ ↦ isMaximalAt_of_not_exists_succ hc hG h⟩

/-- **`MaximalSuccessorComparisonTarget` from `SuccessorStrictnessTarget`.**  The forward
direction needs no strictness (`IsMaximalAt.forall_succ`).  Correspondence with the printed
definitions. -/
theorem maximalSuccessorComparisonTarget_of_successorStrictnessTarget
    (hs : SuccessorStrictnessTarget β M) : MaximalSuccessorComparisonTarget β M := by
  refine fun hc hβ G ↦ ⟨fun hG ↦ ⟨hG.1, hG.forall_succ hβ⟩, fun ⟨hG, h⟩ ↦ ?_⟩
  refine isMaximalAt_of_not_exists_succ hc hG fun ⟨H, hH, hHG⟩ ↦ hs hβ H hH ?_
  exact hHG.trans (h H hH hHG)

end Strictness

/-! ### Transport (C.T5) -/

section Transport

variable (β : Ordinal.{u}) (M : Type v) (N : Type w)

/-- **Target: membership in `K_β[L]` transports along a bijection of carriers.**
Correspondence with the printed definitions. -/
def StageClassTransportTarget : Prop :=
  ∀ (e : M ≃ N) (G : templateLanguage.{u}.Structure M),
    transportStructure e G ∈ templateStageClass N β ↔ G ∈ templateStageClass M β

/-- **Target: the base reduct transports along a bijection of carriers.**  Correspondence with the
printed definitions. -/
def BaseReductTransportTarget : Prop :=
  ∀ (e : M ≃ N) (G : templateLanguage.{u}.Structure M),
    baseReduct (transportStructure e G) =
      @Equiv.inducedStructure baseTemplateLanguage.{u} M N (baseReduct G) e

/-- **Target: `τ_β` commutes with transport along a bijection of carriers.**  Correspondence with
the printed definitions. -/
def ProjectionTransportTarget : Prop :=
  ∀ (e : M ≃ N) (G : templateLanguage.{u}.Structure M),
    projectStructure β (transportStructure e G) = transportStructure e (projectStructure β G)

/-- **Target: maximality at `β` transports along a bijection of carriers.**  Correspondence with
the printed definitions. -/
def MaximalTransportTarget : Prop :=
  ∀ (e : M ≃ N) (G : templateLanguage.{u}.Structure M),
    IsMaximalAt β (transportStructure e G) ↔ IsMaximalAt β G

/-- `StageClassTransportTarget` holds (`mem_templateStageClass_transportStructure_iff`).
Correspondence with the printed definitions. -/
theorem stageClassTransportTarget : StageClassTransportTarget β M N :=
  mem_templateStageClass_transportStructure_iff

/-- `BaseReductTransportTarget` holds (`baseReduct_transportStructure`).  Correspondence with the
printed definitions. -/
theorem baseReductTransportTarget : BaseReductTransportTarget.{u} M N :=
  baseReduct_transportStructure

/-- `ProjectionTransportTarget` holds (`projectStructure_transportStructure`).  Correspondence with
the printed definitions. -/
theorem projectionTransportTarget : ProjectionTransportTarget β M N :=
  projectStructure_transportStructure β

/-- `MaximalTransportTarget` holds (`isMaximalAt_transportStructure_iff`).  Correspondence with the
printed definitions. -/
theorem maximalTransportTarget : MaximalTransportTarget β M N :=
  isMaximalAt_transportStructure_iff

end Transport

/-! ### Infinitude (C.T11) -/

section Infinitude

/-- **A strongly coded legal class has an extension by one point**: at a block stage, a strongly
coded legal class `P` on `n` points is the face along `Fin.castSuccEmb` of a strongly coded legal
class on `n + 1` points.  The exact pinned extension
(`StageType.exists_stronglyCoded_pinned_extension`, from
`StageType.hasStronglyCodedApexCoatomExtensions`) of a representative of `P` over its empty face,
with a one-point legal class (`exists_legalClass`, reduced to the stage).  Native construction. -/
theorem exists_isStronglyCodedLegal_restrictFace_castSuccEmb (β : Ordinal.{u}) {n : ℕ}
    {P : TemplateClass.{u} (blockStage β) n} (hP : P.IsStronglyCodedLegal) :
    ∃ D : TemplateClass.{u} (blockStage β) (n + 1), D.IsStronglyCodedLegal ∧
      D.restrictFace Fin.castSuccEmb = some P := by
  induction P using Quotient.inductionOn with
  | h P₀ =>
    obtain ⟨c⟩ := exists_legalClass.{u} 1
    obtain ⟨d, hd⟩ := Quotient.exists_rep (c.1.reduce (isSuccPrelimit_blockStage β))
    have hdl : d.IsStronglyCodedLegal := by
      have h := (TemplateClass.isStronglyCodedLegal_reduce_iff (isSuccPrelimit_blockStage β)
        c.1).mpr c.2
      rw [← hd] at h
      exact h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (P₀.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
    obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp
      (d.isSome_restrictFace_of_zero Fin.castSuccEmb)
    rw [StageType.eq_of_zero p' p] at hp'
    obtain ⟨Q, hQ, hQP, -⟩ := StageType.exists_stronglyCoded_pinned_extension
      (StageType.hasStronglyCodedApexCoatomExtensions (isSuccPrelimit_blockStage β)) hP hp hdl hp'
    exact ⟨Q.toClass, hQ, by rw [TemplateClass.restrictFace_toClass, hQP, Option.map_some]⟩

variable (β : Ordinal.{u}) (M : Type v)

/-- **Target: a fresh point over every typed tuple.**  For `β < ω₁` and `G ∈ K_β[L]`, every typed
tuple `t` of `decode β G` on `n` points extends to a typed tuple `u` on `n + 1` points that keeps
`t` literally: `Fin.castSuccEmb.trans u = t`.  Native construction. -/
def FreshPointTarget : Prop :=
  β < ω₁ → ∀ G ∈ templateStageClass M β, ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
    ((decode β G).eval t).isSome →
      ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ ((decode β G).eval u).isSome

/-- **Target C.T11, infinitude**: for `β < ω₁`, a carrier with a structure of `K_β[L]` is
infinite.  Native construction. -/
def InfinitudeTarget : Prop :=
  β < ω₁ → ∀ G ∈ templateStageClass M β, Infinite M

variable {β M}

/-- **The new point of an extension keeping the old tuple is fresh**: if
`Fin.castSuccEmb.trans u = t`, the last point of `u` is not a point of `t`, by injectivity of
`u`.  Native construction. -/
theorem apply_last_not_mem_range {n : ℕ} {t : Fin n ↪ M} {u : Fin (n + 1) ↪ M}
    (h : Fin.castSuccEmb.trans u = t) : u (Fin.last n) ∉ Set.range t := by
  rintro ⟨i, hi⟩
  rw [← h] at hi
  exact (Fin.castSucc_lt_last i).ne (u.injective hi)

variable (β M)

/-- **A fresh point over every typed tuple** (`FreshPointTarget β M`): donor density of
`decode β G` (`mem_templateStageClass_iff`) at the permitted cutoff `0`, for a strongly coded
legal donor on `n + 1` points whose face along `Fin.castSuccEmb` is the class of `t`
(`exists_isStronglyCodedLegal_restrictFace_castSuccEmb`).  Native construction. -/
theorem freshPointTarget : FreshPointTarget β M := by
  intro hβ G hG n t ht
  obtain ⟨hM, hc, -, hdd⟩ := (mem_templateStageClass_iff hβ G).mp hG
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp ht
  obtain ⟨D, hD, hDP⟩ := exists_isStronglyCodedLegal_restrictFace_castSuccEmb β
    (hc.isWellFormed_decode.hasLegalTypes t P hP)
  have h0 : Label.IsPermittedCutoff (blockStage β) (0 : Label.{u}) :=
    Label.isPermittedCutoff_zero.mpr (omega0_pos.trans_le (omega0_le_blockStage β))
  obtain ⟨u, hu, q, hq, -⟩ := hdd t P hP D Fin.castSuccEmb hD hDP 0 h0
  exact ⟨u, hu, by rw [hq]; rfl⟩

/-- **Infinitude from fresh points.**  Typed tuples of every length, from the empty tuple
(`decode_eval_zero`) by `FreshPointTarget`; a finite carrier has no injective tuple longer than
its cardinality.  Native construction. -/
theorem infinitudeTarget_of_freshPointTarget (h : FreshPointTarget β M) : InfinitudeTarget β M := by
  intro hβ G hG
  have hall : ∀ n : ℕ, ∃ t : Fin n ↪ M, ((decode β G).eval t).isSome := by
    intro n
    induction n with
    | zero => exact ⟨Function.Embedding.ofIsEmpty, by rw [decode_eval_zero]; rfl⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨u, -, hu⟩ := h hβ G hG t ht
      exact ⟨u, hu⟩
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite M
  obtain ⟨t, -⟩ := hall (Fintype.card M + 1)
  have hle := Fintype.card_le_of_embedding t
  rw [Fintype.card_fin] at hle
  omega

/-- **Target C.T11, infinitude, holds** (`InfinitudeTarget β M` for every `β` and `M`).
Native construction. -/
theorem infinitudeTarget : InfinitudeTarget β M :=
  infinitudeTarget_of_freshPointTarget β M (freshPointTarget β M)

end Infinitude

/-! ### Maximal implies terminal presentation (C.T9) -/

section Terminal

variable (β : Ordinal.{u}) (M : Type v)

/-- **Target: a strongly coded receiving presentation of a structure of `K_β[L]`.**  For `β < ω₁`
on a countable carrier, every `G ∈ K_β[L]` has a realization `R` at `λ_β` in the strongly coded
receiving class whose class reading is `decode β G`.  Native construction. -/
def StronglyCodedPresentationTarget : Prop :=
  β < ω₁ → Countable M → ∀ G ∈ templateStageClass M β,
    ∃ R : Realization.{u, v} (blockStage β) M, R.IsStronglyCodedReceiving ∧
      R.classReading = decode β G

/-- **Target: the class reading of a successor.**  For `β < ω₁` on a nonempty carrier, a
realization `R'` at `λ_{β+1}` in the strongly coded receiving class gives the structure
`H = R'.classReading.toStructure` of `K_{β+1}[L]`, and `τ_β(H)` is the structure of the class
reading of the literal stage reduction `R'.reduce λ_β`.  Native construction. -/
def SuccessorReadingTarget : Prop :=
  β < ω₁ → Nonempty M → ∀ R' : Realization.{u, v} (blockStage (β + 1)) M,
    R'.IsStronglyCodedReceiving →
      R'.classReading.toStructure ∈ templateStageClass M (β + 1) ∧
        projectStructure β R'.classReading.toStructure =
          (R'.reduce (isSuccPrelimit_blockStage β)).classReading.toStructure

/-- **Target C.T9: maximal implies terminal presentation.**  For `β < ω₁`, if `G` is maximal at
`β` and a realization `R` at `λ_β` in the strongly coded receiving class has class reading
`decode β G`, then `R` is terminal in the class at `β`: no realization in the class at `λ_{β+1}`
reduces literally to `R`.  Native construction. -/
def MaximalToTerminalTarget : Prop :=
  β < ω₁ → ∀ G : templateLanguage.{u}.Structure M, IsMaximalAt β G →
    ∀ R : Realization.{u, v} (blockStage β) M, R.IsStronglyCodedReceiving →
      R.classReading = decode β G → R.IsStronglyCodedTerminalAt β

/-- **A strongly coded receiving presentation exists** (`StronglyCodedPresentationTarget β M`):
the decoded class realization of `G ∈ K_β[L]` is well formed with donor density
(`IsTemplateCompatible.isWellFormed_decode`, `mem_templateStageClass_iff`); B.T7
(`presentationTarget`) presents it, and the four properties of the presentation give the class
(receiving through `Realization.HasFiniteExtensionReceivingIn.hasFiniteCutReceivingIn`).
Native construction. -/
theorem stronglyCodedPresentationTarget : StronglyCodedPresentationTarget β M := by
  intro hβ hc G hG
  obtain ⟨hM, hcomp, -, hdd⟩ := (mem_templateStageClass_iff hβ G).mp hG
  obtain ⟨R, hR, hcov, hl, hrec, hRG⟩ :=
    presentationTarget β M hβ hc hM (decode β G) hcomp.isWellFormed_decode hdd
  exact ⟨R, ⟨hR, hcov, fun _ t p hp ↦ (hl t p hp).1, fun _ t p hp ↦ (hl t p hp).2,
    hrec.hasFiniteCutReceivingIn⟩, hRG⟩

/-- **The class reading of a successor** (`SuccessorReadingTarget β M`): the class reading of
`R'` is well formed (`Realization.IsConsistent.classReading`, `Realization.IsCovering.classReading`,
`Realization.classReading_hasLegalTypes`) with donor density
(`Realization.HasFiniteExtensionReceivingIn.hasDonorDensity_classReading`, receiving through
`Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff`); B.T5 (`decoderRoundTrip`) and
`mem_templateStageClass_iff` at `β + 1 < ω₁` give membership; the projection is the structure of
the reduction (`ClassRealization.projectStructure_toStructure_reduce`), and the class reading
commutes with reduction (`Realization.classReading_reduce`).  Native construction. -/
theorem successorReadingTarget : SuccessorReadingTarget β M := by
  intro hβ hM R' hR'
  have hβ1 := add_one_lt_omega_one hβ
  have hwf : R'.classReading.IsWellFormed :=
    ⟨hR'.isConsistent.classReading, hR'.isCovering.classReading,
      Realization.classReading_hasLegalTypes fun _ t p hp ↦
        And.intro (hR'.hasLegalTypes t p hp) (hR'.isStronglyCoded t p hp)⟩
  have hdd : R'.classReading.HasDonorDensity :=
    ((Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff hR'.isConsistent
      (isSuccPrelimit_blockStage _)).mpr hR'.receiving).hasDonorDensity_classReading
  obtain ⟨hcomp, hfix, hdec⟩ := (decoderRoundTrip hβ1).2 _ hwf
  refine ⟨(mem_templateStageClass_iff hβ1 _).mpr ⟨hM, hcomp, hfix, by rw [hdec]; exact hdd⟩, ?_⟩
  rw [ClassRealization.projectStructure_toStructure_reduce hβ hwf.hasLegalTypes,
    Realization.classReading_reduce]

variable {β M}

/-- **Maximal implies terminal presentation, from strictness at the successor level**
(`MaximalToTerminalTarget β M` from `SuccessorStrictnessTarget β M`).  A realization `R'` in the
class at `λ_{β+1}` with `R'.reduce λ_β = R` gives `H ∈ K_{β+1}[L]` with
`τ_β(H) = (R'.reduce λ_β).classReading.toStructure = (decode β G).toStructure = G`
(`successorReadingTarget`, `IsTemplateCompatible.toStructure_decode`).  Maximality at `β` gives
`G = H`, an unchanged successor: `H` is fixed by `τ_β`, which strictness excludes.
Correspondence with the printed definitions. -/
theorem maximalToTerminalTarget_of_successorStrictnessTarget
    (hs : SuccessorStrictnessTarget β M) : MaximalToTerminalTarget β M := by
  intro hβ G hG R hR hRG
  refine ⟨hR, fun ⟨R', hR', hred⟩ ↦ ?_⟩
  obtain ⟨hmem, hproj⟩ := successorReadingTarget β M hβ hG.1.1 R' hR'
  have hHG : projectStructure β R'.classReading.toStructure = G := by
    rw [hproj, hred, hRG, hG.1.2.1.toStructure_decode hG.1.2.2.1]
  exact hs hβ _ hmem (hHG.trans (hG.forall_succ hβ _ hmem hHG))

end Terminal

/-! ### Same-stage injectivity (C.T6) -/

section Injectivity

variable {β : Ordinal.{u}} {M : Type v} {N : Type w}

/-- **An equality with a transport is an isomorphism**: if the transport of `G` along `e` is `H`,
then `e` is an isomorphism `G ≃ H`.  Native construction. -/
def equivOfTransportStructureEq (e : M ≃ N) {G : templateLanguage.{u}.Structure M}
    {H : templateLanguage.{u}.Structure N} (h : transportStructure e G = H) :
    @Language.Equiv templateLanguage.{u} M N G H :=
  h ▸ transportEquiv e G

/-- The underlying bijection of `equivOfTransportStructureEq e h` is `e`.  Native construction. -/
@[simp] theorem toEquiv_equivOfTransportStructureEq (e : M ≃ N)
    {G : templateLanguage.{u}.Structure M} {H : templateLanguage.{u}.Structure N}
    (h : transportStructure e G = H) :
    @Language.Equiv.toEquiv templateLanguage.{u} M N G H (equivOfTransportStructureEq e h) = e := by
  subst h
  rfl

/-- **Same-stage injectivity for `K_β[L]`**: for `β < ω₁` and a countable carrier `M`, if
`G ∈ K_β[L]` on `M` and `H ∈ K_β[L]` on `N` have an isomorphism `e` of base reducts, then `e` is an
isomorphism `G ≃ H` in `L_b[L] ∪ L_c[L]`.  The transport of `H` to `M` along `e⁻¹` is in
`K_β[L]` (`mem_templateStageClass_transportStructure`) with base reduct that of `G`
(`baseReduct_transportStructure`, `FirstOrder.Language.Equiv.inducedStructure_eq`), so it is `G`
by Reconstruction at `β` (`reconstructionTarget`).  Correspondence with the printed definitions. -/
theorem nonempty_equiv_of_baseReduct_equiv [Countable M] (hβ : β < ω₁)
    {G : templateLanguage.{u}.Structure M} {H : templateLanguage.{u}.Structure N}
    (hG : G ∈ templateStageClass M β) (hH : H ∈ templateStageClass N β)
    (e : @Language.Equiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H)) :
    ∃ g : @Language.Equiv templateLanguage.{u} M N G H,
      @Language.Equiv.toEquiv templateLanguage.{u} M N G H g =
        @Language.Equiv.toEquiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H) e := by
  set e₀ := @Language.Equiv.toEquiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H) e
  have hbase : baseReduct (transportStructure e₀.symm H) = baseReduct G := by
    rw [baseReduct_transportStructure]
    exact @Language.Equiv.inducedStructure_eq baseTemplateLanguage.{u} N M (baseReduct H)
      (baseReduct G)
      (@Language.Equiv.symm baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H) e)
  have hGH : G = transportStructure e₀.symm H :=
    reconstructionTarget β M inferInstance hβ G hG _
      (mem_templateStageClass_transportStructure e₀.symm hH) hbase.symm
  have ht : transportStructure e₀ G = H := by
    rw [hGH, transportStructure_transportStructure_symm]
  exact ⟨equivOfTransportStructureEq e₀ ht, toEquiv_equivOfTransportStructureEq e₀ ht⟩

variable (β M N)

/-- **Target C.T6, same-stage injectivity**: for `β < ω₁` and a countable carrier `M`, two
structures maximal at `β`, `G` on `M` and `H` on `N`, with an isomorphism `e` of base reducts, are
isomorphic in `L_b[L] ∪ L_c[L]` by the same bijection.  Correspondence with the printed
definitions. -/
def SameStageInjectivityTarget : Prop :=
  Countable M → β < ω₁ → ∀ (G : templateLanguage.{u}.Structure M)
    (H : templateLanguage.{u}.Structure N), IsMaximalAt β G → IsMaximalAt β H →
    ∀ e : @Language.Equiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H),
      ∃ g : @Language.Equiv templateLanguage.{u} M N G H,
        @Language.Equiv.toEquiv templateLanguage.{u} M N G H g =
          @Language.Equiv.toEquiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H) e

/-- **Target C.T6 holds** (`SameStageInjectivityTarget β M N` for every `β`, `M` and `N`), from
`nonempty_equiv_of_baseReduct_equiv`; maximality is used only through membership in `K_β[L]`.
Correspondence with the printed definitions. -/
theorem sameStageInjectivityTarget : SameStageInjectivityTarget β M N :=
  fun _ hβ _ _ hG hH e ↦ nonempty_equiv_of_baseReduct_equiv hβ hG.1 hH.1 e

end Injectivity

/-! ### The count (C.T10) -/

/-- **Target C.T10, the count of maximal structures** [AFK26, Proposition 4.35]: for `β < ω₁`,
a countable set `S` of structures on `ℕ`, each maximal at `β`, such that every structure maximal
at `β` on a countable carrier `M` is isomorphic, in the full language `L_b[L] ∪ L_c[L]`, to a
member of `S`.  Open; the assembly and the status of its inputs are in the module documentation.
Correspondence with the printed definitions. -/
def MaximalCountTarget (β : Ordinal.{u}) : Prop :=
  β < ω₁ → ∃ S : Set (templateLanguage.{u}.Structure ℕ), S.Countable ∧
    (∀ H ∈ S, IsMaximalAt β H) ∧
    ∀ (M : Type v) [Countable M] (G : templateLanguage.{u}.Structure M), IsMaximalAt β G →
      ∃ H ∈ S, Nonempty (@Language.Equiv templateLanguage.{u} M ℕ G H)

end

end VaughtConjecture

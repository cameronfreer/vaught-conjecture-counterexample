/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Presentation.Scheduler
import VaughtConjecture.Correspondence.Presentation.SuccessorLifting
import VaughtConjecture.Correspondence.Reconstruction.Targets

/-!
# Reconstruction: levels, the base case and the successor step

Write `λ_ξ = blockStage ξ`; level `ξ` is the label stage `λ_ξ`, and level zero is `λ_0 = ω`.
Equality at level `ξ` of two structures of `K_β[L]` is the equality `τ_ξ(G) = τ_ξ(H)` of
structures of `L_b[L] ∪ L_c[L]` on the same carrier.

* **Levels through the decoder** (correspondence with the printed definitions).  The projection to
  level `ξ` of the structure of a class realization with legal types is the structure of its
  reduction to `λ_ξ` (`ClassRealization.projectStructure_toStructure_reduce`, for `ξ < ω₁`),
  through `TemplateClass.globalClass_reduce_blockStage`.  Hence for `ξ ≤ β < ω₁`,
  `τ_ξ(G) = τ_ξ(H)` exactly when the decoded class realizations `decode β G` and `decode β H` have
  equal reductions to `λ_ξ` (`projectStructure_eq_iff`).
* **Base case** (`baseCaseTarget`).  At `λ_0 = ω`, a well-formed class realization is determined
  by the base reduct of its structure (`ClassRealization.eq_of_baseReduct_toStructure_eq`): `R_c`
  reads the class at `ω₁`, which at a stage at most `ω₁` determines the class.  With the base
  reduct read from the decoded class realization at `ω`
  (`baseReduct_eq_of_mem_templateStageClass`), equal base reducts give `τ_0(G) = τ_0(H)`.
* **Successor** (`successorTarget`, native construction in `ClassRealization.reduce_succ_eq`).
  For `ξ + 1 ≤ β < ω₁` on a countable carrier: present both decoded class realizations
  (`ClassRealization.exists_realization_classReading_eq`); their reductions to `λ_{ξ+1}` are
  strongly coded receiving (`Realization.reduce_stronglyCodedReceiving`); equal reductions to
  `λ_ξ` give a coherent renaming of the reductions to `λ_ξ` (`Realization.exists_coherentRenaming`),
  which lifts to `λ_{ξ+1}` with the same bijections (`liftingTarget`); coherently renamed
  realizations have equal class readings.  The hypothesis is equality at `λ_ξ` only; the renaming
  is produced at that stage, and no renaming is carried from one stage to another.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Classes: the class at `ω₁` of a reduction -/

namespace TemplateClass

variable {α : Ordinal.{u}} {n : ℕ}

/-- **The class at `ω₁` of a reduction is the projection of the class at `ω₁`**, for a block
stage `λ_ξ ≤ ω₁`.  Native construction. -/
theorem globalClass_reduce_blockStage {ξ : Ordinal.{u}} (hξ : blockStage ξ ≤ ω₁)
    (d : TemplateClass.{u} α n) :
    (d.reduce (isSuccPrelimit_blockStage ξ)).globalClass =
      d.globalClass.project (isSuccPrelimit_blockStage ξ) := by
  simp only [globalClass, project_eq_reduce_reduce, reduce_reduce _ _ hξ]

end TemplateClass

/-! ### Projection of the structure of a class realization -/

namespace ClassRealization

variable {M : Type v} {β ξ : Ordinal.{u}}

/-- **The projection to level `ξ` of the structure of a class realization is the structure of its
reduction to `λ_ξ`**: `τ_ξ(S.toStructure) = (S.reduce λ_ξ).toStructure`, for `ξ < ω₁` and a class
realization at any stage `α` with legal types.  Native construction. -/
theorem projectStructure_toStructure_reduce {α : Ordinal.{u}} (hξ : ξ < ω₁)
    {S : ClassRealization.{u, v} α M} (hl : S.HasLegalTypes) :
    projectStructure ξ S.toStructure = (S.reduce (isSuccPrelimit_blockStage ξ)).toStructure := by
  have hle : blockStage ξ ≤ ω₁ := (blockStage_lt_omega_one hξ).le
  have h0 : blockStage (0 : Ordinal.{u}) ≤ blockStage ξ :=
    blockStage_mono (zero_le : (0 : Ordinal.{u}) ≤ ξ)
  refine templateStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk =>
    change (∃ h : Function.Injective xs, ∃ c, S.eval ⟨xs, h⟩ = some c ∧ True) ↔
      ∃ h : Function.Injective xs, ∃ c, (S.eval ⟨xs, h⟩).map
        (TemplateClass.reduce (isSuccPrelimit_blockStage ξ)) = some c ∧ True
    refine exists_congr fun h ↦ ?_
    cases S.eval ⟨xs, h⟩ <;> simp
  | base c h0' hk =>
    change (∃ h : Function.Injective xs, ∃ d, S.eval ⟨xs, h⟩ = some d ∧
        d.globalClass.project (isSuccPrelimit_blockStage 0) = c.1) ↔
      ∃ h : Function.Injective xs, ∃ d, (S.eval ⟨xs, h⟩).map
        (TemplateClass.reduce (isSuccPrelimit_blockStage ξ)) = some d ∧
          d.globalClass.project (isSuccPrelimit_blockStage 0) = c.1
    refine exists_congr fun h ↦ ?_
    cases S.eval ⟨xs, h⟩ with
    | none => simp
    | some d =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left']
      rw [TemplateClass.globalClass_reduce_blockStage hle,
        TemplateClass.project_project_of_le _ _ _ h0]
  | invariant c hk =>
    rw [relMap_projectStructure_invariant]
    change (∃ c' : LegalClass.{u} _, c'.project ξ = c ∧ ∃ h : Function.Injective xs, ∃ d,
        S.eval ⟨xs, h⟩ = some d ∧ d.globalClass = c'.1) ↔
      ∃ h : Function.Injective xs, ∃ d, (S.eval ⟨xs, h⟩).map
        (TemplateClass.reduce (isSuccPrelimit_blockStage ξ)) = some d ∧ d.globalClass = c.1
    constructor
    · rintro ⟨c', rfl, h, d, hd, hdc⟩
      refine ⟨h, _, by rw [hd, Option.map_some], ?_⟩
      rw [TemplateClass.globalClass_reduce_blockStage hle, hdc]
      rfl
    · rintro ⟨h, e, he, hec⟩
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp he
      refine ⟨⟨d.globalClass, (TemplateClass.isStronglyCodedLegal_reduce_iff _ d).mpr
        (hl _ d hd)⟩, Subtype.ext ?_, h, d, hd, rfl⟩
      rw [LegalClass.coe_project, ← TemplateClass.globalClass_reduce_blockStage hle, hec]

/-- Reductions of a class realization compose to the lower one.  Native construction. -/
theorem reduce_reduce {α γ δ : Ordinal.{u}} (S : ClassRealization.{u, v} α M)
    (hγ : Order.IsSuccPrelimit γ) (hδ : Order.IsSuccPrelimit δ) (hδγ : δ ≤ γ) :
    (S.reduce hγ).reduce hδ = S.reduce hδ :=
  ext fun t ↦ by
    simp only [reduce_eval, Option.map_map]
    cases S.eval t <;> simp [TemplateClass.reduce_reduce _ _ hδγ]

/-- Reduction to the stage of the class realization is the identity.  Native construction. -/
theorem reduce_self {α : Ordinal.{u}} (S : ClassRealization.{u, v} α M)
    (hα : Order.IsSuccPrelimit α) : S.reduce hα = S :=
  ext fun t ↦ by
    simp only [reduce_eval]
    cases S.eval t <;> simp

end ClassRealization

/-! ### Levels of a structure of `K_β[L]` -/

variable {M : Type v} {β ξ : Ordinal.{u}} {G H : templateLanguage.{u}.Structure M}

/-- **The projection to level `ξ` of a structure of `K_β[L]` is the structure of its decoded
class realization reduced to `λ_ξ`**, for `ξ ≤ β < ω₁`.  Correspondence with the printed
definitions. -/
theorem projectStructure_eq_toStructure_decode_reduce (hβ : β < ω₁) (hξ : ξ ≤ β)
    (hG : G ∈ templateStageClass M β) :
    projectStructure ξ G =
      ((decode β G).reduce (isSuccPrelimit_blockStage ξ)).toStructure := by
  conv_lhs => rw [← hG.2.1.toStructure_decode hG.2.2.1]
  exact ClassRealization.projectStructure_toStructure_reduce (hξ.trans_lt hβ)
    hG.2.1.isWellFormed_decode.hasLegalTypes

/-- **Equality at a level is equality of the reduced decoded class realizations**: for
`ξ ≤ β < ω₁` and structures of `K_β[L]`, `τ_ξ(G) = τ_ξ(H)` exactly when the decoded class
realizations have equal reductions to `λ_ξ`.  Correspondence with the printed definitions. -/
theorem projectStructure_eq_iff (hβ : β < ω₁) (hξ : ξ ≤ β) (hG : G ∈ templateStageClass M β)
    (hH : H ∈ templateStageClass M β) :
    projectStructure ξ G = projectStructure ξ H ↔
      (decode β G).reduce (isSuccPrelimit_blockStage ξ) =
        (decode β H).reduce (isSuccPrelimit_blockStage ξ) := by
  rw [projectStructure_eq_toStructure_decode_reduce hβ hξ hG,
    projectStructure_eq_toStructure_decode_reduce hβ hξ hH]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  have hξ₁ : ξ < ω₁ := hξ.trans_lt hβ
  rw [← decode_toStructure hξ₁ (hG.2.1.isWellFormed_decode.reduce _),
    ← decode_toStructure hξ₁ (hH.2.1.isWellFormed_decode.reduce _), h]

/-! ### The base case -/

namespace ClassRealization

/-- **A well-formed class realization at level zero is determined by the base reduct of its
structure**: at `λ_0 = ω`, the symbol `P_k` records which tuples are typed, and `R_c` records the
class at `ω₁`, which determines the class at a stage at most `ω₁`
(`TemplateClass.globalClass_injective`).  Native construction. -/
theorem eq_of_baseReduct_toStructure_eq {S S' : ClassRealization.{u, v} (blockStage 0) M}
    (hS : S.IsWellFormed) (hS' : S'.IsWellFormed)
    (h : baseReduct S.toStructure = baseReduct S'.toStructure) : S = S' := by
  have h0 : blockStage (0 : Ordinal.{u}) ≤ ω₁ := by
    rw [blockStage_zero]
    exact omega0_lt_omega_one.le
  have hrel {k : ℕ} (r : BaseSymbol.{u} k) (xs : Fin k → M) :
      RelMap (L := templateLanguage.{u}) (self := S.toStructure) r.toTemplateSymbol xs ↔
        RelMap (L := templateLanguage.{u}) (self := S'.toStructure) r.toTemplateSymbol xs :=
    Iff.of_eq (congrArg (fun B : baseTemplateLanguage.{u}.Structure M ↦
      RelMap (L := baseTemplateLanguage.{u}) (self := B) r xs) h)
  refine ext fun {n} t ↦ ?_
  cases n with
  | zero =>
    rw [eval_zero hS.isConsistent hS.isCovering, eval_zero hS'.isConsistent hS'.isCovering]
  | succ n =>
    -- the class read by `R_c` at a typed tuple
    have key {T T' : ClassRealization.{u, v} (blockStage 0) M} (hT : T.IsWellFormed)
        (hrel' : ∀ {k : ℕ} (r : BaseSymbol.{u} k) (xs : Fin k → M),
          RelMap (L := templateLanguage.{u}) (self := T.toStructure) r.toTemplateSymbol xs →
            RelMap (L := templateLanguage.{u}) (self := T'.toStructure) r.toTemplateSymbol xs)
        {c : TemplateClass.{u} (blockStage 0) (n + 1)} (hc : T.eval t = some c) :
        T'.eval t = some c := by
      have hcl : c.globalClass.project (isSuccPrelimit_blockStage 0) = c.globalClass :=
        TemplateClass.project_globalClass _ h0 c
      let c' : LegalClass.{u} (n + 1) :=
        ⟨c.globalClass, (TemplateClass.isStronglyCodedLegal_reduce_iff _ c).mpr
          (hT.hasLegalTypes t c hc)⟩
      have := hrel' (BaseSymbol.base c' hcl n.succ_pos) t ⟨t.injective, c, hc, hcl⟩
      obtain ⟨_, d, hd, hdc⟩ := this
      change T'.eval t = some d at hd
      change d.globalClass.project (isSuccPrelimit_blockStage 0) = c.globalClass at hdc
      rw [TemplateClass.project_globalClass _ h0 d] at hdc
      rw [hd, TemplateClass.globalClass_injective (isSuccPrelimit_blockStage 0) h0 hdc]
    cases hc : S.eval t with
    | some c => exact (key hS (fun r xs ↦ (hrel r xs).mp) hc).symm
    | none =>
      cases hc' : S'.eval t with
      | none => rfl
      | some c' =>
        have := key hS' (fun r xs ↦ (hrel r xs).mpr) hc'
        rw [hc] at this
        exact absurd this (by simp)

end ClassRealization

/-- **The base case of Reconstruction holds** (`BaseCaseTarget β M` for every `β` and `M`): equal
base reducts give equal decoded class realizations at level zero
(`ClassRealization.eq_of_baseReduct_toStructure_eq`, with
`baseReduct_eq_of_mem_templateStageClass`), hence equal projections `τ_0`.  Used: `β < ω₁`.
Correspondence with the printed definitions. -/
theorem baseCaseTarget (β : Ordinal.{u}) (M : Type v) : BaseCaseTarget β M := by
  intro hβ G hG H hH h
  refine (projectStructure_eq_iff hβ (zero_le : (0 : Ordinal.{u}) ≤ β) hG hH).mpr ?_
  refine ClassRealization.eq_of_baseReduct_toStructure_eq
    (hG.2.1.isWellFormed_decode.reduce _) (hH.2.1.isWellFormed_decode.reduce _) ?_
  rw [← baseReduct_eq_of_mem_templateStageClass hG, ← baseReduct_eq_of_mem_templateStageClass hH,
    h]

/-! ### The successor step -/

namespace Realization

variable {α γ : Ordinal.{u}}

/-- **The reduction of a strongly coded receiving realization is strongly coded receiving**: for
an exactly consistent realization at a stage `α` that is zero or a limit, with strongly coded
legal types and finite-extension receiving for the strongly coded legal donors, its reduction to a
stage `γ ≤ α` that is zero or a limit has the same four properties.  Receiving descends through
finite-cut receiving (`Realization.HasFiniteCutReceivingIn.reduce_isStronglyCoded`).
Native construction. -/
theorem reduce_stronglyCodedReceiving {R : Realization.{u, v} α M} (hα : Order.IsSuccPrelimit α)
    (hR : R.IsConsistent)
    (hl : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal)
    (hrec : R.HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (hγ : Order.IsSuccPrelimit γ) (hγα : γ ≤ α) :
    (∀ x : (R.reduce hγ).Occurrence, x.type.rows.IsStronglyCoded) ∧
      (R.reduce hγ).HasLegalTypes ∧
      (R.reduce hγ).HasFiniteExtensionReceivingIn fun t ↦ t.rows.IsStronglyCoded := by
  refine ⟨fun x ↦ ?_, fun n t p hp ↦ ?_, ?_⟩
  · obtain ⟨p, hp, hpx⟩ := Option.map_eq_some_iff.mp x.eval_tuple
    rw [← hpx]
    exact (hl _ p hp).2
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact (hl _ q hq).1
  · exact (hasFiniteExtensionReceivingIn_isStronglyCoded_iff (hR.reduce hγ) hγ).mpr
      (hrec.hasFiniteCutReceivingIn.reduce_isStronglyCoded hα hγ hγα)

end Realization

namespace ClassRealization

/-- **The successor step on class realizations** (native construction): for `ξ + 1 ≤ β < ω₁` on
a countable carrier, two well-formed class realizations at `λ_β` with donor density whose
reductions to `λ_ξ` are equal have equal reductions to `λ_{ξ+1}`.

Proof: present both (`exists_realization_classReading_eq`); reduce the presentations to
`λ_{ξ+1}`, where they keep exact consistency, covering, strongly coded legal types and receiving
(`Realization.reduce_stronglyCodedReceiving`); their reductions to `λ_ξ` have equal class
readings, so they are related by a coherent renaming (`Realization.exists_coherentRenaming`),
which lifts with the same bijections to the reductions to `λ_{ξ+1}` (`liftingTarget`); coherently
renamed realizations have equal class readings. -/
theorem reduce_succ_eq [Countable M] (hβ : β < ω₁) (hξ : ξ + 1 ≤ β)
    {S S' : ClassRealization.{u, v} (blockStage β) M} (hS : S.IsWellFormed)
    (hS' : S'.IsWellFormed) (hd : S.HasDonorDensity) (hd' : S'.HasDonorDensity)
    (h : S.reduce (isSuccPrelimit_blockStage ξ) = S'.reduce (isSuccPrelimit_blockStage ξ)) :
    S.reduce (isSuccPrelimit_blockStage (ξ + 1)) =
      S'.reduce (isSuccPrelimit_blockStage (ξ + 1)) := by
  have hcount := Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ)
  obtain ⟨R, hR, hcov, hl, hrec, hread⟩ :=
    S.exists_realization_classReading_eq (isSuccPrelimit_blockStage β) hcount hS hd
  obtain ⟨R', hR', hcov', hl', hrec', hread'⟩ :=
    S'.exists_realization_classReading_eq (isSuccPrelimit_blockStage β) hcount hS' hd'
  have hle : blockStage (ξ + 1) ≤ blockStage β := blockStage_mono hξ
  have hle' : blockStage ξ ≤ blockStage (ξ + 1) := blockStage_mono (Order.le_succ ξ)
  obtain ⟨h𝒮₁, hl₁, hrec₁⟩ := Realization.reduce_stronglyCodedReceiving
    (isSuccPrelimit_blockStage β) hR hl hrec (isSuccPrelimit_blockStage (ξ + 1)) hle
  obtain ⟨h𝒮₁', hl₁', hrec₁'⟩ := Realization.reduce_stronglyCodedReceiving
    (isSuccPrelimit_blockStage β) hR' hl' hrec' (isSuccPrelimit_blockStage (ξ + 1)) hle
  -- equal class readings at `λ_ξ`, hence a coherent renaming there
  have hξread : ((R.reduce (isSuccPrelimit_blockStage (ξ + 1))).reduce
      (isSuccPrelimit_blockStage ξ)).classReading =
      ((R'.reduce (isSuccPrelimit_blockStage (ξ + 1))).reduce
        (isSuccPrelimit_blockStage ξ)).classReading := by
    rw [Realization.reduce_reduce _ _ _ hle', Realization.reduce_reduce _ _ _ hle',
      Realization.classReading_reduce, Realization.classReading_reduce, hread, hread', h]
  obtain ⟨c⟩ := Realization.exists_coherentRenaming
    ((hR.reduce _).reduce _) ((hR'.reduce _).reduce _) ((hcov.reduce _).reduce _) hξread
  obtain ⟨c', -⟩ := liftingTarget ξ M _ _ h𝒮₁ (hR.reduce _) (hcov.reduce _) hl₁ hrec₁
    h𝒮₁' (hR'.reduce _) (hcov'.reduce _) hl₁' hrec₁' c
  have := Realization.classReading_eq_of_coherentRenaming c'
  rwa [Realization.classReading_reduce, Realization.classReading_reduce, hread, hread'] at this

end ClassRealization

/-- **The successor step of Reconstruction holds** (`SuccessorTarget β ξ M` for every `β`, `ξ`
and `M`): for `ξ + 1 ≤ β < ω₁` on a countable carrier, equal projections of two structures of
`K_β[L]` to level `ξ` give equal projections to level `ξ + 1`
(`ClassRealization.reduce_succ_eq` for the decoded class realizations, which have donor density by
`mem_templateStageClass_iff`).  Used: `Countable M` and `β < ω₁`.  Correspondence with the printed
definitions. -/
theorem successorTarget (β ξ : Ordinal.{u}) (M : Type v) : SuccessorTarget β ξ M := by
  intro _ hβ hξ G hG H hH h
  have hξ' : ξ ≤ β := (Order.le_succ ξ).trans hξ
  refine (projectStructure_eq_iff hβ hξ hG hH).mpr ?_
  exact ClassRealization.reduce_succ_eq hβ hξ hG.2.1.isWellFormed_decode
    hH.2.1.isWellFormed_decode ((mem_templateStageClass_iff hβ G).mp hG).2.2.2
    ((mem_templateStageClass_iff hβ H).mp hH).2.2.2 ((projectStructure_eq_iff hβ hξ' hG hH).mp h)

end

end VaughtConjecture

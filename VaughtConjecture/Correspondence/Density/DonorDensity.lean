/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.Decoder

/-!
# Density through the decoder (target B.T6)

Numbering as in the current draft of [AFK26].

**Target B.T6** (`densityDecoderEquivalence`): for `β < ω₁`, a nonempty carrier, and a structure
`G` compatible with `ID[L]` and fixed by `τ_β`, density `D[α]` at every `α < ω + ω · β`
([AFK26, Definition 4.20]) holds exactly when the decoded class realization has donor density.

The four differences between the two notions are handled as follows.

* **Donors of every rank against donors at the stage.**  A printed donor `u` at `ω₁` is reduced
  to `ω + ω · β`, and a donor `D` at the stage is read at `ω₁`; for a cutoff `δ < ω + ω · β`,
  raw truncation at `δ` of the labels and capped observation at `δ` of the reduced labels agree
  (`TemplateClass.observesAt_reduce_iff_truncEquiv`, from `Label.min_reduce_of_le` and
  `Label.min_eq_min_iff_reduce_eq`), up to renaming on both sides.
* **Old points first against any embedding.**  The places of a donor are permuted so that the
  root comes first (`exists_equiv_castAdd`), the printed axiom is applied, and the witness is
  carried back along the inverse permutation; the observation passes to faces
  (`TemplateClass.LiftRel.exists_restrictFace`).
* **Roots on no points.**  `D[α]` has none.  Over the empty tuple, a point of the (nonempty)
  carrier lies in a typed tuple `v` (covering); the class of `v` and the donor embed jointly into
  a strongly coded legal class (`StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit`
  at the block stage); density over `v` gives a witness for the joint class, whose face is the
  witness for the donor.  This is the only use of `Nonempty M`.
* **Cutoffs.**  The permitted cutoffs `⊥ < x < ω + ω · β` are the ordinals below
  `ω + ω · β` (`Label.isPermittedCutoff_iff`), successors included.

The direction from donor density to `D[α]` uses neither fixedness, nor `β < ω₁`, nor
`Nonempty M`.
Uses compatibility — structured geometry and pair satisfaction — but not Definition 2.4(c), nor a
positional presentation.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Relations of classes: reduction, congruence, faces, joint embedding -/

namespace StageType

variable {γ : Ordinal.{u}} {n m : ℕ}

/-- **Same-scheme relations pass to faces**: if `u` has a face along `f`, so has `s`, and the
faces are related.  Native construction. -/
theorem LabelRel.exists_restrictFace {P : Label.{u} → Label.{u} → Prop}
    {s u : StageType.{u} γ n} (h : s.LabelRel P u) (f : Fin m ↪ Fin n) {u₁ : StageType.{u} γ m}
    (hu : restrictFace f u = some u₁) :
    ∃ s₁, restrictFace f s = some s₁ ∧ s₁.LabelRel P u₁ := by
  obtain ⟨hS, hl⟩ := h
  obtain ⟨S, p, a₁, a₂, a₃, a₄⟩ := s
  obtain ⟨S', p', _, _, _, _⟩ := u
  obtain rfl : S = S' := hS
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ f).mp hu
  exact ⟨_, restrictFace_of_mem (⟨S, p, a₁, a₂, a₃, a₄⟩ : StageType.{u} γ n) f hf, rfl,
    fun i j hij ↦ by
    obtain rfl := Fin.ext hij
    exact hl _ _ rfl⟩

end StageType

namespace TemplateClass

open StageType

variable {γ lam : Ordinal.{u}} {n m : ℕ}

/-- `LiftRel` depends only on the relation of labels.  Native construction. -/
theorem liftRel_congr {P Q : Label.{u} → Label.{u} → Prop} (h : ∀ a b, P a b ↔ Q a b)
    {c d : TemplateClass.{u} γ n} : LiftRel P c d ↔ LiftRel Q c d := by
  have hPQ : P = Q := funext fun a ↦ funext fun b ↦ propext (h a b)
  rw [hPQ]

/-- **Relations of reduced classes are relations of the reduced labels.**  Native
construction. -/
theorem liftRel_reduce_iff {P : Label.{u} → Label.{u} → Prop} (hlam : Order.IsSuccPrelimit lam)
    (c d : TemplateClass.{u} γ n) :
    LiftRel P (c.reduce hlam) (d.reduce hlam) ↔
      LiftRel (fun a b ↦ P (Label.reduce lam a) (Label.reduce lam b)) c d := by
  induction c using Quotient.inductionOn with
  | h s =>
  induction d using Quotient.inductionOn with
  | h u =>
    change LiftRel P (s.reduce hlam).toClass (u.reduce hlam).toClass ↔
      LiftRel _ s.toClass u.toClass
    rw [liftRel_toClass_iff, liftRel_toClass_iff]
    constructor
    · rintro ⟨_, ⟨k, σ, rfl⟩, hS, hl⟩
      exact ⟨s.renameCells σ, ⟨k, σ, rfl⟩, hS, hl⟩
    · rintro ⟨_, ⟨k, σ, rfl⟩, hS, hl⟩
      exact ⟨(s.reduce hlam).renameCells σ, ⟨k, σ, rfl⟩, hS, hl⟩

/-- **Capped observation of reduced classes at a cutoff below the stage is raw truncation**:
for `δ ≤ λ`, `(c ↓ λ)` observes `(d ↓ λ)` at `δ` exactly when `trunc_δ(c) ≅_ren trunc_δ(d)`.
Native construction. -/
theorem observesAt_reduce_iff_truncEquiv (hlam : Order.IsSuccPrelimit lam) {δ : Ordinal.{u}}
    (hδ : δ ≤ lam) (c d : TemplateClass.{u} γ n) :
    (c.reduce hlam).ObservesAt (δ : Label.{u}) (d.reduce hlam) ↔ c.TruncEquiv δ d := by
  rw [ObservesAt, liftRel_reduce_iff, TruncEquiv]
  have hδ' : ((δ : Label.{u})) ≤ (lam : Label.{u}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hδ)
  refine liftRel_congr fun a b ↦ ?_
  rw [Label.min_reduce_of_le hδ', Label.min_reduce_of_le hδ', Label.min_eq_min_iff_reduce_eq]

/-- **Related classes have related faces**: if the second has a face along `f`, so has the first,
and the faces are related.  Native construction. -/
theorem LiftRel.exists_restrictFace {P : Label.{u} → Label.{u} → Prop}
    {c d : TemplateClass.{u} γ n} (h : LiftRel P c d) (f : Fin m ↪ Fin n)
    {d' : TemplateClass.{u} γ m} (hd : d.restrictFace f = some d') :
    ∃ c', c.restrictFace f = some c' ∧ LiftRel P c' d' := by
  obtain ⟨s, u, rfl, rfl, hsu⟩ := h
  rw [restrictFace_toClass] at hd
  obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp hd
  obtain ⟨s₁, hs₁, h₁⟩ := hsu.exists_restrictFace f hu₁
  exact ⟨s₁.toClass, by rw [restrictFace_toClass, hs₁, Option.map_some], s₁, u₁, rfl, rfl, h₁⟩

/-- **Joint embedding of legal classes** at a stage that is zero or a limit (the strongly coded
joint embedding of `VaughtConjecture.Extension.StronglyCodedAmalgamation`, on classes).  Native
construction. -/
theorem exists_jointEmbedding (hγ : Order.IsSuccPrelimit γ) {j : ℕ}
    {e : TemplateClass.{u} γ j} {D : TemplateClass.{u} γ m} (he : e.IsStronglyCodedLegal)
    (hD : D.IsStronglyCodedLegal) :
    ∃ (K : ℕ) (Q : TemplateClass.{u} γ K) (i : Fin j ↪ Fin K) (i' : Fin m ↪ Fin K),
      Q.IsStronglyCodedLegal ∧ Q.restrictFace i = some e ∧ Q.restrictFace i' = some D := by
  induction e using Quotient.inductionOn with
  | h E =>
  induction D using Quotient.inductionOn with
  | h D' =>
    obtain ⟨K, Q, i, i', hQ, hi, hi'⟩ :=
      StageType.exists_stronglyCoded_jointEmbedding_of_isSuccPrelimit hγ he hD
    exact ⟨K, Q.toClass, i, i', hQ, by rw [restrictFace_toClass, hi, Option.map_some],
      by rw [restrictFace_toClass, hi', Option.map_some]⟩

end TemplateClass

/-! ### From `D[α]` to donor density -/

namespace IsTemplateCompatible

variable {M : Type v} {G : templateLanguage.{u}.Structure M} {β : Ordinal.{u}}
  (hG : IsTemplateCompatible G)
include hG

/-- **Donor density over a root on `n ≥ 1` points, from `D[α]`**: for `β < ω₁` and `G` fixed by
`τ_β`.  Native construction. -/
theorem exists_donor_of_satisfiesDensityAt (hβ : β < ω₁) (hfix : projectStructure β G = G)
    (hdens : ∀ α < blockStage β, SatisfiesDensityAt α G) {n m : ℕ} (hn : 0 < n)
    (t : Fin n ↪ M) {p : TemplateClass.{u} (blockStage β) n} (hp : (decode β G).eval t = some p)
    {D : TemplateClass.{u} (blockStage β) m} (g : Fin n ↪ Fin m) (hD : D.IsStronglyCodedLegal)
    (hDg : D.restrictFace g = some p) {δ : Ordinal.{u}} (hδ : δ < blockStage β) :
    ∃ u : Fin m ↪ M, g.trans u = t ∧
      ∃ q, (decode β G).eval u = some q ∧ q.ObservesAt (δ : Label.{u}) D := by
  have hlam := isSuccPrelimit_blockStage β
  have hlamω : blockStage β ≤ ω₁ := (blockStage_lt_omega_one hβ).le
  obtain ⟨c₀, hc₀, rfl⟩ := (decode_eval_eq_some_iff hG hn t p).mp hp
  -- put the root first in the donor
  obtain ⟨k, σ, hσ⟩ := exists_equiv_castAdd g
  obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.mp (D.isSome_restrictFace_equiv σ)
  let ca : Fin n ↪ Fin (n + k) := ⟨Fin.castAdd k, Fin.castAdd_injective n k⟩
  have hca : ca.trans σ.toEmbedding = g := Function.Embedding.ext hσ
  have hD'ca : D'.restrictFace ca = some (c₀.1.reduce hlam) := by
    rw [TemplateClass.restrictFace_trans hD' ca, hca, hDg]
  have hD'l : D'.IsStronglyCodedLegal := hD.restrictFace hD'
  let u₀ : LegalClass.{u} (n + k) :=
    ⟨D'.globalClass, (TemplateClass.isStronglyCodedLegal_reduce_iff _ _).mpr hD'l⟩
  have hc₀fix := hG.project_eq_of_relMap_invariant hfix hc₀
  have hpair : u₀.1.Holds (TemplateSymbol.invariant c₀ hn) (Fin.castAdd k) := by
    refine ⟨Fin.castAdd_injective n k, c₀.1, ?_, rfl⟩
    change (D'.reduce _).restrictFace ca = _
    rw [TemplateClass.restrictFace_reduce, hD'ca, Option.map_some]
    exact congrArg some (LegalClass.globalClass_reduce_of_project_eq hc₀fix)
  -- apply `D[δ]`
  obtain ⟨y, s, hsu, hs⟩ := (satisfiesDensityAt_iff δ G).mp (hdens δ hδ) hn c₀ u₀ hpair t hc₀
  have hw := hG.injective_of_relMap_invariant hs
  have hws : (decode β G).eval ⟨Fin.append t y, hw⟩ = some (s.1.reduce hlam) :=
    (decode_eval_eq_some_iff hG _ _ _).mpr ⟨s, hs, rfl⟩
  -- carry the witness back along the inverse permutation
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    ((s.1.reduce hlam).isSome_restrictFace_equiv σ.symm)
  refine ⟨σ.symm.toEmbedding.trans ⟨Fin.append t y, hw⟩, Function.Embedding.ext fun i ↦ ?_, q,
    (isConsistent_decode hG _ _ σ.symm.toEmbedding hws).trans hq, ?_⟩
  · have : σ.symm (g i) = Fin.castAdd k i := σ.symm_apply_eq.mpr (hσ i).symm
    change Fin.append t y (σ.symm (g i)) = t i
    rw [this, Fin.append_left]
  · have hobs : (s.1.reduce hlam).ObservesAt (δ : Label.{u}) D' := by
      have := (TemplateClass.observesAt_reduce_iff_truncEquiv hlam hδ.le s.1 u₀.1).mpr hsu
      rwa [TemplateClass.reduce_globalClass hlam hlamω] at this
    have hDD : D'.restrictFace σ.symm.toEmbedding = some D := by
      rw [TemplateClass.restrictFace_trans hD' σ.symm.toEmbedding]
      have : σ.symm.toEmbedding.trans σ.toEmbedding = Function.Embedding.refl _ :=
        Function.Embedding.ext fun j ↦ σ.apply_symm_apply j
      rw [this, TemplateClass.restrictFace_refl]
    obtain ⟨q', hq', hobs'⟩ := hobs.exists_restrictFace σ.symm.toEmbedding hDD
    rw [hq] at hq'
    rwa [Option.some.inj hq']

/-- **Donor density from `D[α]`**, for `β < ω₁`, a nonempty carrier, and `G` fixed by `τ_β`.
Native construction. -/
theorem hasDonorDensity_decode (hβ : β < ω₁) (hM : Nonempty M)
    (hfix : projectStructure β G = G) (hdens : ∀ α < blockStage β, SatisfiesDensityAt α G) :
    (decode β G).HasDonorDensity := by
  intro n m t p hp D g hD hDg x hx
  obtain ⟨δ, hδ, rfl⟩ := Label.isPermittedCutoff_iff.mp hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- a root on no points: a typed tuple through a point, and a joint donor
    obtain ⟨a⟩ := hM
    let a₁ : Fin 1 ↪ M := ⟨fun _ ↦ a, fun i j _ ↦ Subsingleton.elim i j⟩
    obtain ⟨j, v, f₁, -, hv⟩ := hG.isCovering_decode a₁
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hv
    have hj : 0 < j :=
      Nat.lt_of_lt_of_le Nat.one_pos (by simpa using Fintype.card_le_of_embedding f₁)
    obtain ⟨K, Q, i, i', hQ, hQi, hQi'⟩ := TemplateClass.exists_jointEmbedding
      (isSuccPrelimit_blockStage β) (hG.hasLegalTypes_decode v e he) hD
    obtain ⟨w, -, q, hq, hobs⟩ :=
      hG.exists_donor_of_satisfiesDensityAt hβ hfix hdens hj v he i hQ hQi hδ
    obtain ⟨q', hq', hobs'⟩ := hobs.exists_restrictFace i' hQi'
    exact ⟨i'.trans w, Function.Embedding.ext fun k ↦ k.elim0, q',
      (hG.isConsistent_decode w q i' hq).trans hq', hobs'⟩
  · exact hG.exists_donor_of_satisfiesDensityAt hβ hfix hdens hn t hp g hD hDg hδ

end IsTemplateCompatible

/-! ### From donor density to `D[α]` -/

/-- **`D[α]` from donor density**, at every `α < ω + ω · β`, for a compatible structure.  No
fixedness, no bound on `β`, no nonemptiness.  Native construction. -/
theorem IsTemplateCompatible.satisfiesDensityAt_of_hasDonorDensity {M : Type v}
    {G : templateLanguage.{u}.Structure M} {β : Ordinal.{u}} (hG : IsTemplateCompatible G)
    (hdd : (decode β G).HasDonorDensity) {α : Ordinal.{u}} (hα : α < blockStage β) :
    SatisfiesDensityAt α G := by
  have hlam := isSuccPrelimit_blockStage β
  refine (satisfiesDensityAt_iff α G).mpr fun n m hn t u hu x hx ↦ ?_
  have hxi := hG.injective_of_relMap_invariant hx
  have ht : (decode β G).eval ⟨x, hxi⟩ = some (t.1.reduce hlam) :=
    (decode_eval_eq_some_iff hG hn _ _).mpr ⟨t, hx, rfl⟩
  let ca : Fin n ↪ Fin (n + m) := ⟨Fin.castAdd m, Fin.castAdd_injective n m⟩
  obtain ⟨_, s, hs, hst⟩ := hu
  have hs' : u.1.restrictFace ca = some t.1 := by
    rw [← show s = t.1 from hst]
    exact hs
  have hDg : (u.1.reduce hlam).restrictFace ca = some (t.1.reduce hlam) := by
    rw [TemplateClass.restrictFace_reduce, hs', Option.map_some]
  obtain ⟨w, hw, q, hq, hobs⟩ := hdd ⟨x, hxi⟩ _ ht (u.1.reduce hlam) ca
    ((TemplateClass.isStronglyCodedLegal_reduce_iff _ _).mpr u.2) hDg (α : Label.{u})
    (Label.isPermittedCutoff_coe.mpr hα)
  obtain ⟨s', hs', rfl⟩ :=
    (decode_eval_eq_some_iff hG (Nat.lt_add_right m hn) w q).mp hq
  refine ⟨⇑w ∘ Fin.natAdd n, s',
    (TemplateClass.observesAt_reduce_iff_truncEquiv hlam hα.le s'.1 u.1).mp hobs, ?_⟩
  have hx' : x = ⇑w ∘ Fin.castAdd m := funext fun i ↦
    (congrArg (fun e : Fin n ↪ M ↦ e i) hw).symm
  have he : Fin.append (⇑w ∘ Fin.castAdd m) (⇑w ∘ Fin.natAdd n) = ⇑w :=
    Fin.append_castAdd_natAdd
  rw [hx', he]
  exact hs'

/-- **Target B.T6, density through the decoder** ([AFK26, Definitions 4.20 and 4.21]), for
`β < ω₁`: for a compatible structure on a nonempty carrier fixed by `τ_β`, `D[α]` at every
`α < ω + ω · β` holds exactly when its decoded class realization has donor density.
Correspondence with the printed definitions. -/
theorem densityDecoderEquivalence {M : Type v} {β : Ordinal.{u}} (hβ : β < ω₁) :
    DensityDecoderEquivalence β M :=
  fun _ hM hG hfix ↦ ⟨hG.hasDonorDensity_decode hβ hM hfix,
    fun hdd _ hα ↦ hG.satisfiesDensityAt_of_hasDonorDensity hdd hα⟩

/-! ### The class `K_β[L]` and its base reduct -/

/-- The class at `ω₁` of a class, projected to `ω`, does not change when the class is first
reduced to `ω`.  Native construction. -/
theorem TemplateClass.project_globalClass_reduce {α : Ordinal.{u}} {n : ℕ}
    (d : TemplateClass.{u} α n) :
    (d.reduce (isSuccPrelimit_blockStage 0)).globalClass.project (isSuccPrelimit_blockStage 0) =
      d.globalClass.project (isSuccPrelimit_blockStage 0) := by
  have h0 : blockStage (0 : Ordinal.{u}) ≤ ω₁ := by
    rw [blockStage_zero]
    exact omega0_lt_omega_one.le
  simp only [TemplateClass.globalClass, TemplateClass.project_eq_reduce_reduce,
    TemplateClass.reduce_reduce _ _ h0, TemplateClass.reduce_reduce _ _ (le_refl _)]

/-- **The base reduct of the structure of a class realization is read from its reduction to
`ω`** (manuscript level `0`, `blockStage 0 = ω`).  Native construction. -/
theorem ClassRealization.baseReduct_toStructure_reduce {α : Ordinal.{u}} {M : Type v}
    (R : ClassRealization.{u, v} α M) :
    baseReduct (R.reduce (isSuccPrelimit_blockStage 0)).toStructure = baseReduct R.toStructure := by
  refine baseStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk =>
    change (∃ h : Function.Injective xs, ∃ c, (R.eval ⟨xs, h⟩).map
        (TemplateClass.reduce (isSuccPrelimit_blockStage 0)) = some c ∧ True) ↔
      ∃ h : Function.Injective xs, ∃ c, R.eval ⟨xs, h⟩ = some c ∧ True
    refine exists_congr fun h ↦ ?_
    cases R.eval ⟨xs, h⟩ <;> simp
  | base c h0 hk =>
    change (∃ h : Function.Injective xs, ∃ d, (R.eval ⟨xs, h⟩).map
        (TemplateClass.reduce (isSuccPrelimit_blockStage 0)) = some d ∧
          d.globalClass.project (isSuccPrelimit_blockStage 0) = c.1) ↔
      ∃ h : Function.Injective xs, ∃ d, R.eval ⟨xs, h⟩ = some d ∧
        d.globalClass.project (isSuccPrelimit_blockStage 0) = c.1
    refine exists_congr fun h ↦ ?_
    cases R.eval ⟨xs, h⟩ with
    | none => simp
    | some d =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left']
      rw [TemplateClass.project_globalClass_reduce]

/-- **The base reduct of a structure of `K_β[L]`** ([AFK26, Definitions 2.2 and 4.17]: `G↾L_c[L]`)
**is read from its decoded class realization reduced to `ω`.**  Native construction. -/
theorem baseReduct_eq_of_mem_templateStageClass {M : Type v} {β : Ordinal.{u}}
    {G : templateLanguage.{u}.Structure M} (hG : G ∈ templateStageClass M β) :
    baseReduct G =
      baseReduct ((decode β G).reduce (isSuccPrelimit_blockStage 0)).toStructure := by
  rw [ClassRealization.baseReduct_toStructure_reduce, hG.2.1.toStructure_decode hG.2.2.1]

/-- **The class `K_β[L]` through the decoder** ([AFK26, Definition 4.21]), for `β < ω₁`: a
structure is in `K_β[L]` exactly when its carrier is nonempty, it is compatible with `ID[L]`,
fixed by `τ_β`, and its decoded class realization has donor density.  Correspondence with the
printed definitions. -/
theorem mem_templateStageClass_iff {M : Type v} {β : Ordinal.{u}} (hβ : β < ω₁)
    (G : templateLanguage.{u}.Structure M) :
    G ∈ templateStageClass M β ↔ Nonempty M ∧ IsTemplateCompatible G ∧
      projectStructure β G = G ∧ (decode β G).HasDonorDensity :=
  ⟨fun ⟨hM, hG, hfix, hd⟩ ↦ ⟨hM, hG, hfix, (densityDecoderEquivalence hβ G hM hG hfix).mp hd⟩,
    fun ⟨hM, hG, hfix, hd⟩ ↦ ⟨hM, hG, hfix, (densityDecoderEquivalence hβ G hM hG hfix).mpr hd⟩⟩

end

end VaughtConjecture

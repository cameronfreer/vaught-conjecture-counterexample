/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ReceivingIn
import VaughtConjecture.Correspondence.Reconstruction.Levels

/-!
# Reconstruction: limit separation, literal equality, and projection

Write `λ_ξ = blockStage ξ`; level `ξ` is the label stage `λ_ξ`, and level zero is `λ_0 = ω`.

* **Separation at a limit level** (native construction).  For a limit `δ`, finitely many labels at
  `λ_δ` lie at one lower stage `λ_ξ` (`Label.exists_lt_forall_atStage_blockStage`).  So two classes
  at `λ_δ` with equal reductions to every `λ_ξ`, `ξ < δ`, are equal
  (`TemplateClass.eq_of_forall_reduce_blockStage_eq`, hence `classSeparationTarget`): at one stage
  above the labels of two representatives, reduction changes no label, and the renaming witnessing
  equality at that stage is a renaming of the representatives.  Tuple by tuple, the same holds for
  class realizations (`ClassRealization.eq_of_forall_reduce_blockStage_eq`) and, through the
  decoder, for the projections of structures of `K_β[L]` (`limitSeparationTarget`).  Each
  hypothesis is an equality at its own level; no renamings coherent across levels are assumed or
  constructed.
* **Reconstruction** (`reconstructionTarget`, B.T10).  By transfinite induction on `ξ ≤ β`:
  `τ_ξ(G) = τ_ξ(H)` at level zero by the base case, at successors by the successor step, at limits
  by separation; at `ξ = β` this is `G = H`, literal equality on the carrier.
* **Projection** (`projectionTarget`, B.T9, at countable stages on countable carriers).
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Separation at a limit level -/

namespace Label

/-- **Finitely many labels at a limit block stage lie at one lower block stage**: for a limit
`δ`, finitely many labels at stage `λ_δ` are all at stage `λ_ξ` for some `ξ < δ`.
Native construction. -/
theorem exists_lt_forall_atStage_blockStage {δ : Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {k : ℕ} (f : Fin k → Label.{u}) (hf : ∀ i, AtStage (blockStage δ) (f i)) :
    ∃ ξ < δ, ∀ i, AtStage (blockStage ξ) (f i) := by
  have hex (i : Fin k) : ∃ ξ < δ, AtStage (blockStage ξ) (f i) := by
    rcases hf i with hi | hi
    · obtain ⟨ξ, hξ, hiξ⟩ := exists_lt_blockStage_of_lt hδ hi
      exact ⟨ξ, hξ, .inl hiξ⟩
    · exact ⟨0, hδ.pos, .inr hi⟩
  choose g hgδ hg using hex
  refine ⟨Finset.univ.sup g, ?_, fun i ↦ (hg i).mono (blockStage_mono ?_)⟩
  · exact (Finset.sup_lt_iff (by simpa using hδ.pos)).mpr fun i _ ↦ hgδ i
  · exact Finset.le_sup (f := g) (Finset.mem_univ i)

end Label

namespace TemplateClass

/-- **Separation of classes at a limit level** (native construction): for a limit `δ`, two classes
at `λ_δ` whose reductions to every `λ_ξ`, `ξ < δ`, are equal are equal.  Each hypothesis is an
equality of classes, witnessed by a renaming chosen at its own stage; one stage suffices: at a
stage `λ_ξ` above every label of two representatives other than the formal top, reduction changes
no label, so the renaming at that stage is a renaming of the representatives.  No family of
renamings coherent across stages is used. -/
theorem eq_of_forall_reduce_blockStage_eq {δ : Ordinal.{u}} (hδ : Order.IsSuccLimit δ) {n : ℕ}
    {c d : TemplateClass.{u} (blockStage δ) n}
    (h : ∀ ξ < δ,
      c.reduce (isSuccPrelimit_blockStage ξ) = d.reduce (isSuccPrelimit_blockStage ξ)) :
    c = d := by
  induction c using Quotient.inductionOn with
  | h s =>
  induction d using Quotient.inductionOn with
  | h t =>
  obtain ⟨ξ₁, hξ₁, hs⟩ := Label.exists_lt_forall_atStage_blockStage hδ s.label s.atStage
  obtain ⟨ξ₂, hξ₂, ht⟩ := Label.exists_lt_forall_atStage_blockStage hδ t.label t.atStage
  have hs' (i : Fin s.card) : Label.AtStage (blockStage (max ξ₁ ξ₂)) (s.label i) :=
    (hs i).mono (blockStage_mono (le_max_left _ _))
  have ht' (i : Fin t.card) : Label.AtStage (blockStage (max ξ₁ ξ₂)) (t.label i) :=
    (ht i).mono (blockStage_mono (le_max_right _ _))
  obtain ⟨k, σ, hσ⟩ := StageType.toClass_eq_toClass_iff.mp (h _ (max_lt hξ₁ hξ₂))
  have hsch := congrArg (fun x : StageType.{u} (blockStage (max ξ₁ ξ₂)) n ↦ x.toScheme) hσ
  refine StageType.toClass_eq_toClass_iff.mpr ⟨k, σ, StageType.ext (by exact hsch)
    fun i j hij ↦ ?_⟩
  have hl := StageType.label_congr hσ hij
  change Label.reduce _ (s.label (σ i)) = Label.reduce _ (t.label j) at hl
  exact ((hs' _).reduce_eq.symm.trans hl).trans (ht' j).reduce_eq

end TemplateClass

/-- **The class separation target holds** (`ClassSeparationTarget δ n` for every `δ` and `n`):
`TemplateClass.eq_of_forall_reduce_blockStage_eq`.  Native construction. -/
theorem classSeparationTarget (δ : Ordinal.{u}) (n : ℕ) : ClassSeparationTarget δ n :=
  fun hδ _ _ h ↦ TemplateClass.eq_of_forall_reduce_blockStage_eq hδ h

namespace ClassRealization

variable {M : Type v}

/-- **Separation of class realizations at a limit level** (native construction): for a limit
`δ`, two class realizations at `λ_δ` whose reductions to every `λ_ξ`, `ξ < δ`, are equal are
equal: tuple by tuple, by separation of classes
(`TemplateClass.eq_of_forall_reduce_blockStage_eq`). -/
theorem eq_of_forall_reduce_blockStage_eq {δ : Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {T T' : ClassRealization.{u, v} (blockStage δ) M}
    (h : ∀ ξ < δ,
      T.reduce (isSuccPrelimit_blockStage ξ) = T'.reduce (isSuccPrelimit_blockStage ξ)) :
    T = T' := by
  refine ext fun t ↦ ?_
  have ht (ξ : Ordinal.{u}) (hξ : ξ < δ) :
      (T.eval t).map (TemplateClass.reduce (isSuccPrelimit_blockStage ξ)) =
        (T'.eval t).map (TemplateClass.reduce (isSuccPrelimit_blockStage ξ)) :=
    congrArg (fun S : ClassRealization.{u, v} _ M ↦ S.eval t) (h ξ hξ)
  cases hc : T.eval t with
  | none =>
    cases hc' : T'.eval t with
    | none => rfl
    | some c' =>
      have := ht 0 hδ.pos
      rw [hc, hc'] at this
      exact absurd this (by simp)
  | some c =>
    cases hc' : T'.eval t with
    | none =>
      have := ht 0 hδ.pos
      rw [hc, hc'] at this
      exact absurd this (by simp)
    | some c' =>
      refine congrArg some (TemplateClass.eq_of_forall_reduce_blockStage_eq hδ fun ξ hξ ↦ ?_)
      have := ht ξ hξ
      rw [hc, hc'] at this
      exact Option.some.inj this

end ClassRealization

/-- **Separation at a limit level holds** (`LimitSeparationTarget β δ M` for every `β`, `δ` and
`M`): for a limit `δ ≤ β < ω₁`, equal projections of two structures of `K_β[L]` to every level
`ξ < δ` give equal projections to level `δ`.  Each hypothesis is an equality at its own level; no
renamings coherent across levels are assumed or constructed
(`ClassRealization.eq_of_forall_reduce_blockStage_eq`).  Used: `β < ω₁`.  Correspondence with the
printed definitions. -/
theorem limitSeparationTarget (β δ : Ordinal.{u}) (M : Type v) : LimitSeparationTarget β δ M := by
  intro hβ hδ hδβ G hG H hH h
  refine (projectStructure_eq_iff hβ hδβ hG hH).mpr
    (ClassRealization.eq_of_forall_reduce_blockStage_eq hδ fun ξ hξ ↦ ?_)
  have hle : blockStage ξ ≤ blockStage δ := blockStage_mono hξ.le
  rw [ClassRealization.reduce_reduce _ _ _ hle, ClassRealization.reduce_reduce _ _ _ hle]
  exact (projectStructure_eq_iff hβ (hξ.le.trans hδβ) hG hH).mp (h ξ hξ)

/-! ### Reconstruction -/

/-- **Target B.T10, Reconstruction, holds** (`ReconstructionTarget β M` for every `β` and `M`):
for `β < ω₁` on a countable carrier, two structures of `K_β[L]` with equal base reducts are equal,
literally, as structures of `L_b[L] ∪ L_c[L]` on the carrier.  By transfinite induction on the
level `ξ ≤ β`, `τ_ξ(G) = τ_ξ(H)`: level zero by the base case (`baseCaseTarget`), successor levels
by the successor step (`successorTarget`), limit levels by separation
(`limitSeparationTarget`); at level `β`, `τ_β(G) = G` and `τ_β(H) = H`.  Used: `Countable M` and
`β < ω₁`.  Correspondence with the printed definitions. -/
theorem reconstructionTarget (β : Ordinal.{u}) (M : Type v) : ReconstructionTarget β M := by
  intro hM hβ G hG H hH h
  have key : ∀ ξ : Ordinal.{u}, ξ ≤ β → projectStructure ξ G = projectStructure ξ H := by
    intro ξ
    induction ξ using WellFoundedLT.induction with
    | _ ξ ih =>
      intro hξ
      rcases zero_or_succ_or_isSuccLimit ξ with rfl | ⟨ζ, rfl⟩ | hlim
      · exact baseCaseTarget β M hβ G hG H hH h
      · have hlt : ζ < Order.succ ζ := Order.lt_succ ζ
        have hζβ : ζ ≤ β := hlt.le.trans hξ
        rw [Order.succ_eq_add_one] at hξ ⊢
        exact successorTarget β ζ M hM hβ hξ G hG H hH (ih ζ hlt hζβ)
      · exact limitSeparationTarget β ξ M hβ hlim hξ G hG H hH fun ζ hζ ↦
          ih ζ hζ (hζ.le.trans hξ)
  have := key β le_rfl
  rwa [hG.2.2.1, hH.2.2.1] at this

/-! ### Projection -/

/-- **Target B.T9, projection at countable stages on countable carriers, holds**
(`ProjectionTarget β ξ M` for every `β`, `ξ` and `M`): for `ξ ≤ β < ω₁` on a countable carrier,
`τ_ξ` sends `K_β[L]` into `K_ξ[L]`.  `τ_ξ(G)` is the structure of the reduction to `λ_ξ` of the
decoded class realization of `G` (`projectStructure_eq_toStructure_decode_reduce`), which is
well-formed, hence compatible (`ClassRealization.IsWellFormed.isTemplateCompatible`); `τ_ξ(G)` is
fixed by `τ_ξ`; and the reduction has donor density: it is the class reading of the reduction of
a strongly coded receiving presentation (`ClassRealization.exists_realization_classReading_eq`),
which is strongly coded receiving (`Realization.reduce_stronglyCodedReceiving`), and receiving
gives donor density of the class reading
(`Realization.HasFiniteExtensionReceivingIn.hasDonorDensity_classReading`).  The premises
`Countable M` and `β < ω₁` are those of this route; they are not shown to be necessary.
Correspondence with the printed definitions. -/
theorem projectionTarget (β ξ : Ordinal.{u}) (M : Type v) : ProjectionTarget β ξ M := by
  intro hM hβ hξ G hG
  have hξ₁ : ξ < ω₁ := hξ.trans_lt hβ
  have hS := hG.2.1.isWellFormed_decode (β := β)
  have hd := ((mem_templateStageClass_iff hβ G).mp hG).2.2.2
  have hred := hS.reduce (isSuccPrelimit_blockStage ξ)
  have hτ := projectStructure_eq_toStructure_decode_reduce hβ hξ hG
  -- donor density of the reduction, through a presentation
  have hcount := Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ)
  obtain ⟨R, hR, -, hl, hrec, hread⟩ :=
    (decode β G).exists_realization_classReading_eq (isSuccPrelimit_blockStage β) hcount hS hd
  obtain ⟨-, -, hrec'⟩ := Realization.reduce_stronglyCodedReceiving
    (isSuccPrelimit_blockStage β) hR hl hrec (isSuccPrelimit_blockStage ξ) (blockStage_mono hξ)
  have hdred : ((decode β G).reduce (isSuccPrelimit_blockStage ξ)).HasDonorDensity := by
    have := hrec'.hasDonorDensity_classReading
    rwa [Realization.classReading_reduce, hread] at this
  refine (mem_templateStageClass_iff hξ₁ _).mpr ⟨hG.1, ?_, projectStructure_projectStructure G, ?_⟩
  · rw [hτ]
    exact hred.isTemplateCompatible
  · rw [hτ, decode_toStructure hξ₁ hred]
    exact hdred

end

end VaughtConjecture

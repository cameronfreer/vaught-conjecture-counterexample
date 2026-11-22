/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.LegalSystem

/-!
# Projection on arbitrary carriers: [AFK26, Theorem 4.23]

Numbering as in the current draft of [AFK26].  `K_β[L]` is `templateStageClass M β`, `τ_ξ` is
`projectStructure ξ`, and `λ_ξ = blockStage ξ = ω + ω · ξ`.

* **Raw truncation up to renaming is symmetric and transitive on classes**
  (`TemplateClass.TruncEquiv.symm`, `TemplateClass.TruncEquiv.trans`), from the same facts for
  classes related cell by cell by a symmetric, resp. transitive, relation on labels.
* **The lifting step** (`projectionLiftTarget`, proved): for `ξ ≤ β < ω₁`, `G ∈ K_β[L]` on an
  arbitrary carrier and `δ < λ_ξ`, one request of `D[δ]` in `τ_ξ(G)` over a root `x`, and a
  higher root `t*` of `x` in `G`.  The pair `(Q_u(x y), Q_t(x))` gives `u↾castAdd = t = τ_ξ(t*)`,
  the face equation of clause (g) [AFK26, Definition 4.11 (g)] at `ξ`
  (`legalClassTruncRepairTarget`), which gives a legal class `v` with `v↾castAdd = t*` and
  `trunc_δ(v) ≅_ren trunc_δ(u)`.  `D[δ]` in `G` (`δ < λ_ξ ≤ λ_β`) for `(Q_v, Q_{t*})` at `x` gives
  `G ⊨ Q_w(x y)` with `trunc_δ(w) ≅_ren trunc_δ(v)`.  The pairs of `ID[L]` in `G`
  (`IsTemplateCompatible.relMap_comp_iff`), read at the first `n` places, where the tuple is `x`
  and `Q_{t*}` holds, give `w↾castAdd = t*`.  Projecting, `τ_ξ(G) ⊨ Q_{τ_ξ(w)}(x y)`, and
  `trunc_δ(τ_ξ(w)) = trunc_δ(w)` (`TemplateClass.truncEquiv_project_iff`).
* **Projection on arbitrary carriers** (`projectionArbitraryCarrierTarget`, proved): for
  `ξ ≤ β < ω₁` and any carrier, `τ_ξ(K_β[L]) ⊆ K_ξ[L]`.  Compatibility and the fixed point are as
  in `projectionTarget` (through the decoded class realization, no countability); density at every
  `δ < λ_ξ` is the lifting step, applied to the higher root `t*` that `τ_ξ(G) ⊨ Q_t(x)` provides on
  the same `x`.  No presentation is used, and `Countable M` is not a premise.  The countable
  statement `ProjectionTarget` follows (`projectionTarget_of_projectionArbitraryCarrierTarget`).
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal Correspondence

noncomputable section

/-! ### Raw truncation up to renaming is an equivalence on classes -/

namespace StageType

variable {γ : Ordinal.{u}} {n : ℕ}

/-- **Labels related cell by cell, composed**: for a transitive `P`, the relation of stage types
with the same scheme and `P`-related labels is transitive.  Native construction. -/
theorem LabelRel.trans {P : Label.{u} → Label.{u} → Prop} (hP : ∀ a b c, P a b → P b c → P a c)
    {s u w : StageType.{u} γ n} (h₁ : s.LabelRel P u) (h₂ : u.LabelRel P w) : s.LabelRel P w := by
  obtain ⟨hS₁, hl₁⟩ := h₁
  obtain ⟨hS₂, hl₂⟩ := h₂
  have hc : s.card = u.card := congrArg Scheme.card hS₁
  exact ⟨hS₁.trans hS₂, fun i j hij ↦
    hP _ _ _ (hl₁ i (Fin.cast hc i) rfl) (hl₂ (Fin.cast hc i) j hij)⟩

end StageType

namespace TemplateClass

variable {γ : Ordinal.{u}} {n : ℕ}

/-- **Classes related cell by cell by a symmetric relation, in the other order.**
Native construction. -/
theorem LiftRel.symm {P : Label.{u} → Label.{u} → Prop} (hP : ∀ a b, P a b → P b a)
    {c d : TemplateClass.{u} γ n} (h : LiftRel P c d) : LiftRel P d c := by
  obtain ⟨s, u, hs, hu, hS, hl⟩ := h
  exact ⟨u, s, hu, hs, hS.symm, fun j i hji ↦ hP _ _ (hl i j hji.symm)⟩

/-- **Classes related cell by cell by a transitive relation, composed**: the representative of the
middle class is aligned by renaming the representative of the first.  Native construction. -/
theorem LiftRel.trans {P : Label.{u} → Label.{u} → Prop} (hP : ∀ a b c, P a b → P b c → P a c)
    {c d e : TemplateClass.{u} γ n} (h₁ : LiftRel P c d) (h₂ : LiftRel P d e) : LiftRel P c e := by
  obtain ⟨s, u, rfl, rfl, h⟩ := h₁
  obtain ⟨u', w, hu', rfl, h'⟩ := h₂
  obtain ⟨k, σ, rfl⟩ := StageType.toClass_eq_toClass_iff.mp hu'.symm
  obtain ⟨π, hπ⟩ := h.exists_renameCells σ
  exact ⟨s.renameCells π, w, StageType.toClass_renameCells s π, rfl, hπ.trans hP h'⟩

/-- **Raw truncation at `α` up to renaming is symmetric** ([AFK26, Definitions 4.6 and 4.10]).
Correspondence with the printed definitions. -/
theorem TruncEquiv.symm {α : Ordinal.{u}} {c d : TemplateClass.{u} γ n} (h : c.TruncEquiv α d) :
    d.TruncEquiv α c :=
  LiftRel.symm (fun _ _ hab ↦ hab.symm) h

/-- **Raw truncation at `α` up to renaming is transitive** ([AFK26, Definitions 4.6 and 4.10]).
Correspondence with the printed definitions. -/
theorem TruncEquiv.trans {α : Ordinal.{u}} {c d e : TemplateClass.{u} γ n}
    (h₁ : c.TruncEquiv α d) (h₂ : d.TruncEquiv α e) : c.TruncEquiv α e :=
  LiftRel.trans (fun _ _ _ hab hbc ↦ hab.trans hbc) h₁ h₂

end TemplateClass

/-! ### The lifting step -/

/-- **Target: the lifting step of projection, holds** (`ProjectionLiftTarget β ξ M` for every
`β`, `ξ` and `M`): one request of `D[δ]`, `δ < λ_ξ`, in `τ_ξ(G)` for `G ∈ K_β[L]` on an arbitrary
carrier, over a root `x` and a higher root `t*` of `x` in `G`, is met by a donor `w` over `t*`
with `G ⊨ Q_w(x y)`, whose projection `τ_ξ(w)` holds of `x y` in `τ_ξ(G)` and agrees with the
requested class at the cutoff `δ`.  Route: clause (g) at `ξ` (`legalClassTruncRepairTarget`), `D[δ]`
in `G`, the pairs of `ID[L]` in `G` at the first `n` places
(`IsTemplateCompatible.relMap_comp_iff`), and `TemplateClass.truncEquiv_project_iff`.  Used:
`β < ω₁` and `ξ ≤ β`; no countability of the carrier.
Correspondence with the printed definitions. -/
theorem projectionLiftTarget (β ξ : Ordinal.{u}) (M : Type v) : ProjectionLiftTarget β ξ M := by
  intro hβ hξ G hG δ hδ n m hn t u hp x _ t' ht' hx'
  have hξω : ξ < ω₁ := hξ.trans_lt hβ
  have hnm : 0 < n + m := Nat.lt_add_right m hn
  -- the face of `u` at the first `n` places is `t = τ_ξ(t*)`
  obtain ⟨hinj, s, hus, hs⟩ := (mk_atom_mem_templateDiagramPairs_iff hnm u
    (TemplateSymbol.invariant t hn) (Fin.castAdd m)).mp hp
  change s = t.1 at hs
  subst hs
  have hface : u.1.restrictFace ⟨Fin.castAdd m, hinj⟩ = some (t'.project ξ).1 := by
    rw [hus, ht']
  -- clause (g) at `ξ` restores the higher root `t*`
  obtain ⟨v, hvf, hvu⟩ :=
    legalClassTruncRepairTarget ξ hξω ⟨Fin.castAdd m, hinj⟩ t' u hn hnm hface δ hδ
  -- density at `δ` in `G`
  have hpv : (⟨n + m, TemplateSymbol.invariant v hnm,
      atom (L := templateLanguage) (TemplateSymbol.invariant t' hn) (Fin.castAdd m)⟩ :
        DiagramPair templateLanguage.{u}) ∈ templateDiagramPairs :=
    (mk_atom_mem_templateDiagramPairs_iff hnm v _ _).mpr
      ⟨hinj, t'.1, hvf, show TemplateSymbol.Reads (TemplateSymbol.invariant t' hn) t'.1 from rfl⟩
  obtain ⟨y, w, hwv, hw⟩ :=
    hG.2.2.2 δ (hδ.trans_le (blockStage_mono hξ)) hn t' v hpv x hx'
  -- the root of the occurrence is `t*`
  have hcomp : Fin.append x y ∘ Fin.castAdd m = x := funext fun i ↦ Fin.append_left x y i
  have hroot : w.1.Holds (TemplateSymbol.invariant t' hn) (Fin.castAdd m) :=
    (hG.2.1.relMap_comp_iff hw (TemplateSymbol.invariant t' hn) (Fin.castAdd m)).mp
      (by rw [hcomp]; exact hx')
  obtain ⟨hinj', s', hws, hs'⟩ := hroot
  change s' = t'.1 at hs'
  subst hs'
  -- the cutoff
  have hwu : w.1.TruncEquiv δ u.1 := hwv.trans hvu
  refine ⟨y, w, (congrArg (w.1.restrictFace ·) (Function.Embedding.ext fun _ ↦ rfl :
    (⟨Fin.castAdd m, hinj'⟩ : Fin n ↪ Fin (n + m)) = Fin.castAddEmb m)).symm.trans hws, hw,
    ⟨w, rfl, hw⟩, ?_⟩
  exact ((TemplateClass.truncEquiv_project_iff (isSuccPrelimit_blockStage ξ)
    (blockStage_lt_omega_one hξω).le hδ.le u.1 w.1).mpr hwu.symm).symm

/-! ### Projection on arbitrary carriers -/

/-- **Target: projection on arbitrary carriers, holds** ([AFK26, Theorem 4.23], the inclusion
`τ_ξ(K_β[L]) ⊆ K_ξ[L]`; `ProjectionArbitraryCarrierTarget β ξ M` for every `β`, `ξ` and `M`): for
`ξ ≤ β < ω₁` and any carrier, `τ_ξ` sends `K_β[L]` into `K_ξ[L]`.  Compatibility: `τ_ξ(G)` is the
structure of the reduction to `λ_ξ` of the decoded class realization of `G`
(`projectStructure_eq_toStructure_decode_reduce`), which is well-formed; fixed point:
`projectStructure_projectStructure`; density at every `δ < λ_ξ`: `projectionLiftTarget`, at the
higher root that `τ_ξ(G) ⊨ Q_t(x)` provides on the same `x`.  Used: `β < ω₁` and `ξ ≤ β`; no
countability of the carrier, no presentation.  Correspondence with the printed definitions. -/
theorem projectionArbitraryCarrierTarget (β ξ : Ordinal.{u}) (M : Type v) :
    ProjectionArbitraryCarrierTarget β ξ M := by
  intro hβ hξ G hG
  have hS := hG.2.1.isWellFormed_decode (β := β)
  have hred := hS.reduce (isSuccPrelimit_blockStage ξ)
  have hτ := projectStructure_eq_toStructure_decode_reduce hβ hξ hG
  refine ⟨hG.1, ?_, projectStructure_projectStructure G, fun δ hδ n m hn t u hp x hx ↦ ?_⟩
  · rw [hτ]
    exact hred.isTemplateCompatible
  · obtain ⟨t', ht', hx'⟩ := hx
    obtain ⟨y, w, -, -, hw, hwu⟩ :=
      projectionLiftTarget β ξ M hβ hξ G hG δ hδ hn t u hp x ⟨t', ht', hx'⟩ t' ht' hx'
    exact ⟨y, w.project ξ, hwu, hw⟩

/-- **Projection at countable stages on countable carriers, through the arbitrary-carrier
statement**: `ProjectionTarget β ξ M` from `projectionArbitraryCarrierTarget`, the premise
`Countable M` unused.  Correspondence with the printed definitions. -/
theorem projectionTarget_of_arbitraryCarrier (β ξ : Ordinal.{u}) (M : Type v) :
    ProjectionTarget β ξ M :=
  projectionTarget_of_projectionArbitraryCarrierTarget (projectionArbitraryCarrierTarget β ξ M)

end

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CutoffStableRecovery
import VaughtConjecture.MainTheorem.CoatomDetermination

/-!
# Cutoff stable recovery at the first coatom

Roadmap, Layer 4, output 3 of higher-stage reconstruction, and Layer 3, 3.3–3.4 ((R4) of the table
of Layer 3, and the exact pinned extension); semantic contract, items 4 and 8.

Cutoff coatom completions (`StageType.HasCutoffCoatomCompletions`, in
`VaughtConjecture.Continuation.CutoffStableRecovery`) are asked at every closed coatom `g` of the
context `T⁺`.  This file reduces them to the first coatom `Fin.castSuccEmb`, the arrangement of
the coatom extension property.  Each item below is compiled in this repository (theorem named),
unless marked otherwise.

**Relabelling** (`StageType.IsCutoffStableRecovery.reindex_extendPerm`).  For a permutation `σ` of
the points of `T⁺` and its extension `τ` fixing the new point, a carrier `(q, δ)` of cutoff stable
recovery for `T⁺.reindex σ` along `f''` gives the carrier `(q.reindex τ⁻¹, δ)` for `T⁺` along
`f''.trans σ`.  Stage reduction commutes with reindexing (`StageType.reindex_reduce`), and
receiving families reindex.

**The graded cap calibration is invariant under relabelling**
(`StageType.GradedCapCalibration.reindex`): it depends only on the labels and grades of the cells
of `T⁺`, and reindexing along a bijection keeps every cell (`Scheme.surjective_cellMap_equiv`).

**The first-coatom form** (`StageType.HasCutoffFirstCoatomCompletions`, open;
`StageType.HasCutoffFirstCoatomCompletions.hasCutoffCoatomCompletions`).  Cutoff coatom completions
at the first coatom give them at every closed coatom, for a calibration invariant under
relabelling: the coatom is the first one after relabelling
(`StageType.exists_perm_castSuccEmb_trans`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- A root followed by the new point, then the inverse extension, is the root relabelled by the
inverse followed by the new point. -/
theorem extendByLast_trans_extendPerm_symm {n : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin n ↪ Fin m) :
    (extendByLast h).trans (extendPerm σ).symm.toEmbedding =
      extendByLast (h.trans σ.symm.toEmbedding) := by
  refine Function.Embedding.ext fun i ↦ ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [Function.Embedding.trans_apply, extendByLast_last, Equiv.coe_toEmbedding]
    rw [Equiv.symm_apply_eq, extendPerm_last]
  | cast i => simp [extendPerm_symm_castSucc]

/-- **Cutoff stable recovery relabels**: a carrier `(q, δ)` for `T⁺.reindex σ` along `f''` gives
the carrier `(q.reindex τ⁻¹, δ)` for `T⁺` along `f''.trans σ`, for the extension `τ` of `σ` fixing
the new point. -/
theorem IsCutoffStableRecovery.reindex_extendPerm {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {σ : Equiv.Perm (Fin m)} {f'' : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {q : StageType.{u} (blockStage ξ) (m + 1)} {δ : Label.{u}}
    (h : (Tp.reindex σ).IsCutoffStableRecovery f'' D γ q δ) :
    Tp.IsCutoffStableRecovery (f''.trans σ.toEmbedding) D γ (q.reindex (extendPerm σ).symm) δ := by
  obtain ⟨hq, hδ, hrec⟩ := h
  refine ⟨reindex_extendPerm_symm_mem_cofaces (by rwa [reindex_reduce]), hδ, fun Q' hQ' hQ'T ↦ ?_⟩
  have hQ'' := reindex_mem_receivingFamily (extendPerm σ) hQ'
  rw [reindex_reindex, Equiv.self_trans_symm, reindex_refl, reindex_reduce] at hQ''
  have hface : restrictFace Fin.castSuccEmb (Q'.reindex (extendPerm σ)) = some (Tp.reindex σ) := by
    rw [restrictFace_reindex, castSuccEmb_trans_extendPerm, ← restrictFace_trans Q' _ _ hQ'T,
      restrictFace_equiv]
  obtain ⟨Q, hQ, hS, hl⟩ := hrec _ hQ'' hface
  refine ⟨Q, ?_, hS, hl⟩
  rwa [restrictFace_reindex, extendByLast_trans_extendPerm] at hQ

/-- **The graded cap calibration is invariant under relabelling**: it depends only on the labels
and the grades of the cells of `T⁺`, which reindexing along a bijection keeps. -/
theorem GradedCapCalibration.reindex {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapCalibration ξ Tp f D γ) (σ : Equiv.Perm (Fin m)) (f' : Fin k ↪ Fin m) :
    GradedCapCalibration ξ (Tp.reindex σ) f' D γ := by
  have hcell (b : Fin Tp.card) : ∃ b' : Fin (Tp.reindex σ).card,
      (Tp.reindex σ).label b' = Tp.label b ∧
        (Tp.reindex σ).toCellScheme.grade b' = Tp.toCellScheme.grade b := by
    obtain ⟨b', rfl⟩ := Tp.toScheme.surjective_cellMap_equiv σ b
    exact ⟨b', rfl, rfl⟩
  obtain ⟨b, hb, hk, hγ, href⟩ := h
  obtain ⟨b', hb'l, hb'g⟩ := hcell b
  refine ⟨b', ?_, ?_, ?_, fun j o ho ↦ ?_⟩
  · rw [hb'l, hb'g]
    exact hb
  · rwa [hb'g]
  · rwa [hb'g]
  · obtain ⟨μ, n, i, a, hμ, ho', hn, hi, ha, hal⟩ := href j o ho
    obtain ⟨a', ha'l, ha'g⟩ := hcell a
    exact ⟨μ, n, i, a', hμ, ho', hb'g ▸ hn, hb'g ▸ hi, by rw [ha'g, hb'g]; exact ha,
      ha'l.trans hal⟩

variable (ξ) in
/-- **Cutoff completions at the first coatom for a calibration `C`** (a named statement; open):
the statement of `StageType.HasCutoffCoatomCompletions` at the first coatom `Fin.castSuccEmb` of
`T⁺`, the arrangement of the coatom extension property.  For every legal `T⁺` on `m + 1` points
with face `p` along `Fin.castSuccEmb`, legal coface `tb` of `p`, embedding `f` of `k > 0` points
with face `P` of `p`, coface `D` of `P` that is the face of `tb` along `f` followed by the new
point, and `γ < λ_{ξ+1}` with `C T⁺ (f.trans Fin.castSuccEmb) D γ`, there are a coface `q` of
`T⁺↓λ_ξ` with face `tb↓λ_ξ` along `extendByLast Fin.castSuccEmb` and a cutoff `δ` carrying cutoff
stable recovery for `T⁺`, `f.trans Fin.castSuccEmb`, `D` and `γ`.  The carrier is chosen for the
input, before any stage type of the class. -/
def HasCutoffFirstCoatomCompletions
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (p : StageType.{u} (blockStage (ξ + 1)) m) (tb : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (f : Fin k ↪ Fin m) (P : StageType.{u} (blockStage (ξ + 1)) k),
    Tp.IsLegal → restrictFace Fin.castSuccEmb Tp = some p → tb ∈ p.cofaces → 0 < k →
    restrictFace f p = some P → ∀ D ∈ P.cofaces, restrictFace (extendByLast f) tb = some D →
      ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) → C Tp (f.trans Fin.castSuccEmb) D γ →
        ∃ (q : StageType.{u} (blockStage ξ) (m + 2)) (δ : Label.{u}),
          restrictFace (extendByLast Fin.castSuccEmb) q =
              some (tb.reduce (isSuccPrelimit_blockStage ξ)) ∧
            Tp.IsCutoffStableRecovery (f.trans Fin.castSuccEmb) D γ q δ

/-- **Cutoff coatom completions from the first coatom**, for a calibration `C` invariant under
relabelling the points of `T⁺` with the root relabelled along (`hinv`). -/
theorem HasCutoffFirstCoatomCompletions.hasCutoffCoatomCompletions
    {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (hinv : ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
      (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) (σ : Equiv.Perm (Fin m)),
      C Tp f D γ → C (Tp.reindex σ) (f.trans σ.symm.toEmbedding) D γ)
    (h : HasCutoffFirstCoatomCompletions ξ C) : HasCutoffCoatomCompletions ξ C := by
  intro m k Tp g p tb f P hT hp htb hk hP D hD htbD γ hγ hC
  obtain ⟨σ, hσ⟩ := exists_perm_castSuccEmb_trans g
  have hp'' : restrictFace Fin.castSuccEmb (Tp.reindex σ) = some p := by
    rw [restrictFace_reindex, hσ, hp]
  have hroot : (f.trans g).trans σ.symm.toEmbedding = f.trans Fin.castSuccEmb :=
    Function.Embedding.ext fun i ↦ by simp [← hσ]
  have hC'' := hinv Tp _ D γ σ hC
  rw [hroot] at hC''
  obtain ⟨q, δ, hqtb, hq⟩ :=
    h (Tp.reindex σ) p tb f P (hT.reindex σ) hp'' htb hk hP D hD htbD γ hγ hC''
  have hroot' : (f.trans Fin.castSuccEmb).trans σ.toEmbedding = f.trans g := by
    rw [Function.Embedding.trans_assoc, hσ]
  refine ⟨q.reindex (extendPerm σ).symm, δ, ?_, hroot' ▸ hq.reindex_extendPerm⟩
  have hg : g.trans σ.symm.toEmbedding = Fin.castSuccEmb :=
    Function.Embedding.ext fun i ↦ by simp [← hσ]
  rw [restrictFace_reindex, extendByLast_trans_extendPerm_symm, hg, hqtb]

/-- **Cutoff stable recovery for the graded cap calibration from first-coatom completions**: the
graded cap calibration is invariant under relabelling and forces a private point. -/
theorem HasCutoffFirstCoatomCompletions.hasCutoffStableRecoverySchemes_gradedCap
    (h : HasCutoffFirstCoatomCompletions ξ (GradedCapCalibration ξ)) :
    HasCutoffStableRecoverySchemes ξ (GradedCapCalibration ξ) :=
  (h.hasCutoffCoatomCompletions fun _ _ _ _ _ _ σ hC ↦
    hC.reindex σ _).hasCutoffStableRecoverySchemes fun _ _ _ _ _ _ hC ↦ hC.lt

/-- **The margin calibration is invariant under relabelling**: like the graded cap calibration, it
depends only on the labels and the grades of the cells of `T⁺`. -/
theorem GradedCapMarginCalibration.reindex {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibration ξ Tp f D γ) (σ : Equiv.Perm (Fin m)) (f' : Fin k ↪ Fin m) :
    GradedCapMarginCalibration ξ (Tp.reindex σ) f' D γ := by
  have hcell (b : Fin Tp.card) : ∃ b' : Fin (Tp.reindex σ).card,
      (Tp.reindex σ).label b' = Tp.label b ∧
        (Tp.reindex σ).toCellScheme.grade b' = Tp.toCellScheme.grade b := by
    obtain ⟨b', rfl⟩ := Tp.toScheme.surjective_cellMap_equiv σ b
    exact ⟨b', rfl, rfl⟩
  obtain ⟨b, hb, hk, ⟨R, hR, hγ⟩, ⟨a, i, hi, ha, hal⟩, href⟩ := h
  obtain ⟨b', hb'l, hb'g⟩ := hcell b
  obtain ⟨a', ha'l, ha'g⟩ := hcell a
  refine ⟨b', ?_, ?_, ⟨R, hb'g ▸ hR, hγ⟩, ⟨a', i, hb'g ▸ hi, by rw [ha'g, hb'g]; exact ha,
    ha'l.trans hal⟩, fun j o ho ↦ ?_⟩
  · rw [hb'l, hb'g]
    exact hb
  · rwa [hb'g]
  · obtain ⟨μ, n, i, c, hμ, ho', hn, hi, hc, hcl⟩ := href j o ho
    obtain ⟨c', hc'l, hc'g⟩ := hcell c
    exact ⟨μ, n, i, c', hμ, ho', hb'g ▸ hn, hb'g ▸ hi, by rw [hc'g, hb'g]; exact hc,
      hc'l.trans hcl⟩

/-- **First-coatom completions for the graded cap calibration give them for the margin
calibration**: the inputs of the margin calibration are inputs of the graded cap calibration
(`StageType.GradedCapMarginCalibration.gradedCapCalibration`). -/
theorem HasCutoffFirstCoatomCompletions.gradedCapMargin
    (h : HasCutoffFirstCoatomCompletions ξ (GradedCapCalibration ξ)) :
    HasCutoffFirstCoatomCompletions ξ (GradedCapMarginCalibration ξ) :=
  fun _ _ Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC ↦
    h Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC.gradedCapCalibration

/-- **Cutoff stable recovery for the margin calibration from first-coatom completions**: the
margin calibration is invariant under relabelling and forces a private point. -/
theorem HasCutoffFirstCoatomCompletions.hasCutoffStableRecoverySchemes_gradedCapMargin
    (h : HasCutoffFirstCoatomCompletions ξ (GradedCapMarginCalibration ξ)) :
    HasCutoffStableRecoverySchemes ξ (GradedCapMarginCalibration ξ) :=
  (h.hasCutoffCoatomCompletions fun _ _ _ _ _ _ σ hC ↦
    hC.reindex σ _).hasCutoffStableRecoverySchemes fun _ _ _ _ _ _ hC ↦
      hC.gradedCapCalibration.lt

end StageType

end VaughtConjecture

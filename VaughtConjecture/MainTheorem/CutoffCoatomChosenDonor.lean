/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CutoffCoatomRelabel

/-!
# Cutoff coatom completions with a chosen intermediate coface

Roadmap, Layer 4 (stable recovery schemes) and Layer 3 ((R4) of the table of 3.4).

The cutoff coatom completions (`StageType.HasCutoffCoatomCompletions`,
`StageType.HasCutoffFirstCoatomCompletions`) quantify over every intermediate coface `tb` of the
face `p` of `T⁺` along the coatom with face `D` along the root followed by the new point.  The
reduction to cutoff stable recovery
(`StageType.HasCutoffCoatomCompletions.hasCutoffStableRecoverySchemes`) uses one such coface, the
exact pinned extension.  Compiled in this repository (theorem named):

* **The forms with a chosen coface** (`StageType.HasCutoffCoatomCompletionsEx`,
  `StageType.HasCutoffFirstCoatomCompletionsEx`): at every input, some legal coface `tb` of `p`
  with face `D` carries a coatom completion.
* **They are implied by the forms over every coface** (`StageType.HasCutoffCoatomCompletions.ex`,
  `StageType.HasCutoffFirstCoatomCompletions.ex`), the coface being the exact pinned extension
  under the compiled coatom extension property at `λ_{ξ+1}`; so the forms over every coface are the
  stronger statements.
* **They suffice** (`StageType.HasCutoffCoatomCompletionsEx.hasCutoffStableRecoverySchemes`,
  `StageType.HasCutoffFirstCoatomCompletionsEx.hasCutoffCoatomCompletionsEx`): the reduction to
  cutoff stable recovery and the reduction to the first coatom (for a calibration invariant under
  relabelling) go through unchanged.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {ξ : Ordinal.{u}}

variable (ξ) in
/-- **Cutoff coatom completions with a chosen coface** for a calibration `C`: the statement of
`StageType.HasCutoffCoatomCompletions` with the intermediate coface `tb` chosen at each input. -/
def HasCutoffCoatomCompletionsEx
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (g : Fin m ↪ Fin (m + 1))
    (p : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k),
    Tp.IsLegal → restrictFace g Tp = some p → 0 < k → restrictFace f p = some P →
    ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) → C Tp (f.trans g) D γ →
      ∃ tb ∈ p.cofaces, restrictFace (extendByLast f) tb = some D ∧
        ∃ (q : StageType.{u} (blockStage ξ) (m + 2)) (δ : Label.{u}),
          restrictFace (extendByLast g) q = some (tb.reduce (isSuccPrelimit_blockStage ξ)) ∧
            Tp.IsCutoffStableRecovery (f.trans g) D γ q δ

variable (ξ) in
/-- **Cutoff completions at the first coatom with a chosen coface**: the statement of
`StageType.HasCutoffFirstCoatomCompletions` with the intermediate coface chosen at each input. -/
def HasCutoffFirstCoatomCompletionsEx
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (p : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k),
    Tp.IsLegal → restrictFace Fin.castSuccEmb Tp = some p → 0 < k → restrictFace f p = some P →
    ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      C Tp (f.trans Fin.castSuccEmb) D γ →
      ∃ tb ∈ p.cofaces, restrictFace (extendByLast f) tb = some D ∧
        ∃ (q : StageType.{u} (blockStage ξ) (m + 2)) (δ : Label.{u}),
          restrictFace (extendByLast Fin.castSuccEmb) q =
              some (tb.reduce (isSuccPrelimit_blockStage ξ)) ∧
            Tp.IsCutoffStableRecovery (f.trans Fin.castSuccEmb) D γ q δ

variable {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
  StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}

/-- **The form over every coface gives the form with a chosen coface**: the exact pinned extension
is a coface of `p` with face `D`. -/
theorem HasCutoffCoatomCompletions.ex (h : HasCutoffCoatomCompletions ξ C) :
    HasCutoffCoatomCompletionsEx ξ C := by
  intro m k Tp g p f P hT hp hk hP D hD γ hγ hC
  obtain ⟨tb, htb, htbp, htbD⟩ := exists_pinned_extension
    (hasCoatomExtensions (isSuccPrelimit_blockStage (ξ + 1))) (hT.restrictFace g hp) hP hD.1 hD.2
  exact ⟨tb, ⟨htb, htbp⟩, htbD, h Tp g p tb f P hT hp ⟨htb, htbp⟩ hk hP D hD htbD γ hγ hC⟩

/-- **The first-coatom form over every coface gives the form with a chosen coface.** -/
theorem HasCutoffFirstCoatomCompletions.ex (h : HasCutoffFirstCoatomCompletions ξ C) :
    HasCutoffFirstCoatomCompletionsEx ξ C := by
  intro m k Tp p f P hT hp hk hP D hD γ hγ hC
  obtain ⟨tb, htb, htbp, htbD⟩ := exists_pinned_extension
    (hasCoatomExtensions (isSuccPrelimit_blockStage (ξ + 1))) (hT.restrictFace _ hp) hP hD.1 hD.2
  exact ⟨tb, ⟨htb, htbp⟩, htbD, h Tp p tb f P hT hp ⟨htb, htbp⟩ hk hP D hD htbD γ hγ hC⟩

/-- **Cutoff stable recovery from cutoff coatom completions with a chosen coface**, for a
calibration that forces a private point. -/
theorem HasCutoffCoatomCompletionsEx.hasCutoffStableRecoverySchemes
    (hC : ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
      (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}), C Tp f D γ → k < m)
    (h : HasCutoffCoatomCompletionsEx ξ C) : HasCutoffStableRecoverySchemes ξ C := by
  intro m k Tp f P hT hk hP D hD γ hγ hCf
  have hkm : k < m := hC Tp f D γ hCf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfT : univ.map f ∈ Tp.toCellScheme.faces := ((restrictFace_eq_some_iff Tp f).mp hP).1
  obtain ⟨g, f', hg, rfl⟩ := Tp.exists_coatom_trans_eq f hfT (by omega)
  have hTp : restrictFace g Tp = some (Tp.comap g hg) := restrictFace_of_mem Tp g hg
  have hpP : restrictFace f' (Tp.comap g hg) = some P := (restrictFace_trans Tp g f' hTp).trans hP
  obtain ⟨-, -, -, q, δ, -, hq⟩ := h Tp g _ f' P hT hTp hk hpP D hD γ hγ hCf
  exact ⟨q, δ, hq⟩

/-- **Cutoff coatom completions with a chosen coface from the first coatom**, for a calibration
invariant under relabelling the points of `T⁺` with the root relabelled along. -/
theorem HasCutoffFirstCoatomCompletionsEx.hasCutoffCoatomCompletionsEx
    (hinv : ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
      (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) (σ : Equiv.Perm (Fin m)),
      C Tp f D γ → C (Tp.reindex σ) (f.trans σ.symm.toEmbedding) D γ)
    (h : HasCutoffFirstCoatomCompletionsEx ξ C) : HasCutoffCoatomCompletionsEx ξ C := by
  intro m k Tp g p f P hT hp hk hP D hD γ hγ hC
  obtain ⟨σ, hσ⟩ := exists_perm_castSuccEmb_trans g
  have hp'' : restrictFace Fin.castSuccEmb (Tp.reindex σ) = some p := by
    rw [restrictFace_reindex, hσ, hp]
  have hroot : (f.trans g).trans σ.symm.toEmbedding = f.trans Fin.castSuccEmb :=
    Function.Embedding.ext fun i ↦ by simp [← hσ]
  have hC'' := hinv Tp _ D γ σ hC
  rw [hroot] at hC''
  obtain ⟨tb, htb, htbD, q, δ, hqtb, hq⟩ :=
    h (Tp.reindex σ) p f P (hT.reindex σ) hp'' hk hP D hD γ hγ hC''
  have hroot' : (f.trans Fin.castSuccEmb).trans σ.toEmbedding = f.trans g := by
    rw [Function.Embedding.trans_assoc, hσ]
  refine ⟨tb, htb, htbD, q.reindex (extendPerm σ).symm, δ, ?_, hroot' ▸ hq.reindex_extendPerm⟩
  have hg : g.trans σ.symm.toEmbedding = Fin.castSuccEmb :=
    Function.Embedding.ext fun i ↦ by simp [← hσ]
  rw [restrictFace_reindex, extendByLast_trans_extendPerm_symm, hg, hqtb]

end StageType

end VaughtConjecture

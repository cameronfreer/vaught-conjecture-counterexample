/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.Continuation.StableRecoveryCounterexample

/-!
# Stable recovery lifts from a closed face of the context

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the decoder of (R4)) with 3.4 (the exact pinned extension); semantic contract, items 4 and 8.

The reading coatom completion (`StageType.HasReadingCoatomCompletions`, a named hypothesis, open)
asks for the cells at the top graded face `(univ, N)` of the last coatom extension to read through
the cap.  A coatom extension does not control those cells.  It does carry recovery upwards: this
file shows that a stable recovery scheme at a closed face of the context lifts, through any legal
extension with the two faces, to a stable recovery scheme at the whole context.  Each item below is
compiled in this repository (theorem named), unless marked otherwise.

**Recovery lifts along a face** (`StageType.IsStableRecoveryScheme.of_comap`).  Let `T⁺` have face
`p` along a closed face `g`, and let `E_B` be a stable recovery scheme for `p`, an embedding `f`
into the points of `g`, a coface `D` and `γ`.  Every legal scheme `E` on one more point whose faces
along the first points and along `g` followed by the new point are the schemes of `T⁺` and of
`E_B` is a stable recovery scheme for `T⁺`, `f.trans g`, `D` and `γ`.  A stage type on `E` with
face `T⁺` has, along `g` followed by the new point, a stage type on `E_B` with face `p`, which
recovers `D`.

**Lifting with the coatom extension property** (`StageType.IsStableRecoveryScheme.exists_lift`).
Under the coatom extension property at `λ_{ξ+1}` (`StageType.HasCoatomExtensions`, implied by
hypothesis 8), a stable recovery scheme at a closed face of a legal `T⁺` gives one at `T⁺`: the
exact pinned extension (`StageType.exists_pinned_extension`) of `T⁺` by a legal stage type on
`E_B` with face `p` (`StageType.IsStableRecoveryScheme.exists_stageType`) has the two faces.  So,
under that property, a stable recovery scheme is needed only at the smallest closed face of the
context containing the root and some calibrated cap with its reference cells (argued, not
formalized as a statement over all inputs).

**What this does not give** (argued, not formalized).  The lifted scheme is a stable recovery
scheme, not a cap-reading extension: the coatom extension property does not prescribe its cells at
`(univ, N)`.  So `StageType.HasReadingCoatomCompletions` is not obtained this way, and no universal
construction of reading coatom completions is compiled here; at the smallest closed face the
reading is again at its top graded face, where the completion of the last coatom pair is open.

**The face version is not a different statement**
(`StageType.hasStableRecoverySchemes_iff_exists_face`).  For every calibration `C`, under the
coatom extension property at `λ_{ξ+1}`, stable recovery schemes for `C` are equivalent to: every
input of `C` has a closed face `g` of `T⁺` through which the root factors (`f = f'.trans g`) and a
stable recovery scheme for the face `p` of `T⁺` along `g`, `f'`, `D` and `γ`.  The face may be the
whole context (`g` the identity), so this reformulation by itself simplifies nothing; a gain needs
a strictly smaller face.

**The smallest face can fail**
(`Continuation.StableRecoveryCounterexample.not_isStableRecoveryScheme_twinRoot`).  At the twin
donors, the face along the root alone (the twin root, with the identity) has no stable recovery
scheme for the first donor at any `γ`: the second donor is a stage type on the same scheme with the
same face and the twins in the other order.  So a face carrying recovery must contain more than the
root.  At both compiled inputs of `VaughtConjecture.Continuation.StableRecoveryCoatomExamples` the
calibrated cap has grade equal to the number of points of the context, hence full scope
(`StageType.gradedIndex_eq_univ_of_grade_eq`), so no proper closed face contains it (argued from
those compiled facts; not stated as a theorem).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace StageType

variable {ξ : Ordinal.{u}} {n m k : ℕ}

/-- **Recovery lifts along a face.**  Let `T⁺` have face `p` along the closed face `g`, and let
`E_B` be a stable recovery scheme for `p`, `f`, `D` and `γ`.  A legal scheme `E` on `n + 1` points
whose faces along the first points and along `g` followed by the new point are the schemes of `T⁺`
and `E_B` is a stable recovery scheme for `T⁺`, `f.trans g`, `D` and `γ`. -/
theorem IsStableRecoveryScheme.of_comap {Tp : StageType.{u} (blockStage (ξ + 1)) n}
    {g : Fin m ↪ Fin n} {p : StageType.{u} (blockStage (ξ + 1)) m}
    (hp : restrictFace g Tp = some p) {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {EB : Scheme.{u} (m + 1)}
    (hB : p.IsStableRecoveryScheme f D γ EB) {E : Scheme.{u} (n + 1)} (hE : E.IsLegal)
    (hc : univ.map Fin.castSuccEmb ∈ E.toCellScheme.faces)
    (hT : E.comap Fin.castSuccEmb = Tp.toScheme)
    (hg : univ.map (extendByLast g) ∈ E.toCellScheme.faces) (hEB : E.comap (extendByLast g) = EB) :
    Tp.IsStableRecoveryScheme (f.trans g) D γ E := by
  refine ⟨exists_mem_cofaces_reduce_of_isLegal hE hc hT, fun Q' hQ'E hQ'T ↦ ?_⟩
  subst hQ'E
  -- the face of `Q'` along `g` followed by the new point is a stage type on `E_B` with face `p`
  have hQB : restrictFace (extendByLast g) Q' = some (Q'.comap (extendByLast g) hg) :=
    restrictFace_of_mem Q' _ hg
  have hQBp : restrictFace Fin.castSuccEmb (Q'.comap (extendByLast g) hg) = some p := by
    rw [restrictFace_trans Q' _ _ hQB, castSuccEmb_trans_extendByLast,
      ← restrictFace_trans Q' _ _ hQ'T, hp]
  obtain ⟨Q, hQ, hQD, hlab⟩ := hB.2 (Q'.comap (extendByLast g) hg) hEB hQBp
  refine ⟨Q, ?_, hQD, hlab⟩
  rw [← extendByLast_trans, ← restrictFace_trans Q' _ _ hQB, hQ]

/-- **Lifting a stable recovery scheme with the coatom extension property.**  Under the coatom
extension property at `λ_{ξ+1}`, a stable recovery scheme for the face `p` of a legal `T⁺` along a
closed face `g` gives a stable recovery scheme for `T⁺` along `f.trans g`: the exact pinned
extension of `T⁺` by a legal stage type on the scheme of the face, with face `p`, is one
(`StageType.IsStableRecoveryScheme.of_comap`). -/
theorem IsStableRecoveryScheme.exists_lift
    (hext : HasCoatomExtensions.{u} (blockStage (ξ + 1)))
    {Tp : StageType.{u} (blockStage (ξ + 1)) n} (hTl : Tp.IsLegal) {g : Fin m ↪ Fin n}
    {p : StageType.{u} (blockStage (ξ + 1)) m} (hp : restrictFace g Tp = some p)
    {f : Fin k ↪ Fin m} {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    {EB : Scheme.{u} (m + 1)} (hB : p.IsStableRecoveryScheme f D γ EB) :
    ∃ E : Scheme.{u} (n + 1), Tp.IsStableRecoveryScheme (f.trans g) D γ E := by
  obtain ⟨d, hdE, hdp⟩ := hB.exists_stageType
  -- the scheme of the face is legal: it is the scheme of a legal coface
  have hEBl : EB.IsLegal := by
    obtain ⟨q, ⟨hql, -⟩, hqE⟩ := hB.1
    exact hqE ▸ hql
  have hdl : d.IsLegal := by
    rw [IsLegal, hdE]
    exact hEBl
  obtain ⟨Q, hQ, hQT, hQd⟩ := exists_pinned_extension hext hTl hp hdl hdp
  obtain ⟨hc, hcT⟩ := (restrictFace_eq_some_iff Q _).mp hQT
  obtain ⟨hg, hgd⟩ := (restrictFace_eq_some_iff Q _).mp hQd
  exact ⟨Q.toScheme, hB.of_comap hp hQ hc (congrArg StageType.toScheme hcT) hg
    ((congrArg StageType.toScheme hgd).trans hdE)⟩

/-! ### The face version of stable recovery -/

/-- **Stable recovery at a closed face is the same statement.**  For a calibration `C`, under the
coatom extension property at `λ_{ξ+1}`, stable recovery schemes for `C` hold exactly when every
input of `C` has a closed face `g` of `T⁺` through which the root factors and a stable recovery
scheme for the face along `g`.  One direction takes `g` the identity; the other is
`StageType.IsStableRecoveryScheme.exists_lift`. -/
theorem hasStableRecoverySchemes_iff_exists_face
    (hext : HasCoatomExtensions.{u} (blockStage (ξ + 1)))
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) :
    HasStableRecoverySchemes ξ C ↔
      ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
        (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
        restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u},
          γ < blockStage (ξ + 1) → C Tp f D γ →
            ∃ (m' : ℕ) (g : Fin m' ↪ Fin m) (f' : Fin k ↪ Fin m')
              (p : StageType.{u} (blockStage (ξ + 1)) m') (EB : Scheme.{u} (m' + 1)),
              restrictFace g Tp = some p ∧ f'.trans g = f ∧ p.IsStableRecoveryScheme f' D γ EB := by
  refine ⟨fun h m k Tp f P hT hk hP D hD γ hγ hC ↦ ?_, fun h m k Tp f P hT hk hP D hD γ hγ hC ↦ ?_⟩
  · obtain ⟨E, hE⟩ := h Tp f P hT hk hP D hD γ hγ hC
    exact ⟨m, Function.Embedding.refl _, f, Tp, E, restrictFace_refl _,
      Function.Embedding.ext fun _ ↦ rfl, hE⟩
  · obtain ⟨m', g, f', p, EB, hp, rfl, hB⟩ := h Tp f P hT hk hP D hD γ hγ hC
    exact hB.exists_lift hext hT hp

end StageType

namespace Continuation.StableRecoveryCounterexample

open CandidateCounterexamples

variable (ξ : Ordinal.{u})

/-- **No stable recovery at the twin root alone**: for every `γ` and every scheme `E`, `E` is not a
stable recovery scheme for the twin root, the identity of its point and the first twin donor.  A
stable recovery scheme there would make every stage type on the five-cell scheme with face the
root agree with the first donor at its twins (`StageType.IsStableRecoveryScheme.label_eq_of_refl`);
the second donor has the twins in the other order. -/
theorem not_isStableRecoveryScheme_twinRoot (γ : Ordinal.{u}) (E : Scheme.{u} 2) :
    ¬ (twinRoot ξ).IsStableRecoveryScheme (Function.Embedding.refl (Fin 1)) (twinDonor₁ ξ) γ E :=
  fun hE ↦ by
  have h2 := hE.label_eq_of_refl (twinDonor₂ ξ) rfl (restrictFace_twinDonor₂ ξ)
    (2 : Fin 5) (2 : Fin 5) rfl (by
      -- the label of the first donor at the twin `2`
      change fiveCellLift₁ (blockStage ξ) 2 ≠ ⊤
      exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne)
  exact not_labelAdd_two_le_one h2.symm.le

end Continuation.StableRecoveryCounterexample

end VaughtConjecture

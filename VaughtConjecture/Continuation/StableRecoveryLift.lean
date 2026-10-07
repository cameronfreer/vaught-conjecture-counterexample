/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom

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
scheme, not a cap-reading extension: its cells at `(univ, N)` are those of the coatom extensions,
not controlled.  So `StageType.HasReadingCoatomCompletions` is not obtained this way, and no
universal construction of reading coatom completions is compiled here; at the smallest closed face
the reading is again at its top graded face, where the completion of the last coatom pair is open.

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

end StageType

end VaughtConjecture

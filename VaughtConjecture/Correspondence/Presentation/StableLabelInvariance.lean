/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Presentation.Lifting

/-!
# Stable labels are invariant under coherent renaming

Native construction throughout.  Write `λ_η = blockStage η`.

**Theorem** (`Realization.stableLabel_eq_of_coherentRenaming`, hence
`stableLabelInvarianceTarget`).  For exactly consistent realizations `S`, `S'` at a stage `β` and
a coherent renaming `c` of `S` into `S'`, at every tuple `u` typed by `p` in `S` and by `q` in
`S'`, the stable label in `S` of a cell `d` of `p` is the stable label in `S'` of the cell
`c.cellEquiv u hp hq d` of `q`, at every stage `α`.  The premises are those of the target: exact
consistency of both realizations and the coherent renaming.

**Proof.**

1. **Forcing under a commuting square** (`StageType.forcesThreshold_iff_of_renaming`): if `D` is
   the renaming of `D'` along `σ`, `p` the renaming of `p'` along `σ₀`, the faces along `f` are
   `p` and `p'`, and `faceCellMap hp' ∘ σ₀ = σ ∘ faceCellMap hp`, then `(D, f)` forces `n` at `d`
   exactly when `(D', f)` forces `n` at `σ₀ d`.  A higher-stage lift `Q'` of `D'` is renamed
   along the same bijection `σ` to a lift of `D` (stage reduction commutes with renaming); its face
   along `f` carries at the position of `d` the label that the face of `Q'` carries at `σ₀ d`.
   The reverse direction uses the inverse renamings.  Hence equal provisional offsets
   (`StageType.provisionalOffset_eq_of_renaming`).
2. **Rooted covers** (`Realization.stableOffset_le_of_coherentRenaming`): a rooted cover
   `(m, D, f)` of `u` in `S`, with its witness `s`, is sent to the rooted cover `(m, D', f)` of `u`
   in `S'` with the **same** witness `s` and the **same** root map `f`, where `D'` is the type of
   `s` in `S'`.  The renaming of `c` at `s` and the renaming of `c` at `u` form a commuting square
   along `f` (`Realization.CoherentRenaming.faceCellMap_comm`, the face equations from exact
   consistency).  No root automorphism is chosen: both renamings are those of `c`.
3. The reverse inequality is the same statement for the inverse coherent renaming
   (`Realization.CoherentRenaming.symm`), whose bijection at `u` is the inverse.
-/

universe u v

namespace VaughtConjecture

open Finset

namespace StageType

variable {α β : Ordinal.{u}} {k m : ℕ} {hβ : Order.IsSuccPrelimit β}

/-- The labels of a face are the labels of the cells named by the face cell map.
Native construction. -/
theorem label_faceCellMap {t : StageType.{u} α m} {s : StageType.{u} α k} {f : Fin k ↪ Fin m}
    (h : restrictFace f t = some s) (i : Fin s.card) : s.label i = t.label (faceCellMap h i) := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp h
  rfl

/-- One direction of `forcesThreshold_iff_of_renaming`: a lift `Q'` of `D'` is renamed along the
same bijection to a lift of `D`. -/
private theorem forcesThreshold_of_renaming {D D' : StageType.{u} β m}
    {p p' : StageType.{u} β k} {f : Fin k ↪ Fin m} (r : D'.Renaming D) (r₀ : p'.Renaming p)
    (hp : restrictFace f D = some p) (hp' : restrictFace f D' = some p')
    (hcomm : ∀ i, faceCellMap hp' (r₀.toEquiv i) = r.toEquiv (faceCellMap hp i))
    {d : Fin p.card} {n : ℕ} (h : ForcesThreshold α hβ D f p d n) :
    ForcesThreshold α hβ D' f p' (r₀.toEquiv d) n := by
  refine ⟨hp', fun Q' P' hQ' hP' i hi ↦ ?_⟩
  subst hQ'
  -- the lift of `D`: the renaming of `Q'` along the same bijection
  have hQ : (Q'.renameCells r.toEquiv).reduce hβ = D := r.renameCells_eq
  obtain ⟨P, hP, -⟩ := restrictFace_renameCells Q' r.toEquiv f hP'
  have hPp : P.reduce hβ = p := by
    have := restrictFace_reduce (Q'.renameCells r.toEquiv) f hβ
    rw [hQ, hp, hP, Option.map_some] at this
    exact (Option.some.inj this).symm
  have hcard : P.card = p.card := congrArg (fun x : StageType.{u} β k ↦ x.card) hPp
  have key := h.2 _ P hQ hP (Fin.cast hcard.symm d) rfl
  have e₁ : faceCellMap hP' i = faceCellMap hp' (r₀.toEquiv d) :=
    Fin.ext (val_faceCellMap_congr hP' hp' rfl hi)
  have e₂ : faceCellMap hP (Fin.cast hcard.symm d) = faceCellMap hp d :=
    Fin.ext (val_faceCellMap_congr hP hp
      (congrArg (fun x : StageType.{u} β m ↦ x.toScheme) hQ) rfl)
  rw [label_faceCellMap hP', e₁, hcomm, ← e₂]
  exact key.trans_eq (label_faceCellMap hP _)

/-- **Forcing a threshold under a commuting square of renamings** (native construction): let `D`
be the renaming of `D'` along `σ = r.toEquiv` and `p` the renaming of `p'` along
`σ₀ = r₀.toEquiv`, with faces `p` of `D` and `p'` of `D'` along `f`, and
`faceCellMap hp' ∘ σ₀ = σ ∘ faceCellMap hp`.  Then `(D, f)` forces `n` at `d` exactly when
`(D', f)` forces `n` at `σ₀ d`.  Each higher-stage lift is renamed along the same bijection
(stage reduction commutes with renaming); the reverse direction uses the inverse renamings. -/
theorem forcesThreshold_iff_of_renaming {D D' : StageType.{u} β m}
    {p p' : StageType.{u} β k} {f : Fin k ↪ Fin m} (r : D'.Renaming D) (r₀ : p'.Renaming p)
    (hp : restrictFace f D = some p) (hp' : restrictFace f D' = some p')
    (hcomm : ∀ i, faceCellMap hp' (r₀.toEquiv i) = r.toEquiv (faceCellMap hp i))
    (d : Fin p.card) (n : ℕ) :
    ForcesThreshold α hβ D f p d n ↔ ForcesThreshold α hβ D' f p' (r₀.toEquiv d) n := by
  refine ⟨forcesThreshold_of_renaming r r₀ hp hp' hcomm, fun h ↦ ?_⟩
  have hcomm' (i : Fin p'.card) :
      faceCellMap hp (r₀.symm.toEquiv i) = r.symm.toEquiv (faceCellMap hp' i) := by
    rw [Renaming.symm_toEquiv, Renaming.symm_toEquiv, Equiv.eq_symm_apply, ← hcomm,
      Equiv.apply_symm_apply]
  have := forcesThreshold_of_renaming r.symm r₀.symm hp' hp hcomm' h
  rwa [Renaming.symm_toEquiv, Equiv.symm_apply_apply] at this

/-- **Provisional offsets under a commuting square of renamings** (native construction):
`forcesThreshold_iff_of_renaming` at every threshold. -/
theorem provisionalOffset_eq_of_renaming {D D' : StageType.{u} β m}
    {p p' : StageType.{u} β k} {f : Fin k ↪ Fin m} (r : D'.Renaming D) (r₀ : p'.Renaming p)
    (hp : restrictFace f D = some p) (hp' : restrictFace f D' = some p')
    (hcomm : ∀ i, faceCellMap hp' (r₀.toEquiv i) = r.toEquiv (faceCellMap hp i))
    (d : Fin p.card) :
    provisionalOffset α hβ D f p d = provisionalOffset α hβ D' f p' (r₀.toEquiv d) :=
  iSup_congr fun n ↦ iSup_congr_Prop (forcesThreshold_iff_of_renaming r r₀ hp hp' hcomm d n)
    fun _ ↦ rfl

end StageType

namespace Realization

open StageType

variable {α β : Ordinal.{u}} {M : Type v} {S S' : Realization.{u, v} β M} {k : ℕ}
  {hβ : Order.IsSuccPrelimit β}

/-- **Rooted covers under a coherent renaming** (native construction): each rooted cover
`(m, D, f)` of `u` in `S`, with witness `s`, gives the rooted cover `(m, D', f)` of `u` in `S'`
with the same witness `s` and the same root map `f`, where `D'` is the type of `s` in `S'`; the
renamings of `c` at `s` and at `u` commute along `f` (`CoherentRenaming.faceCellMap_comm`), so
the provisional offsets agree (`StageType.provisionalOffset_eq_of_renaming`).  Hence the stable
offset in `S` at `d` is at most the stable offset in `S'` at the renamed cell. -/
theorem stableOffset_le_of_coherentRenaming (hS : S.IsConsistent) (hS' : S'.IsConsistent)
    (c : CoherentRenaming S S') (u : Fin k ↪ M) {p q : StageType.{u} β k}
    (hp : S.eval u = some p) (hq : S'.eval u = some q) (d : Fin p.card) :
    S.stableOffset α hβ u p d ≤ S'.stableOffset α hβ u q (c.cellEquiv u hp hq d) := by
  refine iSup₂_le fun x hx ↦ ?_
  obtain ⟨m, D, f⟩ := x
  obtain ⟨s, hs, hsinj, hD⟩ := hx
  let sE : Fin m ↪ M := ⟨s, hsinj⟩
  have hD₀ : S.eval sE = some D := hD
  obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.mp ((c.isSome_eval_iff sE).mp (by simp [hD₀]))
  refine le_iSup₂_of_le (f := fun (x : Σ m : ℕ, StageType.{u} β m × (Fin k ↪ Fin m))
      (_ : S'.ExtendsToCover u x) ↦
      provisionalOffset α hβ x.2.1 x.2.2 q (c.cellEquiv u hp hq d))
    ⟨m, D', f⟩ ⟨s, hs, hsinj, hD'⟩ (le_of_eq ?_)
  have heq : f.trans sE = u := Function.Embedding.ext fun j ↦ congrFun hs j
  subst heq
  have hfp : restrictFace f D = some p := (hS sE D f hD₀).symm.trans hp
  have hfq : restrictFace f D' = some q := (hS' sE D' f hD').symm.trans hq
  exact provisionalOffset_eq_of_renaming (c.renamingAt sE hD₀ hD') (c.renamingAt _ hp hq) hfp hfq
    (fun i ↦ c.faceCellMap_comm sE f hD₀ hD' hp hq hfp hfq i) d

/-- **Stable labels are invariant under coherent renaming** (native construction): for exactly
consistent `S`, `S'` and a coherent renaming `c`, the stable label in `S` of a cell `d` of the
type `p` of `u` is the stable label in `S'` of the cell `c.cellEquiv u hp hq d` of its type `q`.
The reverse inequality of stable offsets is `stableOffset_le_of_coherentRenaming` for the inverse
coherent renaming (`CoherentRenaming.symm`). -/
theorem stableLabel_eq_of_coherentRenaming (hS : S.IsConsistent) (hS' : S'.IsConsistent)
    (c : CoherentRenaming S S') (u : Fin k ↪ M) {p q : StageType.{u} β k}
    (hp : S.eval u = some p) (hq : S'.eval u = some q) (d : Fin p.card) :
    S.stableLabel α hβ u p d = S'.stableLabel α hβ u q (c.cellEquiv u hp hq d) := by
  have hle := stableOffset_le_of_coherentRenaming (α := α) (hβ := hβ) hS hS' c u hp hq d
  have hge := stableOffset_le_of_coherentRenaming (α := α) (hβ := hβ) hS' hS c.symm u hq hp
    (c.cellEquiv u hp hq d)
  have hd : c.symm.cellEquiv u hq hp (c.cellEquiv u hp hq d) = d :=
    (c.cellEquiv u hp hq).symm_apply_apply d
  rw [hd] at hge
  rw [stableLabel, stableLabel, le_antisymm hle hge]

end Realization

/-- **The stable-label invariance target holds** (native construction):
`StableLabelInvarianceTarget η M` for every `η` and `M`, with its premises (exact consistency of
both realizations and a coherent renaming) and no other
(`Realization.stableLabel_eq_of_coherentRenaming`). -/
theorem stableLabelInvarianceTarget (η : Ordinal.{u}) (M : Type v) :
    StableLabelInvarianceTarget η M :=
  fun _ _ hS hS' c _ u _ _ hp hq d ↦
    Realization.stableLabel_eq_of_coherentRenaming hS hS' c u hp hq d

end VaughtConjecture

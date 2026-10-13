/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.Template

/-!
# Faces of renamed stage types

The face of a stage type along `g` numbers the cells visible through `g` in increasing order
(`Scheme.cellMap`).  Renaming the cells of the type (`StageType.renameCells`) changes that order,
so the faces of a renaming are renamings of the faces, and not equal to them in general.  This
file proves the two directions [AFK26, Definitions 4.6 and 4.8] need:

* **the face of a renaming is a renaming of the face** (`StageType.restrictFace_renameCells`), with
  the same definedness (`StageType.restrictFace_renameCells_eq_none_iff`): restriction is defined
  on renaming classes;
* **every renaming of a face is the face of a renaming**
  (`StageType.exists_restrictFace_renameCells`): the cells visible through `g` are permuted among
  themselves and the other cells are fixed.

The second is what the amalgamation of charts needs: two embeddings of one chart fix the common
part only up to renaming, and the native amalgamation (`StageType.exists_amalgam` and its strongly
coded form) needs the two faces to be equal.

Also: renamings with the same values at equal positions are equal (`StageType.renameCells_congr`),
and a stage type at stage `ω₁` whose labels lie at a smaller stage `λ` that is zero or a limit is
the reduction to `λ` read back at `ω₁` (`StageType.castLE_reduce_of_atStage`); face maps commute
with reading at a larger stage (`StageType.restrictFace_castLE`).
-/

universe u

namespace VaughtConjecture

open Finset Label Ordinal

namespace StageType

variable {α : Ordinal.{u}} {n m k c : ℕ}

/-! ### Renamings with equal values -/

/-- **Renamings agreeing at equal positions are equal.** -/
theorem renameCells_congr (t : StageType.{u} α n) {c₁ c₂ : ℕ} (τ : Fin c₁ ≃ Fin t.card)
    (σ : Fin c₂ ≃ Fin t.card) (h : ∀ (i : Fin c₁) (j : Fin c₂), (i : ℕ) = j → τ i = σ j) :
    t.renameCells τ = t.renameCells σ := by
  have hc : c₁ = c₂ := by simpa using (Fintype.card_congr (τ.trans σ.symm))
  subst hc
  obtain rfl : τ = σ := Equiv.ext fun i ↦ h i i rfl
  rfl

/-! ### Reading a stage at a larger stage -/

/-- Reading at a larger stage commutes with restriction to a closed face. -/
theorem restrictFace_castLE (t : StageType.{u} α n) {β : Ordinal.{u}} (h : α ≤ β)
    (f : Fin m ↪ Fin n) : restrictFace f (t.castLE h) = (restrictFace f t).map (castLE · h) := by
  by_cases hf : univ.map f ∈ t.toCellScheme.faces
  · rw [restrictFace_of_mem (t.castLE h) f hf, restrictFace_of_mem t f hf, Option.map_some]
    rfl
  · rw [restrictFace_of_notMem (t.castLE h) f hf, restrictFace_of_notMem t f hf,
      Option.map_none]

/-- **A stage type whose labels lie at a smaller stage `λ`** (zero or a limit) is its reduction to
`λ`, read back at its own stage. -/
theorem castLE_reduce_of_atStage (t : StageType.{u} α n) {β : Ordinal.{u}}
    (hβ : Order.IsSuccPrelimit β) (hβα : β ≤ α) (ht : ∀ d, AtStage β (t.label d)) :
    (t.reduce hβ).castLE hβα = t :=
  ext rfl fun i j hij ↦ by
    rw [Fin.ext hij]
    exact (ht j).reduce_eq

/-! ### The face of a renaming -/

section Faces

variable (t : StageType.{u} α n) (π : Fin k ≃ Fin t.card) (g : Fin m ↪ Fin n)

/-- The faces of a renaming are defined exactly where those of the type are. -/
theorem restrictFace_renameCells_eq_none_iff :
    restrictFace g (t.renameCells π) = none ↔ restrictFace g t = none := by
  rw [restrictFace_eq_none_iff, restrictFace_eq_none_iff]
  rfl

/-- A cell of a renaming is visible through `g` exactly when its image is. -/
private theorem mem_visibleCells_renameCells (d : Fin (t.renameCells π).card) :
    d ∈ (t.renameCells π).visibleCells g ↔ π d ∈ t.visibleCells g := by
  rw [Scheme.mem_visibleCells, Scheme.mem_visibleCells]
  rfl

/-- **The face of a renaming, read through a bijection of the visible cells**: if `τ` sends each
visible cell of the renaming, by position, to the visible cell of `t` that it names, the face of
the renaming is the face of `t` renamed along `τ`. -/
theorem comap_renameCells_eq (hf : univ.map g ∈ t.toCellScheme.faces)
    (τ : Fin ((t.renameCells π).toScheme.comap g).card ≃ Fin (t.toScheme.comap g).card)
    (hτ : ∀ j, t.cellMap g (τ j) = π ((t.renameCells π).cellMap g j)) :
    (t.comap g hf).renameCells τ = (t.renameCells π).comap g hf := by
  refine ext (Scheme.ext rfl rfl rfl (fun i j hij ↦ ?_) (fun i j hij ↦ ?_)
    (fun s s' e e' hs he ↦ ?_)) fun i j hij ↦ ?_
  · obtain rfl := Fin.ext hij
    exact congrArg (fun d ↦ (t.toCellScheme.scope d).preimage g g.injective.injOn) (hτ i)
  · obtain rfl := Fin.ext hij
    exact congrArg t.toCellScheme.grade (hτ i)
  · obtain rfl := Fin.ext hs
    have he' : (e.1 : Fin ((t.renameCells π).toScheme.comap g).card) = e'.1 := Fin.ext he
    change t.rows.row (t.cellMap g (τ s)) ⟨t.cellMap g (τ e.1), _⟩ =
      t.rows.row (π ((t.renameCells π).cellMap g s)) ⟨π ((t.renameCells π).cellMap g e'.1), _⟩
    exact t.rows.row_congr (hτ s) ((hτ e.1).trans (by rw [he']))
  · obtain rfl := Fin.ext hij
    exact congrArg t.label (hτ i)

/-- A renaming has as many cells visible through `g` as `t`. -/
private theorem card_visibleCells_renameCells :
    #((t.renameCells π).visibleCells g) = #(t.visibleCells g) := by
  refine Finset.card_bij' (fun d _ ↦ π d) (fun d _ ↦ π.symm d) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
    (fun d _ ↦ π.symm_apply_apply d) (fun d _ ↦ π.apply_symm_apply d)
  · exact (mem_visibleCells_renameCells t π g d).mp hd
  · have : π (π.symm d) ∈ t.visibleCells g := by rwa [π.apply_symm_apply]
    exact (mem_visibleCells_renameCells t π g (π.symm d)).mpr this

/-- The bijection of visible cells induced by a renaming: each visible cell of the renaming goes to
the position, among the visible cells of `t`, of the cell it names. -/
private theorem exists_faceEquiv :
    ∃ τ : Fin ((t.renameCells π).toScheme.comap g).card ≃ Fin (t.toScheme.comap g).card,
      ∀ j, t.cellMap g (τ j) = π ((t.renameCells π).cellMap g j) := by
  have hvis (j : Fin ((t.renameCells π).toScheme.comap g).card) :
      π ((t.renameCells π).cellMap g j) ∈ t.toCellScheme.visible (Set.range g) := by
    have := (mem_visibleCells_renameCells t π g _).mp ((t.renameCells π).cellMap_mem g j)
    exact Scheme.mem_visibleCells.mp this
  let F : Fin ((t.renameCells π).toScheme.comap g).card → Fin (t.toScheme.comap g).card :=
    fun j ↦ (t.cellEquiv g).symm ⟨_, hvis j⟩
  have hF (j) : t.cellMap g (F j) = π ((t.renameCells π).cellMap g j) := by
    rw [← Scheme.coe_cellEquiv, Equiv.apply_symm_apply]
  have hinj : Function.Injective F := fun i j hij ↦ by
    have := congrArg (t.cellMap g) hij
    rw [hF, hF] at this
    exact ((t.renameCells π).cellMap g).injective (π.injective this)
  have hcard : Fintype.card (Fin ((t.renameCells π).toScheme.comap g).card) =
      Fintype.card (Fin (t.toScheme.comap g).card) := by
    rw [Fintype.card_fin, Fintype.card_fin]
    exact card_visibleCells_renameCells t π g
  exact ⟨Equiv.ofBijective F ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩),
    hF⟩

/-- **The face of a renaming is a renaming of the face** [AFK26, Definitions 4.6 and 4.8]. -/
theorem restrictFace_renameCells {s : StageType.{u} α m} (hs : restrictFace g t = some s) :
    ∃ s', restrictFace g (t.renameCells π) = some s' ∧ s.IsCellRenaming s' := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t g).mp hs
  obtain ⟨τ, hτ⟩ := exists_faceEquiv t π g
  exact ⟨_, restrictFace_of_mem (t.renameCells π) g hf, _, τ, comap_renameCells_eq t π g hf τ hτ⟩

end Faces

/-! ### Every renaming of a face is the face of a renaming -/

/-- A renaming that permutes the cells visible through `g` according to `σ` (by position) has the
face of `t` renamed along `σ` as its face along `g`. -/
private theorem restrictFace_renameCells_of_perm (t : StageType.{u} α n) (g : Fin m ↪ Fin n)
    (hf : univ.map g ∈ t.toCellScheme.faces) (σ : Fin c ≃ Fin (t.comap g hf).card)
    (hc : #(t.visibleCells g) = c) (π : Fin t.card ≃ Fin t.card)
    (hπV : ∀ x : Fin #(t.visibleCells g), π (t.cellMap g x) = t.cellMap g (σ (Fin.cast hc x)))
    (hπmem : ∀ d, π d ∈ t.visibleCells g ↔ d ∈ t.visibleCells g) :
    restrictFace g (t.renameCells π) = some ((t.comap g hf).renameCells σ) := by
  obtain ⟨τ, hτ⟩ := exists_faceEquiv t π g
  -- the visible cells of the renaming are those of `t`, enumerated by the same map
  have hr (d : Fin t.card) :
      d ∈ Set.range ((t.renameCells π).cellMap g) ↔ d ∈ t.visibleCells g :=
    (Set.ext_iff.mp ((t.renameCells π).toScheme.range_cellMap g) d).trans
      (Finset.mem_coe.trans ((mem_visibleCells_renameCells t π g d).trans (hπmem d)))
  have key : (t.comap g hf).renameCells τ = (t.comap g hf).renameCells σ := by
    refine renameCells_congr (t.comap g hf) τ σ fun i j hij ↦ (t.cellMap g).injective ?_
    have hcm : (t.renameCells π).cellMap g i = t.cellMap g (Fin.cast hc.symm j) :=
      t.cellMap_eq_of_strictMono g ((t.renameCells π).cellMap g).strictMono hr
        (by exact hij)
    exact (hτ i).trans ((congrArg π hcm).trans ((hπV _).trans
      (congrArg (fun x ↦ t.cellMap g (σ x)) (Fin.ext rfl))))
  rw [restrictFace_of_mem (t.renameCells π) g hf, ← comap_renameCells_eq t π g hf τ hτ, key]

/-- **Every renaming of a face is the face of a renaming** [AFK26, Definitions 4.6 and 4.8]: if
the face of `t` along `g` is `s` and `s'` is a renaming of `s`, some renaming of `t` has the face
`s'` along `g`.  The renaming permutes the cells visible through `g` and fixes the others. -/
theorem exists_restrictFace_renameCells (t : StageType.{u} α n) (g : Fin m ↪ Fin n)
    {s s' : StageType.{u} α m} (hs : restrictFace g t = some s) (hss' : s.IsCellRenaming s') :
    ∃ π : Fin t.card ≃ Fin t.card, restrictFace g (t.renameCells π) = some s' := by
  classical
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t g).mp hs
  obtain ⟨c, σ, rfl⟩ := hss'
  have hc : #(t.visibleCells g) = c := by
    have := Fintype.card_congr σ
    simp only [Fintype.card_fin] at this
    exact this.symm
  let E : Fin #(t.visibleCells g) ≃ {d // d ∈ t.visibleCells g} :=
    ((t.visibleCells g).orderIsoOfFin rfl).toEquiv
  have hE (x : Fin #(t.visibleCells g)) : (E x : Fin t.card) = t.cellMap g x := rfl
  let ep : Equiv.Perm {d // d ∈ t.visibleCells g} :=
    E.symm.trans ((finCongr hc).trans (σ.trans E))
  refine ⟨Equiv.Perm.subtypeCongr ep (Equiv.refl _),
    restrictFace_renameCells_of_perm t g hf σ hc _ (fun x ↦ ?_) fun d ↦ ?_⟩
  · have hx : t.cellMap g x ∈ t.visibleCells g := t.cellMap_mem g x
    rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    have : (⟨t.cellMap g x, hx⟩ : {d // d ∈ t.visibleCells g}) = E x := Subtype.ext rfl
    rw [this]
    simp only [ep, Equiv.trans_apply, Equiv.symm_apply_apply, finCongr_apply]
    exact hE _
  · by_cases hd : d ∈ t.visibleCells g
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hd]
      exact iff_of_true (ep ⟨d, hd⟩).2 hd
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hd]
      rfl

end StageType

end VaughtConjecture

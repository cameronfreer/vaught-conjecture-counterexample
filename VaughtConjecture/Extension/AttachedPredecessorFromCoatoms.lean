/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachedPredecessor
import VaughtConjecture.Extension.MuteTop
import VaughtConjecture.Extension.PinnedExtension

/-!
# The attached predecessor from the coatom extension property

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the attached predecessor) and the
pinned extension of `VaughtConjecture.Extension.PinnedExtension` (row 6 of the table of 3.4).

**A pinned extension with the other coatom muted**
(`StageType.exists_pinned_extension_muted`).  Under the coatom extension property
(`StageType.HasCoatomExtensions α`), for a legal `P` on `n` points, a closed face `f` of `P` on
`m` points with `m + 1 < n` and restriction `p`, and a legal one-point coface `d` of `p`, there is
a legal stage type `Q` on `n + 1` points with faces `P` along `Fin.castSuccEmb` and `d` along
`extendByLast f` whose cells of grade `n` off the private face and off the full face are muted.
The construction is that of `StageType.exists_pinned_extension`, one coatom extension per point
outside the face, except at the last coatom extension: the one-point coface amalgamated there,
of `n` points, is first muted at its full grade (`StageType.muteTop`), which changes none of its
proper faces (`StageType.restrictFace_muteTop`).  A plan on `n + 1` points has two faces of `n`
points (`Geometry.IsPlan.card_extremes_le_two`): the private face and the face of that last
coface, so every cell of grade `n` off the private and the full face is one of its muted cells.

**The attached predecessor from the coatom extension property**
(`StageType.AttachedPredecessor.nonempty_of_hasCoatomExtensions`): with
`StageType.AttachedPredecessor.ofIsLegal`, an attached predecessor exists for every such `P`,
`f` and `d`.  So the fields of `StageType.AttachedPredecessor` ask nothing beyond the coatom
extension property, hypothesis 8 of the roadmap in its form without the apex
(`StageType.HasApexCoatomExtensions.hasCoatomExtensions`).  What the gate of (R1) needs beyond the
predecessor is not here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Extension.PinnedExtension`.

## References

The coatom extension is [Kni26, Corollary 4.3.22]; the one-point extension is
[Kni26, Proposition 4.3.23].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n m : ℕ}

/-- The cells of full grade of `t` are **muted**: their rows are `⊥` at themselves. -/
def IsMutedTop (t : StageType.{u} α k) : Prop :=
  ∀ c, t.toCellScheme.grade c = k → t.rows.row c ⟨c, t.toCellScheme.mem_below_gradedIndex c⟩ = ⊥

/-- The muted type has its cells of full grade muted. -/
theorem isMutedTop_muteTop (t : StageType.{u} α k) : t.muteTop.IsMutedTop := fun _ hc ↦
  muteTop_row_self hc

/-- **Muted cells through a face.**  If the face of `Q` along `g` is a type whose cells of full
grade `k` are muted, every cell of `Q` of grade `k` visible through `g` is muted. -/
theorem row_self_eq_bot_of_restrictFace {Q : StageType.{u} α n} {g : Fin k ↪ Fin n}
    {T : StageType.{u} α k} (hQ : restrictFace g Q = some T) (hT : T.IsMutedTop)
    {c : Fin Q.card} (hc : (Q.toCellScheme.scope c : Set (Fin n)) ⊆ Set.range g)
    (hg : Q.toCellScheme.grade c = k) :
    Q.rows.row c ⟨c, Q.toCellScheme.mem_below_gradedIndex c⟩ = ⊥ := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp hQ
  obtain ⟨i, rfl⟩ : c ∈ Set.range (Q.cellMap g) := by
    rw [Scheme.range_cellMap]; exact mem_coe.mpr (Scheme.mem_visibleCells.mpr hc)
  exact hT i hg

/-- A face of `n` points of a plan on `n + 1` points other than two given faces of `n` points is
impossible: a plan has at most two extreme points. -/
theorem eq_of_card_eq_of_isPlan {F : Finset (Finset (Fin (n + 1)))} (hF : Geometry.IsPlan univ F)
    {B₁ B₂ B : Finset (Fin (n + 1))} (h₁ : B₁ ∈ F) (h₂ : B₂ ∈ F) (hB : B ∈ F)
    (hc₁ : #B₁ = n) (hc₂ : #B₂ = n) (hc : #B = n) (h₁₂ : B₁ ≠ B₂) (hB₁ : B ≠ B₁) : B = B₂ := by
  -- Each face of `n` points misses one point, an extreme point of the ground set.
  have hmiss : ∀ C ∈ F, #C = n → ∃ y, C = univ.erase y ∧ y ∈ Geometry.extremes F univ := by
    intro C hC hcC
    have hne : C ≠ univ := fun h ↦ by rw [h] at hcC; simp at hcC
    obtain ⟨y, hy⟩ : ∃ y, y ∉ C := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_univ_of_forall hcon)
    have hCy : C = univ.erase y := eq_of_subset_of_card_le
      (fun x hx ↦ mem_erase.mpr ⟨fun h ↦ hy (h ▸ hx), mem_univ x⟩) (by simp [hcC])
    exact ⟨y, hCy, Geometry.mem_extremes.mpr ⟨mem_univ y, hCy ▸ hC⟩⟩
  obtain ⟨y₁, rfl, hy₁⟩ := hmiss B₁ h₁ hc₁
  obtain ⟨y₂, rfl, hy₂⟩ := hmiss B₂ h₂ hc₂
  obtain ⟨y, rfl, hy⟩ := hmiss B hB hc
  by_contra hne
  have hy1 : y ≠ y₁ := fun h ↦ hB₁ (h ▸ rfl)
  have hy2 : y ≠ y₂ := fun h ↦ hne (h ▸ rfl)
  have h12 : y₁ ≠ y₂ := fun h ↦ h₁₂ (h ▸ rfl)
  have hsub : ({y, y₁, y₂} : Finset (Fin (n + 1))) ⊆ Geometry.extremes F univ := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : #({y, y₁, y₂} : Finset (Fin (n + 1))) = 3 := by
    rw [card_insert_of_notMem (by simp [hy1, hy2]), card_pair h12]
  have := (card_le_card hsub).trans (hF.card_extremes_le_two hF.ground_mem)
  omega

/-- **A pinned extension with the other coatom muted.**  Under the coatom extension property, for
a legal `P` on `n` points, a closed face `f` of `P` on `m` points with `m + 1 < n` and restriction
`p`, and a legal one-point coface `d` of `p`, some legal `Q` on `n + 1` points has faces `P` along
`Fin.castSuccEmb` and `d` along `extendByLast f`, and its cells of grade `n` off the private face
and off the full face are muted.  At the last coatom extension the coface is first muted at its
full grade. -/
theorem exists_pinned_extension_muted (hext : HasCoatomExtensions.{u} α) {P : StageType.{u} α n}
    (hP : P.IsLegal) {f : Fin m ↪ Fin n} {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)}
    (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hmn : m + 1 < n) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d ∧
      ∀ c, Q.toCellScheme.grade c = n → Q.toCellScheme.scope c ≠ univ →
        Q.toCellScheme.scope c ≠ univ.map Fin.castSuccEmb →
          Q.rows.row c ⟨c, Q.toCellScheme.mem_below_gradedIndex c⟩ = ⊥ := by
  induction hk : n - m using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    subst hk
    have hplan := P.isWellFormed.isWellFormed.isPlan
    rw [P.isWellFormed.ground_eq] at hplan
    -- A point `x` outside the face whose addition keeps the face closed (accessibility).
    have hfP : univ.map f ∈ P.toCellScheme.faces := ((restrictFace_eq_some_iff P f).mp hPf).1
    have hne : univ.map f ≠ univ := fun he ↦ by
      have := congrArg Finset.card he
      simp at this
      omega
    obtain ⟨x, hx, hxP⟩ := hplan.exists_insert_mem hfP hne
    have hxr : x ∉ Set.range f := fun ⟨i, hi⟩ ↦ hx (by simp [← hi])
    set f₁ := Fin.Embedding.snoc f hxr
    have hff₁ : Fin.castSuccEmb.trans f₁ = f := Fin.Embedding.init_snoc f hxr
    have hf₁P : univ.map f₁ ∈ P.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    set p₁ := P.comap f₁ hf₁P
    have hPf₁ : restrictFace f₁ P = some p₁ := restrictFace_of_mem P f₁ hf₁P
    have hp₁ : p₁.IsLegal := hP.restrictFace f₁ hPf₁
    have hp₁p : restrictFace Fin.castSuccEmb p₁ = some p := by
      rw [restrictFace_trans P f₁ _ hPf₁, hff₁, hPf]
    -- One coatom extension: amalgamate `p₁` and `d` over `p`.
    obtain ⟨t, ht, htp₁, htd⟩ := hext m p₁ d p hp₁ hd hp₁p hdp
    by_cases hlast : m + 2 < n
    · obtain ⟨Q, hQ, hQP, hQt, hQm⟩ := ih (n - (m + 1)) (by omega) hPf₁ ht htp₁ hlast rfl
      refine ⟨Q, hQ, hQP, ?_, hQm⟩
      rw [← hff₁, ← extendByLast_trans, ← restrictFace_trans Q _ _ hQt, htd]
    -- The last coatom extension, of the muted coface.
    have hne₁ : univ.map f₁ ≠ univ := fun he ↦ by
      have := congrArg Finset.card he
      simp at this
      omega
    obtain ⟨y, hy, hyP⟩ := hplan.exists_insert_mem hf₁P hne₁
    have hyr : y ∉ Set.range f₁ := fun ⟨i, hi⟩ ↦ hy (by simp [← hi])
    set f₂ := Fin.Embedding.snoc f₁ hyr
    have hf₁f₂ : Fin.castSuccEmb.trans f₂ = f₁ := Fin.Embedding.init_snoc f₁ hyr
    have hf₂P : univ.map f₂ ∈ P.toCellScheme.faces := by rwa [Fin.Embedding.univ_map_snoc]
    have hsurj : Function.Surjective f₂ := by
      have hbij : Function.Bijective f₂ := (Fintype.bijective_iff_injective_and_card f₂).mpr
        ⟨f₂.injective, by simp; omega⟩
      exact hbij.2
    set p₂ := P.comap f₂ hf₂P
    have hPf₂ : restrictFace f₂ P = some p₂ := restrictFace_of_mem P f₂ hf₂P
    have hp₂ : p₂.IsLegal := hP.restrictFace f₂ hPf₂
    have hp₂p₁ : restrictFace Fin.castSuccEmb p₂ = some p₁ := by
      rw [restrictFace_trans P f₂ _ hPf₂, hf₁f₂, hPf₁]
    have hcs : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ≠ univ := fun he ↦ by
      have := congrArg Finset.card he
      simp at this
    have ht₀p₁ : restrictFace Fin.castSuccEmb t.muteTop = some p₁ := by
      rw [restrictFace_muteTop _ hcs, htp₁]
    obtain ⟨t', ht', ht'p₂, ht't₀⟩ := hext (m + 1) p₂ t.muteTop p₁ hp₂ ht.muteTop hp₂p₁ ht₀p₁
    obtain ⟨Q, hQ, hQP, hQt'⟩ := exists_pinned_extension_of_surjective hsurj hPf₂ ht' ht'p₂
    -- The face of `Q` along the last coface is the muted coface.
    have hQt₀ : restrictFace (extendByLast f₁) Q = some t.muteTop := by
      rw [← hf₁f₂, ← extendByLast_trans, ← restrictFace_trans Q _ _ hQt', ht't₀]
    have hed : univ.map (extendByLast (Fin.castSuccEmb : Fin m ↪ Fin (m + 1))) ≠ univ :=
      fun he ↦ by
        have := congrArg Finset.card he
        simp at this
    refine ⟨Q, hQ, hQP, ?_, fun c hcg hcu hcp ↦ ?_⟩
    · rw [← hff₁, ← extendByLast_trans, ← restrictFace_trans Q _ _ hQt₀,
        restrictFace_muteTop _ hed, htd]
    -- The cell `c` lies on the face of the last coface, the other face of `n` points.
    have hplanQ := Q.isWellFormed.isWellFormed.isPlan
    rw [Q.isWellFormed.ground_eq] at hplanQ
    have hB₂ : univ.map (extendByLast f₁) ∈ Q.toCellScheme.faces :=
      ((restrictFace_eq_some_iff Q _).mp hQt₀).1
    have hB₁ : univ.map Fin.castSuccEmb ∈ Q.toCellScheme.faces :=
      ((restrictFace_eq_some_iff Q _).mp hQP).1
    have hcard_c : #(Q.toCellScheme.scope c) = n := by
      have h1 := Q.isWellFormed.isWellFormed.grade_le_card c
      have h2 := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hcu⟩)
      simp only [card_univ, Fintype.card_fin] at h2
      omega
    have h12 : univ.map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) ≠ univ.map (extendByLast f₁) :=
      fun he ↦ by
        have hl : Fin.last n ∈ univ.map (extendByLast f₁) := by
          rw [univ_map_extendByLast]; exact mem_insert_self _ _
        rw [← he] at hl
        obtain ⟨z, -, hz⟩ := mem_map.mp hl
        exact (Fin.castSucc_lt_last z).ne hz
    have hsc := eq_of_card_eq_of_isPlan hplanQ hB₁ hB₂
      (Q.isWellFormed.isWellFormed.scope_mem c) (by simp) (by simp; omega) hcard_c h12 hcp
    have hvis : (Q.toCellScheme.scope c : Set (Fin (n + 1))) ⊆ Set.range (extendByLast f₁) := by
      intro z hz
      rw [hsc] at hz
      obtain ⟨w, -, rfl⟩ := mem_map.mp (mem_coe.mp hz)
      exact ⟨w, rfl⟩
    exact row_self_eq_bot_of_restrictFace hQt₀ (isMutedTop_muteTop t) hvis (by omega)

/-- **The attached predecessor from the coatom extension property.**  Under
`StageType.HasCoatomExtensions α`, for a legal `P` on `n` points, a closed face `f` of `P` on `m`
points with `m + 1 < n` and restriction `p`, and a legal one-point coface `d` of `p`, an attached
predecessor of `P` over `f` with donor `d` exists. -/
theorem AttachedPredecessor.nonempty_of_hasCoatomExtensions (hext : HasCoatomExtensions.{u} α)
    {P : StageType.{u} α n} (hP : P.IsLegal) {f : Fin m ↪ Fin n} {p : StageType.{u} α m}
    {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p) (hmn : m + 1 < n) :
    Nonempty (AttachedPredecessor P f d) := by
  obtain ⟨Q, hQ, hQP, hQd, hQm⟩ := exists_pinned_extension_muted hext hP hPf hd hdp hmn
  exact ⟨AttachedPredecessor.ofIsLegal hQ hQP hQd (by omega) hQm⟩

end StageType

end VaughtConjecture

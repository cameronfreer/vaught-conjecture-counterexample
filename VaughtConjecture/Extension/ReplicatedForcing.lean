/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedGradeOne

/-!
# Sections of the replicated scheme are determined by their cells of full scope

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

**Equal readings give equal capped values** (`Scheme.min_eq_min_of_rowAt_eq`): in a section lawful
below a pair, two cells read alike by a cell `u` below the pair carry the same label capped at the
label of `u` (the capped decoder at `u`).

**Every cell of the attachment is read as a shadow** (`Seed.exists_shadow_rowAt_eq`): a cell of
full scope of the ladder tower at a grade `k ≥ 1` reads every cell of the attachment of grade at
most `k` (of grade one when `k = 1`) as a ladder point of grade one, the shadow of that cell for its
member: a ladder point reads a cell of grade one as its shadow (`Seed.rowAt_ladCell_baseCellEmb`),
and a controller of state `R` reads a cell `e` as `R e`, which is the positive table of `R` at the
rank of `e`, the reading of the shadow of `e` for the member of `R`.

**Hence a section is determined by its cells of full scope** (`Seed.eq_of_eq_on_full`): two
sections lawful below `(univ, j)` that agree at the cells of full scope agree everywhere below
`(univ, j)`.  A cell of the attachment of grade `k` lies below a cell `u` of full scope at grade
`k` of maximal label (availability), and is read by `u` as a ladder point; so its label is that of
the ladder point capped at `u`.  A copy carries the label of its original
(`Scheme.eq_of_mirrorOrig_eq`).

**The lift from a mixed face is unique** (`Seed.eq_of_eq_below_mixed`): two sections lawful below
`(univ, j)` that agree below `(U, j)`, for a mixed face `U` with `j ≤ |U|`, agree everywhere: their
cells of full scope carry the labels of their copies at `U`.  So a capped lift from `(U, j)` into
`(univ, j)` exists exactly when the section forced by the prescription is lawful and keeps the
ambient at the cap.

## References

Lawful sections and bountifulness are [Kni26, Definitions 2.5.4 and 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **Equal readings give equal capped values**: in a section lawful below `Y`, two cells read
alike by a cell `u` below `Y` carry the same label capped at the label of `u`. -/
theorem min_eq_min_of_rowAt_eq {Y : Finset (Fin n) × ℕ} {w : Fin S.card → Label.{u}}
    (hw : S.rows.IsLawfulBelow Y fun d ↦ w d) {u t v : Fin S.card}
    (huY : u ∈ S.toCellScheme.below Y)
    (ht : t ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (hv : v ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u))
    (hrow : S.rowAt u t = S.rowAt u v) : min (w t) (w u) = min (w v) (w u) := by
  obtain ⟨θ, -, -, hθ⟩ := exists_cappedDecoder_below hw huY rfl
  rw [← hθ t ht, ← hθ v hv, hrow]

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

/-- **A cell of full scope reads every cell of the attachment of its grade as a shadow**: for a
cell `f` of the tower at `(univ, k)`, `1 ≤ k ≤ m + 1`, and a cell `e` of the attachment of grade
`k`, some ladder point is read by `f` as `f` reads `e`. -/
theorem exists_shadow_rowAt_eq (hcard : (I.attachmentBase g).S.card ≤ H)
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m + 1) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.gradedIndex f =
      ((univ : Finset (Fin (m + 2))), k))
    {e : Fin (I.attachment g).card} (he : (I.attachment g).toCellScheme.grade e = k) :
    ∃ v, (I.attachTower g H Γ A B').rowAt f ((I.attachmentBase g).baseCellEmb m e) =
      (I.attachTower g H Γ A B').rowAt f (ladCell H Γ A B' v) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- a ladder point
    have hk' : k = 1 := by omega
    subst hk'
    rcases tower_grade_one_cases f (congrArg Prod.snd hf) with ⟨p, rfl⟩ | ⟨e', -, rfl⟩
    · exact ⟨(p.1, Sum.inr e), rowAt_ladCell_baseCellEmb p he⟩
    · exfalso
      exact (I.attachmentBase g).scope_ne_univ e'
        ((congrArg Prod.fst (Scheme.LadderBaseData.gradedIndex_baseCellEmb (H := H) (Γ := Γ)
          (A := A) (B' := B') m e')).symm.trans (congrArg Prod.fst hf))
  · -- a controller
    have hf' : (I.attachTower g H Γ A B').toCellScheme.gradedIndex f =
        ((univ : Finset (Fin (m + 2))), k - 2 + 2) := by
      rw [show k - 2 + 2 = k by omega]; exact hf
    obtain ⟨R, -, hR, hrowA, hrowL⟩ :=
      Scheme.LadderBaseData.exists_controller_ladderTower (B := I.attachmentBase g) (A := A)
        (Γ := Γ) (B' := B') hcard (k - 2) m (by omega) f hf'
    refine ⟨(Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR, Sum.inr e), ?_⟩
    refine (hrowA e (show (I.attachment g).toCellScheme.grade e ≤ k - 2 + 2 by omega)).trans
      (Eq.trans ?_ (hrowL _).symm)
    have h := Scheme.baseIndex_self (Scheme.rankProf_le (I.attachmentBase g).S H)
      ((Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR, Sum.inr e) :
        Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    simp only [Scheme.ladderCeil] at h
    rw [h]
    exact (posTable_rankVector ((I.attachmentBase g).isSelfVisible_one_of_isLawful hR) e).symm

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

/-- The full face at a grade. -/
local notation "𝕐[" k "]" => ((univ : Finset (Fin (m + 2))), k)

/-- A cell of the replicated scheme of full scope is a cell of the tower. -/
theorem exists_eq_castAdd_of_scope (z : Fin (𝔼).card) (hz : (𝔼).toCellScheme.scope z = univ) :
    ∃ f, z = Fin.castAdd _ f ∧ (𝕋).toCellScheme.gradedIndex f = (𝔼).toCellScheme.gradedIndex z := by
  induction z using Fin.addCases with
  | right jj =>
    exfalso
    exact ((I.mem_mixedFaces g).mp (scope_replicated_natAdd jj)).2.1 hz
  | left x =>
    exact ⟨x, rfl, (Scheme.gradedIndex_mirror_castAdd
      (hmix := I.not_subset_scope_tower g H Γ A B') x).symm⟩

/-- **A section is determined by its cells of full scope**: two sections lawful below `(univ, j)`,
`j ≤ m + 1`, that agree at the cells of full scope agree at every cell below `(univ, j)`. -/
theorem eq_of_eq_on_full (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty) {j : ℕ} (hjm : j ≤ m + 1)
    {w w' : Fin (𝔼).card → Label.{u}} (hw : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ w d)
    (hw' : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ w' d)
    (hfull : ∀ f : Fin (𝕋).card, (𝕋).toCellScheme.scope f = univ → (𝕋).toCellScheme.grade f ≤ j →
      w (Fin.castAdd _ f) = w' (Fin.castAdd _ f))
    {d : Fin (𝔼).card} (hd : d ∈ (𝔼).toCellScheme.below 𝕐[j]) : w d = w' d := by
  classical
  have hgi (f : Fin (𝕋).card) : (𝔼).toCellScheme.gradedIndex (Fin.castAdd _ f) =
      (𝕋).toCellScheme.gradedIndex f :=
    Scheme.gradedIndex_mirror_castAdd (hmix := I.not_subset_scope_tower g H Γ A B') f
  induction d using Fin.addCases with
  | right jj =>
    set f := (((𝕋).copyEquiv (I.mixedFaces g)).symm jj).1.2 with hfdef
    have hfs : (𝕋).toCellScheme.scope f = univ := (((𝕋).copyEquiv (I.mixedFaces g)).symm jj).2.2.1
    have horig : (𝕋).mirrorOrig (I.mixedFaces g) (Fin.natAdd _ jj) =
        (𝕋).mirrorOrig (I.mixedFaces g) (Fin.castAdd _ f) := by
      rw [Scheme.mirrorOrig_natAdd, Scheme.mirrorOrig_castAdd]
    have hgf : (𝕋).toCellScheme.grade f ≤ j := by
      have h := hd.2
      change (𝕋).toCellScheme.grade ((𝕋).mirrorOrig (I.mixedFaces g) (Fin.natAdd _ jj)) ≤ j at h
      rwa [Scheme.mirrorOrig_natAdd] at h
    have hfY : (Fin.castAdd _ f : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below 𝕐[j] := by
      rw [CellScheme.mem_below, hgi]
      exact ⟨hfs ▸ subset_rfl, hgf⟩
    have hsc : (𝔼).toCellScheme.scope (Fin.natAdd _ jj) ⊆
        (𝔼).toCellScheme.scope (Fin.castAdd _ f) :=
      subset_trans (subset_univ _) (le_of_eq ((congrArg Prod.fst (hgi f)).trans hfs).symm)
    rw [Scheme.eq_of_mirrorOrig_eq hw horig hsc hfY, Scheme.eq_of_mirrorOrig_eq hw' horig hsc hfY]
    exact hfull f hfs hgf
  | left x =>
    have hxj : (𝕋).toCellScheme.grade x ≤ j :=
      (congrArg Prod.snd (hgi x)).symm.trans_le hd.2
    by_cases hx : (𝕋).toCellScheme.scope x = univ
    · exact hfull x hx hxj
    obtain ⟨e, rfl⟩ := (I.attachmentBase g).mem_range_baseCellEmb m x hx
    -- the grade of the cell
    set k := (I.attachment g).toCellScheme.grade e with hkdef
    have hge : (𝕋).toCellScheme.grade ((I.attachmentBase g).baseCellEmb m e) = k :=
      congrArg Prod.snd ((I.attachmentBase g).gradedIndex_baseCellEmb m e)
    have hk1 : 1 ≤ k := (I.isWellFormed_attachment g).isWellFormed.grade_pos e
    have hkj : k ≤ j := hge ▸ hxj
    -- a cell of full scope at the grade `k` of maximal label
    obtain ⟨f₀, hf₀⟩ := (I.attachmentBase g).exists_gradedIndex_univ_ladderTower (B' := B') hH hne
      m k hk1 (by omega)
    obtain ⟨u, hu, hmax⟩ := (univ.filter fun f : Fin (𝕋).card ↦
        (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k)).exists_max_image
      (fun f ↦ w (Fin.castAdd _ f)) ⟨f₀, by simp [hf₀]⟩
    rw [mem_filter] at hu
    have hu' := hu.2
    have huE : (𝔼).toCellScheme.gradedIndex (Fin.castAdd _ u) =
        ((univ : Finset (Fin (m + 2))), k) := (hgi u).trans hu'
    have huY : (Fin.castAdd _ u : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below 𝕐[j] := by
      rw [CellScheme.mem_below, huE]; exact ⟨subset_rfl, hkj⟩
    have hdE : (𝔼).toCellScheme.gradedIndex (Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m e)) =
        ((I.attachment g).toCellScheme.scope e, k) :=
      (hgi _).trans ((I.attachmentBase g).gradedIndex_baseCellEmb m e)
    -- the cell lies below a cell of full scope at most `u`, for both sections
    have hbelow (v : Fin (𝔼).card → Label.{u}) (hv : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ v d)
        (hvmax : ∀ f ∈ univ.filter fun f : Fin (𝕋).card ↦
          (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k),
          v (Fin.castAdd _ f) ≤ v (Fin.castAdd _ u)) :
        v (Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m e)) ≤ v (Fin.castAdd _ u) := by
      obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hv
      obtain ⟨u', hu'E, hle⟩ := havail _ _ huY
        (subset_trans (subset_univ _) (le_of_eq (congrArg Prod.fst huE).symm))
        ((congrArg Prod.snd hdE).trans (congrArg Prod.snd huE).symm)
      obtain ⟨f', rfl, hf'⟩ := exists_eq_castAdd_of_scope u'
        ((congrArg Prod.fst hu'E).trans (congrArg Prod.fst huE))
      exact hle.trans (hvmax f' (by rw [mem_filter]; exact ⟨mem_univ _, hf'.trans
        (hu'E.trans huE)⟩))
    have hmax' (f) (hf : f ∈ univ.filter fun f : Fin (𝕋).card ↦
        (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k)) :
        w' (Fin.castAdd _ f) ≤ w' (Fin.castAdd _ u) := by
      rw [mem_filter] at hf
      have hfs := congrArg Prod.fst hf.2
      have hfg := congrArg Prod.snd hf.2
      rw [← hfull f hfs (hfg.trans_le hkj), ← hfull u (congrArg Prod.fst hu')
        ((congrArg Prod.snd hu').trans_le hkj)]
      exact hmax f (by rw [mem_filter]; exact hf)
    have hle := hbelow w hw hmax
    have hle' := hbelow w' hw' hmax'
    -- the shadow read alike
    obtain ⟨v, hv⟩ := exists_shadow_rowAt_eq (Γ := Γ) (A := A) (B' := B') hcard hk1
      (by omega) u hu' rfl
    have hrow : (𝔼).rowAt (Fin.castAdd _ u) (Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m e)) =
        (𝔼).rowAt (Fin.castAdd _ u) (Fin.castAdd _ (ladCell H Γ A B' v)) := by
      rw [Scheme.rowAt_mirror_castAdd, Scheme.rowAt_mirror_castAdd]
      exact hv
    have ht : (Fin.castAdd _ ((I.attachmentBase g).baseCellEmb m e) : Fin (𝔼).card) ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ u)) := by
      rw [CellScheme.mem_below, hdE, huE]; exact ⟨subset_univ _, le_rfl⟩
    have hvb : (Fin.castAdd _ (ladCell H Γ A B' v) : Fin (𝔼).card) ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ u)) := by
      rw [CellScheme.mem_below, gradedIndex_castAdd_ladCell, huE]; exact ⟨subset_rfl, hk1⟩
    have e1 := Scheme.min_eq_min_of_rowAt_eq hw huY ht hvb hrow
    have e2 := Scheme.min_eq_min_of_rowAt_eq hw' huY ht hvb hrow
    rw [min_eq_left hle] at e1
    rw [min_eq_left hle'] at e2
    have hvs : (𝕋).toCellScheme.scope (ladCell H Γ A B' v) = univ :=
      congrArg Prod.fst (gradedIndex_ladCell v)
    have hvg : (𝕋).toCellScheme.grade (ladCell H Γ A B' v) ≤ j :=
      (congrArg Prod.snd (gradedIndex_ladCell (Γ := Γ) (A := A) (B' := B') v)).trans_le
        (hk1.trans hkj)
    rw [e1, e2, hfull _ hvs hvg, hfull u (congrArg Prod.fst hu')
      ((congrArg Prod.snd hu').trans_le hkj)]

/-- **The lift from a mixed face is unique**: two sections lawful below `(univ, j)`, `j ≤ m + 1`,
that agree below `(U, j)`, for a mixed face `U` with `j ≤ |U|`, agree at every cell below
`(univ, j)`: their cells of full scope carry the labels of their copies at `U`. -/
theorem eq_of_eq_below_mixed (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty) {j : ℕ} (hjm : j ≤ m + 1)
    (hU : U ∈ I.mixedFaces g) (hjU : j ≤ #U)
    {w w' : Fin (𝔼).card → Label.{u}} (hw : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ w d)
    (hw' : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ w' d)
    (hX : ∀ d ∈ (𝔼).toCellScheme.below (U, j), w d = w' d)
    {d : Fin (𝔼).card} (hd : d ∈ (𝔼).toCellScheme.below 𝕐[j]) : w d = w' d := by
  refine eq_of_eq_on_full hH hcard hne hjm hw hw' (fun f hfs hfg ↦ ?_) hd
  have hfU : (𝕋).toCellScheme.grade f ≤ #U := hfg.trans hjU
  have hfY : (Fin.castAdd _ f : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below 𝕐[j] := by
    rw [CellScheme.mem_below, Scheme.gradedIndex_mirror_castAdd]
    exact ⟨hfs ▸ subset_rfl, hfg⟩
  have hcX : copyAt H Γ A B' hU f hfs hfU ∈ (𝔼).toCellScheme.below (U, j) := by
    rw [CellScheme.mem_below, gradedIndex_copyAt]
    exact ⟨subset_rfl, hfg⟩
  rw [← eq_copyAt hU hw hfs hfU hfY, ← eq_copyAt hU hw' hfs hfU hfY]
  exact hX _ hcX

end Seed

end VaughtConjecture

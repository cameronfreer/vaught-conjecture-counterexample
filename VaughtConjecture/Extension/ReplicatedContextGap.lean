/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.RepairedTieLift
import VaughtConjecture.Extension.ReplicatedForcing

/-!
# A gap below the heights defeats the context lift

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme with agreement heights
in `Scheme.heightSet`).

At the top grade `2` of the replicated scheme over a seed with `m = 1`, a cell `u` at `(univ, 2)`
reads every cell of grade at most `2`: the cells of the attachment through the entry of its state,
and the other cells of its layer through agreement heights (`Scheme.rowAt_catalogueLayer_natAdd`).
A lift with a prescribed value above the cap at a context cell of grade `2` has, by availability, a
cell `u` at `(univ, 2)` at least that value, and its capped decoder (locality at `u`) reads the
whole lift below the value at `u` from the row of `u`.

**The gap** (`Seed.not_cappedLift_context_of_gap`).  Let the ambient be the writing of a state
`R₀` of the catalogue; let `b` be a cell of the attachment of grade at most `2` with `R₀ b` below
the cap, and `a`, `a'` two context cells with `R₀ a = R₀ a'`, with **no height at the grade `2` in
`(R₀ b, R₀ a]`**.  Let the prescription be `v ≠ v'` at `a`, `a'`, at least the cap, and at most
the value `v₃` at a context cell of grade `2`.  Then the context lift at the grade `2` fails:

* the cell `t₀` of `R₀` at `(univ, 2)` carries the top of the heights in the ambient, so the lift
  is at least the cap there, and the decoder at `u` reads its agreement height `h` with the state
  of `u` at least at the cap;
* the decoder at `u` reads `R₀ b` below the cap at `b`, so the state of `u` equals `R₀` at `b`,
  below `h`; so `h` is a height above `R₀ b`, hence above `R₀ a`;
* so the state of `u` equals `R₀` at `a` and at `a'`, and the decoder at `u` reads `v` and `v'`
  from one value.

The cap is then not a height (it lies in `(R₀ b, R₀ a]`), and `a`, `a'` have grade `1` (a value of
`Γ` self-visible at `2` is a height).  No coded representative of the cap and no decoder can help:
the obstruction is in the rows of the layer, not in a choice of the lift.

Whether a legal seed realizes the gap is not settled here.  The context of
`VaughtConjecture.MainTheorem.ReplicatedTieInstance` does not: its cell `e` is `⊥` in every lawful
section, and its cells of grade `2` read `y` and `z` alike, so a prescription at most their value
there is equal at `y` and `z`.  A realization needs two context cells read apart by the context's
own cells of grade `2` while the state `R₀` takes one value there; at a context cell of grade `2`
above both in `R₀` this forces that value to be self-visible at `2` (`Seed.not_context_pin`'s
mechanism, `Label.isSelfVisible_of_witness_eq`), hence a height, against the gap (an argument not
compiled here).

## References

Lawful sections are [Kni26, Definition 2.5.4]; agreement heights are those of the coatom extension
construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {k : ℕ} {F : Type*} [Fintype F] {read : Fin S.card → F}
  {G : Finset Label.{u}} {C : Finset (F → Label.{u})}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **A new cell reads a new cell of its layer at the agreement height of their entries.** -/
theorem rowAt_catalogueLayer_natAdd (i i' : Fin C.card) :
    (S.catalogueLayer k read G C hS).rowAt (Fin.natAdd S.card i) (Fin.natAdd S.card i') =
      agreementHeight G (layerEntry C i) (layerEntry C i') := by
  have hmem : Fin.natAdd S.card i' ∈ (S.catalogueLayer k read G C hS).toCellScheme.below
      ((S.catalogueLayer k read G C hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd,
      appendFullCellsScheme_gradedIndex_natAdd]
  rw [rowAt_of_mem hmem, appendFullCells_row_natAdd_eq]
  exact layerRow_natAdd _ i'

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {n : ℕ} {I : Seed.{u} α 1} {g : Fin n ↪ Fin 1} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- **A gap below the heights defeats the context lift at the grade `2`** (`m = 1`): the ambient
is the writing of a state `R₀` of the catalogue; `b` is a cell of the attachment of grade at most
`2` with `R₀ b` below the cap `c`; `a`, `a'` are context cells of grade at most `2` with
`R₀ a' = R₀ a` and no height at `2` in `(R₀ b, R₀ a]`; the prescription is `v ≠ v'` at `a`, `a'`,
`c ≤ v`, and both at most the value `v₃` at a context cell `a₃` of grade `2`.  The cap is at most
the top `gridPoint 2 B'` of the heights. -/
theorem not_cappedLift_context_of_gap (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : R₀ ∈ (I.attachmentBase g).towerCat Γ A (1 + 2)) {c : Label.{u}}
    (hc : IsSelfVisible 2 c) (hcB : c ≤ gridPoint 2 B')
    {p : (I.replicated g H Γ A B').toCellScheme.below (univ.erase (Fin.last 2), 2) → Label.{u}}
    (hp : (I.replicated g H Γ A B').rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) p)
    (hpq : ∀ e, min (I.replicatedWriting g H Γ A B' R₀ e.1) c = min (p e) c)
    {b a a' a₃ : Fin (I.attachment g).card} (hb : (I.attachment g).toCellScheme.grade b ≤ 2)
    (hbc : R₀ b < c) (hgap : ∀ h ∈ Scheme.heightSet Γ B' 2, R₀ b < h → R₀ a < h)
    (haa : R₀ a' = R₀ a) (ha : (I.attachment g).toCellScheme.grade a ≤ 2)
    (ha' : (I.attachment g).toCellScheme.grade a' ≤ 2)
    (ha₃ : (I.attachment g).toCellScheme.grade a₃ = 2)
    (hsa : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom 1)
    (hsa' : (I.attachment g).toCellScheme.scope a' ⊆ ctxCoatom 1)
    (hsa₃ : (I.attachment g).toCellScheme.scope a₃ ⊆ ctxCoatom 1) {v v' v₃ : Label.{u}}
    (hpa : ∀ e, e.1 = I.attachEmb g H Γ A B' a → p e = v)
    (hpa' : ∀ e, e.1 = I.attachEmb g H Γ A B' a' → p e = v')
    (hpa₃ : ∀ e, e.1 = I.attachEmb g H Γ A B' a₃ → p e = v₃) (hcv : c ≤ v) (hv : v ≤ v₃)
    (hv' : v' ≤ v₃) (hne : v ≠ v') :
    ¬ (I.replicated g H Γ A B').rows.CappedLift
      (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  intro hlift
  set T0 := Scheme.layerTower ((I.attachmentBase g).towerBase H)
    ((I.attachmentBase g).towerCat Γ A) (fun k ↦ Scheme.heightSet Γ B' k) 0 with hT0
  set Ent := T0.entries ((I.attachmentBase g).towerCat Γ A 2) with hEnt
  have hR₀l : (I.attachment g).rows.IsLawful R₀ := (Scheme.LadderBaseData.mem_towerCat.mp hR₀).2.1
  have hR₀2 : R₀ ∈ (I.attachmentBase g).towerCat Γ A 2 :=
    Scheme.LadderBaseData.towerCat_mono hA (by omega : 0 ≤ 1) hR₀
  -- the ambient and the lift
  set q := I.replicatedWriting g H Γ A B' R₀ with hq
  have hql : (𝔼).rows.IsLawful q := isLawful_replicatedWriting hH hcard hΓ hA hR₀
  obtain ⟨q', hq', hq'q, hq'p⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp hlift c hc
    p (fun d ↦ q d) hp (hql.isLawfulBelow _) fun e ↦ hpq e
  set w : Fin (𝔼).card → Label.{u} := fun d ↦
    if hd : d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2) then q' ⟨d, hd⟩ else ⊥ with hw
  have hwq' (d) (hd : d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2)) :
      w d = q' ⟨d, hd⟩ := dite_eq_left hd
  have hwl : (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) fun d ↦ w d := by
    have : (fun d : (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2) ↦ w d) = q' :=
      funext fun d ↦ hwq' d.1 d.2
    rw [this]; exact hq'
  have hmemY (d : Fin (I.attachment g).card) (hd : (I.attachment g).toCellScheme.grade d ≤ 2) :
      I.attachEmb g H Γ A B' d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2) :=
    (attachEmb_mem_below_iff d _).mpr ⟨subset_univ _, hd⟩
  have hmemX (d : Fin (I.attachment g).card) (hd : (I.attachment g).toCellScheme.grade d ≤ 2)
      (hs : (I.attachment g).toCellScheme.scope d ⊆ ctxCoatom 1) :
      I.attachEmb g H Γ A B' d ∈ (𝔼).toCellScheme.below (univ.erase (Fin.last 2), 2) :=
    (attachEmb_mem_below_iff d _).mpr ⟨hs, hd⟩
  have hwctx (d : Fin (I.attachment g).card) (hd : (I.attachment g).toCellScheme.grade d ≤ 2)
      (hs : (I.attachment g).toCellScheme.scope d ⊆ ctxCoatom 1) {x : Label.{u}}
      (hx : ∀ e, e.1 = I.attachEmb g H Γ A B' d → p e = x) : w (I.attachEmb g H Γ A B' d) = x := by
    rw [hwq' _ (hmemY d hd)]
    have h := hq'p ⟨_, hmemX d hd hs⟩
    rw [show (Set.inclusion _ ⟨_, hmemX d hd hs⟩ : (𝔼).toCellScheme.below
      ((univ : Finset (Fin 3)), 2)) = ⟨_, hmemY d hd⟩ from rfl] at h
    rw [h]; exact hx _ rfl
  -- the cell `t₀` of `R₀` in the layer at `2`
  obtain ⟨i₀, hi₀⟩ := Scheme.exists_layerEntry_eq (C := Ent) (mem_image_of_mem T0.v hR₀2)
  set t₀ : Fin (𝔼).card :=
    Fin.castAdd _ (Fin.natAdd T0.S.card i₀ : Fin (I.attachTower g H Γ A B').card) with ht₀
  have ht₀g : (𝔼).toCellScheme.gradedIndex t₀ = ((univ : Finset (Fin 3)), 2) :=
    (Scheme.gradedIndex_mirror_castAdd _).trans
      (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _)
  have ht₀Y : t₀ ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
    rw [CellScheme.mem_below, ht₀g]
  have hqt₀ : q t₀ = gridPoint 2 B' := by
    change ((I.attachmentBase g).ladderTower H Γ A B' 1).v R₀
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) t₀) = _
    rw [ht₀]
    erw [Scheme.mirrorOrig_castAdd]
    change (Scheme.layerRow T0.S (fun d ↦ d) (Scheme.heightSet Γ B' 2) Ent (T0.v R₀))
      (Fin.natAdd _ i₀) = _
    rw [Scheme.layerRow_natAdd, hi₀]
    exact Label.agreementHeight_self (Scheme.gridPoint_mem_heightSet Γ)
      (fun _ hx ↦ Scheme.le_gridPoint_of_mem_heightSet hΓ le_rfl hx) _
  have hwt₀ : c ≤ w t₀ := by
    have h := hq'q ⟨t₀, ht₀Y⟩
    rw [← hwq' t₀ ht₀Y] at h
    change min (w t₀) c = min (q t₀) c at h
    rw [hqt₀, min_eq_right hcB] at h
    exact h ▸ min_le_left _ _
  -- a cell at `(univ, 2)` at least `v₃`
  obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hwl
  obtain ⟨u, hu, hle⟩ := havail (I.attachEmb g H Γ A B' a₃) t₀ ht₀Y
    (by rw [show (𝔼).toCellScheme.scope t₀ = univ from congrArg Prod.fst ht₀g]; exact subset_univ _)
    (by rw [show (𝔼).toCellScheme.grade t₀ = 2 from congrArg Prod.snd ht₀g]
        exact (congrArg Prod.snd (gradedIndex_attachEmb a₃)).trans ha₃)
  rw [ht₀g] at hu
  rw [hwctx a₃ ha₃.le hsa₃ hpa₃] at hle
  have huY : u ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
    rw [CellScheme.mem_below, hu]
  obtain ⟨f, rfl, hf⟩ := exists_eq_castAdd_of_scope u (congrArg Prod.fst hu)
  rw [hu] at hf
  obtain ⟨i, rfl⟩ := Scheme.exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T0.S) (k := 2)
    (read := fun d ↦ d) (G := Scheme.heightSet Γ B' 2) (C := Ent) (hS := T0.not_le) hf
  -- the capped decoder at `u`
  obtain ⟨θ, hθ, -, hθr⟩ := Scheme.exists_cappedDecoder_below hwl huY (congrArg Prod.snd hu)
  have hbelow (d) (hd : d ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin 3)), 2)) :
      d ∈ (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex
        (Fin.castAdd _ (Fin.natAdd T0.S.card i : Fin (I.attachTower g H Γ A B').card))) := by
    rw [hu]; exact hd
  -- the rows of `u`
  have hrow_t₀ : (𝔼).rowAt (Fin.castAdd _ (Fin.natAdd T0.S.card i :
      Fin (I.attachTower g H Γ A B').card)) t₀ =
      agreementHeight (Scheme.heightSet Γ B' 2) (Scheme.layerEntry Ent i) (T0.v R₀) := by
    rw [ht₀]
    refine (Scheme.rowAt_mirror_castAdd _ _).trans ?_
    exact (Scheme.rowAt_catalogueLayer_natAdd (hS := T0.not_le) i i₀).trans (by rw [hi₀])
  have hrow_att (d : Fin (I.attachment g).card) (hd : (I.attachment g).toCellScheme.grade d ≤ 2) :
      (𝔼).rowAt (Fin.castAdd _ (Fin.natAdd T0.S.card i : Fin (I.attachTower g H Γ A B').card))
        (I.attachEmb g H Γ A B' d) = Scheme.layerEntry Ent i (Fin.castAdd _ d) := by
    change (𝔼).rowAt _ (Fin.castAdd _ (Fin.castAdd _ (Fin.castAdd _ d))) = _
    refine (Scheme.rowAt_mirror_castAdd _ _).trans ?_
    refine Scheme.rowAt_catalogueLayer_castAdd (hS := T0.not_le) i ?_
    change ((I.attachment g).appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ 2
    rw [Scheme.appendFullCellsScheme_grade_castAdd]; exact hd
  set h := agreementHeight (Scheme.heightSet Γ B' 2) (Scheme.layerEntry Ent i) (T0.v R₀) with hh
  obtain ⟨hhG, hhag⟩ := agreementHeight_spec (Scheme.bot_mem_heightSet Γ B' 2)
    (Scheme.layerEntry Ent i) (T0.v R₀)
  have hT0v (d : Fin (I.attachment g).card) : T0.v R₀ (Fin.castAdd _ d) = R₀ d :=
    Scheme.LadderBaseData.stateExt_castAdd hR₀l hcard d
  -- the decoder reads `t₀` at least at the cap
  have hθt₀ : c ≤ θ h := by
    have e := hθr t₀ (hbelow t₀ ht₀Y)
    rw [hrow_t₀] at e
    rw [e]
    exact le_min hwt₀ (hcv.trans (hv.trans hle))
  -- the decoder reads `R₀ b` at `b`
  have hwb : w (I.attachEmb g H Γ A B' b) = R₀ b := by
    have e := hq'q ⟨_, hmemY b hb⟩
    rw [← hwq' _ (hmemY b hb)] at e
    change min (w _) c = min (q (I.attachEmb g H Γ A B' b)) c at e
    rw [hq, replicatedWriting_attachEmb hcard hR₀l, min_eq_left hbc.le] at e
    rcases le_total (w (I.attachEmb g H Γ A B' b)) c with h' | h'
    · rwa [min_eq_left h'] at e
    · rw [min_eq_right h'] at e; exact absurd e.symm hbc.ne
  have hlt_b : Scheme.layerEntry Ent i (Fin.castAdd _ b) < h := by
    by_contra hge
    have e := hθr _ (hbelow _ (hmemY b hb))
    rw [hrow_att b hb, hwb, min_eq_left (hbc.le.trans (hcv.trans (hv.trans hle)))] at e
    have := hθ.monotone (not_lt.mp hge)
    rw [e] at this
    exact absurd (hθt₀.trans this) (not_le.mpr hbc)
  have hb_eq : Scheme.layerEntry Ent i (Fin.castAdd _ b) = R₀ b := by
    have e := hhag (Fin.castAdd _ b)
    rw [min_eq_left hlt_b.le, hT0v] at e
    rcases le_total (R₀ b) h with h' | h'
    · rwa [min_eq_left h'] at e
    · rw [min_eq_right h'] at e; exact absurd e hlt_b.ne
  have hah : R₀ a < h := hgap h hhG (hb_eq ▸ hlt_b)
  have hentry (d : Fin (I.attachment g).card) (hd : R₀ d = R₀ a) :
      Scheme.layerEntry Ent i (Fin.castAdd _ d) = R₀ a := by
    have e := hhag (Fin.castAdd _ d)
    rw [hT0v, hd, min_eq_left hah.le] at e
    rcases le_total (Scheme.layerEntry Ent i (Fin.castAdd _ d)) h with h' | h'
    · rwa [min_eq_left h'] at e
    · rw [min_eq_right h'] at e; exact absurd e.symm hah.ne
  -- the decoder reads `v` and `v'` from one value
  have e1 := hθr _ (hbelow _ (hmemY a ha))
  have e2 := hθr _ (hbelow _ (hmemY a' ha'))
  rw [hrow_att a ha, hentry a rfl, hwctx a ha hsa hpa, min_eq_left (hv.trans hle)] at e1
  rw [hrow_att a' ha', hentry a' haa, hwctx a' ha' hsa' hpa', min_eq_left (hv'.trans hle)] at e2
  exact hne (e1.symm.trans e2)

end Seed

end VaughtConjecture

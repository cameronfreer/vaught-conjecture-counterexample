/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedContextPin
import VaughtConjecture.Extension.LadderTowerContextLiftReplicated

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

**The gap is void under a context cell reading the tied cells** (`Seed.not_gap_of_context_cell`,
`Seed.not_gap_of_full_context_cell`): a context cell `d` of grade `2` reading `a` and `a'`, with
the prescription at `d` at least `v` and `v'`, gives a height at `2` in `(R₀ b, R₀ a]`: `R₀ d` if
`R₀ d < R₀ a`; otherwise the capped decoder of the prescription at `d` reads `a` and `a'` apart,
that of `R₀` reads them alike, and a witness identifies two labels only at a value self-visible at
its grade (`Label.isSelfVisible_of_witness_eq`), so `R₀ a` is a height.  For context-only
prescriptions over a context with a cell at `(ctxCoatom 1, 2)` above `a₃` (availability in a legal
context) the gap does not occur.

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
the top `gridPoint 2 B'` of the heights.

**The gap cannot occur when** a context cell of grade `2` reads `a` and `a'` with the prescription
there at least `v` and `v'` (`Seed.not_gap_of_context_cell`), in particular when `a₃` has the
whole context coatom as scope (`Seed.not_gap_of_full_context_cell`); a legal context has such a
cell at `(ctxCoatom 1, 2)` above `a₃` by availability (not compiled here).  So for context-only
prescriptions this obstruction is void wherever such a cell exists. -/
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

/-- **The gap cannot occur under a context cell of grade `2` reading the tied cells** (context-only
prescriptions): in the setting of `Seed.not_cappedLift_context_of_gap`, let `d` be a context cell
of grade `2` reading `a` and `a'` with the prescription `v_d` at `d` at least `v` and `v'`.  Then
there is a height at the grade `2` in `(R₀ b, R₀ a]`.  Either `R₀ d < R₀ a`, and `R₀ d` (a value of
`Γ` self-visible at `2`, at least the cap) is that height; or `R₀ a ≤ R₀ d`, the capped decoder of
the prescription at `d` reads `a` and `a'` apart (so their rows at `d` differ), the capped decoder
of `R₀` at `d` reads them alike, and a witness identifies two labels only at a value self-visible
at its grade (`Label.isSelfVisible_of_witness_eq`): `R₀ a` is self-visible at `2`, a height. -/
theorem not_gap_of_context_cell (hcard : (I.attachmentBase g).S.card ≤ H) {K : ℕ}
    {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : R₀ ∈ (I.attachmentBase g).towerCat Γ A K) {c : Label.{u}}
    {p : (I.replicated g H Γ A B').toCellScheme.below (univ.erase (Fin.last 2), 2) → Label.{u}}
    (hp : (I.replicated g H Γ A B').rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) p)
    (hpq : ∀ e, min (I.replicatedWriting g H Γ A B' R₀ e.1) c = min (p e) c)
    {b a a' d : Fin (I.attachment g).card} (hbc : R₀ b < c) (haa : R₀ a' = R₀ a)
    (hd : (I.attachment g).toCellScheme.grade d = 2)
    (hsd : (I.attachment g).toCellScheme.scope d ⊆ ctxCoatom 1)
    (hda : a ∈ (I.attachment g).toCellScheme.below ((I.attachment g).toCellScheme.gradedIndex d))
    (hda' : a' ∈ (I.attachment g).toCellScheme.below ((I.attachment g).toCellScheme.gradedIndex d))
    {v v' vd : Label.{u}}
    (hpa : ∀ e, e.1 = I.attachEmb g H Γ A B' a → p e = v)
    (hpa' : ∀ e, e.1 = I.attachEmb g H Γ A B' a' → p e = v')
    (hpd : ∀ e, e.1 = I.attachEmb g H Γ A B' d → p e = vd) (hcv : c ≤ v) (hv : v ≤ vd)
    (hv' : v' ≤ vd) (hne : v ≠ v') :
    ¬ ∀ h ∈ Scheme.heightSet Γ B' 2, R₀ b < h → R₀ a < h := by
  classical
  intro hgap
  obtain ⟨hR₀Γ, hR₀l, -⟩ := Scheme.LadderBaseData.mem_towerCat.mp hR₀
  have hgX (x : Fin (I.attachment g).card)
      (hx : x ∈ (I.attachment g).toCellScheme.below
        ((I.attachment g).toCellScheme.gradedIndex d)) :
      I.attachEmb g H Γ A B' x ∈ (𝔼).toCellScheme.below (univ.erase (Fin.last 2), 2) := by
    refine (attachEmb_mem_below_iff x _).mpr ⟨hx.1.trans hsd, ?_⟩
    exact (hx.2 : (I.attachment g).toCellScheme.grade x ≤ _).trans hd.le
  have hdd : d ∈ (I.attachment g).toCellScheme.below
      ((I.attachment g).toCellScheme.gradedIndex d) :=
    CellScheme.mem_below_gradedIndex _ d
  -- the ambient at least the cap at `d` and at `a`
  have hcap (x : Fin (I.attachment g).card) (hx : x ∈ (I.attachment g).toCellScheme.below
      ((I.attachment g).toCellScheme.gradedIndex d)) {vx : Label.{u}}
      (hpx : ∀ e, e.1 = I.attachEmb g H Γ A B' x → p e = vx) (hcx : c ≤ vx) : c ≤ R₀ x := by
    have e := hpq ⟨_, hgX x hx⟩
    rw [hpx _ rfl, min_eq_right hcx] at e
    change min (I.replicatedWriting g H Γ A B' R₀ (I.attachEmb g H Γ A B' x)) c = c at e
    rw [replicatedWriting_attachEmb hcard hR₀l] at e
    exact e ▸ min_le_left _ _
  have hcd : c ≤ R₀ d := hcap d hdd hpd (hcv.trans hv)
  have hca : c ≤ R₀ a := hcap a hda hpa hcv
  have hmemH (x : Fin (I.attachment g).card) (hx : IsSelfVisible 2 (R₀ x)) :
      R₀ x ∈ Scheme.heightSet Γ B' 2 := Scheme.mem_heightSet.mpr (.inr ⟨hR₀Γ x, hx⟩)
  rcases lt_or_ge (R₀ d) (R₀ a) with hlt | hle
  · have hv2 : IsSelfVisible 2 (R₀ d) := hd ▸ hR₀l.orderly d
    exact absurd (hgap _ (hmemH d hv2) (hbc.trans_le hcd)) (not_lt.mpr hlt.le)
  -- the capped decoder of `R₀` at `d`
  obtain ⟨θ₀, hθ₀, -, hθ₀r⟩ := Scheme.exists_cappedDecoder_below (S := I.attachment g)
    (hR₀l.isLawfulBelow ((I.attachment g).toCellScheme.gradedIndex d)) hdd hd
  have e₀ := hθ₀r a hda
  have e₀' := hθ₀r a' hda'
  rw [min_eq_left hle] at e₀
  rw [haa, min_eq_left hle] at e₀'
  -- the capped decoder of the prescription at `d`
  set w : Fin (𝔼).card → Label.{u} := fun z ↦
    if hz : z ∈ (𝔼).toCellScheme.below (univ.erase (Fin.last 2), 2) then p ⟨z, hz⟩ else ⊥
    with hw
  have hwp (z) (hz : z ∈ (𝔼).toCellScheme.below (univ.erase (Fin.last 2), 2)) :
      w z = p ⟨z, hz⟩ := dite_eq_left hz
  have hwl : (𝔼).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) fun z ↦ w z := by
    have : (fun z : (𝔼).toCellScheme.below (univ.erase (Fin.last 2), 2) ↦ w z) = p :=
      funext fun z ↦ hwp z.1 z.2
    rw [this]; exact hp
  obtain ⟨θ, -, -, hθr⟩ := Scheme.exists_cappedDecoder_below hwl (hgX d hdd)
    ((congrArg Prod.snd (gradedIndex_attachEmb d)).trans hd)
  have hbelowE (x) (hx : x ∈ (I.attachment g).toCellScheme.below
      ((I.attachment g).toCellScheme.gradedIndex d)) :
      I.attachEmb g H Γ A B' x ∈ (𝔼).toCellScheme.below
        ((𝔼).toCellScheme.gradedIndex (I.attachEmb g H Γ A B' d)) := by
    rw [gradedIndex_attachEmb]; exact (attachEmb_mem_below_iff x _).mpr hx
  have hwx (x : Fin (I.attachment g).card) (hx : x ∈ (I.attachment g).toCellScheme.below
      ((I.attachment g).toCellScheme.gradedIndex d)) {vx : Label.{u}}
      (hpx : ∀ e, e.1 = I.attachEmb g H Γ A B' x → p e = vx) :
      w (I.attachEmb g H Γ A B' x) = vx := by
    rw [hwp _ (hgX x hx)]; exact hpx _ rfl
  have e₁ := hθr _ (hbelowE a hda)
  have e₁' := hθr _ (hbelowE a' hda')
  rw [rowAt_attachEmb, hwx a hda hpa, hwx d hdd hpd, min_eq_left hv] at e₁
  rw [rowAt_attachEmb, hwx a' hda' hpa', hwx d hdd hpd, min_eq_left hv'] at e₁'
  have hrow : (I.attachment g).rowAt d a ≠ (I.attachment g).rowAt d a' := fun h ↦
    hne (e₁.symm.trans (h ▸ e₁'))
  -- the identification makes `R₀ a` self-visible at `2`
  have hvis : IsSelfVisible 2 (R₀ a) := by
    rcases lt_or_gt_of_ne hrow with h | h
    · have := Label.isSelfVisible_of_witness_eq hθ₀ h (e₀.trans e₀'.symm)
      rwa [e₀] at this
    · have := Label.isSelfVisible_of_witness_eq hθ₀ h (e₀'.trans e₀.symm)
      rwa [e₀'] at this
  exact lt_irrefl _ (hgap _ (hmemH a hvis) (hbc.trans_le hca))

/-- **The gap cannot occur when the dominating context cell has the full context scope**: in the
setting of `Seed.not_cappedLift_context_of_gap`, if the cell `a₃` has scope the whole context
coatom, it reads `a` and `a'` (`Seed.not_gap_of_context_cell` with `d = a₃`). -/
theorem not_gap_of_full_context_cell (hcard : (I.attachmentBase g).S.card ≤ H) {K : ℕ}
    {R₀ : Fin (I.attachment g).card → Label.{u}}
    (hR₀ : R₀ ∈ (I.attachmentBase g).towerCat Γ A K) {c : Label.{u}}
    {p : (I.replicated g H Γ A B').toCellScheme.below (univ.erase (Fin.last 2), 2) → Label.{u}}
    (hp : (I.replicated g H Γ A B').rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) p)
    (hpq : ∀ e, min (I.replicatedWriting g H Γ A B' R₀ e.1) c = min (p e) c)
    {b a a' a₃ : Fin (I.attachment g).card} (hbc : R₀ b < c) (haa : R₀ a' = R₀ a)
    (ha : (I.attachment g).toCellScheme.grade a ≤ 2)
    (ha' : (I.attachment g).toCellScheme.grade a' ≤ 2)
    (ha₃ : (I.attachment g).toCellScheme.grade a₃ = 2)
    (hsa : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom 1)
    (hsa' : (I.attachment g).toCellScheme.scope a' ⊆ ctxCoatom 1)
    (hsa₃ : (I.attachment g).toCellScheme.scope a₃ = ctxCoatom 1) {v v' v₃ : Label.{u}}
    (hpa : ∀ e, e.1 = I.attachEmb g H Γ A B' a → p e = v)
    (hpa' : ∀ e, e.1 = I.attachEmb g H Γ A B' a' → p e = v')
    (hpa₃ : ∀ e, e.1 = I.attachEmb g H Γ A B' a₃ → p e = v₃) (hcv : c ≤ v) (hv : v ≤ v₃)
    (hv' : v' ≤ v₃) (hne : v ≠ v') :
    ¬ ∀ h ∈ Scheme.heightSet Γ B' 2, R₀ b < h → R₀ a < h :=
  not_gap_of_context_cell hcard hR₀ hp hpq hbc haa ha₃ hsa₃.le
    ⟨hsa.trans hsa₃.symm.le, ha.trans ha₃.symm.le⟩ ⟨hsa'.trans hsa₃.symm.le, ha'.trans ha₃.symm.le⟩
    hpa hpa' hpa₃ hcv hv hv' hne

end Seed

end VaughtConjecture

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.HeightSetTie
import VaughtConjecture.Extension.ReplicatedRankAgreement
import VaughtConjecture.Extension.ReplicatedWriting

/-!
# Capped agreement of decoded writings in the replicated scheme

Roadmap, Layer 3 ((R3) and (R4), the rendering of states in the replicated scheme).

A state of the catalogue is **rendered** in the replicated scheme by a decoder: its writing
(`Seed.replicatedWriting`: the state on the attachment, its positive table on the ladder, agreement
heights on the layers, every copy reading its original) followed by a witness.  The question tested
here: do two renderings agreeing capped at a cap `c` on the attachment agree capped at `c` at every
cell?  This is the named statement `Seed.CapCompatibleRendering` (the states of the catalogue at
`m + 2` agreeing capped at `c`, two witnesses bounded by the grade `j` of `c` whose decodings agree
capped at `c` on the attachment, every cell of grade at most `j`).

* **It holds through a common cut** (`Seed.capCompatibleRendering`,
  `Scheme.LadderBaseData.min_map_v_eq_of_cut`): for a value `x ≠ ⊥` of `Γ` self-visible at `j` (a
  height at every grade `2, …, j` of the layers) at which the two states agree capped, and decoders
  agreeing capped at `c` on every label below `x` and reaching `c` at `x`.  A cell of grade at most
  `j` is written as at the height `j - 1` (`Scheme.exists_layerTower_v_eq_of_grade_le`).  With the
  identity decoders the cut is the cap `c` itself, when `c` is such a value
  (`Seed.capCompatibleRendering_id`).
* **It fails at a cap that is not a height** (`Seed.not_capCompatibleRendering_of_split`): two
  states agreeing capped at `c`, separated at a cell where both are at least `c`, with no height
  between `c` and the smaller of the two values.  The layer cell of the first state carries its own
  writing at the top of the height set, and the second state's writing there is their agreement
  height, a height at most the smaller value, hence below `c` (`agreementHeight_le_of_ne`).  The
  decoders are the identity; the states agree capped at `c` before and after decoding.  Reducing to
  the greatest height below `c` gives agreement only capped at that height, and the failure shows
  this is sharp.
* **It fails at a cap that is a height when the decoders are compared on the values of the states
  only** (`Seed.not_capCompatibleRendering_of_collapse`): one state, decoded by the identity and by
  the collapse of the finite parts at `j` (`Label.finCollapse`), at a cap `h ∈ Γ` of finite part
  above `j`.  The two decodings agree capped at `h` on the attachment when the state has no value
  of finite part above `j` below `h`, but at the layer cell of a state agreeing with it capped at
  `h` and separated at a cell below `h` the writing is the agreement height `h` itself
  (`agreementHeight_v_eq`), decoded to `h` and to a label below `h`.

So the rendering keeps capped agreement exactly through a common cut: a coded representative of
the cap among the heights, with the decoders compared on every label below it, not only on the
values of the states.

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4];
witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

/-- **Decoding through a common cut**: two labels agreeing capped at `x`, decoded by monotone maps
agreeing capped at `c` below `x` and reaching `c` at `x`, agree capped at `c`. -/
theorem min_map_eq_of_cut {σ σ' : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ' : Monotone σ')
    {x c w w' : Label.{u}} (hag : min w' x = min w x) (hcx : c ≤ σ x) (hcx' : c ≤ σ' x)
    (hcut : ∀ v < x, min (σ v) c = min (σ' v) c) : min (σ w) c = min (σ' w') c := by
  rcases lt_or_ge w x with h | h
  · rw [eq_of_min_eq_of_lt hag.symm h]
    exact hcut w h
  · have h' : x ≤ w' := not_lt.mp fun h' ↦
      absurd (lt_of_eq_of_lt (eq_of_min_eq_of_lt hag h') h') (not_lt.mpr h)
    rw [min_eq_right (hcx.trans (hσ h)), min_eq_right (hcx'.trans (hσ' h'))]

/-- Two labels agreeing capped at `x` above the smaller of them are equal. -/
theorem eq_of_capAgree_of_min_lt {w w' x : Label.{u}} (h : min w' x = min w x)
    (hlt : min w w' < x) : w = w' := by
  rcases le_total w w' with hww | hww
  · rw [min_eq_left hww] at hlt
    exact (eq_of_min_eq_of_lt h.symm hlt).symm
  · rw [min_eq_right hww] at hlt
    exact eq_of_min_eq_of_lt h hlt

/-- **The collapse at `j` lowers an ordinal of finite part above `j`.** -/
theorem finCollapse_lt {j : ℕ} {a : Ordinal.{u}} (ha : j < finNat a) :
    finCollapse j (a : Label.{u}) < (a : Label.{u}) := by
  rw [finCollapse, blockwise_coe, min_eq_right ha.le]
  refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
  calc blockOf a + (j : Ordinal.{u}) < blockOf a + (finNat a : Ordinal.{u}) :=
        (add_lt_add_iff_left (blockOf a)).mpr (by exact_mod_cast ha)
    _ = a := blockOf_add_finNat a

/-- The collapse at `j` fixes an ordinal of finite part at most `j`. -/
theorem finCollapse_eq_self {j : ℕ} {a : Ordinal.{u}} (ha : finNat a ≤ j) :
    finCollapse j (a : Label.{u}) = (a : Label.{u}) := by
  rw [finCollapse, blockwise_coe, min_eq_left ha, blockOf_add_finNat]

/-- An ordinal of finite part at least `j` is self-visible at `j`. -/
theorem isSelfVisible_of_le_finNat {j : ℕ} {a : Ordinal.{u}} (ha : j ≤ finNat a) :
    IsSelfVisible j (a : Label.{u}) := by
  rw [isSelfVisible_coe, finNat_spec]
  exact_mod_cast ha

/-- **A finite set of labels has a finite part above its finite parts in a block**: some `F`
above a given bound exceeds the finite part of every member of `Γ` in the block `b₀`. -/
theorem exists_finPart_above (Γ : Finset Label.{u}) (b₀ N : ℕ) :
    ∃ F, N < F ∧ ∀ e : ℕ, gridPoint.{u} e b₀ ∈ Γ → e < F := by
  have hfin : {e : ℕ | gridPoint.{u} e b₀ ∈ Γ}.Finite :=
    Set.Finite.preimage (fun e _ e' _ he ↦ le_antisymm
      (by simpa using (gridPoint_le_gridPoint_iff_lex.mp he.le))
      (by simpa using (gridPoint_le_gridPoint_iff_lex.mp he.ge))) Γ.finite_toSet
  obtain ⟨M, hM⟩ := hfin.bddAbove
  exact ⟨max M N + 1, by omega, fun e he ↦ by have := hM he; omega⟩

end Label

namespace Scheme

/-- **A cell of grade at most `K + 1` is written as at the height `K`**: at every height
`K' ≥ K`, a cell of the tower of grade at most `K + 1` carries the writing of every state at one
cell of the tower at the height `K`. -/
theorem exists_layerTower_v_eq_of_grade_le {n : ℕ} {σ : Type*} {B : LayerTower.{u} n σ 0}
    {C : ℕ → Finset σ} {G : ℕ → Finset Label.{u}} (K : ℕ) :
    ∀ K', K ≤ K' → ∀ z : Fin (layerTower B C G K').S.card,
      (layerTower B C G K').S.toCellScheme.grade z ≤ K + 1 →
        ∃ t : Fin (layerTower B C G K).S.card,
          ∀ R, (layerTower B C G K').v R z = (layerTower B C G K).v R t := by
  intro K' hK'
  induction K', hK' using Nat.le_induction with
  | base => exact fun z _ ↦ ⟨z, fun _ ↦ rfl⟩
  | succ K' _ ih =>
    intro z hz
    induction z using Fin.addCases with
    | left z =>
      have hz' : (layerTower B C G K').S.toCellScheme.grade z ≤ K + 1 := by
        change ((layerTower B C G K').S.appendFullCellsScheme (K' + 2) _).grade
          (Fin.castAdd _ z) ≤ K + 1 at hz
        rwa [appendFullCellsScheme_grade_castAdd] at hz
      obtain ⟨t, ht⟩ := ih z hz'
      refine ⟨t, fun R ↦ ?_⟩
      rw [← ht R]
      change layerRow (layerTower B C G K').S (fun d ↦ d) (G (K' + 2))
        ((layerTower B C G K').entries (C (K' + 2))) ((layerTower B C G K').v R)
        (Fin.castAdd _ z) = _
      rw [layerRow_castAdd]
    | right i =>
      exfalso
      change ((layerTower B C G K').S.appendFullCellsScheme (K' + 2) _).grade
        (Fin.natAdd _ i) ≤ K + 1 at hz
      rw [appendFullCellsScheme_grade_natAdd] at hz
      omega

/-- **No height between a cap above a block and the next block's low values**: for `Γ` below
`ω ^ 2`, a cap `ω * b₀ + F` with `F` above `k + 2` and above every finite part of `Γ` in the block
`b₀`, and a value `ω * (b₀ + 1) + f` with `f < k + 2`, every height at the grade `k + 2` at least
the cap lies above the value. -/
theorem lt_of_mem_heightSet_of_cap {Γ : Finset Label.{u}}
    (hΓω : ∀ x ∈ Γ, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) {B' k b₀ F f : ℕ}
    (hF : ∀ e : ℕ, gridPoint.{u} e b₀ ∈ Γ → e < F) (hFk : k + 2 < F) (hf : f < k + 2)
    {x : Label.{u}} (hx : x ∈ heightSet Γ B' (k + 2)) (hcx : gridPoint F b₀ ≤ x) :
    gridPoint f (b₀ + 1) < x := by
  rcases mem_heightSet.mp hx with hx | ⟨hxΓ, hxv⟩
  · rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
    · exact absurd (le_bot_iff.mp hcx) (gridPoint_ne_bot _ _)
    · rcases gridPoint_le_gridPoint_iff_lex.mp hcx with hb | ⟨-, hle⟩
      · exact gridPoint_lt_gridPoint_iff_lex.mpr (by omega)
      · omega
  · rcases lt_omega0_sq_iff.mp (hΓω x hxΓ) with rfl | ⟨i, e, rfl⟩
    · exact absurd (le_bot_iff.mp hcx) (gridPoint_ne_bot _ _)
    · have he : k + 2 ≤ e :=
        (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mp hxv
      change gridPoint F b₀ ≤ gridPoint e i at hcx
      change gridPoint f (b₀ + 1) < gridPoint e i
      rcases gridPoint_le_gridPoint_iff_lex.mp hcx with hb | ⟨rfl, hle⟩
      · exact gridPoint_lt_gridPoint_iff_lex.mpr (by omega)
      · exact absurd (hF e hxΓ) (by omega)

end Scheme

namespace Scheme.LadderBaseData

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin B.S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The catalogues decrease along the grades. -/
theorem towerCat_subset_of_le (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {k l : ℕ} (hkl : k ≤ l) :
    B.towerCat Γ A (l + 2) ⊆ B.towerCat Γ A (k + 2) := by
  induction l, hkl using Nat.le_induction with
  | base => exact subset_rfl
  | succ l _ ih => exact (towerCat_succ_subset hA l).trans ih

/-- The writing of a lawful state at an old cell of the attachment is the state. -/
theorem v_towerEmb_castAdd (hcard : B.S.card ≤ H) {R : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (K : ℕ) (d : Fin B.S.card) :
    (B.ladderTower H Γ A B' K).v R (B.towerEmb K (Fin.castAdd _ d)) = R d :=
  (layerTower_v_emb (B := B.towerBase H) (C := B.towerCat Γ A)
    (G := fun k ↦ heightSet Γ B' k) R _ K).trans (stateExt_castAdd hR hcard d)

/-- **The writing of a state at its own layer cell is the top of the height set.** -/
theorem agreementHeight_v_self (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (k : ℕ)
    (R : Fin B.S.card → Label.{u}) :
    agreementHeight (heightSet Γ B' (k + 2)) ((B.ladderTower H Γ A B' k).v R)
      ((B.ladderTower H Γ A B' k).v R) = gridPoint (k + 2) B' :=
  Label.agreementHeight_self (gridPoint_mem_heightSet Γ)
    (fun _ hx ↦ le_gridPoint_of_mem_heightSet hΓ (by omega) hx) _

/-- **An agreement height is at most a separated value**: two lawful states differing at a cell
have writings with agreement height at most the smaller of their values there. -/
theorem agreementHeight_le_of_ne (hcard : B.S.card ≤ H) {R R' : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (hR' : B.S.rows.IsLawful R') (k : ℕ) {a : Fin B.S.card}
    (hne : R a ≠ R' a) :
    agreementHeight (heightSet Γ B' (k + 2)) ((B.ladderTower H Γ A B' k).v R')
      ((B.ladderTower H Γ A B' k).v R) ≤ min (R a) (R' a) := by
  have hag := (agreementHeight_spec (bot_mem_heightSet Γ B' (k + 2))
    ((B.ladderTower H Γ A B' k).v R') ((B.ladderTower H Γ A B' k).v R)).2
    (B.towerEmb k (Fin.castAdd _ a))
  rw [v_towerEmb_castAdd hcard hR', v_towerEmb_castAdd hcard hR] at hag
  exact not_lt.mp fun hlt ↦ hne (eq_of_capAgree_of_min_lt hag hlt)

/-- **The agreement height at a height of `Γ`**: a lawful state `R''` agreeing with `R` capped at
a value `h ≠ ⊥` of `Γ` self-visible at `k + 2`, and separated from it at a cell where `R''` is at
most `h`, has with `R` the agreement height `h`. -/
theorem agreementHeight_v_eq (hcard : B.S.card ≤ H) {R R'' : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (hR'' : B.S.rows.IsLawful R'') {k : ℕ} {h : Label.{u}}
    (hhΓ : h ∈ Γ) (hh0 : h ≠ ⊥) (hhv : IsSelfVisible (k + 2) h)
    (hag : ∀ d, min (R'' d) h = min (R d) h) {a : Fin B.S.card} (ha : R'' a ≤ h)
    (hlt : R'' a < R a) :
    agreementHeight (heightSet Γ B' (k + 2)) ((B.ladderTower H Γ A B' k).v R)
      ((B.ladderTower H Γ A B' k).v R'') = h := by
  refine le_antisymm ?_ ?_
  · refine (agreementHeight_le_of_ne hcard hR'' hR k hlt.ne).trans ?_
    exact (min_le_left _ _).trans ha
  · exact le_agreementHeight (mem_heightSet.mpr (.inr ⟨hhΓ, hhv⟩)) fun x ↦
      (min_v_eq_of_capAgree hcard hhΓ hh0 hR hR'' hag k (hhv.mono (by omega)) x).symm

/-- **Rendering through a common cut, on the ladder tower**: two lawful states agreeing capped at
a value `x ≠ ⊥` of `Γ` self-visible at `K + 1`, decoded by monotone maps agreeing capped at `c`
below `x` and reaching `c` at `x`, have decoded writings agreeing capped at `c` at every cell of
the tower at the height `K`. -/
theorem min_map_v_eq_of_cut (hcard : B.S.card ≤ H) {R R' : Fin B.S.card → Label.{u}}
    (hR : B.S.rows.IsLawful R) (hR' : B.S.rows.IsLawful R') {x : Label.{u}} (hxΓ : x ∈ Γ)
    (hx0 : x ≠ ⊥) {K : ℕ} (hxv : IsSelfVisible (K + 1) x) (hag : ∀ d, min (R' d) x = min (R d) x)
    {σ σ' : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ' : Monotone σ') {c : Label.{u}}
    (hcx : c ≤ σ x) (hcx' : c ≤ σ' x) (hcut : ∀ w < x, min (σ w) c = min (σ' w) c)
    (t : Fin (B.ladderTower H Γ A B' K).S.card) :
    min (σ ((B.ladderTower H Γ A B' K).v R t)) c =
      min (σ' ((B.ladderTower H Γ A B' K).v R' t)) c :=
  min_map_eq_of_cut hσ hσ' (min_v_eq_of_capAgree hcard hxΓ hx0 hR hR' hag K hxv t) hcx hcx' hcut

end Scheme.LadderBaseData

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **The layer cell of a state in the replicated scheme**: for a state `R` of the catalogue at a
grade `k + 2 ≤ m + 1`, a cell of grade `k + 2` carries the writing of every state `R'` as the
agreement height of the writings of `R'` and `R` at the height `k`. -/
theorem exists_layerCell_replicatedWriting {k : ℕ} (hkm : k + 1 ≤ m)
    {R : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat Γ A (k + 2)) :
    ∃ z : Fin (I.replicated g H Γ A B').card,
      (I.replicated g H Γ A B').toCellScheme.grade z = k + 2 ∧
      ∀ R' : Fin (I.attachment g).card → Label.{u},
        I.replicatedWriting g H Γ A B' R' z = agreementHeight (Scheme.heightSet Γ B' (k + 2))
          (((I.attachmentBase g).ladderTower H Γ A B' k).v R')
          (((I.attachmentBase g).ladderTower H Γ A B' k).v R) := by
  obtain ⟨u, hu, -, hv⟩ := Scheme.exists_layerTower_cell_of_mem_v
    (B := (I.attachmentBase g).towerBase H) (C := (I.attachmentBase g).towerCat Γ A)
    (G := fun k ↦ Scheme.heightSet Γ B' k) k hR m hkm
  refine ⟨Fin.castAdd _ u, congrArg Prod.snd ((Scheme.gradedIndex_mirror_castAdd u).trans hu),
    fun R' ↦ ?_⟩
  change ((I.attachmentBase g).ladderTower H Γ A B' m).v R'
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ u)) = _
  rw [Scheme.mirrorOrig_castAdd]
  exact hv R'

variable (I g H Γ A B') in
/-- **Cap-compatible rendering at the grade `j`**: for every cap `c` self-visible at `j`, two
states of the catalogue at `m + 2` agreeing capped at `c`, and two witnesses bounded by `j` whose
decodings of the states agree capped at `c` on the attachment, the decoded writings agree capped at
`c` at every cell of the replicated scheme of grade at most `j` (the cells of the tower layers, the
ladder, and the copies). -/
def CapCompatibleRendering (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c →
    ∀ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2),
      ∀ R' ∈ (I.attachmentBase g).towerCat Γ A (m + 2),
        (∀ a, min (R a) c = min (R' a) c) →
        ∀ σ σ' : Label.{u} → Label.{u},
          IsWitness (stepSuppressor j) σ → IsWitness (stepSuppressor j) σ' →
          (∀ a, min (σ (R a)) c = min (σ' (R' a)) c) →
          ∀ z : Fin (I.replicated g H Γ A B').card,
            (I.replicated g H Γ A B').toCellScheme.grade z ≤ j →
            min (σ (I.replicatedWriting g H Γ A B' R z)) c =
              min (σ' (I.replicatedWriting g H Γ A B' R' z)) c

/-- **Cap-compatible rendering through a common cut**: two lawful states agreeing capped at a
value `x ≠ ⊥` of `Γ` self-visible at `j` (a height at every grade `2, …, j` of the layers),
decoded by monotone maps agreeing capped at `c` on every label below `x` and reaching `c` at `x`,
have decoded writings agreeing capped at `c` at every cell of the replicated scheme of grade at
most `j`.  The cap `c` need not be a height; the cut `x` must be one, and the decoders are compared
on every label below it. -/
theorem capCompatibleRendering (hcard : (I.attachmentBase g).S.card ≤ H)
    {R R' : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (hR' : (I.attachment g).rows.IsLawful R') {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m + 1)
    {x : Label.{u}} (hxΓ : x ∈ Γ) (hx0 : x ≠ ⊥) (hxv : IsSelfVisible j x)
    (hag : ∀ a, min (R' a) x = min (R a) x) {σ σ' : Label.{u} → Label.{u}} (hσ : Monotone σ)
    (hσ' : Monotone σ') {c : Label.{u}} (hcx : c ≤ σ x) (hcx' : c ≤ σ' x)
    (hcut : ∀ w < x, min (σ w) c = min (σ' w) c) (z : Fin (I.replicated g H Γ A B').card)
    (hz : (I.replicated g H Γ A B').toCellScheme.grade z ≤ j) :
    min (σ (I.replicatedWriting g H Γ A B' R z)) c =
      min (σ' (I.replicatedWriting g H Γ A B' R' z)) c := by
  have hz' : (I.attachTower g H Γ A B').toCellScheme.grade
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) ≤ j - 1 + 1 := by
    have h : (I.attachTower g H Γ A B').toCellScheme.grade
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) ≤ j := hz
    omega
  obtain ⟨t, ht⟩ := Scheme.exists_layerTower_v_eq_of_grade_le
    (B := (I.attachmentBase g).towerBase H) (C := (I.attachmentBase g).towerCat Γ A)
    (G := fun k ↦ Scheme.heightSet Γ B' k) (j - 1) m (by omega) _ hz'
  change min (σ (((I.attachmentBase g).ladderTower H Γ A B' m).v R _)) c =
    min (σ' (((I.attachmentBase g).ladderTower H Γ A B' m).v R' _)) c
  rw [ht R, ht R']
  exact Scheme.LadderBaseData.min_map_v_eq_of_cut hcard hR hR' hxΓ hx0
    (by rwa [Nat.sub_add_cancel hj1]) hag hσ hσ' hcx hcx' hcut t

/-- **With the identity decoders, the rendering keeps capped agreement at a cap that is a value of
`Γ`**, at every cell of grade at most `j`, for a cap self-visible at `j` (a height at every grade
`2, …, j` of the layers). -/
theorem capCompatibleRendering_id (hcard : (I.attachmentBase g).S.card ≤ H)
    {R R' : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (hR' : (I.attachment g).rows.IsLawful R') {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m + 1)
    {c : Label.{u}} (hcΓ : c ∈ Γ) (hc0 : c ≠ ⊥) (hcv : IsSelfVisible j c)
    (hag : ∀ a, min (R a) c = min (R' a) c) (z : Fin (I.replicated g H Γ A B').card)
    (hz : (I.replicated g H Γ A B').toCellScheme.grade z ≤ j) :
    min (I.replicatedWriting g H Γ A B' R z) c = min (I.replicatedWriting g H Γ A B' R' z) c :=
  capCompatibleRendering (σ := id) (σ' := id) hcard hR hR' hj1 hjm hcΓ hc0 hcv
    (fun a ↦ (hag a).symm) monotone_id monotone_id le_rfl le_rfl (fun _ _ ↦ rfl) z hz

/-- **The rendering fails at a cap that is not a height** (split upper values): two states of the
catalogue at `m + 2` agreeing capped at `c` and separated at a cell `a`, with no height of the
grade `k + 2 ≤ j` between `c` and the smaller of their values at `a`.  At the layer cell of `R`
its writing is the top of the height set, at least `c`, and that of `R'` is their agreement
height, below `c`; the decoders are the identity. -/
theorem not_capCompatibleRendering_of_split (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j k : ℕ}
    (hkj : k + 2 ≤ j) (hkm : k + 1 ≤ m) {c : Label.{u}} (hc : IsSelfVisible j c)
    {R R' : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat Γ A (m + 2))
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A (m + 2))
    (hag : ∀ a, min (R a) c = min (R' a) c) {a : Fin (I.attachment g).card} (hne : R a ≠ R' a)
    (hgap : ∀ x ∈ Scheme.heightSet Γ B' (k + 2), c ≤ x → min (R a) (R' a) < x) :
    ¬ I.CapCompatibleRendering g H Γ A B' j := by
  intro hren
  have hRk := Scheme.LadderBaseData.towerCat_subset_of_le hA (show k ≤ m by omega) hR
  obtain ⟨hRΓ, hRl, -⟩ := Scheme.LadderBaseData.mem_towerCat.mp hR
  have hR'l := (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  obtain ⟨z, hz, hv⟩ := exists_layerCell_replicatedWriting (H := H) (B' := B') hkm hRk
  have e := hren c hc R hR R' hR' hag id id (IsWitness.id_step j) (IsWitness.id_step j) hag z
    (hz ▸ hkj)
  simp only [id] at e
  rw [hv R, hv R', Scheme.LadderBaseData.agreementHeight_v_self (B := I.attachmentBase g)
    (H := H) (A := A) hΓ k R] at e
  have hcRa : c ≤ R a := not_lt.mp fun h ↦ hne (eq_of_min_eq_of_lt (hag a) h).symm
  have hcgp : c ≤ gridPoint (k + 2) B' := hcRa.trans ((hΓ _ (hRΓ a)).trans
    (gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩)))
  rw [min_eq_right hcgp] at e
  have hle := Scheme.LadderBaseData.agreementHeight_le_of_ne (Γ := Γ) (A := A) (B' := B') hcard
    hRl hR'l k hne
  have hmem := (agreementHeight_spec (Scheme.bot_mem_heightSet Γ B' (k + 2))
    (((I.attachmentBase g).ladderTower H Γ A B' k).v R')
    (((I.attachmentBase g).ladderTower H Γ A B' k).v R)).1
  have hlt := not_le.mp fun h ↦ absurd (hgap _ hmem h) (not_lt.mpr hle)
  rw [min_eq_left hlt.le] at e
  exact hlt.ne e.symm

/-- **The rendering fails at a cap that is a height when the decoders agree only on the values of
the states** (long coded values): a state `R` of the catalogue at `m + 2` decoded by the identity
and by the collapse of the finite parts at `j`, which agree capped at the cap `h` on its values, and
a state `R''` of the catalogue at `k + 2 ≤ j` agreeing with `R` capped at `h` and separated from
it at a cell where `R''` is at most `h`.  The cap `h` is a value of `Γ`, self-visible at `j`,
lowered by the collapse.  At the layer cell of `R''` the writing of `R` is `h`, decoded to `h` and
below `h`. -/
theorem not_capCompatibleRendering_of_collapse (hcard : (I.attachmentBase g).S.card ≤ H)
    {j k : ℕ} (hkj : k + 2 ≤ j) (hkm : k + 1 ≤ m) {h : Label.{u}} (hhΓ : h ∈ Γ) (hh0 : h ≠ ⊥)
    (hhv : IsSelfVisible j h) (hhc : finCollapse j h < h)
    {R R'' : Fin (I.attachment g).card → Label.{u}}
    (hR : R ∈ (I.attachmentBase g).towerCat Γ A (m + 2))
    (hR'' : R'' ∈ (I.attachmentBase g).towerCat Γ A (k + 2))
    (hag : ∀ d, min (R'' d) h = min (R d) h) {a : Fin (I.attachment g).card} (ha : R'' a ≤ h)
    (hlt : R'' a < R a) (hfix : ∀ d, min (finCollapse j (R d)) h = min (R d) h) :
    ¬ I.CapCompatibleRendering g H Γ A B' j := by
  intro hren
  have hRl := (Scheme.LadderBaseData.mem_towerCat.mp hR).2.1
  have hR''l := (Scheme.LadderBaseData.mem_towerCat.mp hR'').2.1
  obtain ⟨z, hz, hv⟩ := exists_layerCell_replicatedWriting (H := H) (B' := B') hkm hR''
  have e := hren h hhv R hR R hR (fun _ ↦ rfl) id (finCollapse j) (IsWitness.id_step j)
    (isWitness_finCollapse j) (fun d ↦ (hfix d).symm) z (hz ▸ hkj)
  rw [hv R, Scheme.LadderBaseData.agreementHeight_v_eq hcard hRl hR''l hhΓ hh0
    (hhv.mono hkj) hag ha hlt] at e
  simp only [id, min_self, min_eq_left hhc.le] at e
  exact hhc.ne e.symm

end Seed

end VaughtConjecture

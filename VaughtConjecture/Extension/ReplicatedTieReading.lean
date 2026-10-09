/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftCap
import VaughtConjecture.Extension.ReplicatedServingCell

/-!
# A tie of the ambient inside a block of the grid defeats the lifts into the full face

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap and the context
lift of the replicated scheme).

The layer cells of the replicated scheme at a grade `k ≥ 2` read one another through agreement
heights in the grid at `k`, whose points `ω * b + k` have finite part `k`.  The codes of states
have larger finite parts, so two codes in one block above its grid point are never separated by an
agreement height.

**Every cell above the cap reads the ambient's tie.**  Let the ambient be the writing of a state
`R'` of the catalogue (decoded by a map `σ`), and let `R'` carry `R' a₁ ≤ R' a₂` at two cells of
the attachment of one grade `k`, with every grid point at `k` at most `R' a₂` decoded below a cap
`c`.  A cell `u` at `(univ, k)` whose label exceeds `c` in a lift keeping the ambient at `c`
carries a label at least `c` in the ambient, so the writing's value at `u` (a point of the grid,
`Scheme.layerTower_v_mem`) exceeds `R' a₂`; the state `R` read by `u` agrees with `R'` below that
value (`Seed.exists_reading_of_writing`), so `R a₁ ≤ R a₂`, and the capped decoder of the lift at
`u` reads the lift at `a₁` at most at `a₂`.  Availability asks such a cell above the lift's value
at `a₁`.  So no lawful labelling below `(univ, j)` keeping the ambient at `c` carries `v₂ < v₁` at
`a₂`, `a₁` with `v₁` above `c` (`Seed.not_lawful_of_tie`).

**Consequences.**
* `Seed.not_towerExtensionPos_of_tie`: the extension over the tower at a positive cap
  (`Seed.TowerExtensionPos`) fails at such an ambient and a state breaking the tie above `c`.
* For the admission predicate (`Seed.attachAdmits`): the cap `min P y` of a state `P` of the
  catalogue at a value `y` self-visible at `m + 2` is in the catalogue
  (`Seed.min_mem_towerCat_attachAdmits`) and ties every pair of cells where `P ≥ y`; a grid point
  at `k ≤ m + 1` is not `y` (`Seed.gridPoint_ne_of_isSelfVisible`).  So
  `Seed.not_towerExtensionPos_attachAdmits` (two values `y ≤ P a₂ < P a₁` at one grade
  `2 ≤ k ≤ j`) and, at cells of the context, `Seed.not_hasContextLift_attachAdmits`: **the
  context lift itself fails**, with the prescription the writing of `P` below the context coatom
  and the ambient the writing of `min P y`.
* From a lawful admitted state (`Seed.exists_stateCode_isSelfVisible`, the code keeping the
  values self-visible at `m + 2`, `Label.isSelfVisible_blockCompress_squash`):
  `Seed.not_towerExtensionPos_of_state`, `Seed.not_hasContextLift_of_state`; from a lawful context
  section through its admitted completion over the attachment:
  `Seed.not_hasContextLift_of_section`.
* With two values in different blocks: the raise of the finite parts to `m + 2`
  (`Label.finRaise`, a witness bounded by `m + 2`, `Label.isWitness_finRaise`) separates them and
  makes the lower one self-visible at `m + 2`: `Seed.not_towerExtensionPos_of_blocks`,
  `Seed.not_hasContextLift_of_blocks` — the latter a condition on one lawful section of the first
  coatom type (for instance its labels): two cells of one grade `2 ≤ k ≤ m + 1` carrying ordinals
  of different blocks.

* **Every positive pair** (no condition on the blocks or the finite parts): the ambient may be the
  writing of the positive constant `m + 2` on the support of a state (`Label.posConst`, a witness
  bounded by `m + 2`; the value `Seed.tieValue m` lies in the code set, in the block `0` above its
  grid point `k ≤ m + 1`), and the prescription the state shifted by one block
  (`Label.omegaShift`, a witness at every grade, all positive values above `ω`).  So
  `Seed.not_towerExtensionPos_of_pair` (a lawful admitted state with `⊥ < P₀ a₂ < P₀ a₁` at two
  cells of one grade `2 ≤ k ≤ j`), `Seed.not_cappedLift_context_of_pair` (two context cells) and
  `Seed.not_cappedLift_context_of_section_pair` (a lawful section of the first coatom type with
  `⊥ < u' x₂ < u' x₁` at two cells of one grade `2 ≤ k ≤ m + 1`).  These subsume the conditions
  on blocks and visibility above.  A tie needs both values positive: below a positive cap a value
  `⊥` of the prescription is `⊥` in the ambient.

The hypotheses on the requests (`ClassCalibrated`, the labels pair admitted, the relative lift on
the exact class) and on the values (`codeSet ⊆ Γ ≤ gridPoint 2 B'`) are those under which the
context lift is reduced to the extension over the tower (`Seed.hasContextLift_attachAdmits_pos`).

## References

Lawful sections and bountifulness are [Kni26, Definitions 2.5.4 and 2.5.14]; agreement heights
are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

/-- **The code of a label self-visible at `K` is self-visible at `K`**: the squash at `K` keeps a
finite part at least `K` at least `K`, and the block compression keeps the finite part. -/
theorem isSelfVisible_blockCompress_squash {V : Finset Label.{u}} {K : ℕ} {x : Label.{u}}
    (hx : x ∈ V) (hv : IsSelfVisible K x) :
    IsSelfVisible K (blockCompress (V.image (squash V K)) K (squash V K x)) := by
  induction x using recBotCoeTop with
  | bot => exact isSelfVisible_bot K
  | top =>
    have e : squash V K (⊤ : Label.{u}) = ⊤ := rfl
    rw [e, blockCompress_top, isSelfVisible_coe, finNat_spec,
      finNat_add_natCast (isSuccPrelimit_omega0_mul _)]
    unfold compressBound
    exact_mod_cast (by omega : K ≤ K + 1 + _)
  | coe a =>
    have e : squash V K (a : Label.{u}) =
        ((blockOf a + (squashNat V K (finNat a) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := rfl
    have hxW : squash V K (a : Label.{u}) ∈ V.image (squash V K) := mem_image_of_mem _ hx
    rw [e] at hxW ⊢
    rw [blockCompress_coe hxW, finNat_add_natCast (isSuccPrelimit_blockOf a), isSelfVisible_coe,
      finNat_spec, finNat_add_natCast (isSuccPrelimit_omega0_mul _)]
    rw [isSelfVisible_coe, finNat_spec] at hv
    have hK : K ≤ finNat a := by exact_mod_cast hv
    rw [squashNat_of_le hK]
    exact_mod_cast Nat.le_add_right K _

/-- **The raise of the finite parts to `K`**: every ordinal keeps its block and its finite part is
raised to at least `K`. -/
noncomputable def finRaise (K : ℕ) : Label.{u} → Label.{u} := blockwise fun f ↦ max f K

/-- **The raise to `K` is a witness bounded by `K`**: at a threshold `k ≤ K` a raised finite part
is at least `k`, so visibility replacement fixes the raised label, and the raise of a replaced
label is the same raised label. -/
theorem isWitness_finRaise (K : ℕ) : IsWitness (stepSuppressor K) (finRaise.{u} K) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := rfl
  monotone := monotone_blockwise fun _ _ h ↦ max_le_max h le_rfl
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · induction x using recBotCoeTop with
      | bot => rfl
      | top => rfl
      | coe a =>
        rw [finRaise, visibilityReplace_coe, blockwise_coe, blockwise_coe, visibilityReplace_coe,
          visibilityReplace_eq_blockOf, visibilityReplace_eq_blockOf]
        simp only [blockOf_add_natCast (isSuccPrelimit_blockOf a),
          finNat_add_natCast (isSuccPrelimit_blockOf a)]
        have h1 : ¬ max (finNat a) K < k := by omega
        rw [ite_eq_right h1]
        by_cases h : finNat a < k
        · rw [ite_eq_left h, max_eq_right (by omega : finNat a ≤ K),
            max_eq_right (by omega : i ≤ K)]
        · rw [ite_eq_right h]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, finRaise, blockwise_eq_bot_iff] at hx
      subst hx
      rfl

theorem finRaise_eq_bot_iff (K : ℕ) {x : Label.{u}} : finRaise K x = ⊥ ↔ x = ⊥ :=
  blockwise_eq_bot_iff _

/-- A raised ordinal is self-visible at `K`. -/
theorem isSelfVisible_finRaise (K : ℕ) (a : Ordinal.{u}) :
    IsSelfVisible K (finRaise K (a : Label.{u})) := by
  rw [finRaise, blockwise_coe, isSelfVisible_coe, finNat_spec,
    finNat_add_natCast (isSuccPrelimit_blockOf a)]
  exact_mod_cast le_max_right _ _

/-- The raise keeps the order of labels of different blocks. -/
theorem finRaise_lt_finRaise {K : ℕ} {a b : Ordinal.{u}} (h : blockOf a < blockOf b) :
    finRaise K (a : Label.{u}) < finRaise K (b : Label.{u}) := by
  rw [finRaise, blockwise_coe, blockwise_coe, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  exact (add_natCast_lt_of_lt (isSuccPrelimit_blockOf b) h _).trans_le le_self_add

/-- **The shift by one block**: `a ↦ ω + a` on ordinals; `⊥` and the formal top are fixed. -/
noncomputable def omegaShift : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun a ↦ Ordinal.omega0 + a)

/-- **The shift by one block is a witness** bounded by every `K`: visibility replacement acts on
the part after the limit `ω`. -/
theorem isWitness_omegaShift (K : ℕ) : IsWitness (stepSuppressor K) (omegaShift.{u}) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := rfl
  monotone := Monotone.withBot_map (Monotone.withTop_map fun _ _ h ↦ add_le_add_right h _)
  visibilityReplace_comm x k _ i _ := by
    induction x using recBotCoeTop with
    | bot => rfl
    | top => rfl
    | coe a =>
      change ((Ordinal.omega0 + Ordinal.visibilityReplace k i a : Ordinal.{u}) : Label.{u}) =
        ((Ordinal.visibilityReplace k i (Ordinal.omega0 + a) : Ordinal.{u}) : Label.{u})
      rw [Ordinal.visibilityReplace_add Ordinal.isSuccLimit_omega0.isSuccPrelimit]

theorem omegaShift_eq_bot_iff {x : Label.{u}} : omegaShift x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => simp [omegaShift]
  | top => simp [omegaShift]
  | coe a => simp [omegaShift]

theorem omegaShift_strictMono : StrictMono (omegaShift.{u}) :=
  WithBot.strictMono_map_iff.mpr (WithTop.strictMono_map_iff.mpr fun _ _ h ↦
    (add_lt_add_iff_left _).mpr h)

/-- A shifted label other than `⊥` is at least every ordinal below `ω`. -/
theorem le_omegaShift {x : Label.{u}} (hx : x ≠ ⊥) {o : Ordinal.{u}} (ho : o < Ordinal.omega0) :
    (o : Label.{u}) ≤ omegaShift x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe a =>
    change (o : Label.{u}) ≤ ((Ordinal.omega0 + a : Ordinal.{u}) : Label.{u})
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (ho.le.trans le_self_add))

/-- **The positive constant** `v`: `⊥` at `⊥`, `v` elsewhere. -/
noncomputable def posConst (v : Label.{u}) (x : Label.{u}) : Label.{u} := if x = ⊥ then ⊥ else v

/-- **The positive constant at a label self-visible at `K` is a witness bounded by `K`**:
visibility replacement keeps `⊥` and the other labels apart and fixes `v`. -/
theorem isWitness_posConst {K : ℕ} {v : Label.{u}} (hv : IsSelfVisible K v) :
    IsWitness (stepSuppressor K) (posConst v) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := ite_eq_left rfl
  monotone x y hxy := by
    unfold posConst
    by_cases hx : x = ⊥
    · rw [ite_eq_left hx]; exact bot_le
    · rw [ite_eq_right hx, ite_eq_right (show ¬ y = ⊥ from fun hy ↦ hx (le_bot_iff.mp
        (hy ▸ hxy)))]
  visibilityReplace_comm x k hx i hi := by
    have hinv : posConst v (visibilityReplace k i x) = posConst v x := by
      simp only [posConst, visibilityReplace_eq_bot_iff]
    rw [hinv]
    by_cases hk : k ≤ K
    · unfold posConst
      split_ifs
      · rfl
      · exact ((hv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]

theorem posConst_eq_bot_iff {v x : Label.{u}} (hv : v ≠ ⊥) : posConst v x = ⊥ ↔ x = ⊥ := by
  unfold posConst
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h' ↦ absurd h' hv, fun h' ↦ absurd h' h⟩

end Label

namespace Scheme

variable {n : ℕ} {σ : Type*} {B : LayerTower.{u} n σ 0} {C : ℕ → Finset σ}
  {G : ℕ → Finset Label.{u}}

/-- **The writing of a state at a cell of a layer is a value of the layer's label set**: at every
height `K ≥ k + 1`, the writing of every state at a cell of full scope at the grade `k + 2` lies
in `G (k + 2)` (it is an agreement height). -/
theorem layerTower_v_mem (hG0 : ∀ k, ⊥ ∈ G (k + 2)) (k : ℕ) (R' : σ) :
    ∀ K, k + 1 ≤ K → ∀ u : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) →
      (layerTower B C G K).v R' u ∈ G (k + 2) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro u hu
    set T := layerTower B C G k with hT
    classical
    obtain ⟨i, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T.S) (k := k + 2)
      (read := fun d ↦ d) (G := G (k + 2)) (C := T.entries (C (k + 2))) (hS := T.not_le) hu
    change layerRow T.S (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2))) (T.v R')
      (Fin.natAdd _ i) ∈ G (k + 2)
    rw [layerRow_natAdd]
    exact (agreementHeight_spec (hG0 k) _ _).1
  | succ K hK ih =>
    intro u hu
    set T := layerTower B C G K with hT
    have hu' : ∃ u', u = Fin.castAdd _ u' := by
      induction u using Fin.addCases with
      | left u' => exact ⟨u', rfl⟩
      | right i =>
        exfalso
        have h := congrArg Prod.snd hu
        change (T.S.appendFullCellsScheme (K + 2) _).grade (Fin.natAdd _ i) = k + 2 at h
        rw [appendFullCellsScheme_grade_natAdd] at h
        omega
    obtain ⟨u', rfl⟩ := hu'
    have hu'' : T.S.toCellScheme.gradedIndex u' = ((univ : Finset (Fin n)), k + 2) := by
      have h := hu
      change (T.S.appendFullCellsScheme (K + 2) _).gradedIndex (Fin.castAdd _ u') = _ at h
      rwa [appendFullCellsScheme_gradedIndex_castAdd] at h
    change layerRow T.S (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2))) (T.v R')
      (Fin.castAdd _ u') ∈ G (k + 2)
    rw [layerRow_castAdd]
    exact ih u' hu''

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- The ladder tower over the attachment. -/
local notation "𝕋" => Seed.attachTower I g H Γ A B'

/-- The full face at a grade. -/
local notation "𝕐[" k "]" => ((univ : Finset (Fin (m + 2))), k)

/-- **A cell of full scope at a grade `k ≥ 2` reads the attachment as a state agreeing with every
writing below the writing's value at the cell**: for a cell `f` of the tower at `(univ, k)`,
`2 ≤ k ≤ m + 1`, some lawful state `R` of the catalogue at `k` is read by `f` at the cells of the
attachment of grade at most `k`, the writing of a lawful state `R'` at `f` is a point of the grid
at `k`, and `R` equals `R'` at every cell where `R'` lies below that value. -/
theorem exists_reading_of_writing (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ}
    (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) (f : Fin (𝕋).card)
    (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k))
    {R' : Fin (I.attachment g).card → Label.{u}} (hR' : (I.attachment g).rows.IsLawful R') :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A k,
      (∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
        (𝔼).rowAt (Fin.castAdd _ f) (I.attachEmb g H Γ A B' a) = R a) ∧
      ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f ∈ Scheme.heightSet Γ B' k ∧
      ∀ a, R' a < ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f → R a = R' a := by
  have hf' : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k - 2 + 2) := by
    rw [show k - 2 + 2 = k by omega]; exact hf
  obtain ⟨R, hRC, hrow, hagr⟩ := Scheme.exists_layerTower_layerCell
    (B := (I.attachmentBase g).towerBase H) (C := (I.attachmentBase g).towerCat Γ A)
    (G := fun k ↦ Scheme.heightSet Γ B' k) (fun _ ↦ Scheme.bot_mem_heightSet _ _ _) (k - 2) m
    (by omega) f hf'
  have hk : k - 2 + 2 = k := by omega
  rw [hk] at hRC
  have hRl : (I.attachment g).rows.IsLawful R :=
    (Scheme.LadderBaseData.mem_towerCat.mp hRC).2.1
  refine ⟨R, hRC, fun a ha ↦ ?_, ?_, fun a ha ↦ ?_⟩
  · refine (Scheme.rowAt_mirror_castAdd _ _).trans ((hrow (Fin.castAdd _ a) ?_).trans
      (Scheme.LadderBaseData.stateExt_castAdd hRl hcard a))
    change ((I.attachment g).appendFullCellsScheme 1 _).grade (Fin.castAdd _ a) ≤ k - 2 + 2
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    omega
  · have h := Scheme.layerTower_v_mem (B := (I.attachmentBase g).towerBase H)
      (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k)
      (fun _ ↦ Scheme.bot_mem_heightSet _ _ _) (k - 2) R' m (by omega) f hf'
    rwa [hk] at h
  · have e := hagr R' (Fin.castAdd _ a)
    change min ((I.attachmentBase g).stateExt H R' (Fin.castAdd _ a)) _ =
      min ((I.attachmentBase g).stateExt H R (Fin.castAdd _ a)) _ at e
    erw [Scheme.LadderBaseData.stateExt_castAdd hR' hcard,
      Scheme.LadderBaseData.stateExt_castAdd hRl hcard] at e
    rw [min_eq_left ha.le] at e
    rcases le_total (R a) (((I.attachmentBase g).ladderTower H Γ A B' m).v R' f) with h | h
    · rw [min_eq_left h] at e; exact e.symm
    · rw [min_eq_right h] at e; exact absurd e ha.ne

/-- **No lawful labelling breaks a tie of the ambient above the grid.**  Let the ambient be the
writing of a state `R'` of the catalogue decoded by a map `σ`, and let two attachment cells `a₁`,
`a₂` of one grade `2 ≤ k ≤ j` carry `R' a₁ ≤ R' a₂`, with every point `x` of the grid at `k` at most
`R' a₂` decoded below the cap `c`.  Then no labelling `r` lawful below `(univ, j)` with the
observation of the ambient at `c` carries labels `v₂ < v₁` at `a₂`, `a₁` with `v₁` above `c`: a
cell at `(univ, k)` available above `v₁` carries a label above `c` in the ambient, so the
writing's value at it, a point of the grid at `k`, exceeds `R' a₂`; its state agrees with `R'` at
`a₁` and `a₂`; and its capped decoder reads `v₁ ≤ v₂`. -/
theorem not_lawful_of_tie (hcard : (I.attachmentBase g).S.card ≤ H)
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j)
    (hjm : j ≤ m + 1) {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A (m + 2)) {σ : Label.{u} → Label.{u}}
    {c : Label.{u}} {a₁ a₂ : Fin (I.attachment g).card}
    (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k) (hR'12 : R' a₁ ≤ R' a₂)
    (hgrid : ∀ x ∈ Scheme.heightSet Γ B' k, x ≤ R' a₂ → σ x < c) {v₁ v₂ : Label.{u}} (h21 : v₂ < v₁)
    (hc1 : ¬ v₁ ≤ c)
    {r : (𝔼).toCellScheme.below 𝕐[j] → Label.{u}}
    (hr : (𝔼).rows.IsLawfulBelow 𝕐[j] r)
    (hr₁ : ∀ d, d.1 = I.attachEmb g H Γ A B' a₁ → r d = v₁)
    (hr₂ : ∀ d, d.1 = I.attachEmb g H Γ A B' a₂ → r d = v₂)
    (hrq : ∀ d, min (r d) c = min (σ (I.replicatedWriting g H Γ A B' R' d)) c) : False := by
  classical
  have hR'l : (I.attachment g).rows.IsLawful R' :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  -- the labelling on all cells
  set w : Fin (𝔼).card → Label.{u} := fun d ↦ if hd : d ∈ (𝔼).toCellScheme.below 𝕐[j] then
    r ⟨d, hd⟩ else ⊥ with hwdef
  have hwr : (fun d : (𝔼).toCellScheme.below 𝕐[j] ↦ w d) = r :=
    funext fun d ↦ dite_eq_left d.2
  have hw : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ w d := by rw [hwr]; exact hr
  have hmemY (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k) :
      I.attachEmb g H Γ A B' a ∈ (𝔼).toCellScheme.below 𝕐[j] :=
    (attachEmb_mem_below_iff a _).mpr ⟨subset_univ _, ha.le.trans hkj⟩
  have hw₁ : w (I.attachEmb g H Γ A B' a₁) = v₁ := by
    change (if hd : _ ∈ (𝔼).toCellScheme.below 𝕐[j] then r ⟨_, hd⟩ else ⊥) = v₁
    rw [dite_eq_left (hmemY a₁ ha₁)]
    exact hr₁ ⟨_, hmemY a₁ ha₁⟩ rfl
  have hw₂ : w (I.attachEmb g H Γ A B' a₂) = v₂ := by
    change (if hd : _ ∈ (𝔼).toCellScheme.below 𝕐[j] then r ⟨_, hd⟩ else ⊥) = v₂
    rw [dite_eq_left (hmemY a₂ ha₂)]
    exact hr₂ ⟨_, hmemY a₂ ha₂⟩ rfl
  -- a cell at `(univ, k)` available above `v₁`
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  obtain ⟨u₀, -, hu₀, -⟩ := exists_cell_of_mem_towerCat (B' := B') hcard hk2 (hkj.trans hjm)
    (Scheme.LadderBaseData.towerCat_mono hA (by omega : k' ≤ m) hR')
  have hu₀Y : u₀ ∈ (𝔼).toCellScheme.below 𝕐[j] := by
    rw [CellScheme.mem_below, hu₀]; exact ⟨subset_rfl, hkj⟩
  obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨u, huE, hle⟩ := havail (I.attachEmb g H Γ A B' a₁) u₀ hu₀Y
    (by rw [show (𝔼).toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
        exact subset_univ _)
    (by rw [show (𝔼).toCellScheme.grade u₀ = k' + 2 from congrArg Prod.snd hu₀]
        exact (congrArg Prod.snd (gradedIndex_attachEmb a₁)).trans ha₁)
  rw [hu₀] at huE
  rw [hw₁] at hle
  obtain ⟨f, rfl, hf⟩ := exists_eq_castAdd_of_scope u (congrArg Prod.fst huE)
  rw [huE] at hf
  have huY : (Fin.castAdd _ f : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below 𝕐[j] := by
    rw [CellScheme.mem_below, huE]; exact ⟨subset_rfl, hkj⟩
  -- the ambient is at least the cap at the cell
  set W := ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f with hWdef
  have hqu : c ≤ σ W := by
    have e := hrq ⟨_, huY⟩
    have e1 : w (Fin.castAdd _ f) = r ⟨_, huY⟩ := dite_eq_left huY
    rw [← e1, min_eq_right ((not_le.mp hc1).le.trans hle)] at e
    have e2 : I.replicatedWriting g H Γ A B' R' (Fin.castAdd _ f) = W := by
      change ((I.attachmentBase g).ladderTower H Γ A B' m).v R'
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ f)) = W
      rw [Scheme.mirrorOrig_castAdd]
    rw [show (⟨_, huY⟩ : (𝔼).toCellScheme.below 𝕐[j]).1 = Fin.castAdd _ f from rfl, e2] at e
    exact e ▸ min_le_left _ _
  -- the reading of the cell agrees with `R'` at the two cells
  obtain ⟨R, -, hrow, hWg, hRR'⟩ := exists_reading_of_writing (Γ := Γ) (A := A) (B' := B')
    hcard hk2 (hkj.trans hjm) f hf hR'l
  have hW2 : R' a₂ < W := by
    by_contra hcon
    exact absurd hqu (not_le.mpr (hgrid W hWg (not_lt.mp hcon)))
  have hR1 : R a₁ = R' a₁ := hRR' a₁ (hR'12.trans_lt hW2)
  have hR2 : R a₂ = R' a₂ := hRR' a₂ hW2
  -- the capped decoder at the cell
  obtain ⟨θ, hθ, -, hθr⟩ := Scheme.exists_cappedDecoder_below hw huY (congrArg Prod.snd huE)
  have hb (a : Fin (I.attachment g).card)
      (ha : (I.attachment g).toCellScheme.grade a = k' + 2) :
      I.attachEmb g H Γ A B' a ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ f)) := by
    rw [huE]; exact (attachEmb_mem_below_iff a _).mpr ⟨subset_univ _, ha.le⟩
  have h1 := hθr _ (hb a₁ ha₁)
  have h2 := hθr _ (hb a₂ ha₂)
  rw [hrow a₁ ha₁.le, hR1, hw₁, min_eq_left hle] at h1
  rw [hrow a₂ ha₂.le, hR2, hw₂] at h2
  have hmono := hθ.monotone hR'12
  rw [h1, h2] at hmono
  exact absurd (hmono.trans (min_le_left _ _)) (not_le.mpr h21)

/-- **A tie of the ambient above the grid defeats the extension over the tower at a positive
cap**: the ambient is the decoded writing of `R'` (lawful below `(univ, j)` for a witness bounded
by `j` sending only `⊥` to `⊥`), and a lawful state `P` satisfying `A (m + 2)`, equal to it capped
at `c` below the grade, breaks the tie of `R'` at `a₁`, `a₂` above `c`
(`Seed.not_lawful_of_tie`). -/
theorem not_towerExtensionPos_of_tie (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j) (hjm : j ≤ m + 1)
    {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A (m + 2))
    {σ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor j) σ)
    (hσb : ∀ x, σ x = ⊥ → x = ⊥) {c : Label.{u}} (hc : IsSelfVisible j c) (hc0 : c ≠ ⊥)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : A (m + 2) P)
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ j → min (P a) c = min (σ (R' a)) c)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k) (hR'12 : R' a₁ ≤ R' a₂)
    (hP12 : P a₂ < P a₁) (hPc : ¬ P a₁ ≤ c)
    (hgrid : ∀ x ∈ Scheme.heightSet Γ B' k, x ≤ R' a₂ → σ x < c) :
    ¬ TowerExtensionPos I g H Γ A B' j := by
  intro h
  have hR'l : (I.attachment g).rows.IsLawful R' :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  set Y : Finset (Fin (m + 2)) × ℕ := ((univ : Finset (Fin (m + 2))), j) with hYdef
  have hq : (𝔼).rows.IsLawfulBelow Y fun d ↦ σ (I.replicatedWriting g H Γ A B' R' d) :=
    isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hR' Y hσ hσb
  obtain ⟨q', hq', hq'P, hq'q⟩ := h c hc hc0 _ hq P hP hPA (fun d a ha ↦ by
      have hag : (I.attachment g).toCellScheme.grade a ≤ j :=
        ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a Y).mp
          (ha ▸ d.2)).2
      change min (P a) c = min (σ (I.replicatedWriting g H Γ A B' R' d.1)) c
      rw [← ha, replicatedWriting_attachEmb hcard hR'l]
      exact hPq a hag)
    ⟨a₁, ha₁.le.trans hkj, hPc⟩
  exact not_lawful_of_tie hcard hA hk2 hkj hjm hR' ha₁ ha₂ hR'12 hgrid hP12 hPc hq'
    (fun d hd ↦ hq'P d a₁ hd.symm) (fun d hd ↦ hq'P d a₂ hd.symm) hq'q

/-! ### The tie for the admission predicate -/

/-- A point of the grid at a grade `k` is self-visible at no grade above `k`. -/
theorem gridPoint_ne_of_isSelfVisible {k K : ℕ} (hk : k < K) (b : ℕ) {y : Label.{u}}
    (hy : IsSelfVisible K y) : gridPoint k b ≠ y := by
  rintro rfl
  rw [gridPoint, isSelfVisible_coe, finNat_spec,
    finNat_add_natCast (isSuccPrelimit_omega0_mul (b : Ordinal.{u}))] at hy
  exact absurd (by exact_mod_cast hy) (not_le.mpr hk)

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The cap of a state of the catalogue** at a label of the values self-visible at `m + 2` is a
state of the catalogue, for requests calibrated on the class. -/
theorem min_mem_towerCat_attachAdmits
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {P : Fin (I.attachment g).card → Label.{u}}
    (hP : P ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2)) {y : Label.{u}}
    (hy : y ∈ Γ) (hy0 : y ≠ ⊥) (hyv : IsSelfVisible (m + 2) y) :
    (fun a ↦ min (P a) y) ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2) := by
  obtain ⟨hPΓ, hPl, hPA⟩ := Scheme.LadderBaseData.mem_towerCat.mp hP
  have hν : IsWitness (stepSuppressor (m + 2)) fun x ↦ min x y :=
    (IsWitness.id_step (m + 2)).min_const hyv
  refine Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ ?_,
    hPl.min_const_of_isSelfVisible (fun a ↦ (I.attachmentType g).grade_le a) hyv,
    attachAdmits_comp hd hQ hPA hν (fun a ↦ ?_) _⟩
  · rcases min_choice (P a) y with h | h <;> rw [h]
    · exact hPΓ a
    · exact hy
  · constructor
    · intro h
      rcases min_eq_bot.mp h with h | h
      · exact h
      · exact absurd h hy0
    · intro h; rw [h, min_eq_left bot_le]

/-- **The extension over the tower at a positive cap fails for the admission predicate** whenever
a state `P` of the catalogue at `m + 2` carries two values `P a₂ < P a₁` at cells of one grade
`2 ≤ k ≤ j`, both at least a value `y ≠ ⊥` of `Γ` self-visible at `m + 2`: the ambient is the
writing of the cap of `P` at `y`, which ties `a₁` and `a₂` at `y`, a value strictly inside a block
of the grid at `k` (`Seed.not_towerExtensionPos_of_tie`). -/
theorem not_towerExtensionPos_attachAdmits (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j) (hjm : j ≤ m + 1)
    {P : Fin (I.attachment g).card → Label.{u}}
    (hP : P ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2)) {y : Label.{u}}
    (hy : y ∈ Γ) (hy0 : y ≠ ⊥) (hyv : IsSelfVisible (m + 2) y)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k) (hy2 : y ≤ P a₂) (h21 : P a₂ < P a₁) :
    ¬ TowerExtensionPos I g H Γ (I.attachAdmits g hd Q) B' j := by
  obtain ⟨-, hPl, hPA⟩ := Scheme.LadderBaseData.mem_towerCat.mp hP
  have hy1 : y ≤ P a₁ := hy2.trans h21.le
  refine not_towerExtensionPos_of_tie (R' := fun a ↦ min (P a) y) (σ := id) (c := y) hH hcard hΓ
    (fun k R h ↦ I.attachAdmits_succ g hd Q k R h) hk2 hkj hjm
    (min_mem_towerCat_attachAdmits hd hQ hP hy hy0 hyv) (IsWitness.id_step j)
    (fun _ h ↦ h) (hyv.mono (by omega)) hy0 hPl hPA (fun a _ ↦ ?_) ha₁ ha₂ ?_ h21
    (not_le.mpr (hy2.trans_lt h21)) fun x hx hxy ↦ ?_
  · change min (P a) y = min (min (P a) y) y
    rw [min_assoc, min_self]
  · rw [min_eq_right hy1, min_eq_right hy2]
  · change x < y
    change x ≤ min (P a₂) y at hxy
    rw [min_eq_right hy2] at hxy
    rcases Scheme.mem_heightSet.mp hx with hx | ⟨hxΓ, hxv⟩
    · refine lt_of_le_of_ne hxy ?_
      rcases (mem_grid.mp hx) with rfl | ⟨b, -, rfl⟩
      · exact hy0.symm
      · exact gridPoint_ne_of_isSelfVisible (by omega) b hyv
    · rw [hΓk x hxΓ hxv]; exact bot_lt_iff_ne_bot.mpr hy0

/-- **The context lift fails for the admission predicate** whenever a state `P` of the catalogue
at `m + 2` carries two values `P a₂ < P a₁` at context cells of one grade `2 ≤ k ≤ m + 1`, both at
least a value `y ≠ ⊥` of `Γ` self-visible at `m + 2`: the prescription is the writing of `P` below
the context coatom, the ambient the writing of the cap of `P` at `y`; they agree at `y` below the
coatom, and the lift would break the tie of the ambient at `a₁` and `a₂` above `y`
(`Seed.not_lawful_of_tie`). -/
theorem not_cappedLift_context_attachAdmits (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hk2 : 2 ≤ k)
    (hkm : k ≤ m + 1) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : P ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2)) {y : Label.{u}}
    (hy : y ∈ Γ) (hy0 : y ≠ ⊥) (hyv : IsSelfVisible (m + 2) y)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k)
    (hs₁ : (I.attachment g).toCellScheme.scope a₁ ⊆ ctxCoatom m)
    (hs₂ : (I.attachment g).toCellScheme.scope a₂ ⊆ ctxCoatom m)
    (hy2 : y ≤ P a₂) (h21 : P a₂ < P a₁) :
    ¬ (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), k)) (Y := ((univ : Finset (Fin (m + 2))), k))
      ⟨erase_subset _ _, le_rfl⟩ := by
  intro hlift
  have hA : ∀ k R, I.attachAdmits g hd Q (k + 3) R → I.attachAdmits g hd Q (k + 2) R :=
    fun k R h ↦ I.attachAdmits_succ g hd Q k R h
  have hPl : (I.attachment g).rows.IsLawful P := (Scheme.LadderBaseData.mem_towerCat.mp hP).2.1
  have hy1 : y ≤ P a₁ := hy2.trans h21.le
  have hR' := min_mem_towerCat_attachAdmits hd hQ hP hy hy0 hyv
  have hR'l : (I.attachment g).rows.IsLawful fun a ↦ min (P a) y :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  set wP := I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' P with hwP
  set wR := I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' (fun a ↦ min (P a) y) with hwR
  have hlawP := isLawful_replicatedWriting hH hcard hΓ hA hP
  have hlawR := isLawful_replicatedWriting hH hcard hΓ hA hR'
  obtain ⟨q', hq', hq'q, hq'p⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp
    hlift y (hyv.mono (by omega)) (fun d ↦ wP d) (fun d ↦ wR d)
    (hlawP.isLawfulBelow _) (hlawR.isLawfulBelow _) fun e ↦ by
      obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx e.2
      change min (wR e.1) y = min (wP e.1) y
      rw [← ha, hwR, hwP, replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q)
        (B' := B') hcard hR'l a, replicatedWriting_attachEmb (Γ := Γ)
        (A := I.attachAdmits g hd Q) (B' := B') hcard hPl a, min_assoc, min_self]
  have hmem (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k)
      (hs : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom m) :
      I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a ∈
        (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
          (univ.erase (Fin.last (m + 1)), k) :=
    (attachEmb_mem_below_iff a _).mpr ⟨hs, ha.le⟩
  have hval (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k)
      (hs : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom m) (e) (he : e.1 =
        I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a) : q' e = P a := by
    have h := hq'p ⟨_, hmem a ha hs⟩
    rw [show (Set.inclusion _ ⟨_, hmem a ha hs⟩ : (I.replicated g H Γ (I.attachAdmits g hd Q)
      B').toCellScheme.below ((univ : Finset (Fin (m + 2))), k)) = e from Subtype.ext he.symm]
      at h
    rw [h]
    exact replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B') hcard hPl a
  exact not_lawful_of_tie (R' := fun a ↦ min (P a) y) (σ := id) (c := y) hcard hA hk2 le_rfl hkm
    hR' ha₁ ha₂ (by rw [min_eq_right hy1, min_eq_right hy2])
    (fun x hx hxy ↦ by
      change x ≤ min (P a₂) y at hxy
      rw [min_eq_right hy2] at hxy
      rcases Scheme.mem_heightSet.mp hx with hx | ⟨hxΓ, hxv⟩
      · refine lt_of_le_of_ne hxy ?_
        rcases (mem_grid.mp hx) with rfl | ⟨b, -, rfl⟩
        · exact hy0.symm
        · exact gridPoint_ne_of_isSelfVisible (by omega) b hyv
      · rw [hΓk x hxΓ hxv]; exact bot_lt_iff_ne_bot.mpr hy0)
    h21 (not_le.mpr (hy2.trans_lt h21)) hq' (hval a₁ ha₁ hs₁) (hval a₂ ha₂ hs₂) hq'q

/-- **The code of a state keeps the values self-visible at `m + 2`** (`Seed.exists_stateCode` with
the visibility of the code): every complete lawful admitted state `P` is read from a state `R` of
the catalogue at `m + 2` by a monotone map sending only `⊥` to `⊥`, and `R` is self-visible at
`m + 2` wherever `P` is. -/
theorem exists_stateCode_isSelfVisible
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : I.attachAdmits g hd Q (m + 2) P) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2),
      ∃ σ : Label.{u} → Label.{u}, Monotone σ ∧ σ ⊥ = ⊥ ∧ (∀ a, σ (R a) = P a) ∧
        ∀ a, IsSelfVisible (m + 2) (P a) → IsSelfVisible (m + 2) (R a) := by
  classical
  set V : Finset Label.{u} := univ.image P with hV
  set W : Finset Label.{u} := V.image (squash V (m + 2)) with hW
  have hPV (a : Fin (I.attachment g).card) : P a ∈ V := mem_image_of_mem _ (mem_univ a)
  have hPW (a : Fin (I.attachment g).card) : squash V (m + 2) (P a) ∈ W :=
    mem_image_of_mem _ (hPV a)
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  set S : Fin (I.attachment g).card → Label.{u} := squash V (m + 2) ∘ P with hSdef
  have hSl : (I.attachment g).rows.IsLawful S :=
    hP.map_of_bot_iff hP hgr isWitness_squash fun a ↦ squash_eq_bot_iff
  have hSA : I.attachAdmits g hd Q (m + 2) S :=
    attachAdmits_comp hd hQ hPA isWitness_squash (fun a ↦ squash_eq_bot_iff) _
  set R : Fin (I.attachment g).card → Label.{u} := blockCompress W (m + 2) ∘ S with hRdef
  have hRl : (I.attachment g).rows.IsLawful R :=
    hSl.map_of_bot_iff hSl hgr (isWitness_blockCompress (m + 2))
      fun a ↦ blockCompress_eq_bot_iff (hPW a) (m + 2)
  have hRA : I.attachAdmits g hd Q (m + 2) R :=
    attachAdmits_comp hd hQ hSA (isWitness_blockCompress (m + 2))
      (fun a ↦ blockCompress_eq_bot_iff (hPW a) (m + 2)) _
  have hVc : #V ≤ (I.attachment g).card := card_image_le.trans (by simp)
  have hσw : IsWitness (stepSuppressor (m + 2)) (unsquash V (m + 2) ∘ blockExpand W) :=
    IsWitness.comp_of_bot_reflecting (isWitness_blockExpand (m + 2)) isWitness_unsquash
      fun x hx ↦ unsquash_eq_bot_iff.mp hx
  refine ⟨R, Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ hΓc
      (blockCompress_squash_mem_codeSet hVc (hPV a)), hRl, hRA⟩,
    unsquash V (m + 2) ∘ blockExpand W, hσw.monotone, hσw.map_bot, fun a ↦ ?_,
    fun a ha ↦ isSelfVisible_blockCompress_squash (hPV a) ha⟩
  change unsquash V (m + 2) (blockExpand W (blockCompress W (m + 2)
    (squash V (m + 2) (P a)))) = P a
  rw [blockExpand_blockCompress (hPW a), unsquash_squash (hPV a)]

/-- **The extension over the tower at a positive cap fails for the admission predicate at a
lawful admitted state with two values at one grade**: if a complete lawful state `P₀` satisfying
the admission at `m + 2` carries `P₀ a₂ < P₀ a₁` at two cells of one grade `2 ≤ k ≤ j`, with
`P₀ a₂ ≠ ⊥` self-visible at `m + 2`, then, for values containing the code set, the extension over
the tower at `j` fails (`Seed.not_towerExtensionPos_attachAdmits` at the code of `P₀`, with `y`
the code of `P₀ a₂`). -/
theorem not_towerExtensionPos_of_state (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j) (hjm : j ≤ m + 1)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    {P₀ : Fin (I.attachment g).card → Label.{u}} (hP₀ : (I.attachment g).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits g hd Q (m + 2) P₀)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k) (h21 : P₀ a₂ < P₀ a₁)
    (h20 : P₀ a₂ ≠ ⊥) (h2v : IsSelfVisible (m + 2) (P₀ a₂)) :
    ¬ TowerExtensionPos I g H Γ (I.attachAdmits g hd Q) B' j := by
  obtain ⟨R, hR, σ, hσm, hσ0, hσR, hvis⟩ := exists_stateCode_isSelfVisible hd hQ hΓc hP₀ hP₀A
  have hRΓ := (Scheme.LadderBaseData.mem_towerCat.mp hR).1
  refine not_towerExtensionPos_attachAdmits hH hcard hΓ hd hQ hk2 hkj hjm hR (hRΓ a₂)
    (fun h ↦ h20 ((hσR a₂).symm.trans ((congrArg σ h).trans hσ0))) (hvis a₂ h2v) hΓk ha₁ ha₂
    le_rfl
    (lt_of_not_ge fun h ↦ ?_)
  exact absurd ((hσR a₁).symm.le.trans ((hσm h).trans (hσR a₂).le)) (not_le.mpr h21)

/-- **The context lift fails for the admission predicate** at the grade `k` of
`Seed.not_cappedLift_context_attachAdmits`. -/
theorem not_hasContextLift_attachAdmits (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hk2 : 2 ≤ k)
    (hkm : k ≤ m + 1) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : P ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2)) {y : Label.{u}}
    (hy : y ∈ Γ) (hy0 : y ≠ ⊥) (hyv : IsSelfVisible (m + 2) y)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k)
    (hs₁ : (I.attachment g).toCellScheme.scope a₁ ⊆ ctxCoatom m)
    (hs₂ : (I.attachment g).toCellScheme.scope a₂ ⊆ ctxCoatom m)
    (hy2 : y ≤ P a₂) (h21 : P a₂ < P a₁) :
    ¬ I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' := fun h ↦
  not_cappedLift_context_attachAdmits hH hcard hΓ hd hQ hk2 hkm hP hy hy0 hyv hΓk ha₁ ha₂ hs₁
    hs₂ hy2 h21 (h k (by omega) hkm)

/-- **The context lift fails for the admission predicate at a lawful admitted state with two
values at one grade of the context**: as `Seed.not_towerExtensionPos_of_state`, with `a₁`, `a₂`
cells of the context (`Seed.not_hasContextLift_attachAdmits` at the code of `P₀`). -/
theorem not_cappedLift_context_of_state (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {P₀ : Fin (I.attachment g).card → Label.{u}}
    (hP₀ : (I.attachment g).rows.IsLawful P₀) (hP₀A : I.attachAdmits g hd Q (m + 2) P₀)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k)
    (hs₁ : (I.attachment g).toCellScheme.scope a₁ ⊆ ctxCoatom m)
    (hs₂ : (I.attachment g).toCellScheme.scope a₂ ⊆ ctxCoatom m) (h21 : P₀ a₂ < P₀ a₁)
    (h20 : P₀ a₂ ≠ ⊥) (h2v : IsSelfVisible (m + 2) (P₀ a₂)) :
        ¬ (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), k)) (Y := ((univ : Finset (Fin (m + 2))), k))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨R, hR, σ, hσm, hσ0, hσR, hvis⟩ := exists_stateCode_isSelfVisible hd hQ hΓc hP₀ hP₀A
  have hRΓ := (Scheme.LadderBaseData.mem_towerCat.mp hR).1
  refine not_cappedLift_context_attachAdmits hH hcard hΓ hd hQ hk2 hkm hR (hRΓ a₂)
    (fun h ↦ h20 ((hσR a₂).symm.trans ((congrArg σ h).trans hσ0))) (hvis a₂ h2v) hΓk ha₁ ha₂ hs₁
    hs₂ le_rfl
    (lt_of_not_ge fun h ↦ ?_)
  exact absurd ((hσR a₁).symm.le.trans ((hσm h).trans (hσR a₂).le)) (not_le.mpr h21)

/-- **The context lift fails for the admission predicate at a lawful admitted state with two
values at one grade of the context** (`Seed.not_cappedLift_context_of_state`). -/
theorem not_hasContextLift_of_state (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {P₀ : Fin (I.attachment g).card → Label.{u}}
    (hP₀ : (I.attachment g).rows.IsLawful P₀) (hP₀A : I.attachAdmits g hd Q (m + 2) P₀)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k)
    (hs₁ : (I.attachment g).toCellScheme.scope a₁ ⊆ ctxCoatom m)
    (hs₂ : (I.attachment g).toCellScheme.scope a₂ ⊆ ctxCoatom m) (h21 : P₀ a₂ < P₀ a₁)
    (h20 : P₀ a₂ ≠ ⊥) (h2v : IsSelfVisible (m + 2) (P₀ a₂)) :
        ¬ I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' := fun h ↦
  not_cappedLift_context_of_state hH hcard hΓ hΓc hd hQ hk2 hΓk hkm hP₀ hP₀A ha₁ ha₂ hs₁ hs₂ h21 h20
    h2v (h k (by omega) hkm)

/-- **The extension over the tower at a positive cap fails for the admission predicate at a
lawful admitted state with two blocks at one grade**: as `Seed.not_towerExtensionPos_of_state`,
for ordinals `o₂`, `o₁` of blocks `blockOf o₂ < blockOf o₁` at two cells of one grade
`2 ≤ k ≤ j`, after the raise of the finite parts to `m + 2` (`Label.finRaise`). -/
theorem not_towerExtensionPos_of_blocks (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j) (hjm : j ≤ m + 1)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    {P₀ : Fin (I.attachment g).card → Label.{u}} (hP₀ : (I.attachment g).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits g hd Q (m + 2) P₀)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k) {o₁ o₂ : Ordinal.{u}} (h₁ : P₀ a₁ = o₁)
    (h₂ : P₀ a₂ = o₂) (hb : blockOf o₂ < blockOf o₁) :
    ¬ TowerExtensionPos I g H Γ (I.attachAdmits g hd Q) B' j := by
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  refine not_towerExtensionPos_of_state hH hcard hΓ hΓc hd hQ hk2 hkj hjm hΓk
    (P₀ := finRaise (m + 2) ∘ P₀)
    (hP₀.map_of_bot_iff hP₀ hgr (isWitness_finRaise (m + 2)) fun _ ↦ finRaise_eq_bot_iff _)
    (attachAdmits_comp hd hQ hP₀A (isWitness_finRaise (m + 2)) (fun _ ↦ finRaise_eq_bot_iff _) _)
    ha₁ ha₂ ?_ ?_ ?_
  · change finRaise (m + 2) (P₀ a₂) < finRaise (m + 2) (P₀ a₁)
    rw [h₁, h₂]; exact finRaise_lt_finRaise hb
  · change finRaise (m + 2) (P₀ a₂) ≠ ⊥
    rw [Ne, finRaise_eq_bot_iff, h₂]; exact WithBot.coe_ne_bot
  · change IsSelfVisible (m + 2) (finRaise (m + 2) (P₀ a₂))
    rw [h₂]; exact isSelfVisible_finRaise _ _

/-! ### Every positive pair at one grade -/

/-- The value `m + 2` of the code set, self-visible at `m + 2`: the positive constant of the
ambient's tie. -/
noncomputable abbrev tieValue (m : ℕ) : Label.{u} :=
  ((Ordinal.omega0 * ((0 : ℕ) : Ordinal.{u}) + ((m + 2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
    Label.{u})

theorem tieValue_ne_bot (m : ℕ) : tieValue.{u} m ≠ ⊥ := WithBot.coe_ne_bot

theorem isSelfVisible_tieValue (m : ℕ) : IsSelfVisible (m + 2) (tieValue.{u} m) :=
  isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) le_rfl

theorem tieValue_le_omegaShift (m : ℕ) {x : Label.{u}} (hx : x ≠ ⊥) :
    tieValue.{u} m ≤ omegaShift x :=
  le_omegaShift hx (by
    rw [Nat.cast_zero, mul_zero, zero_add]; exact Ordinal.natCast_lt_omega0 _)

theorem tieValue_mem_codeSet (C m : ℕ) : tieValue.{u} m ∈ codeSet C (m + 2) :=
  mem_codeSet (Nat.zero_le _) (by omega)

/-- The ambient's tie: the positive constant `m + 2` on the support of a state. -/
theorem posConst_mem_towerCat
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : I.attachAdmits g hd Q (m + 2) P) :
    (posConst (tieValue m) ∘ P) ∈
      (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2) := by
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  have hw := isWitness_posConst (isSelfVisible_tieValue.{u} m)
  have hb (a) : posConst (tieValue m) (P a) = ⊥ ↔ P a = ⊥ := posConst_eq_bot_iff (tieValue_ne_bot m)
  refine Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ hΓc ?_,
    hP.map_of_bot_iff hP hgr hw hb, attachAdmits_comp hd hQ hPA hw hb _⟩
  change posConst (tieValue m) (P a) ∈ _
  unfold posConst
  split_ifs
  · exact mem_insert_self _ _
  · exact tieValue_mem_codeSet _ m

/-- The shifted state agrees with the tie at `m + 2`, capped there. -/
theorem min_omegaShift_tieValue (m : ℕ) (x : Label.{u}) :
    min (omegaShift x) (tieValue m) = min (posConst (tieValue m) x) (tieValue m) := by
  by_cases hx : x = ⊥
  · rw [hx]; rfl
  · rw [min_eq_right (tieValue_le_omegaShift m hx), posConst, ite_eq_right hx, min_self]

/-- No grid point at a grade `k ≤ m + 1` lies at or below the tie except below it. -/
theorem lt_tieValue_of_mem_grid {k : ℕ} (hk : k ≤ m + 1)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥) {x : Label.{u}}
    (hx : x ∈ Scheme.heightSet Γ B' k) (hxv : x ≤ tieValue m) : x < tieValue m := by
  rcases Scheme.mem_heightSet.mp hx with hx | ⟨hxΓ, hxk⟩
  · refine lt_of_le_of_ne hxv ?_
    rcases mem_grid.mp hx with rfl | ⟨b, -, rfl⟩
    · exact (tieValue_ne_bot m).symm
    · exact gridPoint_ne_of_isSelfVisible (by omega) b (isSelfVisible_tieValue m)
  · rw [hΓk x hxΓ hxk]; exact bot_lt_iff_ne_bot.mpr (tieValue_ne_bot m)

/-- **The extension over the tower at a positive cap fails for the admission predicate at every
lawful admitted state with two positive values at one grade**: if `P₀` carries
`⊥ < P₀ a₂ < P₀ a₁` at two cells of one grade `2 ≤ k ≤ j`, the prescription is `P₀` shifted by one
block (`Label.omegaShift`, all positive values above `ω`), the ambient the writing of the positive
constant `m + 2` on the support of `P₀` (`Label.posConst`), which ties `a₁` and `a₂` at `m + 2`,
strictly inside the block `0` of the grid at `k`, and the cap is `m + 2`
(`Seed.not_towerExtensionPos_of_tie`).  No condition on the blocks or the finite parts. -/
theorem not_towerExtensionPos_of_pair (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j) (hjm : j ≤ m + 1)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    {P₀ : Fin (I.attachment g).card → Label.{u}} (hP₀ : (I.attachment g).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits g hd Q (m + 2) P₀)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k) (h20 : P₀ a₂ ≠ ⊥) (h21 : P₀ a₂ < P₀ a₁) :
    ¬ TowerExtensionPos I g H Γ (I.attachAdmits g hd Q) B' j := by
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  have h10 : P₀ a₁ ≠ ⊥ := fun h ↦ absurd (h ▸ h21) (not_lt_bot)
  have hv2 := tieValue_le_omegaShift m h20
  refine not_towerExtensionPos_of_tie (R' := posConst (tieValue m) ∘ P₀) (σ := id)
    (c := tieValue m) (P := omegaShift ∘ P₀) hH hcard hΓ
    (fun k R h ↦ I.attachAdmits_succ g hd Q k R h) hk2 hkj hjm
    (posConst_mem_towerCat hd hQ hΓc hP₀ hP₀A) (IsWitness.id_step j) (fun _ h ↦ h)
    ((isSelfVisible_tieValue m).mono (by omega)) (tieValue_ne_bot m)
    (hP₀.map_of_bot_iff hP₀ hgr (isWitness_omegaShift (m + 2)) fun _ ↦ omegaShift_eq_bot_iff)
    (attachAdmits_comp hd hQ hP₀A (isWitness_omegaShift (m + 2))
      (fun _ ↦ omegaShift_eq_bot_iff) _)
    (fun a _ ↦ min_omegaShift_tieValue m (P₀ a)) ha₁ ha₂ ?_ (omegaShift_strictMono h21)
    (not_le.mpr (hv2.trans_lt (omegaShift_strictMono h21)))
    fun x hx hxv ↦ lt_tieValue_of_mem_grid (by omega) hΓk hx (by
      change x ≤ posConst (tieValue m) (P₀ a₂) at hxv
      rwa [posConst, ite_eq_right h20] at hxv)
  change posConst (tieValue m) (P₀ a₁) ≤ posConst (tieValue m) (P₀ a₂)
  rw [posConst, posConst, ite_eq_right h10, ite_eq_right h20]

/-- **The context lift fails for the admission predicate at every lawful admitted state with two
positive values at one grade of the context**, at that grade: the prescription is the decoded
writing of the code of `P₀` shifted by one block, below the context coatom; the ambient the
writing of the positive constant `m + 2` on the support of `P₀` (`Seed.not_lawful_of_tie`). -/
theorem not_cappedLift_context_of_pair (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {P₀ : Fin (I.attachment g).card → Label.{u}}
    (hP₀ : (I.attachment g).rows.IsLawful P₀) (hP₀A : I.attachAdmits g hd Q (m + 2) P₀)
    {a₁ a₂ : Fin (I.attachment g).card} (ha₁ : (I.attachment g).toCellScheme.grade a₁ = k)
    (ha₂ : (I.attachment g).toCellScheme.grade a₂ = k)
    (hs₁ : (I.attachment g).toCellScheme.scope a₁ ⊆ ctxCoatom m)
    (hs₂ : (I.attachment g).toCellScheme.scope a₂ ⊆ ctxCoatom m) (h20 : P₀ a₂ ≠ ⊥)
    (h21 : P₀ a₂ < P₀ a₁) :
    ¬ (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), k)) (Y := ((univ : Finset (Fin (m + 2))), k))
      ⟨erase_subset _ _, le_rfl⟩ := by
  intro hlift
  have hA : ∀ k R, I.attachAdmits g hd Q (k + 3) R → I.attachAdmits g hd Q (k + 2) R :=
    fun k R h ↦ I.attachAdmits_succ g hd Q k R h
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  have h10 : P₀ a₁ ≠ ⊥ := fun h ↦ absurd (h ▸ h21) (not_lt_bot)
  -- the shifted state and its code
  set P := omegaShift ∘ P₀ with hPdef
  have hPl : (I.attachment g).rows.IsLawful P :=
    hP₀.map_of_bot_iff hP₀ hgr (isWitness_omegaShift (m + 2)) fun _ ↦ omegaShift_eq_bot_iff
  have hPA : I.attachAdmits g hd Q (m + 2) P :=
    attachAdmits_comp hd hQ hP₀A (isWitness_omegaShift (m + 2)) (fun _ ↦ omegaShift_eq_bot_iff) _
  obtain ⟨RP, hRP, σ, hσ, hσb, hσR⟩ := exists_stateCode hd hQ hΓc hPl hPA
  have hRPl : (I.attachment g).rows.IsLawful RP :=
    (Scheme.LadderBaseData.mem_towerCat.mp hRP).2.1
  -- the tie
  have hR' := posConst_mem_towerCat hd hQ hΓc hP₀ hP₀A
  have hR'l : (I.attachment g).rows.IsLawful (posConst (tieValue m) ∘ P₀) :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  set wP := I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' RP with hwP
  set wR := I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B'
    (posConst (tieValue m) ∘ P₀) with hwR
  have hlawP := isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hRP
    (univ.erase (Fin.last (m + 1)), k) (hσ k (by omega)) hσb
  have hlawR := isLawful_replicatedWriting hH hcard hΓ hA hR'
  obtain ⟨q', hq', hq'q, hq'p⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp
    hlift (tieValue m) ((isSelfVisible_tieValue m).mono (by omega)) (fun d ↦ σ (wP d))
    (fun d ↦ wR d) hlawP (hlawR.isLawfulBelow _) fun e ↦ by
      obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx e.2
      change min (wR e.1) (tieValue m) = min (σ (wP e.1)) (tieValue m)
      rw [← ha, hwR, hwP, replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q)
        (B' := B') hcard hR'l a, replicatedWriting_attachEmb (Γ := Γ)
        (A := I.attachAdmits g hd Q) (B' := B') hcard hRPl a, hσR a]
      exact (min_omegaShift_tieValue m (P₀ a)).symm
  have hmem (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k)
      (hs : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom m) :
      I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a ∈
        (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
          (univ.erase (Fin.last (m + 1)), k) :=
    (attachEmb_mem_below_iff a _).mpr ⟨hs, ha.le⟩
  have hval (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a = k)
      (hs : (I.attachment g).toCellScheme.scope a ⊆ ctxCoatom m) (e) (he : e.1 =
        I.attachEmb g H Γ (I.attachAdmits g hd Q) B' a) : q' e = P a := by
    have h := hq'p ⟨_, hmem a ha hs⟩
    rw [show (Set.inclusion _ ⟨_, hmem a ha hs⟩ : (I.replicated g H Γ (I.attachAdmits g hd Q)
      B').toCellScheme.below ((univ : Finset (Fin (m + 2))), k)) = e from Subtype.ext he.symm]
      at h
    rw [h]
    change σ (wP _) = P a
    rw [hwP, replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B') hcard
      hRPl a]
    exact hσR a
  exact not_lawful_of_tie (R' := posConst (tieValue m) ∘ P₀) (σ := id) (c := tieValue m) hcard hA
    hk2 le_rfl hkm hR' ha₁ ha₂
    (by change posConst _ (P₀ a₁) ≤ posConst _ (P₀ a₂); rw [posConst, posConst, ite_eq_right h10,
      ite_eq_right h20])
    (fun x hx hxv ↦ lt_tieValue_of_mem_grid hkm hΓk hx (by
      change x ≤ posConst (tieValue m) (P₀ a₂) at hxv
      rwa [posConst, ite_eq_right h20] at hxv))
    (omegaShift_strictMono h21)
    (not_le.mpr ((tieValue_le_omegaShift m h20).trans_lt (omegaShift_strictMono h21))) hq'
    (hval a₁ ha₁ hs₁) (hval a₂ ha₂ hs₂) hq'q

/-- **The context lift fails for the admission predicate at a lawful context section with two
values at one grade**: for requests calibrated on the class with the labels pair admitted and the
relative lift on the exact class (the hypotheses of the state lift), and values containing the
code set, a lawful section `u'` of the first coatom type carrying `u' x₂ < u' x₁` at two cells of
one grade `2 ≤ k ≤ m + 1`, with `u' x₂ ≠ ⊥` self-visible at `m + 2`, defeats the context lift:
its admitted completion over the attachment (`Seed.exists_admitted_completion_attachment`) is a
state as in `Seed.not_hasContextLift_of_state`. -/
theorem not_cappedLift_context_of_section (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {u' : Fin I.left.card → Label.{u}} (hu' : I.left.rows.IsLawful u') {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {x₁ x₂ : Fin I.left.card} (hx₁ : I.left.toCellScheme.grade x₁ = k)
    (hx₂ : I.left.toCellScheme.grade x₂ = k) (h21 : u' x₂ < u' x₁) (h20 : u' x₂ ≠ ⊥)
    (h2v : IsSelfVisible (m + 2) (u' x₂)) :
        ¬ (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), k)) (Y := ((univ : Finset (Fin (m + 2))), k))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨R, hRl, hRu, hadm⟩ := I.exists_admitted_completion_attachment hte hdp hd hpair hrel hu'
  have hRc (x : Fin I.left.card) : R (I.attachCtxCell g x) = u' x := hRu x
  have hRA : I.attachAdmits g hd Q (m + 2) R :=
    attachAdmits_of_admitsOnClass hd hQ (m + 2) (by
      rw [show (fun x ↦ R (I.attachCtxCell g x)) = u' from funext hRc]
      exact hadm)
  refine not_cappedLift_context_of_state hH hcard hΓ hΓc hd hQ hk2 hΓk hkm hRl hRA
    ((grade_attachCtxCell x₁).trans hx₁) ((grade_attachCtxCell x₂).trans hx₂)
    (scope_attachCtxCell_subset x₁) (scope_attachCtxCell_subset x₂) ?_ ?_ ?_
  · rw [hRc, hRc]; exact h21
  · rw [hRc]; exact h20
  · rw [hRc]; exact h2v

/-- **The context lift fails for the admission predicate at a lawful context section with two
values at one grade** (`Seed.not_cappedLift_context_of_section`). -/
theorem not_hasContextLift_of_section (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {u' : Fin I.left.card → Label.{u}} (hu' : I.left.rows.IsLawful u') {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {x₁ x₂ : Fin I.left.card} (hx₁ : I.left.toCellScheme.grade x₁ = k)
    (hx₂ : I.left.toCellScheme.grade x₂ = k) (h21 : u' x₂ < u' x₁) (h20 : u' x₂ ≠ ⊥)
    (h2v : IsSelfVisible (m + 2) (u' x₂)) :
        ¬ I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' := fun h ↦
  not_cappedLift_context_of_section hH hcard hΓ hΓc hte hdp hd hQ hpair hrel hu' hk2 hΓk hkm hx₁
    hx₂
    h21 h20 h2v (h k (by omega) hkm)

/-- **The context lift fails for the admission predicate at every lawful context section with two
positive values at one grade**, at that grade: for requests calibrated on the class with the
labels pair admitted and the relative lift on the exact class, and values containing the code set,
a lawful section `u'` of the first coatom type with `⊥ < u' x₂ < u' x₁` at two cells of one grade
`2 ≤ k ≤ m + 1`: its admitted completion over the attachment
(`Seed.exists_admitted_completion_attachment`) is a state as in
`Seed.not_cappedLift_context_of_pair`. -/
theorem not_cappedLift_context_of_section_pair (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {u' : Fin I.left.card → Label.{u}} (hu' : I.left.rows.IsLawful u') {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {x₁ x₂ : Fin I.left.card} (hx₁ : I.left.toCellScheme.grade x₁ = k)
    (hx₂ : I.left.toCellScheme.grade x₂ = k) (h20 : u' x₂ ≠ ⊥) (h21 : u' x₂ < u' x₁) :
    ¬ (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), k)) (Y := ((univ : Finset (Fin (m + 2))), k))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨R, hRl, hRu, hadm⟩ := I.exists_admitted_completion_attachment hte hdp hd hpair hrel hu'
  have hRc (x : Fin I.left.card) : R (I.attachCtxCell g x) = u' x := hRu x
  have hRA : I.attachAdmits g hd Q (m + 2) R :=
    attachAdmits_of_admitsOnClass hd hQ (m + 2) (by
      rw [show (fun x ↦ R (I.attachCtxCell g x)) = u' from funext hRc]
      exact hadm)
  refine not_cappedLift_context_of_pair hH hcard hΓ hΓc hd hQ hk2 hΓk hkm hRl hRA
    ((grade_attachCtxCell x₁).trans hx₁) ((grade_attachCtxCell x₂).trans hx₂)
    (scope_attachCtxCell_subset x₁) (scope_attachCtxCell_subset x₂) ?_ ?_
  · rw [hRc]; exact h20
  · rw [hRc, hRc]; exact h21

/-- **The context lift fails for the admission predicate at a lawful context section with two
blocks at one grade**: as `Seed.not_hasContextLift_of_section`, for a lawful section `u'` of the
first coatom type carrying ordinals `o₂`, `o₁` of blocks `blockOf o₂ < blockOf o₁` at two cells of
one grade `2 ≤ k ≤ m + 1`; the raise of the finite parts to `m + 2` (`Label.finRaise`, a witness
bounded by `m + 2`) keeps `u'` lawful and the two values apart, and makes the lower one
self-visible at `m + 2`.  With `u'` the label section of the first coatom type, this is a condition
on its labels alone. -/
theorem not_hasContextLift_of_blocks (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    {u' : Fin I.left.card → Label.{u}} (hu' : I.left.rows.IsLawful u') {k : ℕ} (hk2 : 2 ≤ k)
    (hΓk : ∀ x ∈ Γ, IsSelfVisible k x → x = ⊥)
    (hkm : k ≤ m + 1) {x₁ x₂ : Fin I.left.card} (hx₁ : I.left.toCellScheme.grade x₁ = k)
    (hx₂ : I.left.toCellScheme.grade x₂ = k) {o₁ o₂ : Ordinal.{u}} (h₁ : u' x₁ = o₁)
    (h₂ : u' x₂ = o₂) (hb : blockOf o₂ < blockOf o₁) :
    ¬ I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' := by
  have hu'' : I.left.rows.IsLawful (finRaise (m + 2) ∘ u') :=
    hu'.map_of_bot_iff hu' (fun x ↦ (I.left.grade_le x).trans (Nat.le_succ _))
      (isWitness_finRaise (m + 2)) fun _ ↦ finRaise_eq_bot_iff _
  refine not_hasContextLift_of_section hH hcard hΓ hΓc hte hdp hd hQ hpair hrel hu'' hk2 hΓk hkm
    hx₁
    hx₂ ?_ ?_ ?_
  · change finRaise (m + 2) (u' x₂) < finRaise (m + 2) (u' x₁)
    rw [h₁, h₂]; exact finRaise_lt_finRaise hb
  · change finRaise (m + 2) (u' x₂) ≠ ⊥
    rw [Ne, finRaise_eq_bot_iff, h₂]; exact WithBot.coe_ne_bot
  · change IsSelfVisible (m + 2) (finRaise (m + 2) (u' x₂))
    rw [h₂]; exact isSelfVisible_finRaise _ _

end Seed

end VaughtConjecture

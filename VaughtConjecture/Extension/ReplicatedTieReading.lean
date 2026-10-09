/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftCap
import VaughtConjecture.Extension.ReplicatedServingCell

/-!
# Ties and pins of the ambient against the agreement heights

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap and the context
lift of the replicated scheme).

The layer cells of the replicated scheme at a grade `k ≥ 2` read one another through agreement
heights in the height set `Scheme.heightSet Γ B' k` (the grid at `k` and the values of `Γ`
self-visible at `k`).  A cell `u` at `(univ, k)` whose label exceeds a cap `c` in a lift keeping
the ambient at `c` carries a label at least `c` in the ambient; for the decoded writing of a state
`R'` of the catalogue the ambient there is `σ W`, with `W` the writing of `R'` at `u`, a height
(`Scheme.layerTower_v_mem`), and the state `R` read by `u` agrees with `R'` capped at `W`
(`Seed.exists_reading_of_writing`).

**Pins** (`Seed.not_lawful_of_pin`, `Seed.not_towerExtensionPos_of_pin`).  If every height `x`
at `k` with `c ≤ σ x` lies above `R' a` (the pin), the state of every such `u` equals `R'` at `a`
and is at least that at a cell `a₁` with `R' a ≤ R' a₁`; so no lawful labelling keeping the ambient
at `c` carries `v₁ < v ≤ v₃` at `a₁`, `a` and a cell `a₃` of grade `k` with `v₃` above `c`: the
cell available above `v₃` reads `v ≤ v₁` through its capped decoder.  Hence the extension over the
tower at a positive cap fails at such an ambient and a state reversing the pin.

**Where a pin can sit** (`Seed.not_pin_of_isSelfVisible`, `Seed.not_pin_of_grade`,
`Seed.cap_not_mem_heightSet_of_pin`): the pinned value is not a height, so the pinned cell has
grade below `k`; in particular a tie of two cells of the grade `k` at a value of the catalogue
(the obstruction of the grid alone, refuted at commit `86a30a0` for the seed choice, see
`VaughtConjecture.MainTheorem.ReplicatedTieInstance`) is broken by the height set.  For the ambient
read literally, the cap of a pin is not a height: a pin exploits a cap with no coded
representative in the height set.  The cells that may serve above the cap are selected by the
ambient's own values at the cells of full scope, which are heights
(`Seed.replicatedWriting_castAdd_mem_heightSet`); the lift's decoder at such a cell enters only
through its monotonicity, so no decoder depending on the cap rescues a pin.  A realized pin at the
seed position: `VaughtConjecture.MainTheorem.ReplicatedPinInstance`.

**Witnesses** (`Label`): the raise of the finite parts to `K` (`Label.finRaise`), the shift by
one block (`Label.omegaShift`) and the positive constant (`Label.posConst`), witnesses bounded by
`K`; the code of a label self-visible at `K` stays self-visible at `K`
(`Label.isSelfVisible_blockCompress_squash`).

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
writing up to the writing's value at the cell**: for a cell `f` of the tower at `(univ, k)`,
`2 ≤ k ≤ m + 1`, some lawful state `R` of the catalogue at `k` is read by `f` at the cells of the
attachment of grade at most `k`, the writing of a lawful state `R'` at `f` is a height at `k`
(`Scheme.heightSet`), and `R` agrees with `R'` capped at that value: equal where `R'` lies below
it, at least it where `R'` is. -/
theorem exists_reading_of_writing (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ}
    (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) (f : Fin (𝕋).card)
    (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k))
    {R' : Fin (I.attachment g).card → Label.{u}} (hR' : (I.attachment g).rows.IsLawful R') :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A k,
      (∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
        (𝔼).rowAt (Fin.castAdd _ f) (I.attachEmb g H Γ A B' a) = R a) ∧
      ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f ∈ Scheme.heightSet Γ B' k ∧
      (∀ a, R' a < ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f → R a = R' a) ∧
      ∀ a, ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f ≤ R' a →
        ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f ≤ R a := by
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
  set W := ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f with hW
  have hag (a : Fin (I.attachment g).card) : min (R' a) W = min (R a) W := by
    have e := hagr R' (Fin.castAdd _ a)
    change min ((I.attachmentBase g).stateExt H R' (Fin.castAdd _ a)) _ =
      min ((I.attachmentBase g).stateExt H R (Fin.castAdd _ a)) _ at e
    erw [Scheme.LadderBaseData.stateExt_castAdd hR' hcard,
      Scheme.LadderBaseData.stateExt_castAdd hRl hcard] at e
    exact e
  refine ⟨R, hRC, fun a ha ↦ ?_, ?_, fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · refine (Scheme.rowAt_mirror_castAdd _ _).trans ((hrow (Fin.castAdd _ a) ?_).trans
      (Scheme.LadderBaseData.stateExt_castAdd hRl hcard a))
    change ((I.attachment g).appendFullCellsScheme 1 _).grade (Fin.castAdd _ a) ≤ k - 2 + 2
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    omega
  · have h := Scheme.layerTower_v_mem (B := (I.attachmentBase g).towerBase H)
      (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ Scheme.heightSet Γ B' k)
      (fun _ ↦ Scheme.bot_mem_heightSet _ _ _) (k - 2) R' m (by omega) f hf'
    rwa [hk] at h
  · have e := hag a
    rw [min_eq_left ha.le] at e
    rcases le_total (R a) W with h | h
    · rw [min_eq_left h] at e; exact e.symm
    · rw [min_eq_right h] at e; exact absurd e ha.ne
  · have e := hag a
    rw [min_eq_right ha] at e
    exact min_eq_right_iff.mp e.symm

/-- **A pin of the ambient below every height above the cap defeats every lawful labelling that
reverses it.**  Let the ambient be the writing of a state `R'` of the catalogue read through a map
`σ`, let `a`, `a₁` be attachment cells of grades at most `k` with `R' a ≤ R' a₁`, and let every
height `x` at `k` (`Scheme.heightSet Γ B' k`) with `c ≤ σ x` lie above `R' a` (the **pin**).
Then no labelling `r` lawful below `(univ, j)`, `2 ≤ k ≤ j ≤ m + 1`, with the observation of the
ambient at `c`, carries `v₁ < v ≤ v₃` at `a₁`, `a` and a cell `a₃` of grade `k` with `v₃` above
`c`: a cell at `(univ, k)` available above `v₃` carries a label at least `c` in the ambient, so
the writing's value `W` at it is a height decoded at least `c`, so `R' a < W`; its state `R` is
`R' a` at `a` and at least that at `a₁`; and its capped decoder reads `v ≤ v₁`. -/
theorem not_lawful_of_pin (hcard : (I.attachmentBase g).S.card ≤ H)
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j)
    (hjm : j ≤ m + 1) {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A (m + 2)) {σ : Label.{u} → Label.{u}}
    {c : Label.{u}} {a a₁ a₃ : Fin (I.attachment g).card}
    (ha : (I.attachment g).toCellScheme.grade a ≤ k)
    (ha₁ : (I.attachment g).toCellScheme.grade a₁ ≤ k)
    (ha₃ : (I.attachment g).toCellScheme.grade a₃ = k) (hR'a : R' a ≤ R' a₁)
    (hpin : ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ σ x → R' a < x) {v v₁ v₃ : Label.{u}}
    (hv3 : v ≤ v₃) (hv1 : v₁ < v) (hc3 : ¬ v₃ ≤ c)
    {r : (𝔼).toCellScheme.below 𝕐[j] → Label.{u}}
    (hr : (𝔼).rows.IsLawfulBelow 𝕐[j] r)
    (hra : ∀ d, d.1 = I.attachEmb g H Γ A B' a → r d = v)
    (hra₁ : ∀ d, d.1 = I.attachEmb g H Γ A B' a₁ → r d = v₁)
    (hra₃ : ∀ d, d.1 = I.attachEmb g H Γ A B' a₃ → r d = v₃)
    (hrq : ∀ d, min (r d) c = min (σ (I.replicatedWriting g H Γ A B' R' d)) c) : False := by
  classical
  have hR'l : (I.attachment g).rows.IsLawful R' :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  set w : Fin (𝔼).card → Label.{u} := fun d ↦ if hd : d ∈ (𝔼).toCellScheme.below 𝕐[j] then
    r ⟨d, hd⟩ else ⊥ with hwdef
  have hwr : (fun d : (𝔼).toCellScheme.below 𝕐[j] ↦ w d) = r :=
    funext fun d ↦ dite_eq_left d.2
  have hw : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ w d := by rw [hwr]; exact hr
  have hmemY (b : Fin (I.attachment g).card) (hb : (I.attachment g).toCellScheme.grade b ≤ k) :
      I.attachEmb g H Γ A B' b ∈ (𝔼).toCellScheme.below 𝕐[j] :=
    (attachEmb_mem_below_iff b _).mpr ⟨subset_univ _, hb.trans hkj⟩
  have hwv (b : Fin (I.attachment g).card) (hb : (I.attachment g).toCellScheme.grade b ≤ k)
      {x : Label.{u}} (hx : ∀ d, d.1 = I.attachEmb g H Γ A B' b → r d = x) :
      w (I.attachEmb g H Γ A B' b) = x := by
    change (if hd : _ ∈ (𝔼).toCellScheme.below 𝕐[j] then r ⟨_, hd⟩ else ⊥) = x
    rw [dite_eq_left (hmemY b hb)]
    exact hx ⟨_, hmemY b hb⟩ rfl
  have hw₃ := hwv a₃ ha₃.le hra₃
  -- a cell at `(univ, k)` available above `v₃`
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  obtain ⟨u₀, -, hu₀, -⟩ := exists_cell_of_mem_towerCat (B' := B') hcard hk2 (hkj.trans hjm)
    (Scheme.LadderBaseData.towerCat_mono hA (by omega : k' ≤ m) hR')
  have hu₀Y : u₀ ∈ (𝔼).toCellScheme.below 𝕐[j] := by
    rw [CellScheme.mem_below, hu₀]; exact ⟨subset_rfl, hkj⟩
  obtain ⟨-, -, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨u, huE, hle⟩ := havail (I.attachEmb g H Γ A B' a₃) u₀ hu₀Y
    (by rw [show (𝔼).toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
        exact subset_univ _)
    (by rw [show (𝔼).toCellScheme.grade u₀ = k' + 2 from congrArg Prod.snd hu₀]
        exact (congrArg Prod.snd (gradedIndex_attachEmb a₃)).trans ha₃)
  rw [hu₀] at huE
  rw [hw₃] at hle
  obtain ⟨f, rfl, hf⟩ := exists_eq_castAdd_of_scope u (congrArg Prod.fst huE)
  rw [huE] at hf
  have huY : (Fin.castAdd _ f : Fin (𝔼).card) ∈ (𝔼).toCellScheme.below 𝕐[j] := by
    rw [CellScheme.mem_below, huE]; exact ⟨subset_rfl, hkj⟩
  -- the ambient is at least the cap at the cell
  set W := ((I.attachmentBase g).ladderTower H Γ A B' m).v R' f with hWdef
  have hqu : c ≤ σ W := by
    have e := hrq ⟨_, huY⟩
    have e1 : w (Fin.castAdd _ f) = r ⟨_, huY⟩ := dite_eq_left huY
    rw [← e1, min_eq_right ((not_le.mp hc3).le.trans hle)] at e
    have e2 : I.replicatedWriting g H Γ A B' R' (Fin.castAdd _ f) = W := by
      change ((I.attachmentBase g).ladderTower H Γ A B' m).v R'
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ f)) = W
      rw [Scheme.mirrorOrig_castAdd]
    rw [show (⟨_, huY⟩ : (𝔼).toCellScheme.below 𝕐[j]).1 = Fin.castAdd _ f from rfl, e2] at e
    exact e ▸ min_le_left _ _
  -- the reading of the cell: pinned at `a`, at least that at `a₁`
  obtain ⟨R, -, hrow, hWg, hRlt, hRge⟩ := exists_reading_of_writing (Γ := Γ) (A := A)
    (B' := B') hcard hk2 (hkj.trans hjm) f hf hR'l
  have hpa : R' a < W := hpin W hWg hqu
  have hRa : R a = R' a := hRlt a hpa
  have hRa₁ : R a ≤ R a₁ := by
    rcases lt_or_ge (R' a₁) W with h | h
    · rw [hRa, hRlt a₁ h]; exact hR'a
    · rw [hRa]; exact hpa.le.trans (hRge a₁ h)
  -- the capped decoder at the cell
  obtain ⟨θ, hθ, -, hθr⟩ := Scheme.exists_cappedDecoder_below hw huY (congrArg Prod.snd huE)
  have hb (b : Fin (I.attachment g).card)
      (hgb : (I.attachment g).toCellScheme.grade b ≤ k' + 2) :
      I.attachEmb g H Γ A B' b ∈
        (𝔼).toCellScheme.below ((𝔼).toCellScheme.gradedIndex (Fin.castAdd _ f)) := by
    rw [huE]; exact (attachEmb_mem_below_iff b _).mpr ⟨subset_univ _, hgb⟩
  have h1 := hθr _ (hb a ha)
  have h2 := hθr _ (hb a₁ ha₁)
  rw [hrow a ha, hwv a ha hra, min_eq_left (hv3.trans hle)] at h1
  rw [hrow a₁ ha₁, hwv a₁ ha₁ hra₁, min_eq_left ((hv1.trans_le hv3).le.trans hle)] at h2
  have hmono := hθ.monotone hRa₁
  rw [h1, h2] at hmono
  exact absurd hmono (not_le.mpr hv1)

/-- **A pin of the ambient defeats the extension over the tower at a positive cap**: the ambient
is the decoded writing of `R'` (lawful below `(univ, j)` for a witness bounded by `j` sending only
`⊥` to `⊥`), and a lawful state `P` satisfying `A (m + 2)`, equal to it capped at `c` below the
grade, reverses the pin: `P a₁ < P a ≤ P a₃`, `P a₃` above `c` (`Seed.not_lawful_of_pin`). -/
theorem not_towerExtensionPos_of_pin (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    {j k : ℕ} (hk2 : 2 ≤ k) (hkj : k ≤ j) (hjm : j ≤ m + 1)
    {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A (m + 2))
    {σ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor j) σ)
    (hσb : ∀ x, σ x = ⊥ → x = ⊥) {c : Label.{u}} (hc : IsSelfVisible j c) (hc0 : c ≠ ⊥)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : A (m + 2) P)
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ j → min (P a) c = min (σ (R' a)) c)
    {a a₁ a₃ : Fin (I.attachment g).card} (ha : (I.attachment g).toCellScheme.grade a ≤ k)
    (ha₁ : (I.attachment g).toCellScheme.grade a₁ ≤ k)
    (ha₃ : (I.attachment g).toCellScheme.grade a₃ = k) (hR'a : R' a ≤ R' a₁)
    (hpin : ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ σ x → R' a < x)
    (hv3 : P a ≤ P a₃) (hv1 : P a₁ < P a) (hc3 : ¬ P a₃ ≤ c) :
    ¬ TowerExtensionPos I g H Γ A B' j := by
  intro h
  have hR'l : (I.attachment g).rows.IsLawful R' :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  have hq : (𝔼).rows.IsLawfulBelow 𝕐[j] fun d ↦ σ (I.replicatedWriting g H Γ A B' R' d) :=
    isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hR' 𝕐[j] hσ hσb
  obtain ⟨q', hq', hq'P, hq'q⟩ := h c hc hc0 _ hq P hP hPA (fun d b hb ↦ by
      have hgb : (I.attachment g).toCellScheme.grade b ≤ j :=
        ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') b 𝕐[j]).mp
          (hb ▸ d.2)).2
      change min (P b) c = min (σ (I.replicatedWriting g H Γ A B' R' d.1)) c
      rw [← hb, replicatedWriting_attachEmb hcard hR'l]
      exact hPq b hgb)
    ⟨a₃, ha₃.le.trans hkj, hc3⟩
  exact not_lawful_of_pin hcard hA hk2 hkj hjm hR' ha ha₁ ha₃ hR'a hpin hv3 hv1 hc3 hq'
    (fun d hd ↦ hq'P d a hd.symm) (fun d hd ↦ hq'P d a₁ hd.symm) (fun d hd ↦ hq'P d a₃ hd.symm)
    hq'q

/-! ### Where a pin can sit -/

/-- **A pinned value is not a height**: the pin of `Seed.not_lawful_of_pin` fails at a cell where
the ambient's state, a value of `Γ`, is self-visible at `k` and decoded at least the cap. -/
theorem not_pin_of_isSelfVisible {K k : ℕ} {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A K) {σ : Label.{u} → Label.{u}} {c : Label.{u}}
    {a : Fin (I.attachment g).card} (hv : IsSelfVisible k (R' a)) (hc : c ≤ σ (R' a)) :
    ¬ ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ σ x → R' a < x := fun h ↦
  lt_irrefl _ (h _ (Scheme.mem_heightSet.mpr
    (.inr ⟨(Scheme.LadderBaseData.mem_towerCat.mp hR').1 a, hv⟩)) hc)

/-- **No pin at a cell of the grade**: a cell of grade `k` carries, in a lawful state of the
catalogue, a value self-visible at `k`, a height; so a pinned cell decoded at least the cap has
grade below `k`.  In particular every tie of two cells of the grade `k` (the obstruction of the
grid alone) is broken by the height set. -/
theorem not_pin_of_grade {K k : ℕ} {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A K) {σ : Label.{u} → Label.{u}} {c : Label.{u}}
    {a : Fin (I.attachment g).card} (ha : (I.attachment g).toCellScheme.grade a = k)
    (hc : c ≤ σ (R' a)) :
    ¬ ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ σ x → R' a < x :=
  not_pin_of_isSelfVisible hR' (ha ▸ (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1.orderly a)
    hc

/-- In a pin of `Seed.not_towerExtensionPos_of_pin` the ambient is decoded at least the cap at
the pinned cell: the prescription is at least the cap there. -/
theorem le_of_pin {c : Label.{u}} {p q : Label.{u}} (hpq : min p c = min q c) (hp : c ≤ p) :
    c ≤ q := by
  rw [min_eq_right hp] at hpq
  exact min_eq_right_iff.mp hpq.symm

/-- **The cap of a pin is not a height**: for the ambient read literally (`σ = id`), a pin at a
cell whose ambient value is at least the cap forces the cap out of the height set; a cap of `Γ`
self-visible at `k` (a coded cap) admits no pin. -/
theorem cap_not_mem_heightSet_of_pin {k : ℕ} {R' : Fin (I.attachment g).card → Label.{u}}
    {c : Label.{u}} {a : Fin (I.attachment g).card} (hc : c ≤ R' a)
    (hpin : ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ id x → R' a < x) :
    c ∉ Scheme.heightSet Γ B' k := fun h ↦
  absurd (hpin c h le_rfl) (not_lt.mpr hc)

/-- **The literal ambient at a cell of full scope is a height**: the writing of a lawful state at
a cell of the tower at `(univ, k)`, `2 ≤ k ≤ m + 1`, read in the replicated scheme, lies in the
height set at `k`.  So in `Seed.not_lawful_of_pin` the cells that may serve above the cap are
selected by the ambient's own values, heights, whatever decoder a lift uses at them (the argument
uses only the monotonicity of the lift's capped decoder). -/
theorem replicatedWriting_castAdd_mem_heightSet (hcard : (I.attachmentBase g).S.card ≤ H)
    {k : ℕ} (hk2 : 2 ≤ k) (hkm : k ≤ m + 1) (f : Fin (𝕋).card)
    (hf : (𝕋).toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), k))
    {R' : Fin (I.attachment g).card → Label.{u}} (hR' : (I.attachment g).rows.IsLawful R') :
    I.replicatedWriting g H Γ A B' R' (Fin.castAdd _ f) ∈ Scheme.heightSet Γ B' k := by
  obtain ⟨-, -, -, hW, -, -⟩ := exists_reading_of_writing (Γ := Γ) (A := A) (B' := B') hcard hk2
    hkm f hf hR'
  change ((I.attachmentBase g).ladderTower H Γ A B' m).v R'
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ f)) ∈ _
  rw [Scheme.mirrorOrig_castAdd]
  exact hW

end Seed

end VaughtConjecture

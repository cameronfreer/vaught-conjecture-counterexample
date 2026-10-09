/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedTieReading
import VaughtConjecture.Extension.HeightSetTie

/-!
# The lift at the tie input with agreement heights in the height set

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme with the height sets).

**The tie input** (the input of the refutation over the grid alone, research/port-growth-pos-test
`86a30a0`): a complete lawful admitted state `P₀` of the attachment, the cap `m + 2`
(`Seed.tieValue`, in the code set and self-visible at `m + 2`), the ambient the writing of the
positive constant `m + 2` on the support of `P₀` (`Label.posConst`), and the prescription below the
context coatom the decoded writing of a code of `P₀` shifted by one block (`Label.omegaShift`).
With heights in the grid alone the ambient ties two cells of one grade strictly inside the block
`0` and no lift exists.  With heights in `Scheme.heightSet` the lift exists
(`Seed.exists_lift_of_tie`): it is the writing of the **shifted code** `S` of `P₀`
(`Seed.exists_shiftedCode`: the code of `P₀` in the code set, shifted by one block, so at least `ω`
off `⊥`) read through the **shifted decoder** (`Label.shiftDecode`: the identity below `ω`, the
inverse of the shifted code at or above `ω`).

**The cap agreement, cell class by cell class** (the writings of `S` and of the positive
constant, which agree capped at `m + 2`):

* the cells of the attachment (`Scheme.LadderBaseData.min_stateExt_castAdd_eq`): generic in the
  cap;
* the ladder cells (`Scheme.LadderBaseData.min_stateExt_natAdd_eq`): generic in the cap (any
  `y ≠ ⊥` self-visible at `1`; rank agreement and positive tables);
* the old cells of a layer (`Scheme.min_layerRow_eq`, the old part): generic;
* the cells of a new layer at the grade `K + 2`, among them the cell of
  `Scheme.LadderBaseData.exists_cell_le_v_of_capAgree` at which the refutation over the grid
  stopped (`Scheme.min_layerRow_eq`, the new part): **uses the cap as a height**,
  `m + 2 ∈ Scheme.heightSet Γ B' (K + 2)`;
* the copies (`Seed.replicatedWriting_eq_v_mirrorOrig`): generic, a copy reads its original;
* the decoder (`Label.min_map_eq_min`): generic in a decoder fixing the labels below the cap and
  keeping the labels at least the cap at least the cap; the shifted decoder is such, since the cap
  `m + 2` lies below `ω`.  Here the external cap and its coded representative coincide.

This is the lift at one input.  The context lift at every input of a seed position (every cap,
prescription and ambient) is the extension over the tower at a positive cap
(`Seed.TowerExtensionPos`), not proved here.

## References

Lawful sections and bountifulness are [Kni26, Definitions 2.5.4 and 2.5.14]; agreement heights
are those of the coatom extension construction [Kni26, §4.4].
-/
universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

/-- **The unshift**: `ω + b ↦ b`, the inverse of the shift by one block on the labels at least
`ω`. -/
noncomputable def omegaUnshift : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun a ↦ a - Ordinal.omega0)

theorem omegaUnshift_omegaShift (x : Label.{u}) : omegaUnshift (omegaShift x) = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe a =>
    change (((Ordinal.omega0 + a) - Ordinal.omega0 : Ordinal.{u}) : Label.{u}) = _
    rw [Ordinal.add_sub_cancel]

/-- A label at least `ω` is the shift of its unshift. -/
theorem omegaShift_omegaUnshift {x : Label.{u}} (hx : (Ordinal.omega0 : Label.{u}) ≤ x) :
    omegaShift (omegaUnshift x) = x := by
  induction x using recBotCoeTop with
  | bot => exact absurd hx (not_le.mpr (WithBot.bot_lt_coe _))
  | top => rfl
  | coe a =>
    have ha : Ordinal.omega0 ≤ a := by exact_mod_cast hx
    change ((Ordinal.omega0 + (a - Ordinal.omega0) : Ordinal.{u}) : Label.{u}) = _
    rw [Ordinal.add_sub_cancel_of_le ha]

/-- **A splice at `ω`**: the identity below `ω`, a map `ψ` at or above `ω`. -/
noncomputable def lowSplice (ψ : Label.{u} → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x < (Ordinal.omega0 : Label.{u}) then x else ψ x

/-- **The splice at `ω` of a map commuting with visibility replacement up to `K` at or above `ω`,
monotone there and staying at or above `ω`, is a witness bounded by `K`** sending only `⊥` to
`⊥`. -/
theorem isWitness_lowSplice {ψ : Label.{u} → Label.{u}} {K : ℕ}
    (hψω : ∀ x, (Ordinal.omega0 : Label.{u}) ≤ x → (Ordinal.omega0 : Label.{u}) ≤ ψ x)
    (hψm : ∀ x y, (Ordinal.omega0 : Label.{u}) ≤ x → x ≤ y → ψ x ≤ ψ y)
    (hψv : ∀ x, (Ordinal.omega0 : Label.{u}) ≤ x → ∀ k ≤ K, ∀ i ≤ k,
      ψ (visibilityReplace k i x) = visibilityReplace k i (ψ x)) :
    IsWitness (stepSuppressor K) (lowSplice ψ) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := by unfold lowSplice; rw [ite_eq_left (WithBot.bot_lt_coe _)]
  monotone x y h := by
    unfold lowSplice
    split_ifs with hx hy hy
    · exact h
    · exact (le_of_lt hx).trans (hψω y (not_lt.mp hy))
    · exact absurd (h.trans_lt hy) hx
    · exact hψm x y (not_lt.mp hx) h
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · unfold lowSplice
      by_cases hω : x < (Ordinal.omega0 : Label.{u})
      · rw [ite_eq_left ((visibilityReplace_lt_omega0_iff k i x).mpr hω), ite_eq_left hω]
      · rw [ite_eq_right (mt (visibilityReplace_lt_omega0_iff k i x).mp hω), ite_eq_right hω]
        exact hψv x (not_lt.mp hω) k hk i hi
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hx0 : x = ⊥ := by
        unfold lowSplice at hx
        split_ifs at hx with h
        · exact hx
        · exact absurd (hψω x (not_lt.mp h)) (by rw [hx]; exact not_le.mpr (WithBot.bot_lt_coe _))
      subst hx0
      rfl

theorem lowSplice_eq_bot_iff {ψ : Label.{u} → Label.{u}}
    (hψω : ∀ x, (Ordinal.omega0 : Label.{u}) ≤ x → (Ordinal.omega0 : Label.{u}) ≤ ψ x)
    {x : Label.{u}} : lowSplice ψ x = ⊥ ↔ x = ⊥ := by
  unfold lowSplice
  split_ifs with h
  · rfl
  · constructor
    · intro h0
      exact absurd (hψω x (not_lt.mp h)) (by rw [h0]; exact not_le.mpr (WithBot.bot_lt_coe _))
    · intro h0; subst h0; exact absurd (WithBot.bot_lt_coe _) h

/-- The ordinal identity of the shift of a code: `ω + (ω * r + f) = ω * (r + 1) + f`. -/
theorem omega0_add_omega0_mul_add (r : ℕ) (f : Ordinal.{u}) :
    Ordinal.omega0 + (Ordinal.omega0 * (r : Ordinal.{u}) + f) =
      Ordinal.omega0 * ((r + 1 : ℕ) : Ordinal.{u}) + f := by
  rw [← add_assoc]
  congr 1
  rw [show r + 1 = 1 + r by omega, Nat.cast_add, Nat.cast_one, mul_add, mul_one]

/-- The block count of a set is at most the number of its labels other than the formal top. -/
theorem blockCount_le_card_erase_top (W : Finset Label.{u}) : blockCount W ≤ #(W.erase ⊤) := by
  classical
  refine (card_le_card fun μ hμ ↦ ?_).trans (card_image_le (s := W.erase ⊤)
    (f := recBotCoeTop (motive := fun _ ↦ Ordinal.{u}) 0 blockOf 0))
  obtain ⟨x, hx, hμx⟩ := mem_biUnion.mp hμ
  induction x using recBotCoeTop with
  | bot => exact absurd hμx (Finset.notMem_empty _)
  | top => exact absurd hμx (Finset.notMem_empty _)
  | coe a =>
    exact mem_image.mpr ⟨_, mem_erase.mpr ⟨fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h),
      hx⟩, (mem_singleton.mp hμx).symm⟩

/-- **The shifted code of a set of at most `C` labels takes its values in the code set**: the shift
by one block raises the block of a code by one, and the codes use at most `C - 1` blocks below the
formal top. -/
theorem omegaShift_blockCompress_squash_mem_codeSet {V : Finset Label.{u}} {K C : ℕ}
    (hC : #V ≤ C) {x : Label.{u}} (hx : x ∈ V) :
    omegaShift (blockCompress (V.image (squash V K)) K (squash V K x)) ∈ codeSet C K := by
  classical
  set W := V.image (squash V K) with hW
  have hxW : squash V K x ∈ W := mem_image_of_mem _ hx
  have hWc : #W ≤ C := card_image_le.trans hC
  have hsup : W.sup labelFinNat ≤ K + #V := Finset.sup_le fun y hy ↦ by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    exact labelFinNat_squash_le hz
  induction x using recBotCoeTop with
  | bot => exact mem_insert_self _ _
  | top =>
    have e : squash V K (⊤ : Label.{u}) = ⊤ := rfl
    rw [e] at hxW ⊢
    rw [blockCompress_top]
    have hb : blockCount W + 1 ≤ C := by
      have h1 := blockCount_le_card_erase_top W
      have h2 := card_erase_of_mem hxW
      have h3 : 1 ≤ #W := card_pos.mpr ⟨_, hxW⟩
      omega
    change ((Ordinal.omega0 + (Ordinal.omega0 * (blockCount W : Ordinal.{u}) +
      (compressBound W K : Ordinal.{u})) : Ordinal.{u}) : Label.{u}) ∈ _
    rw [omega0_add_omega0_mul_add]
    refine mem_codeSet hb ?_
    unfold compressBound
    omega
  | coe a =>
    have e : squash V K (a : Label.{u}) =
        ((blockOf a + (squashNat V K (finNat a) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := rfl
    rw [e] at hxW ⊢
    rw [blockCompress_coe hxW, finNat_add_natCast (isSuccPrelimit_blockOf a)]
    change ((Ordinal.omega0 + (Ordinal.omega0 * (blockRank W (blockOf (blockOf a +
      (squashNat V K (finNat a) : Ordinal.{u}))) : Ordinal.{u}) +
      (squashNat V K (finNat a) : Ordinal.{u})) : Ordinal.{u}) : Label.{u}) ∈ _
    rw [omega0_add_omega0_mul_add]
    refine mem_codeSet ?_ ?_
    · have := blockRank_lt (blockOf_mem_blockSet hxW)
      have := blockCount_le W
      omega
    · have := squashNat_finNat_lt (K := K) hx
      omega

/-- A label other than `⊥` is shifted to at least `ω`. -/
theorem omega0_le_omegaShift {x : Label.{u}} (hx : x ≠ ⊥) :
    (Ordinal.omega0 : Label.{u}) ≤ omegaShift x := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe a =>
    change ((Ordinal.omega0 : Ordinal.{u}) : Label.{u}) ≤
      ((Ordinal.omega0 + a : Ordinal.{u}) : Label.{u})
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

theorem monotone_omegaUnshift : Monotone (omegaUnshift.{u}) :=
  Monotone.withBot_map (Monotone.withTop_map fun _ b h ↦
    Ordinal.sub_le.2 (h.trans (Ordinal.le_add_sub b _)))

/-- The unshift commutes with visibility replacement at or above `ω`. -/
theorem omegaUnshift_visibilityReplace {x : Label.{u}} (hx : (Ordinal.omega0 : Label.{u}) ≤ x)
    {k i : ℕ} (hi : i ≤ k) :
    omegaUnshift (visibilityReplace k i x) = visibilityReplace k i (omegaUnshift x) := by
  obtain ⟨x', rfl⟩ : ∃ x', x = omegaShift x' := ⟨_, (omegaShift_omegaUnshift hx).symm⟩
  rw [← (isWitness_omegaShift k).visibilityReplace_comm x' k
    (by rw [stepSuppressor_of_le le_rfl]; exact le_top) i hi, omegaUnshift_omegaShift,
    omegaUnshift_omegaShift]

theorem omegaUnshift_ne_bot {x : Label.{u}} (hx : (Ordinal.omega0 : Label.{u}) ≤ x) :
    omegaUnshift x ≠ ⊥ := fun h ↦ by
  have e := omegaShift_omegaUnshift hx
  rw [h] at e
  exact absurd (e ▸ hx) (not_le.mpr (WithBot.bot_lt_coe _))

/-- **The shifted decoder** of the codes of `V` at `K` (with `W` the squash of `V`): the identity
below `ω`; at or above `ω` the unshift, the block expansion of `W`, the unsquash of `V` and the
shift by one block.  It reads the shifted code of a label of `V` as the shifted label
(`Label.shiftDecode_omegaShift_code`). -/
noncomputable def shiftDecode (V W : Finset Label.{u}) (K : ℕ) : Label.{u} → Label.{u} :=
  lowSplice fun x ↦ omegaShift (unsquash V K (blockExpand W (omegaUnshift x)))

section shiftDecode

variable {V W : Finset Label.{u}} {K : ℕ}

theorem omega0_le_shiftDecode_aux {x : Label.{u}} (hx : (Ordinal.omega0 : Label.{u}) ≤ x) :
    (Ordinal.omega0 : Label.{u}) ≤ omegaShift (unsquash V K (blockExpand W (omegaUnshift x))) :=
  omega0_le_omegaShift (by
    rw [Ne, unsquash_eq_bot_iff, blockExpand_eq_bot_iff]; exact omegaUnshift_ne_bot hx)

/-- **The shifted decoder is a witness** bounded by `K`. -/
theorem isWitness_shiftDecode : IsWitness (stepSuppressor K) (shiftDecode V W K) := by
  refine isWitness_lowSplice (fun x hx ↦ omega0_le_shiftDecode_aux hx)
    (fun x y _ h ↦ (isWitness_omegaShift 0).monotone (isWitness_unsquash.monotone
      ((isWitness_blockExpand K).monotone (monotone_omegaUnshift h))))
    fun x hx k hk i hi ↦ ?_
  have hg : ∀ z : Label.{u}, z ≤ stepSuppressor K k := fun _ ↦ by
    rw [stepSuppressor_of_le hk]; exact le_top
  rw [omegaUnshift_visibilityReplace hx hi,
    (isWitness_blockExpand K).visibilityReplace_comm _ k (hg _) i hi,
    (isWitness_unsquash (V := V) (K := K)).visibilityReplace_comm _ k (hg _) i hi,
    (isWitness_omegaShift K).visibilityReplace_comm _ k (hg _) i hi]

theorem shiftDecode_eq_bot_iff {x : Label.{u}} : shiftDecode V W K x = ⊥ ↔ x = ⊥ :=
  lowSplice_eq_bot_iff fun _ hx ↦ omega0_le_shiftDecode_aux hx

theorem shiftDecode_of_lt {x : Label.{u}} (hx : x < (Ordinal.omega0 : Label.{u})) :
    shiftDecode V W K x = x := by
  unfold shiftDecode lowSplice; rw [ite_eq_left hx]

theorem omega0_le_shiftDecode {x : Label.{u}} (hx : (Ordinal.omega0 : Label.{u}) ≤ x) :
    (Ordinal.omega0 : Label.{u}) ≤ shiftDecode V W K x := by
  unfold shiftDecode lowSplice
  rw [ite_eq_right (not_lt.mpr hx)]
  exact omega0_le_shiftDecode_aux hx

end shiftDecode

/-- **The shifted decoder reads the shifted code of a label of `V` as the shifted label.** -/
theorem shiftDecode_omegaShift_code {V : Finset Label.{u}} {K : ℕ} {x : Label.{u}} (hx : x ∈ V) :
    shiftDecode V (V.image (squash V K)) K
      (omegaShift (blockCompress (V.image (squash V K)) K (squash V K x))) = omegaShift x := by
  classical
  have hxW : squash V K x ∈ V.image (squash V K) := mem_image_of_mem _ hx
  by_cases hc : blockCompress (V.image (squash V K)) K (squash V K x) = ⊥
  · have hx0 : x = ⊥ := squash_eq_bot_iff.mp ((blockCompress_eq_bot_iff hxW K).mp hc)
    rw [hc, hx0]
    exact isWitness_shiftDecode.map_bot
  · unfold shiftDecode lowSplice
    rw [ite_eq_right (not_lt.mpr (omega0_le_omegaShift hc))]
    beta_reduce
    rw [omegaUnshift_omegaShift, blockExpand_blockCompress hxW, unsquash_squash hx]

/-- **A decoder fixing every label below a cap `y` and sending every label at least `y` to a label
at least `y` keeps every label capped at `y`** (generic in the decoder). -/
theorem min_map_eq_min {σ : Label.{u} → Label.{u}} {y : Label.{u}}
    (hlow : ∀ x, x < y → σ x = x) (hhigh : ∀ x, y ≤ x → y ≤ σ x) (x : Label.{u}) :
    min (σ x) y = min x y := by
  rcases lt_or_ge x y with h | h
  · rw [hlow x h]
  · rw [min_eq_right (hhigh x h), min_eq_right h]

end Label

namespace Seed

/-! ### The tie value -/

/-- The value `m + 2` of the code set, self-visible at `m + 2`: the positive constant of the
ambient's tie, and the cap of the tie input. -/
noncomputable abbrev tieValue (m : ℕ) : Label.{u} :=
  ((Ordinal.omega0 * ((0 : ℕ) : Ordinal.{u}) + ((m + 2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
    Label.{u})

theorem tieValue_ne_bot (m : ℕ) : tieValue.{u} m ≠ ⊥ := WithBot.coe_ne_bot

theorem isSelfVisible_tieValue (m : ℕ) : IsSelfVisible (m + 2) (tieValue.{u} m) :=
  isSelfVisible_coe_add (Label.isSuccPrelimit_omega0_mul _) le_rfl

theorem tieValue_lt_omega0 (m : ℕ) : tieValue.{u} m < (Ordinal.omega0 : Label.{u}) := by
  have h : (Ordinal.omega0 * ((0 : ℕ) : Ordinal.{u}) + ((m + 2 : ℕ) : Ordinal.{u})) <
      Ordinal.omega0 := by
    rw [Nat.cast_zero, mul_zero, zero_add]; exact Ordinal.natCast_lt_omega0 _
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)

theorem tieValue_mem_codeSet (C m : ℕ) : tieValue.{u} m ∈ codeSet C (m + 2) :=
  mem_codeSet (Nat.zero_le _) (by omega)

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {B' : ℕ} {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

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

/-! ### The shifted code -/

/-- **The shifted code of a state**: for requests calibrated on the class and values containing
the code set of the attachment at `m + 2`, a complete lawful admitted state `P₀` has a state `S`
of the catalogue at `m + 2` (its code shifted by one block: `⊥` exactly where `P₀` is, at least
`ω` elsewhere) and a decoder `φ` (`Label.shiftDecode`: a witness at every grade up to `m + 2`,
sending only `⊥` to `⊥`, the identity below `ω`, at least `ω` at or above `ω`) reading `S` as
`P₀` shifted by one block. -/
theorem exists_shiftedCode
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {P₀ : Fin (I.attachment g).card → Label.{u}} (hP₀ : (I.attachment g).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits g hd Q (m + 2) P₀) :
    ∃ S ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2),
      (∀ a, S a = ⊥ ↔ P₀ a = ⊥) ∧ (∀ a, S a ≠ ⊥ → (Ordinal.omega0 : Label.{u}) ≤ S a) ∧
      ∃ φ : Label.{u} → Label.{u}, (∀ j ≤ m + 2, IsWitness (stepSuppressor j) φ) ∧
        (∀ x, φ x = ⊥ → x = ⊥) ∧ (∀ x, x < (Ordinal.omega0 : Label.{u}) → φ x = x) ∧
        (∀ x, (Ordinal.omega0 : Label.{u}) ≤ x → (Ordinal.omega0 : Label.{u}) ≤ φ x) ∧
        ∀ a, φ (S a) = omegaShift (P₀ a) := by
  classical
  set V : Finset Label.{u} := univ.image P₀ with hV
  set W : Finset Label.{u} := V.image (squash V (m + 2)) with hW
  have hPV (a : Fin (I.attachment g).card) : P₀ a ∈ V := mem_image_of_mem _ (mem_univ a)
  have hPW (a : Fin (I.attachment g).card) : squash V (m + 2) (P₀ a) ∈ W :=
    mem_image_of_mem _ (hPV a)
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  -- squash, compress, shift
  set S₁ : Fin (I.attachment g).card → Label.{u} := squash V (m + 2) ∘ P₀ with hS₁
  have hS₁l : (I.attachment g).rows.IsLawful S₁ :=
    hP₀.map_of_bot_iff hP₀ hgr isWitness_squash fun a ↦ squash_eq_bot_iff
  have hS₁A : I.attachAdmits g hd Q (m + 2) S₁ :=
    attachAdmits_comp hd hQ hP₀A isWitness_squash (fun a ↦ squash_eq_bot_iff) _
  set S₂ : Fin (I.attachment g).card → Label.{u} := blockCompress W (m + 2) ∘ S₁ with hS₂
  have hb₂ (a) : S₂ a = ⊥ ↔ S₁ a = ⊥ := blockCompress_eq_bot_iff (hPW a) (m + 2)
  have hS₂l : (I.attachment g).rows.IsLawful S₂ :=
    hS₁l.map_of_bot_iff hS₁l hgr (isWitness_blockCompress (m + 2)) hb₂
  have hS₂A : I.attachAdmits g hd Q (m + 2) S₂ :=
    attachAdmits_comp hd hQ hS₁A (isWitness_blockCompress (m + 2)) hb₂ _
  set S : Fin (I.attachment g).card → Label.{u} := omegaShift ∘ S₂ with hS
  have hSl : (I.attachment g).rows.IsLawful S :=
    hS₂l.map_of_bot_iff hS₂l hgr (isWitness_omegaShift (m + 2)) fun _ ↦ omegaShift_eq_bot_iff
  have hSA : I.attachAdmits g hd Q (m + 2) S :=
    attachAdmits_comp hd hQ hS₂A (isWitness_omegaShift (m + 2)) (fun _ ↦ omegaShift_eq_bot_iff) _
  have hVc : #V ≤ (I.attachment g).card := card_image_le.trans (by simp)
  have hSb (a) : S a = ⊥ ↔ P₀ a = ⊥ := by
    change omegaShift (S₂ a) = ⊥ ↔ _
    rw [omegaShift_eq_bot_iff, hb₂]
    exact squash_eq_bot_iff
  refine ⟨S, Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ hΓc
      (omegaShift_blockCompress_squash_mem_codeSet hVc (hPV a)), hSl, hSA⟩, hSb,
    fun a ha ↦ omega0_le_omegaShift fun h ↦ ha (by change omegaShift (S₂ a) = ⊥; rw [h]; rfl),
    shiftDecode V W (m + 2), fun j hj ↦ isWitness_shiftDecode.of_le_stepSuppressor hj,
    fun x hx ↦ shiftDecode_eq_bot_iff.mp hx, fun x hx ↦ shiftDecode_of_lt hx,
    fun x hx ↦ omega0_le_shiftDecode hx, fun a ↦ shiftDecode_omegaShift_code (hPV a)⟩

/-! ### The lift at the tie input -/

/-- **Cell class: the copies** (generic): the writing at a copy is the writing at its original in
the ladder tower. -/
theorem replicatedWriting_eq_v_mirrorOrig {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) →
    Prop} (R : Fin (I.attachment g).card → Label.{u}) (z : Fin (I.replicated g H Γ A B').card) :
    I.replicatedWriting g H Γ A B' R z = ((I.attachmentBase g).ladderTower H Γ A B' m).v R
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) z) := rfl

/-- **The writings on the replicated scheme of two lawful states agreeing capped at a value `y` of
`Γ` agree capped at `y`** at every cell, for `y ≠ ⊥` self-visible at `m + 1`: copies read their
originals (`Seed.replicatedWriting_eq_v_mirrorOrig`, generic); in the ladder tower the cells of
the attachment and the ladder cells are generic in `y`
(`Scheme.LadderBaseData.min_stateExt_castAdd_eq`, `Scheme.LadderBaseData.min_stateExt_natAdd_eq`),
the old cells of a layer carry their writing, and the cells of a new layer at the grade `K + 2`
use `y` as a height there (`Scheme.min_layerRow_eq`, `y ∈ Scheme.heightSet Γ B' (K + 2)`). -/
theorem min_replicatedWriting_eq_of_capAgree
    {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    (hcard : (I.attachmentBase g).S.card ≤ H) {y : Label.{u}} (hyΓ : y ∈ Γ) (hy0 : y ≠ ⊥)
    (hyv : IsSelfVisible (m + 1) y) {R R' : Fin (I.attachment g).card → Label.{u}}
    (hR : (I.attachment g).rows.IsLawful R) (hR' : (I.attachment g).rows.IsLawful R')
    (hag : ∀ a, min (R' a) y = min (R a) y) (z : Fin (I.replicated g H Γ A B').card) :
    min (I.replicatedWriting g H Γ A B' R' z) y = min (I.replicatedWriting g H Γ A B' R z) y := by
  rw [replicatedWriting_eq_v_mirrorOrig, replicatedWriting_eq_v_mirrorOrig]
  exact Scheme.LadderBaseData.min_v_eq_of_capAgree hcard hyΓ hy0 hR hR' hag m hyv _

/-- **The lift at the tie input** (the input of the refutation over the grid alone,
`Seed.not_cappedLift_context_of_pair` at commit `86a30a0`): for a complete lawful admitted state
`P₀`, the cap `m + 2` (`Seed.tieValue`), the ambient the writing of the positive constant `m + 2`
on the support of `P₀`, and the prescription below the context coatom the decoded writing of any
code `(RP, σ)` of `P₀` shifted by one block, the replicated scheme with agreement heights in the
height set has a lift at every grade `k ≤ m + 1`: the writing of the shifted code `S` of `P₀`
(`Seed.exists_shiftedCode`) read through the shifted decoder `φ`.

* **Lawful** below `(univ, k)`: `φ` is a witness bounded by `k` sending only `⊥` to `⊥`.
* **The ambient at the cap**: `S` and the positive constant agree capped at `m + 2` (both `⊥`
  exactly where `P₀` is; elsewhere `S ≥ ω` and the constant is `m + 2`); their writings agree
  capped at `m + 2` (`Seed.min_replicatedWriting_eq_of_capAgree`; the cap `m + 2` lies in the
  code set, so in `Γ`, and is self-visible at `m + 1`: a height at every layer); and `φ` keeps
  every label capped at `m + 2` (`Label.min_map_eq_min`: the identity below `ω`, at least `ω`
  above).
* **The prescription**: below the context coatom every cell is a cell of the attachment, where the
  writing of `S` is `S`, and `φ ∘ S` is `P₀` shifted, which `σ` reads from `RP`. -/
theorem exists_lift_of_tie (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {k : ℕ} (hkm : k ≤ m + 1)
    {P₀ : Fin (I.attachment g).card → Label.{u}} (hP₀ : (I.attachment g).rows.IsLawful P₀)
    (hP₀A : I.attachAdmits g hd Q (m + 2) P₀) {RP : Fin (I.attachment g).card → Label.{u}}
    (hRP : RP ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2))
    {σ : Label.{u} → Label.{u}} (hσR : ∀ a, σ (RP a) = omegaShift (P₀ a)) :
    ∃ q' : (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), k) → Label.{u},
      (I.replicated g H Γ (I.attachAdmits g hd Q) B').rows.IsLawfulBelow
        ((univ : Finset (Fin (m + 2))), k) q' ∧
      (∀ e, min (q' e) (tieValue m) = min (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B'
        (posConst (tieValue m) ∘ P₀) e.1) (tieValue m)) ∧
      ∀ e : (I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
          (univ.erase (Fin.last (m + 1)), k),
        q' (Set.inclusion ((I.replicated g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below_mono
          (show ((univ.erase (Fin.last (m + 1)), k) : Finset (Fin (m + 2)) × ℕ) ≤
            ((univ : Finset (Fin (m + 2))), k) from ⟨erase_subset _ _, le_rfl⟩)) e) =
          σ (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' RP e.1) := by
  have hA : ∀ k R, I.attachAdmits g hd Q (k + 3) R → I.attachAdmits g hd Q (k + 2) R :=
    fun k R h ↦ I.attachAdmits_succ g hd Q k R h
  obtain ⟨S, hS, hSb, hSω, φ, hφ, hφb, hφlow, hφω, hφS⟩ := exists_shiftedCode hd hQ hΓc hP₀ hP₀A
  have hSl : (I.attachment g).rows.IsLawful S := (Scheme.LadderBaseData.mem_towerCat.mp hS).2.1
  have hR' := posConst_mem_towerCat hd hQ hΓc hP₀ hP₀A
  have hR'l : (I.attachment g).rows.IsLawful (posConst (tieValue m) ∘ P₀) :=
    (Scheme.LadderBaseData.mem_towerCat.mp hR').2.1
  have hRPl : (I.attachment g).rows.IsLawful RP := (Scheme.LadderBaseData.mem_towerCat.mp hRP).2.1
  have hyω := tieValue_lt_omega0.{u} m
  -- the shifted code and the tie agree capped at the cap
  have hag (a : Fin (I.attachment g).card) :
      min (S a) (tieValue m) = min ((posConst (tieValue m) ∘ P₀) a) (tieValue m) := by
    by_cases h0 : P₀ a = ⊥
    · change min (S a) _ = min (posConst _ (P₀ a)) _
      rw [(hSb a).mpr h0, h0]; rfl
    · change min (S a) _ = min (posConst _ (P₀ a)) _
      rw [posConst, ite_eq_right h0, min_self,
        min_eq_right (hyω.le.trans (hSω a (mt (hSb a).mp h0)))]
  refine ⟨fun e ↦ φ (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' S e.1),
    isLawfulBelow_map_replicatedWriting hH hcard hΓ hA hS _ (hφ k (by omega)) hφb,
    fun e ↦ ?_, fun e ↦ ?_⟩
  · -- the ambient at the cap
    rw [min_map_eq_min (fun x hx ↦ hφlow x (hx.trans hyω)) (fun x hx ↦ by
      rcases lt_or_ge x (Ordinal.omega0 : Label.{u}) with h | h
      · rw [hφlow x h]; exact hx
      · exact hyω.le.trans (hφω x h)) _]
    exact min_replicatedWriting_eq_of_capAgree hcard (hΓc (tieValue_mem_codeSet _ m))
      (tieValue_ne_bot m) ((isSelfVisible_tieValue m).mono (by omega)) hR'l hSl hag e.1
  · -- the prescription below the context coatom
    obtain ⟨a, ha⟩ := exists_attachEmb_eq_of_mem_below_ctx e.2
    change φ (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' S e.1) =
      σ (I.replicatedWriting g H Γ (I.attachAdmits g hd Q) B' RP e.1)
    rw [← ha, replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B') hcard
      hSl a, replicatedWriting_attachEmb (Γ := Γ) (A := I.attachAdmits g hd Q) (B' := B') hcard
      hRPl a, hφS a, hσR a]

end Seed

end VaughtConjecture

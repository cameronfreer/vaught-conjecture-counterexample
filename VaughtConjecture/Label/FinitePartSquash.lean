/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.BlockCompress

/-!
# Squashing the finite parts above a grade

Roadmap, Layer 3 ((R3) and (R4), the coding of states by the catalogue).

The block compression (`Label.blockCompress`) keeps the finite part of every label, so the values
of a compressed labelling are bounded only by the finite parts of the labelling.  Above a grade `K`
the finite parts are invisible to visibility replacement at the thresholds `k ≤ K`, so they can be
renumbered.

* **Blockwise maps** (`Label.blockwise`): a monotone map `φ` of the finite parts fixing every
  value at most `K` acts on every block; the action is a witness bounded by `K`
  (`Label.isWitness_blockwise`) and sends only `⊥` to `⊥`.
* **The squash** of a finite set `V` of labels at `K` (`Label.squash`) renumbers the finite parts
  at least `K` of the labels of `V` (and `K` itself) as `K, K + 1, …`; the **unsquash**
  (`Label.unsquash`) sends each such number back to its finite part.  Both are blockwise, and the
  unsquash inverts the squash on `V` (`Label.unsquash_squash`).  The finite parts of the squashed
  labels of `V` are at most `K + |V|` (`Label.finNat_squash_lt`).
* **The code set** (`Label.codeSet C K`): `⊥` and the ordinals `ω * i + f` with `i ≤ C` and
  `f < 3 K + C + 3`.  The block compression at `K` of the squash at `K` of a set `V` of at most
  `C` labels takes its values on `V` in the code set (`Label.blockCompress_squash_mem_codeSet`):
  one finite set for all sets of at most `C` labels.

## References

Visibility replacement is [Kni26, Definition 2.2.3]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal Finset

/-! ### Blockwise maps -/

/-- **The blockwise action** of a map of the finite parts: every ordinal keeps its block and its
finite part is mapped by `φ`; `⊥` and the formal top are fixed. -/
noncomputable def blockwise (φ : ℕ → ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map fun a ↦ blockOf a + (φ (finNat a) : Ordinal.{u}))

@[simp] theorem blockwise_bot (φ : ℕ → ℕ) : blockwise φ (⊥ : Label.{u}) = ⊥ := rfl

@[simp] theorem blockwise_top (φ : ℕ → ℕ) : blockwise φ (⊤ : Label.{u}) = ⊤ := rfl

theorem blockwise_coe (φ : ℕ → ℕ) (a : Ordinal.{u}) :
    blockwise φ (a : Label.{u}) = ((blockOf a + (φ (finNat a) : Ordinal.{u}) : Ordinal.{u}) :
      Label.{u}) := rfl

theorem blockwise_eq_bot_iff (φ : ℕ → ℕ) {x : Label.{u}} : blockwise φ x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe a => rw [blockwise_coe]; simp

theorem blockwise_blockwise (φ ψ : ℕ → ℕ) (a : Ordinal.{u}) :
    blockwise ψ (blockwise φ (a : Label.{u})) = blockwise (ψ ∘ φ) (a : Label.{u}) := by
  rw [blockwise_coe, blockwise_coe, blockwise_coe,
    blockOf_add_natCast (isSuccPrelimit_blockOf a), finNat_add_natCast (isSuccPrelimit_blockOf a)]
  rfl

theorem monotone_blockwise {φ : ℕ → ℕ} (hφ : Monotone φ) : Monotone (blockwise.{u} φ) := by
  refine Monotone.withBot_map (Monotone.withTop_map fun a b hab ↦ ?_)
  rcases (blockOf_mono hab).lt_or_eq with hlt | heq
  · exact (add_natCast_lt_of_lt (isSuccPrelimit_blockOf b) hlt _).le.trans le_self_add
  · rw [heq]
    have h := hφ (finNat_le_of_le hab heq)
    gcongr

/-- A blockwise map fixing the finite parts at most `K` commutes with visibility replacement at the
thresholds `k ≤ K`. -/
theorem blockwise_visibilityReplace {φ : ℕ → ℕ} {K : ℕ} (hφ : Monotone φ)
    (hfix : ∀ f ≤ K, φ f = f) (x : Label.{u}) {k i : ℕ} (hk : k ≤ K) (hi : i ≤ k) :
    blockwise φ (visibilityReplace k i x) = visibilityReplace k i (blockwise φ x) := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe a =>
    rw [visibilityReplace_coe, blockwise_coe, blockwise_coe, visibilityReplace_coe,
      visibilityReplace_eq_blockOf, visibilityReplace_eq_blockOf]
    simp only [blockOf_add_natCast (isSuccPrelimit_blockOf a),
      finNat_add_natCast (isSuccPrelimit_blockOf a)]
    have hlt : φ (finNat a) < k ↔ finNat a < k := by
      constructor
      · intro h
        by_contra h'
        push Not at h'
        rcases le_total (finNat a) K with hK | hK
        · rw [hfix _ hK] at h; omega
        · have := hφ hK; rw [hfix K le_rfl] at this; omega
      · intro h
        rw [hfix _ (by omega)]; exact h
    by_cases h : finNat a < k
    · rw [ite_eq_left h, ite_eq_left (hlt.mpr h), hfix i (by omega)]
    · rw [ite_eq_right h, ite_eq_right (mt hlt.mp h)]

/-- **A blockwise map fixing the finite parts at most `K` is a witness bounded by `K`.** -/
theorem isWitness_blockwise {φ : ℕ → ℕ} {K : ℕ} (hφ : Monotone φ) (hfix : ∀ f ≤ K, φ f = f) :
    IsWitness (stepSuppressor K) (blockwise.{u} φ) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := rfl
  monotone := monotone_blockwise hφ
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · exact blockwise_visibilityReplace hφ hfix x hk hi
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff, blockwise_eq_bot_iff] at hx
      subst hx
      rfl

/-! ### The squash and the unsquash -/

variable (V : Finset Label.{u}) (K : ℕ)

/-- The finite parts of the ordinal labels of `V`. -/
noncomputable def finParts : Finset ℕ :=
  V.biUnion fun x ↦ recBotCoeTop (motive := fun _ ↦ Finset ℕ) ∅ (fun a ↦ {finNat a}) ∅ x

theorem finNat_mem_finParts {a : Ordinal.{u}} (ha : (a : Label.{u}) ∈ V) :
    finNat a ∈ finParts V :=
  mem_biUnion.mpr ⟨_, ha, mem_singleton_self _⟩

theorem card_finParts_le : #(finParts V) ≤ #V := by
  refine (card_le_card fun f hf ↦ ?_).trans (card_image_le (s := V) (f := labelFinNat))
  obtain ⟨x, hx, hfx⟩ := mem_biUnion.mp hf
  induction x using recBotCoeTop with
  | bot => exact absurd hfx (Finset.notMem_empty _)
  | top => exact absurd hfx (Finset.notMem_empty _)
  | coe a => exact mem_image.mpr ⟨_, hx, (mem_singleton.mp hfx).symm⟩

/-- The renumbered finite parts: `K` and the finite parts at least `K` of the labels of `V`. -/
noncomputable def highParts : Finset ℕ := insert K ((finParts V).filter (K ≤ ·))

theorem K_mem_highParts : K ∈ highParts V K := mem_insert_self _ _

theorem le_of_mem_highParts {y : ℕ} (hy : y ∈ highParts V K) : K ≤ y := by
  rcases mem_insert.mp hy with rfl | hy
  · exact le_rfl
  · exact (mem_filter.mp hy).2

theorem card_highParts_le : #(highParts V K) ≤ #V + 1 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ ((card_filter_le _ _).trans (card_finParts_le V)))

/-- **The squash of the finite parts**: a finite part below `K` is kept, one at least `K` goes to
`K` plus the number of renumbered parts below it. -/
noncomputable def squashNat (f : ℕ) : ℕ :=
  if f < K then f else K + #((highParts V K).filter (· < f))

variable {V K}

theorem squashNat_of_lt {f : ℕ} (h : f < K) : squashNat V K f = f := ite_eq_left h

theorem squashNat_of_le {f : ℕ} (h : K ≤ f) :
    squashNat V K f = K + #((highParts V K).filter (· < f)) := ite_eq_right (not_lt.mpr h)

theorem squashNat_fix {f : ℕ} (hf : f ≤ K) : squashNat V K f = f := by
  rcases hf.lt_or_eq with h | rfl
  · exact squashNat_of_lt h
  · rw [squashNat_of_le le_rfl, filter_false_of_mem fun y hy ↦ not_lt.mpr
      (le_of_mem_highParts V _ hy), card_empty, add_zero]

theorem monotone_squashNat : Monotone (squashNat V K) := by
  intro f f' h
  rcases lt_or_ge f K with hf | hf
  · rw [squashNat_of_lt hf]
    rcases lt_or_ge f' K with hf' | hf'
    · rw [squashNat_of_lt hf']; exact h
    · rw [squashNat_of_le hf']; omega
  · rw [squashNat_of_le hf, squashNat_of_le (hf.trans h)]
    exact Nat.add_le_add_left (card_le_card fun y hy ↦ mem_filter.mpr
      ⟨(mem_filter.mp hy).1, lt_of_lt_of_le (mem_filter.mp hy).2 h⟩) _

theorem squashNat_lt_squashNat {y f : ℕ} (hy : y ∈ highParts V K) (hf : f ∈ highParts V K)
    (h : y < f) : squashNat V K y < squashNat V K f := by
  rw [squashNat_of_le (le_of_mem_highParts V K hy), squashNat_of_le (le_of_mem_highParts V K hf)]
  refine Nat.add_lt_add_left (card_lt_card ⟨fun z hz ↦ mem_filter.mpr
    ⟨(mem_filter.mp hz).1, (mem_filter.mp hz).2.trans h⟩, fun hsub ↦ ?_⟩) _
  have := (mem_filter.mp (hsub (mem_filter.mpr ⟨hy, h⟩))).2
  exact lt_irrefl _ this

theorem squashNat_lt {f : ℕ} (hf : f ∈ highParts V K) : squashNat V K f < K + #V + 1 := by
  rw [squashNat_of_le (le_of_mem_highParts V K hf)]
  have h1 : #((highParts V K).filter (· < f)) < #(highParts V K) :=
    card_lt_card ⟨filter_subset _ _, fun hsub ↦ lt_irrefl f (mem_filter.mp (hsub hf)).2⟩
  have := card_highParts_le V K
  omega

variable (V K) in
/-- **The unsquash of the finite parts**: below `K` the identity; at least `K`, the largest
renumbered part whose squash is at most the value. -/
noncomputable def unsquashNat (g : ℕ) : ℕ :=
  if h : g < K then g else
    ((highParts V K).filter fun y ↦ squashNat V K y ≤ g).max'
      ⟨K, mem_filter.mpr ⟨K_mem_highParts V K, by rw [squashNat_fix le_rfl]; omega⟩⟩

theorem unsquashNat_of_lt {g : ℕ} (h : g < K) : unsquashNat V K g = g := dite_eq_left h

theorem unsquashNat_of_le {g : ℕ} (h : K ≤ g) :
    unsquashNat V K g = ((highParts V K).filter fun y ↦ squashNat V K y ≤ g).max'
      ⟨K, mem_filter.mpr ⟨K_mem_highParts V K, by rw [squashNat_fix le_rfl]; exact h⟩⟩ :=
  dite_eq_right (not_lt.mpr h)

theorem unsquashNat_squashNat {f : ℕ} (hf : f ∈ highParts V K) :
    unsquashNat V K (squashNat V K f) = f := by
  have hK := le_of_mem_highParts V K hf
  have hsK : K ≤ squashNat V K f := by rw [squashNat_of_le hK]; omega
  rw [unsquashNat_of_le hsK]
  refine le_antisymm (Finset.max'_le _ _ _ fun y hy ↦ ?_)
    (Finset.le_max' ((highParts V K).filter fun y ↦ squashNat V K y ≤ squashNat V K f) f
      (mem_filter.mpr ⟨hf, le_rfl⟩))
  obtain ⟨hyH, hyle⟩ := mem_filter.mp hy
  by_contra hlt
  exact absurd hyle (not_le.mpr (squashNat_lt_squashNat hf hyH (not_le.mp hlt)))

theorem unsquashNat_fix {g : ℕ} (hg : g ≤ K) : unsquashNat V K g = g := by
  rcases hg.lt_or_eq with h | rfl
  · exact unsquashNat_of_lt h
  · have h := unsquashNat_squashNat (K_mem_highParts V g)
    rwa [squashNat_fix le_rfl] at h

theorem monotone_unsquashNat : Monotone (unsquashNat V K) := by
  intro g g' h
  rcases lt_or_ge g K with hg | hg
  · rw [unsquashNat_of_lt hg]
    rcases lt_or_ge g' K with hg' | hg'
    · rw [unsquashNat_of_lt hg']; exact h
    · rw [unsquashNat_of_le hg']
      exact hg.le.trans (le_of_mem_highParts V K (mem_filter.mp (Finset.max'_mem _ _)).1)
  · rw [unsquashNat_of_le hg, unsquashNat_of_le (hg.trans h)]
    exact Finset.max'_le _ _ _ fun y hy ↦ Finset.le_max'
      ((highParts V K).filter fun y ↦ squashNat V K y ≤ g') y
      (mem_filter.mpr ⟨(mem_filter.mp hy).1, (mem_filter.mp hy).2.trans h⟩)

/-- The finite parts of the ordinal labels of `V` are kept or renumbered. -/
theorem unsquashNat_squashNat_of_mem {a : Ordinal.{u}} (ha : (a : Label.{u}) ∈ V) :
    unsquashNat V K (squashNat V K (finNat a)) = finNat a := by
  rcases lt_or_ge (finNat a) K with h | h
  · rw [squashNat_of_lt h, unsquashNat_of_lt h]
  · exact unsquashNat_squashNat (mem_insert_of_mem (mem_filter.mpr ⟨finNat_mem_finParts V ha, h⟩))

theorem squashNat_finNat_lt {a : Ordinal.{u}} (ha : (a : Label.{u}) ∈ V) :
    squashNat V K (finNat a) < K + #V + 1 := by
  rcases lt_or_ge (finNat a) K with h | h
  · rw [squashNat_of_lt h]; omega
  · exact squashNat_lt (mem_insert_of_mem (mem_filter.mpr ⟨finNat_mem_finParts V ha, h⟩))

variable (V K) in
/-- **The squash** of `V` at `K`. -/
noncomputable def squash : Label.{u} → Label.{u} := blockwise (squashNat V K)

variable (V K) in
/-- **The unsquash** of `V` at `K`. -/
noncomputable def unsquash : Label.{u} → Label.{u} := blockwise (unsquashNat V K)

theorem isWitness_squash : IsWitness (stepSuppressor K) (squash.{u} V K) :=
  isWitness_blockwise monotone_squashNat fun _ hf ↦ squashNat_fix hf

theorem isWitness_unsquash : IsWitness (stepSuppressor K) (unsquash.{u} V K) :=
  isWitness_blockwise monotone_unsquashNat fun _ hf ↦ unsquashNat_fix hf

theorem squash_eq_bot_iff {x : Label.{u}} : squash V K x = ⊥ ↔ x = ⊥ := blockwise_eq_bot_iff _

theorem unsquash_eq_bot_iff {x : Label.{u}} : unsquash V K x = ⊥ ↔ x = ⊥ :=
  blockwise_eq_bot_iff _

/-- **The unsquash inverts the squash on `V`.** -/
theorem unsquash_squash {x : Label.{u}} (hx : x ∈ V) : unsquash V K (squash V K x) = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe a =>
    rw [squash, unsquash, blockwise_blockwise, blockwise_coe, Function.comp_apply,
      unsquashNat_squashNat_of_mem hx, blockOf_add_finNat]

/-! ### The code set -/

/-- **The code set**: `⊥` and the ordinals `ω * i + f` with `i ≤ C` and `f < 3 K + C + 3`. -/
noncomputable def codeSet (C K : ℕ) : Finset Label.{u} :=
  insert ⊥ ((range (C + 1) ×ˢ range (3 * K + C + 3)).image fun p ↦
    (((ω * (p.1 : Ordinal.{u}) + (p.2 : Ordinal.{u}) : Ordinal.{u})) : Label.{u}))

theorem mem_codeSet {C K i f : ℕ} (hi : i ≤ C) (hf : f < 3 * K + C + 3) :
    (((ω * (i : Ordinal.{u}) + (f : Ordinal.{u}) : Ordinal.{u})) : Label.{u}) ∈ codeSet C K :=
  mem_insert_of_mem (mem_image.mpr ⟨(i, f), mem_product.mpr ⟨mem_range.mpr (by omega),
    mem_range.mpr hf⟩, rfl⟩)

/-- The block count of a set is at most its size. -/
theorem blockCount_le (W : Finset Label.{u}) : blockCount W ≤ #W := by
  refine (card_le_card fun μ hμ ↦ ?_).trans (card_image_le (s := W)
    (f := recBotCoeTop (motive := fun _ ↦ Ordinal.{u}) 0 blockOf 0))
  obtain ⟨x, hx, hμx⟩ := mem_biUnion.mp hμ
  induction x using recBotCoeTop with
  | bot => exact absurd hμx (Finset.notMem_empty _)
  | top => exact absurd hμx (Finset.notMem_empty _)
  | coe a => exact mem_image.mpr ⟨_, hx, (mem_singleton.mp hμx).symm⟩

theorem labelFinNat_squash_le {x : Label.{u}} (hx : x ∈ V) :
    labelFinNat (squash V K x) ≤ K + #V := by
  induction x using recBotCoeTop with
  | bot => exact Nat.zero_le _
  | top => exact Nat.zero_le _
  | coe a =>
    change labelFinNat (blockwise (squashNat V K) (a : Label.{u})) ≤ _
    rw [blockwise_coe, labelFinNat_coe, finNat_add_natCast (isSuccPrelimit_blockOf a)]
    have := squashNat_finNat_lt (K := K) hx
    omega

/-- **The compressed squash of a set of at most `C` labels takes its values in the code set.** -/
theorem blockCompress_squash_mem_codeSet {C : ℕ} (hC : #V ≤ C) {x : Label.{u}} (hx : x ∈ V) :
    blockCompress (V.image (squash V K)) K (squash V K x) ∈ codeSet C K := by
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
    refine mem_codeSet ((blockCount_le W).trans hWc) ?_
    unfold compressBound
    omega
  | coe a =>
    have e : squash V K (a : Label.{u}) =
        ((blockOf a + (squashNat V K (finNat a) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := rfl
    rw [e] at hxW ⊢
    rw [blockCompress_coe hxW, finNat_add_natCast (isSuccPrelimit_blockOf a)]
    refine mem_codeSet (((blockRank_lt (blockOf_mem_blockSet hxW)).le.trans
      (blockCount_le W)).trans hWc) ?_
    have := squashNat_finNat_lt (K := K) hx
    omega

/-- The code set lies below `ω ^ 2`. -/
theorem lt_omega0_sq_of_mem_codeSet {C K : ℕ} {x : Label.{u}} (hx : x ∈ codeSet C K) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_insert.mp hx with rfl | hx
  · exact WithBot.bot_lt_coe _
  obtain ⟨⟨i, f⟩, -, rfl⟩ := mem_image.mp hx
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, sq]
  have h1 : ω * (i : Ordinal.{u}) + f < ω * ((i + 1 : ℕ) : Ordinal.{u}) := by
    rw [Nat.cast_succ, mul_add_one]
    exact add_lt_add_right (natCast_lt_omega0 _) _
  exact h1.trans ((mul_lt_mul_iff_right₀ omega0_pos).mpr (natCast_lt_omega0 _))

end VaughtConjecture.Label

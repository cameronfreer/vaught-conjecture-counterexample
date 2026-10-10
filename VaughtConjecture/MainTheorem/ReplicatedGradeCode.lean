/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeCut
import VaughtConjecture.Extension.ReplicatedRendering

/-!
# Codes per grade above a reachable cut

Roadmap, Layer 3 ((R3) and (R4), the context lift at an arbitrary grade `2 ≤ k ≤ m + 1`, the top
grade included), the values per grade proposed in place of the single set of values of the seed.

**The values at the grade `k`** are the code grid `Label.codeGrid k B` (`⊥` and the points
`ω * b + f`, `b ≤ B`, `f ≤ k`), with the bound `B = 2 * #F + 2` fixed from the seed (`F` the cells
of the attachment).  Unlike `Seed.seedValues`, it is not a fixed alphabet from which codes are
taken: a state is coded by its orbit code (`Label.orbitCode`), whose blocks are the key ranks of
its own values.

* **The cut at the grade `k`** (`Label.mem_grid_of_mem_codeGrid`): a value of the code grid at `k`
  self-visible at `k` is a point of the grid at `k` and short at `k` (finite part exactly `k`).
  A catalogue at `k` with values in the code grid at `k` therefore has its reachable cuts in the
  grid at `k`, short at `k` (`Seed.reachableCut_mem_grid`).  Such catalogues are not nested in the
  grade (the code grid grows with it), while the lawfulness of the current tower asks the
  catalogue to decrease (`hA`); the cut lemma does not use lawfulness.
* **Fresh codes above the cut** (`Label.exists_freshCode_above_cut`): for an orbit-canonical
  anchor `a` and a cut `h` self-visible and short at `k`, every labelling `w` agreeing with `a`
  capped at `h` has its orbit code in the code grid, orbit-canonical, agreeing with `a` capped at
  `h` (`Label.min_orbitCode_eq`), at least `h` where `w` is, read back literally by the orbit
  decoder, a witness bounded by `k` (`Label.orbitDecoder_orbitCode`).
* **Strictly above for the values not self-visible** (`Label.lt_freshCode_of_not_isSelfVisible`):
  a value of `w` at least `h` and not self-visible at `k` has its code strictly above `h`.  This is
  the reverse of `Seed.not_exists_code_above_top` for the single set of values, where no value
  above the top cut is read as a label not self-visible at `k`.  The orbit code needs no room in a
  fixed alphabet: it uses the blocks at most `2 * #F` (`Label.orbitCode_lt_omega0_mul`), and the
  bound `2 * #F + 2` leaves two blocks above every code.
* **The rendering with the per-grade values** (`Seed.decoder_preserves_capAgreement_at_grade`):
  the replicated scheme with the values `codeGrid (m + 1) B` and the block bound `B + 1` of its
  heights (a value of the current definitions, no new tower) renders two lawful states agreeing
  capped at a cut `h` of the code grid at `k` through two decoders agreeing capped at the cap below
  `h` and reaching it at `h` with capped agreement at every cell of grade at most `k`: attachment,
  ladder, layers with their heights, copies (`Seed.capCompatibleRendering`, the cut a value of the
  code grid self-visible at `k`, hence a height at every grade of the layers up to `k`).

What is not compiled here: the decoder itself, equal to the ambient's decoder capped below the cut
and reading the fresh codes as the prescription above it.  A witness bounded by `k` agreeing below
`h = ω * b + k` with a decoder reaching the cap there is forced at `h` by visibility replacement
(`visibilityReplace k k` sends the strip below `h` to `h`); this is the alignment of the aligned
encoding, not proved here.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9]; agreement heights
are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

variable {k : ℕ}

/-- **A cut of the code grid at `k` is a grid point, short at `k`.** -/
theorem mem_grid_of_mem_codeGrid {B : ℕ} {x : Label.{u}} (hx : x ∈ codeGrid k B)
    (hv : IsSelfVisible k x) : x ∈ grid k B ∧ IsShort k x := by
  refine ⟨?_, isShort_of_mem_codeGrid hx⟩
  rcases mem_codeGrid.mp hx with rfl | ⟨b, hb, f, hf, rfl⟩
  · exact bot_mem_grid k B
  · have hkf : k ≤ f := (isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul _)).mp hv
    obtain rfl : f = k := le_antisymm hf hkf
    exact gridPoint_mem_grid hb

/-- The code grid grows with the grade. -/
theorem codeGrid_mono_grade {B k K : ℕ} (hkK : k ≤ K) : codeGrid.{u} k B ⊆ codeGrid K B :=
  fun x hx ↦ by
    rcases mem_codeGrid.mp hx with rfl | ⟨b, hb, f, hf, rfl⟩
    · exact mem_insert_self _ _
    · exact mem_codeGrid.mpr (.inr ⟨b, hb, f, hf.trans hkK, rfl⟩)

variable {ι : Type*} [Fintype ι]

/-- **Fresh codes above a cut**: for an orbit-canonical anchor `a` and a cut `h` self-visible and
short at `k`, other than `⊥`, a labelling `w` agreeing with `a` capped at `h` has an orbit code
`P` in the code grid of every bound `B ≥ 2 * #ι`, orbit-canonical, agreeing with `a` capped at
`h`, equal to `w` below `h`, at least `h` where `w` is, and read literally as `w` by the orbit
decoder, a witness bounded by `k`. -/
theorem exists_freshCode_above_cut {B : ℕ} (hB : 2 * Fintype.card ι ≤ B) {a w : ι → Label.{u}}
    (ha : orbitCode k a = a) {h : Label.{u}} (hh : IsSelfVisible k h) (hs : IsShort k h)
    (h0 : h ≠ ⊥) (hag : ∀ d, min (w d) h = min (a d) h) :
    (∀ d, orbitCode k w d ∈ codeGrid k B) ∧ orbitCode k (orbitCode k w) = orbitCode k w ∧
      (∀ d, min (orbitCode k w d) h = min (a d) h) ∧
      (∀ d, w d < h → orbitCode k w d = w d) ∧ (∀ d, h ≤ w d → h ≤ orbitCode k w d) ∧
      IsWitness (stepSuppressor k) (orbitMap k w) ∧
      IsWitness (stepSuppressor k) (orbitDecoder k w h) ∧
      ∀ d, orbitDecoder k w h (orbitCode k w d) = w d := by
  have hP (d : ι) : min (orbitCode k w d) h = min (a d) h := min_orbitCode_eq hh hs ha hag d
  have hPw (d : ι) : min (orbitCode k w d) h = min (w d) h := (hP d).trans (hag d).symm
  refine ⟨fun d ↦ orbitMap_mem_codeGrid hB _, orbitCode_orbitCode, hP, fun d hd ↦ ?_,
    fun d hd ↦ ?_, isWitness_orbitMap k w, isWitness_orbitDecoder hh h0,
    orbitDecoder_orbitCode hPw⟩
  · have e := hPw d
    rw [min_eq_left hd.le] at e
    rcases le_total (orbitCode k w d) h with h' | h'
    · rwa [min_eq_left h'] at e
    · rw [min_eq_right h'] at e; exact absurd e.symm hd.ne
  · have e := hPw d
    rw [min_eq_right hd] at e
    exact e ▸ min_le_left _ _

/-- **A value not self-visible at `k` above the cut has its code strictly above the cut**: the
code at the cut itself is self-visible at `k`, and the orbit decoder, a witness bounded by `k`,
would read it as a label self-visible at `k` (`Label.isSelfVisible_witness`). -/
theorem lt_freshCode_of_not_isSelfVisible {a w : ι → Label.{u}} (ha : orbitCode k a = a)
    {h : Label.{u}} (hh : IsSelfVisible k h) (hs : IsShort k h) (h0 : h ≠ ⊥)
    (hag : ∀ d, min (w d) h = min (a d) h) {d : ι} (hd : h ≤ w d)
    (hv : ¬ IsSelfVisible k (w d)) : h < orbitCode k w d := by
  obtain ⟨-, -, -, -, hge, -, hθ, hread⟩ := exists_freshCode_above_cut (B := 2 * Fintype.card ι)
    le_rfl ha hh hs h0 hag
  refine lt_of_le_of_ne (hge d hd) fun he ↦ hv ?_
  rw [← hread d, ← he]
  exact isSelfVisible_witness hθ hh

/-- **The orbit codes use the blocks at most `2 * #ι`**: they lie below `ω * (2 * #ι + 1)`. -/
theorem orbitCode_lt_omega0_mul (w : ι → Label.{u}) (d : ι) :
    orbitCode k w d <
      (((Ordinal.omega0 * ((2 * Fintype.card ι + 1 : ℕ) : Ordinal.{u})) : Ordinal.{u}) :
        Label.{u}) := by
  refine (le_gridPoint_of_mem_codeGrid (orbitMap_mem_codeGrid le_rfl (w d))).trans_lt ?_
  rw [gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe, Nat.cast_succ, mul_add_one]
  exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 k)

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}

/-- **A reachable cut at the grade `k` of a catalogue with values in the code grid at `k` is a
point of the grid at `k`, short at `k`** (`Seed.reachableCut_mem`,
`Label.mem_grid_of_mem_codeGrid`).  The predicate `A` carries the values per grade; the cut is
fixed from the seed through `B`. -/
theorem reachableCut_mem_grid {B : ℕ} {Γ : Finset Label.{u}}
    {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
    (hcard : (I.attachmentBase g).S.card ≤ H) {k : ℕ} (hk2 : 2 ≤ k) (hkm : k ≤ m + 1)
    (hAk : ∀ R, A k R → ∀ a, R a ∈ codeGrid k B) {x : Label.{u}}
    (hx : I.ReachableCut g H Γ A B' k x) : x ∈ grid k B ∧ IsShort k x := by
  obtain ⟨f, hf, d, hd, rfl, hv⟩ := hx
  obtain ⟨R, hR, hrow, -⟩ := exists_reading_of_writing (Γh := Γ) hcard hk2 hkm f hf
    (CellScheme.Rows.isLawful_const_bot (R := (I.attachment g).rows))
  have hRB := hAk R (Scheme.LadderBaseData.mem_towerCat.mp hR).2.2 d
  rw [← hrow d hd] at hRB
  exact mem_grid_of_mem_codeGrid hRB hv

/-- **The rendering with the values per grade**: in the replicated scheme with the values
`codeGrid (m + 1) B` and the block bound `B + 1` of its heights, two lawful states agreeing capped
at a cut `h` of the code grid at `k` self-visible at `k` (a fresh code's cut,
`Label.exists_freshCode_above_cut`), decoded by monotone maps agreeing capped at the cap `c` below
`h` and reaching `c` at `h`, agree capped at `c` at every cell of grade at most `k`
(`Seed.capCompatibleRendering`). -/
theorem decoder_preserves_capAgreement_at_grade {B : ℕ}
    {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    (hcard : (I.attachmentBase g).S.card ≤ H) {R R' : Fin (I.attachment g).card → Label.{u}}
    (hR : (I.attachment g).rows.IsLawful R) (hR' : (I.attachment g).rows.IsLawful R') {k : ℕ}
    (hk1 : 1 ≤ k) (hkm : k ≤ m + 1) {h : Label.{u}} (hhB : h ∈ codeGrid k B) (h0 : h ≠ ⊥)
    (hh : IsSelfVisible k h) (hag : ∀ a, min (R' a) h = min (R a) h)
    {σ σ' : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ' : Monotone σ') {c : Label.{u}}
    (hc : c ≤ σ h) (hc' : c ≤ σ' h) (hcut : ∀ v < h, min (σ v) c = min (σ' v) c)
    (z : Fin (I.replicated g H (codeGrid (m + 1) B) A (B + 1)).card)
    (hz : (I.replicated g H (codeGrid (m + 1) B) A (B + 1)).toCellScheme.grade z ≤ k) :
    min (σ (I.replicatedWriting g H (codeGrid (m + 1) B) A (B + 1) R z)) c =
      min (σ' (I.replicatedWriting g H (codeGrid (m + 1) B) A (B + 1) R' z)) c :=
  capCompatibleRendering hcard hR hR' hk1 hkm (codeGrid_mono_grade hkm hhB) h0 hh hag hσ hσ'
    hc hc' hcut z hz

end Seed

namespace TieInstance

open SeparationObstruction

/-- **The prescription above the cut gets a fresh code** (the test at the grade `2`, on the context
cells, `o` the cell `3`, `y` the cell `0`): the anchor is the orbit code at `2` of the two-level
state of `sep` (its value at `o` the
cut `h`, self-visible and short at `2`); the labelling `w` keeps the anchor below `h` and is the
larger of `h` and `TieInstance.topSection C` elsewhere.  Its orbit code lies in the code grid of
bound `2 * 5`, agrees with the anchor capped at `h`, and is read literally by the orbit decoder;
at `y` the decoder reads `max h (topSection C y)`, which for `C ≥ 10` is `topSection C y`, not
self-visible at `2`, with its code strictly above the cut. -/
theorem freshCode_topSection (C : ℕ) :
    let v₁ : Label.{u} := topCode C 3
    let v₂ : Label.{u} := topCode C 4
    let anc := orbitCode 2 (fun x : Fin 5 ↦ Label.twoLevel v₁ v₂ (sep ω x))
    let h := anc 3
    let w : Fin 5 → Label.{u} := fun x ↦ if anc x < h then anc x else max h (topSection C x)
    IsSelfVisible 2 h ∧ IsShort 2 h ∧ h ≠ ⊥ ∧
      (∀ x, orbitCode 2 w x ∈ codeGrid 2 (2 * 5)) ∧
      (∀ x, min (orbitCode 2 w x) h = min (anc x) h) ∧
      IsWitness (stepSuppressor 2) (orbitDecoder 2 w h) ∧
      (∀ x, orbitDecoder 2 w h (orbitCode 2 w x) = w x) ∧
      orbitDecoder 2 w h (orbitCode 2 w 0) = max h (topSection C 0) ∧
      (10 ≤ C → max h (topSection C 0) = topSection C 0 ∧ ¬ IsSelfVisible 2 (topSection C 0) ∧
        h < orbitCode 2 w 0) := by
  intro v₁ v₂ anc h w
  have hv₂ : IsSelfVisible 2 v₂ := isSelfVisible_topCode C (by omega)
  have hω : (Ordinal.omega0 : Label.{u}) ≤ labelAdd Ordinal.omega0 3 := by
    rw [labelAdd, WithBot.coe_le_coe, WithTop.coe_le_coe]; exact le_self_add
  have hso : sep ω (3 : Fin 5) = labelAdd Ordinal.omega0 3 := rfl
  have hsy : sep ω (0 : Fin 5) = labelAdd Ordinal.omega0 3 := rfl
  have h2o : Label.twoLevel v₁ v₂ (sep ω (3 : Fin 5)) = v₂ := by
    rw [hso]; exact Label.twoLevel_of_le hω
  have hcode : h = orbitMap 2 (fun x : Fin 5 ↦ Label.twoLevel v₁ v₂ (sep ω x)) v₂ := by
    change orbitMap 2 _ (Label.twoLevel v₁ v₂ (sep ω (3 : Fin 5))) = _
    rw [h2o]
  have hhv : IsSelfVisible 2 h := hcode ▸ isSelfVisible_witness (isWitness_orbitMap 2 _) hv₂
  have hhB : h ∈ codeGrid.{u} 2 (2 * 5) := by
    rw [hcode]; exact orbitMap_mem_codeGrid (by simp) _
  have hhs : IsShort 2 h := isShort_of_mem_codeGrid hhB
  have hh0 : h ≠ ⊥ := by
    rw [hcode, Ne, orbitMap_eq_bot_iff]; exact WithBot.coe_ne_bot
  have hanc : orbitCode 2 anc = anc := orbitCode_orbitCode
  have hag (x : Fin 5) : min (w x) h = min (anc x) h := by
    change min (if anc x < h then anc x else max h (topSection C x)) h = _
    split_ifs with hx
    · rfl
    · rw [min_eq_right (le_max_left _ _), min_eq_right (not_lt.mp hx)]
  obtain ⟨hmem, -, hP, -, hge, -, hθ, hread⟩ :=
    exists_freshCode_above_cut (B := 2 * 5) (by simp) hanc hhv hhs hh0 hag
  have hy : anc 0 = h := by
    change orbitMap 2 _ (Label.twoLevel v₁ v₂ (sep ω (0 : Fin 5))) =
      orbitMap 2 _ (Label.twoLevel v₁ v₂ (sep ω (3 : Fin 5)))
    rw [hsy, hso]
  have hw0 : w 0 = max h (topSection C 0) := by
    change (if anc 0 < h then anc 0 else max h (topSection C 0)) = _
    rw [hy, ite_eq_right (lt_irrefl h)]
  refine ⟨hhv, hhs, hh0, hmem, hP, hθ, hread, (hread 0).trans hw0, fun hC ↦ ?_⟩
  have hhle : h ≤ gridPoint 2 (2 * 5) := le_gridPoint_of_mem_codeGrid hhB
  have hlt : h < topSection.{u} C 0 := by
    refine hhle.trans_lt ?_
    change gridPoint 2 (2 * 5) < labelAdd (Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u})) 1
    rw [gridPoint, labelAdd, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    calc Ordinal.omega0 * ((2 * 5 : ℕ) : Ordinal.{u}) + ((2 : ℕ) : Ordinal.{u})
        < Ordinal.omega0 * ((2 * 5 : ℕ) : Ordinal.{u}) + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 2)
      _ = Ordinal.omega0 * ((2 * 5 + 1 : ℕ) : Ordinal.{u}) := by
          rw [Nat.cast_add (2 * 5) 1, Nat.cast_one, mul_add_one]
      _ ≤ Ordinal.omega0 * ((C + 1 : ℕ) : Ordinal.{u}) :=
          omega0_mul_natCast_le_iff.mpr (by omega)
      _ ≤ _ := le_self_add
  have hmax : max h (topSection.{u} C 0) = topSection C 0 := max_eq_right hlt.le
  refine ⟨hmax, not_isSelfVisible_topSection_y C, ?_⟩
  refine lt_freshCode_of_not_isSelfVisible hanc hhv hhs hh0 hag ?_ ?_
  · rw [hw0]; exact le_max_left _ _
  · rw [hw0, hmax]; exact not_isSelfVisible_topSection_y C

end TieInstance

end VaughtConjecture

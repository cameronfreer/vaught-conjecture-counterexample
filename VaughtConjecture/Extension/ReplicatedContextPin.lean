/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedTieReading
import VaughtConjecture.Extension.ReplicatedLiftUniv

/-!
# No pin inside the context

Roadmap, Layer 3 ((R3) and (R4), the context lift of the replicated scheme with agreement heights
in `Scheme.heightSet`).

The pin of `Seed.not_lawful_of_pin` refutes the extension over the tower at the seed position
(`VaughtConjecture.MainTheorem.ReplicatedPinInstance`) with the pinned cell in the context and the
reversing cells in the donor.  The context lift prescribes only below the context coatom, so a
pin refuting it must have its three cells `a`, `a₁`, `a₃` in the context.  That is impossible:

* **Witnesses identify only visible values** (`Label.isSelfVisible_of_witness_eq`): a witness
  bounded by `k` with `σ x = σ y`, `x < y`, takes there a value self-visible at `k`.
* **A reversal at one cell forces visibility** (`Scheme.isSelfVisible_of_reversal`): if lawful
  sections `u`, `w` and a cell `d` reading `a`, `a₁` have `u a₁ < u a ≤ u d` but `w a ≤ w a₁`,
  `w a < w d`, then `w a` is self-visible at the grade of `d`: the row of `d` reads `a₁` below
  `a` (from `u`), and the capped decoder of `w` at `d` identifies the two readings.
* **No pin inside one face** (`Scheme.false_of_face_pin`): a cell of grade `k` above the cap in
  the prescription has, by availability, a cell `d` of full scope of the face at `(univ, k)` above
  it, reading every cell of grade at most `k`; its ambient value is a value of `Γ` self-visible at
  `k`, hence a height; were `w a` pinned, the reversal at `d` would make `w a` a height.
* **For the replicated scheme** (`Seed.not_context_pin`): with the first coatom type legal
  (complete at `(univ, k)`), every state of the catalogue as ambient, and every lawful context
  section as prescription agreeing with it capped at `c` below the grade `k`, no context cell is
  pinned against a reversal by two context cells.

* **A copy face asks nothing beyond the full face** (`Seed.exists_full_eq_of_copyFace`): a cell
  at a mixed face `(U, k)` carries the label of a cell of the tower at `(univ, k)`; so availability
  and ordering at copy faces are those of the cells of full scope.

So the pin technique cannot refute the context lift, and copy faces add no obstruction; this is
not a proof of the context lift.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9]; lawful sections
are [Kni26, Definition 2.5.4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

/-- **A witness bounded by `k` identifies two labels only at a value self-visible at `k`**: if
`σ x = σ y` for `x < y`, the common value is self-visible at `k`.  Below `k` a witness keeps the
finite part inside the block (it commutes with visibility replacement at `k`), and a value of
finite part at least `k` has its preimages of finite part at least `k`, which visibility
replacement fixes. -/
theorem isSelfVisible_of_witness_eq {k : ℕ} {σ : Label.{u} → Label.{u}}
    (hσ : IsWitness (stepSuppressor k) σ) {x y : Label.{u}} (hxy : x < y) (he : σ x = σ y) :
    IsSelfVisible k (σ x) := by
  by_contra hv
  have hcomm (z : Label.{u}) (i : ℕ) (hi : i ≤ k) :
      σ (visibilityReplace k i z) = visibilityReplace k i (σ z) :=
    hσ.visibilityReplace_comm z k (by rw [stepSuppressor_of_le le_rfl]; exact le_top) i hi
  -- a preimage of a value not self-visible has finite part below `k`
  have hfin (z : Label.{u}) (hz : σ z = σ x) : ∃ o : Ordinal.{u}, z = o ∧ finNat o < k := by
    induction z using recBotCoeTop with
    | bot => exact absurd (by rw [← hz, hσ.map_bot]; exact isSelfVisible_bot k) hv
    | top =>
      exfalso
      have h := hcomm ⊤ k le_rfl
      rw [visibilityReplace_top, hz] at h
      exact hv h.symm
    | coe o =>
      refine ⟨o, rfl, not_le.mp fun hko ↦ hv ?_⟩
      have hfix : visibilityReplace k k (o : Label.{u}) = o := by
        rw [visibilityReplace_coe, visibilityReplace_eq_blockOf, ite_eq_right (not_lt.mpr hko),
          blockOf_add_finNat]
      have h := hcomm o k le_rfl
      rw [hfix, hz] at h
      exact h.symm
  obtain ⟨o, rfl, hok⟩ := hfin x rfl
  -- the common value
  obtain ⟨ν, hν, hνk⟩ : ∃ ν : Ordinal.{u}, σ o = ν ∧ finNat ν < k := by
    induction h : σ (o : Label.{u}) using recBotCoeTop with
    | bot => exact absurd (h ▸ isSelfVisible_bot k) hv
    | top => exact absurd (h ▸ isSelfVisible_top k) hv
    | coe ν =>
      refine ⟨ν, rfl, not_le.mp fun hk ↦ hv ?_⟩
      rw [h, isSelfVisible_coe, finNat_spec]
      exact_mod_cast hk
  have hval (i : ℕ) (hi : i ≤ k) :
      σ ((blockOf o + i : Ordinal.{u}) : Label.{u}) =
        ((blockOf ν + i : Ordinal.{u}) : Label.{u}) := by
    have h := hcomm o i hi
    rw [visibilityReplace_coe, visibilityReplace_eq_blockOf, ite_eq_left hok, hν,
      visibilityReplace_coe, visibilityReplace_eq_blockOf, ite_eq_left hνk] at h
    exact h
  have hlt : (ν : Label.{u}) < ((blockOf ν + k : Ordinal.{u}) : Label.{u}) := by
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    conv_lhs => rw [← blockOf_add_finNat ν]
    exact (add_lt_add_iff_left _).mpr (by exact_mod_cast hνk)
  -- the larger label
  have hy := hfin y he.symm
  obtain ⟨o', rfl, hok'⟩ := hy
  have hoo : o < o' := by exact_mod_cast hxy
  rcases (blockOf_mono hoo.le).lt_or_eq with hb | hb
  · -- different blocks: the top of the block of `o` lies below `o'`
    have hle : ((blockOf o + k : Ordinal.{u}) : Label.{u}) ≤ (o' : Label.{u}) := by
      rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
      exact (add_natCast_lt_of_lt (isSuccPrelimit_blockOf o') hb k).le.trans
        (le_self_add.trans_eq (blockOf_add_finNat o'))
    have := hσ.monotone hle
    rw [hval k le_rfl, ← he, hν] at this
    exact absurd this (not_le.mpr hlt)
  · -- one block: the finite parts are read apart
    have h1 := hval (finNat o) hok.le
    have h2 := hval (finNat o') hok'.le
    rw [blockOf_add_finNat] at h1
    have ho' : blockOf o + (finNat o' : Ordinal.{u}) = o' := by rw [hb, blockOf_add_finNat]
    rw [ho'] at h2
    rw [h1, h2, WithBot.coe_inj, WithTop.coe_inj] at he
    have hf : finNat o = finNat o' := by exact_mod_cast (add_left_cancel he)
    have : o = o' := by rw [← blockOf_add_finNat o, ← blockOf_add_finNat o', hb, hf]
    exact absurd this hoo.ne

end Label

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n}

/-- **A reversal at one cell forces visibility**: let `u` and `w` be lawful sections, `d` a cell
reading `a` and `a₁` (both below it), with `u a₁ < u a ≤ u d` (the section `u` orders `a₁` below
`a` under the label of `d`) and `w a ≤ w a₁`, `w a < w d` (the section `w` does not).  Then the
row of `d` reads `a₁` strictly below `a` (from `u`), and the capped decoder of `w` at `d`, a
witness bounded by the grade of `d`, identifies the two readings at `w a`; so `w a` is
self-visible at the grade of `d` (`Label.isSelfVisible_of_witness_eq`). -/
theorem isSelfVisible_of_reversal {u w : Fin S.card → Label.{u}} (hu : S.rows.IsLawful u)
    (hw : S.rows.IsLawful w) {d a a₁ : Fin S.card}
    (ha : a ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex d))
    (ha₁ : a₁ ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex d)) (h1 : u a₁ < u a)
    (had : u a ≤ u d) (hwa : w a ≤ w a₁) (hwd : w a < w d) :
    IsSelfVisible (S.toCellScheme.grade d) (w a) := by
  have hdd : d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex d) :=
    CellScheme.mem_below_gradedIndex _ d
  obtain ⟨θu, hθu, -, hθur⟩ := exists_cappedDecoder_below
    (hu.isLawfulBelow (S.toCellScheme.gradedIndex d)) hdd rfl
  obtain ⟨θw, hθw, -, hθwr⟩ := exists_cappedDecoder_below
    (hw.isLawfulBelow (S.toCellScheme.gradedIndex d)) hdd rfl
  have hrow : S.rowAt d a₁ < S.rowAt d a := by
    by_contra hcon
    have h := hθu.monotone (not_lt.mp hcon)
    rw [hθur a ha, hθur a₁ ha₁, min_eq_left had] at h
    exact absurd ((h.trans (min_le_left _ _))) (not_le.mpr h1)
  have e1 : θw (S.rowAt d a) = w a := by rw [hθwr a ha, min_eq_left hwd.le]
  have e2 : θw (S.rowAt d a₁) = w a := by
    refine le_antisymm (e1 ▸ hθw.monotone hrow.le) ?_
    rw [hθwr a₁ ha₁]
    exact le_min hwa hwd.le
  have h := Label.isSelfVisible_of_witness_eq hθw hrow (e2.trans e1.symm)
  rwa [e2] at h

/-- **No pin inside one face**: let `u` (a prescription) and `w` (an ambient state with values in
`Γ`) be lawful sections agreeing capped at `c` at the cells of grade at most `k`, and let the face
carry a cell `d₀` at `(univ, k)`.  If `u` orders `u a₁ < u a ≤ u a₃` with `a₃` of grade `k` above
`c`, `a`, `a₁` of grades at most `k`, while `w a ≤ w a₁`, then `w a` is not pinned: some value of
`Γ` self-visible at `k` and at least `c` lies at or below `w a`.  Availability puts `a₃` below a
cell `d` at `(univ, k)` with `u d ≥ u a₃`; its ambient value is a value of `Γ` self-visible at
`k`, at least `c`; were `w a` pinned, `w a < w d` and `Scheme.isSelfVisible_of_reversal` would make
`w a` itself such a value. -/
theorem false_of_face_pin {k : ℕ} {Γ : Finset Label.{u}} {u w : Fin S.card → Label.{u}}
    (hu : S.rows.IsLawful u) (hw : S.rows.IsLawful w) (hwΓ : ∀ x, w x ∈ Γ) {d₀ a a₁ a₃ : Fin S.card}
    (hd₀ : S.toCellScheme.gradedIndex d₀ = ((univ : Finset (Fin n)), k))
    (ha : S.toCellScheme.grade a ≤ k) (ha₁ : S.toCellScheme.grade a₁ ≤ k)
    (ha₃ : S.toCellScheme.grade a₃ = k) {c : Label.{u}}
    (hcap : ∀ x, S.toCellScheme.grade x ≤ k → min (u x) c = min (w x) c) (h1 : u a₁ < u a)
    (h3 : u a ≤ u a₃) (hc3 : ¬ u a₃ ≤ c) (hwa : w a ≤ w a₁)
    (hpin : ∀ x ∈ Γ, IsSelfVisible k x → c ≤ x → w a < x) : False := by
  -- the ambient at `a` is at least the cap
  have hca : c ≤ w a := by
    rcases lt_or_ge (u a) c with hlt | hge
    · exfalso
      have e := hcap a ha
      have e₁ := hcap a₁ ha₁
      rw [min_eq_left hlt.le] at e
      rw [min_eq_left (h1.trans hlt).le] at e₁
      have key (x y : Label.{u}) (hxy : x = min y c) (hx : x < c) : y = x := by
        rcases le_total y c with hyc | hyc
        · rw [min_eq_left hyc] at hxy; exact hxy.symm
        · rw [min_eq_right hyc] at hxy; exact absurd hxy hx.ne
      have hwa' : w a = u a := key _ _ e hlt
      have hwa₁ : w a₁ = u a₁ := key _ _ e₁ (h1.trans hlt)
      exact absurd (hwa.trans_eq hwa₁) (by rw [hwa']; exact not_le.mpr h1)
    · have e := hcap a ha
      rw [min_eq_right hge] at e
      exact min_eq_right_iff.mp e.symm
  -- the cell available above `a₃`
  obtain ⟨d, hd, hle⟩ := hu.availability a₃ d₀
    (by rw [show S.toCellScheme.scope d₀ = univ from congrArg Prod.fst hd₀]; exact subset_univ _)
    (ha₃.trans (congrArg Prod.snd hd₀).symm)
  rw [hd₀] at hd
  have hdk : S.toCellScheme.grade d = k := congrArg Prod.snd hd
  have hcd : c ≤ w d := by
    have e := hcap d hdk.le
    rw [min_eq_right ((not_le.mp hc3).le.trans hle)] at e
    exact min_eq_right_iff.mp e.symm
  have hwd : w a < w d := hpin _ (hwΓ d) (hdk ▸ hw.orderly d) hcd
  have hbelow (b : Fin S.card) (hb : S.toCellScheme.grade b ≤ k) :
      b ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex d) := by
    rw [CellScheme.mem_below, hd]; exact ⟨subset_univ _, hb⟩
  have hv := isSelfVisible_of_reversal hu hw (hbelow a ha) (hbelow a₁ ha₁) h1
    (h3.trans hle) hwa hwd
  rw [hdk] at hv
  exact lt_irrefl _ (hpin _ (hwΓ a) hv hca)

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m) {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- **No pin of the replicated scheme inside the context**: for a state `R'` of the catalogue
(the ambient's state) and a lawful section `u` of the first coatom type (for the context lift, the
prescription's context section, `Seed.isLawful_ctxSection`) agreeing with `R'` capped at `c` at the
context cells of grade at most `k`, `1 ≤ k ≤ m + 1`, if `u` orders three context cells
`u a₁ < u a ≤ u a₃` (`a₃` of grade `k` above `c`, `a`, `a₁` of grades at most `k`) while
`R' a ≤ R' a₁`, then the pin of `Seed.not_lawful_of_pin` at `a` fails: some height at `k` at
least `c` lies at or below `R' a`.  The first coatom type is legal, so complete at `(univ, k)`;
availability puts `a₃` below its cell `d` there, which reads `a` and `a₁`
(`Scheme.false_of_face_pin`).  Hence a pin refuting the context lift (whose prescription lies in
the context) cannot have all three cells in the context. -/
theorem not_context_pin {K k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m + 1)
    {R' : Fin (I.attachment g).card → Label.{u}}
    (hR' : R' ∈ (I.attachmentBase g).towerCat Γ A K) {u : Fin I.left.card → Label.{u}}
    (hu : I.left.rows.IsLawful u) {a a₁ a₃ : Fin I.left.card}
    (ha : I.left.toCellScheme.grade a ≤ k) (ha₁ : I.left.toCellScheme.grade a₁ ≤ k)
    (ha₃ : I.left.toCellScheme.grade a₃ = k) {c : Label.{u}}
    (hcap : ∀ x, I.left.toCellScheme.grade x ≤ k → min (u x) c = min (R' (I.attachCtxCell g x)) c)
    (h1 : u a₁ < u a) (h3 : u a ≤ u a₃) (hc3 : ¬ u a₃ ≤ c)
    (hwa : R' (I.attachCtxCell g a) ≤ R' (I.attachCtxCell g a₁)) :
    ¬ ∀ x ∈ Scheme.heightSet Γ B' k, c ≤ x → R' (I.attachCtxCell g a) < x := by
  intro hpin
  obtain ⟨hRΓ, hRl, -⟩ := Scheme.LadderBaseData.mem_towerCat.mp hR'
  have hw : I.left.rows.IsLawful fun x ↦ R' (I.attachCtxCell g x) :=
    GrowthRequests.isLawful_root (I.restrictFace_left_attachmentType g) hRl
  obtain ⟨d₀, hd₀⟩ := I.isLegal_left.isComplete ((univ : Finset (Fin (m + 1))), k)
    ⟨I.left.univ_mem_faces, hk1, by simpa using hkm⟩
  exact Scheme.false_of_face_pin (Γ := Γ) hu hw (fun x ↦ hRΓ _) hd₀ ha ha₁ ha₃ hcap h1 h3 hc3 hwa
    fun x hx hv hcx ↦ hpin x (Scheme.mem_heightSet.mpr (.inr ⟨hx, hv⟩)) hcx

/-- **A copy face asks nothing beyond the full face**: in a section lawful below `(univ, j)`, a
cell at a mixed face `(U, k)`, `k ≤ #U`, `k ≤ j`, carries the label of a cell of the tower at
`(univ, k)` (it is the copy of one, `Seed.exists_eq_copyFull`, and copies carry their original's
label, `Seed.eq_copyAt`).  So availability at a copy face is served by the cells of full scope,
and an obstruction to a lift at a copy face is already one at the full face. -/
theorem exists_full_eq_of_copyFace {U : Finset (Fin (m + 2))} (hU : U ∈ I.mixedFaces g)
    {j k : ℕ} (hkU : k ≤ #U) (hkj : k ≤ j) {w : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hw : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ w d)
    (z : Fin (I.replicated g H Γ A B').card)
    (hz : (I.replicated g H Γ A B').toCellScheme.gradedIndex z = (U, k)) :
    ∃ v : Fin (I.attachTower g H Γ A B').card,
      (I.attachTower g H Γ A B').toCellScheme.gradedIndex v =
        ((univ : Finset (Fin (m + 2))), k) ∧ w z = w (Fin.castAdd _ v) := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_copyFull hU hkU z hz
  refine ⟨v, hv, eq_copyAt hU hw _ _ ?_⟩
  rw [CellScheme.mem_below, Scheme.gradedIndex_mirror_castAdd, hv]
  exact ⟨subset_rfl, hkj⟩

end Seed

end VaughtConjecture

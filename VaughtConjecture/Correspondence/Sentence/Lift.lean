/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Sentence.LevelZero

/-!
# From a model of `σ[L]` to a lift in `K₀[L]`

Numbering as in the current draft of [AFK26].  For a structure `B` of `L_c[L]`, `liftStructure B`
is the structure of `L_b[L] ∪ L_c[L]` on the same carrier that keeps `P_n` and `R_t` and reads the
invariant `Q_t` as `R_t` when `t` has rank zero and as empty otherwise: the identification of the
rank-zero invariants with the symbols of `L_c[L]` in the proof of [AFK26, Theorem 4.23].  Its base
reduct is `B` (`baseReduct_liftStructure`) and it is fixed by `τ₀`
(`projectStructure_liftStructure`).  When `B` satisfies `σ[L]` it is compatible with `ID[L]`
(`isTemplateCompatible_liftStructure`: clauses (a) `Th_Geo` and (b), (c) of
[AFK26, Definition 4.22]) and satisfies `D[α]` for every `α < ω`
(`satisfiesDensityAt_liftStructure`: clause (d), through rank-zero density,
`density_baseReduct_iff`, and the donor reduction and witness passage of
`satisfiesDensityAt_of_rankZero`).  On a nonempty carrier it lies in `K₀[L]`
(`liftStructure_mem_templateStageClass`).  No countability is used.  Correspondence with the
printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

variable {M : Type v}

/-! ### A class of rank zero carries its faces -/

namespace LegalClass

/-- **The invariants of the faces of a class of rank zero**: `Q_{c'}` holds along `i` in the
template of `c` exactly when `c'` has rank zero and `R_{c'}` holds along `i`.
Correspondence with the printed definitions. -/
theorem holds_invariant_iff {n k : ℕ} {c : LegalClass.{u} n} (hc : c.IsRankZero)
    (c' : LegalClass.{u} k) (hk : 0 < k) (i : Fin k → Fin n) :
    c.1.Holds (TemplateSymbol.invariant c' hk) i ↔
      ∃ h0 : c'.IsRankZero, c.1.Holds (TemplateSymbol.base c' h0 hk) i := by
  constructor
  · rintro ⟨hi, s, hs, hread⟩
    have hs0 := TemplateClass.project_eq_of_restrictFace_eq _ hc hs
    change s = c'.1 at hread
    subst hread
    exact ⟨hs0, hi, _, hs, hs0⟩
  · rintro ⟨h0, hi, s, hs, hread⟩
    have hs0 := TemplateClass.project_eq_of_restrictFace_eq _ hc hs
    change s.project _ = c'.1 at hread
    rw [hs0] at hread
    exact ⟨hi, s, hs, hread⟩

end LegalClass

/-! ### The lift -/

/-- The relations of `liftStructure B`. -/
def liftRelMap (B : baseTemplateLanguage.{u}.Structure M) :
    ∀ {k : ℕ}, TemplateSymbol.{u} k → (Fin k → M) → Prop
  | _, .closed hn, xs =>
      RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.closed hn) xs
  | _, .invariant c hn, xs => ∃ h0 : c.IsRankZero,
      RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.base c h0 hn) xs
  | _, .base c h0 hn, xs =>
      RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.base c h0 hn) xs

/-- **The rank-zero lift of a structure of `L_c[L]`**: `P_n` and `R_t` as in `B`, and `Q_t` as
`R_t` for `t` of rank zero (and as empty otherwise).
Correspondence with the printed definitions. -/
@[instance_reducible] def liftStructure (B : baseTemplateLanguage.{u}.Structure M) :
    templateLanguage.{u}.Structure M where
  funMap f := Empty.elim f
  RelMap r xs := liftRelMap B r xs

variable (B : baseTemplateLanguage.{u}.Structure M)

@[simp] theorem relMap_liftStructure_closed {k : ℕ} (hk : 0 < k) (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := liftStructure B) (TemplateSymbol.closed hk) xs ↔
      RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.closed hk) xs :=
  Iff.rfl

@[simp] theorem relMap_liftStructure_invariant {k : ℕ} (c : LegalClass.{u} k) (hk : 0 < k)
    (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := liftStructure B) (TemplateSymbol.invariant c hk)
      xs ↔ ∃ h0 : c.IsRankZero,
        RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.base c h0 hk) xs :=
  Iff.rfl

@[simp] theorem relMap_liftStructure_base {k : ℕ} (c : LegalClass.{u} k) (h0 : c.IsRankZero)
    (hk : 0 < k) (xs : Fin k → M) :
    RelMap (L := templateLanguage.{u}) (self := liftStructure B) (TemplateSymbol.base c h0 hk)
      xs ↔ RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.base c h0 hk) xs :=
  Iff.rfl

/-- **The base reduct of the lift is `B`.**  Correspondence with the printed definitions. -/
theorem baseReduct_liftStructure : baseReduct (liftStructure B) = B :=
  baseStructure_ext fun r _ ↦ by cases r <;> exact Iff.rfl

/-- **The lift is fixed by `τ₀`.**  Correspondence with the printed definitions. -/
theorem projectStructure_liftStructure :
    projectStructure 0 (liftStructure B) = liftStructure B := by
  refine templateStructure_ext fun r xs ↦ ?_
  cases r with
  | closed hk => exact Iff.rfl
  | base c h0 hk => exact Iff.rfl
  | invariant c hk =>
    rw [relMap_projectStructure_invariant, relMap_liftStructure_invariant]
    constructor
    · rintro ⟨c', rfl, h0, hx⟩
      rw [LegalClass.project_eq_self h0]
      exact ⟨h0, hx⟩
    · rintro ⟨h0, hx⟩
      exact ⟨c, LegalClass.project_eq_self h0, h0, hx⟩

/-! ### Compatibility and density -/

variable {B}

private theorem injective_of_pairwise {n : ℕ} {x : Fin n → M}
    (h : ∀ i j, i < j → x i ≠ x j) : Function.Injective x := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h i j hlt hij
  · exact h j i hlt hij.symm

/-- **The lift of a model of `σ[L]` is compatible with `ID[L]`**: `Th_Geo` from clause (a), the
structured geometry from clause (b), and the pairs of `ID[L]` from clause (c), with the invariant
pairs read through the faces of rank-zero classes (`LegalClass.holds_invariant_iff`).
Correspondence with the printed definitions. -/
theorem isTemplateCompatible_liftStructure (h : @IsTemplateSentenceModel.{u} M B) :
    IsTemplateCompatible (liftStructure B) := by
  let := B
  let : templateLanguage.{u}.Structure M := liftStructure B
  refine
    { isStructuredGeometry :=
        { isGeometry :=
            { injective := ?_
              perm := ?_
              exists_closed := ?_
              inter := ?_ }
          closed_iff := ?_
          exclusive := ?_
          determines := ?_ }
      satisfiesPairs := ?_ }
  · intro n hn x hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    exact injective_of_pairwise (h.distinct n x hx)
  · intro n hn x e
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    exact h.perm n x e
  · intro n hn x hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    obtain ⟨k, y, hy⟩ := h.extension n x fun i j hij ↦ hx.ne hij.ne
    exact ⟨k, Fin.append x y, TemplateSentence.append_comp_castAdd y, hy⟩
  · intro n₀ n₁ k h₀ h₁ hk x y z hx hy hz hxyz
    obtain ⟨n₀, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h₀.ne'
    obtain ⟨n₁, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h₁.ne'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
    refine h.inter n₀ n₁ k x y z hx hy (fun l l' hl ↦ hz.ne hl.ne) (fun l ↦ ?_) fun i j hij ↦ ?_
    · have hl : z l ∈ Set.range x ∩ Set.range y := hxyz ▸ Set.mem_range_self l
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hl
      exact ⟨⟨i, hi.symm⟩, ⟨j, hj.symm⟩⟩
    · have hl : x i ∈ Set.range z := hxyz ▸ ⟨Set.mem_range_self i, hij ▸ Set.mem_range_self j⟩
      obtain ⟨l, hl⟩ := hl
      exact ⟨l, hl.symm⟩
  · intro n hn x
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    change ClosedRel.{u} _ x ↔ _
    rw [h.typing n x]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨TemplateSymbol.invariant t.1 n.succ_pos, trivial, t.2, ht⟩
    · rintro ⟨Q, hQ, hx⟩
      obtain ⟨c, hk, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
      obtain ⟨h0, hx⟩ := hx
      exact ⟨⟨c, h0⟩, hx⟩
  · intro n Q Q' hQ hQ' hne x hx hx'
    obtain ⟨c, hn, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
    obtain ⟨c', hn', rfl⟩ := TemplateSymbol.exists_eq_invariant hQ'
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    obtain ⟨h0, hx⟩ := hx
    obtain ⟨h0', hx'⟩ := hx'
    refine h.exclusive n ⟨c, h0⟩ ⟨c', h0'⟩ (fun hcc ↦ hne ?_) x hx hx'
    obtain rfl : c = c' := congrArg Subtype.val hcc
    rfl
  · intro n k Q R i hQ x y hx hy
    obtain ⟨c, hn, rfl⟩ := TemplateSymbol.exists_eq_invariant hQ
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    obtain ⟨h0, hx⟩ := hx
    obtain ⟨h0', hy⟩ := hy
    have hd := h.determines n ⟨c, h0⟩
    cases R with
    | closed hk => exact hd k (BaseSymbol.closed hk) i x y hx hy
    | base c'' h0'' hk => exact hd k (BaseSymbol.base c'' h0'' hk) i x y hx hy
    | invariant c'' hk =>
      exact exists_congr fun h'' ↦ hd k (BaseSymbol.base c'' h'' hk) i x y hx hy
  · rw [satisfiesPairs_templateDiagramPairs_iff]
    intro n hn c x hx k r i
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    obtain ⟨h0, hx⟩ := hx
    have hd := h.diagram n ⟨c, h0⟩ x hx k
    cases r with
    | closed hk => exact hd (BaseSymbol.closed hk) i
    | base c'' h0'' hk => exact hd (BaseSymbol.base c'' h0'' hk) i
    | invariant c'' hk =>
      rw [LegalClass.holds_invariant_iff h0]
      exact exists_congr fun h'' ↦ hd (BaseSymbol.base c'' h'' hk) i

/-- **The lift of a model of `σ[L]` satisfies `D[α]` for every `α < ω`**: clause (d) is rank-zero
density (`density_baseReduct_iff`), which gives density for donors of every rank by donor
reduction and witness passage (`satisfiesDensityAt_of_rankZero`).
Correspondence with the printed definitions. -/
theorem satisfiesDensityAt_liftStructure (h : @IsTemplateSentenceModel.{u} M B) {α : Ordinal.{u}}
    (hα : α < blockStage 0) : SatisfiesDensityAt α (liftStructure B) := by
  rw [blockStage_zero] at hα
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hα
  have hG := isTemplateCompatible_liftStructure h
  have hfix := projectStructure_liftStructure B
  refine satisfiesDensityAt_of_rankZero hfix hα.le ((density_baseReduct_iff hG hfix).mp ?_ k)
  rw [baseReduct_liftStructure]
  exact h.density

/-- **The lift of a model of `σ[L]` lies in `K₀[L]`**, on a nonempty carrier.
Correspondence with the printed definitions. -/
theorem liftStructure_mem_templateStageClass [Nonempty M] (h : @IsTemplateSentenceModel.{u} M B) :
    liftStructure B ∈ templateStageClass M (0 : Ordinal.{u}) :=
  ⟨‹_›, isTemplateCompatible_liftStructure h, projectStructure_liftStructure B,
    fun _ hα ↦ satisfiesDensityAt_liftStructure h hα⟩

end

end VaughtConjecture

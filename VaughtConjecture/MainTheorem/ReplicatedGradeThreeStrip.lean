/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedGradeTwoLift

/-!
# Strip pairs of the grade three: coverage, nesting and strip freedom conflict

Roadmap, Layer 3 ((R3) and (R4), the heights of a level of grade `3`).

**The shape of a strip violation** (`Label.exists_strip_shape`): a label `x` self-visible at `j`
on the strip of `c` at a grade `k > j` (`visibilityReplace k k x = c`) and strictly below it is
`ω * β + f` with `j ≤ f < k`, and `c = ω * β + k`.  So every violation of strip freedom off the
natural strip at the grades `2 < 3` (`Scheme.IsStripFreeOffNatural G Γ 3`, heights self-visible at
their grade) is a pair `ω * β + 2 ∈ G 2`, `ω * β + 3 ∈ G 3 ∩ Γ` with `β ≠ 0`
(`Scheme.exists_shape_of_not_isStripFreeOffNatural`): the finite parts come from the violation.

**The conflict** (`Seed.not_isStripFreeOffNatural_of_stripPair`): the catalogues of a ladder tower
decrease (`Scheme.LadderBaseData.towerCat_succ_subset`; the writing of a state of the grade `3` is
lawful only as an entry of the layer `2`, `Scheme.isLawful_layerRow`), so a state of the
catalogue at `3` is a state of the catalogue at `2`.  If the heights cover the catalogue values
(every value self-visible at `k` of a state of the catalogue at `k` at a cell of grade at most `k`
is in `G k`; each such value is a reachable cut, read by the cell of its state,
`Seed.exists_cell_of_mem_towerCat`, so separation asks it), a state of the catalogue at `3` with a
**strip pair** (`x` self-visible at `2` at a cell of grade at most `2`, `c` self-visible at `3`
at a cell of grade at most `3`, `visibilityReplace 3 3 x = c`, `x < c`, `c ≠ ω * 0 + 3`) defeats
strip freedom off the natural strip.  This holds for any heights, any values and any blocks: it is
a conflict between coverage, nesting and `Scheme.IsStripFreeOffNatural`, not a statement about
the block sets `D k`.

**Orbit codes produce strip pairs** (`Label.orbitCode_stripPair`): a value `x` not self-visible at
`k` and the value `visibilityReplace k k x` of the same labelling are coded in one code block, the
first on the strip of the second and strictly below it, keeping self-visibility at every lower
grade (`Label.isSelfVisible_orbitCode_of_isOrbitKey`).  So a catalogue at `3` containing the code
of a state with values `ω * a + 2`, `ω * a + 3` (`a ≠ 0`, at cells of grades at most `2`, `3`)
defeats strip freedom off the natural strip under coverage and nesting
(`Seed.not_isStripFreeOffNatural_of_orbitCode`).  A block relabelling that moves whole blocks keeps
the pair on one strip (not compiled: the relabelled code is not defined here).

**Where the jump needs the strip** (`Label.orbitDecoder_of_orbitClass`).  The pair of a strip pair
is an orbit key class: its cut is coded from an orbit key.  The orbit decoder reads every label
`x` of the strip of a cut literally when every cell coded on that strip has an orbit key value
with the key of `x` (the natural strip is the case of the block `0`,
`Label.orbitDecoder_of_natural`); the jump of `Label.le_orbitDecoder_of_code_at_cut` needs a cell
coded at the cut whose value is not an orbit key.  Whether every cut of a lift that carries a
height of a strip pair below it is of the first kind is not settled here.

**Scope.**  An obstruction to the earlier constructions (the replicated scheme over the height-set
tower, or carriers with admitted controllers), or a step of one; not used by the main theorem
through the levels (`VaughtConjecture.MainTheorem.GrowthLevelRoute`), and kept as the compiled
reason that construction was replaced.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

/-- **The shape of a strip violation**: a label self-visible at `j`, on the strip of `c` at a
grade `k` and strictly below it, is `ω * β + f` with `j ≤ f < k`, and `c = ω * β + k`. -/
theorem exists_strip_shape {j k : ℕ} {x c : Label.{u}} (hx : IsSelfVisible j x)
    (hxc : visibilityReplace k k x = c) (hlt : x < c) :
    ∃ (β : Ordinal.{u}) (f : ℕ), j ≤ f ∧ f < k ∧
      x = ((ω * β + (f : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ∧
      c = ((ω * β + (k : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot =>
    rw [visibilityReplace_bot] at hxc
    subst hxc
    exact absurd hlt (lt_irrefl _)
  | top => exact absurd hlt (not_lt_of_ge le_top)
  | coe o =>
    obtain ⟨f, hf⟩ : ∃ f : ℕ, o % ω = f :=
      ⟨_, (Ordinal.lt_omega0.mp (Ordinal.mod_lt o Ordinal.omega0_ne_zero)).choose_spec⟩
    have ho : o = ω * (o / ω) + f := by rw [← hf]; exact (Ordinal.div_add_mod o ω).symm
    rw [ho] at hx hxc hlt ⊢
    rw [visibilityReplace_block] at hxc
    have hjf : j ≤ f := by
      have := isSelfVisible_coe.mp hx
      rw [omega0_mul_add_natCast_mod] at this
      exact_mod_cast this
    by_cases hfk : f < k
    · rw [ite_eq_left hfk] at hxc
      exact ⟨o / ω, f, hjf, hfk, rfl, hxc.symm⟩
    · rw [ite_eq_right hfk] at hxc
      rw [← hxc] at hlt
      exact absurd hlt (lt_irrefl _)

/-- **Orbit codes produce strip pairs**: for a value `W a` not self-visible at `k`, other than
`⊥`, and the value `W a' = visibilityReplace k k (W a)`, the codes are in one code block, the first
on the strip of the second and strictly below it. -/
theorem orbitCode_stripPair {k : ℕ} {ι : Type*} [Fintype ι] {W : ι → Label.{u}} {a a' : ι}
    (h0 : W a ≠ ⊥) (hnv : ¬ IsSelfVisible k (W a)) (hkey : visibilityReplace k k (W a) = W a') :
    visibilityReplace k k (orbitCode k W a) = orbitCode k W a' ∧
      orbitCode k W a < orbitCode k W a' := by
  have hidem : visibilityReplace k k (W a') = visibilityReplace k k (W a) := by
    rw [← hkey]
    exact visibilityReplace_self_visibilityReplace_of_le le_rfl le_rfl _
  have h0' : W a' ≠ ⊥ := fun h ↦ h0 (visibilityReplace_eq_bot_iff.mp (hkey.trans h))
  have hvis' : IsSelfVisible k (W a') := hidem.trans hkey
  have hok : IsOrbitKey k W (W a) := ⟨a, rfl, hnv⟩
  have hok' : IsOrbitKey k W (W a') := (isOrbitKey_congr hidem).mpr hok
  have hP' : IsSelfVisible k (orbitCode k W a') := by
    rw [orbitCode_apply]
    exact (isSelfVisible_orbitMap_iff h0').mpr (.inr hvis')
  have hP : ¬ IsSelfVisible k (orbitCode k W a) := by
    rw [orbitCode_apply, isSelfVisible_orbitMap_iff h0]
    rintro (h | h)
    · exact h hok
    · exact hnv h
  have hv : visibilityReplace k k (orbitCode k W a) = orbitCode k W a' := by
    rw [orbitCode_apply, visibilityReplace_orbitMap h0, codeBlock_congr hidem.symm,
      ← visibilityReplace_orbitMap h0', ← orbitCode_apply]
    exact hP'
  refine ⟨hv, lt_of_le_of_ne ?_ fun he ↦ hP (he ▸ hP')⟩
  rw [orbitCode_apply, orbitCode_apply, ← hkey]
  exact monotone_orbitMap k W (le_visibilityReplace (by omega) _)

/-- **The block move keeps self-visibility**: an orbit code of a value self-visible at `j` is
self-visible at `j` when the value is an orbit key (the code moves it to its code block). -/
theorem isSelfVisible_orbitCode_of_isOrbitKey {k j : ℕ} {ι : Type*} [Fintype ι]
    {W : ι → Label.{u}} {a : ι} (hok : IsOrbitKey k W (W a)) (hj : IsSelfVisible j (W a)) :
    IsSelfVisible j (orbitCode k W a) := by
  rw [orbitCode_apply, orbitMap_of_isOrbitKey hok]
  change visibilityReplace j j _ = _
  rw [← moveToBlock_visibilityReplace, hj]

/-- **The orbit decoder reads an orbit key class literally**: if every cell whose code has the
key `visibilityReplace k k x` has an orbit key value with that key, the orbit decoder reads `x`,
below the cut `h`, as `x` (`Label.orbitDecoder_of_natural` is the case of the natural key). -/
theorem orbitDecoder_of_orbitClass {k : ℕ} {ι : Type*} [Fintype ι] {W : ι → Label.{u}}
    {h x : Label.{u}} (hxh : x < h)
    (hcls : ∀ e, visibilityReplace k k (orbitCode k W e) = visibilityReplace k k x →
      IsOrbitKey k W (W e) ∧ visibilityReplace k k (W e) = visibilityReplace k k x) :
    orbitDecoder k W h x = x := by
  classical
  unfold orbitDecoder
  rw [min_eq_left hxh.le]
  refine max_eq_left (Finset.sup_le fun e he ↦ ?_)
  by_cases hlt : visibilityReplace k k x < visibilityReplace k k (orbitCode k W e)
  · rw [cellReading, ite_eq_left hlt]
    exact bot_le
  · rw [cellReading, ite_eq_right hlt]
    by_cases heq : visibilityReplace k k x = visibilityReplace k k (orbitCode k W e)
    · obtain ⟨hok, hk⟩ := hcls e heq.symm
      rw [ite_eq_left ⟨heq, hok⟩, moveToBlock_eq_self hk]
    · exfalso
      have hhe : h ≤ visibilityReplace k k (orbitCode k W e) := (Finset.mem_filter.mp he).2
      have hle : visibilityReplace k k (orbitCode k W e) < visibilityReplace k k x :=
        lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)
      -- a label self-visible at `k` strictly between `x` and its key does not exist
      have hxe : x < visibilityReplace k k (orbitCode k W e) := hxh.trans_le hhe
      have hsv : IsSelfVisible k (visibilityReplace k k (orbitCode k W e)) :=
        visibilityReplace_self_visibilityReplace_of_le le_rfl le_rfl _
      have hmono := monotone_visibilityReplace (k := k) (i := k) le_rfl hxe.le
      rw [hsv] at hmono
      exact absurd hle (not_lt.mpr hmono)

end Label

namespace Scheme

/-- **Every violation of strip freedom off the natural strip at the grades `2 < 3` is a pair
`ω * β + 2`, `ω * β + 3`**, `β ≠ 0`, for heights self-visible at their grade: the finite parts are
derived from the violation (`Label.exists_strip_shape`). -/
theorem exists_shape_of_not_isStripFreeOffNatural {G : ℕ → Finset Label.{u}}
    {Γ : Finset Label.{u}} (hGv : ∀ j, ∀ x ∈ G j, IsSelfVisible j x)
    (h : ¬ IsStripFreeOffNatural G Γ 3) :
    ∃ β : Ordinal.{u}, β ≠ 0 ∧
      ((ω * β + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ∈ G 2 ∧
      ((ω * β + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ∈ G 3 ∧
      ((ω * β + ((3 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ∈ Γ := by
  unfold IsStripFreeOffNatural at h
  push Not at h
  obtain ⟨j, k, hj, hjk, hk, x, hx, c, hc, hcΓ, hnat, hxc, hlt⟩ := h
  obtain rfl : j = 2 := by omega
  obtain rfl : k = 3 := by omega
  obtain ⟨β, f, hjf, hfk, rfl, rfl⟩ := Label.exists_strip_shape (hGv 2 _ hx) hxc hlt
  obtain rfl : f = 2 := by omega
  refine ⟨β, fun hβ ↦ hnat ?_, hx, hc, hcΓ⟩
  rw [hβ, gridPoint]
  simp

end Scheme

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-- **Coverage, nesting and strip freedom off the natural strip conflict** at a strip pair: if a
state `R` of the catalogue at `3` has a strip pair (`R a` self-visible at `2` at a cell of grade at
most `2`, `R a'` self-visible at `3` at a cell of grade at most `3`, on its strip strictly below
it, not the natural cut), the catalogues decrease (`A 3 R → A 2 R`, as the ladder tower asks), and
the heights cover the catalogue values, then strip freedom off the natural strip fails. -/
theorem not_isStripFreeOffNatural_of_stripPair {G : ℕ → Finset Label.{u}}
    {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    (hA : ∀ R, A 3 R → A 2 R)
    (hcov : ∀ k, ∀ R ∈ (I.attachmentBase g).towerCat Γ A k, ∀ a,
      (I.attachment g).toCellScheme.grade a ≤ k → IsSelfVisible k (R a) → R a ∈ G k)
    {R : Fin (I.attachment g).card → Label.{u}} (hR : R ∈ (I.attachmentBase g).towerCat Γ A 3)
    {a a' : Fin (I.attachment g).card} (ha : (I.attachment g).toCellScheme.grade a ≤ 2)
    (ha' : (I.attachment g).toCellScheme.grade a' ≤ 3) (hx : IsSelfVisible 2 (R a))
    (hc : IsSelfVisible 3 (R a')) (hstrip : visibilityReplace 3 3 (R a) = R a')
    (hlt : R a < R a') (hnat : R a' ≠ gridPoint 3 0) :
    ¬ Scheme.IsStripFreeOffNatural G Γ 3 := by
  obtain ⟨hRΓ, hRl, hRA⟩ := Scheme.LadderBaseData.mem_towerCat.mp hR
  have hR2 : R ∈ (I.attachmentBase g).towerCat Γ A 2 :=
    Scheme.LadderBaseData.mem_towerCat.mpr ⟨hRΓ, hRl, hA R hRA⟩
  intro h
  exact h 2 3 le_rfl (by norm_num) le_rfl (R a) (hcov 2 R hR2 a ha hx) (R a')
    (hcov 3 R hR a' ha' hc) (hRΓ a') hnat ⟨hstrip, hlt⟩

/-- **The conflict from the code of a state with a strip pair**: if the catalogue at `3` contains
the orbit code at `3` of a state `W` with values `W a` (self-visible at `2`, not at `3`, at a cell
of grade at most `2`) and `W a' = visibilityReplace 3 3 (W a)` (at a cell of grade at most `3`,
not the natural cut), the catalogues decrease and the heights cover the catalogue values, then
strip freedom off the natural strip fails (`Label.orbitCode_stripPair`,
`Seed.not_isStripFreeOffNatural_of_stripPair`).  The lift at a grade `3` puts the code of its
state step in the catalogue, and the state step is literal on the context, so a prescription with
such a pair at context cells of grades `2` and `3` produces such a `W`. -/
theorem not_isStripFreeOffNatural_of_orbitCode {G : ℕ → Finset Label.{u}}
    {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop}
    (hA : ∀ R, A 3 R → A 2 R)
    (hcov : ∀ k, ∀ R ∈ (I.attachmentBase g).towerCat Γ A k, ∀ a,
      (I.attachment g).toCellScheme.grade a ≤ k → IsSelfVisible k (R a) → R a ∈ G k)
    {W : Fin (I.attachment g).card → Label.{u}}
    (hWC : orbitCode 3 W ∈ (I.attachmentBase g).towerCat Γ A 3)
    {a a' : Fin (I.attachment g).card} (ha : (I.attachment g).toCellScheme.grade a ≤ 2)
    (ha' : (I.attachment g).toCellScheme.grade a' ≤ 3) (h0 : W a ≠ ⊥)
    (hx : IsSelfVisible 2 (W a)) (hnv : ¬ IsSelfVisible 3 (W a))
    (hkey : visibilityReplace 3 3 (W a) = W a') (hnat : W a' ≠ gridPoint 3 0) :
    ¬ Scheme.IsStripFreeOffNatural G Γ 3 := by
  obtain ⟨hv, hlt⟩ := orbitCode_stripPair h0 hnv hkey
  have hok : IsOrbitKey 3 W (W a) := ⟨a, rfl, hnv⟩
  have h0' : W a' ≠ ⊥ := fun h ↦ h0 (visibilityReplace_eq_bot_iff.mp (hkey.trans h))
  have hvis' : IsSelfVisible 3 (W a') := by
    rw [← hkey]
    exact visibilityReplace_self_visibilityReplace_of_le le_rfl le_rfl _
  have hc : IsSelfVisible 3 (orbitCode 3 W a') := by
    rw [orbitCode_apply]
    exact (isSelfVisible_orbitMap_iff h0').mpr (.inr hvis')
  refine not_isStripFreeOffNatural_of_stripPair hA hcov hWC ha ha'
    (isSelfVisible_orbitCode_of_isOrbitKey hok hx) hc hv hlt fun he ↦ hnat ?_
  have hle : visibilityReplace 3 3 (orbitCode 3 W a') ≤ gridPoint 3 0 := by
    have hc' : visibilityReplace 3 3 (orbitCode 3 W a') = orbitCode 3 W a' := hc
    rw [hc', he]
  have hv' : visibilityReplace 3 3 (W a') = W a' := hvis'
  rw [← hv']
  exact (natural_of_visibilityReplace_orbitCode_le h0' hle).2.2

end Seed

end VaughtConjecture

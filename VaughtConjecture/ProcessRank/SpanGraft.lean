/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CappedDecoder

/-!
# Grafting a high tail onto a lawful labelling

Process rank `ω₁`, the finite span of mutual rigidity: a local lemma on lawful labellings.

**The graft.**  Let `S` be a scheme (finitely many cells, indexed by `Fin S.card`), let `x` and
`y` be labellings of its cells lawful below a pair `X`, let `c` be a cap self-visible at the grade
of `X`, and let `x` and `y` have the same **high set** below `X`: `c ≤ x d ↔ c ≤ y d` for every
cell `d` below `X`.  The graft `z` equal to `x` at the low cells and to `y` at the high cells is
lawful below `X` (`Scheme.GraftHighTailTarget`).  The statement is for schemes, whose cells are
finite in number: the proof takes the largest of finitely many low readings and uses the capped
decoder of a scheme (`Scheme.exists_cappedDecoder_below`).  At
the cap `⊥` every cell is high and `z = y`.  The intended proof:

* order and availability: a low availability witness of `x` stays low or becomes high, and a high
  witness of `y` stays high;
* locality at a low owner is that of `x`, since every high cell is read at the owner's label;
* locality at a high owner `o` of grade `k`: capped decoders `θ_x`, `θ_y` at `o` with the step
  suppressor at `k` (`Scheme.exists_cappedDecoder_below`); with `b` the largest replacement
  `vr k k` of the row entries of the low cells below `o`, the map equal to `min θ_x c` up to `b`
  and to `max θ_y c` above `b` is monotone and commutes with visibility replacement through the
  grade `k`, and reads every cell below `o` as `z` capped at `z o`.  It need not be a witness
  above `k`: interpolation off the zero set of `θ_x` (`Label.exists_isWitness_interpolation`)
  gives a witness with the same readings, since the required readings have exactly the bottom
  pattern of `θ_x`.

Proved (`Scheme.graftHighTail`).  The cap `⊥` is the case `z = y`.  For a cap other than `⊥`, a
cell read at `⊥` by `θ_x` is low with label `⊥`, so the interpolant is `⊥` exactly where the
readings are.  The cut `t ≤ b` is invariant under the replacements at thresholds `k' ≤ k` with
values `i ≤ k'`, since `b` is self-visible at `k`
(`Scheme.visibilityReplace_le_iff_le_of_isSelfVisible`).
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

/-- **Target: grafting a high tail.**  For a scheme `S`, two labellings `x` and `y` of its cells
lawful below `X` with the same high set below `X` at a cap `c` self-visible at the grade of `X`
give a labelling lawful below `X`: `y` at the high cells and `x` at the others.  Proved
(`Scheme.graftHighTail`). -/
def GraftHighTailTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Scheme.{u} n) (X : Finset (Fin n) × ℕ) (x y : Fin S.card → Label.{u})
    (c : Label.{u}), S.rows.IsLawfulBelow X (fun d ↦ x d) → S.rows.IsLawfulBelow X (fun d ↦ y d) →
    IsSelfVisible X.2 c → (∀ d ∈ S.toCellScheme.below X, c ≤ x d ↔ c ≤ y d) →
      S.rows.IsLawfulBelow X fun d ↦ if c ≤ x d then y d else x d

/-- **The cut at a self-visible bound is invariant under replacement**: for `b` self-visible at
`k`, `k' ≤ k` and `i ≤ k'`, a label lies below `b` exactly when its replacement does. -/
theorem visibilityReplace_le_iff_le_of_isSelfVisible {b t : Label.{u}} {k k' i : ℕ}
    (hb : IsSelfVisible k b) (hk : k' ≤ k) (hi : i ≤ k') :
    visibilityReplace k' i t ≤ b ↔ t ≤ b := by
  have hb' := hb.mono hk
  refine ⟨fun h ↦ ?_, fun h ↦ visibilityReplace_le_of_le hi hb' h⟩
  have h2 := visibilityReplace_le_of_le le_rfl hb' h
  rw [visibilityReplace_self_visibilityReplace hi] at h2
  exact (le_visibilityReplace (by omega) t).trans h2

/-- **Locality of the graft at a high owner**: at a cell `o` below `X` with `c ≤ x o`, for a cap
`c` other than `⊥`, the row of `o` transforms to the graft capped at its label `y o`.  The map
`min θ_x c` up to the largest replacement `b` of the low readings and `max θ_y c` above it,
interpolated off the zero set of `θ_x`, is the witness. -/
theorem graftHighTail_highOwner {n : ℕ} {S : Scheme.{u} n} {X : Finset (Fin n) × ℕ}
    {x y : Fin S.card → Label.{u}} {c : Label.{u}}
    (hx : S.rows.IsLawfulBelow X (fun d ↦ x d)) (hy : S.rows.IsLawfulBelow X (fun d ↦ y d))
    (hc : IsSelfVisible X.2 c) (hc0 : c ≠ ⊥)
    (hhigh : ∀ d ∈ S.toCellScheme.below X, c ≤ x d ↔ c ≤ y d) {o : Fin S.card}
    (ho : o ∈ S.toCellScheme.below X) (hoc : c ≤ x o) :
    TransformsTo (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex o) ↦
        S.toCellScheme.grade d) (S.rows.row o)
      (fun d ↦ min ((fun d ↦ if c ≤ x d then y d else x d) d.1)
        ((fun d ↦ if c ≤ x d then y d else x d) o)) := by
  classical
  have hyo : c ≤ y o := (hhigh o ho).mp hoc
  set k := S.toCellScheme.grade o with hk
  have hkX : k ≤ X.2 := ho.2
  have hck : IsSelfVisible k c := hc.mono hkX
  obtain ⟨θx, hθx, -, hθxr⟩ := exists_cappedDecoder_below hx ho rfl
  obtain ⟨θy, hθy, -, hθyr⟩ := exists_cappedDecoder_below hy ho rfl
  have hcomm {θ : Label.{u} → Label.{u}} (hθ : IsWitness (stepSuppressor k) θ) (t : Label.{u})
      {k' : ℕ} (hk' : k' ≤ k) {i : ℕ} (hi : i ≤ k') :
      θ (visibilityReplace k' i t) = visibilityReplace k' i (θ t) :=
    hθ.visibilityReplace_comm t k' (by rw [stepSuppressor_of_le hk']; exact le_top) i hi
  -- the low cells below `o` and the largest replacement of their readings
  set L : Finset (Fin S.card) := univ.filter fun d ↦
    d ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex o) ∧ ¬ c ≤ x d with hL
  set b : Label.{u} := L.sup fun d ↦ visibilityReplace k k (S.rowAt o d) with hb
  have hbv : IsSelfVisible k b :=
    Finset.sup_induction (isSelfVisible_bot _) (fun _ h₁ _ h₂ ↦ h₁.max h₂)
      fun _ _ ↦ isSelfVisible_visibilityReplace_self k _
  have hθyb : θy b ≤ c := by
    refine Finset.sup_induction (p := fun t ↦ θy t ≤ c) (by rw [hθy.map_bot]; exact bot_le)
      (fun a ha a' ha' ↦ by rw [hθy.monotone.map_max]; exact max_le ha ha') fun e he ↦ ?_
    obtain ⟨he₁, he₂⟩ := (mem_filter.mp he).2
    have heX : e ∈ S.toCellScheme.below X := CellScheme.Rows.mem_below_of_le he₁ ho
    have hye : y e < c := not_le.mp fun h ↦ he₂ ((hhigh e heX).mpr h)
    rw [hcomm hθy _ le_rfl le_rfl, hθyr e he₁]
    exact visibilityReplace_le_of_le le_rfl hck ((min_le_left _ _).trans hye.le)
  -- the glued map
  set f : Label.{u} → Label.{u} := fun t ↦ if t ≤ b then min (θx t) c else max (θy t) c with hf
  have hf0 : f ⊥ = ⊥ := by
    simp only [hf, bot_le, ite_true, hθx.map_bot, min_bot_left]
  have hfm : Monotone f := by
    intro t t' htt'
    simp only [hf]
    split_ifs with h₁ h₂ h₂
    · exact min_le_min_right _ (hθx.monotone htt')
    · exact (min_le_right _ _).trans (le_max_right _ _)
    · exact absurd (htt'.trans h₂) h₁
    · exact max_le_max_right _ (hθy.monotone htt')
  have hfc : ∀ t, ∀ k' ≤ k, ∀ i ≤ k',
      f (visibilityReplace k' i t) = visibilityReplace k' i (f t) := by
    intro t k' hk' i hi
    simp only [hf, visibilityReplace_le_iff_le_of_isSelfVisible hbv hk' hi]
    split_ifs
    · rw [hcomm hθx t hk' hi, visibilityReplace_min_of_isSelfVisible hi (hck.mono hk')]
    · rw [hcomm hθy t hk' hi, visibilityReplace_max hi, (hck.mono hk').visibilityReplace_eq]
  obtain ⟨ρ, hρ, hρ0, hρf⟩ := exists_isWitness_interpolation (m := k) hf0 hfm hfc
    (S := {t | θx t = ⊥}) (fun t t' htt' ht' ↦ le_bot_iff.mp (ht' ▸ hθx.monotone htt'))
    (fun t ht k' i hi ↦ hθx.apply_visibilityReplace_eq_bot ht k' hi)
  refine ⟨stepSuppressor k, ρ, hρ, fun d ↦ ?_⟩
  have hdk : S.toCellScheme.grade d ≤ k := d.2.2
  have hdX : (d : Fin S.card) ∈ S.toCellScheme.below X := CellScheme.Rows.mem_below_of_le d.2 ho
  simp only [stepSuppressor_of_le hdk, min_top_right, ite_eq_left hoc]
  rw [show S.rows.row o d = S.rowAt o d from (rowAt_of_mem d.2).symm]
  by_cases hθ0 : θx (S.rowAt o d) = ⊥
  · rw [hρ0 _ hθ0]
    have h := hθxr d d.2
    rw [hθ0, eq_comm, min_eq_bot] at h
    have hxd : x d = ⊥ := h.resolve_right fun h' ↦ hc0 (le_bot_iff.mp (h' ▸ hoc))
    have hdc : ¬ c ≤ x d := fun h' ↦ hc0 (le_bot_iff.mp (hxd ▸ h'))
    rw [ite_eq_right hdc, hxd, min_bot_left]
  have hfd : f (S.rowAt o d) ≠ ⊥ := by
    simp only [hf]
    split_ifs
    · rw [Ne, min_eq_bot, not_or]
      exact ⟨hθ0, hc0⟩
    · exact ne_bot_of_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hc0) (le_max_right _ _))
  rw [hρf _ hθ0 hfd]
  by_cases hdc : c ≤ x d
  · rw [ite_eq_left hdc]
    have hyd : c ≤ y d := (hhigh d hdX).mp hdc
    have hcmin : c ≤ min (y d) (y o) := le_min hyd hyo
    simp only [hf]
    split_ifs with hle
    · rw [hθxr d d.2, min_eq_right (le_min hdc hoc)]
      refine le_antisymm ?_ hcmin
      rw [← hθyr d d.2]
      exact (hθy.monotone hle).trans hθyb
    · rw [hθyr d d.2, max_eq_left hcmin]
  · rw [ite_eq_right hdc]
    have hxdc : x d < c := not_le.mp hdc
    have hdL : (d : Fin S.card) ∈ L := mem_filter.mpr ⟨mem_univ _, d.2, hdc⟩
    have hle : S.rowAt o d ≤ b := (le_visibilityReplace (by omega) _).trans
      (Finset.le_sup (f := fun d ↦ visibilityReplace k k (S.rowAt o d)) hdL)
    simp only [hf, ite_eq_left hle]
    rw [hθxr d d.2, min_eq_left (hxdc.le.trans hoc), min_eq_left hxdc.le,
      min_eq_left (hxdc.le.trans hyo)]

/-- **Grafting a high tail**: for a scheme, two labellings lawful below `X` with the same high set
below `X` at a cap self-visible at the grade of `X` give a lawful labelling below `X`, equal to the
second at the high cells and to the first at the others. -/
theorem graftHighTail : GraftHighTailTarget.{u} := by
  intro n S X x y c hx hy hc hhigh
  classical
  by_cases hc0 : c = ⊥
  · subst hc0
    simpa using hy
  obtain ⟨hxo, hxl, hxa⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hx
  obtain ⟨hyo, hyl, hya⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hy
  set z : Fin S.card → Label.{u} := fun d ↦ if c ≤ x d then y d else x d with hz
  have hzhi {d : Fin S.card} (h : c ≤ x d) : z d = y d := ite_eq_left h
  have hzlo {d : Fin S.card} (h : ¬ c ≤ x d) : z d = x d := ite_eq_right h
  change S.rows.IsLawfulBelow X (fun d ↦ z d)
  refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d hd ↦ ?_, fun o ho ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · -- order
    by_cases h : c ≤ x d
    · rw [hzhi h]; exact hyo d hd
    · rw [hzlo h]; exact hxo d hd
  · -- locality
    by_cases hoc : c ≤ x o
    · exact graftHighTail_highOwner hx hy hc hc0 hhigh ho hoc
    · have heq : (fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex o) ↦
          min (z d) (z o)) = fun d : S.toCellScheme.below (S.toCellScheme.gradedIndex o) ↦
          min (x d) (x o) := by
        funext d
        have hdX : (d : Fin S.card) ∈ S.toCellScheme.below X :=
          CellScheme.Rows.mem_below_of_le d.2 ho
        have hxo' : x o < c := not_le.mp hoc
        rw [hzlo hoc]
        by_cases hd : c ≤ x d
        · rw [hzhi hd, min_eq_right (hxo'.le.trans ((hhigh d hdX).mp hd)),
            min_eq_right (hxo'.le.trans hd)]
        · rw [hzlo hd]
      rw [heq]
      exact hxl o ho
  · -- availability
    have hs : s ∈ S.toCellScheme.below X := CellScheme.Rows.mem_below_of_scope_subset hst hg ht
    by_cases hsc : c ≤ x s
    · obtain ⟨u, hu, hle⟩ := hya s t ht hst hg
      have huX : u ∈ S.toCellScheme.below X := CellScheme.Rows.mem_below_of_le hu.le ht
      have hyu : c ≤ y u := ((hhigh s hs).mp hsc).trans hle
      refine ⟨u, hu, ?_⟩
      rw [hzhi hsc, hzhi ((hhigh u huX).mpr hyu)]
      exact hle
    · obtain ⟨u, hu, hle⟩ := hxa s t ht hst hg
      have huX : u ∈ S.toCellScheme.below X := CellScheme.Rows.mem_below_of_le hu.le ht
      refine ⟨u, hu, ?_⟩
      rw [hzlo hsc]
      by_cases huc : c ≤ x u
      · rw [hzhi huc]
        exact (not_le.mp hsc).le.trans ((hhigh u huX).mp huc)
      · rw [hzlo huc]
        exact hle

end VaughtConjecture.Scheme

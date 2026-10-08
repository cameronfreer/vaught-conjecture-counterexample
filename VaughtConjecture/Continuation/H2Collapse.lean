/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2ArityOne
import VaughtConjecture.Extension.CapTransport

/-!
# h2: donor raising by a band raise (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

**The band raise** (`H2.bandRaise B h c`): the label `c` on the band of labels above `B`, at least
`h` and below `c`; the identity elsewhere.  For `B` and `c` self-visible at `K` and either `h ≤ B`
or `h` self-visible at `K + 1`, it is a witness bounded by the grade `K` (`H2.isWitness_bandRaise`).

**Refined donor raising from capped lifts** (`H2.donorRaisingV_of_cappedLift`), at any grade `K`:
from a capped lift `W₁` of the served face with the root of the context face, the band raise with
`B` the replaced low maximum of `W₁` and `c` the frontier cap fixes the root (every root cell is a
low cell or a designated root top, at least `c`), keeps the agreement capped at `h`, and sends
every designated top at least `h` to at least `c` or keeps it at most `B`.  For a cap `h` above
`B` not self-visible at `K + 1`, the band raise above `h` itself leaves only the tops at exactly
`h`; that case is a separate hypothesis (`H2.TieAtCap`).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label

/-! ### The band raise -/

/-- Replacement at `k ≤ K` with value `i ≤ k` does not cross a label self-visible at `K` from
above. -/
theorem visibilityReplace_le_iff_of_isSelfVisible {K k i : ℕ} {B : Label.{u}}
    (hB : IsSelfVisible K B) (hk : k ≤ K) (hi : i ≤ k) (x : Label.{u}) :
    visibilityReplace k i x ≤ B ↔ x ≤ B := by
  refine ⟨fun hle ↦ (le_visibilityReplace (k := k) (i := k) (by omega) x).trans ?_,
    fun hle ↦ visibilityReplace_le_of_le hi (hB.mono hk) hle⟩
  have := visibilityReplace_le_of_le le_rfl (hB.mono hk) hle
  rw [visibilityReplace_visibilityReplace_of_le le_rfl] at this
  split_ifs at this with hik
  · exact this
  · obtain rfl : i = k := by omega
    exact this

/-- **The band raise**: `c` at the labels above `B`, at least `h` and below `c`. -/
noncomputable def bandRaise (B h c x : Label.{u}) : Label.{u} :=
  if B < x ∧ h ≤ x ∧ x < c then c else x

variable {B h c x : Label.{u}}

theorem le_bandRaise (B h c x : Label.{u}) : x ≤ bandRaise B h c x := by
  unfold bandRaise
  split_ifs with hx
  exacts [hx.2.2.le, le_rfl]

theorem bandRaise_of_mem (hx : B < x ∧ h ≤ x ∧ x < c) : bandRaise B h c x = c := ite_eq_left hx

theorem bandRaise_of_not_mem (hx : ¬ (B < x ∧ h ≤ x ∧ x < c)) : bandRaise B h c x = x :=
  ite_eq_right hx

theorem bandRaise_of_le (hx : x ≤ B) : bandRaise B h c x = x :=
  bandRaise_of_not_mem fun h' ↦ h'.1.not_ge hx

theorem bandRaise_of_ge (hx : c ≤ x) : bandRaise B h c x = x :=
  bandRaise_of_not_mem fun h' ↦ h'.2.2.not_ge hx

/-- The band raise does not change a label capped at `h`. -/
theorem min_bandRaise (B h c x : Label.{u}) : min (bandRaise B h c x) h = min x h := by
  unfold bandRaise
  split_ifs with hx
  · rw [min_eq_right (hx.2.1.trans hx.2.2.le), min_eq_right hx.2.1]
  · rfl

/-- **The band raise is a witness bounded by the grade `K`**, for `B` and `c` self-visible at `K`
and either `h ≤ B` or `h` self-visible at `K + 1`. -/
theorem isWitness_bandRaise {K : ℕ} (hB : IsSelfVisible K B) (hc : IsSelfVisible K c)
    (hh : h ≤ B ∨ IsSelfVisible (K + 1) h) : IsWitness (stepSuppressor K) (bandRaise B h c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := bandRaise_of_not_mem fun h' ↦ not_lt_bot h'.1
  monotone := by
    intro x y hxy
    unfold bandRaise
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact not_lt.mp fun hyc ↦ h2 ⟨h1.1.trans_le hxy, h1.2.1.trans hxy, hyc⟩
    · exact hxy.trans h2.2.2.le
    · exact hxy
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · have hlow : ∀ y, (B < visibilityReplace k i y ∧ h ≤ visibilityReplace k i y) ↔
          (B < y ∧ h ≤ y) := by
        intro y
        have e1 : B < visibilityReplace k i y ↔ B < y := by
          rw [← not_le, ← not_le, visibilityReplace_le_iff_of_isSelfVisible hB hk hi]
        rcases hh with hhB | hh3
        · constructor
          · rintro ⟨h1, -⟩
            exact ⟨e1.mp h1, hhB.trans (e1.mp h1).le⟩
          · rintro ⟨h1, -⟩
            exact ⟨e1.mpr h1, hhB.trans (e1.mpr h1).le⟩
        · rw [e1, hh3.le_visibilityReplace_iff hk hi]
      have hcc : visibilityReplace k i c = c := (hc.mono hk).visibilityReplace_eq i
      by_cases hJ : B < x ∧ h ≤ x ∧ x < c
      · rw [bandRaise_of_mem hJ, hcc]
        have hle : visibilityReplace k i x ≤ c :=
          visibilityReplace_le_of_le hi (hc.mono hk) hJ.2.2.le
        obtain ⟨h1, h2⟩ := (hlow x).mpr ⟨hJ.1, hJ.2.1⟩
        rcases hle.lt_or_eq with hlt | heq
        · exact bandRaise_of_mem ⟨h1, h2, hlt⟩
        · rw [heq]
          exact bandRaise_of_ge le_rfl
      · rw [bandRaise_of_not_mem hJ]
        refine bandRaise_of_not_mem fun ⟨h1, h2, h3⟩ ↦ ?_
        obtain ⟨h1', h2'⟩ := (hlow x).mp ⟨h1, h2⟩
        have hxc : c ≤ x := not_lt.mp fun hxc ↦ hJ ⟨h1', h2', hxc⟩
        exact h3.not_ge (hcc ▸ monotone_visibilityReplace hi hxc)
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      have hx0 : x = ⊥ := le_bot_iff.mp (hx ▸ le_bandRaise B h c x)
      subst hx0
      rw [visibilityReplace_bot, hx, visibilityReplace_bot]

/-! ### Refined donor raising from capped lifts -/

section Raising

variable {ιC ιD ιR : Type*} {rc : ιR → ιC} {rd : ιR → ιD} {K : ℕ}

/-- **The capped-lift provision**: a lawful served face `R` and a lawful context face `f` agreeing
on the root capped at `h` (self-visible at `K`) have a lawful served face with the root of `f`,
agreeing with `R` capped at `h`. -/
def HasCappedLifts (rc : ιR → ιC) (rd : ιR → ιD) (K : ℕ) (C : (ιC → Label.{u}) → Prop)
    (D : (ιD → Label.{u}) → Prop) : Prop :=
  ∀ {h : Label.{u}}, IsSelfVisible K h → ∀ {R : ιD → Label.{u}} {f : ιC → Label.{u}}, D R → C f →
    (∀ x, min (f (rc x)) h = min (R (rd x)) h) →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ ∀ d, min (W d) h = min (R d) h

/-- **The tie at a cap not self-visible at `K + 1`**: the refined donor raising at a cap `h` not
self-visible at `K + 1`, given a capped lift `W₁` whose replaced low maximum is below `h` and whose
designated tops at least `h` are at least `c` or exactly `h` (the case the band raise leaves
open). -/
def TieAtCap (rc : ιR → ιC) (rd : ιR → ιD) (K : ℕ) (C : (ιC → Label.{u}) → Prop)
    (D : (ιD → Label.{u}) → Prop) (A : Set ιR) (Lo Tops : Finset ιD) : Prop :=
  ∀ {h c : Label.{u}}, IsSelfVisible K h → ¬ IsSelfVisible (K + 1) h → IsSelfVisible K c →
    ∀ {R : ιD → Label.{u}} {f : ιC → Label.{u}} {W₁ : ιD → Label.{u}}, D R → C f →
    (∀ x, min (f (rc x)) h = min (R (rd x)) h) → (∀ a ∈ A, c ≤ f (rc a)) →
    D W₁ → (∀ x, W₁ (rd x) = f (rc x)) → (∀ d, min (W₁ d) h = min (R d) h) →
    (∀ t ∈ Tops, h ≤ R t → c ≤ W₁ t ∨ W₁ t = h) → visibilityReplace K K (Lo.sup W₁) < h →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t ∈ Tops, h ≤ R t → c ≤ W t ∨ W t ≤ visibilityReplace K K (Lo.sup W)

/-- **Refined donor raising from capped lifts and the band raise**, at any grade `K`: every root
cell is a low cell or a designated root top, the served faces are closed under witnesses bounded by
`K` above the identity, and the tie at caps not self-visible at `K + 1` holds. -/
theorem donorRaisingV_of_cappedLift {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {A : Set ιR} {Lo Tops : Finset ιD}
    (hlift : HasCappedLifts rc rd K C D)
    (hmap : ∀ {ν : Label.{u} → Label.{u}}, IsWitness (stepSuppressor K) ν → (∀ x, x ≤ ν x) →
      ∀ {W : ιD → Label.{u}}, D W → D fun d ↦ ν (W d))
    (hroot : ∀ x, rd x ∈ Lo ∨ x ∈ A) (htie : TieAtCap rc rd K C D A Lo Tops) :
    DonorRaisingV rc rd K C D A Lo Tops := by
  intro h c hh hc R f hR hf hagr hA
  obtain ⟨W₁, hW₁, hW₁r, hW₁R⟩ := hlift hh hR hf hagr
  set B := visibilityReplace K K (Lo.sup W₁) with hBdef
  have hW₁t : ∀ t, h ≤ R t → h ≤ W₁ t := fun t hRt ↦ by
    have e := hW₁R t
    rw [min_eq_right hRt] at e
    exact min_eq_right_iff.mp e
  by_cases hgood : h ≤ B ∨ IsSelfVisible (K + 1) h
  swap
  · -- the band raise above `h` itself, leaving the tops at exactly `h`
    push Not at hgood
    obtain ⟨hBh, hh3⟩ := hgood
    have hlo : ∀ d ∈ Lo, W₁ d < h := fun d hd ↦
      ((Finset.le_sup (f := W₁) hd).trans (le_visibilityReplace (by omega) _)).trans_lt hBh
    refine htie hh hh3 hc hR hf hagr hA
      (hmap (isWitness_bandRaise hh hc (.inl le_rfl)) (le_bandRaise h h c) hW₁) (fun x ↦ ?_)
      (fun d ↦ ?_) (fun t _ hRt ↦ ?_) ?_
    · rw [hW₁r]
      rcases hroot x with hx | hx
      · refine bandRaise_of_le ?_
        rw [← hW₁r]
        exact (hlo _ hx).le
      · exact bandRaise_of_ge (hA x hx)
    · rw [min_bandRaise, hW₁R]
    · by_cases hJ : h < W₁ t ∧ h ≤ W₁ t ∧ W₁ t < c
      · exact .inl (bandRaise_of_mem hJ).ge
      · rw [bandRaise_of_not_mem hJ]
        rcases (hW₁t t hRt).lt_or_eq with hlt | heq
        · exact .inl (not_lt.mp fun hc' ↦ hJ ⟨hlt, hlt.le, hc'⟩)
        · exact .inr heq.symm
    · rw [Finset.sup_congr rfl fun d hd ↦ bandRaise_of_le (B := h) (h := h) (c := c) (hlo d hd).le]
      exact hBh
  have hB : IsSelfVisible K B := visibilityReplace_self_visibilityReplace le_rfl _
  have hν := isWitness_bandRaise hB hc hgood
  refine ⟨fun d ↦ bandRaise B h c (W₁ d), hmap hν (le_bandRaise B h c) hW₁, fun x ↦ ?_,
    fun d ↦ ?_, fun t _ hRt ↦ ?_⟩
  · change bandRaise B h c (W₁ (rd x)) = f (rc x)
    rw [hW₁r]
    rcases hroot x with hx | hx
    · refine bandRaise_of_le ?_
      rw [← hW₁r]
      exact (Finset.le_sup (f := W₁) hx).trans (le_visibilityReplace (by omega) _)
    · exact bandRaise_of_ge (hA x hx)
  · change min (bandRaise B h c (W₁ d)) h = min (R d) h
    rw [min_bandRaise, hW₁R]
  · have hsup : B ≤ visibilityReplace K K (Lo.sup fun d ↦ bandRaise B h c (W₁ d)) :=
      monotone_visibilityReplace le_rfl
        (Finset.sup_mono_fun fun d _ ↦ le_bandRaise B h c (W₁ d))
    by_cases hJ : B < W₁ t ∧ h ≤ W₁ t ∧ W₁ t < c
    · left
      change c ≤ bandRaise B h c (W₁ t)
      rw [bandRaise_of_mem hJ]
    · by_cases hle : W₁ t ≤ B
      · right
        change bandRaise B h c (W₁ t) ≤ _
        rw [bandRaise_of_le hle]
        exact hle.trans hsup
      · left
        have : c ≤ W₁ t := not_lt.mp fun hlt ↦ hJ ⟨not_le.mp hle, hW₁t t hRt, hlt⟩
        exact this.trans (le_bandRaise _ _ _ _)

end Raising

/-! ### Capped lifts at a legal stage type from a face -/

/-- **Capped lifts from a face of a legal stage type**: for a face on `n > 0` points, `n < K ≤ k`,
every cell of grade at most `K`, and a cap `h` self-visible at `K`, a lawful labelling `L` and a
lawful labelling `y` of the face agreeing with `L` capped at `h` have a lawful labelling with face
`y`, agreeing with `L` capped at `h` (bountifulness). -/
theorem exists_isLawful_cappedLift_face {α : Ordinal.{u}} {k n K : ℕ} {t : StageType.{u} α k}
    (hleg : t.IsLegal) {g : Fin n ↪ Fin k} {s : StageType.{u} α n}
    (ht : StageType.restrictFace g t = some s) (hn : 0 < n) (hnK : n < K) (hKk : K ≤ k)
    (hK : ∀ d, t.toCellScheme.grade d ≤ K) {h : Label.{u}} (hh : IsSelfVisible K h)
    {L : Fin t.card → Label.{u}} (hL : t.rows.IsLawful L) {y : Fin s.card → Label.{u}}
    (hy : s.rows.IsLawful y) (hroot : ∀ i, min (y i) h = min (L (StageType.faceCell ht i)) h) :
    ∃ W : Fin t.card → Label.{u}, t.rows.IsLawful W ∧ (∀ i, W (StageType.faceCell ht i) = y i) ∧
      ∀ d, min (W d) h = min (L d) h := by
  classical
  obtain ⟨hf, -⟩ := (StageType.restrictFace_eq_some_iff (t := t) (f := g)).mp ht
  have he := StageType.comap_toScheme_of_restrictFace ht
  have hinj : Function.Injective (StageType.faceCell ht) := by
    intro i j hij
    have := (t.toScheme.cellMap g).injective hij
    exact Fin.cast_injective _ this
  set x : Fin t.card → Label.{u} := Function.extend (StageType.faceCell ht) y (fun _ ↦ ⊥)
  have hx (i : Fin s.card) : x (StageType.faceCell ht i) = y i := hinj.extend_apply _ _ i
  have hpX : t.rows.IsLawfulBelow (Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n))
      (fun d ↦ x d) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ x).mp ?_
    convert hy.isLawfulBelow ((univ : Finset (Fin n)), n) using 2 with i
    exact hx i.1
  have hXY : Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n) ≤
      ((univ : Finset (Fin k)), K) := ⟨subset_univ _, hnK.le⟩
  have hX : Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n) ∈
      t.toCellScheme.gradedFaces := ⟨hf, hn, by simp⟩
  have hY : ((univ : Finset (Fin k)), K) ∈ t.toCellScheme.gradedFaces :=
    ⟨t.univ_mem_faces, hn.trans hnK, by simpa using hKk⟩
  have hlift := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (hleg.isBountiful hX hY hXY) h hh (fun d ↦ x d) (fun d ↦ L d) hpX
    (hL.isLawfulBelow _) (fun d ↦ ?_)
  rotate_left
  · have hvis : d.1 ∈ t.toScheme.visibleCells g := by
      refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
      have hy' : y ∈ (univ : Finset (Fin n)).map g := d.2.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hvis
    change min (L d.1) h = min (x d.1) h
    rw [← hi]
    change min (L (StageType.faceCell ht i)) h = min (x (StageType.faceCell ht i)) h
    rw [hx]
    exact (hroot i).symm
  obtain ⟨q', hq', hq'L, hq'p⟩ := hlift
  have hmem (d : Fin t.card) : d ∈ t.toCellScheme.below ((univ : Finset (Fin k)), K) :=
    ⟨subset_univ _, hK d⟩
  refine ⟨fun d ↦ q' ⟨d, hmem d⟩, hq'.isLawful fun d ↦ hmem d, fun i ↦ ?_, fun d ↦ ?_⟩
  · have hvX : StageType.faceCell ht i ∈ t.toCellScheme.below
        (Prod.map (Finset.map g) id ((univ : Finset (Fin n)), n)) :=
      (CellScheme.mem_below _).mpr
        ⟨show t.toCellScheme.scope (StageType.faceCell ht i) ⊆ (univ : Finset (Fin n)).map g by
          rw [StageType.scope_faceCell]; exact map_subset_map.mpr (subset_univ _),
        show t.toCellScheme.grade (StageType.faceCell ht i) ≤ n by
          rw [StageType.grade_faceCell]; exact s.grade_le i⟩
    have := hq'p ⟨_, hvX⟩
    change q' ⟨StageType.faceCell ht i, _⟩ = x (StageType.faceCell ht i) at this
    exact this.trans (hx i)
  · exact hq'L ⟨d, hmem d⟩

/-- **Capped lifts between two legal stage types sharing a face** (`H2.HasCappedLifts`), lifting
into the second. -/
theorem hasCappedLifts_of_isLegal {α : Ordinal.{u}} {k n K : ℕ} {t' : StageType.{u} α k}
    {g : Fin n ↪ Fin k} {s : StageType.{u} α n} (ht : StageType.restrictFace g t' = some s)
    {tb : StageType.{u} α k} (htbleg : tb.IsLegal) (htb : StageType.restrictFace g tb = some s)
    (hn : 0 < n) (hnK : n < K) (hKk : K ≤ k) (hK : ∀ d, tb.toCellScheme.grade d ≤ K) :
    HasCappedLifts (StageType.faceCell ht) (StageType.faceCell htb) K t'.rows.IsLawful
      tb.rows.IsLawful := fun hh _ _ hR hf hagr ↦
  exists_isLawful_cappedLift_face htbleg htb hn hnK hKk hK hh hR
    (StageType.isLawful_comp_faceCell ht hf) hagr

end VaughtConjecture.H2

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Band
import VaughtConjecture.Stage.Threshold
import VaughtConjecture.Stage.TopFree

/-!
# Marked caps: forced thresholds are read by the row of a top cap

Roadmap, Layer 3 ((R3) of the table of 3.4: the hollow context, with its private cap and marker;
3.1: the splice of two witnesses).  Everything here concerns labels and stage types only: no
realization and no model is involved.

Throughout, `β` is a limit stage and `α ≥ β + ω`; in the application `β = λ_ξ` and
`α = λ_{ξ+1}` are consecutive block stages.

**The splice of two witnesses** (`Label.TransformsTo.splice_bandMap`, compiled in this repository
(theorem named)).  On a finite family of cells of grades at most `K`, let a source `e` transform to
`q`, whose values are below `β` or the formal top, and to `r`, which is at least `μ` (zero or a
limit) wherever `q` is the formal top.  Then `e` transforms to the labelling that is `q` where `q`
is below `β` and the band map from `μ` to `β` at `K` of `r` where `q` is the formal top.  The
shifter keeps the values of the first shifter below `β`, capped at a cutoff `c`, and otherwise
applies the band map to the values of the second shifter at least `μ` and sends the rest to `c`;
the suppressor is bottom above `K`, the band map of the second suppressor where the first is the
formal top and the second is at least `μ`, and a smaller cutoff `c₀ < c` elsewhere.  The guard
of the commutation law with visibility replacement reduces to the guards of the two witnesses,
except where the second shifter exceeds its suppressor; there both band values are `β + K`
(`Label.bandMap_lt_bandMap`).  This is the transformation lemma that replaces the transitivity
step of the printed proof of [Kni26, Lemma 5.3.5] for the rows other than the top-witness row
(roadmap, Layer 3, 3.1); the band rule (`Label.IsWitness.transformsTo_bandMap`) is the
top-witness row.

**Top caps and markers.**  A **top cap** of a stage type `q` (`StageType.IsTopCap`) is a cell of
full scope labelled `⊤` whose grade `N` is the largest grade of a cell labelled `⊤`; every cell
labelled `⊤` lies below it (`StageType.IsTopCap.mem_below`), and a legal stage type that is not
top-free has one (`StageType.exists_isTopCap`, from completeness and availability).  A **marker**
of a cell `c` (`StageType.IsMarker`) is a cell below `c` labelled `⊤` at which the row of `c`, read
with `Scheme.rowAt`, is least among the cells below `c` labelled `⊤`; every cell labelled `⊤` has
one (`StageType.exists_isMarker`, no hypothesis).

**The band lift** (`StageType.IsMarker.exists_lift`, compiled in this repository (theorem named)).
For a legal `q` at `β` with a top cap `c` of grade `N` and a marker `r`, the row of `c` reads `r`
at an ordinal `μ + j` (`μ` zero or a limit), and the labelling equal to `q` below `β` and to the
band map from `μ` to `β` at `N` of the row of `c` at the cells labelled `⊤` is a lawful lift of
`q` to `α`.  Order: the rows are orderly.  Availability at a cell labelled `⊤`: availability of
the row of `c` (lawful below `c` by consistency), whose cell is labelled `⊤` by locality of `q` at
`c`.  Locality at a cell `s` labelled `⊤`: the splice of locality of `q` at `s` with locality at
`s` of the row of `c`.  The other cells keep the laws of `q`.

**Forcing is read by the rows** (`StageType.IsMarker.visibilityReplace_rowAt_le`,
`StageType.ForcesThreshold.visibilityReplace_rowAt_le`, compiled in this repository (theorem
named)).  Cover-hollowness reads the provisional values of the tops through forcing (every lift of
a rooted cover); the hollow argument reads them through the row of a top cap.  The implication
holds: if `(q, f)` forces the threshold `L` at a cell of the root labelled `⊤`, transported to the
cell `e` of `q`, then for every top cap `c` of grade `N` and every marker `r` of `c`, `L ≤ N` and
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`.  The band lift has the label `β + min j' N`
at `e` when the row of `c` reads `e` in the block of the marker, at `μ + j'`, and `β + N`
otherwise; forcing `L` makes it at least `β + L`.

**The marked-cap context** (`StageType.IsMarkedCapContext`, defined in this repository; acquisition
and determination open).  A stage type `t'` on `k` points is a marked-cap context along
`h : Fin n ↪ Fin k` when it has a top cap `c` of grade `N > n + 1` and a marker `r` of `c` with
`visibilityReplace N (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a` at every cell `a` of the root (visible
through `h`) labelled `⊤`.  The finite step from forcing is compiled: a legal rooted cover with a
top cap of grade above `n + 1` that forces `n + 1` at every cell of its root labelled `⊤` is a
marked-cap context (`StageType.isMarkedCapContext_of_forcesThreshold`).  A marked-cap context is
not top-free (`StageType.IsMarkedCapContext.not_isTopFree`), so a context on no points is not one
(`StageType.not_isMarkedCapContext_of_zero`), and neither is a context whose cells labelled `⊤`
have grades at most `n + 1` (`StageType.not_isMarkedCapContext_of_grade_le`).  The
statements with the top grade, the form at a cover-hollow realization, and the exclusion of the
determination counterexamples are in `VaughtConjecture.Continuation.MarkedCap`.

Neither acquisition (`Realization.HollowAcquisition` for this predicate) nor determination
(`Realization.SchemeDetermination` or `Realization.CutoffDetermination` for it) is stated or
proved here, and nothing here proves or reduces (R3).

## Placement

This file belongs to Layer 1 of `roadmap/README.md`; its statements about labels belong to
`Label/Band`.

## References

The band map and the band rule are the post-composition in the proof of [Kni26, Lemma 5.3.5];
the transformation relation is [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Order
open scoped Ordinal

namespace Label

/-! ### The splice of two witnesses -/

section Splice

variable {D : Type*} {grade : D → ℕ} {e q r T : D → Label.{u}} {β μ : Ordinal.{u}} {K : ℕ}

/-- A label between an ordinal and a stage is an ordinal below the stage. -/
private theorem exists_coe_eq_of_le_of_lt {x : Label.{u}} {o : Ordinal.{u}}
    (h₀ : (o : Label.{u}) ≤ x) (h : x < β) : ∃ ν : Ordinal.{u}, x = ν ∧ ν < β := by
  induction x using recBotCoeTop with
  | bot => exact absurd h₀ (not_le.mpr (WithBot.bot_lt_coe _))
  | coe ν => exact ⟨ν, rfl, WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)⟩
  | top => exact absurd h (not_lt.mpr le_top)

/-- On the labels at least `μ`, the band map at `K` keeps self-visibility at every `n ≤ K`. -/
theorem isSelfVisible_bandMap (hβ : IsSuccPrelimit β) (hμ : IsSuccPrelimit μ) {n : ℕ}
    (hn : n ≤ K) {y : Label.{u}} (hy : (μ : Label.{u}) ≤ y) (hv : IsSelfVisible n y) :
    IsSelfVisible n (bandMap β μ K y) := by
  unfold IsSelfVisible
  rw [← bandMap_visibilityReplace hβ hμ hn le_rfl hy, hv.visibilityReplace_eq]

/-- **The band map is strictly increasing below `μ + K`**: if `μ ≤ z < μ + K` and `z < y`, then
the band map at `K` is larger at `y` than at `z`. -/
theorem bandMap_lt_bandMap {y z : Label.{u}} (hz : (μ : Label.{u}) ≤ z)
    (hzK : z < ((μ + K : Ordinal.{u}) : Label.{u})) (hzy : z < y) :
    bandMap β μ K z < bandMap β μ K y := by
  obtain ⟨ν, rfl, -⟩ := exists_coe_eq_of_le_of_lt hz hzK
  have hν₁ : μ ≤ ν := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hz)
  have hν₂ : ν < μ + K := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hzK)
  obtain ⟨j, rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hν₁
    (hν₂.trans (add_lt_add_right (Ordinal.natCast_lt_omega0 K) μ))
  have hjK : j < K := by
    have := (add_lt_add_iff_left μ).mp hν₂
    exact_mod_cast this
  have hy : ((μ + (j + 1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤ y := by
    rw [Nat.cast_add_one, ← add_assoc]
    exact not_lt.mp fun h ↦ hzy.not_ge (lt_coe_add_one_iff.mp h)
  refine lt_of_lt_of_le ?_ (monotone_bandMap β μ K hy)
  rw [bandMap_coe_add_natCast, bandMap_coe_add_natCast, min_eq_left hjK.le,
    min_eq_left (Nat.succ_le_of_lt hjK)]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ((add_lt_add_iff_left β).mpr
    (by exact_mod_cast j.lt_succ_self)))

/-- **The splice of two witnesses with the same source.**  Let `β` be a limit and `μ` zero or a
limit, and let the family of cells be finite with all grades at most `K`.  Let the source `e`
transform to `q`, whose values are below `β` or the formal top, and to `r`, which is at least `μ`
at every cell where `q` is the formal top.  Then `e` transforms to every labelling `T` that agrees
with `q` where `q` is below `β` and is the band map of `r` (from `μ` to `β` at `K`) where `q` is
the formal top. -/
theorem TransformsTo.splice_bandMap [Finite D] (hβ : IsSuccLimit β) (hμ : IsSuccPrelimit μ)
    (hgr : ∀ d, grade d ≤ K) (h₁ : TransformsTo grade e q) (h₂ : TransformsTo grade e r)
    (hq : ∀ d, q d < β ∨ q d = ⊤) (hr : ∀ d, q d = ⊤ → (μ : Label.{u}) ≤ r d)
    (hlow : ∀ d, q d < β → T d = q d) (htop : ∀ d, q d = ⊤ → T d = bandMap β μ K (r d)) :
    TransformsTo grade e T := by
  classical
  obtain ⟨g₁, σ₁, hw₁, heq₁⟩ := h₁
  obtain ⟨g₂, σ₂, hw₂, heq₂⟩ := h₂
  have hβ' := hβ.isSuccPrelimit
  have h0β : ((0 : Ordinal.{u}) : Label.{u}) < β :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hβ.pos)
  -- two cutoffs `c₀ < c` below `β`, self-visible at `K`, with `c₀` above the values of `q` below
  -- `β`
  obtain ⟨c₀', h0c₀, hc₀β, hc₀K, hbd⟩ := exists_isSelfVisible_bound hβ' K h0β q
  obtain ⟨ν₀, rfl, hν₀β⟩ := exists_coe_eq_of_le_of_lt h0c₀ hc₀β
  obtain ⟨ν, hν₀ν, hνβ, hνK⟩ := exists_lt_lt_isSelfVisible hβ' hν₀β K
  have hc₀c : (ν₀ : Label.{u}) < ν := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hν₀ν)
  have hcβ : (ν : Label.{u}) < β := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hνβ)
  have hcband (y : Label.{u}) (hy : (μ : Label.{u}) ≤ y) : (ν : Label.{u}) < bandMap β μ K y :=
    hcβ.trans_le (coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le hy).ne')
  set σ : Label.{u} → Label.{u} := fun x ↦
    if σ₁ x < β then min (σ₁ x) ν
    else if (μ : Label.{u}) ≤ σ₂ x then bandMap β μ K (σ₂ x) else ν with hσdef
  set g : ℕ → Label.{u} := fun n ↦
    if K < n then ⊥
    else if g₁ n = ⊤ then (if (μ : Label.{u}) ≤ g₂ n then bandMap β μ K (g₂ n) else ν₀)
    else min (g₁ n) ν₀ with hgdef
  -- the three values of the shifter
  have hσlow (x : Label.{u}) (hx : σ₁ x < β) : σ x = min (σ₁ x) ν := ite_eq_left hx
  have hσband (x : Label.{u}) (hx : ¬ σ₁ x < β) (h2 : (μ : Label.{u}) ≤ σ₂ x) :
      σ x = bandMap β μ K (σ₂ x) :=
    (ite_eq_right hx).trans (ite_eq_left h2)
  have hσc (x : Label.{u}) (hx : ¬ σ₁ x < β) (h2 : ¬ (μ : Label.{u}) ≤ σ₂ x) : σ x = ν :=
    (ite_eq_right hx).trans (ite_eq_right h2)
  -- the four values of the suppressor
  have hgK (n : ℕ) (hn : K < n) : g n = ⊥ := ite_eq_left hn
  have hgB (n : ℕ) (hn : n ≤ K) (h1 : g₁ n = ⊤) (h2 : (μ : Label.{u}) ≤ g₂ n) :
      g n = bandMap β μ K (g₂ n) :=
    (ite_eq_right (not_lt.mpr hn)).trans ((ite_eq_left h1).trans (ite_eq_left h2))
  have hgC (n : ℕ) (hn : n ≤ K) (h1 : g₁ n = ⊤) (h2 : ¬ (μ : Label.{u}) ≤ g₂ n) : g n = ν₀ :=
    (ite_eq_right (not_lt.mpr hn)).trans ((ite_eq_left h1).trans (ite_eq_right h2))
  have hgA (n : ℕ) (hn : n ≤ K) (h1 : g₁ n ≠ ⊤) : g n = min (g₁ n) ν₀ :=
    (ite_eq_right (not_lt.mpr hn)).trans (ite_eq_right h1)
  have hσge (x : Label.{u}) (hx : ¬ σ₁ x < β) : (ν : Label.{u}) ≤ σ x := by
    by_cases h2 : (μ : Label.{u}) ≤ σ₂ x
    · rw [hσband x hx h2]
      exact (hcband _ h2).le
    · rw [hσc x hx h2]
  have hgge (n : ℕ) (hn : n ≤ K) (h1 : g₁ n = ⊤) : (ν₀ : Label.{u}) ≤ g n := by
    by_cases h2 : (μ : Label.{u}) ≤ g₂ n
    · rw [hgB n hn h1 h2]
      exact (hc₀c.trans (hcband _ h2)).le
    · rw [hgC n hn h1 h2]
  have hw : IsWitness g σ := by
    refine ⟨fun n n' hnn' ↦ ?_, fun n ↦ ?_, ?_, fun x y hxy ↦ ?_, fun x k hx i hi ↦ ?_⟩
    · -- the suppressor is antitone
      by_cases hn' : K < n'
      · rw [hgK n' hn']
        exact bot_le
      have hn'K : n' ≤ K := not_lt.mp hn'
      have hn : n ≤ K := hnn'.trans hn'K
      by_cases h1' : g₁ n' = ⊤
      · have h1 : g₁ n = ⊤ := top_le_iff.mp (h1' ▸ hw₁.antitone hnn')
        by_cases h2' : (μ : Label.{u}) ≤ g₂ n'
        · rw [hgB n' hn'K h1' h2', hgB n hn h1 (h2'.trans (hw₂.antitone hnn'))]
          exact monotone_bandMap β μ K (hw₂.antitone hnn')
        · rw [hgC n' hn'K h1' h2']
          exact hgge n hn h1
      · have hle : g n' ≤ ν₀ := by
          rw [hgA n' hn'K h1']
          exact min_le_right _ _
        by_cases h1 : g₁ n = ⊤
        · exact hle.trans (hgge n hn h1)
        · rw [hgA n' hn'K h1', hgA n hn h1]
          exact min_le_min_right _ (hw₁.antitone hnn')
    · -- every value of the suppressor is self-visible at its grade
      by_cases hn : K < n
      · rw [hgK n hn]
        exact isSelfVisible_bot n
      have hnK : n ≤ K := not_lt.mp hn
      by_cases h1 : g₁ n = ⊤
      · by_cases h2 : (μ : Label.{u}) ≤ g₂ n
        · rw [hgB n hnK h1 h2]
          exact isSelfVisible_bandMap hβ' hμ hnK h2 (hw₂.isSelfVisible n)
        · rw [hgC n hnK h1 h2]
          exact hc₀K.mono hnK
      · rw [hgA n hnK h1]
        exact (hw₁.isSelfVisible n).min (hc₀K.mono hnK)
    · -- the shifter fixes bottom
      rw [hσlow ⊥ (by rw [hw₁.map_bot]; exact WithBot.bot_lt_coe _), hw₁.map_bot]
      exact min_eq_left bot_le
    · -- the shifter is monotone
      by_cases hy : σ₁ y < β
      · have hx : σ₁ x < β := (hw₁.monotone hxy).trans_lt hy
        rw [hσlow x hx, hσlow y hy]
        exact min_le_min_right _ (hw₁.monotone hxy)
      by_cases hx : σ₁ x < β
      · exact (hσlow x hx ▸ min_le_right _ _).trans (hσge y hy)
      by_cases h2x : (μ : Label.{u}) ≤ σ₂ x
      · have h2y : (μ : Label.{u}) ≤ σ₂ y := h2x.trans (hw₂.monotone hxy)
        rw [hσband x hx h2x, hσband y hy h2y]
        exact monotone_bandMap β μ K (hw₂.monotone hxy)
      · rw [hσc x hx h2x]
        exact hσge y hy
    · -- the shifter commutes with visibility replacement under the guard
      rcases lt_or_ge K k with hk | hk
      · -- above `K` the suppressor is bottom, so `σ x = ⊥`, hence `σ₁ x = ⊥`
        rw [hgK k hk, le_bot_iff] at hx
        have hx1 : σ₁ x < β := by
          by_contra h
          exact (WithBot.bot_lt_coe _).ne' (le_bot_iff.mp (hx ▸ hσge x h))
        rw [hσlow x hx1] at hx
        have hx1' : σ₁ x = ⊥ :=
          (min_eq_bot.mp hx).resolve_right (WithBot.bot_lt_coe _).ne'
        have hc := hw₁.visibilityReplace_comm x k (hx1' ▸ bot_le) i hi
        rw [hx1', visibilityReplace_bot] at hc
        rw [hσlow _ (hc ▸ WithBot.bot_lt_coe _), hc, hσlow x hx1, hx1', min_eq_left bot_le,
          visibilityReplace_bot]
      have hsub (y : Label.{u}) (hy : σ₁ y < β) (hyg : σ₁ y ≤ g₁ k) :
          σ (visibilityReplace k i y) = visibilityReplace k i (σ y) := by
        have hc := hw₁.visibilityReplace_comm y k hyg i hi
        have hlt : σ₁ (visibilityReplace k i y) < β := by
          rw [hc, visibilityReplace_lt_iff hβ']
          exact hy
        rw [hσlow _ hlt, hσlow y hy, hc]
        exact (visibilityReplace_min_of_isSelfVisible hi (hνK.mono hk) _).symm
      by_cases hx1 : σ₁ x < β
      · refine hsub x hx1 ?_
        by_cases hg1 : g₁ k = ⊤
        · rw [hg1]
          exact le_top
        rw [hgA k hk hg1, hσlow x hx1] at hx
        have hxc : σ₁ x < ν := by
          by_contra h
          rw [min_eq_right (not_lt.mp h)] at hx
          exact (hx.trans (min_le_right _ _)).not_gt hc₀c
        rw [min_eq_left hxc.le] at hx
        exact hx.trans (min_le_left _ _)
      -- here `σ₁ x ≥ β`, so the guard forces `g₁ k = ⊤` and `μ ≤ g₂ k`
      have hcx : (ν : Label.{u}) ≤ σ x := hσge x hx1
      have hg1 : g₁ k = ⊤ := by
        by_contra hg1
        rw [hgA k hk hg1] at hx
        exact (hcx.trans (hx.trans (min_le_right _ _))).not_gt hc₀c
      have hg2 : (μ : Label.{u}) ≤ g₂ k := by
        by_contra hg2
        rw [hgC k hk hg1 hg2] at hx
        exact (hcx.trans hx).not_gt hc₀c
      rw [hgB k hk hg1 hg2] at hx
      have hc1 := hw₁.visibilityReplace_comm x k (hg1 ▸ le_top) i hi
      have hx1' : ¬ σ₁ (visibilityReplace k i x) < β := by
        rw [hc1, visibilityReplace_lt_iff hβ']
        exact hx1
      by_cases hx2 : (μ : Label.{u}) ≤ σ₂ x
      · rw [hσband x hx1 hx2] at hx ⊢
        rcases le_or_gt (σ₂ x) (g₂ k) with h22 | h22
        · have hc2 := hw₂.visibilityReplace_comm x k h22 i hi
          have hx2' : (μ : Label.{u}) ≤ σ₂ (visibilityReplace k i x) := by
            rw [hc2]
            exact not_lt.mp fun h ↦ not_lt.mpr hx2 ((visibilityReplace_lt_iff hμ).mp h)
          rw [hσband _ hx1' hx2', hc2]
          exact bandMap_visibilityReplace hβ' hμ hk hi hx2
        · have h22' := hw₂.lt_apply_visibilityReplace h22 hi
          by_cases hK : ((μ + K : Ordinal.{u}) : Label.{u}) ≤ g₂ k
          · rw [hσband _ hx1' (hg2.trans h22'.le), bandMap_of_le (hK.trans h22'.le),
              bandMap_of_le (hK.trans h22.le), (isSelfVisible_coe_add hβ' hk).visibilityReplace_eq]
          · exact absurd hx (not_le.mpr (bandMap_lt_bandMap hg2 (not_le.mp hK) h22))
      · have h22 : σ₂ x ≤ g₂ k := (not_le.mp hx2).le.trans hg2
        have hc2 := hw₂.visibilityReplace_comm x k h22 i hi
        have hx2' : ¬ (μ : Label.{u}) ≤ σ₂ (visibilityReplace k i x) := by
          rw [hc2, not_le, visibilityReplace_lt_iff hμ]
          exact not_le.mp hx2
        rw [hσc _ hx1' hx2', hσc x hx1 hx2]
        exact ((hνK.mono hk).visibilityReplace_eq i).symm
  refine ⟨g, σ, hw, fun d ↦ ?_⟩
  have hdK := hgr d
  rcases hq d with hqd | hqd
  · -- a cell where `q` is below `β`
    have hqc₀ : q d ≤ ν₀ := hbd d hqd
    rw [hlow d hqd]
    rw [heq₁ d] at hqd hqc₀ ⊢
    by_cases hb : g₁ (grade d) = ⊤
    · rw [hb, min_top_right] at hqd hqc₀ ⊢
      rw [hσlow _ hqd, min_eq_left (hqc₀.trans hc₀c.le)]
      exact (min_eq_left (hqc₀.trans (hgge _ hdK hb))).symm
    rw [hgA _ hdK hb]
    by_cases ha : σ₁ (e d) < β
    · rw [hσlow _ ha, min_min_min_comm, min_eq_right hc₀c.le]
      exact (min_eq_left hqc₀).symm
    · have hmin : min (σ₁ (e d)) (g₁ (grade d)) = g₁ (grade d) :=
        min_eq_right (not_lt.mp fun h ↦ ha (lt_of_eq_of_lt (min_eq_left h.le).symm hqd))
      rw [hmin] at hqc₀ ⊢
      rw [min_eq_left hqc₀]
      exact (min_eq_right (hqc₀.trans (hc₀c.le.trans (hσge _ ha)))).symm
  · -- a cell where `q` is the formal top
    have hμr := hr d hqd
    rw [htop d hqd, heq₂ d]
    rw [heq₂ d] at hμr
    rw [heq₁ d] at hqd
    obtain ⟨ha, hb⟩ := min_eq_top.mp hqd
    have hμa : (μ : Label.{u}) ≤ σ₂ (e d) := hμr.trans (min_le_left _ _)
    have hμb : (μ : Label.{u}) ≤ g₂ (grade d) := hμr.trans (min_le_right _ _)
    rw [hσband _ (by rw [ha]; exact not_top_lt) hμa, hgB _ hdK hb hμb]
    exact (monotone_bandMap β μ K).map_min

end Splice

end Label

namespace StageType

open Label

variable {α β : Ordinal.{u}} {m k n : ℕ} {q : StageType.{u} β m} {c r e : Fin q.card}

/-! ### Top caps and markers -/

/-- A **top cap** of `q`: a cell of full scope labelled `⊤` whose grade is at least the grade of
every cell labelled `⊤`, so that its grade is the largest grade of a cell labelled `⊤`. -/
def IsTopCap (q : StageType.{u} β m) (c : Fin q.card) : Prop :=
  q.toCellScheme.scope c = univ ∧ q.label c = ⊤ ∧
    ∀ x, q.label x = ⊤ → q.toCellScheme.grade x ≤ q.toCellScheme.grade c

/-- Every cell labelled `⊤` lies below a top cap. -/
theorem IsTopCap.mem_below (hc : q.IsTopCap c) {x : Fin q.card} (hx : q.label x = ⊤) :
    x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) := by
  -- membership below `c` is the comparison of graded indices
  change q.toCellScheme.gradedIndex x ≤ q.toCellScheme.gradedIndex c
  exact Prod.mk_le_mk.mpr ⟨by rw [hc.1]; exact subset_univ _,
    hc.2.2 x hx⟩

/-- **A legal stage type with a cell labelled `⊤` has a top cap**: completeness gives a cell of
full scope at the largest grade `K` of a cell labelled `⊤`, and availability gives one such cell
labelled `⊤`. -/
theorem exists_isTopCap (hq : q.IsLegal) (h : ¬ q.IsTopFree) : ∃ c, q.IsTopCap c := by
  classical
  set T := univ.filter fun d : Fin q.card ↦ q.label d = ⊤
  have hT : T.Nonempty := by
    obtain ⟨s, hs⟩ : ∃ s, q.label s = ⊤ := by
      by_contra h'
      exact h fun d hd ↦ h' ⟨d, hd⟩
    exact ⟨s, mem_filter.mpr ⟨mem_univ _, hs⟩⟩
  obtain ⟨E, hE, hEmax⟩ := T.exists_max_image (fun d ↦ q.toCellScheme.grade d) hT
  have hEt : q.label E = ⊤ := (mem_filter.mp hE).2
  have hpos : 0 < q.toCellScheme.grade E := q.isWellFormed.isWellFormed.grade_pos E
  obtain ⟨D', hD'⟩ := hq.isComplete ((univ : Finset (Fin m)), q.toCellScheme.grade E)
    ⟨q.univ_mem_faces, hpos, by
      -- the second component of the pair is the grade, the first the whole ground set
      change q.toCellScheme.grade E ≤ #(Finset.univ : Finset (Fin m))
      rw [Finset.card_univ, Fintype.card_fin]
      exact q.grade_le E⟩
  have hD's : q.toCellScheme.scope D' = univ := congrArg Prod.fst hD'
  have hD'g : q.toCellScheme.grade D' = q.toCellScheme.grade E := congrArg Prod.snd hD'
  obtain ⟨C, hC, hEC⟩ := q.isLawful.availability E D' (hD's ▸ subset_univ _) hD'g.symm
  have hCi : q.toCellScheme.gradedIndex C = (univ, q.toCellScheme.grade E) := hC.trans hD'
  refine ⟨C, congrArg Prod.fst hCi, top_le_iff.mp (hEt ▸ hEC), fun x hx ↦ ?_⟩
  rw [show q.toCellScheme.grade C = q.toCellScheme.grade E from congrArg Prod.snd hCi]
  exact hEmax x (mem_filter.mpr ⟨mem_univ _, hx⟩)

/-- A **marker** of the cell `c`: a cell below `c` labelled `⊤` at which the row of `c` is least
among the cells below `c` labelled `⊤`. -/
def IsMarker (q : StageType.{u} β m) (c r : Fin q.card) : Prop :=
  q.label r = ⊤ ∧ r ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) ∧
    ∀ x, q.label x = ⊤ → x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) →
      q.rowAt c r ≤ q.rowAt c x

/-- **Every cell labelled `⊤` has a marker**: the cells below it labelled `⊤` form a finite set
containing the cell itself, and the row takes a least value on it. -/
theorem exists_isMarker (hc : q.label c = ⊤) : ∃ r, q.IsMarker c r := by
  classical
  set S := univ.filter fun x : Fin q.card ↦
    q.label x = ⊤ ∧ x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c)
  have hS : S.Nonempty :=
    ⟨c, mem_filter.mpr ⟨mem_univ _, hc, q.toCellScheme.mem_below_gradedIndex c⟩⟩
  obtain ⟨r, hr, hmin⟩ := S.exists_min_image (q.rowAt c) hS
  obtain ⟨-, hrt, hrc⟩ := mem_filter.mp hr
  exact ⟨r, hrt, hrc, fun x hx hxc ↦ hmin x (mem_filter.mpr ⟨mem_univ _, hx, hxc⟩)⟩

/-! ### The band lift of the marker's block -/

/-- **The band lift.**  Let `β` be a limit, `β + ω ≤ α`, `q` a legal stage type at `β`, `c` a top
cap of `q` of grade `N`, and `r` a marker of `c`.  The entry of the row of `c` at `r` is `μ + j`
with `μ` zero or a limit, and some stage type at `α` reducing to `q` carries, at every cell `d`
labelled `⊤` in `q`, the band map from `μ` to `β` at `N` of the row of `c` read at `d`.

The labels below `β` are kept.  Order: the rows are orderly, and the band map keeps
self-visibility at the grades at most `N`.  Availability: at a cell labelled `⊤` it is
availability of the row of `c`, which is lawful below `c`; the cell it gives is labelled `⊤` by
locality of `q` at `c`.  Locality at a cell `s` labelled `⊤` is the splice
(`Label.TransformsTo.splice_bandMap`) of locality of `q` at `s` with locality at `s` of the row of
`c`; at the other cells it is locality of `q`. -/
theorem IsMarker.exists_lift (hβ : IsSuccLimit β) (hα : β + ω ≤ α) (hq : q.IsLegal)
    (hc : q.IsTopCap c) (hr : q.IsMarker c r) :
    ∃ (μ : Ordinal.{u}) (j : ℕ), IsSuccPrelimit μ ∧
      q.rowAt c r = ((μ + j : Ordinal.{u}) : Label.{u}) ∧
      ∃ Q : StageType.{u} α m, Q.reduce hβ.isSuccPrelimit = q ∧
        ∀ (d : Fin q.card) (d' : Fin Q.card), (d' : ℕ) = d → q.label d = ⊤ →
          Q.label d' = bandMap β μ (q.toCellScheme.grade c) (q.rowAt c d) := by
  classical
  have hβ' := hβ.isSuccPrelimit
  set N := q.toCellScheme.grade c
  obtain ⟨hrt, hrc, hrmin⟩ := hr
  -- the entry at the marker is an ordinal `μ + j`
  have hne_bot : q.rowAt c r ≠ ⊥ := by
    intro h
    rw [Scheme.rowAt_of_mem hrc] at h
    have := (q.isLawful.locality c).eq_bot (d := ⟨r, hrc⟩) h
    rw [hrt, hc.2.1, min_self] at this
    exact top_ne_bot this
  have hne_top : q.rowAt c r ≠ ⊤ := ((q.isCoded.rowAt_lt c r).trans_le le_top).ne
  obtain ⟨o, ho⟩ : ∃ o : Ordinal.{u}, q.rowAt c r = o := by
    induction h : q.rowAt c r using recBotCoeTop with
    | bot => exact absurd h hne_bot
    | coe o => exact ⟨o, rfl⟩
    | top => exact absurd h hne_top
  obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
  have hμle (d : Fin q.card) (hd : q.label d = ⊤) : (μ : Label.{u}) ≤ q.rowAt c d :=
    (ho ▸ coe_le_coe_add μ j).trans (hrmin d hd (hc.mem_below hd))
  have hband_ge (d : Fin q.card) (hd : q.label d = ⊤) :
      (β : Label.{u}) ≤ bandMap β μ N (q.rowAt c d) :=
    coe_le_bandMap ((WithBot.bot_lt_coe _).trans_le (hμle d hd)).ne'
  -- the labels of the lift
  set ℓ : Fin q.card → Label.{u} := fun d ↦
    if q.label d = ⊤ then bandMap β μ N (q.rowAt c d) else q.label d
  have hℓtop (d : Fin q.card) (hd : q.label d = ⊤) : ℓ d = bandMap β μ N (q.rowAt c d) :=
    ite_eq_left hd
  have hℓlow (d : Fin q.card) (hd : q.label d ≠ ⊤) : ℓ d = q.label d := ite_eq_right hd
  have hlt (d : Fin q.card) (hd : q.label d ≠ ⊤) : q.label d < β :=
    (q.atStage d).resolve_right hd
  have hlaw : q.rows.IsLawful ℓ := by
    refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
    · -- order
      by_cases hd : q.label d = ⊤
      · have hdc := hc.mem_below hd
        rw [hℓtop d hd]
        refine isSelfVisible_bandMap hβ' hμ (hc.2.2 d hd) (hμle d hd) ?_
        rw [Scheme.rowAt_of_mem hdc]
        exact hq.isConsistent.isOrderly c ⟨d, hdc⟩
      · rw [hℓlow d hd]
        exact q.isLawful.orderly d
    · -- locality
      by_cases hs : q.label s = ⊤
      · have hsc := hc.mem_below hs
        have hgs : q.toCellScheme.grade s ≤ N := hc.2.2 s hs
        have hcons := CellScheme.Rows.isLawfulBelow_iff.mp (hq.isConsistent c)
        have hbelow (x : Fin q.card)
            (hx : x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex s)) :
            x ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) :=
          show q.toCellScheme.gradedIndex x ≤ q.toCellScheme.gradedIndex c from le_trans hx hsc
        have h₂ : TransformsTo
            (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              q.toCellScheme.grade d)
            (q.rows.row s) (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              min (q.rows.row c ⟨d.1, hbelow d.1 d.2⟩) (q.rows.row c ⟨s, hsc⟩)) :=
          (hcons.locality ⟨s, hsc⟩).reindex
            fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              ⟨⟨d.1, hbelow d.1 d.2⟩, d.2⟩
        refine TransformsTo.splice_bandMap hβ hμ
          (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦ d.2.2.trans hgs)
          (q.isLawful.locality s) h₂ (fun d ↦ ?_) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
          (fun d hd ↦ ?_)
        · rw [hs, min_top_right]
          exact q.atStage d
        · rw [hs, min_top_right] at hd
          have h₁ := hμle d hd
          have h₂ := hμle s hs
          rw [Scheme.rowAt_of_mem (hbelow d.1 d.2)] at h₁
          rw [Scheme.rowAt_of_mem hsc] at h₂
          exact le_min h₁ h₂
        · rw [hs, min_top_right] at hd ⊢
          rw [hℓlow d.1 (hd.trans_le le_top).ne, hℓtop s hs]
          exact min_eq_left (hd.le.trans (hband_ge s hs))
        · rw [hs, min_top_right] at hd
          rw [hℓtop d.1 hd, hℓtop s hs, Scheme.rowAt_of_mem (hbelow d.1 d.2),
            Scheme.rowAt_of_mem hsc]
          exact ((monotone_bandMap β μ N).map_min).symm
      · have hfun : (fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
            min (ℓ d) (ℓ s)) =
            fun d : q.toCellScheme.below (q.toCellScheme.gradedIndex s) ↦
              min (q.label d) (q.label s) := by
          funext d
          rw [hℓlow s hs]
          by_cases hd : q.label d = ⊤
          · rw [hℓtop d hd, hd, min_top_left,
              min_eq_right ((hlt s hs).le.trans (hband_ge d hd))]
          · rw [hℓlow d hd]
        rw [hfun]
        exact q.isLawful.locality s
    · -- availability
      by_cases hs : q.label s = ⊤
      · have hsc := hc.mem_below hs
        have htc : t ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex c) := by
          -- membership below `c` is the comparison of graded indices
          change q.toCellScheme.gradedIndex t ≤ q.toCellScheme.gradedIndex c
          exact Prod.mk_le_mk.mpr ⟨by rw [hc.1]; exact subset_univ _,
            hg ▸ hc.2.2 s hs⟩
        obtain ⟨u, hu, hrow⟩ := (CellScheme.Rows.isLawfulBelow_iff.mp
          (hq.isConsistent c)).availability ⟨s, hsc⟩ ⟨t, htc⟩ hst hg
        have hu' : q.toCellScheme.gradedIndex u.1 = q.toCellScheme.gradedIndex t := hu
        have hug : q.toCellScheme.grade u.1 = q.toCellScheme.grade s :=
          (congrArg Prod.snd hu').trans hg.symm
        have hloc := (q.isLawful.locality c).le_of_le (d := ⟨s, hsc⟩) (d' := u) hrow hug.le
        have hut : q.label u.1 = ⊤ := by
          -- locality of `q` at `c`, read at the cells `s` and `u`
          change min (q.label s) (q.label c) ≤ min (q.label u.1) (q.label c) at hloc
          rw [hs, hc.2.1, min_self] at hloc
          exact top_le_iff.mp (hloc.trans (min_le_left _ _))
        refine ⟨u.1, hu', ?_⟩
        rw [hℓtop s hs, hℓtop u.1 hut, Scheme.rowAt_of_mem hsc, Scheme.rowAt_of_mem u.2]
        exact monotone_bandMap β μ N hrow
      · obtain ⟨u, hu, hle⟩ := q.isLawful.availability s t hst hg
        refine ⟨u, hu, ?_⟩
        rw [hℓlow s hs]
        by_cases hut : q.label u = ⊤
        · rw [hℓtop u hut]
          exact (hlt s hs).le.trans (hband_ge u hut)
        · rw [hℓlow u hut]
          exact hle
  have hNα : β + N < α :=
    ((add_lt_add_iff_left β).mpr (Ordinal.natCast_lt_omega0 N)).trans_le hα
  refine ⟨μ, j, hμ, ho, ⟨q.toScheme, ℓ, q.isWellFormed, q.isCoded, hlaw, fun d ↦ ?_⟩, ?_,
    fun d d' hdd' hd ↦ ?_⟩
  · -- every label of the lift occurs at `α`
    by_cases hd : q.label d = ⊤
    · rw [hℓtop d hd]
      exact .inl ((bandMap_le _).trans_lt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hNα)))
    · rw [hℓlow d hd]
      exact (q.atStage d).mono ((le_self_add.trans hα))
  · -- the lift reduces to `q`
    refine StageType.ext rfl fun i i' hii' ↦ ?_
    obtain rfl : i = i' := Fin.ext hii'
    -- the reduced label is the reduction of `ℓ i`
    change Label.reduce β (ℓ i) = q.label i
    by_cases hd : q.label i = ⊤
    · rw [hd, Label.reduce_of_le (by rw [hℓtop i hd]; exact hband_ge i hd)]
    · rw [hℓlow i hd, Label.reduce_of_lt (hlt i hd)]
  · -- the label of the lift at a cell labelled `⊤`
    obtain rfl : d' = d := Fin.ext hdd'
    exact hℓtop d' hd

/-- A cell of `q` transported from a cell of the root labelled `⊤` is labelled `⊤`. -/
theorem label_cellMap_eq_top {f : Fin k ↪ Fin m} {p : StageType.{u} β k}
    (hp : restrictFace f q = some p) {d : Fin p.card} (hd : p.label d = ⊤)
    (i : Fin (q.toScheme.comap f).card) (hi : (i : ℕ) = d) : q.label (q.cellMap f i) = ⊤ := by
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hp
  -- the label of `q` at the transported cell is the label of the face at `i`
  change (q.comap f hf).label i = ⊤
  exact (label_congr hqp hi).trans hd

/-! ### Forcing is read by the row of a top cap -/

/-- **Thresholds bounded below in every lift are read by the row of a top cap.**  Let `β` be a
limit, `β + ω ≤ α`, `q` a legal stage type at `β`, `c` a top cap of `q` of grade `N`, `r` a marker
of `c`, and `e` a cell labelled `⊤`.  If every stage type at `α` reducing to `q` has a label at
least `β + L` at `e`, then `L ≤ N` and
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`.

The band lift (`StageType.IsMarker.exists_lift`) has the label `β + min j' N` at `e` when the row
of `c` reads `e` in the block `[μ, μ + ω)` of the marker, at `μ + j'`, and `β + N` otherwise. -/
theorem IsMarker.visibilityReplace_rowAt_le (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) (he : q.label e = ⊤) {L : ℕ}
    (hL : ∀ (Q : StageType.{u} α m) (e' : Fin Q.card), Q.reduce hβ.isSuccPrelimit = q →
      (e' : ℕ) = e → ((β + L : Ordinal.{u}) : Label.{u}) ≤ Q.label e') :
    L ≤ q.toCellScheme.grade c ∧
      visibilityReplace (q.toCellScheme.grade c) L (q.rowAt c r) ≤ q.rowAt c e := by
  obtain ⟨μ, j, hμ, hrj, Q, hQ, hQl⟩ := hr.exists_lift hβ hα hq hc
  set N := q.toCellScheme.grade c
  set e' : Fin Q.card :=
    ⟨e, lt_of_lt_of_eq e.2 (congrArg (fun t : StageType.{u} β m ↦ t.card) hQ).symm⟩
  have h := hL Q e' hQ rfl
  rw [hQl e e' rfl he] at h
  have hLN : L ≤ N := by
    have h' := h.trans (bandMap_le _)
    exact_mod_cast (add_le_add_iff_left β).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h'))
  refine ⟨hLN, ?_⟩
  have hre : q.rowAt c r ≤ q.rowAt c e := hr.2.2 e he (hc.mem_below he)
  rw [hrj] at hre ⊢
  have hblock (i : ℕ) : ((μ + i : Ordinal.{u}) : Label.{u}) < ((μ + ω : Ordinal.{u}) : Label.{u}) :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      ((add_lt_add_iff_left μ).mpr (Ordinal.natCast_lt_omega0 i)))
  rw [visibilityReplace_coe_add hμ]
  by_cases hω : ((μ + ω : Ordinal.{u}) : Label.{u}) ≤ q.rowAt c e
  · split_ifs
    · exact ((hblock L).trans_le hω).le
    · exact ((hblock j).trans_le hω).le
  -- the row of `c` reads `e` at `μ + j'`
  obtain ⟨ν, hν, -⟩ := exists_coe_eq_of_le_of_lt ((coe_le_coe_add μ j).trans hre) (not_le.mp hω)
  have hν₁ : μ ≤ ν := by
    have := (coe_le_coe_add μ j).trans (hν ▸ hre)
    exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
  have hν₂ : ν < μ + ω := by
    have := hν ▸ not_le.mp hω
    exact WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp this)
  obtain ⟨j', rfl⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0 hν₁ hν₂
  rw [hν] at hre h ⊢
  rw [bandMap_coe_add_natCast] at h
  have hLj' : L ≤ j' := by
    have h' := (add_le_add_iff_left β).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h))
    have : L ≤ min j' N := by exact_mod_cast h'
    exact this.trans (min_le_left _ _)
  have hjj' : j ≤ j' := by
    have h' := (add_le_add_iff_left μ).mp (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hre))
    exact_mod_cast h'
  split_ifs
  · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      ((add_le_add_iff_left μ).mpr (by exact_mod_cast hLj')))
  · exact hre

/-- **Forcing is read by the rows.**  Let `β` be a limit, `β + ω ≤ α`, `q` a legal stage
type at `β` restricting along `f` to a root `p`, `c` a top cap of `q` of grade `N`, and `r` a
marker of `c`.  If `(q, f)` forces the threshold `L` at a cell `d` of `p` labelled `⊤`, and `e` is
the cell of `q` transported from `d`, then `L ≤ N` and
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`. -/
theorem ForcesThreshold.visibilityReplace_rowAt_le (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) (hc : q.IsTopCap c) (hr : q.IsMarker c r) {f : Fin k ↪ Fin m}
    {p : StageType.{u} β k} {d : Fin p.card} {L : ℕ}
    (hforce : ForcesThreshold α hβ.isSuccPrelimit q f p d L) (hd : p.label d = ⊤)
    (he : ∀ i : Fin (q.toScheme.comap f).card, (i : ℕ) = d → q.cellMap f i = e) :
    L ≤ q.toCellScheme.grade c ∧
      visibilityReplace (q.toCellScheme.grade c) L (q.rowAt c r) ≤ q.rowAt c e := by
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hforce.1
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β k ↦ s.card) hqp
  set i₀ : Fin (q.comap f hf).card := ⟨d, lt_of_lt_of_eq d.2 hcard.symm⟩
  have hie : q.cellMap f i₀ = e := he i₀ rfl
  have hel : q.label e = ⊤ := by
    rw [← hie, ← comap_label q f hf i₀]
    exact (label_congr hqp rfl).trans hd
  refine hr.visibilityReplace_rowAt_le hβ hα hq hc hel fun Q e' hQ he' ↦ ?_
  subst hQ
  have hf' : univ.map f ∈ Q.toCellScheme.faces := hf
  have h := hforce.2 Q (Q.comap f hf') rfl (restrictFace_of_mem Q f hf') i₀ rfl
  -- the label of the face of `Q` at `i₀` is the label of `Q` at the transported cell
  change ((β + L : Ordinal.{u}) : Label.{u}) ≤ Q.label (Q.cellMap f i₀) at h
  -- the cells of `Q` and of its reduction are the same, by position
  have hpos : Q.cellMap f i₀ = e' := Fin.ext (by rw [he']; exact congrArg Fin.val hie)
  rwa [hpos] at h

/-! ### The marked-cap context -/

/-- A stage type `t'` on `k` points is a **marked-cap context** along `h : Fin n ↪ Fin k` when it
has a top cap `c` of grade `N > n + 1` with a marker `r`, and at every cell `a` of the root (a cell
visible through `h`) labelled `⊤` the row of `c` satisfies
`visibilityReplace N (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a`.  The grade of a top cap is the top
grade of `t'`, the largest grade of a cell labelled `⊤`. -/
def IsMarkedCapContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsTopCap c ∧ t'.IsMarker c r ∧ n + 1 < t'.toCellScheme.grade c ∧
    ∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
      visibilityReplace (t'.toCellScheme.grade c) (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a

/-- **A marked-cap context is not top-free**: its top cap is labelled `⊤`. -/
theorem IsMarkedCapContext.not_isTopFree {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : t'.IsMarkedCapContext h) : ¬ t'.IsTopFree :=
  fun htf ↦ let ⟨c, _, hc, _⟩ := ht; htf c hc.2.1

/-- A top-free stage type is a marked-cap context along no embedding. -/
theorem not_isMarkedCapContext_of_isTopFree {t' : StageType.{u} α k} (ht : t'.IsTopFree)
    (h : Fin n ↪ Fin k) : ¬ t'.IsMarkedCapContext h :=
  fun hm ↦ hm.not_isTopFree ht

/-- A stage type on no points is a marked-cap context along no embedding: it is top-free. -/
theorem not_isMarkedCapContext_of_zero (t : StageType.{u} α 0) (h : Fin n ↪ Fin 0) :
    ¬ t.IsMarkedCapContext h :=
  not_isMarkedCapContext_of_isTopFree (isTopFree_of_zero t) h

/-- **A context whose cells labelled `⊤` have grades at most `n + 1` is a marked-cap context along
no embedding of `n` points**: the grade of a top cap is the grade of a cell labelled `⊤`. -/
theorem not_isMarkedCapContext_of_grade_le {t' : StageType.{u} α k}
    (ht : ∀ x, t'.label x = ⊤ → t'.toCellScheme.grade x ≤ n + 1) (h : Fin n ↪ Fin k) :
    ¬ t'.IsMarkedCapContext h :=
  fun ⟨c, _, hc, _, hn, _⟩ ↦ (ht c hc.2.1).not_gt hn

/-- **Forcing at the root gives a marked-cap context.**  Let `β` be a limit, `β + ω ≤ α`, `q` a
legal stage type at `β` restricting along `f : Fin n ↪ Fin m` to `p`, and `c` a top cap of `q` of
grade above `n + 1`.  If `(q, f)` forces the threshold `n + 1` at every cell of
`p` labelled `⊤`, then `q` is a marked-cap context along `f`, with any marker of `c`. -/
theorem isMarkedCapContext_of_forcesThreshold (hβ : IsSuccLimit β) (hα : β + ω ≤ α)
    (hq : q.IsLegal) {f : Fin n ↪ Fin m} {p : StageType.{u} β n}
    (hp : restrictFace f q = some p) (hc : q.IsTopCap c)
    (hn : n + 1 < q.toCellScheme.grade c)
    (hforce : ∀ d : Fin p.card, p.label d = ⊤ →
      ForcesThreshold α hβ.isSuccPrelimit q f p d (n + 1)) :
    q.IsMarkedCapContext f := by
  obtain ⟨r, hr⟩ := exists_isMarker hc.2.1
  refine ⟨c, r, hc, hr, hn, fun a ha hat ↦ ?_⟩
  obtain ⟨hf, hqp⟩ := (restrictFace_eq_some_iff q f).mp hp
  have hcard : (q.comap f hf).card = p.card :=
    congrArg (fun s : StageType.{u} β n ↦ s.card) hqp
  obtain ⟨i, rfl⟩ : a ∈ Set.range (q.cellMap f) := by
    rw [Scheme.range_cellMap]
    exact ha
  set d : Fin p.card := ⟨i, lt_of_lt_of_eq i.2 hcard⟩
  have hd : p.label d = ⊤ := by
    rw [← hat]
    exact (label_congr hqp.symm rfl).trans (comap_label q f hf i)
  exact (ForcesThreshold.visibilityReplace_rowAt_le hβ hα hq hc hr (hforce d hd) hd
    fun i' hi' ↦ congrArg (q.cellMap f) (Fin.ext hi')).2

end StageType

end VaughtConjecture

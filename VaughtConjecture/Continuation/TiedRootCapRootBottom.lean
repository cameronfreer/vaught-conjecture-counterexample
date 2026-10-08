/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapBotKeeping

/-!
# Acquisition of caps respecting the root bottoms, from bot-keeping completions

Roadmap, Layer 3 ((R3) of the table of 3.4) and Layer 4 (cover-hollowness).

`Realization.RootBottomAcquisition` is hollow acquisition of the marked-cap contexts with root
offsets below the grade of the cap and the cap reading the root cells labelled `⊥` as `⊥`
(`TiedRootCapRelabel.MarkedCapContextBelow'`).  This file proves it from one explicit hypothesis:
every seed has a bot-keeping completion below the full grade
(`CompletionBelowFullGrade.BotKeeping`).

* **Synchronization with forcing** (`Realization.IsModel.exists_forcing_floor`, compiled in this
  repository (theorem named)): as `Realization.IsModel.exists_synchronized_floor`, with the forcing
  of the threshold `x.arity + 1` at every root cell labelled `⊤` as output.
* **The bottom pattern of a bot-keeping coface** (`StageType.markedCapContextBelow'_of_botKeeping`,
  compiled): over a legal `p₀` with a root face `p` along `h₀`, forcing at the root tops, and a cell
  labelled `⊤` of a grade `G` above `n + 1` and above the root offsets, every coface `q` of `p₀`
  with the scheme and bottom pattern of a coface `qs` whose cells of full scope that are its apex
  or not labelled `⊥` read the cells of proper scope labelled `⊥` as `⊥`, is in
  `MarkedCapContextBelow'` along `h₀.trans Fin.castSuccEmb`.  A top cap of `q` has full scope and
  grade at least `G`; it is `⊤`, so not `⊥` in `qs` below the full grade (the bottom pattern); the
  marker inequality at the root tops passes by forcing
  (`StageType.IsMarker.visibilityReplace_le_of_forcesThreshold`).
* **Acquisition** (`Realization.rootBottomAcquisition_of_botKeeping`, compiled): under
  `hcomp : ∀ α m (I : Seed α m), ∃ F : CompletionBelowFullGrade I, F.BotKeeping`,
  `Realization.RootBottomAcquisition` holds.  Synchronize the root to an occurrence `Z`
  (forcing, top grade above `n + 1` and the root offsets); extend `Z` by one point (high-arity
  dominance at `0`) to `Z₁` of type `q₀`, a coface of the type of `Z`; take a bot-keeping
  completion of the seed of `q₀` with itself; realize, over `Z₁`, a member of the bottom-pattern
  instance of its completion (clause 4(a)ii).  The extension by one point first makes the face
  along `Fin.castSuccEmb` of the seed exist (a coatom of the type of `Z` need not be a face).

**Status.**  `hcomp` is compiled at the arities `m ≤ 2` (`Seed.exists_botKeeping_of_le_two`), and
under the lifting invariant at the top grade (`Seed.exists_botKeeping_of_towerInvariant`).  At
every arity it is not compiled on this branch (prospective): the completion at every arity (the
profile tower, `Seed.nonempty_completionBelowFullGrade` on `main`) is not on this branch.  It
follows from level bot-keeping of the profile tower through
`CompletionBelowFullGrade.exists_botKeeping_of_eq_fieldLayer` (see
`VaughtConjecture.Continuation.TiedRootCapBotKeeping`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

/-! ### The bottom pattern of a bot-keeping coface -/

namespace StageType

variable {β α' : Ordinal.{u}} {k n : ℕ}

/-- **The bottom pattern of a bot-keeping coface gives a context respecting the root bottoms.** -/
theorem markedCapContextBelow'_of_botKeeping (hβ : Order.IsSuccLimit β) (hα' : β + ω ≤ α')
    {p₀ : StageType.{u} β k} {qs : StageType.{u} β (k + 1)} (hqs : qs ∈ p₀.cofaces)
    (hclean : ∀ u y, qs.toCellScheme.scope u = univ →
      (qs.toCellScheme.grade u = k + 1 ∨ qs.label u ≠ ⊥) → qs.toCellScheme.scope y ≠ univ →
        qs.label y = ⊥ → qs.rowAt u y = ⊥)
    {q : StageType.{u} β (k + 1)} (hq : q ∈ p₀.cofaces ∩ bottomPatternFamily qs.toScheme qs.label)
    {h₀ : Fin n ↪ Fin k} {p : StageType.{u} β n} (hp : restrictFace h₀ p₀ = some p)
    {K : ℕ} (hK : ∀ d (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
      p.label d = ((μ + f : Ordinal.{u}) : Label.{u}) → f ≤ K)
    (hforce : ∀ d, p.label d = ⊤ → ForcesThreshold α' hβ.isSuccPrelimit p₀ h₀ p d (n + 1))
    {e : Fin p₀.card} (he : p₀.label e = ⊤) (hne : n + 1 < p₀.toCellScheme.grade e)
    (hKe : K < p₀.toCellScheme.grade e) :
    TiedRootCapRelabel.MarkedCapContextBelow' q (h₀.trans Fin.castSuccEmb) := by
  obtain ⟨-, -⟩ := hqs
  obtain ⟨S, ℓ, hw, hcod, hl, hat⟩ := q
  obtain ⟨⟨hql, hq₁⟩, hS, hpat⟩ := hq
  change S = qs.toScheme at hS
  subst hS
  set q : StageType.{u} β (k + 1) := ⟨qs.toScheme, ℓ, hw, hcod, hl, hat⟩ with hqdef
  have hroot : restrictFace (h₀.trans Fin.castSuccEmb) q = some p := by
    rw [← restrictFace_trans _ _ _ hq₁]
    exact hp
  have hforce' (d : Fin p.card) (hd : p.label d = ⊤) :
      ForcesThreshold α' hβ.isSuccPrelimit q (h₀.trans Fin.castSuccEmb) p d (n + 1) :=
    (hforce d hd).trans_face hq₁
  -- a cell of `q` labelled `⊤` of the grade of `e`
  set e' : Fin q.card := faceCell hq₁ e
  have he' : q.label e' = ⊤ := (label_faceCell hq₁ e).trans he
  have he'g : q.toCellScheme.grade e' = p₀.toCellScheme.grade e := grade_faceCell hq₁ e
  have hnt : ¬ q.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    have := grade_le_topGrade he'
    omega
  obtain ⟨c, hc⟩ := StageType.exists_isTopCap hql hnt
  obtain ⟨r, hr⟩ := StageType.exists_isMarker hc.2.1
  have hcg : p₀.toCellScheme.grade e ≤ q.toCellScheme.grade c := he'g ▸ hc.2.2 e' he'
  refine ⟨c, r, ⟨hc, hr, by omega,
    hr.visibilityReplace_le_of_forcesThreshold hβ hα' hql hroot hc hforce'⟩,
    fun y hy μ f hμ hf ↦ ?_, fun y hy hyb ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_eq hroot hy
    rw [label_faceCell] at hf
    have := hK z μ f hμ hf
    omega
  · obtain ⟨z, rfl⟩ := exists_faceCell_eq hroot hy
    have hn : n ≤ k := by simpa using Fintype.card_le_of_embedding h₀
    have hyg : q.toCellScheme.grade (faceCell hroot z) ≤ k :=
      (grade_faceCell hroot z).trans_le ((p.grade_le z).trans hn)
    refine hclean c _ hc.1 ?_ ?_ ((hpat _ _ rfl hyg).mp hyb)
    · rcases Nat.lt_or_ge (q.toCellScheme.grade c) (k + 1) with hlt | hge
      · exact .inr fun hb ↦ top_ne_bot (hc.2.1.symm.trans ((hpat c c rfl (by omega)).mpr hb))
      · exact .inl (le_antisymm (q.grade_le c) hge)
    · change q.toCellScheme.scope (faceCell hroot z) ≠ univ
      rw [scope_faceCell]
      intro h
      have hlast : Fin.last k ∈ (p.toCellScheme.scope z).map (h₀.trans Fin.castSuccEmb) :=
        h ▸ mem_univ _
      obtain ⟨i, -, hi⟩ := mem_map.mp hlast
      exact Fin.castSucc_ne_last _ hi

end StageType

/-! ### Synchronization with forcing -/

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Synchronization with forcing**: in a model at a block stage, cover-hollow, with unbounded
growth, every occurrence `x` is a literal face, along some `g`, of an occurrence `Z` of top grade
above `x.arity + 1` and above `K`, at which `x.arity + 1` is forced at every cell of `x` labelled
`⊤`. -/
theorem IsModel.exists_forcing_floor (hR : R.IsModel) (hhol : R.IsCoverHollow)
    (htop : R.topGradeSup = ⊤) (K : ℕ) (x : R.Occurrence) :
    ∃ (Z : R.Occurrence) (g : Fin x.arity ↪ Fin Z.arity), g.trans Z.tuple = x.tuple ∧
      x.arity + 1 < Z.type.topGrade ∧ K < Z.type.topGrade ∧ ∀ a, x.type.label a = ⊤ →
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) Z.type g
          x.type a (x.arity + 1) := by
  classical
  have hO (a : Fin x.type.card) : ∃ O : R.Occurrence, x.type.label a = ⊤ →
      ∃ g : Fin x.arity ↪ Fin O.arity, g.trans O.tuple = x.tuple ∧
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) O.type g
          x.type a (x.arity + 1) := by
    by_cases ha : x.type.label a = ⊤
    · have hno : ¬ R.IsTopAnchor x a (x.arity + 1) := fun hA ↦ hhol ⟨x, a, x.arity + 1, hA⟩
      simp only [IsTopAnchor, not_and, not_forall, not_not] at hno
      obtain ⟨⟨m, q, g⟩, ⟨s, hs, hsq⟩, hforce⟩ := hno ha
      refine ⟨⟨m, ⟨s, hsq.injective⟩, q, hsq.eval_eq⟩, fun _ ↦ ⟨g, ?_, hforce⟩⟩
      exact Function.Embedding.ext fun i ↦ congrFun hs i
    · exact ⟨x, fun h ↦ absurd h ha⟩
  choose O hO using hO
  have hw (N : ℕ) : ∃ w : R.Occurrence, N < w.type.topGrade := by
    have hlt : ((N : ℕ) : ℕ∞) < R.topGradeSup := htop ▸ ENat.natCast_lt_top _
    obtain ⟨w, hw⟩ := lt_iSup_iff.mp hlt
    exact ⟨w, by exact_mod_cast hw⟩
  obtain ⟨w₁, hw₁⟩ := hw (x.arity + 1)
  obtain ⟨w₂, hw₂⟩ := hw K
  obtain ⟨Z, hZ⟩ := hR.isCovering.exists_subset_support
    (x.support ∪ w₁.support ∪ w₂.support ∪ univ.biUnion fun a ↦ (O a).support)
  have hxZ : x ≤ Z := subset_union_left.trans (subset_union_left.trans
    (subset_union_left.trans hZ))
  have hw₁Z : w₁ ≤ Z := subset_union_right.trans (subset_union_left.trans
    (subset_union_left.trans hZ))
  have hw₂Z : w₂ ≤ Z := subset_union_right.trans (subset_union_left.trans hZ)
  have hOZ (a : Fin x.type.card) : O a ≤ Z :=
    (subset_biUnion_of_mem (fun a ↦ (O a).support) (mem_univ a)).trans
      (subset_union_right.trans hZ)
  obtain ⟨g, hg, -⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp hxZ
  refine ⟨Z, g, hg, hw₁.trans_le (Occurrence.topGrade_mono hR.isConsistent hw₁Z),
    hw₂.trans_le (Occurrence.topGrade_mono hR.isConsistent hw₂Z), fun a ha ↦ ?_⟩
  obtain ⟨g', hg', hfa⟩ := hO a ha
  obtain ⟨ga, hga, hgar⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp (hOZ a)
  have heq : g'.trans ga = g := by
    refine Function.Embedding.ext fun i ↦ Z.tuple.injective ?_
    have h₁ := DFunLike.congr_fun (congrArg (fun e ↦ g'.trans e) hga) i
    have h₂ := DFunLike.congr_fun hg' i
    have h₃ := DFunLike.congr_fun hg i
    simp only [Function.Embedding.trans_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  exact heq ▸ hfa.trans_face hgar

end Realization

/-! ### Acquisition -/

namespace Realization

/-- **Acquisition of caps respecting the root bottoms, from bot-keeping completions.**  If every
seed has a bot-keeping completion below the full grade, `Realization.RootBottomAcquisition`
holds. -/
theorem rootBottomAcquisition_of_botKeeping
    (hcomp : ∀ ⦃α : Ordinal.{u}⦄ (m : ℕ) (I : Seed.{u} α m),
      ∃ F : CompletionBelowFullGrade I, F.BotKeeping) :
    RootBottomAcquisition.{u, w} where
  exists_context α M R hα hR hH htop n t c hc := by
    obtain ⟨ξ, rfl, hhol⟩ := hH
    have hβ := isSuccLimit_blockStage ξ
    have hα' : blockStage ξ + ω ≤ blockStage (ξ + 1) := (blockStage_add_one ξ).ge
    set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨K, hK⟩ := StageType.exists_offset_bound t
    obtain ⟨Z, g, hg, hNZ, hKZ, hforce⟩ := hR.exists_forcing_floor hhol htop K x
    have htZ : StageType.restrictFace g Z.type = some t :=
      Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hg
    -- a top cap of the type of `Z`
    have hnt : ¬ Z.type.IsTopFree := fun htf ↦ by
      rw [← StageType.topGrade_eq_zero_iff] at htf
      omega
    obtain ⟨cc, hcc⟩ := StageType.exists_isTopCap (hR.isLegal _ _ Z.eval_tuple) hnt
    -- one point more, by high-arity dominance at `0`
    obtain ⟨u, hu, q₀, ⟨⟨hq₀l, hq₀f⟩, -⟩, he₀⟩ :=
      (hR.dominance Z 0 hβ.bot_lt).inter_cofaces hR.isConsistent hR.isLegal
    set Z₁ : R.Occurrence := ⟨Z.arity + 1, u, q₀, he₀⟩
    -- the bot-keeping completion of the seed of `q₀` with itself
    obtain ⟨F, hF⟩ := hcomp Z.arity (Seed.ofCoatoms hq₀l hq₀l hq₀f hq₀f)
    set qs := F.completion hβ.isSuccPrelimit
    have hqs : qs ∈ q₀.cofaces :=
      ⟨F.isLegal_completion _, F.restrictFace_left_completion hβ.isSuccPrelimit⟩
    have hne : (Z₁.type.cofaces ∩ StageType.bottomPatternFamily qs.toScheme qs.label).Nonempty :=
      ⟨qs, hqs, rfl, fun i j hij _ ↦ by obtain rfl : i = j := Fin.ext hij; rfl⟩
    obtain ⟨v, hv, q, hq, hev⟩ :=
      (hR.bottomPattern Z₁ qs.toScheme qs.label hne).inter_cofaces hR.isConsistent hR.isLegal
    -- the root along `g` followed by the first points
    have hp : StageType.restrictFace (g.trans Fin.castSuccEmb) q₀ = some t := by
      rw [← StageType.restrictFace_trans _ _ _ hq₀f]
      exact htZ
    refine ⟨Z.arity + 2, q, v, (g.trans Fin.castSuccEmb).trans Fin.castSuccEmb,
      covers_of_eval _ hev, ?_, ?_⟩
    · funext i
      have h₁ := DFunLike.congr_fun hv (Fin.castSucc (g i))
      have h₂ := DFunLike.congr_fun hu (g i)
      have h₃ := DFunLike.congr_fun hg i
      simp only [Function.Embedding.trans_apply, Fin.coe_castSuccEmb] at h₁ h₂ h₃ ⊢
      change v (Fin.castSucc (Fin.castSucc (g i))) = c i
      rw [h₁, h₂, h₃]
      rfl
    · exact StageType.markedCapContextBelow'_of_botKeeping hβ hα' hqs
        (fun u y hsu hu hys hyb ↦ hF.rowAt_completion_eq_bot hβ.isSuccPrelimit u y hsu hu hys hyb)
        hq hp hK (fun d hd ↦ (hforce d hd).trans_face hq₀f) (e := StageType.faceCell hq₀f cc)
        ((StageType.label_faceCell hq₀f cc).trans hcc.2.1)
        (by rw [StageType.grade_faceCell, hcc.grade_eq_topGrade]; exact hNZ)
        (by rw [StageType.grade_faceCell, hcc.grade_eq_topGrade]; exact hKZ)

end Realization

end VaughtConjecture

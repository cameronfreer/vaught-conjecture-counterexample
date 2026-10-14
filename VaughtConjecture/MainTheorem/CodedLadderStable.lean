/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TopGradeTruncation
import VaughtConjecture.MainTheorem.CodedLevelCompletion
import VaughtConjecture.MainTheorem.GrowthRelabelLadder

/-!
# The coded ladder contracts at every strongly coded context

Roadmap, Layer 3 ((R3) and (R4), the growth carrier) and Correspondence, item 1 (the strongly
coded legal stage types).  All results here are native constructions of this repository.

* `StageType.exists_stronglyCodedGrowthSeed_of_isSuccLimit`: at a limit stage, for a legal,
  strongly coded context `t'` and a legal, strongly coded coface `d` of the root face, some seed has
  `t'` as its first coatom type, a strongly coded second coatom type, and `d` as the face of its
  amalgam along the root followed by the new point.  The second coatom type is the strongly coded
  pinned extension (`StageType.exists_stronglyCoded_pinned_extension`, with
  `StageType.hasStronglyCodedApexCoatomExtensions`) in place of the exact one of
  `StageType.exists_growthSeed_of_isSuccLimit`.
* `StageType.hasCodedLadderGrowthCarriersStableAtSeed_levels`: the coded contract at the seed
  position (`StageType.HasCodedLadderGrowthCarriersStableAtSeed`) holds, through
  `Seed.hasCodedLadderCarrier_seedChoice` at that seed.
* `StageType.CodedLadderCarrierBody.relabel`,
  `StageType.HasCodedLadderGrowthCarriersStableAtSeed.hasCodedLadderGrowthCarriersStable`: the
  relabelling transport of `VaughtConjecture.MainTheorem.GrowthRelabelLadder` for coded ladder
  carriers; the relabelled carrier and the relabelled context are restrictions, hence strongly
  coded.  So `StageType.hasCodedLadderGrowthCarriersStable_levels` and
  `StageType.hasCodedLadderGrowthCarriers_levels`.
* `StageType.exists_stronglyCoded_pinned_extension_topGrade_le`: **the bounded strongly coded
  pinned-extension lemma**, the strongly coded pinned extension truncated above a top grade `K`
  (`StageType.exists_truncation_topGrade_le`), keeping both faces when their top grades are at most
  `K`.  It is one of the preservation inputs of (R2), not (R2) itself.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace StageType

/-- **The strongly coded growth seed** (native construction): at a limit stage, for a legal,
strongly coded context `t'` on `m + 1` points with face `p'` along the first `m` points, a root
`e₀` of `p'` with face `p`, and a legal, strongly coded coface `d` of `p`, some seed has `t'` as its
first coatom type, a strongly coded second coatom type, and `d` as the face of its amalgam along
the root followed by the new point.  The second coatom type is the strongly coded pinned
extension. -/
theorem exists_stronglyCodedGrowthSeed_of_isSuccLimit {α : Ordinal.{u}} {m n : ℕ}
    (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (m + 1)} (ht' : t'.IsLegal)
    (hsc : t'.rows.IsStronglyCoded) {p' : StageType.{u} α m}
    (hp' : restrictFace Fin.castSuccEmb t' = some p') {e₀ : Fin n ↪ Fin m}
    {p : StageType.{u} α n} (hp : restrictFace e₀ p' = some p) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ p.cofaces) (hdsc : d.rows.IsStronglyCoded) :
    ∃ I : Seed.{u} α m, I.left = t' ∧ I.right.rows.IsStronglyCoded ∧
      restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d := by
  obtain ⟨Q, hQ, hQp', hQd⟩ := exists_stronglyCoded_pinned_extension
    (hasStronglyCodedApexCoatomExtensions hα.isSuccPrelimit)
    ⟨ht'.restrictFace _ hp', isStronglyCoded_of_restrictFace hp' hsc⟩ hp ⟨hd.1, hdsc⟩ hd.2
  let I : Seed.{u} α m := Seed.ofCoatoms ht' hQ.1 hp' hQp'
  refine ⟨I, rfl, hQ.2, ?_⟩
  have hright : restrictFace (Coatom.right m) I.amalgam = some Q := I.restrictFace_right
  rw [← extendByLast_trans, ← restrictFace_trans I.amalgam _ _ hright]
  exact hQd

/-- **The coded contract at the seed position** (native construction): at the strongly coded seed
(`StageType.exists_stronglyCodedGrowthSeed_of_isSuccLimit`), both coatom types are strongly coded,
and the completion of the replicated coded level at the seed-fixed parameters is a coded ladder
carrier (`Seed.hasCodedLadderCarrier_seedChoice`).  Every premise is a binder of the contract. -/
theorem hasCodedLadderGrowthCarriersStableAtSeed_levels :
    HasCodedLadderGrowthCarriersStableAtSeed.{u} := by
  intro α n m t' g p' hα ht' hsc hp' p hte d hd hdsc hn Q hpair hQ hrel
  obtain ⟨I, rfl, hr, hdA⟩ := exists_stronglyCodedGrowthSeed_of_isSuccLimit hα ht' hsc hp'
    ((restrictFace_trans t' _ g hp').trans hte) hd hdsc
  exact Seed.hasCodedLadderCarrier_seedChoice hα hte hd hn hpair hQ hrel hdA hsc hr

/-! ### Relabelling -/

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The **body of the coded ladder contracts** at `t'`, `e`, `d` and `Q`: a coded ladder carrier
(`GrowthCarrier.CodedLadder`) with the schemes of `t'` and `d` as literal faces. -/
def CodedLadderCarrierBody (t' : StageType.{u} α k) (e : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (Q : GrowthRequests t' d.toScheme) : Prop :=
  ∃ (G : GrowthCarrier t'.toScheme d.toScheme e) (Mb : Type) (H : ℕ)
    (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **The body of the coded ladder contracts is transported along a relabelling** (native
construction), as `StageType.LadderCarrierBody.relabel`; the relabelled carrier is a restriction of
the carrier, hence strongly coded. -/
theorem CodedLadderCarrierBody.relabel {t' : StageType.{u} α k} (σ : Equiv.Perm (Fin k))
    {e'' : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {Q : GrowthRequests t' d.toScheme}
    (h : CodedLadderCarrierBody (t'.reindex σ) e'' d (Q.reindex σ)) :
    CodedLadderCarrierBody t' (e''.trans σ.toEmbedding) d Q := by
  obtain ⟨G, Mb, H, r, ⟨⟨w, hw⟩, ⟨hH, hr, hrd, hrp⟩, hctrl, hsc⟩⟩ := h
  rw [GrowthRequests.threshold_reindex] at hw hctrl
  refine ⟨G.relabel (C := t'.toScheme) σ, Mb, H, fun a i ↦ (G.relabelCell σ).symm (r a i),
    ⟨⟨(G.relabelCell σ).symm w, ?_⟩, ⟨hH, fun a i hi ↦ ?_, fun a i hi ↦ ?_, fun a i hi hi0 ↦ ?_⟩,
      fun u hu ↦ ?_, Scheme.isStronglyCoded_comap hsc _⟩⟩
  · rw [GrowthCarrier.gradedIndex_relabel_eq_univ_iff, Equiv.apply_symm_apply]
    exact hw
  · rw [GrowthCarrier.gradedIndex_relabel_eq_univ_iff, Equiv.apply_symm_apply]
    exact hr a i hi
  · rw [GrowthCarrier.rowAt_relabel, Equiv.apply_symm_apply]
    exact hrd a i hi
  · rw [GrowthCarrier.rowAt_relabel, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hrp a i hi hi0
  · obtain ⟨a, F, hc⟩ := hctrl _ ((G.gradedIndex_relabel_eq_univ_iff σ u _).mp hu)
    refine ⟨a, F, ?_⟩
    have := hc.relabel σ G
    rwa [Equiv.symm_apply_apply] at this

/-- **The stable inputs at a relabelled context, coded** (native construction): as
`StageType.ladderCarrierBody_of_reindex`, for coded ladder carriers; the relabelled context is
strongly coded when `t'` is. -/
theorem codedLadderCarrierBody_of_reindex {n j : ℕ}
    {t' : StageType.{u} α (j + 1)} (hsc : t'.rows.IsStronglyCoded) {e : Fin n ↪ Fin (j + 1)}
    {p : StageType.{u} α n}
    (hte : restrictFace e t' = some p) {d : StageType.{u} α (n + 1)}
    (hdp : restrictFace Fin.castSuccEmb d = some p) {Q : GrowthRequests t' d.toScheme}
    (hlab : ∀ i, Q.CorrectAt t'.label i (d.label i)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hseed : ∀ (σ : Equiv.Perm (Fin (j + 1))) (g : Fin n ↪ Fin j) (p' : StageType.{u} α j),
      (t'.reindex σ).rows.IsStronglyCoded →
      restrictFace Fin.castSuccEmb (t'.reindex σ) = some p' →
      ∀ hte'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some p,
      (∀ i, (Q.reindex σ).CorrectAt (t'.reindex σ).label i (d.label i)) →
      (Q.reindex σ).ClassCalibrated hte'' → (Q.reindex σ).HasRelativeLiftOnClass hte'' hdp →
      CodedLadderCarrierBody (t'.reindex σ) (g.trans Fin.castSuccEmb) d (Q.reindex σ)) :
    CodedLadderCarrierBody t' e d Q := by
  obtain ⟨σ, g, p', rfl, hp'⟩ := Realization.exists_perm_root_eq hte hQ.not_surjective
  have hte'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some p := by
    rw [restrictFace_reindex]
    exact hte
  exact (hseed σ g p' (Scheme.isStronglyCoded_comap hsc _) hp' hte''
    (fun i ↦ (GrowthRequests.correctAt_reindex_iff σ Q t'.label i _).mpr (hlab i))
    (hQ.reindex σ hte'' hte) (hrel.reindex σ hte'' hte hdp)).relabel σ

/-- **The stable coded contract from the seed position** (native construction): the coded contract
at the seed position gives `StageType.HasCodedLadderGrowthCarriersStable`, by relabelling. -/
theorem HasCodedLadderGrowthCarriersStableAtSeed.hasCodedLadderGrowthCarriersStable
    (h : HasCodedLadderGrowthCarriersStableAtSeed.{u}) :
    HasCodedLadderGrowthCarriersStable.{u} := by
  intro α n k t' e hα ht' hsc p hte d hd hdsc hn Q hlab hQ hrel
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range e := by
      by_contra! hall
      exact hQ.not_surjective hall
    exact ⟨k - 1, by have := x.2; omega⟩
  exact codedLadderCarrierBody_of_reindex hsc hte hd.2 hlab hQ hrel
    fun σ g p' hsc' hp' hte'' hlab'' hQ'' hrel'' ↦
      h (t'.reindex σ) g p' hα (ht'.reindex σ) hsc' hp' p hte'' d hd hdsc hn _ hlab'' hQ'' hrel''

/-- **The stable coded contract** (native construction): coded ladder carriers for requests
calibrated on the class at every legal, strongly coded context and strongly coded donor. -/
theorem hasCodedLadderGrowthCarriersStable_levels : HasCodedLadderGrowthCarriersStable.{u} :=
  hasCodedLadderGrowthCarriersStableAtSeed_levels.hasCodedLadderGrowthCarriersStable

/-- **The coded contract** (native construction), the (R3) instance: coded ladder carriers for
calibrated requests read exactly at the labels of a legal, strongly coded context, with a strongly
coded donor. -/
theorem hasCodedLadderGrowthCarriers_levels : HasCodedLadderGrowthCarriers.{u} :=
  hasCodedLadderGrowthCarriersStable_levels.hasCodedLadderGrowthCarriers

/-! ### The bounded strongly coded pinned extension -/

/-- **The bounded strongly coded pinned-extension lemma** (native construction): at a limit stage,
for a strongly coded legal `P` on `n` points with face `p` along `f`, and a strongly coded legal
one-point extension `d` of `p`, both of top grade at most `K`, some strongly coded legal `Q` on
`n + 1` points of top grade at most `K` has `P` as its face along the first `n` points and `d` as
its face along `f` followed by the new point.  It is the strongly coded pinned extension
(`StageType.exists_stronglyCoded_pinned_extension`) truncated above `K`
(`StageType.exists_truncation_topGrade_le`, which keeps the scheme, hence strong coding, and the
faces of top grade at most `K`).  It is one of the preservation inputs of (R2), not (R2)
itself. -/
theorem exists_stronglyCoded_pinned_extension_topGrade_le {m : ℕ} (hα : Order.IsSuccLimit α)
    {P : StageType.{u} α n} (hP : P.IsStronglyCodedLegal) {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p)
    (hd : d.IsStronglyCodedLegal) (hdp : restrictFace Fin.castSuccEmb d = some p) {K : ℕ}
    (hPK : P.topGrade ≤ K) (hdK : d.topGrade ≤ K) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsStronglyCodedLegal ∧ Q.topGrade ≤ K ∧
      restrictFace Fin.castSuccEmb Q = some P ∧ restrictFace (extendByLast f) Q = some d := by
  obtain ⟨Q₀, hQ₀, hQ₀P, hQ₀d⟩ := exists_stronglyCoded_pinned_extension
    (hasStronglyCodedApexCoatomExtensions hα.isSuccPrelimit) hP hPf hd hdp
  obtain ⟨Q, hQs, hQl, hQK, hQf⟩ := exists_truncation_topGrade_le hα Q₀ K
  have hsc : Q.rows.IsStronglyCoded := by
    rw [hQs]
    exact hQ₀.2
  exact ⟨Q, ⟨hQl.mpr hQ₀.1, hsc⟩, hQK, hQf _ P hQ₀P hPK, hQf _ d hQ₀d hdK⟩

end StageType

end VaughtConjecture

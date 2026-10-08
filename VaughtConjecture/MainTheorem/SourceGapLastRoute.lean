/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SourceGapMarkedCapRoute

/-!
# The receiving route with the lost point off the coatom (work file)

WORK FILE (branch `research/h2-last-reduction`).  No placeholders.

The coatom form of cutoff determination for source-gap contexts
(`Realization.CoatomCutoffDetermination`, `StageType.IsSourceGapContext`) asks determination also
at contexts whose lost point lies on the first coatom.  This file replaces the predicate by:
* `StageType.IsSourceGapContextOff`: a source-gap context whose coatom off the lost point (the
  complement of the lost point) is closed;
* `StageType.IsSourceGapContextLast`: a source-gap context whose lost point is the last point.

**Acquisition** (`Realization.residualAcquisition_isSourceGapContextOff`): the compiled acquisition
of source-gap contexts (`Realization.exists_covers_isSourceGapContextAt`) produces contexts with the
lost point last whose first coatom is the face of first loss, closed; the proof is repeated here
with that face exported.

**Reduction** (`Realization.FirstCoatomCutoffDetermination.cutoffDetermination_off`): cutoff
determination at the first coatom for `IsSourceGapContextLast` gives cutoff determination for
`IsSourceGapContextOff`, by the transposition of the lost point with the last point (the
complement of the lost point is closed, so it becomes the first coatom); the coatom form gives the
former (`Realization.CoatomCutoffDetermination.cutoffDetermination_off`).

**The main theorem from three finite statements, lost point last**
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGapLast_
markedCap`).
The (R2) hypothesis is coatom cutoff determination for `IsSourceGapContextLast`, weaker than the
one for `IsSourceGapContext`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- A **source-gap context with the coatom off the lost point closed**. -/
def IsSourceGapContextOff (K : ℕ) (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ (l : Fin k) (o r : Fin t'.card), t'.IsSourceGapContextAt K h l o r ∧
    univ.erase l ∈ t'.toCellScheme.faces

/-- A **source-gap context with the lost point last**. -/
def IsSourceGapContextLast (K : ℕ) (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ (l : Fin k) (o r : Fin t'.card), (l : ℕ) + 1 = k ∧ t'.IsSourceGapContextAt K h l o r

/-- **First loss, with `B` closed**: `StageType.exists_firstLoss`, also exporting that the face
`B` is closed. -/
theorem exists_firstLoss_mem {Q : StageType.{u} α m} {H : Set (Fin Q.card)} {G : Finset (Fin m)}
    (hG : G ∈ Q.toCellScheme.faces)
    (hfull : ∀ d, Q.toCellScheme.scope d ⊆ G → Q.label d = ⊤ → d ∈ H)
    (hloss : ∃ d, Q.label d = ⊤ ∧ d ∉ H) :
    ∃ (B : Finset (Fin m)) (p : Fin m), B ∈ Q.toCellScheme.faces ∧ G ⊆ B ∧ p ∉ B ∧
      insert p B ∈ Q.toCellScheme.faces ∧
      (∀ d, Q.toCellScheme.scope d ⊆ B → Q.label d = ⊤ → d ∈ H) ∧
      ∃ r, Q.label r = ⊤ ∧ r ∉ H ∧ Q.toCellScheme.scope r ⊆ insert p B ∧
        p ∈ Q.toCellScheme.scope r := by
  classical
  obtain ⟨B, hB, hmax⟩ := exists_max_image
    {B ∈ Q.toCellScheme.faces | G ⊆ B ∧
      ∀ d, Q.toCellScheme.scope d ⊆ B → Q.label d = ⊤ → d ∈ H} card
    ⟨G, mem_filter.mpr ⟨hG, Subset.rfl, hfull⟩⟩
  obtain ⟨hBf, hGB, hBfull⟩ := mem_filter.mp hB
  have hne : B ≠ univ := by
    rintro rfl
    obtain ⟨d, hd, hdH⟩ := hloss
    exact hdH (hBfull d (subset_univ _) hd)
  obtain ⟨p, hp, hpB⟩ := Q.isPlan.exists_insert_mem hBf hne
  have hnot : ¬ ∀ d, Q.toCellScheme.scope d ⊆ insert p B → Q.label d = ⊤ → d ∈ H := by
    intro hfull'
    have := hmax _ (mem_filter.mpr ⟨hpB, hGB.trans (subset_insert _ _), hfull'⟩)
    rw [card_insert_of_notMem hp] at this
    omega
  push Not at hnot
  obtain ⟨r, hrs, hr, hrH⟩ := hnot
  refine ⟨B, p, hBf, hGB, hp, hpB, hBfull, r, hr, hrH, hrs, ?_⟩
  by_contra hpr
  exact hrH (hBfull r ((subset_insert_iff_of_notMem hpr).mp hrs) hr)

/-- A tuple whose values are among the values of `φ` factors through `φ` along an embedding. -/
theorem exists_embedding_comp_eq' {β : Type*} {c : Fin n → β} (hc : Function.Injective c)
    {φ : Fin k → β} (h : ∀ i, ∃ j, φ j = c i) : ∃ e : Fin n ↪ Fin k, φ ∘ e = c := by
  choose j hj using h
  exact ⟨⟨j, fun a b hab ↦ hc (by rw [← hj a, ← hj b, hab])⟩, funext hj⟩


/-- **A source-gap context with its first coatom closed**:
`StageType.exists_isSourceGapContextAt_comap`, also exporting that the enumerated face minus the
lost point (the face `B` of first loss) is closed. -/
theorem exists_isSourceGapContextAt_comap_coatom {Q : StageType.{u} α m} (hQ : Q.IsLegal) {K : ℕ}
    (hQK : Q.topGrade = K) {H : Set (Fin Q.card)} (hH : Q.IsAdmissibleTopSupport H)
    {G : Finset (Fin m)} (hG : G ∈ Q.toCellScheme.faces)
    (hfull : ∀ d, Q.toCellScheme.scope d ⊆ G → Q.label d = ⊤ → d ∈ H)
    (hloss : ∃ d, Q.label d = ⊤ ∧ d ∉ H) {s₀ : Fin Q.card} (hs₀ : Q.label s₀ = ⊤)
    (hs₀K : Q.toCellScheme.grade s₀ = K) (hs₀G : Q.toCellScheme.scope s₀ ⊆ G) {g : Fin n → Fin m}
    (hg : Function.Injective g) (hgG : ∀ i, g i ∈ G) :
    ∃ (k : ℕ) (ι : Fin (k + 1) ↪ Fin m) (hι : univ.map ι ∈ Q.toCellScheme.faces)
      (e : Fin n ↪ Fin k), (∀ i, ι (e i).castSucc = g i) ∧
        univ.map (Fin.castSuccEmb.trans ι) ∈ Q.toCellScheme.faces ∧
        ∃ o r,
          (Q.comap ι hι).IsSourceGapContextAt K (e.trans Fin.castSuccEmb) (Fin.last k) o r := by
  classical
  -- the lawful section witnessing `H`
  obtain ⟨τ, hτ, hτH⟩ := hH.exists_isLawful
  -- first loss and the owner
  obtain ⟨B, p, hBf, hGB, hpB, hF, hBfull, r, hr, hrH, hrF, hpr⟩ :=
    exists_firstLoss_mem hG hfull hloss
  obtain ⟨o, ho, hoτ⟩ := exists_owner hQ hτ hF ((hτH s₀).mpr (hfull s₀ hs₀G hs₀))
    (hs₀G.trans (hGB.trans (subset_insert _ _)))
  rw [hs₀K] at ho
  -- the enumeration `ι` of `insert p B` with `p` last
  set k := #B
  let φ : Fin k → Fin m := fun i ↦ B.orderEmbOfFin rfl i
  have hφ : Function.Injective φ := (B.orderEmbOfFin rfl).injective
  have hφr : Set.range φ = B := by simp [φ]
  let ι : Fin (k + 1) ↪ Fin m :=
    ⟨Fin.snoc φ p, Fin.snoc_injective_of_injective hφ (by rw [hφr]; exact hpB)⟩
  have hιc (i : Fin k) : ι i.castSucc = φ i := Fin.snoc_castSucc (α := fun _ ↦ Fin m) _ _ _
  have hιl : ι (Fin.last k) = p := Fin.snoc_last (α := fun _ ↦ Fin m) _ _
  have hιF : univ.map ι = insert p B := by
    ext y
    simp only [mem_map, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last => exact Or.inl hιl
      | cast i =>
        refine Or.inr ?_
        rw [hιc, ← mem_coe, ← hφr]
        exact Set.mem_range_self i
    · rintro (rfl | hy)
      · exact ⟨Fin.last k, hιl⟩
      · obtain ⟨i, rfl⟩ : y ∈ Set.range φ := hφr ▸ hy
        exact ⟨i.castSucc, hιc i⟩
  have hF' : univ.map ι ∈ Q.toCellScheme.faces := hιF ▸ hF
  set t' := Q.comap ι hF'
  have hι : restrictFace ι Q = some t' := restrictFace_of_mem _ _ hF'
  -- the root embedding `e`
  obtain ⟨e, he⟩ := exists_embedding_comp_eq' hg (φ := φ) fun i ↦ by
    obtain ⟨j, hj⟩ : g i ∈ Set.range φ := hφr ▸ hGB (hgG i)
    exact ⟨j, hj⟩
  have hBι : univ.map (Fin.castSuccEmb.trans ι) = B := by
    ext y
    simp only [mem_map, mem_univ, true_and, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hιc, ← mem_coe, ← hφr]
      exact Set.mem_range_self i
    · intro hy
      obtain ⟨i, rfl⟩ : y ∈ Set.range φ := hφr ▸ hy
      exact ⟨i, hιc i⟩
  refine ⟨k, ι, hF', e, fun i ↦ (hιc (e i)).trans (congrFun he i), hBι ▸ hBf, ?_⟩
  -- the cells of `t'`
  have hvis {d : Fin Q.card} (hd : Q.toCellScheme.scope d ⊆ insert p B) :
      ∃ d', faceCell hι d' = d :=
    Q.toScheme.exists_faceCell_eq _ (Scheme.mem_visibleCells.mpr fun y hy ↦ by
      obtain ⟨i, -, hi⟩ := mem_map.mp (hιF ▸ hd hy)
      exact ⟨i, hi⟩)
  have hoF : Q.toCellScheme.scope o = insert p B := congrArg Prod.fst ho
  have hoK : Q.toCellScheme.grade o = K := congrArg Prod.snd ho
  obtain ⟨o', rfl⟩ := hvis hoF.le
  obtain ⟨r', rfl⟩ := hvis hrF
  have hscope_o : t'.toCellScheme.scope o' = univ := by
    refine map_injective ι ?_
    rw [← scope_faceCell hι, hoF, hιF]
  have hgrade_o : t'.toCellScheme.grade o' = K := (grade_faceCell hι o').symm.trans hoK
  have hlabel_o : t'.label o' = ⊤ :=
    (label_faceCell hι o').symm.trans (hH.subset ((hτH _).mp hoτ))
  have htopK : t'.topGrade = K := le_antisymm (hQK ▸ topGrade_le_of_restrictFace hι)
    (hgrade_o ▸ grade_le_topGrade hlabel_o)
  -- every top cell of `t'` lies below the owner
  have hbelow {a : Fin t'.card} (ha : t'.label a = ⊤) :
      a ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o') :=
    (CellScheme.gradedIndex_le_iff _).mpr
      ⟨(CellScheme.gradedIndex_fst _ ▸ hscope_o ▸ subset_univ _ :),
        (CellScheme.gradedIndex_snd _ ▸ hgrade_o ▸ htopK ▸ grade_le_topGrade ha :)⟩
  have hlabel_r : t'.label r' = ⊤ := (label_faceCell hι r').symm.trans hr
  -- the lawful section witnessing `H`, on the face
  have hτ' := isLawful_comp_faceCell hι hτ
  have hgap {a : Fin t'.card} (ha : t'.label a = ⊤) (haτ : τ (faceCell hι a) = ⊤) :
      visibilityReplace K K (t'.rowAt o' r') < t'.rowAt o' a := by
    have := Scheme.visibilityReplace_rowAt_lt hτ' hoτ (mt (hτH _).mp hrH) haτ (hbelow hlabel_r)
      (hbelow ha)
    rwa [hgrade_o] at this
  refine ⟨o', r', ⟨fun ⟨i, hi⟩ ↦ ?_, htopK, hscope_o, hgrade_o, hlabel_o, hlabel_r, ?_,
    hgap hlabel_o hoτ, fun a ha hla ↦ hgap ha ?_⟩⟩
  · -- the root avoids the last point
    exact (Fin.castSucc_lt_last (e i)).ne hi
  · -- the lost top contains the last point
    rw [scope_faceCell hι, mem_map] at hpr
    obtain ⟨y, hy, hyp⟩ := hpr
    obtain rfl : y = Fin.last k := ι.injective (hyp.trans hιl.symm)
    exact hy
  · -- a top cell avoiding the last point is visible in `B`, so in `H`
    refine (hτH _).mpr (hBfull _ ?_ ((label_faceCell hι a).trans ha))
    rw [scope_faceCell hι]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr fun h ↦ hla (h ▸ hy')
    rw [hιc, ← mem_coe, ← hφr]
    exact Set.mem_range_self i

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n : ℕ}

/-- **Residual acquisition of a source-gap context with its first coatom closed**:
`Realization.exists_covers_isSourceGapContextAt`, also exporting that the first coatom of the
acquired context (the complement of the lost point) is closed. -/
theorem exists_covers_isSourceGapContextAt_coatom (hα : Order.IsSuccLimit α) (hR : R.IsModel)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) :
    ∃ (k : ℕ) (t' : StageType.{u} α (k + 1)) (c' : Fin (k + 1) → M) (e : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ (e.trans Fin.castSuccEmb) = c ∧
        univ.map Fin.castSuccEmb ∈ t'.toCellScheme.faces ∧
        ∃ o r, t'.IsSourceGapContextAt K (e.trans Fin.castSuccEmb) (Fin.last k) o r := by
  classical
  -- the eventual top grade is positive: otherwise the empty tuple is a globally rigid core
  have hKpos : 0 < K := by
    refine Nat.pos_of_ne_zero fun hK0 ↦ hcore ?_
    obtain ⟨p, hp⟩ := hR.exists_covers_zero
    exact ⟨0, p, ![], hp, (hR.isGloballyRigidCore_empty_iff hα).mpr (by rw [hK, hK0]; rfl)⟩
  -- the tail, and an occurrence `z` above it containing the points of `c`
  obtain ⟨x₀, hx₀⟩ := exists_forall_le_topGrade_eq hR.isConsistent hR.isCovering hK
  obtain ⟨z, hz⟩ := hR.isCovering.exists_subset_support (univ.image c ∪ x₀.support)
  have hzK : z.type.topGrade = K := hx₀ z (subset_union_right.trans hz)
  -- `z` is not a globally rigid core
  have hnr : ¬ R.IsGloballyRigidCore z.tuple :=
    fun h ↦ hcore ⟨_, _, _, covers_of_eval _ z.eval_tuple, h⟩
  simp only [IsGloballyRigidCore, StageType.IsRigidCoreIn] at hnr
  push Not at hnr
  obtain ⟨m, Q, x, e₀, hx, hxe, H, hH, hcoreH, d₀, hd₀, hd₀H⟩ := hnr
  -- the occurrence of `x` lies above `z`, so `Q` has top grade `K`
  let y : R.Occurrence := ⟨m, ⟨x, hx.injective⟩, Q, hx.eval_eq⟩
  have hzy : z ≤ y := by
    intro a ha
    obtain ⟨j, rfl⟩ := (Occurrence.mem_support _).mp ha
    exact (Occurrence.mem_support _).mpr ⟨e₀ j, congrFun hxe j⟩
  have hQK : Q.topGrade = K := hx₀ y ((subset_union_right.trans hz).trans hzy)
  -- the face of `Q` along `e₀` is the type of `z`
  have hface : StageType.restrictFace e₀ Q = some z.type := by
    have he : e₀.trans ⟨x, hx.injective⟩ = z.tuple := Function.Embedding.ext fun j ↦ congrFun hxe j
    rw [← hR.isConsistent _ Q e₀ hx.eval_eq, he, z.eval_tuple]
  have hG : univ.map e₀ ∈ Q.toCellScheme.faces := ((StageType.restrictFace_eq_some_iff _ _).mp
    hface).1
  have hfull (d : Fin Q.card) (hd : Q.toCellScheme.scope d ⊆ univ.map e₀) (hdt : Q.label d = ⊤) :
      d ∈ H :=
    hcoreH d (mem_filter.mpr ⟨mem_univ _, hd⟩) hdt
  -- a top cell `s` of grade `K` of the type of `z`, visible through `e₀` in `Q`
  obtain ⟨s, hs, hsK⟩ := StageType.exists_grade_eq_topGrade (t := z.type) (hzK ▸ hKpos)
  have hsG : Q.toCellScheme.scope (StageType.faceCell hface s) ⊆ univ.map e₀ := by
    rw [StageType.scope_faceCell]
    exact map_subset_map.mpr (subset_univ _)
  -- the positions `g` of `c` in `x`, inside the range of `e₀`
  have hpos (i : Fin n) : ∃ j₀, x (e₀ j₀) = c i := by
    obtain ⟨j₀, hj₀⟩ := (Occurrence.mem_support _).mp
      (hz (mem_union_left _ (mem_image_of_mem c (mem_univ i))))
    exact ⟨j₀, (congrFun hxe j₀).trans hj₀⟩
  obtain ⟨g, hg⟩ := StageType.exists_embedding_comp_eq' hc.injective (φ := x) fun i ↦
    let ⟨j₀, hj₀⟩ := hpos i
    ⟨e₀ j₀, hj₀⟩
  have hgG (i : Fin n) : g i ∈ univ.map e₀ := by
    obtain ⟨j₀, hj₀⟩ := hpos i
    exact mem_map.mpr ⟨j₀, mem_univ _, hx.injective (hj₀.trans (congrFun hg i).symm)⟩
  obtain ⟨k, ι, hι, e, he, hcf, o, r, hsg⟩ := StageType.exists_isSourceGapContextAt_comap_coatom
    (hR.isLegal _ _ hx.eval_eq) hQK hH hG hfull ⟨d₀, hd₀, hd₀H⟩
    ((StageType.label_faceCell hface s).trans hs)
    ((StageType.grade_faceCell hface s).trans (hsK.trans hzK)) hsG g.injective hgG
  refine ⟨k, Q.comap ι hι, x ∘ ι, e, ⟨hx.injective.comp ι.injective, ?_⟩, ?_,
    (StageType.map_univ_mem_comap_faces_iff Q ι Fin.castSuccEmb hι).mpr hcf, o, r, hsg⟩
  · have hxι : (⟨x ∘ ι, hx.injective.comp ι.injective⟩ : Fin (k + 1) ↪ M) =
        ι.trans ⟨x, hx.injective⟩ := Function.Embedding.ext fun _ ↦ rfl
    rw [hxι, hR.isConsistent _ Q ι hx.eval_eq, StageType.restrictFace_of_mem _ _ hι]
  · funext i
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Fin.coe_castSuccEmb, he]
    exact congrFun hg i


/-- **Residual acquisition for source-gap contexts with the coatom off the lost point closed**. -/
theorem residualAcquisition_isSourceGapContextOff :
    ResidualAcquisition.{u, w} fun K t' h ↦ t'.IsSourceGapContextOff K h where
  exists_context _ _ _ _ hα hR hcore hK _ _ _ hc := by
    obtain ⟨k, t', c', e, hc', hcc', hcf, o, r, hs⟩ :=
      exists_covers_isSourceGapContextAt_coatom hα hR hcore hK hc
    refine ⟨k + 1, t', c', _, hc', hcc', Fin.last k, o, r, hs, ?_⟩
    have : univ.erase (Fin.last k) = univ.map Fin.castSuccEmb := by
      ext y
      simp [Fin.exists_castSucc_eq]
    rw [this]
    exact hcf

/-- **Cutoff determination with the lost point off the coatom, from the form at the first coatom
with the lost point last**: transpose the lost point with the last point. -/
theorem FirstCoatomCutoffDetermination.cutoffDetermination_off
    (hdet : FirstCoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h where
  exists_coface α K n k t' h hα ht' hP t ht d hd hdK := by
    obtain ⟨l, o, r, hs, hface⟩ := hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := l.2; omega⟩
    set σ : Equiv.Perm (Fin (j + 1)) := Equiv.swap l (Fin.last j) with hσ
    have hsurj := t'.toScheme.surjective_cellMap_equiv σ
    obtain ⟨o', rfl⟩ := hsurj o
    obtain ⟨r', rfl⟩ := hsurj r
    have hs' := hs.reindex (σ := σ)
    have hσl : σ.symm l = Fin.last j := by simp [hσ]
    rw [hσl] at hs'
    have hne (i : Fin n) : (h.trans σ.symm.toEmbedding) i ≠ Fin.last j :=
      fun hi ↦ hs'.notMem_range ⟨i, hi⟩
    let g : Fin n ↪ Fin j :=
      ⟨fun i ↦ ((h.trans σ.symm.toEmbedding) i).castPred (hne i), fun a b hab ↦
        (h.trans σ.symm.toEmbedding).injective (by simpa using congrArg Fin.castSucc hab)⟩
    have hg : g.trans Fin.castSuccEmb = h.trans σ.symm.toEmbedding :=
      Function.Embedding.ext fun i ↦ by simp [g]
    have hP' : (t'.reindex σ).IsSourceGapContextLast K (g.trans Fin.castSuccEmb) :=
      ⟨Fin.last j, o', r', by simp, hg ▸ hs'⟩
    have hcf : univ.map (Fin.castSuccEmb.trans σ.toEmbedding) ∈ t'.toCellScheme.faces := by
      convert hface using 1
      ext y
      simp only [mem_map, mem_univ, true_and, mem_erase, and_true,
        Function.Embedding.trans_apply, Fin.coe_castSuccEmb, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨i, rfl⟩ hl
        have h1 : σ (Fin.castSucc i) = σ (Fin.last j) := by rw [hl]; simp [hσ]
        exact Fin.castSucc_ne_last i (σ.injective h1)
      · intro hy
        have hσy : σ y ≠ Fin.last j := fun h1 ↦ hy (by
          have := congrArg σ h1
          simpa [hσ] using this)
        obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hσy
        exact ⟨i, by rw [hi]; simp [hσ]⟩
    have hp : StageType.restrictFace Fin.castSuccEmb (t'.reindex σ) =
        some (t'.comap (Fin.castSuccEmb.trans σ.toEmbedding) hcf) := by
      rw [StageType.restrictFace_reindex]
      exact StageType.restrictFace_of_mem t' _ hcf
    have ht'' : StageType.restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some t := by
      rw [StageType.restrictFace_reindex, hg]
      convert ht using 2
      exact Function.Embedding.ext fun i ↦ by simp
    obtain ⟨D'', hD'', δ, hδ, hdet''⟩ := hdet.exists_coface (t'.reindex σ) g _ hα (ht'.reindex σ)
      hP' hp t ht'' d hd hdK
    refine ⟨_, StageType.reindex_extendPerm_symm_mem_cofaces hD'', δ, hδ, ?_⟩
    have hroot : (g.trans Fin.castSuccEmb).trans σ.toEmbedding = h := by
      rw [hg]
      exact Function.Embedding.ext fun i ↦ by simp
    have := hdet''.reindex_extendPerm
    rwa [hroot] at this

/-- **Cutoff determination with the lost point off the coatom, from the coatom form with the lost
point last**: transpose the lost point with the last point. -/
theorem CoatomCutoffDetermination.cutoffDetermination_off
    (hdet : CoatomCutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextLast K h) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContextOff K h :=
  hdet.firstCoatom.cutoffDetermination_off

end Realization

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType
open Ordinal hiding univ

/-- **The thin `ℵ₁` spectrum from three finite coatom statements, lost point last**: as
`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`, with (R2)
asked only at the source-gap contexts whose lost point is the last point
(`StageType.IsSourceGapContextLast`):
* (R4): cutoff completions at the first coatom for the graded cap calibration at every `ξ < ω₁`
  (`h4`);
* (R2): coatom cutoff determination for the source-gap context with the lost point last (`h2`);
* (R3): hollow coatom cutoff determination for the marked-cap context (`h3`).
The acquisition is `Realization.residualAcquisition_isSourceGapContextOff`, and the reduction is
`Realization.CoatomCutoffDetermination.cutoffDetermination_off`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGapLast_markedCap
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletions.{0} ξ (GradedCapCalibration.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContextLast K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_determinations
    (fun ξ hξ ↦ (h4 ξ hξ).hasCutoffStableRecoverySchemes_gradedCap)
    residualAcquisition_isSourceGapContextOff h2.cutoffDetermination_off
    hollowAcquisition_isMarkedCapContext
    (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
      fun _ _ _ _ _ σ ht ↦ ht.reindex σ)

end MainTheorem

end VaughtConjecture

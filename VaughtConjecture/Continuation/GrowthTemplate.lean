/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthReferenceCalibration
import VaughtConjecture.Continuation.GrowthRelativeLift
import VaughtConjecture.Continuation.SourceGapDoubledCompletion
import VaughtConjecture.Label.BlockReading

/-!
# The template of the growth construction at a calibrated context

Roadmap, Layer 3 ((R3) and (R4), the template of the relative lift).

At a context `t'` calibrated for a donor `d` (`StageType.HollowReferenceCalibration'`), the
requests read through the cap (the bottom cells, the ordinal cells through their reference cells,
the cells labelled `⊤` through the marker) have a **template**
(`StageType.HollowReferenceCalibration'.exists_template`): a lawful donor labelling equal to the
cleaned cap row on the root and reading the requests from it.

The capped decoder `θ₀` of the labels of `t'` at the cap (labelled `⊤`) reads the cap's row as the
labels (`Scheme.exists_cappedDecoder`).  Through it the cap-row codes of the references lie in
increasing blocks, one per block of the donor's ordinal labels (`Label.blockOf_lt_of_read`), below
the marker read (`Label.blockOf_add_le_of_read_top`); the block code with these strips
(`Label.BlockCode.ofFinset`) encodes the donor
(`StageType.GrowthRequests.exists_template_of_encoding`).
On the root the encoding is the cap row: cells labelled `⊥` by the cleaning, cells labelled `⊤` by
the root-top inequality of the marked cap, ordinal cells by reading their codes in their block
(`Label.blockOf_eq_of_read`, `Label.finNat_eq_of_read`).

## References

The template is the growth step of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The ordinal of an ordinal label (`0` at `⊥` and `⊤`). -/
noncomputable def ordOf (x : Label.{u}) : Ordinal.{u} :=
  match x with
  | some (some s) => s
  | _ => 0

@[simp] theorem ordOf_coe (s : Ordinal.{u}) : ordOf (s : Label.{u}) = s := rfl

/-- A label strictly between `⊥` and `⊤` is its ordinal. -/
theorem eq_coe_ordOf {x : Label.{u}} (hb : x ≠ ⊥) (ht : x ≠ ⊤) : x = (ordOf x : Label.{u}) := by
  induction x using Label.recBotCoeTop with
  | bot => exact absurd rfl hb
  | top => exact absurd rfl ht
  | coe s => rfl

/-- A coded row value is not `⊤`. -/
theorem rowAt_ne_top {t : StageType.{u} α k} (c x : Fin t.card) : t.rowAt c x ≠ ⊤ :=
  (lt_of_lt_of_le (t.isCoded.rowAt_lt c x) le_top).ne

/-- **The template at a calibrated context.**  At a legal context `t'` calibrated along its root
`e` for a legal donor `d` (root face `p`, `0 < n`), some requests on `d` are read exactly at the
labels of `t'`, have a cap of full scope, references, marker and offsets at most the threshold, and
a template. -/
theorem HollowReferenceCalibration'.exists_template {t' : StageType.{u} α k} (ht' : t'.IsLegal)
    {e : Fin n ↪ Fin k} {p : StageType.{u} α n} (hte : restrictFace e t' = some p)
    {d : StageType.{u} α (n + 1)} (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hd : d.IsLegal) (hn : 0 < n) (hC : HollowReferenceCalibration' t' e d) :
    ∃ Q : GrowthRequests t' d.toScheme,
      (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) ∧
      t'.toCellScheme.scope Q.cap = univ ∧
      (∀ j ∈ Q.exacts, t'.toCellScheme.grade (Q.ref j) ≤ Q.threshold ∧
        Q.offset j ≤ Q.threshold) ∧
      (t'.toCellScheme.grade Q.marker ≤ Q.threshold ∧ Q.markerOffset ≤ Q.threshold) ∧
      Q.HasTemplate hte hdp := by
  classical
  obtain ⟨jj, g, h₀, c, r, hh, hmc, hoff, hbotR, href⟩ := hC
  set N := t'.toCellScheme.grade c with hNdef
  have hcap : t'.label c = ⊤ := hmc.1.2.1
  have hscope : t'.toCellScheme.scope c = univ := hmc.1.1
  have hmark : t'.label r = ⊤ := hmc.2.1.1
  have hrb : r ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := hmc.2.1.2.1
  have hRN : jj + 1 < N := hmc.2.2.1
  have hN0 : 0 < N := by omega
  have hnj : n ≤ jj := by simpa using Fintype.card_le_of_embedding h₀
  -- cells below the cap
  have hbelow (x : Fin t'.card) (hx : t'.toCellScheme.grade x ≤ N) :
      x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := by
    rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
      CellScheme.gradedIndex_snd, hscope]
    exact ⟨subset_univ _, hx⟩
  -- cells visible through the enlarged root have grade below the cap's
  have hgvis (x : Fin t'.card) (hx : x ∈ t'.visibleCells g) :
      t'.toCellScheme.grade x ≤ jj := by
    have h1 := t'.isWellFormed.isWellFormed.grade_le_card x
    have h2 : t'.toCellScheme.scope x ⊆ univ.map g := by
      intro y hy
      obtain ⟨i, hi⟩ := (Scheme.mem_visibleCells.mp hx) (mem_coe.mpr hy)
      exact mem_map.mpr ⟨i, mem_univ _, hi⟩
    exact h1.trans ((card_le_card h2).trans (by simp))
  -- references and offsets, per donor cell
  have hsel : ∀ j : Fin d.card, ∃ (μ : Ordinal.{u}) (m r' : ℕ) (a : Fin t'.card),
      ∀ o : Ordinal.{u}, d.label j = o → Order.IsSuccPrelimit μ ∧ o = μ + m ∧ m < N ∧
        a ∈ t'.visibleCells g ∧ t'.label a = ((μ + r' : Ordinal.{u}) : Label.{u}) := by
    intro j
    by_cases hj : ∃ o : Ordinal.{u}, d.label j = o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨μ, m, r', a, hμ, hom, hmN, ha, hal⟩ := href j o ho
      refine ⟨μ, m, r', a, fun o' ho' ↦ ?_⟩
      have : o' = o := Label.coe_inj'.mp (ho'.symm.trans ho)
      subst this
      exact ⟨hμ, hom, hmN, ha, hal⟩
    · exact ⟨0, 0, 0, c, fun o ho ↦ absurd ⟨o, ho⟩ hj⟩
  choose μ m r' a hsel using hsel
  let Q : GrowthRequests t' d.toScheme :=
    { cap := c, marker := r, markerOffset := jj + 1, bottoms := {j | d.label j = ⊥},
      exacts := {j | d.label j ≠ ⊥ ∧ d.label j ≠ ⊤}, highs := {j | d.label j = ⊤}, ref := a,
      offset := m }
  have hQN : Q.threshold = N := rfl
  -- the ordinal of an exact cell's label
  have hexo (j : Fin d.card) (hj : j ∈ Q.exacts) :
      d.label j = ((μ j + m j : Ordinal.{u}) : Label.{u}) := by
    obtain ⟨hb, ht⟩ := hj
    have h1 := eq_coe_ordOf hb ht
    rw [h1, (hsel j _ h1).2.1]
  have hexs (j : Fin d.card) (hj : j ∈ Q.exacts) := hsel j _ (hexo j hj)
  -- the references read below the threshold
  have hrefN (j : Fin d.card) (hj : j ∈ Q.exacts) : r' j < N :=
    hoff (a j) (hexs j hj).2.2.2.1 (μ j) (r' j) (hexs j hj).1 (hexs j hj).2.2.2.2
  -- exactness of the requests at the labels of `t'`
  have hexact : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j := by
    intro j ℓ
    have hQc : t'.label Q.cap = ⊤ := hcap
    have hQm : t'.label Q.marker = ⊤ := hmark
    simp only [GrowthRequests.CorrectAt, hQc, min_top_right]
    by_cases hb : d.label j = ⊥
    · have hz : j ∈ Q.bottoms := hb
      have hf : j ∉ Q.exacts := fun h ↦ h.1 hb
      have hy : j ∉ Q.highs := fun h ↦ by
        have : d.label j = ⊤ := h
        rw [hb] at this; exact bot_ne_top this
      simp [hz, hf, hy, hb]
    by_cases ht : d.label j = ⊤
    · have hz : j ∉ Q.bottoms := hb
      have hf : j ∉ Q.exacts := fun h ↦ h.2 ht
      have hy : j ∈ Q.highs := ht
      have hr : Q.readMarker t'.label = ⊤ := by simp [GrowthRequests.readMarker, hQc, hQm]
      simp [hz, hf, hy, hr, ht]
    · have hf : j ∈ Q.exacts := ⟨hb, ht⟩
      have hz : j ∉ Q.bottoms := hb
      have hy : j ∉ Q.highs := ht
      have hr : Q.readExact t'.label j = d.label j := by
        simp only [GrowthRequests.readExact, hQc, min_top_right]
        change visibilityReplace N (m j) (t'.label (a j)) = _
        rw [(hexs j hf).2.2.2.2, hexo j hf,
          GrowthRequests.visibilityReplace_add_natCast (hexs j hf).1 (hrefN j hf)]
      simp [hz, hf, hy, hr]
  -- the decoder of the labels of `t'` at the cap
  obtain ⟨θ, hθm, hθb, -, hθv, -, hθr⟩ := Scheme.exists_cappedDecoder (S := t'.toScheme)
    t'.isLawful (rfl : t'.toCellScheme.grade c = N)
  have hθl (x : Fin t'.card) (hx : t'.toCellScheme.grade x ≤ N) :
      θ (t'.rowAt c x) = t'.label x := by
    rw [hθr x (hbelow x hx), hcap, min_top_right]
  -- the codes of the cells below the cap with a label other than `⊥`
  have hcode (x : Fin t'.card) (hx : t'.toCellScheme.grade x ≤ N) (hxb : t'.label x ≠ ⊥) :
      t'.rowAt c x = (ordOf (t'.rowAt c x) : Label.{u}) := by
    refine eq_coe_ordOf (fun h0 ↦ hxb ?_) (rowAt_ne_top c x)
    rw [← hθl x hx, h0, hθb]
  have hrefg (j : Fin d.card) (hj : j ∈ Q.exacts) : t'.toCellScheme.grade (a j) ≤ N :=
    (hgvis _ (hexs j hj).2.2.2.1).trans (by omega)
  have hrefb (j : Fin d.card) (hj : j ∈ Q.exacts) : t'.label (a j) ≠ ⊥ := by
    rw [(hexs j hj).2.2.2.2]; exact WithBot.coe_ne_bot
  have hread (j : Fin d.card) (hj : j ∈ Q.exacts) :
      θ ((ordOf (t'.rowAt c (a j)) : Ordinal.{u}) : Label.{u}) =
        ((μ j + r' j : Ordinal.{u}) : Label.{u}) := by
    rw [← hcode _ (hrefg j hj) (hrefb j hj), hθl _ (hrefg j hj), (hexs j hj).2.2.2.2]
  have hrg : t'.toCellScheme.grade r ≤ N := hrb.2
  have hreadm : θ ((ordOf (t'.rowAt c r) : Ordinal.{u}) : Label.{u}) = ⊤ := by
    rw [← hcode r hrg (by rw [hmark]; exact top_ne_bot), hθl r hrg, hmark]
  -- the codes of the references, block by block
  set code : Fin d.card → Ordinal.{u} := fun j ↦ ordOf (t'.rowAt c (a j)) with hcodedef
  set sa : Ordinal.{u} := ordOf (t'.rowAt c r) with hsadef
  have hθv' : ∀ k' ≤ N, ∀ i ≤ k', ∀ x, θ (visibilityReplace k' i x) =
      visibilityReplace k' i (θ x) := fun k' hk i hi x ↦ hθv k' hk i hi x
  set S : Finset Ordinal.{u} := (univ.filter (· ∈ Q.exacts)).image μ with hSdef
  have hmemS {ν : Ordinal.{u}} : ν ∈ S ↔ ∃ j, j ∈ Q.exacts ∧ μ j = ν := by
    simp [hSdef]
  let strip : Ordinal.{u} → Ordinal.{u} := fun ν ↦
    if h : ∃ j, j ∈ Q.exacts ∧ μ j = ν then blockOf (code (Classical.choose h)) else 0
  have hstrip (j : Fin d.card) (hj : j ∈ Q.exacts) : strip (μ j) = blockOf (code j) := by
    have h : ∃ j', j' ∈ Q.exacts ∧ μ j' = μ j := ⟨j, hj, rfl⟩
    have hs : strip (μ j) = blockOf (code (Classical.choose h)) := dite_eq_left h
    obtain ⟨hj', hμj'⟩ := Classical.choose_spec h
    have hr' := hread _ hj'
    rw [hμj'] at hr'
    rw [hs]
    exact Label.blockOf_eq_of_read hθm hθv' hN0 (hexs j hj).1 (hrefN _ hj') (hrefN j hj) hr'
      (hread j hj)
  have hlim : ∀ ν ∈ S, Order.IsSuccPrelimit (strip ν) := by
    intro ν hν
    obtain ⟨j, hj, rfl⟩ := hmemS.mp hν
    rw [hstrip j hj]; exact isSuccPrelimit_blockOf _
  set htop : Ordinal.{u} := Ordinal.visibilityReplace N (jj + 1) sa with hhtop
  have hle : ∀ ν ∈ S, strip ν + N ≤ htop := by
    intro ν hν
    obtain ⟨j, hj, rfl⟩ := hmemS.mp hν
    rw [hstrip j hj]
    exact Label.blockOf_add_le_of_read_top hθm hθv' (hexs j hj).1 (hrefN j hj) (hread j hj)
      hreadm
  have hstrict : ∀ ν ∈ S, ∀ ν' ∈ S, ν < ν' → strip ν < strip ν' := by
    intro ν hν ν' hν' hlt
    obtain ⟨j, hj, rfl⟩ := hmemS.mp hν
    obtain ⟨j', hj', rfl⟩ := hmemS.mp hν'
    rw [hstrip j hj, hstrip j' hj']
    exact Label.blockOf_lt_of_read hθm hθv' (hexs j hj).1 (hexs j' hj').1 hlt (hrefN j hj)
      (hrefN j' hj') (hread j hj) (hread j' hj')
  have hRtop : jj + 1 ≤ finNat htop := Label.le_finNat_visibilityReplace hRN
  set B := BlockCode.ofFinset N (jj + 1) hRN S strip htop hlim hle hstrict hRtop with hB
  have hBΛ (j : Fin d.card) (hj : j ∈ Q.exacts) : B.Λ (μ j) = some (strip (μ j)) :=
    BlockCode.ofFinset_Λ N (jj + 1) hRN S strip htop hlim hle hstrict hRtop
      (hmemS.mpr ⟨j, hj, rfl⟩)
  -- the code of an exact label
  have hencF (j : Fin d.card) (hj : j ∈ Q.exacts) :
      B.code (d.label j) = ((blockOf (code j) + m j : Ordinal.{u}) : Label.{u}) := by
    have hμ := (hexs j hj).1
    rw [hexo j hj, BlockCode.code_coe, B.codeOrd_listed
      (by rw [blockOf_add_natCast hμ]; exact hmemS.mpr ⟨j, hj, rfl⟩)
      (by rw [blockOf_add_natCast hμ]; exact hBΛ j hj)
      (by rw [finNat_add_natCast hμ]; exact (hexs j hj).2.2.1.le),
      finNat_add_natCast hμ, hstrip j hj]
  -- the code is a witness bounded by `n + 1`, and reads only `⊥` as `⊥`
  have henc : IsWitness (stepSuppressor (n + 1)) B.code :=
    B.isWitness_code'.of_le_stepSuppressor (show n + 1 ≤ jj + 1 by omega)
  have hbot (j : Fin d.card) (h : B.code (d.label j) = ⊥) : d.label j = ⊥ := by
    by_contra hb
    by_cases ht : d.label j = ⊤
    · rw [ht, BlockCode.code_top] at h; exact WithBot.coe_ne_bot h
    · rw [hencF j ⟨hb, ht⟩] at h; exact WithBot.coe_ne_bot h
  have hHvis : IsSelfVisible (n + 1) ((htop : Ordinal.{u}) : Label.{u}) :=
    isSelfVisible_coe.mpr (by rw [finNat_spec]; exact_mod_cast (show n + 1 ≤ finNat htop by omega))
  -- the cleaned cap row
  have heC (x : Fin t'.card) (hx : t'.label x ≠ ⊥) : Q.cleanedCapRow x = t'.rowAt c x :=
    ite_eq_right hx
  have heCb (x : Fin t'.card) (hx : t'.label x = ⊥) : Q.cleanedCapRow x = ⊥ := ite_eq_left hx
  have heCr : Q.cleanedCapRow r = ((sa : Ordinal.{u}) : Label.{u}) := by
    rw [heC r (by rw [hmark]; exact top_ne_bot)]
    exact hcode r hrg (by rw [hmark]; exact top_ne_bot)
  have heCa (j : Fin d.card) (hj : j ∈ Q.exacts) :
      Q.cleanedCapRow (a j) = ((code j : Ordinal.{u}) : Label.{u}) := by
    rw [heC _ (hrefb j hj)]
    exact hcode _ (hrefg j hj) (hrefb j hj)
  have hfinref (j : Fin d.card) (hj : j ∈ Q.exacts) : finNat (code j) = r' j :=
    Label.finNat_eq_of_read hθv' (hexs j hj).1 (hrefN j hj) (hread j hj)
  have hFj (j : Fin d.card) (hj : j ∈ Q.exacts) :
      visibilityReplace Q.threshold (Q.offset j) (Q.cleanedCapRow (Q.ref j)) =
        ((blockOf (code j) + m j : Ordinal.{u}) : Label.{u}) := by
    change visibilityReplace N (m j) (Q.cleanedCapRow (a j)) = _
    rw [heCa j hj, visibilityReplace_coe,
      Label.visibilityReplace_blockOf_of_lt (by rw [hfinref j hj]; exact hrefN j hj)]
  have hltH (j : Fin d.card) (hj : j ∈ Q.exacts) :
      ((blockOf (code j) + m j : Ordinal.{u}) : Label.{u}) <
        ((htop : Ordinal.{u}) : Label.{u}) := by
    rw [Label.coe_lt_coe_iff]
    refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr ?_) (hstrip j hj ▸ hle (μ j)
      (hmemS.mpr ⟨j, hj, rfl⟩))
    exact_mod_cast (hexs j hj).2.2.1
  -- the cells of the root
  have hvis (i : Fin p.card) : t'.faceCell hte i ∈ t'.visibleCells g := by
    have h1 := Scheme.faceCell_mem_visibleCells (comap_toScheme_of_restrictFace hte) i
    rw [Scheme.mem_visibleCells] at h1
    change _ ∈ t'.toScheme.visibleCells g
    rw [Scheme.mem_visibleCells]
    intro y hy
    obtain ⟨z, hz⟩ := h1 hy
    exact ⟨h₀ z, by rw [← hz, ← hh]; rfl⟩
  have hclean (i : Fin p.card) :
      Q.cleanedCapRow (t'.faceCell hte i) = t'.rowAt c (t'.faceCell hte i) := by
    by_cases hb : t'.label (t'.faceCell hte i) = ⊥
    · rw [heCb _ hb, hbotR _ (hvis i) hb]
    · exact heC _ hb
  have hgi : t'.toCellScheme.gradedIndex c = ((univ : Finset (Fin k)), N) := by
    rw [← hscope]; rfl
  have heρ : p.rows.IsLawful fun i ↦ Q.cleanedCapRow (t'.faceCell hte i) := by
    have hlaw : t'.rows.IsLawful (t'.rowAt c) := Scheme.isLawful_rowAt ht'.isConsistent hgi
    have h1 : p.rows.IsLawful fun i ↦ t'.rowAt c (t'.faceCell hte i) := by
      obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t' e).mp hte
      exact hlaw.comap (t'.isLowerEmbedding_comap e)
    convert h1 using 2 with i
    exact hclean i
  -- the three root checks
  have hroot (i : Fin p.card) : min (B.code (d.label (d.faceCell hdp i))) (htop : Label.{u}) =
      min (Q.cleanedCapRow (t'.faceCell hte i)) (htop : Label.{u}) := by
    set x := t'.faceCell hte i with hxdef
    have hlx : d.label (d.faceCell hdp i) = t'.label x := by
      rw [StageType.label_faceCell, StageType.label_faceCell]
    by_cases hb : t'.label x = ⊥
    · rw [hlx, hb, BlockCode.code_bot, heCb x hb]
    by_cases ht : t'.label x = ⊤
    · rw [hlx, ht, BlockCode.code_top]
      change min ((htop : Ordinal.{u}) : Label.{u}) _ = _
      rw [min_self, heC x hb]
      refine (min_eq_right ?_).symm
      have h1 := hmc.2.2.2 x (hvis i) ht
      rw [hcode r hrg (by rw [hmark]; exact top_ne_bot), visibilityReplace_coe] at h1
      exact h1
    · set j := d.faceCell hdp i
      have hj : j ∈ Q.exacts := ⟨by rw [hlx]; exact hb, by rw [hlx]; exact ht⟩
      have hxg : t'.toCellScheme.grade x ≤ N := (hgvis x (hvis i)).trans (by omega)
      have hsx : θ ((ordOf (t'.rowAt c x) : Ordinal.{u}) : Label.{u}) =
          ((μ j + m j : Ordinal.{u}) : Label.{u}) := by
        rw [← hcode x hxg hb, hθl x hxg, ← hlx, hexo j hj]
      have hf := Label.finNat_eq_of_read hθv' (hexs j hj).1 (hexs j hj).2.2.1 hsx
      have hbk := Label.blockOf_eq_of_read hθm hθv' hN0 (hexs j hj).1 (hexs j hj).2.2.1
        (hrefN j hj) hsx (hread j hj)
      have hxo : ordOf (t'.rowAt c x) = blockOf (code j) + m j := by
        rw [← blockOf_add_finNat (ordOf (t'.rowAt c x)), hf, hbk]
      rw [hencF j hj, heC x hb, hcode x hxg hb, hxo]
  obtain ⟨V, hV, hVr, hVc, hVf⟩ := GrowthRequests.exists_template_of_encoding
    (eC := Q.cleanedCapRow) hte hdp Q hd hn heρ henc hbot WithBot.coe_ne_bot hHvis hroot
    (fun _ hj ↦ hj)
    (fun j hj ↦ by rw [hencF j hj, hFj j hj]) (fun j hj ↦ by rw [hFj j hj]; exact hltH j hj)
    (fun j hj ↦ by
      have : d.label j = ⊤ := hj
      rw [this, BlockCode.code_top]; rfl)
    (by
      simp only [GrowthRequests.readMarker]
      change _ = min (visibilityReplace N (jj + 1) (Q.cleanedCapRow r)) _
      rw [heCr, visibilityReplace_coe])
  exact ⟨Q, hexact, hscope, fun j hj ↦ ⟨hrefg j hj, (hexs j hj).2.2.1.le⟩,
    ⟨hrg, show jj + 1 ≤ N by omega⟩, V, hV, hVr, hVc, hVf⟩

end StageType

end VaughtConjecture
